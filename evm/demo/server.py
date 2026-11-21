#!/usr/bin/env python3
"""A web page in front of the service running in an Intel TDX trust domain.

    demo/server.py            (from evm/, after: scripts/build-efi tdx)

Boots the TDX image with the OS's scripts/run-efi and keeps it running, serves demo/page.html, and for each
press of the button puts one attested request (Evm/Attest.lean) to the guest, has this host's quote
generation service turn the guest's TDREPORT into a quote, and hands response and quote to the page. The
page, not this program, checks the quote: this program is the untrusted host in the demonstration, and
nothing it says about the guest is asked to be believed.

A visitor chooses a fixture, one of three alterations and a challenge. Requests are built here from the
files in fixtures/, so no bytes of a visitor's own reach the guest. One request runs at a time, because the
guest reads no packet while it works.

Settings, all in the environment:

    EVM_DEMO_PORT   loopback port this listens on (default 5172)
    SILO_HOST_PORT  loopback port the guest's port 5005 is forwarded to (default 5025)
    SILO_TDVF       the firmware, as scripts/run-efi takes it
    EVM_DEMO_QGS    the quote generation service's socket (default /var/run/tdx-qgs/qgs.socket)
    EVM_DEMO_BUILT  where builder/shadow keeps blocks it built, with their quotes, for the page at /built
                    (default /data/eth/shadow/landed)
"""
import base64, glob, hashlib, importlib.machinery, importlib.util, json, os, re, shutil, signal, socket, struct
import subprocess, sys, threading, time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
system = os.path.dirname(here)
demo = os.path.join(here, "demo")
fixtures_dir = os.path.join(here, "fixtures")
work = os.path.join(here, ".lake/build/demo")
image = os.path.join(here, ".lake/build/efi/tdx/evm-os/BOOTX64.EFI")
listen_port = int(os.environ.get("EVM_DEMO_PORT", "5172"))
guest_port = int(os.environ.get("SILO_HOST_PORT", "5025"))
qgs_socket = os.environ.get("EVM_DEMO_QGS", "/var/run/tdx-qgs/qgs.socket")
built_dir = os.environ.get("EVM_DEMO_BUILT", "/data/eth/shadow/landed")
firmware = os.environ.get("SILO_TDVF", os.path.join(system, ".lake/build/efi/tdx/OVMF.fd"))

# The OS's own client for the quote generation service; it is a script, so it is loaded by path, and
# without leaving a compiled copy beside it.
sys.dont_write_bytecode = True
_loader = importlib.machinery.SourceFileLoader("tdx_quote", os.path.join(system, "scripts/tdx-quote"))
_spec = importlib.util.spec_from_loader("tdx_quote", _loader)
tdx_quote = importlib.util.module_from_spec(_spec)
_loader.exec_module(tdx_quote)


def sha256_file(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def git(*args):
    try:
        return subprocess.run(["git", "-C", system, *args], capture_output=True, text=True, timeout=20).stdout
    except (OSError, subprocess.SubprocessError):
        return ""


# ---- The fixtures, and where in each the two alterations go.

def rlp_prefix(data, at):
    """The length of the RLP list header at `at`."""
    first = data[at]
    if first < 0xc0:
        raise ValueError("not an RLP list")
    return 1 if first < 0xf8 else 1 + (first - 0xf7)


def describe(name):
    with open(os.path.join(fixtures_dir, name + ".req"), "rb") as f:
        request = f.read()
    with open(os.path.join(fixtures_dir, name + ".expected"), "rb") as f:
        expected = f.read()
    at = 5 + 1 + 8
    accounts, = struct.unpack_from(">I", request, at)
    at += 4
    balance = at + 20 + 8 + 31  # the last byte of the first account's balance
    for _ in range(accounts):
        at += 20 + 8 + 32
        code, = struct.unpack_from(">I", request, at)
        at += 4 + code
        slots, = struct.unpack_from(">I", request, at)
        at += 4 + 64 * slots
    genesis, = struct.unpack_from(">I", request, at)
    at += 4 + genesis
    blocks, = struct.unpack_from(">I", request, at)
    at += 4
    last = at
    for _ in range(blocks):
        size, = struct.unpack_from(">I", request, at)
        last = at + 4
        at += 4 + size
    if at != len(request):
        raise ValueError(f"{name}: not a request")
    # A block is a list whose first item is the header, a list: parent hash, ommers hash, beneficiary,
    # state root. Each hash is one length byte and 32 bytes; the beneficiary one and 20.
    header = last + rlp_prefix(request, last)
    fields = header + rlp_prefix(request, header)
    root = fields + 33 + 33 + 21
    if request[root] != 0xa0:
        raise ValueError(f"{name}: no state root where one is expected")
    return {"name": name, "size": len(request), "sha256": hashlib.sha256(request).hexdigest(),
            "accounts": accounts, "blocks": blocks, "expected": expected.hex(),
            "alter": {"none": None, "root": root + 32, "state": balance}}, request


catalogue, requests = {}, {}
for path in sorted(glob.glob(os.path.join(fixtures_dir, "*.req"))):
    entry, body = describe(os.path.basename(path)[:-4])
    catalogue[entry["name"]] = entry
    requests[entry["name"]] = body


def build(name, alter, challenge):
    """The attested frame for a fixture, one byte of it changed if asked. The page builds the same bytes."""
    body = bytearray(requests[name])
    at = catalogue[name]["alter"][alter]
    if at is not None:
        body[at] ^= 1
    return b"JATT1" + challenge + bytes(body)


# ---- The guest.

class Guest:
    def __init__(self):
        self.process = None
        self.log = os.path.join(work, "serial.log")
        self.started = 0.0
        self.boots = 0

    def serial(self):
        try:
            with open(self.log, "rb") as f:
                return f.read().decode("utf-8", "replace")
        except OSError:
            return ""

    def console(self):
        return [line for line in self.serial().splitlines() if line.startswith(("silo:", "evm:"))]

    def alive(self):
        return self.process is not None and self.process.poll() is None

    def stop(self):
        if self.process is not None:
            try:
                os.killpg(self.process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                self.process.wait(timeout=20)
            except subprocess.TimeoutExpired:
                os.killpg(self.process.pid, signal.SIGKILL)
            self.process = None

    def start(self):
        self.stop()
        # The OS's launcher looks for an image under its own build directory, by name.
        slot = os.path.join(system, ".lake/build/efi/tdx/evm-os")
        os.makedirs(slot, exist_ok=True)
        shutil.copyfile(image, os.path.join(slot, "BOOTX64.EFI"))
        self.process = subprocess.Popen(
            [os.path.join(system, "scripts/run-efi"), "tdx", "evm-os"], cwd=system,
            env=dict(os.environ, SILO_HOST_PORT=str(guest_port), SILO_TDVF=firmware),
            stdout=open(self.log, "wb"), stderr=subprocess.STDOUT, start_new_session=True)
        began = time.time()
        while "serving TCP 5005" not in self.serial():
            if self.process.poll() is not None or time.time() - began > 120:
                tail = self.serial()[-2000:]
                self.stop()
                raise RuntimeError("the guest did not come up; its serial output:\n" + tail)
            time.sleep(0.2)
        self.started = time.time()
        self.boots += 1

    def ask(self, frame, patience):
        """One frame to the guest, one frame back."""
        with socket.create_connection(("127.0.0.1", guest_port), timeout=10) as s:
            s.settimeout(patience)
            s.sendall(struct.pack(">I", len(frame)) + frame)
            return tdx_quote.read_frame(s, 69 + 1024)


guest = Guest()
turn = threading.Lock()
waiting = threading.Semaphore(4)
identity = {}


def run(name, alter, challenge):
    frame = build(name, alter, challenge)
    with turn:
        if not guest.alive():
            guest.start()
        before = len(guest.console())
        sent = time.time()
        try:
            reply = guest.ask(frame, 180)
        except (OSError, ValueError) as error:
            # A guest that stopped answering is replaced, so the next visitor finds one that does.
            guest.start()
            raise RuntimeError(f"the guest did not answer ({error}); it has been restarted")
        took = time.time() - sent
        lines = guest.console()[before:]
        if len(reply) == 69 + 1024:
            quote = tdx_quote.get_quote(qgs_socket, reply[69:])
        elif len(reply) == 69:
            quote = b""
        else:
            raise RuntimeError(f"the guest answered with {len(reply)} bytes")
    if alter == "none":
        for line in lines:
            if line.startswith("evm: status ") and " ms" in line:
                catalogue[name]["last_ms"] = int(line.split(", ")[1].split(" ")[0])
    return {"response": reply[:69].hex(), "quote": base64.b64encode(quote).decode(),
            "round_trip_ms": round(took * 1000), "console": lines}


def time_fixtures():
    """Each fixture once, shortest first, so the page can say how long each takes on this boot."""
    for name in sorted(catalogue, key=lambda n: catalogue[n]["size"]):
        try:
            answer = run(name, "none", os.urandom(32))
            agrees = answer["response"] == catalogue[name]["expected"]
            print(f"demo: {name}: {'the fixture answer' if agrees else 'WRONG ' + answer['response']}", flush=True)
        except (RuntimeError, ValueError, OSError) as error:
            print(f"demo: {name}: {error}", flush=True)


def describe_self():
    head = git("rev-parse", "HEAD").strip()
    dirty = bool(git("status", "--porcelain", "--", ".").strip())
    recorded = None
    try:
        with open(os.path.join(work, "measurements.json")) as f:
            recorded = json.load(f)
    except (OSError, ValueError):
        pass
    identity.update({
        "image_sha256": sha256_file(image), "firmware_sha256": sha256_file(firmware),
        "commit": head, "uncommitted_changes": dirty, "recorded": recorded,
        "fixtures": list(catalogue.values())})


# ---- The web server.

# Blocks the builder built and kept with their quotes (builder/shadow), for demo/built.html.
BUILT_FILE = re.compile(r"[0-9]{1,12}\.(req|reply|quote|json)")

def built_index():
    """The blocks kept under the directory, newest first: those with all four files."""
    entries = []
    for path in glob.glob(os.path.join(built_dir, "*.json")):
        name = os.path.basename(path)[:-5]
        if not name.isdigit() or not all(os.path.isfile(os.path.join(built_dir, f"{name}.{e}")) for e in ("req", "reply", "quote")):
            continue
        try:
            with open(path) as f:
                landed = bool(json.load(f).get("landed"))
        except (OSError, ValueError):
            continue
        entries.append({"name": name, "landed": landed})
    return sorted(entries, key=lambda e: -int(e["name"]))


class Handler(BaseHTTPRequestHandler):
    server_version = "evm-demo"
    protocol_version = "HTTP/1.1"

    def log_message(self, format, *args):
        sys.stderr.write("%s %s\n" % (time.strftime("%H:%M:%S"), format % args))

    def send(self, status, kind, body):
        self.send_response(status)
        self.send_header("Content-Type", kind)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.end_headers()
        self.wfile.write(body)

    def json(self, status, value):
        self.send(status, "application/json", json.dumps(value).encode())

    def file(self, name, kind):
        with open(os.path.join(demo, name), "rb") as f:
            self.send(200, kind, f.read())

    def do_GET(self):
        path = self.path.split("?")[0]
        if path == "/":
            self.file("page.html", "text/html; charset=utf-8")
        elif path == "/verify.js":
            self.file("verify.js", "text/javascript; charset=utf-8")
        elif path == "/seal":
            self.file("seal.html", "text/html; charset=utf-8")
        elif path == "/seal.js":
            self.file("seal.js", "text/javascript; charset=utf-8")
        elif path == "/built":
            self.file("built.html", "text/html; charset=utf-8")
        elif path == "/built.js":
            self.file("built.js", "text/javascript; charset=utf-8")
        elif path == "/built/index.json":
            self.json(200, built_index())
        elif path.startswith("/built/") and BUILT_FILE.fullmatch(path[7:]) and \
                os.path.isfile(os.path.join(built_dir, path[7:])):
            with open(os.path.join(built_dir, path[7:]), "rb") as f:
                self.send(200, "application/json" if path.endswith(".json") else "application/octet-stream", f.read())
        elif path == "/api/info":
            self.json(200, dict(identity, guest_up_seconds=round(time.time() - guest.started),
                                guest_boots=guest.boots))
        elif path == "/api/console":
            self.json(200, {"lines": guest.console()[-40:]})
        elif path.startswith("/fixtures/") and path.endswith(".req") and path[10:-4] in requests:
            self.send(200, "application/octet-stream", requests[path[10:-4]])
        else:
            self.json(404, {"error": "no such page"})

    def do_POST(self):
        if self.path == "/api/sealkey":
            # The machine's key for sealed transactions (Evm/Seal.lean), asked for with a report.
            try:
                length = int(self.headers.get("Content-Length", "0"))
                if not 0 < length <= 256:
                    raise ValueError("a request for the key is a small JSON object")
                challenge = bytes.fromhex(json.loads(self.rfile.read(length))["challenge"])
                if len(challenge) != 32:
                    raise ValueError("a challenge is 32 bytes")
            except (ValueError, KeyError, TypeError) as error:
                return self.json(400, {"error": str(error)})
            try:
                with turn:
                    reply = guest.ask(b"JATT1" + challenge + b"JSEK1", 30)
                quote = tdx_quote.get_quote(qgs_socket, reply[32:]) if len(reply) == 32 + 1024 else b""
                return self.json(200, {"key": reply[:32].hex(), "quote": base64.b64encode(quote).decode()})
            except (RuntimeError, ValueError, OSError) as error:
                return self.json(502, {"error": str(error)})
        if self.path != "/api/run":
            return self.json(404, {"error": "no such page"})
        try:
            length = int(self.headers.get("Content-Length", "0"))
            if not 0 < length <= 1024:
                raise ValueError("a request to this page is a small JSON object")
            asked = json.loads(self.rfile.read(length))
            name, alter = asked["fixture"], asked["alter"]
            challenge = bytes.fromhex(asked["challenge"])
            if name not in catalogue or alter not in ("none", "root", "state") or len(challenge) != 32:
                raise ValueError("unknown fixture or alteration, or a challenge that is not 32 bytes")
        except (ValueError, KeyError, TypeError) as error:
            return self.json(400, {"error": str(error)})
        if not waiting.acquire(blocking=False):
            return self.json(503, {"error": "the guest is busy and others are already waiting; try again"})
        try:
            self.json(200, run(name, alter, challenge))
        except (RuntimeError, ValueError, OSError) as error:
            self.json(502, {"error": str(error)})
        finally:
            waiting.release()


def record():
    """Boots the image once more, asks it one question, and writes down the measurements in the quote."""
    os.makedirs(work, exist_ok=True)
    guest.start()
    try:
        answer = run(sorted(catalogue)[0], "none", os.urandom(32))
    finally:
        guest.stop()
    quote = base64.b64decode(answer["quote"])
    if len(quote) < 632 or struct.unpack_from("<HHI", quote) != (4, 2, 0x81):
        sys.exit("record: the quote is not a version 4 TDX quote")
    body = quote[48:632]
    fields = {"MRTD": 136, "RTMR0": 328, "RTMR1": 376, "RTMR2": 424, "RTMR3": 472}
    values = {name: body[at:at + 48].hex() for name, at in fields.items()}
    values["image_sha256"] = sha256_file(image)
    values["firmware_sha256"] = sha256_file(firmware)
    with open(os.path.join(work, "measurements.json"), "w") as f:
        json.dump(values, f, indent=2)
        f.write("\n")
    print(json.dumps(values, indent=2))


def main():
    if not os.path.exists(image):
        sys.exit(f"demo: no {image} (run: scripts/build-efi tdx)")
    if len(sys.argv) == 2 and sys.argv[1] == "record":
        return record()
    if len(sys.argv) != 1:
        sys.exit(__doc__)
    os.makedirs(work, exist_ok=True)
    describe_self()
    guest.start()
    server = ThreadingHTTPServer(("127.0.0.1", listen_port), Handler)
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
    print(f"demo: guest up, page at http://127.0.0.1:{listen_port}/", flush=True)
    threading.Thread(target=time_fixtures, daemon=True).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        guest.stop()


if __name__ == "__main__":
    main()
