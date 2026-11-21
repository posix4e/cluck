"""The stand-in relay's certificates, for the shadow image and its tests.

The shadow image (`EfiShadow.lean`) trusts one root, for one name, `relay.test`, at the host's own address.
That root's key is made from a phrase printed here, so anyone can sign for it: it stands for nothing, and
no image that is meant to keep a secret trusts it. `scripts/relay-roots` puts the root's certificate into
`Evm/Roots.lean`; this module makes the same key again and signs a certificate for a server with it."""
import datetime, hashlib
from cryptography import x509
from cryptography.x509.oid import NameOID
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ec

PHRASE = b"a root for stand-in relays, its key known to everyone"
NAME = "relay.test"
PORT = 5443
ORDER = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
ROOT_NAME = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, "a stand-in root, its key known to everyone")])

def root_key():
    return ec.derive_private_key(int.from_bytes(hashlib.sha256(PHRASE).digest(), "big") % (ORDER - 1) + 1, ec.SECP256R1())

def root_certificate():
    """The root's certificate, as DER. Its signature differs each time it is made; its name and key do not,
    and those are all that is read of a root."""
    key = root_key()
    return (x509.CertificateBuilder().subject_name(ROOT_NAME).issuer_name(ROOT_NAME).public_key(key.public_key())
            .serial_number(1).not_valid_before(datetime.datetime(2026, 1, 1, tzinfo=datetime.timezone.utc))
            .not_valid_after(datetime.datetime(2046, 1, 1, tzinfo=datetime.timezone.utc))
            .add_extension(x509.BasicConstraints(ca=True, path_length=None), critical=True)
            .sign(key, hashes.SHA256()).public_bytes(serialization.Encoding.DER))

def server(names=(NAME,), days=30):
    """A key and a certificate for a server of these names, good from yesterday: both as PEM."""
    key = ec.generate_private_key(ec.SECP256R1())
    now = datetime.datetime.now(datetime.timezone.utc)
    certificate = (x509.CertificateBuilder()
                   .subject_name(x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, names[0])])).issuer_name(ROOT_NAME)
                   .public_key(key.public_key()).serial_number(x509.random_serial_number())
                   .not_valid_before(now - datetime.timedelta(days=1)).not_valid_after(now + datetime.timedelta(days=days))
                   .add_extension(x509.BasicConstraints(ca=False, path_length=None), critical=True)
                   .add_extension(x509.SubjectAlternativeName([x509.DNSName(n) for n in names]), critical=False)
                   .sign(root_key(), hashes.SHA256()))
    return (key.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8, serialization.NoEncryption()),
            certificate.public_bytes(serialization.Encoding.PEM))
