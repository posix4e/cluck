# Contributing

Rules for anyone working on this repository, people and coding assistants alike. Each one is here because it
was got wrong once.

## Commits

- **Authors are people.** A commit's author and committer are the person responsible for it, and its message
  ends where its text ends. No `Co-Authored-By:` line for a tool or an assistant, no "generated with" line, no
  assistant's name anywhere in a commit, a tag, a pull request title or body, or a code comment. GitHub shows
  such a trailer as a co-author of the repository, and it stays in history.
- **One commit until there is a releasable artifact, then small commits.** Until the repository produces
  something that could be released (an enclave image that runs in a real Nitro Enclave and whose attestation
  verifies, see `TODO.md`), it is a single commit. New work is folded into that commit, not stacked on top
  of it: amend, then push with `--force-with-lease`. Do not push after every small step. Once that artifact
  exists, history starts: small commits, one change each, each building and passing its checks on its own,
  and no more rewriting what has been pushed.
- **Write the message for someone reading it cold.** Say what the repository now does and what it does not.
  Do not narrate the order things were tried in.

## Before pushing

- Run the build and check that it actually succeeded: look at `lake build`'s exit status, not at filtered
  output.
- Run what CI runs (`.github/workflows/ci.yml`). The checks that need no Linux run anywhere:

  ```
  lake build
  .lake/build/bin/demo-test && .lake/build/bin/kernel-test && .lake/build/bin/vsock-test && .lake/build/bin/nsm-test
  .lake/build/bin/sim-test .lake/build/bin/demo-sim
  python3 verify/test-verify-attestation     # needs verify/requirements.txt installed
  for exe in rt-test big-test demo-sim; do scripts/build-min "$exe"; done
  .lake/build/bin/rt-test | cmp - <(.lake/build/bin/rt-test-min)
  .lake/build/bin/big-test | cmp - <(.lake/build/bin/big-test-min)
  .lake/build/bin/sim-test .lake/build/bin/demo-sim-min
  scripts/build-bare rt-test
  for shape in elf bzImage long.bzImage; do
    scripts/run-qemu .lake/build/bare/rt-test.$shape | cmp - <(.lake/build/bin/rt-test)
    scripts/check-protection $shape
  done
  ```

- Say what was not run. "Builds" is not "boots", and "boots under QEMU" is not "boots in an enclave".

## Documents

- **Status goes in `TODO.md`**, not in a README. A README says what something is and how to use it.
- **`THREAT_MODEL.md` changes with the code.** A change that adds an input, a device, a secret or a piece of
  C says there what it exposes and what stands in the way, in the same commit.
- Comments say why, in plain words, for a reader who was not there.

## Continuous integration

- CI runs on Linux only: the image is x86-64 with no operating system, and a macOS job re-checks a developer's
  laptop and costs ten times as much. Do not add one.
- Which Linux is a setting, not a change to the workflow: the repository variable `SILO_RUNNER` names the
  runners' label, and without it jobs go to GitHub's `ubuntu-24.04`. Self-hosted runners belong in a
  virtual machine of their own, set up as GitHub's are (the same packages, sudo, a vsock device), so that
  nothing a job does, such as ending every QEMU it can see, reaches anything else on that machine. Do not
  register runners without asking.
- Kept tools (QEMU, the image builder, the vsock daemon) are kept per kind of runner: a copy saved on one
  does not unpack to the right place on another. And the job that boots machines runs one at a time there.
- A machine that is not thrown away after each job can hide what a clean one would show. The step that
  builds the images twice starts from nothing each time; before a release, run the workflow once on GitHub's
  runners (clear the variable) and compare the measurements.

## Code

- **All logic is Lean.** C and assembly exist only underneath it (`rt/`, `boot/`) and never interpret bytes
  that came from the parent instance.
- **Nothing the parent runs goes into the enclave.** No Linux, no C library, no library of someone else's
  for parsing or cryptography. The enclave and the machine beside it must not be breakable by the same flaw
  (THREAT_MODEL.md, "One flaw is not enough"), so a new dependency in the image needs its case made there.
- **Proofs stay out of what runs.** A file of proofs is imported by other proofs, never by code that ends up in an
  image: importing one links Lean's own tooling into the enclave. What a theorem assumes is a hypothesis in
  its statement, and the documents that cite it say so.
- **The runtime provides what is measured, no more.** A new runtime function is justified by
  `scripts/measure-runtime` showing compiled Lean needs it, and is held to Lean's own runtime by the
  differential tests.
- **Nothing that is not there may pass for something that is.** A missing piece stops the machine by name.
- **Secrets never pass through `Nat` or `Int`**, whose arithmetic takes time that depends on the values.

## Things that cost money or touch accounts

- Ask before launching anything in AWS, and say what it costs.
- Ask before downloading large files, installing software, or creating accounts, keys, roles or runners.
