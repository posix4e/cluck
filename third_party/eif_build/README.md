# The versions AWS's image builder is built from

`eif_build` packs a kernel image into the enclave image file a Nitro Enclave loads, and writes down the
measurements. It is AWS's, from https://github.com/aws/aws-nitro-enclaves-image-format, and CI builds it from
source at release v0.8.1 (commit `6a5fdad1adb981769da31c51377fb82efbb27d97`).

That release does not say which versions of its 271 dependencies to build with, so a build picks whatever is
newest that day. `Cargo.lock` here fixes them: CI copies it into the source before building and builds with
`--locked`, with a fixed version of the Rust compiler. It was made with `cargo generate-lockfile` in that
source on 2026-11-15 and has not been edited.

To move to a newer release: change the tag and the commit in `.github/workflows/ci.yml`, run
`cargo generate-lockfile` in the new source, and replace the file.
