# Zero Sum Pair Checker



## Setup

### Aeneas Installation

Run the automated setup script to install Aeneas and Charon:

```bash
./scripts/setup-aeneas.sh
```

**What setup-aeneas.sh does:**
- Checks for required dependencies (git, OCaml/opam, make, Rust)
- Sets up OCaml 4.14.2 environment with opam
- Installs necessary OCaml packages
- Clones the Aeneas verification tool repository
- Sets up and builds Charon (Rust-to-LLBC compiler)
- Builds Aeneas

After setup, the tools will be available at:
- Charon: `./aeneas/charon/bin/charon`
- Aeneas: `./aeneas/bin/aeneas`

### Lean Toolchain Sync

Keep your Lean versions synchronized:

```bash
./scripts/update-lean-toolchain.sh
```

**What update-lean-toolchain.sh does:**
- Checks if both `verify/lean-toolchain` and `aeneas/backends/lean/lean-toolchain` exist
- Compares Lean versions between the two files
- Updates `verify/lean-toolchain` to match Aeneas if versions differ
- Reports any missing files or version changes

### Lean Code Extraction

Extract Lean verification code from the Rust implementation:

```bash
./scripts/extract-lean.sh
```

**What extract-lean.sh does:**
- Auto-detects crate name from `Cargo.toml`
- Runs Charon to generate LLBC (Low-Level Borrow Checker) intermediate representation
- Runs Aeneas to translate LLBC to Lean code
- Outputs generated Lean files to `verify/Verify/` directory
- Synchronizes Lean toolchain versions

## To do:

- Add lean specification
- Add lean proof
