# Rust ❤️ Lean - Playground 

This repo is a playground for verifying Rust code using Lean. 
the folder src is the source code of a rust crate
the folder verify is a lean project

**Why this is great**
The verification is confirmed by a ci workflow
Lean means that there is massive amount of mathematics available for stating and proving properties of functions. 

**What would improve this:**
the rust docs can include statements from lean which specify the behaviour of the public api of the crate and the validity of these lean statements is verified during the production of the docs. I.e., one can read the docs of the rust crate and can know that the function satisfies the stated specs without looking any further into the source code. 
aeneas supporting some of the parts of rust which are not yet supported
more theorems/simprocs/etc available to quickly dispatch common goals seen if this application of lean.

## Setup

### Compile Rust code

Assuming that Rust is installed, run:
```bash
cargo build
```

### Aeneas Installation

Run the automated setup script to install Aeneas and Charon:

```bash
bash scripts/setup-aeneas.sh
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

### Lean Project Setup

Set up the Lean project with all dependencies:

```bash
bash scripts/setup-lean.sh
```

**What setup-lean.sh does:**
- Lets Lake automatically install Lean/elan if needed (based on `verify/lean-toolchain`)
- Updates project dependencies with `lake update`
- Downloads mathlib cache for faster builds with `lake exe cache get`
- Builds the Lean project in the `verify/` directory
- Verifies the setup by testing compilation

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
bash scripts/extract-lean.sh
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
