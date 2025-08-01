# Rust ❤️ Lean - Playground 

This repository demonstrates a complete toolchain for formally verifying Rust code using Lean 4. The project consists of two main components: the `src/` folder containing a Rust crate, and the `verify/` folder containing a Lean project that proves properties about the Rust code.

## What's great about this approach

This verification workflow offers several key advantages:

- **Automated verification**: The entire verification process is validated through CI workflows, ensuring proofs remain valid as code evolves
- **Rich mathematical foundation**: Lean's extensive mathematical library (mathlib) provides powerful tools for expressing and proving complex properties about program behaviour
- **Type-safe extraction**: The Aeneas tool translates Rust code to Lean while preserving semantic correctness

## The dreamed of future

Several enhancements would make this toolchain even more powerful:

- **Integrated specs**: Rust docs could directly embed Lean specifications for public APIs, with verification status checked during documentation generation. This would allow developers to read function documentation and immediately understand proven behavioural guarantees without examining source code.
- **Specs which are easy to parse for humans**: At the moment the specs are written in Lean which provides a relatively easy to read presentation. However a DSL could improve this is some contexts.
- **Expanded Rust support**: Enhanced Aeneas capabilities to handle more Rust language features and patterns
- **Even more proof automation**: Additional theorems, simplification procedures, and tactics specifically designed for common verification goals in systems programming

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

Keep your Lean versions synchronised:

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
- Synchronises Lean toolchain versions

## To do:

- Add lean specification
- Add lean proof
