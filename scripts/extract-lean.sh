#!/bin/bash

# Extract Lean Script
# Uses Charon to generate LLBC, then Aeneas to produce Lean files

set -e  # Exit on any error

echo "=== Extracting Lean Files from Rust Code ==="
echo

# Configuration - auto-detect crate name from Cargo.toml
CRATE_NAME=$(grep '^name = ' Cargo.toml | sed 's/name = "\(.*\)"/\1/' | tr '-' '_')
CHARON_BIN="./aeneas/charon/bin/charon"
AENEAS_BIN="./aeneas/bin/aeneas"
OUTPUT_DIR="verify/Verify"

if [ -z "$CRATE_NAME" ]; then
    echo "Error: Could not determine crate name from Cargo.toml"
    exit 1
fi

LLBC_FILE="${CRATE_NAME}.llbc"

# Check if required tools exist
check_tools() {
    echo "Checking required tools..."
    
    if [ ! -f "$CHARON_BIN" ]; then
        echo "Error: Charon not found at $CHARON_BIN"
        echo "Run the setup script first: ./scripts/setup-aeneas.sh"
        exit 1
    fi
    
    if [ ! -f "$AENEAS_BIN" ]; then
        echo "Error: Aeneas not found at $AENEAS_BIN"
        echo "Run the setup script first: ./scripts/setup-aeneas.sh"
        exit 1
    fi
    
    echo "✓ Tools found"
    echo
}

# Generate LLBC file using Charon
generate_llbc() {
    echo "Step 1: Generating LLBC file with Charon..."
    
    # Remove existing LLBC file if it exists
    if [ -f "$LLBC_FILE" ]; then
        echo "Removing existing $LLBC_FILE"
        rm "$LLBC_FILE"
    fi
    
    # Run Charon to generate LLBC
    echo "Running: $CHARON_BIN cargo --preset=aeneas"
    "$CHARON_BIN" cargo --preset=aeneas
    
    if [ ! -f "$LLBC_FILE" ]; then
        echo "Error: Failed to generate $LLBC_FILE"
        exit 1
    fi
    
    echo "✓ LLBC file generated: $LLBC_FILE"
    echo
}

# Generate Lean files using Aeneas
generate_lean() {
    echo "Step 2: Generating Lean files with Aeneas..."
    
    # Create output directory if it doesn't exist
    mkdir -p "$OUTPUT_DIR"
    
    # Run Aeneas to generate Lean files
    echo "Running: $AENEAS_BIN -backend lean -dest $OUTPUT_DIR $LLBC_FILE"
    "$AENEAS_BIN" -backend lean -dest "$OUTPUT_DIR" "$LLBC_FILE"
    
    echo "✓ Lean files generated in $OUTPUT_DIR"
    echo
}

# Update lean-toolchain to match Aeneas
sync_toolchain() {
    echo "Step 3: Synchronizing Lean toolchain..."
    
    if [ -f "./scripts/update-lean-toolchain.sh" ]; then
        ./scripts/update-lean-toolchain.sh
    else
        echo "⚠ Toolchain sync script not found, skipping"
    fi
    
    echo
}

# Main execution
main() {
    echo "Working directory: $(pwd)"
    echo "Extracting Lean files for crate: $CRATE_NAME"
    echo
    
    check_tools
    generate_llbc
    generate_lean
    sync_toolchain
    
    echo "=== Extraction Complete! ==="
    echo
    echo "Generated files:"
    echo "- LLBC file: $LLBC_FILE"
    echo "- Lean files: $OUTPUT_DIR/"
    echo
    echo "Next steps:"
    echo "1. Review the generated Lean files in $OUTPUT_DIR/"
    echo "2. Add specifications and proofs"
    echo "3. Build with: cd verify && lake build"
}

# Run the main function
main "$@"