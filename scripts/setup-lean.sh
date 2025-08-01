#!/bin/bash

# Lean Project Setup Script
# This script sets up dependencies and builds the Lean project
# Note: Lake automatically installs Lean via elan if needed

set -e  # Exit on any error

echo "=== Lean Project Setup Script ==="
echo

# Get the absolute path to the script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
VERIFY_DIR="$PROJECT_ROOT/verify"

echo "Project root: $PROJECT_ROOT"
echo "Verify directory: $VERIFY_DIR"
echo

# Check if verify directory exists
if [ ! -d "$VERIFY_DIR" ]; then
    echo "Error: verify directory not found at $VERIFY_DIR"
    exit 1
fi

# Check if lakefile.toml exists
if [ ! -f "$VERIFY_DIR/lakefile.toml" ]; then
    echo "Error: lakefile.toml not found in $VERIFY_DIR"
    echo "This doesn't appear to be a valid Lean project."
    exit 1
fi

# Function to check for curl (needed for elan auto-install)
check_prerequisites() {
    echo "Checking prerequisites..."
    
    # Check if curl is available (needed for elan auto-install)
    if ! command -v curl &> /dev/null; then
        echo "Warning: curl not found. If Lean/elan needs to be installed, you may need curl."
        echo "Consider installing curl first: sudo apt install curl (Ubuntu/Debian) or brew install curl (macOS)"
    else
        echo "✓ curl is available"
    fi
    
    echo
}

# Function to setup the project
setup_project() {
    echo "Setting up Lean project..."
    
    cd "$VERIFY_DIR"
    
    # Lake will automatically install Lean via elan if needed based on lean-toolchain file
    echo "Lake will automatically install/use Lean based on lean-toolchain file:"
    if [ -f "lean-toolchain" ]; then
        cat lean-toolchain
    else
        echo "Warning: No lean-toolchain file found"
    fi
    echo
    
    # Update dependencies
    echo "Updating dependencies..."
    lake update
    
    # Download precompiled caches (including mathlib)
    echo "Downloading dependency caches..."
    lake exe cache get || {
        echo "Warning: Cache download failed, but continuing with build..."
        echo "This may result in longer compilation times."
    }
    
    # Build the project
    echo "Building project..."
    lake build
    
    echo "✓ Lean project setup complete"
    echo
}

# Function to verify the setup
verify_setup() {
    echo "Verifying setup..."
    
    cd "$VERIFY_DIR"
    
    # Check if we can build the main target
    if lake build Verify; then
        echo "✓ Project builds successfully"
    else
        echo "Warning: Build verification failed"
        echo "Check for compilation errors in your Lean files"
        return 1
    fi
    
    # Show Lean version if available
    if command -v lean &> /dev/null; then
        echo "✓ Lean version: $(lean --version)"
    fi
    
    echo
}

# Main execution
main() {
    echo "Starting Lean project setup..."
    echo "Note: Lake will automatically install Lean/elan if needed"
    echo
    
    check_prerequisites
    setup_project
    verify_setup
    
    echo "=== Setup Complete! ==="
    echo
    echo "Your Lean project in $VERIFY_DIR is ready!"
    echo
    echo "Useful commands:"
    echo "  cd $VERIFY_DIR"
    echo "  lake build              # Build the project"
    echo "  lake exe cache get      # Download/update caches"
    echo "  lake update             # Update dependencies"
    echo "  lake clean              # Clean build artifacts"
    echo
    echo "If this was your first time:"
    echo "- Lake automatically installed Lean via elan"
    echo "- You may need to restart your shell to use 'lean' command directly"
}

# Run the main function
main "$@"