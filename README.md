# Zero Sum Pair Checker

A Rust crate that checks if a list of integers contains two numbers that sum to zero.

## Features

- **Efficient Algorithm**: Uses HashSet for O(n) time complexity
- **Alternative Implementation**: Includes brute force O(n²) approach for comparison
- **Pair Finding**: Can return the actual pair of numbers that sum to zero
- **Interactive CLI**: Command-line interface for testing with custom input
- **Comprehensive Tests**: Full test coverage with edge cases

## Usage



### As a Library

Add this to your `Cargo.toml`:

```toml
[dependencies]
zero_sum_checker = "0.1.0"
```

Then use it in your code:

```rust
use zero_sum_checker::has_zero_sum_pair;

fn main() {
    let numbers = vec![1, 2, -1, 4];
    
    if has_zero_sum_pair(&numbers) {
        println!("Found a zero-sum pair!");
    }
}
```

### Running the CLI Program

```bash
cargo run
```

## API Reference

```rust
has_zero_sum_pair(numbers: &[i32]) -> bool
```
Checks if the slice contains two numbers that sum to zero.

- Time Complexity: O(n)
- Space Complexity: O(n)

```rust
find_zero_sum_pair(numbers: &[i32]) -> Option<(i32, i32)>
```
Finds and returns the first pair of numbers that sum to zero.

```rust
has_zero_sum_pair_brute_force(numbers: &[i32]) -> bool
```
Alternative brute force implementation.

- Time Complexity: O(n²)
- Space Complexity: O(1)

## 

Make sure `charon` is installed by running the script

- `sudo apt-get install opam`
- `opam switch create 4.14.0+options`
- `eval $(opam env --switch=4.14.0+options)`

- `scripts/check-charon-install.sh --force`
- `cd charon/`
- `opam install . --deps-only`

- `nix build -L .#charon --extra-experimental-features nix-command --extra-experimental-features flakes`



```
/script

Run `charon` to produce `LLBC` from the Rust code

Another option:
```
nix run github:aeneasverif/aeneas#charon -L --extra-experimental-features nix-command --extra-experimental-features flakes
```



- Run `aeneas` to produce lean file


## To do:

- Setup script to run Aeneas
- Add lean specification
- Add lean proof
- Add lean specification to the documentation