use zero_sum_checker::{has_zero_sum_pair, find_zero_sum_pair};
use std::io::{self, Write};

fn main() {
    println!("Zero Sum Pair Checker");
    println!("====================");
    
    // Example with predefined lists
    let test_cases = vec![
        vec![1, 2, -1, 4],
        vec![1, 2, 3, 4],
        vec![5, -3, 2, -2, 8],
        vec![-10, 15, 3, -3, 7],
        vec![0, 1, 2, 3],
        vec![],
        vec![42],
    ];

    println!("\nTesting predefined lists:");
    for (i, numbers) in test_cases.iter().enumerate() {
        println!("\nTest case {}: {:?}", i + 1, numbers);
        
        if has_zero_sum_pair(numbers) {
            println!("✓ Contains a zero-sum pair");
            if let Some((a, b)) = find_zero_sum_pair(numbers) {
                println!("  Found pair: {} + {} = 0", a, b);
            }
        } else {
            println!("✗ No zero-sum pair found");
        }
    }

    // Interactive mode
    println!("\n{}", "=".repeat(50));
    println!("Interactive mode - Enter your own numbers!");
    println!("Enter integers separated by spaces (or 'quit' to exit):");

    loop {
        print!("\n> ");
        io::stdout().flush().unwrap();

        let mut input = String::new();
        match io::stdin().read_line(&mut input) {
            Ok(_) => {
                let input = input.trim();
                
                if input.eq_ignore_ascii_case("quit") || input.eq_ignore_ascii_case("q") {
                    println!("Goodbye!");
                    break;
                }

                if input.is_empty() {
                    continue;
                }

                // Parse the input
                let numbers: Result<Vec<i32>, _> = input
                    .split_whitespace()
                    .map(|s| s.parse::<i32>())
                    .collect();

                match numbers {
                    Ok(nums) => {
                        println!("Checking: {:?}", nums);
                        
                        if has_zero_sum_pair(&nums) {
                            println!("✓ Contains a zero-sum pair!");
                            if let Some((a, b)) = find_zero_sum_pair(&nums) {
                                println!("  Found pair: {} + {} = 0", a, b);
                            }
                        } else {
                            println!("✗ No zero-sum pair found");
                        }
                    }
                    Err(_) => {
                        println!("Error: Please enter valid integers separated by spaces");
                        println!("Example: 1 2 -1 4");
                    }
                }
            }
            Err(error) => {
                println!("Error reading input: {}", error);
                break;
            }
        }
    }
}