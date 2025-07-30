use std::collections::HashSet;

/// Checks if a list of integers contains two numbers that sum to zero.
/// 
/// This function uses a HashSet for O(n) time complexity.
/// 
/// # Arguments
/// 
/// * `numbers` - A slice of integers to check
/// 
/// # Returns
/// 
/// * `true` if there are two numbers that sum to zero, `false` otherwise
/// 
/// # Examples
/// 
/// ```
/// use zero_sum_checker::has_zero_sum_pair;
/// 
/// assert_eq!(has_zero_sum_pair(&[1, 2, -1, 4]), true); // 1 + -1 = 0
/// assert_eq!(has_zero_sum_pair(&[1, 2, 3, 4]), false);
/// assert_eq!(has_zero_sum_pair(&[0, 0, 5, 10]), true); // 0 + 0 = 0 
/// assert_eq!(has_zero_sum_pair(&[0]), false); // Only one number
/// ```
pub fn has_zero_sum_pair(numbers: &[i32]) -> bool {
    let mut seen = HashSet::new();
    
    for &num in numbers {
        let complement = -num;
        if seen.contains(&complement) {
            return true;
        }
        seen.insert(num);
    }
    
    false
}

/// Alternative implementation with O(n²) time complexity but O(1) space complexity.
/// 
/// This is a brute force approach that checks all pairs.
/// 
/// # Arguments
/// 
/// * `numbers` - A slice of integers to check
/// 
/// # Returns
/// 
/// * `true` if there are two numbers that sum to zero, `false` otherwise
pub fn has_zero_sum_pair_brute_force(numbers: &[i32]) -> bool {
    for i in 0..numbers.len() {
        for j in (i + 1)..numbers.len() {
            if numbers[i] + numbers[j] == 0 {
                return true;
            }
        }
    }
    false
}

/// Finds and returns the first pair of numbers that sum to zero.
/// 
/// # Arguments
/// 
/// * `numbers` - A slice of integers to check
/// 
/// # Returns
/// 
/// * `Some((a, b))` where a + b = 0, or `None` if no such pair exists
/// 
/// # Examples
/// 
/// ```
/// use zero_sum_checker::find_zero_sum_pair;
/// 
/// assert_eq!(find_zero_sum_pair(&[1, 2, -1, 4]), Some((1, -1)));
/// assert_eq!(find_zero_sum_pair(&[1, 2, 3, 4]), None);
/// ```
pub fn find_zero_sum_pair(numbers: &[i32]) -> Option<(i32, i32)> {
    let mut seen = HashSet::new();
    
    for &num in numbers {
        let complement = -num;
        if seen.contains(&complement) {
            return Some((complement, num));
        }
        seen.insert(num);
    }
    
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_has_zero_sum_pair() {
        // Test cases with zero sum pairs
        assert!(has_zero_sum_pair(&[1, 2, -1, 4]));
        assert!(has_zero_sum_pair(&[5, -3, 2, -2, 8]));
        assert!(has_zero_sum_pair(&[-1, 0, 1, 2]));
        assert!(has_zero_sum_pair(&[3, -3]));
        
        // Test cases without zero sum pairs
        assert!(!has_zero_sum_pair(&[1, 2, 3, 4]));
        assert!(!has_zero_sum_pair(&[1, 2, 4, 8]));
        assert!(!has_zero_sum_pair(&[-1, -2, -3, -4]));
        
        // Edge cases
        assert!(!has_zero_sum_pair(&[])); // Empty array
        assert!(!has_zero_sum_pair(&[5])); // Single element
        assert!(!has_zero_sum_pair(&[0])); // Single zero
        assert!(has_zero_sum_pair(&[0, 0])); // Two zeros
        assert!(!has_zero_sum_pair(&[0, 1, 2])); // Zero with other numbers
    }

    #[test]
    fn test_brute_force_implementation() {
        // Test that both implementations give the same results
        let test_cases = vec![
            vec![1, 2, -1, 4],
            vec![1, 2, 3, 4],
            vec![5, -3, 2, -2, 8],
            vec![-1, 0, 1, 2],
            vec![],
            vec![5],
            vec![0, 0],
        ];

        for test_case in test_cases {
            assert_eq!(
                has_zero_sum_pair(&test_case),
                has_zero_sum_pair_brute_force(&test_case),
                "Implementations disagree on test case: {:?}",
                test_case
            );
        }
    }

    #[test]
    fn test_find_zero_sum_pair() {
        // Test finding actual pairs
        match find_zero_sum_pair(&[1, 2, -1, 4]) {
            Some((a, b)) => assert_eq!(a + b, 0),
            None => panic!("Should have found a pair"),
        }

        match find_zero_sum_pair(&[5, -3, 2, -2, 8]) {
            Some((a, b)) => assert_eq!(a + b, 0),
            None => panic!("Should have found a pair"),
        }

        // Test cases with no pairs
        assert_eq!(find_zero_sum_pair(&[1, 2, 3, 4]), None);
        assert_eq!(find_zero_sum_pair(&[]), None);
        assert_eq!(find_zero_sum_pair(&[5]), None);
    }
}