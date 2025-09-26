use subtle::{Choice, ConditionallySelectable};
use core::ops::{Index, IndexMut};

/// `L` is the order of base point, i.e. 2^252 + 27742317777372353535851937790883648493
pub const L: Scalar52 = Scalar52([
    0x0002631a5cf5d3ed,
    0x000dea2f79cd6581,
    0x000000000014def9,
    0x0000000000000000,
    0x0000100000000000,
]);

pub struct Scalar52(pub [u64; 5]);

impl Index<usize> for Scalar52 {
    type Output = u64;
    fn index(&self, _index: usize) -> &u64 {
        &(self.0[_index])
    }
}

impl IndexMut<usize> for Scalar52 {
    fn index_mut(&mut self, _index: usize) -> &mut u64 {
        &mut (self.0[_index])
    }
}

impl Scalar52 {
    /// The scalar \\( 0 \\).
    pub const ZERO: Scalar52 = Scalar52([0, 0, 0, 0, 0]);

    pub(crate) fn conditional_add_l(&mut self, condition: Choice) -> u64 {
        let mut carry: u64 = 0;
        let mask = (1u64 << 52) - 1;

        for i in 0..5 {
            let addend = u64::conditional_select(&0, &L[i], condition);
            carry = (carry >> 52) + self[i] + addend;
            self[i] = carry & mask;
        }

        carry
    }

    /// Compute `a - b` (mod l)
    pub fn sub(a: &Scalar52, b: &Scalar52) -> Scalar52 {
        let mut difference = Scalar52::ZERO;
        let mask = (1u64 << 52) - 1;

        // a - b
        let mut borrow: u64 = 0;
        for i in 0..5 {
            borrow = a[i].wrapping_sub(b[i] + (borrow >> 63));
            difference[i] = borrow & mask;
        }

        // conditionally add l if the difference is negative
        difference.conditional_add_l(Choice::from((borrow >> 63) as u8));
        difference
    }
}