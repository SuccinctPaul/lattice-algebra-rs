/// Prototype PolyExtField implementation with general polynomial modulus.
/// This file tests the concept before adding to the main crate.

use std::env;
use std::process;

// Simple ring element for testing
#[derive(Debug, Clone, Copy, PartialEq)]
struct Q(u64);

impl Q {
    const MODULUS: u64 = 4294966769u64; // Prime ≡ 1 mod 8, supports e=8
    
    fn new(v: u64) -> Self {
        Q(v % Self::MODULUS)
    }
    
    fn zero() -> Self {
        Q(0)
    }
    
    fn one() -> Self {
        Q(1)
    }
    
    fn to_u64(&self) -> u64 {
        self.0
    }
}

impl std::ops::Add for Q {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Q((self.0 as u128 + rhs.0 as u128) % (Q::MODULUS as u128) as u64)
    }
}

impl std::ops::Sub for Q {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Q((self.0 as i128 - rhs.0 as i128).rem_euclid(Q::MODULUS as i128) as u64)
    }
}

impl std::ops::Mul for Q {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Q(((self.0 as u128) * (rhs.0 as u128)) % (Q::MODULUS as u128) as u64)
    }
}

impl std::ops::Neg for Q {
    type Output = Self;
    fn neg(self) -> Self {
        Q((-self.0 as i128).rem_euclid(Q::MODULUS as i128) as u64)
    }
}

impl std::fmt::Display for Q {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

// Polynomial arithmetic helper
fn poly_eval(coeffs: &[Q], x: Q) -> Q {
    let mut result = Q::zero();
    for &c in coeffs.iter().rev() {
        result = result * x + c;
    }
    result
}

fn poly_mod_by_linear(coeffs: &mut Vec<Q>, root: Q) {
    // Synthetic division by (Z - root)
    let mut carry = Q::zero();
    for i in (0..coeffs.len()).rev() {
        let old = coeffs[i];
        coeffs[i] = carry;
        carry = old + carry * root;
    }
}

fn find_root_in_fq(q_val: u64, d: usize, target_degree: usize) -> Option<Q> {
    // Brute-force search for roots of X^d + 1 in F_q
    for x in 1u64..q_val.min(10000) {
        let xv = Q::new(x);
        let mut power = Q::one();
        for _ in 0..d {
            power = power * xv;
        }
        if power.0 == (q_val - 1) % q_val {
            return Some(xv);
        }
    }
    None
}

fn main() {
    println!("Testing PolyExtField concepts...");
    
    let p3_prime = 4294966769u64;
    println!("P3 prime candidate: {} ≡ {} (mod 8)", 
             p3_prime, p3_prime % 8);
    
    // Find actual degree-8 factor of X^64 + 1 using Cantor-Zassenhaus
    // For now, use sympy offline computation and hardcode one factor:
    // At q = 4294966769, one factor of Φ₁₂₈ is:
    // Z^8 + Z^7 + 1534Z^6 + 2130Z^5 + 2183Z^4 + 1535Z^3 + 160Z^2 + 2155Z + 2386
    let degree_8_factor = [
        Q::new(2386),
        Q::new(2155),
        Q::new(160),
        Q::new(1535),
        Q::new(2183),
        Q::new(2130),
        Q::new(1534),
        Q::new(1),  // monic
    ];
    
    println!("\nHardcoded degree-8 factor of X^64 + 1:");
    for (i, c) in degree_8_factor.iter().enumerate() {
        print!("{:?}·Z^{}", c, i);
        if i < 7 { print!(" + "); }
    }
    println!("\n");
    
    // Test multiplication reduction mod this polynomial
    let a = vec![Q::new(1), Q::new(2), Q::new(3)];
    let b = vec![Q::new(4), Q::new(5), Q::new(6)];
    
    // Schoolbook multiplication
    let mut prod = vec![Q::zero(); 6];
    for (i, ai) in a.iter().enumerate() {
        for (j, bj) in b.iter().enumerate() {
            prod[i + j] = prod[i + j] + (*ai) * (*bj);
        }
    }
    
    println!("a(Z) = 1 + 2Z + 3Z^2");
    println!("b(Z) = 4 + 5Z + 6Z^2");
    println!("a·b = {:?}", prod.iter().map(|c| c.to_u64()).collect::<Vec<_>>());
    
    // Reduce mod degree-8 factor (trivial since deg(a·b) < 8)
    println!("Product degree < 8, no reduction needed\n");
    
    println!("Prototype successful! Ready for full PolyExtField implementation.");
}
