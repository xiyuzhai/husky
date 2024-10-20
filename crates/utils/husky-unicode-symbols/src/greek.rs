// Lowercase letters
pub const GREEK_LETTER_LOWERCASE_ALPHA: char = 'α';
pub const GREEK_LETTER_LOWERCASE_BETA: char = 'β';
pub const GREEK_LETTER_LOWERCASE_GAMMA: char = 'γ';
pub const GREEK_LETTER_LOWERCASE_DELTA: char = 'δ';
pub const GREEK_LETTER_LOWERCASE_EPSILON: char = 'ε';
pub const GREEK_LETTER_LOWERCASE_ZETA: char = 'ζ';
pub const GREEK_LETTER_LOWERCASE_ETA: char = 'η';
pub const GREEK_LETTER_LOWERCASE_THETA: char = 'θ';
pub const GREEK_LETTER_LOWERCASE_IOTA: char = 'ι';
pub const GREEK_LETTER_LOWERCASE_KAPPA: char = 'κ';
pub const GREEK_LETTER_LOWERCASE_LAMBDA: char = 'λ';
pub const GREEK_LETTER_LOWERCASE_MU: char = 'μ';
pub const GREEK_LETTER_LOWERCASE_NU: char = 'ν';
pub const GREEK_LETTER_LOWERCASE_XI: char = 'ξ';
pub const GREEK_LETTER_LOWERCASE_OMICRON: char = 'ο';
pub const GREEK_LETTER_LOWERCASE_PI: char = 'π';
pub const GREEK_LETTER_LOWERCASE_RHO: char = 'ρ';
pub const GREEK_LETTER_LOWERCASE_FINAL_SIGMA: char = 'ς';
pub const GREEK_LETTER_LOWERCASE_SIGMA: char = 'σ';
pub const GREEK_LETTER_LOWERCASE_TAU: char = 'τ';
pub const GREEK_LETTER_LOWERCASE_UPSILON: char = 'υ';
pub const GREEK_LETTER_LOWERCASE_PHI: char = 'φ';
pub const GREEK_LETTER_LOWERCASE_CHI: char = 'χ';
pub const GREEK_LETTER_LOWERCASE_PSI: char = 'ψ';
pub const GREEK_LETTER_LOWERCASE_OMEGA: char = 'ω';

// Uppercase letters
pub const GREEK_LETTER_UPPERCASE_ALPHA: char = 'Α';
pub const GREEK_LETTER_UPPERCASE_BETA: char = 'Β';
pub const GREEK_LETTER_UPPERCASE_GAMMA: char = 'Γ';
pub const GREEK_LETTER_UPPERCASE_DELTA: char = 'Δ';
pub const GREEK_LETTER_UPPERCASE_EPSILON: char = 'Ε';
pub const GREEK_LETTER_UPPERCASE_ZETA: char = 'Ζ';
pub const GREEK_LETTER_UPPERCASE_ETA: char = 'Η';
pub const GREEK_LETTER_UPPERCASE_THETA: char = 'Θ';
pub const GREEK_LETTER_UPPERCASE_IOTA: char = 'Ι';
pub const GREEK_LETTER_UPPERCASE_KAPPA: char = 'Κ';
pub const GREEK_LETTER_UPPERCASE_LAMBDA: char = 'Λ';
pub const GREEK_LETTER_UPPERCASE_MU: char = 'Μ';
pub const GREEK_LETTER_UPPERCASE_NU: char = 'Ν';
pub const GREEK_LETTER_UPPERCASE_XI: char = 'Ξ';
pub const GREEK_LETTER_UPPERCASE_OMICRON: char = 'Ο';
pub const GREEK_LETTER_UPPERCASE_PI: char = 'Π';
pub const GREEK_LETTER_UPPERCASE_RHO: char = 'Ρ';
pub const GREEK_LETTER_UPPERCASE_FINAL_SIGMA: char = 'Σ';
pub const GREEK_LETTER_UPPERCASE_SIGMA: char = 'Σ';
pub const GREEK_LETTER_UPPERCASE_TAU: char = 'Τ';
pub const GREEK_LETTER_UPPERCASE_UPSILON: char = 'Υ';
pub const GREEK_LETTER_UPPERCASE_PHI: char = 'Φ';
pub const GREEK_LETTER_UPPERCASE_CHI: char = 'Χ';
pub const GREEK_LETTER_UPPERCASE_PSI: char = 'Ψ';
pub const GREEK_LETTER_UPPERCASE_OMEGA: char = 'Ω';

pub fn is_greek(c: char) -> bool {
    let c = c as u32;
    if c >= 0x0370 && c <= 0x03FF {
        true
    } else if c >= 0x1F00 && c <= 0x1FFF {
        true
    } else {
        false
    }
}
