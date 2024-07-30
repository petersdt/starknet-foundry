use crate as conversions; // trick for CairoDeserialize macro
use cairo_serde_macros::{CairoDeserialize, CairoSerialize};

#[derive(CairoDeserialize, CairoSerialize)]
pub struct CairoU256 {
    low: u128,
    high: u128,
}

impl CairoU256 {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        Self {
            low: u128::from_be_bytes(bytes[16..32].try_into().unwrap()),
            high: u128::from_be_bytes(bytes[0..16].try_into().unwrap()),
        }
    }

    pub fn to_be_bytes(&self) -> [u8; 32] {
        let mut result = [0; 32];

        result[16..].copy_from_slice(&self.low.to_be_bytes());
        result[..16].copy_from_slice(&self.high.to_be_bytes());

        result
    }
}
