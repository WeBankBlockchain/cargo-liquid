#![cfg_attr(not(feature = "std"), no_std)]

use liquid_lang as liquid;

#[liquid::collaboration]
mod {{name}} {
    /// Unit tests in Rust are normally defined within such a `#[cfg(test)]`
    /// module and test functions are marked with a `#[test]` attribute.
    /// The below code is technically just normal Rust code.
    #[cfg(test)]
    mod tests {
        /// Imports all the definitions from the outer scope so we can use them here.
        use super::*;
    }
}