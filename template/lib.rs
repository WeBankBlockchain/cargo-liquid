#![cfg_attr(not(feature = "std"), no_std)]

use liquid_lang as liquid;

#[liquid::contract(version = "0.1.0")]
mod {{name}} {
    use liquid_core::storage;

    /// Defines the storage of your contract.
    #[liquid(storage)]
    struct {{camel_name}} {
        /// Add new fields to the below struct in order
        /// to add new static storage fields to your contract.
    }

    /// Defines the methods of your contract.
    #[liquid(methods)]
    struct {{camel_name}} {
        /// Constructor that initializes your storage.
        /// The name of constructor must be `new`;
        /// The receiver of constructor must be `&mut self`.
        /// The visibility of constructor must be `pub`.
        pub fn new(&mut self) {}
    }

    /// Unit tests in Rust are normally defined within such a `#[cfg(test)]`
    /// module and test functions are marked with a `#[test]` attribute.
    /// The below code is technically just normal Rust code.
    #[cfg(test)]
    mod tests {
        /// Imports all the definitions from the outer scope so we can use them here.
        use super::*;
    }
}