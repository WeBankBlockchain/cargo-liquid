#![cfg_attr(not(feature = "std"), no_std)]

use liquid::storage;
use liquid_lang as liquid;

#[liquid::contract]
mod {{name}} {
    use super::*;

    /// Defines the state variables of your contract.
    #[liquid(storage)]
    struct {{camel_name}} {}

    /// Defines the methods of your contract.
    #[liquid(methods)]
    impl {{camel_name}} {
        /// Defines the constructor which will be executed automatically when the contract is
        /// under deploying. Usually constructor is used to initialize state variables.
        /// 
        /// # Note
        /// 1. The name of constructor must be `new`;
        /// 2. The receiver of constructor must be `&mut self`;
        /// 3. The visibility of constructor must be `pub`.
        /// 4. The constructor should return nothing.
        /// 5. If you forget to initialize state variables, you 
        ///    will be trapped in an runtime-error for attempting 
        ///    to visit uninitialized storage.
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