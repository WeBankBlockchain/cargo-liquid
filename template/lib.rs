#![cfg_attr(not(feature = "std"), no_std)]

use liquid_lang as liquid;

#[liquid::contract(version = "0.1.0")]
mod {{name}} {
    use liquid_core::storage;

    /// Defines the storage of your contract.
    #[liquid(storage)]
    struct {{camel_name}} {
        // Add new fields here in order to define
        // static storage fields for your contract.

        /// In this simple example, we stores a single `String` value on the storage
        name: storage::Value<String>,
    }

    /// Defines the methods of your contract.
    #[liquid(methods)]
    impl {{camel_name}} {
        /// Constructor that initializes your storage.
        /// # Note
        /// 1. The name of constructor must be `new`;
        /// 2. The receiver of constructor must be `&mut self`;
        /// 3. The visibility of constructor must be `pub`.
        /// 4. The constructor should return nothing.
        pub fn new(&mut self) {
            // Do *NOT* forget to initialize you storage fields before used them,
            // otherwise you will be trapped in an runtime-error for attempting 
            // to visit uninitialized storage.
            let name = "{{name}}";
            self.name.initialize(String::from(name));
        }

        /// Simply gets the name stored in the storage.
        pub fn get(&self) -> String {
            self.name.clone()
        }

        /// Simply sets a new name to the storage.
        pub fn set(&mut self, name: String) {
            *self.name = name;
        }
    }

    /// Unit tests in Rust are normally defined within such a `#[cfg(test)]`
    /// module and test functions are marked with a `#[test]` attribute.
    /// The below code is technically just normal Rust code.
    #[cfg(test)]
    mod tests {
        /// Imports all the definitions from the outer scope so we can use them here.
        use super::*;

        /// We test if the constructor and `get` method do their job.
        #[test]
        fn get_works() {
            // Note that even though we defined the constructor above 
            // as a `&mut self` function that returns nothing, we can
            // call them in test code as if they were normal Rust constructors
            // that take no `self` argument but return `Self`.
            let contract = {{camel_name}}::new();
            assert_eq!(contract.get(), String::from("Alice"));
        }

        /// We test if `set` method does its job.
        #[test]
        fn set_works() {
            // Note that in this test case, we will call `set` method
            // which takes a mutable reference to contract as its first
            // parameter, so we need to put a `mut` keyword in front of
            // the variable name to declare that it's mutable.
            let mut contract = {{camel_name}}::new();

            let mut new_name = String::from("Bob");

            // Note that `set` method will take the ownership of `new_name`
            // we provided above, and then `new_name` will be invalid and
            // we cannot use it anymore. To avoid this situation we clone
            // `new_name` here.
            contract.set(new_name.clone());
            assert_eq!(contract.get(), new_name);
        }
    }
}