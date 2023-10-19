#![cfg_attr(not(feature = "std"), no_std)]

use liquid::{storage, InOut};
use liquid_lang as liquid;
//use std::dbg;
//use log::info;

#[liquid::contract]
mod contract {
    use super::*;

    const CONSTANT_POSITIVE: u128 = 1;
    const CONSTANT_ZERO: i8 = 0;
    const CONSTANT_NEGATIVE: i128 = -1;

    #[derive(InOut)]
    pub struct Child {
        year: u64,
        name: String,
    }

    #[liquid(storage)]
    struct Contract {
        val_container: storage::Value<i8>,

        env_address: storage::Mapping<Address, u32>,
        env_timestamp: storage::Mapping<timestamp, u32>,
        env_u64: storage::Mapping<u64, u32>,

        constant_u128: storage::Mapping<u128, u32>,
        constant_i8: storage::Mapping<i8, u32>,
        constant_i128: storage::Mapping<i128, u32>,

        complex_data_structure: storage::Vec<Child>,
    }

    #[liquid(methods)]
    impl Contract {
        pub fn new(&mut self) {
            self.val_container.initialize(0);
            //println!("------------------TEST1{:?}",val_container);
            //dbg!(val_container);

            self.env_address.initialize();
            //dbg!(env_address);
            //println!("------------------TEST2{:?}",env_address);
            self.env_timestamp.initialize();
            //dbg!(env_timestamp);
            //println!("------------------TEST3{:?}",env_timestamp);
            self.env_u64.initialize();

            self.constant_u128.initialize();
            self.constant_i8.initialize();
            self.constant_i128.initialize();

            self.complex_data_structure.initialize();
        }

        // test cases for kind 0
        pub fn visit_val_container(&mut self) {
             self.val_container.set(0);
         }

         // test cases for kind 1
         pub fn change_complex_data_structure(&mut self) {
            let child = Child {
                year: 8,
                name: String::from("child"),
            };
            self.complex_data_structure.push(child);
        }

        // test cases for kind 2
        pub fn test_env_caller(&mut self) {
            self.env_address.get(&self.env().get_caller());
            // println!("{:?}",ret);
            //self.env().emit_event("env_address", &self.env_address);
           // info!("------------------TEST1{:?}", self.env_address);
        }
        pub fn test_env_tx_origin(&mut self) {
            self.env_address.get(&self.env().get_tx_origin());
        }
        pub fn test_env_now(&mut self) {
            self.env_timestamp.get(&self.env().now());
        }
        pub fn test_env_block_number(&mut self) {
            self.env_u64.get(&self.env().get_block_number());
        }
        pub fn test_env_address(&mut self) {
            self.env_address.get(&self.env().get_address());
        }

        // test cases for kind 3
        pub fn test_method_parameter(&mut self, temp_var: Child) {
            self.env_u64.get(&temp_var.year);
        }

        // test cases for kind 4
        pub fn test_constant_positive(&mut self) {
            self.constant_u128.get(&CONSTANT_POSITIVE);
        }
        pub fn test_constant_zero(&mut self) {
            self.constant_i8.get(&CONSTANT_ZERO);
        }
        pub fn test_constant_negative(&mut self) {
            self.constant_i128.get(&CONSTANT_NEGATIVE);
        }

        // test cases for interprocedural calling
        pub fn test_interprocedural_calling(&mut self, temp_var: Child) {
            self.test_method_parameter(temp_var);
        }

        // test cases for branch statement
        pub fn test_branch_statement(&mut self, temp_var: i8) {
            if temp_var <= 0 {
                self.env_address.get(&self.env().get_tx_origin());
            } else {
                self.env_address.get(&self.env().get_caller());
                //self.emit_event("EnvAddress", &self.env_address);
            }
        }

       // fn emit_event<T: liquid_abi::TypeInfo>(&mut self, event_name: &str, data: &T) {
        //    liquid_lang::emit_event(event_name, data);
       // }
    }
}
