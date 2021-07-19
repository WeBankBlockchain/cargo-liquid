// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;

use crate::{
    control_flow::{CHABuilder, ForwardCFG},
    ifds::{problems::UninitializedStates, IfdsSolver},
};
use log::*;
use rustc_driver::Compilation;
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::TyCtxt;
use std::path::PathBuf;

pub struct AnalysisCallbacks {
    pub cfg_path: Option<PathBuf>,
}

impl rustc_driver::Callbacks for AnalysisCallbacks {
    /// Called after the compiler has completed all analysis passes and before it
    /// lowers MIR to LLVM IR. At this point the compiler is ready to tell us all
    /// it knows and we can proceed to do analysis of all of the functions that
    /// will end up in the compiler output.
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        compiler.session().abort_if_errors();
        queries
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| self.analyze_with_mir(compiler, tcx));

        // This is only a analyzer, cargo still needs code generation to work.
        Compilation::Continue
    }
}

impl AnalysisCallbacks {
    fn analyze_with_mir<'tcx>(&mut self, _: &Compiler, tcx: TyCtxt<'tcx>) {
        let mut fwd_cg = ForwardCFG::new(tcx);
        debug!("all1: {:?}", fwd_cg.contract_methods);
        let entry_points = fwd_cg
            .contract_methods
            .iter()
            .filter_map(|(def_id, info)| {
                if info.visible && info.mutable {
                    Some(*def_id)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        let mut cfg_builder = CHABuilder::new(&mut fwd_cg);
        let entry_points = cfg_builder.build(entry_points);

        if let Some(ref cfg_path) = self.cfg_path {
            if let Err(err) = fwd_cg.dump(cfg_path.as_path(), &entry_points) {
                error!("unable to dump the call graph due to: `{:?}`", err);
            }
        }

        /*
        let constructor = entry_points
            .iter()
            .filter(|method| {
                let def_id = method.def_id;
                debug!("key: {:?}", def_id);
                debug!("all: {:?}", fwd_cg.contract_methods);
                let info = &fwd_cg.contract_methods[&def_id];
                info.mutable == true && info.visible == true && info.name == "new"
            })
            .collect::<Vec<_>>();
        debug_assert!(constructor.len() == 1);
        let constructor = constructor[0];
        let problem = UninitializedStates;
        let mut ifds_solver = IfdsSolver::new(problem, &fwd_cg, true);
        ifds_solver.solve(constructor);*/
    }
}
