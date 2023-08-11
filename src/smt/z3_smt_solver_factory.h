//
// Copyright 2023 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

// Factory for Z3 implementation of SMTSolver interface.

#ifndef SRC_SMT_Z3_SMT_SOLVER_FACTORY_H_
#define SRC_SMT_Z3_SMT_SOLVER_FACTORY_H_

#include <memory>

#include "src/smt/smt.h"
#include "src/smt/smt_solver_factory.h"

namespace smt {

class Z3SMTSolverFactory final : public SMTSolverFactory {
 public:
  // The pointer to the Z3SMTSolver.
  std::unique_ptr<SMTSolver> Create() const override;
};

}  //  namespace smt

#endif  // SRC_SMT_Z3_SMT_SOLVER_FACTORY_H_
