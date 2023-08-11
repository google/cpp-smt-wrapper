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

#ifndef SRC_SMT_PRINTING_SMT_SOLVER_FACTORY_H_
#define SRC_SMT_PRINTING_SMT_SOLVER_FACTORY_H_

#include <functional>
#include <memory>
#include <string>

#include "src/smt/z3_smt_solver_factory.h"
#include "src/smt/printing_smt_solver.h"
#include "src/smt/smt.h"
#include "src/smt/smt_solver_factory.h"

namespace smt {

class PrintingSMTSolverFactory : public SMTSolverFactory {
 public:
  // Creates a PrintingSMTSolverFactory that defaults to outputting SMT commands
  // to std::cout and which wraps a CVC4 solver.
  std::unique_ptr<SMTSolver> Create() const override;

  // Creates a PrintingSMTSolver with the specified mode, outputting via the
  // given function, and wrapping a particular solver.  Takes ownership of the
  // solver passed in.
  std::unique_ptr<SMTSolver> Create(PrintingMode mode,
                                    std::function<void(std::string)> logger,
                                    std::unique_ptr<SMTSolver> solver) const;
};

}  //  namespace smt

#endif  // SRC_SMT_PRINTING_SMT_SOLVER_FACTORY_H_
