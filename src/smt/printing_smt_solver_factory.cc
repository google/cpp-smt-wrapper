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

#include "src/smt/printing_smt_solver_factory.h"

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <utility>

#include "src/smt/printing_smt_solver.h"

namespace smt {

std::unique_ptr<SMTSolver> PrintingSMTSolverFactory::Create() const {
  return Create(
      PrintingMode::kSMT, [](std::string str) { std::cout << str; },
      Z3SMTSolverFactory().Create());
}

std::unique_ptr<SMTSolver> PrintingSMTSolverFactory::Create(
    PrintingMode mode, std::function<void(std::string)> logger,
    std::unique_ptr<SMTSolver> solver) const {
  return std::unique_ptr<SMTSolver>(
      new PrintingSolver(mode, logger, std::move(solver)));
}

}  // namespace smt
