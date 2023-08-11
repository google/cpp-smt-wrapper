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

#ifndef SRC_SMT_PRINTING_SMT_SOLVER_H_
#define SRC_SMT_PRINTING_SMT_SOLVER_H_

#include <cstdint>
#include <functional>
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

#include "src/smt/smt.h"
#include "src/smt/smt_term.h"
#include "absl/container/node_hash_map.h"
#include "absl/status/status.h"

namespace smt {

// Printing Mode--either print just the SMT-lib calls, or print all calls to
// the solver object.
enum PrintingMode { kSMT, kAll };

// A PrintingSolver is a facade that wraps a particular solver and calls the
// logger function on each SMT assertion.
class PrintingSolver : public SMTSolver {
 public:
  PrintingSolver(PrintingMode mode,
                 std::function<void(const std::string&)> logger,
                 std::unique_ptr<SMTSolver> wrapped_solver)
      : SMTSolver("PRINTING"),
        mode_(mode),
        logger_(logger),
        solver_(std::move(wrapped_solver)) {}

  // The following are implementations of interface methods.
  Sort DeclareSort(std::string name, int arity) final;
  Sort GetTheorySort(op::Sort op_sort) final;
  Sort GetTheorySort(op::Sort op_sort, unsigned num) final;
  Sort ApplySort(Sort sort_constructor, const std::vector<Sort>& args) final;
  Term DeclareFunction(std::string name, Sort sort) final;
  Function DeclareFunction(std::string name,
                           const std::vector<Sort>& rank) final;
  Function GetTheoryFunction(op::Function op_function) final;
  Function GetTheoryFunction(op::Function op_function, unsigned index) final;
  Function GetTheoryFunction(op::Function op_function, unsigned index1,
                             unsigned index2) final;
  Term GetTheoryConstantTerm(op::Function op_function) final;
  Term BooleanTerm(bool b) final;
  Term NumeralTerm(uint64_t num) final;
  Term NumeralTerm(std::string num) final;
  Term SignedNumeralTerm(int64_t num) final;
  Term DecimalTerm(double dec) final;
  Term DecimalTerm(std::string dec) final;
  Term BitvectorConstantTerm(uint64_t num, int width) final;
  Term BinaryConstantTerm(std::string bin_str) final;
  Term HexConstantTerm(std::string hex_str) final;
  Term StringConstantTerm(std::string str) final;
  Term SetSortOfTerm(Term t, Sort sort) final;
  Term ApplyFunction(Function f, const std::vector<Term>& args) final;
  Term BoundVariableTerm(std::string name, Sort sort) final;
  Term Forall(const std::vector<Term>& vars, Term body) final;
  Term Exists(const std::vector<Term>& vars, Term body) final;
  absl::Status SetLogic(std::string logic_name) final;
  void SetOption(std::string option_name, bool value) final;
  void SetOption(std::string option_name, unsigned num) final;
  void SetOption(std::string option_name, std::string value) final;
  void SetEngineTimeout(unsigned timeout_ms) final;
  void AssertFormula(Term assertion) final;
  CheckSatResponse CheckSat() final;
  Term GetValue(Term t) final;
  void Push() final;
  void Pop() final;
  void Reset() final;
  void ResetAssertions() final;
  void RegisterErrorHandler(HandlerFunctionType handler_function) final {
    SMTSolver::RegisterErrorHandler(handler_function);
    solver_->RegisterErrorHandler(handler_function);
  }

 private:
  // The printing mode.
  PrintingMode mode_;

  // The logger function to call on each SMT call.
  std::function<void(std::string)> logger_;

  // The pointer to the main SMT Solver.
  std::unique_ptr<SMTSolver> solver_;
};

}  // namespace smt

#endif  // SRC_SMT_PRINTING_SMT_SOLVER_H_
