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

#include "src/smt/printing_smt_solver.h"

#include <cstdint>
#include <sstream>
#include <string>
#include <vector>

#include "absl/status/status.h"
#include "absl/strings/str_cat.h"

namespace smt {

// The following are implementations of interface methods.
Sort PrintingSolver::DeclareSort(std::string name, int arity) {
  logger_(absl::StrCat("(define-sort ", name, " ", arity, ")", "\n"));
  return solver_->DeclareSort(name, arity);
}

Sort PrintingSolver::GetTheorySort(op::Sort op_sort) {
  if (mode_ == PrintingMode::kAll) {
    logger_(absl::StrCat("; get-sort ", op_sort, "\n"));
  }
  return solver_->GetTheorySort(op_sort);
}

Sort PrintingSolver::GetTheorySort(op::Sort op_sort, unsigned num) {
  if (mode_ == PrintingMode::kAll) {
    logger_(absl::StrCat("; get-sort ", op_sort, "(", num, ")", "\n"));
  }
  return solver_->GetTheorySort(op_sort, num);
}

Sort PrintingSolver::ApplySort(Sort sort_constructor,
                               const std::vector<Sort>& args) {
  // TODO: GetSort(smt::op::kArray) returns an empty sort for Z3,
  // so we have to combine two calls at the SMT-lib layer to create an ArraySort.
  // We should print here if we can get that addressed.
  return solver_->ApplySort(sort_constructor, args);
}

Term PrintingSolver::DeclareFunction(std::string name, Sort sort) {
  logger_(
      absl::StrCat("(declare-fun ", name, " () ", sort.ToString(), ")", "\n"));
  return solver_->DeclareFunction(name, sort);
}

Function PrintingSolver::DeclareFunction(std::string name,
                                         const std::vector<Sort>& rank) {
  std::stringstream sstr;
  for (int i = 0; i < rank.size() - 1; i++) {
    sstr << rank[i].ToString() << " ";
  }

  logger_(absl::StrCat("(declare-fun ", name, " (", sstr.str(), ") ",
                       rank[rank.size() - 1].ToString(), " )", "\n"));

  return solver_->DeclareFunction(name, rank);
}

Function PrintingSolver::GetTheoryFunction(op::Function op_function) {
  if (mode_ == PrintingMode::kAll) {
    logger_(absl::StrCat("; get-function ", op_function, "\n"));
  }
  return solver_->GetTheoryFunction(op_function);
}

Function PrintingSolver::GetTheoryFunction(op::Function op_function,
                                           unsigned index) {
  if (mode_ == PrintingMode::kAll) {
    logger_(
        absl::StrCat("; get-function ", op_function, "(", index, ")", "\n"));
  }
  return solver_->GetTheoryFunction(op_function, index);
}

Function PrintingSolver::GetTheoryFunction(op::Function op_function,
                                           unsigned index1, unsigned index2) {
  if (mode_ == PrintingMode::kAll) {
    logger_(absl::StrCat("; get-function ", op_function, "(", index1, ", ",
                         index2, ")", "\n"));
  }
  return solver_->GetTheoryFunction(op_function, index1, index2);
}

Term PrintingSolver::GetTheoryConstantTerm(op::Function op_function) {
  if (mode_ == PrintingMode::kAll) {
    logger_(absl::StrCat("; Get Constant Term = ", op_function, "\n"));
  }
  return solver_->GetTheoryConstantTerm(op_function);
}

Term PrintingSolver::BooleanTerm(bool b) {
  if (mode_ == PrintingMode::kAll) {
    logger_(absl::StrCat("; boolean term = ", b, "\n"));
  }
  return solver_->BooleanTerm(b);
}

Term PrintingSolver::NumeralTerm(uint64_t num) {
  if (mode_ == PrintingMode::kAll) {
    logger_(absl::StrCat("; numeral term = ", num, "\n"));
  }
  return solver_->NumeralTerm(num);
}

Term PrintingSolver::NumeralTerm(std::string num) {
  if (mode_ == PrintingMode::kAll) {
    logger_(absl::StrCat("; numeral term = ", num, "\n"));
  }
  return solver_->NumeralTerm(num);
}

Term PrintingSolver::SignedNumeralTerm(int64_t num) {
  if (mode_ == PrintingMode::kAll) {
    logger_(absl::StrCat("; signed numeral term = ", num, "\n"));
  }
  return solver_->SignedNumeralTerm(num);
}

Term PrintingSolver::DecimalTerm(double dec) {
  if (mode_ == PrintingMode::kAll) {
    logger_(absl::StrCat("; decimal term = ", dec, "\n"));
  }
  return solver_->DecimalTerm(dec);
}

Term PrintingSolver::DecimalTerm(std::string dec) {
  if (mode_ == PrintingMode::kAll) {
    logger_(absl::StrCat("; decimal term = ", dec, "\n"));
  }
  return solver_->DecimalTerm(dec);
}

Term PrintingSolver::BitvectorConstantTerm(uint64_t num, int width) {
  if (mode_ == PrintingMode::kAll) {
    logger_(
        absl::StrCat("; bv constant term = (", num, ", ", width, ")", "\n"));
  }
  return solver_->BitvectorConstantTerm(num, width);
}

Term PrintingSolver::BinaryConstantTerm(std::string bin_str) {
  if (mode_ == PrintingMode::kAll) {
    logger_(absl::StrCat("; bin term = ", bin_str, "\n"));
  }
  return solver_->BinaryConstantTerm(bin_str);
}

Term PrintingSolver::HexConstantTerm(std::string hex_str) {
  if (mode_ == PrintingMode::kAll) {
    logger_(absl::StrCat("; hex term = ", hex_str, "\n"));
  }
  return solver_->HexConstantTerm(hex_str);
}

Term PrintingSolver::StringConstantTerm(std::string str) {
  if (mode_ == PrintingMode::kAll) {
    logger_(absl::StrCat("; string term = ", str, "\n"));
  }
  return solver_->StringConstantTerm(str);
}

Term PrintingSolver::SetSortOfTerm(Term t, Sort sort) {
  return solver_->SetSortOfTerm(t, sort);
}

Term PrintingSolver::ApplyFunction(Function f, const std::vector<Term>& args) {
  if (mode_ == PrintingMode::kAll) {
    std::stringstream sstr;
    for (auto& arg : args) {
      sstr << arg.ToString() << " ";
    }
    logger_(absl::StrCat("; (", f.ToString(), " ", sstr.str(), ")", "\n"));
  }
  return solver_->ApplyFunction(f, args);
}

Term PrintingSolver::BoundVariableTerm(std::string name, Sort sort) {
  logger_(
      absl::StrCat("(declare-const ", name, " ", sort.ToString(), ")", "\n"));
  return solver_->BoundVariableTerm(name, sort);
}

Term PrintingSolver::Forall(const std::vector<Term>& vars, Term body) {
  if (mode_ == PrintingMode::kAll) {
    std::stringstream sstr;
    for (auto& var : vars) {
      sstr << "(" << var.ToString() << ") ";
    }
    logger_(absl::StrCat("; (forall (", sstr.str(), ") (", body.ToString(), ")",
                         "\n"));
  }
  return solver_->Forall(vars, body);
}

Term PrintingSolver::Exists(const std::vector<Term>& vars, Term body) {
  if (mode_ == PrintingMode::kAll) {
    std::stringstream sstr;
    for (auto& var : vars) {
      sstr << "(" << var.ToString() << ") ";
    }
    logger_(absl::StrCat("; (exists (", sstr.str(), ") (", body.ToString(), ")",
                         "\n"));
  }
  return solver_->Exists(vars, body);
}

absl::Status PrintingSolver::SetLogic(std::string logic_name) {
  logger_(absl::StrCat(R"((set-logic ")", logic_name, R"("))", "\n"));
  return solver_->SetLogic(logic_name);
}

void PrintingSolver::SetOption(std::string option_name, bool value) {
  logger_(absl::StrCat("(set-option :", option_name, " ", value, ")", "\n"));
  return solver_->SetOption(option_name, value);
}

void PrintingSolver::SetOption(std::string option_name, unsigned num) {
  logger_(absl::StrCat("(set-option :", option_name, " ", num, ")", "\n"));
  return solver_->SetOption(option_name, num);
}

void PrintingSolver::SetOption(std::string option_name, std::string value) {
  logger_(absl::StrCat("(set-option :", option_name, " ", value, ")", "\n"));
  return solver_->SetOption(option_name, value);
}

void PrintingSolver::SetEngineTimeout(unsigned timeout_ms) {
  if (mode_ == PrintingMode::kAll) {
    logger_(absl::StrCat("; set-timeout=", timeout_ms, "\n"));
  }
  return solver_->SetEngineTimeout(timeout_ms);
}

void PrintingSolver::AssertFormula(Term assertion) {
  logger_(absl::StrCat("(assert ", assertion.ToString(), ")", "\n"));
  return solver_->AssertFormula(assertion);
}

SMTSolver::CheckSatResponse PrintingSolver::CheckSat() {
  logger_(absl::StrCat("(check-sat)", "\n"));
  return solver_->CheckSat();
}

Term PrintingSolver::GetValue(Term t) {
  logger_(absl::StrCat("(get-value ", t.ToString(), ")", "\n"));
  return solver_->GetValue(t);
}

void PrintingSolver::Push() {
  logger_(absl::StrCat("(push)", "\n"));
  return solver_->Push();
}

void PrintingSolver::Pop() {
  logger_(absl::StrCat("(pop)", "\n"));
  return solver_->Pop();
}

void PrintingSolver::Reset() {
  logger_(absl::StrCat("(reset)", "\n"));
  return solver_->Reset();
}

void PrintingSolver::ResetAssertions() {
  logger_(absl::StrCat("(reset)", "\n"));
  return solver_->ResetAssertions();
}

}  // namespace smt
