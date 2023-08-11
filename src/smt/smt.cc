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

// Implementation of methods for SMTSolver abstract interface

#include "src/smt/smt.h"

#include <cstdlib>
#include <memory>
#include <ostream>
#include <string>
#include <utility>
#include <vector>

#include "absl/log/log.h"

namespace smt {


// Default error handler for SMTSolver class
static void DefaultErrorHandler(SMTSolver::ErrorType error, std::string msg) {
  std::string error_message;
  switch (error) {
    case SMTSolver::kError:
      error_message = "Error: ";
      break;
    case SMTSolver::kUnsupported:
      error_message = "Unsupported: ";
      break;
    case SMTSolver::kOther:
      error_message = "Other message: ";
      break;
  }
  LOG(FATAL) << error_message << msg << std::endl;
}

SMTSolver::SMTSolver(std::string solver_name)
    : handler_function_(DefaultErrorHandler),
      solver_name_(std::move(solver_name)) {
  AddSort("Bool", op::kBool);
  AddSort("Array", op::kArray);
  AddSort("BitVec", op::kBitvec);
  AddSort("Int", op::kInt);
  AddSort("Real", op::kReal);
  AddFunction("true", op::kTrue);
  AddFunction("false", op::kFalse);
  AddFunction("not", op::kNot);
  AddFunction("=>", op::kImplies);
  AddFunction("and", op::kAnd);
  AddFunction("or", op::kOr);
  AddFunction("xor", op::kXor);
  AddFunction("=", op::kEqual);
  AddFunction("distinct", op::kDistinct);
  AddFunction("ite", op::kIte);
  AddFunction("select", op::kSelect);
  AddFunction("store", op::kStore);
  AddFunction("concat", op::kConcat);
  AddFunction("extract", op::kExtract);
  AddFunction("bvnot", op::kBvnot);
  AddFunction("bvand", op::kBvand);
  AddFunction("bvor", op::kBvor);
  AddFunction("bvneg", op::kBvneg);
  AddFunction("bvadd", op::kBvadd);
  AddFunction("bvmul", op::kBvmul);
  AddFunction("bvudiv", op::kBvudiv);
  AddFunction("bvurem", op::kBvurem);
  AddFunction("bvshl", op::kBvshl);
  AddFunction("bvlshr", op::kBvlshr);
  AddFunction("bvnand", op::kBvnand);
  AddFunction("bvnor", op::kBvnor);
  AddFunction("bvxor", op::kBvxor);
  AddFunction("bvcomp", op::kBvcomp);
  AddFunction("bvsub", op::kBvsub);
  AddFunction("bvsdiv", op::kBvsdiv);
  AddFunction("bvsrem", op::kBvsrem);
  AddFunction("bvsmod", op::kBvsmod);
  AddFunction("bvashr", op::kBvashr);
  AddFunction("repeat", op::kRepeat);
  AddFunction("zero_extend", op::kZeroExtend);
  AddFunction("sign_extend", op::kSignExtend);
  AddFunction("rotate_left", op::kRotateLeft);
  AddFunction("rotate_right", op::kRotateRight);
  AddFunction("bvult", op::kBvult);
  AddFunction("bvule", op::kBvule);
  AddFunction("bvugt", op::kBvugt);
  AddFunction("bvuge", op::kBvuge);
  AddFunction("bvslt", op::kBvslt);
  AddFunction("bvsle", op::kBvsle);
  AddFunction("bvsgt", op::kBvsgt);
  AddFunction("bvsge", op::kBvsge);
  AddFunction("-", op::kMinus);
  AddFunction("+", op::kPlus);
  AddFunction("*", op::kMult);
  AddFunction("<=", op::kLe);
  AddFunction("<", op::kLt);
  AddFunction(">=", op::kGe);
  AddFunction(">", op::kGt);
  AddFunction("div", op::kIntDiv);
  AddFunction("mod", op::kMod);
  AddFunction("abs", op::kAbs);
  AddFunction("divisible", op::kDivisible);
  AddFunction("to_real", op::kToReal);
  AddFunction("/", op::kRealDiv);
  AddFunction("to_int", op::kToInt);
  AddFunction("is_int", op::kIsInt);
}


Sort SMTSolver::GetTheorySort(Identifier name) {
  auto it = sort_symbols_.find(name.symbol());
  if (it != sort_symbols_.end()) {
    if (!name.IsIndexed()) {
      return GetTheorySort(op::Sort((*it).second));
    } else if (name.GetSize() == 1 &&
               !name.GetIndex(0).IsSymbol()) {
      return GetTheorySort(op::Sort((*it).second), name.GetIndex(0).GetNum());
    } else {
      HandleError(kError, "Unknown indexed theory sort");
      return Sort();
    }
  } else {
    HandleError(kError, "Unknown theory sort");
    return Sort();
  }
}


Sort SMTSolver::ApplySort(Sort sort_constructor, Sort arg) {
  std::vector<Sort> args{arg};
  return ApplySort(sort_constructor, args);
}


Sort SMTSolver::ApplySort(Sort sort_constructor, Sort arg1, Sort arg2) {
  std::vector<Sort> args{arg1, arg2};
  return ApplySort(sort_constructor, args);
}


Function SMTSolver::GetTheoryFunction(Identifier name) {
  auto it = function_symbols_.find(name.symbol());
  if (it != function_symbols_.end()) {
    if (!name.IsIndexed()) {
      return GetTheoryFunction(op::Function((*it).second));
    } else if (name.GetSize() == 1 &&
               !name.GetIndex(0).IsSymbol()) {
      return GetTheoryFunction(op::Function((*it).second),
                               name.GetIndex(0).GetNum());
    } else if (name.GetSize() == 2 &&
               !name.GetIndex(0).IsSymbol() && !name.GetIndex(1).IsSymbol()) {
      return GetTheoryFunction(op::Function((*it).second),
                               name.GetIndex(0).GetNum(),
                               name.GetIndex(1).GetNum());
    } else {
      HandleError(kError, "Unknown indexed theory function");
      return Function();
    }
  } else {
    HandleError(kError, "Unknown theory function");
    return Function();
  }
}


Function SMTSolver::DeclareFunction(std::string name, Sort arg_sort,
                                    Sort return_sort) {
  std::vector<Sort> rank{arg_sort, return_sort};
  return DeclareFunction(name, rank);
}


Function SMTSolver::DeclareFunction(std::string name, Sort arg1_sort,
                                    Sort arg2_sort, Sort return_sort) {
  std::vector<Sort> rank{arg1_sort, arg2_sort, return_sort};
  return DeclareFunction(name, rank);
}


Term SMTSolver::GetTheoryConstantTerm(Identifier name) {
  auto it = function_symbols_.find(name.symbol());
  if (it != function_symbols_.end()) {
    if (!name.IsIndexed()) {
      return GetTheoryConstantTerm(op::Function((*it).second));
    } else {
      HandleError(kError, "Unknown indexed theory constant");
      return Term();
    }
  } else {
    HandleError(kError, "Unknown theory constant");
    return Term();
  }
}


Term SMTSolver::ApplyFunction(Function f, Term arg) {
  std::vector<Term> args{arg};
  return ApplyFunction(f, args);
}


Term SMTSolver::ApplyFunction(Function f, Term arg1, Term arg2) {
  std::vector<Term> args{arg1, arg2};
  return ApplyFunction(f, args);
}


Term SMTSolver::ApplyFunction(Function f, Term arg1, Term arg2, Term arg3) {
  std::vector<Term> args{arg1, arg2, arg3};
  return ApplyFunction(f, args);
}


Term SMTSolver::ApplyFunction(op::Function op_function, Term arg) {
  return ApplyFunction(GetTheoryFunction(op_function), arg);
}


Term SMTSolver::ApplyFunction(op::Function op_function, Term arg1, Term arg2) {
  return ApplyFunction(GetTheoryFunction(op_function), arg1, arg2);
}


Term SMTSolver::ApplyFunction(op::Function op_function,
                              Term arg1, Term arg2, Term arg3) {
  return ApplyFunction(GetTheoryFunction(op_function), arg1, arg2, arg3);
}


Term SMTSolver::ApplyFunction(op::Function op_function,
                              const std::vector<Term>& args) {
  return ApplyFunction(GetTheoryFunction(op_function), args);
}


void SMTSolver::AddSort(std::string name, op::Sort sort) {
  sort_symbols_.emplace(name, sort);
}


void SMTSolver::AddFunction(std::string name, op::Function function) {
  function_symbols_.emplace(name, function);
}


}  // namespace smt
