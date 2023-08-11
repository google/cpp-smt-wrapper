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

// An auto-generated mocking class implementing an SMTSolver as defined in
// smt.h. Used for testing purposes only.

#ifndef SRC_SMT_MOCK_SMT_H_
#define SRC_SMT_MOCK_SMT_H_

#include <cstdint>
#include <memory>
#include <string>
#include <gtest/gtest.h>

#include "src/smt/smt.h"
#include "src/smt/smt_solver_factory.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"

namespace smt {

class MockSMTSolver : public SMTSolver {
 public:
  explicit MockSMTSolver(std::string solver_name) : SMTSolver(solver_name) {}

  MOCK_METHOD(void, RegisterErrorHandler,
              (HandlerFunctionType handler_function), (override));
  MOCK_METHOD(Sort, DeclareSort, (std::string name, int arity), (override));
  MOCK_METHOD(Sort, GetTheorySort, (Identifier name), (override));
  MOCK_METHOD(Sort, GetTheorySort, (op::Sort op_sort), (override));
  MOCK_METHOD(Sort, GetTheorySort, (op::Sort op_sort, unsigned index),
              (override));
  MOCK_METHOD(Sort, ApplySort, (Sort sort_constructor, Sort arg), (override));
  MOCK_METHOD(Sort, ApplySort, (Sort sort_constructor, Sort arg1, Sort arg2),
              (override));
  MOCK_METHOD(Sort, ApplySort,
              (Sort sort_constructor, const std::vector<Sort>& args),
              (override));
  MOCK_METHOD(Term, DeclareFunction, (std::string name, Sort sort), (override));
  MOCK_METHOD(Function, DeclareFunction,
              (std::string name, Sort arg_sort, Sort return_sort), (override));
  MOCK_METHOD(Function, DeclareFunction,
              (std::string name, Sort arg1_sort, Sort arg2_sort,
               Sort return_sort),
              (override));
  MOCK_METHOD(Function, DeclareFunction,
              (std::string name, const std::vector<Sort>& rank), (override));
  MOCK_METHOD(Function, GetTheoryFunction, (Identifier name), (override));
  MOCK_METHOD(Function, GetTheoryFunction, (op::Function op_function),
              (override));
  MOCK_METHOD(Function, GetTheoryFunction,
              (op::Function op_function, unsigned index), (override));
  MOCK_METHOD(Function, GetTheoryFunction,
              (op::Function op_function, unsigned index1, unsigned index2),
              (override));
  MOCK_METHOD(Term, GetTheoryConstantTerm, (Identifier name), (override));
  MOCK_METHOD(Term, GetTheoryConstantTerm, (op::Function op_function),
              (override));
  MOCK_METHOD(Term, BooleanTerm, (bool b), (override));
  MOCK_METHOD(Term, NumeralTerm, (uint64_t num), (override));
  MOCK_METHOD(Term, NumeralTerm, (std::string num), (override));
  MOCK_METHOD(Term, SignedNumeralTerm, (int64_t num), (override));
  MOCK_METHOD(Term, DecimalTerm, (double decimal_value), (override));
  MOCK_METHOD(Term, DecimalTerm, (std::string decimal_str), (override));
  MOCK_METHOD(Term, BitvectorConstantTerm, (uint64_t num, int width),
              (override));
  MOCK_METHOD(Term, BinaryConstantTerm, (std::string bin_str), (override));
  MOCK_METHOD(Term, HexConstantTerm, (std::string hex_str), (override));
  MOCK_METHOD(Term, StringConstantTerm, (std::string str), (override));
  MOCK_METHOD(Term, SetSortOfTerm, (Term t, Sort sort), (override));
  MOCK_METHOD(Term, ApplyFunction, (Function f, Term arg), (override));
  MOCK_METHOD(Term, ApplyFunction, (Function f, Term arg1, Term arg2),
              (override));
  MOCK_METHOD(Term, ApplyFunction,
              (Function f, Term arg1, Term arg2, Term arg3), (override));
  MOCK_METHOD(Term, ApplyFunction, (Function f, const std::vector<Term>& args),
              (override));
  MOCK_METHOD(Term, ApplyFunction, (op::Function op_function, Term arg),
              (override));
  MOCK_METHOD(Term, ApplyFunction,
              (op::Function op_function, Term arg1, Term arg2), (override));
  MOCK_METHOD(Term, ApplyFunction,
              (op::Function op_function, Term arg1, Term arg2, Term arg3),
              (override));
  MOCK_METHOD(Term, ApplyFunction,
              (op::Function op_function, const std::vector<Term>& args),
              (override));
  MOCK_METHOD(Term, BoundVariableTerm, (std::string name, Sort sort),
              (override));
  MOCK_METHOD(Term, Forall, (const std::vector<Term>& vars, Term body),
              (override));
  MOCK_METHOD(Term, Exists, (const std::vector<Term>& vars, Term body),
              (override));
  MOCK_METHOD(absl::Status, SetLogic, (std::string logic_name), (override));
  MOCK_METHOD(void, SetOption, (std::string option_name, bool value),
              (override));
  MOCK_METHOD(void, SetOption, (std::string option_name, unsigned num),
              (override));
  MOCK_METHOD(void, SetOption, (std::string option_name, std::string value),
              (override));
  MOCK_METHOD(void, SetEngineTimeout, (unsigned timeout_ms), (override));
  MOCK_METHOD(void, AssertFormula, (Term assertion), (override));
  MOCK_METHOD(CheckSatResponse, CheckSat, (), (override));
  MOCK_METHOD(Term, GetValue, (Term t), (override));
  MOCK_METHOD(void, Push, (), (override));
  MOCK_METHOD(void, Pop, (), (override));
  MOCK_METHOD(void, Reset, (), (override));
  MOCK_METHOD(void, ResetAssertions, (), (override));
};

class MockSMTSolverFactory final : public SMTSolverFactory {
 public:
  std::unique_ptr<SMTSolver> Create() const override {
    return std::unique_ptr<SMTSolver>(new MockSMTSolver("Mock"));
  }
};

// Helper for MockSort.  When a MockSort method is called, it will generate a
// call to the corresponding method in the MockSortImplementation, so this is
// where the expectation should be set.
class MockSortImplementation : public SortImplementation {
 public:
  MockSortImplementation() {}
  MOCK_METHOD(std::string, ToString, (), (const, override));
  MOCK_METHOD(bool, Equals, (const SortImplementation& rhs), (const, override));
};

// MockSort can be used wherever Sort would normally be used.  One nice feature
// for mocking is that two different MockSorts are automatically different from
// each other according to operator== (unlike using a default Sort declaration).
// If you want to actually call one of the Sort methods, you need to use
// get_implementation and use the resulting MockSortImplementation object as
// that is where the functionality is implemented.
class MockSort : public Sort {
 public:
  MockSort() : Sort(std::make_shared<MockSortImplementation>()) {}
  const MockSortImplementation* get_implementation() const {
    return down_cast<const MockSortImplementation*>(GetImplementation());
  }
};

// Helper for MockFunction.  When a MockFunction method is called, it will
// generate a call to the corresponding method in the
// MockFunctionImplementation, so this is where the expectation should be set.
class MockFunctionImplementation : public FunctionImplementation {
 public:
  MockFunctionImplementation() {}
  MOCK_METHOD(std::string, ToString, (), (const, override));
  MOCK_METHOD(bool, Equals, (const FunctionImplementation& rhs),
              (const, override));
};

// MockFunction can be used wherever Function would normally be used.  One nice
// feature for mocking is that two different MockFunctions are automatically
// different from each other according to operator== (unlike using a default
// Function declaration).  If you want to actually call one of the Function
// methods, you need to use get_implementation and use the resulting
// MockFunctionImplementation object as that is where the functionality is
// implemented.
class MockFunction : public Function {
 public:
  MockFunction() : Function(std::make_shared<MockFunctionImplementation>()) {}
  const MockFunctionImplementation* get_implementation() const {
    return down_cast<const MockFunctionImplementation*>(GetImplementation());
  }
};

// Helper for MockTerm.  When a MockTerm method is called, it will generate a
// call to the corresponding method in the MockTermImplementation, so this is
// where the expectation should be set.  Note that if operator[] is called,
// the expectation must be set on GetChild.
class MockTermImplementation : public TermImplementation {
 public:
  MockTermImplementation() {}
  MOCK_METHOD(std::string, ToString, (), (const, override));
  MOCK_METHOD(unsigned, NumChildren, (), (const, override));
  MOCK_METHOD(Term, GetChild, (unsigned index), (const));
  Term operator[](unsigned index) const override { return GetChild(index); }
  MOCK_METHOD(bool, Equals, (const TermImplementation& rhs), (const, override));
  MOCK_METHOD(bool, IsTheoryConstant, (), (const));
  MOCK_METHOD(bool, IsBoolConstant, (), (const, override));
  MOCK_METHOD(bool, GetBoolConstant, (), (const, override));
  MOCK_METHOD(bool, IsIntegerConstant, (), (const, override));
  MOCK_METHOD(absl::StatusOr<int64_t>, IntegerConstantToInt64, (),
              (const, override));
  MOCK_METHOD(absl::StatusOr<uint64_t>, IntegerConstantToUint64, (),
              (const, override));
  MOCK_METHOD(bool, IsBVConstant, (), (const, override));
  MOCK_METHOD(uint64_t, BvConstantToUnsigned, (), (const, override));
  MOCK_METHOD(std::string, BvConstantToDecimalString, (), (const, override));
  MOCK_METHOD(bool, IsStringConstant, (), (const, override));
  MOCK_METHOD(std::string, GetStringConstant, (), (const, override));
  MOCK_METHOD(unsigned, GetBVSize, (), (const, override));
  MOCK_METHOD(bool, GetBit, (unsigned index), (const, override));
  MOCK_METHOD(Sort, GetSort, (), (const, override));
};

// MockTerm can be used wherever Term would normally be used.  One nice feature
// for mocking is that two different MockTerms are automatically different from
// each other according to operator== (unlike using a default Term declaration).
// If you want to actually call one of the Term methods, you need to use
// get_implementation and use the resulting MockTermImplementation object as
// that is where the functionality is implemented.
class MockTerm : public Term {
 public:
  MockTerm() : Term(std::make_shared<MockTermImplementation>()) {}
  const MockTermImplementation* get_implementation() const {
    return down_cast<const MockTermImplementation*>(GetImplementation());
  }
};

}  // namespace smt

#endif  // SRC_SMT_MOCK_SMT_H_
