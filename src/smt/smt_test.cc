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

// Unit tests for SMTSolver class.
// Adapted from cvc4 system test called "cvc3_main.cpp" (which was adapted from
// cvc3 system test).

#include "src/smt/smt.h"

#include <cstdint>
#include <fstream>
#include <limits>
#include <memory>
#include <ostream>
#include <string>
#include <vector>
#include <gtest/gtest.h>

#include "src/smt/printing_smt_solver_factory.h"
#include "src/smt/smt_ops.h"
#include "src/smt/z3_smt_solver_factory.h"
#include "src/base/testing/status_matchers.h"
#include "absl/strings/numbers.h"
#include "absl/debugging/leak_check.h"
#include "absl/status/status.h"
#include "absl/strings/str_cat.h"


using smt::Function;
using smt::Sort;
using smt::Term;
using ::smt::base::testing::StatusIs;
using ::smt::base::testing::IsOkAndHolds;

enum class SolverName {
  kZ3,
  kPrintingDefault,
  kPrintingZ3
};
std::ostream& operator<<(std::ostream& os, const SolverName& solver_name) {
  switch (solver_name) {
    case SolverName::kZ3:
      os << "Z3";
      return os;
    case SolverName::kPrintingDefault:
      os << "PRINTING DEFAULT";
      return os;
    case SolverName::kPrintingZ3:
      os << "PRINTING Z3";
      return os;
    default:
      os << "Unknown solver:";
      return os;
  }
}

class SMTTest : public ::testing::TestWithParam<SolverName> {
 protected:
  void SetUp() override {
    switch (GetParam()) {
      case SolverName::kZ3: {
        smt::Z3SMTSolverFactory z3_factory;
        smt_ = z3_factory.Create();
      } break;
      case SolverName::kPrintingDefault: {
        smt::PrintingSMTSolverFactory printing_factory;
        smt_ = printing_factory.Create();
      } break;
      case SolverName::kPrintingZ3: {
        printing_stream_.open("/dev/null");
        smt::PrintingSMTSolverFactory printing_factory;
        smt_ = printing_factory.Create(
            smt::PrintingMode::kSMT,
            [this](std::string str) { this->printing_stream_ << str; },
            smt::Z3SMTSolverFactory().Create());
      } break;
      default: { LOG(ERROR) << "Unknown solver."; }
    }
  }

  void TearDown() override { smt_.reset(nullptr); }

  // This asserts (not formula) to the solver and returns true if the assertion
  // set is unsat.
  //
  // Note that this leaves (not formula) in the assertion set.
  // This is in contrast to CVC3 and CVC4's version of CheckValid which removes
  // (not formula) in the assertion set.
  bool CheckValid(const Term& formula) {
    smt_->AssertFormula(smt_->ApplyFunction(smt::op::kNot, formula));
    smt::SMTSolver::CheckSatResponse response = smt_->CheckSat();
    return response == smt::SMTSolver::kUnsat;
  }

  // Attempts to set the logic.  Returns true if successful, false if the logic
  // is not supported by this solver, and fails if some other non-ok status is
  // returned.
  bool TrySetLogic(std::string logic) {
    absl::Status status = smt_->SetLogic(logic);
    if (absl::IsUnimplemented(status)) {
      return false;
    }
    CHECK_OK(status);
    return true;
  }
  std::ofstream printing_stream_;

  std::unique_ptr<smt::SMTSolver> smt_;
};

using SMTDeathTest = SMTTest;

TEST_P(SMTTest, UninterpretedFunctionsSetLogic) {
  // This tests the success of calling SetLogic on an SmtSolver.  SetLogic
  // corresponds to the (set-logic ...) command in the SMT-LIB language.  If
  // successful, it also performs a trivial check (that the formula "true" is
  // valid).
  if (!TrySetLogic("QF_UF")) return;
  EXPECT_TRUE(CheckValid(smt_->GetTheoryConstantTerm(smt::op::kTrue)));
}

TEST_P(SMTTest, BitvectorsSetLogic) {
  if (!TrySetLogic("QF_BV")) return;
  EXPECT_TRUE(CheckValid(smt_->GetTheoryConstantTerm(smt::op::kTrue)));
}

TEST_P(SMTTest, DeclareSortDoesNotCrash) {
  // This tests the success of making a sort using DeclareSort on an SmtSolver.
  // SetLogic corresponds to the (declare-sort ...) command in the SMT-LIB
  // language.
  if (!TrySetLogic("QF_UF")) return;
  Sort uninterpreted_sort = smt_->DeclareSort("u", 0);

  // We then check that the uninterpreted sort is inhabited by checking that a
  // variable in the uninterpreted sort is equal to itself.
  Term variable_x = smt_->DeclareFunction("x", uninterpreted_sort);
  Term x_eq_x = smt_->ApplyFunction(smt::op::kEqual, variable_x, variable_x);
  EXPECT_TRUE(CheckValid(x_eq_x));
}

TEST_P(SMTTest, BoolSortAccessible) {
  // This tests that the Bool sort is accessible from the bitvector logic.
  if (!TrySetLogic("QF_BV")) return;
  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  EXPECT_FALSE(bool_sort.IsNull());
}

TEST_P(SMTTest, BoolSortIsNotIntSort) {
  if (!TrySetLogic("QF_LIA")) return;

  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  Sort int_sort = smt_->GetTheorySort(smt::op::kInt);

  EXPECT_NE(bool_sort, int_sort);
}

TEST_P(SMTTest, SortDefaultConstructorIsNull) {
  if (!TrySetLogic("QF_BV")) return;
  Sort null_sort;
  EXPECT_TRUE(null_sort.IsNull());
}

TEST_P(SMTTest, NullSortEqualsItself) {
  if (!TrySetLogic("QF_BV")) return;
  Sort null_sort;
  EXPECT_EQ(null_sort, null_sort);
}

TEST_P(SMTTest, BoolSortIsNotNullSort) {
  if (!TrySetLogic("QF_BV")) return;
  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  Sort null_sort;

  // This tests operator== for null_sort appearing as both the left hand and
  // right hand side.
  EXPECT_NE(null_sort, bool_sort);
  EXPECT_NE(bool_sort, null_sort);
}

TEST_P(SMTTest, BoolSortEqualsItself) {
  if (!TrySetLogic("QF_BV")) return;
  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  EXPECT_EQ(bool_sort, smt_->GetTheorySort(smt::op::kBool));
}

TEST_P(SMTTest, ArraySortConstructorEqualsItself) {
  if (!TrySetLogic("QF_ABV")) return;
  Sort array_sort = smt_->GetTheorySort(smt::op::kArray);
  EXPECT_EQ(array_sort, smt_->GetTheorySort(smt::op::kArray));
}

TEST_P(SMTTest, BoolSortIsNotArraySortSymbol) {
  if (!TrySetLogic("QF_ABV")) return;
  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  Sort array_sort = smt_->GetTheorySort(smt::op::kArray);

  EXPECT_NE(bool_sort, array_sort);
}

TEST_P(SMTTest, UninterpretedSortEqualsItself) {
  if (!TrySetLogic("QF_UF")) return;
  Sort u_sort = smt_->DeclareSort("u", 0);
  EXPECT_EQ(u_sort, u_sort);
}

TEST_P(SMTTest, UninterpretedSortDoesNotEqualBoolSort) {
  if (!TrySetLogic("QF_UF")) return;
  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  Sort u_sort = smt_->DeclareSort("u", 0);
  EXPECT_NE(bool_sort, u_sort);
}

TEST_P(SMTTest, TwoUninterpretedSortsAreNotOperatorEqual) {
  if (!TrySetLogic("QF_UF")) return;
  Sort u_sort = smt_->DeclareSort("u", 0);
  Sort v_sort = smt_->DeclareSort("v", 0);
  EXPECT_NE(u_sort, v_sort);
}

TEST_P(SMTTest, ApplyingArraySortConstructorGeneratesTheSameSort) {
  // This tests that two different applications of the array sort
  // constructor generate the same sort.
  if (!TrySetLogic("QF_AX")) return;
  Sort array_sort_constructor = smt_->GetTheorySort(smt::op::kArray);
  Sort uninterpreted_sort = smt_->DeclareSort("u", 0);
  // This generates two copies of (Array u u).
  Sort array_u_to_u_sort_first = smt_->ApplySort(
      array_sort_constructor, uninterpreted_sort, uninterpreted_sort);
  Sort array_u_to_u_sort_second = smt_->ApplySort(
      array_sort_constructor, uninterpreted_sort, uninterpreted_sort);
  EXPECT_EQ(array_u_to_u_sort_first, array_u_to_u_sort_second);
}

TEST_P(SMTTest, TestBitvectorSortEquals) {
  if (!TrySetLogic("QF_BV")) return;
  const Sort bitvector_sort = smt_->GetTheorySort(smt::op::kBitvec, 32);
  Sort sort;
  EXPECT_NE(bitvector_sort, sort);
  sort = smt_->GetTheorySort(smt::op::kBitvec, 32);
  EXPECT_EQ(bitvector_sort, sort);
}

TEST_P(SMTTest, ArrayOfBitvectorsSortEqualsItself) {
  if (!TrySetLogic("QF_ABV")) return;
  const Sort array_sort_constructor = smt_->GetTheorySort(smt::op::kArray);
  const Sort bitvector_sort = smt_->GetTheorySort(smt::op::kBitvec, 32);
  const Sort array_32_32_sort =
      smt_->ApplySort(array_sort_constructor, bitvector_sort, bitvector_sort);
  Sort sort;
  EXPECT_NE(array_32_32_sort, sort);
  sort =
      smt_->ApplySort(array_sort_constructor, bitvector_sort, bitvector_sort);
  EXPECT_EQ(array_32_32_sort, sort);
}

TEST_P(SMTTest, FunctionDefaultConstructorGeneratesNullFunction) {
  if (!TrySetLogic("QF_BV")) return;
  Function null_function;
  EXPECT_TRUE(null_function.IsNull());
}

TEST_P(SMTTest, NullFunctionEqualsItself) {
  if (!TrySetLogic("QF_BV")) return;
  Function null_function;
  EXPECT_EQ(null_function, null_function);
}

TEST_P(SMTTest, TestFunctionNotEqualToNullFunction) {
  if (!TrySetLogic("QF_BV")) return;
  const Function bvadd = smt_->GetTheoryFunction(smt::op::kBvadd);
  Function function;
  EXPECT_NE(bvadd, function);
}

TEST_P(SMTTest, TestFunctionEqualsItself) {
  if (!TrySetLogic("QF_BV")) return;
  const Function bvadd = smt_->GetTheoryFunction(smt::op::kBvadd);
  const Function bvadd2 = smt_->GetTheoryFunction(smt::op::kBvadd);
  EXPECT_EQ(bvadd, bvadd2);
}

TEST_P(SMTTest, TestRepeatFunction) {
  if (!TrySetLogic("QF_BV")) return;
  const Function repeat2 = smt_->GetTheoryFunction(smt::op::kRepeat, 2);
  const Function repeat3 = smt_->GetTheoryFunction(smt::op::kRepeat, 3);
  CheckValid(smt_->ApplyFunction(
      smt::op::kEqual,
      smt_->ApplyFunction(repeat2, smt_->BitvectorConstantTerm(0xA, 4)),
      smt_->BitvectorConstantTerm(0xAA, 4 * 2)));
  CheckValid(smt_->ApplyFunction(
      smt::op::kEqual,
      smt_->ApplyFunction(repeat3, smt_->BitvectorConstantTerm(0xA, 4)),
      smt_->BitvectorConstantTerm(0xAAA, 4 * 3)));
  CheckValid(smt_->ApplyFunction(
      smt::op::kNot,
      smt_->ApplyFunction(
          smt::op::kEqual,
          smt_->ApplyFunction(repeat3, smt_->BitvectorConstantTerm(0xA, 4)),
          smt_->BitvectorConstantTerm(0xABA, 4 * 3))));
}

// TODO: Z3 fails this test - need to investigate.
TEST_P(SMTTest, TestRepeatFunctionWithDifferentIndicesNotEqual_DISABLED) {
  if (!TrySetLogic("QF_BV")) return;
  const Function repeat2 = smt_->GetTheoryFunction(smt::op::kRepeat, 2);
  const Function repeat3 = smt_->GetTheoryFunction(smt::op::kRepeat, 3);
  EXPECT_NE(repeat2, repeat3);
}

TEST_P(SMTTest, TestExtractFunctionWithDifferentIndicesNotEqual) {
  if (!TrySetLogic("QF_BV")) return;
  const Function extract_31_0 =
      smt_->GetTheoryFunction(smt::op::kExtract, 31, 0);
  const Function extract_31_1 =
      smt_->GetTheoryFunction(smt::op::kExtract, 31, 1);
  EXPECT_NE(extract_31_0, extract_31_1);
}

TEST_P(SMTTest, PlusFunctionIsNotNullFunction) {
  if (!TrySetLogic("QF_LRA")) return;
  Function plus_function = smt_->GetTheoryFunction(smt::op::kPlus);
  Function null_function;

  // This tests operator== for null_function appearing as both the left hand and
  // right hand side.
  EXPECT_NE(null_function, plus_function);
  EXPECT_NE(plus_function, null_function);
}

TEST_P(SMTTest, PlusFunctionEqualsItself) {
  if (!TrySetLogic("QF_LIA")) return;

  // This builds the plus function and checks that it equals the plus function.
  Function plus_function = smt_->GetTheoryFunction(smt::op::kPlus);

  EXPECT_EQ(plus_function, smt_->GetTheoryFunction(smt::op::kPlus));
}

TEST_P(SMTTest, PlusAndMultiplicationFunctionsNotOperatorEqual) {
  if (!TrySetLogic("QF_LIA")) return;

  // This builds the plus and multiplication functions and checks that they are
  // not equal.
  Function plus_function = smt_->GetTheoryFunction(smt::op::kPlus);
  Function mult_function = smt_->GetTheoryFunction(smt::op::kMult);

  EXPECT_NE(plus_function, mult_function);
}

TEST_P(SMTTest, FunctionObjectOperatorEqualToItself) {
  if (!TrySetLogic("QF_UF")) return;

  // This builds an uninterpreted function f and checks that it equals itself.
  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  Function f = smt_->DeclareFunction("f", bool_sort, bool_sort);

  EXPECT_EQ(f, f);
}

TEST_P(SMTTest, TwoNonSimpleFunctionsNotOperatorEqual) {
  if (!TrySetLogic("QF_UF")) return;

  // This builds two uninterpreted functions f and g and checks that they are
  // not the same.
  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  Function f = smt_->DeclareFunction("f", bool_sort, bool_sort);
  Function g = smt_->DeclareFunction("g", bool_sort, bool_sort);
  EXPECT_NE(f, g);
}

TEST_P(SMTTest, SimpleAndNonSimpleFunctionsNotOperatorEqual) {
  if (!TrySetLogic("QF_UF")) return;

  // This builds an uninterpreted function f and checks that it is not equal
  // to the plus function.
  Sort int_sort = smt_->GetTheorySort(smt::op::kInt);
  Function f = smt_->DeclareFunction("f", int_sort, int_sort, int_sort);
  EXPECT_NE(f, smt_->GetTheoryFunction(smt::op::kPlus));
}

TEST_P(SMTTest, TermDefaultConstructorGeneratesNullTerm) {
  if (!TrySetLogic("QF_BV")) return;
  Term null_term;
  EXPECT_TRUE(null_term.IsNull());
}

TEST_P(SMTTest, NullTermEqualsItself) {
  if (!TrySetLogic("QF_BV")) return;
  Term null_term;
  EXPECT_EQ(null_term, null_term);
}

TEST_P(SMTTest, FalseTermIsNotNullTerm) {
  if (!TrySetLogic("QF_BV")) return;
  Term false_term = smt_->GetTheoryConstantTerm(smt::op::kFalse);
  Term null_term;

  // This tests operator== for null_term appearing as both the left hand and
  // right hand side.
  EXPECT_NE(null_term, false_term);
  EXPECT_NE(false_term, null_term);
}

TEST_P(SMTTest, FalseTermEqualsItself) {
  if (!TrySetLogic("QF_BV")) return;
  // This builds a false Boolean term and checks that it equals itself.
  Term false_term = smt_->GetTheoryConstantTerm(smt::op::kFalse);

  EXPECT_EQ(false_term, smt_->GetTheoryConstantTerm(smt::op::kFalse));
}

TEST_P(SMTTest, TrueAndFalseTermsAreNotEqual) {
  if (!TrySetLogic("QF_BV")) return;
  // This builds the true and false terms and checks that they are not equal.
  Term false_term = smt_->GetTheoryConstantTerm(smt::op::kFalse);
  Term true_term = smt_->GetTheoryConstantTerm(smt::op::kTrue);

  EXPECT_NE(false_term, true_term);
}

TEST_P(SMTTest, BooleanTermDirectCreation) {
  if (!TrySetLogic("QF_BV")) return;
  // This builds a false Boolean term two different ways and checks that the
  // results are equal.
  EXPECT_EQ(smt_->BooleanTerm(false),
            smt_->GetTheoryConstantTerm(smt::op::kFalse));
  // This builds a true Boolean term two different ways and checks that the
  // results are equal.
  EXPECT_EQ(smt_->BooleanTerm(true),
            smt_->GetTheoryConstantTerm(smt::op::kTrue));
}

TEST_P(SMTTest, BV0IsNotNull) {
  if (!TrySetLogic("QF_BV")) return;
  const Term bv0 = smt_->BitvectorConstantTerm(0, 1);
  const Term term;
  EXPECT_FALSE(bv0 == term);
}

TEST_P(SMTTest, BV0EqualsItself) {
  if (!TrySetLogic("QF_BV")) return;
  const Term bv0 = smt_->BitvectorConstantTerm(0, 1);
  EXPECT_EQ(smt_->BitvectorConstantTerm(0, 1), bv0);
}

TEST_P(SMTTest, BvnotTermEqualsItself) {
  if (!TrySetLogic("QF_BV")) return;
  const Sort bitvector_sort = smt_->GetTheorySort(smt::op::kBitvec, 32);
  const Term x = smt_->DeclareFunction("x", bitvector_sort);
  const Term bvnot = smt_->ApplyFunction(smt::op::kBvnot, x);
  EXPECT_EQ(smt_->ApplyFunction(smt::op::kBvnot, x), bvnot);
}

TEST_P(SMTTest, BvandTermEqualsItself) {
  if (!TrySetLogic("QF_BV")) return;
  const Sort bitvector_sort = smt_->GetTheorySort(smt::op::kBitvec, 32);
  const Term x = smt_->DeclareFunction("x", bitvector_sort);
  const Term y = smt_->DeclareFunction("y", bitvector_sort);
  const Term bvand = smt_->ApplyFunction(smt::op::kBvand, x, y);
  EXPECT_EQ(smt_->ApplyFunction(smt::op::kBvand, x, y), bvand);
}

TEST_P(SMTTest, TestGetBVSize) {
  if (!TrySetLogic("QF_BV")) return;
  const Sort bitvector_sort = smt_->GetTheorySort(smt::op::kBitvec, 32);
  const Term x = smt_->DeclareFunction("x", bitvector_sort);
  EXPECT_EQ(x.GetBVSize(), 32);
}

TEST_P(SMTTest, TestGetSort) {
  if (!TrySetLogic("QF_BV")) return;
  const Sort bitvector_sort = smt_->GetTheorySort(smt::op::kBitvec, 32);
  const Term x = smt_->DeclareFunction("x", bitvector_sort);
  EXPECT_EQ(x.GetSort(), bitvector_sort);
}

TEST_P(SMTTest, NumeralTermWorksOnLowerLimit) {
  EXPECT_THAT(smt_->NumeralTerm(0).IntegerConstantToUint64(), IsOkAndHolds(0));
}

TEST_P(SMTTest, NumeralTermWorksOnUpperLimit) {
  EXPECT_THAT(smt_->NumeralTerm(std::numeric_limits<uint64_t>::max())
                  .IntegerConstantToUint64(),
              IsOkAndHolds(std::numeric_limits<uint64_t>::max()));
}

TEST_P(SMTTest, SignedNumeralTermWorksOnLowerLimit) {
  EXPECT_THAT(smt_->SignedNumeralTerm(std::numeric_limits<int64_t>::min())
                  .IntegerConstantToInt64(),
              IsOkAndHolds(std::numeric_limits<int64_t>::min()));
}

TEST_P(SMTTest, SignedNumeralTermWorksOnUpperLimit) {
  EXPECT_THAT(smt_->SignedNumeralTerm(std::numeric_limits<int64_t>::max())
                  .IntegerConstantToInt64(),
              IsOkAndHolds(std::numeric_limits<int64_t>::max()));
}

TEST_P(SMTTest, IntegerConstantToUint64CorrectlyReturnsError) {
  smt::Term negative_term = smt_->SignedNumeralTerm(-1);
  EXPECT_THAT(negative_term.IntegerConstantToUint64(),
              StatusIs(absl::StatusCode::kOutOfRange));
}

TEST_P(SMTTest, IntegerConstantToInt64CorrectlyReturnsError) {
  smt::Term negative_term = smt_->NumeralTerm(
      (static_cast<uint64_t>(std::numeric_limits<int64_t>::max()) + 1));
  EXPECT_THAT(negative_term.IntegerConstantToInt64(),
              StatusIs(absl::StatusCode::kOutOfRange));
}

TEST_P(SMTTest, TestUminusFiveIsNotIntegerConstant) {
  if (!TrySetLogic("QF_UFLIA")) return;
  EXPECT_FALSE(smt_->ApplyFunction(smt::op::kUminus, smt_->NumeralTerm(5))
                   .IsIntegerConstant());
}

TEST_P(SMTTest, TestUnconstrainedVarIsNotBoolConstant) {
  if (!TrySetLogic("QF_UFLIA")) return;
  smt::Term a = smt_->DeclareFunction("a", smt_->GetTheorySort(smt::op::kBool));
  EXPECT_FALSE(a.IsBoolConstant());
}

TEST_P(SMTTest, TestIsIntegerConstant) {
  if (!TrySetLogic("QF_UFLIA")) return;
  smt::Term a = smt_->DeclareFunction("a", smt_->GetTheorySort(smt::op::kInt));
  EXPECT_FALSE(a.IsIntegerConstant());
}

TEST_P(SMTTest, TestIsBVConstant) {
  if (!TrySetLogic("QF_BV")) return;
  const Sort bitvector_sort = smt_->GetTheorySort(smt::op::kBitvec, 32);
  const Term a = smt_->DeclareFunction("x", bitvector_sort);
  EXPECT_FALSE(a.IsBVConstant());
}

TEST_P(SMTTest, TestFiveIsIntegerConstant) {
  if (!TrySetLogic("QF_UFLIA")) return;
  EXPECT_TRUE(smt_->NumeralTerm(5).IsIntegerConstant());
}

TEST_P(SMTTest, TestBuiltinOperators) {
  if (!TrySetLogic("QF_BV")) return;
  const Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  const Term x = smt_->DeclareFunction("x", bool_sort);
  Function f = smt_->GetTheoryFunction(smt::op::kNot);
  smt_->ApplyFunction(f, x);
  f = smt_->GetTheoryFunction(smt::op::kImplies);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kAnd);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kOr);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kXor);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kEqual);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kDistinct);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kIte);
  smt_->ApplyFunction(f, x, x, x);
}

TEST_P(SMTTest, TestBVOperators) {
  if (!TrySetLogic("QF_BV")) return;
  const Sort bitvector_sort = smt_->GetTheorySort(smt::op::kBitvec, 32);
  const Term x = smt_->DeclareFunction("x", bitvector_sort);
  Function f = smt_->GetTheoryFunction(smt::op::kConcat);
  smt_->ApplyFunction(f, x, x);
  smt_->ApplyFunction(f, x, x, x);
  f = smt_->GetTheoryFunction(smt::op::kExtract, 15, 0);
  smt_->ApplyFunction(f, x);
  f = smt_->GetTheoryFunction(smt::op::kBvnot);
  smt_->ApplyFunction(f, x);
  f = smt_->GetTheoryFunction(smt::op::kBvand);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvor);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvneg);
  smt_->ApplyFunction(f, x);
  f = smt_->GetTheoryFunction(smt::op::kBvadd);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvmul);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvudiv);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvurem);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvnand);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvnor);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvxor);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvcomp);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvsub);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvsdiv);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvsrem);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvsmod);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kZeroExtend, 32);
  smt_->ApplyFunction(f, x);
  f = smt_->GetTheoryFunction(smt::op::kSignExtend, 16);
  smt_->ApplyFunction(f, x);
  f = smt_->GetTheoryFunction(smt::op::kBvult);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvule);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvugt);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvuge);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvslt);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvsle);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvsgt);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvsge);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvashr);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvlshr);
  smt_->ApplyFunction(f, x, x);
  f = smt_->GetTheoryFunction(smt::op::kBvshl);
  smt_->ApplyFunction(f, x, x);
}

TEST_P(SMTTest, UninterpretedFunctionsDiffer) {
  if (!TrySetLogic("QF_UFLIA")) return;

  // Build f(z) three ways and check that they are the same
  Sort int_sort = smt_->GetTheorySort(smt::op::kInt);
  Function f = smt_->DeclareFunction("f", int_sort, int_sort);
  Term z = smt_->DeclareFunction("z", int_sort);
  Term f1 = smt_->ApplyFunction(f, z);
  Term f2 = smt_->ApplyFunction(f, z);
  Term f3 = smt_->ApplyFunction(f, f1[0]);
  EXPECT_TRUE(f1 == f2 && f1 == f3 && f2 == f3);

  // Check f(f(z)) is not the same as f(z)
  Term f4 = smt_->ApplyFunction(f, f2);
  EXPECT_NE(f4, f1);
  EXPECT_NE(f4, f2);
  EXPECT_NE(f4, f3);
}

TEST_P(SMTTest, TestBoolIntSort) {
  if (!TrySetLogic("QF_UFLIA")) return;

  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  Sort int_sort = smt_->GetTheorySort(smt::op::kInt);

  Function f = smt_->DeclareFunction("f", bool_sort, int_sort);
  Term z = smt_->DeclareFunction("z", bool_sort);
  EXPECT_EQ(bool_sort, z.GetSort());

  Term fz = smt_->ApplyFunction(f, z);
  EXPECT_EQ(int_sort, fz.GetSort());
}

TEST_P(SMTTest, Test_UF_LIA_1) {
  if (!TrySetLogic("QF_UFLIA")) return;
  smt_->SetOption("produce-models", true);

  // Trivial check that "true" is satisfiable
  smt_->Push();
  smt_->AssertFormula(smt_->GetTheoryConstantTerm(smt::op::kTrue));
  smt::SMTSolver::CheckSatResponse b = smt_->CheckSat();
  EXPECT_EQ(b, smt::SMTSolver::kSat);
  smt_->Pop();

  // Trivial check that "false" is unsatisfiable
  smt_->Push();
  smt_->AssertFormula(smt_->GetTheoryConstantTerm(smt::op::kFalse));
  b = smt_->CheckSat();
  EXPECT_EQ(b, smt::SMTSolver::kUnsat);
  smt_->Pop();

  // Trivial check that BooleanTerm "true" is satisfiable
  smt_->Push();
  smt_->AssertFormula(smt_->BooleanTerm(true));
  b = smt_->CheckSat();
  EXPECT_EQ(b, smt::SMTSolver::kSat);
  smt_->Pop();

  // Trivial check that BooleanTerm "false" is unsatisfiable
  smt_->Push();
  smt_->AssertFormula(smt_->BooleanTerm(false));
  b = smt_->CheckSat();
  EXPECT_EQ(b, smt::SMTSolver::kUnsat);
  smt_->Pop();

  // Check p OR ~p
  smt_->Push();
  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  Term p = smt_->DeclareFunction("p", bool_sort);
  Term e = smt_->ApplyFunction(smt::op::kOr, p,
                               smt_->ApplyFunction(smt::op::kNot, p));
  EXPECT_TRUE(CheckValid(e));
  smt_->Pop();

  // Check x = y -> f(x) = f(y)
  smt_->Push();
  Sort int_sort = smt_->GetTheorySort(smt::op::kInt);
  Term x = smt_->DeclareFunction("x", int_sort);
  Term y = smt_->DeclareFunction("y", int_sort);

  Function f = smt_->DeclareFunction("f", int_sort, int_sort);
  Term fx = smt_->ApplyFunction(f, x);
  Term fy = smt_->ApplyFunction(f, y);
  e = smt_->ApplyFunction(smt::op::kImplies,
                          smt_->ApplyFunction(smt::op::kEqual, x, y),
                          smt_->ApplyFunction(smt::op::kEqual, fx, fy));
  EXPECT_TRUE(CheckValid(e));
  smt_->Pop();

  // Check f(x) = f(y) -> x = y
  smt_->Push();
  e = smt_->ApplyFunction(smt::op::kImplies,
                          smt_->ApplyFunction(smt::op::kEqual, fx, fy),
                          smt_->ApplyFunction(smt::op::kEqual, x, y));
  EXPECT_FALSE(CheckValid(e));

  // Get counter-example
  Term value1 = smt_->GetValue(fx);
  Term value2 = smt_->GetValue(fy);
  EXPECT_TRUE(value1.IsIntegerConstant());
  EXPECT_TRUE(value2.IsIntegerConstant());
  EXPECT_EQ(value1, value2);
  EXPECT_TRUE(smt_->GetValue(x).IsIntegerConstant());
  EXPECT_TRUE(smt_->GetValue(y).IsIntegerConstant());
  EXPECT_NE(smt_->GetValue(x), smt_->GetValue(y));

  // Reset to initial scope
  smt_->Pop();

  // Check w = x & x = y & y = z & f(x) = f(y) & x = 1 & z = 2
  Term w = smt_->DeclareFunction("w", int_sort);
  Term z = smt_->DeclareFunction("z", int_sort);
  smt_->Push();
  smt_->AssertFormula(smt_->ApplyFunction(smt::op::kEqual, w, x));
  smt_->AssertFormula(smt_->ApplyFunction(smt::op::kEqual, x, y));
  smt_->AssertFormula(smt_->ApplyFunction(smt::op::kEqual, y, z));
  smt_->AssertFormula(smt_->ApplyFunction(smt::op::kEqual, fx, fy));
  smt_->AssertFormula(
      smt_->ApplyFunction(smt::op::kEqual, x, smt_->NumeralTerm(1)));
  smt_->AssertFormula(
      smt_->ApplyFunction(smt::op::kEqual, z, smt_->NumeralTerm(2)));
  b = smt_->CheckSat();
  EXPECT_EQ(b, smt::SMTSolver::kUnsat);
  smt_->Pop();
}

TEST_P(SMTTest, Test_UF_LRA_2) {
  if (!TrySetLogic("QF_UFLRA")) return;
  smt_->SetOption("produce-models", true);

  // b < 10 && (c = 0 || c = 1) => b <= 10
  Sort int_sort = smt_->GetTheorySort(smt::op::kInt);
  Term bexpr = smt_->DeclareFunction("b", int_sort);
  smt_->AssertFormula(
      smt_->ApplyFunction(smt::op::kLt, bexpr, smt_->NumeralTerm(10)));
  Term c = smt_->DeclareFunction("c", int_sort);
  Term e = smt_->ApplyFunction(smt::op::kEqual, c, smt_->NumeralTerm(0));
  e = smt_->ApplyFunction(
      smt::op::kOr, e,
      smt_->ApplyFunction(smt::op::kEqual, c, smt_->NumeralTerm(1)));
  smt_->Push();
  EXPECT_TRUE(CheckValid(
      smt_->ApplyFunction(smt::op::kLe, bexpr, smt_->NumeralTerm(10))));
  smt_->Pop();

  // Check that false is invalid
  smt_->Push();
  EXPECT_FALSE(CheckValid(smt_->GetTheoryConstantTerm(smt::op::kFalse)));
  smt_->Pop();

  // Check x = y -> g(x,y) = g(y,x)
  Sort real_sort = smt_->GetTheorySort(smt::op::kReal);
  Term x = smt_->DeclareFunction("x", real_sort);
  Term y = smt_->DeclareFunction("y", real_sort);
  std::vector<Sort> rank{real_sort, real_sort, real_sort};
  Function g = smt_->DeclareFunction("g", rank);
  Term gxy = smt_->ApplyFunction(g, x, y);
  Term gyx = smt_->ApplyFunction(g, y, x);
  e = smt_->ApplyFunction(smt::op::kImplies,
                          smt_->ApplyFunction(smt::op::kEqual, x, y),
                          smt_->ApplyFunction(smt::op::kEqual, gxy, gyx));
  smt_->Push();
  EXPECT_TRUE(CheckValid(e));
  smt_->Pop();

  // Check x = y => h(x,y) = h(y,x)
  Function h = smt_->DeclareFunction("h", rank);
  Term hxy = smt_->ApplyFunction(h, x, y);
  Term hyx = smt_->ApplyFunction(h, y, x);
  e = smt_->ApplyFunction(smt::op::kImplies,
                          smt_->ApplyFunction(smt::op::kEqual, x, y),
                          smt_->ApplyFunction(smt::op::kEqual, hxy, hyx));
  EXPECT_TRUE(CheckValid(e));
}

TEST_P(SMTTest, TestStringSimple) {
  if (!TrySetLogic("QF_S")) return;

  const Sort string_sort = smt_->GetTheorySort(smt::op::kString);
  const Term hello = smt_->StringConstantTerm("hello");
  const Term var = smt_->DeclareFunction("var", string_sort);

  smt_->AssertFormula(smt_->ApplyFunction(smt::op::kEqual, var, hello));
  const smt::SMTSolver::CheckSatResponse response = smt_->CheckSat();

  EXPECT_EQ(response, smt::SMTSolver::kSat);
}

TEST_P(SMTTest, TestStringGetValue) {
  if (!TrySetLogic("QF_S")) return;
  smt_->SetOption("produce-models", true);

  const Sort string_sort = smt_->GetTheorySort(smt::op::kString);
  const Term var = smt_->DeclareFunction("var", string_sort);
  const Term k = smt_->StringConstantTerm("k");

  // Length 2 string that starts and ends in k.
  smt_->AssertFormula(smt_->ApplyFunction(
      smt::op::kEqual, smt_->ApplyFunction(smt::op::kStrLen, var),
      smt_->NumeralTerm(2)));
  smt_->AssertFormula(smt_->ApplyFunction(smt::op::kStrStarts, k, var));
  smt_->AssertFormula(smt_->ApplyFunction(smt::op::kStrEnds, k, var));

  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);
  const Term value = smt_->GetValue(var);
  EXPECT_TRUE(value.IsStringConstant());
  EXPECT_EQ(value.GetSort(), string_sort);
  EXPECT_EQ(value, smt_->StringConstantTerm("kk"));
}

TEST_P(SMTTest, TestStringConstantIsStringConstant) {
  if (!TrySetLogic("QF_S")) return;
  EXPECT_TRUE(smt_->StringConstantTerm("k").IsStringConstant());
}

TEST_P(SMTTest, TestStringVarIsNotStringConstant) {
  if (!TrySetLogic("QF_S")) return;
  const Sort string_sort = smt_->GetTheorySort(smt::op::kString);
  EXPECT_FALSE(smt_->DeclareFunction("v", string_sort).IsStringConstant());
}

TEST_P(SMTTest, TestGetStringConstantAllOneLetterStrings) {
  if (!TrySetLogic("QF_S")) return;
  smt_->SetOption("produce-models", true);
  const Sort string_sort = smt_->GetTheorySort(smt::op::kString);
  for (unsigned char i = 0; i < 255; ++i) {
    const auto str = std::string(1, i);
    const auto str_constant = smt_->StringConstantTerm(str);
    EXPECT_TRUE(str_constant.IsStringConstant());
    EXPECT_EQ(str_constant.GetStringConstant().size(), 1);
    EXPECT_EQ(str_constant.GetStringConstant(), str);
  }
}

TEST_P(SMTTest, TestGetStringConstantAllOneLetterStringsGetModel) {
  if (!TrySetLogic("QF_S")) return;
  // We also test it via a solve, sometimes find bugs this way in other parts.
  smt_->SetOption("produce-models", true);
  const Sort string_sort = smt_->GetTheorySort(smt::op::kString);
  for (unsigned char i = 0; i < 255; ++i) {
    smt_->Push();
    const auto str = std::string(1, i);
    const auto var = smt_->DeclareFunction("var", string_sort);
    smt_->AssertFormula(smt_->ApplyFunction(smt::op::kEqual, var,
                                            smt_->StringConstantTerm(str)));
    EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);
    const Term value = smt_->GetValue(var);
    EXPECT_TRUE(value.IsStringConstant());
    EXPECT_EQ(value.GetStringConstant().size(), 1);
    EXPECT_EQ(value.GetStringConstant(), str);
    smt_->Pop();
  }
}

TEST_P(SMTTest, TestGetStringConstantEmptyAndLongerStrings) {
  if (!TrySetLogic("QF_S")) return;
  const std::vector<std::string> strings_to_test = {
      "",
      "simple"
      "string with spaces",
      "string with\tall kinds of\nwhitespaces\n\t",
      "\"\"",
      "\"quoted\"",
      "\'\"Hello!\" said Simon.'",
      "Hello\x00World",
      "\x01\x05\x0a\x15",
      "\x01\x01\x02\x04\x01",
      "||",
      "|foo|",
      "||foo||",
      "\\\\",
      "\\\\\\",
      "\\a",
      "\\n",
      "\\|foo\\|",
      "\\x1",
      "\\x01",
      "\0",
      "\0\0",
      "\\0"};

  smt_->SetOption("produce-models", true);
  const Sort string_sort = smt_->GetTheorySort(smt::op::kString);
  for (const auto& str : strings_to_test) {
    smt_->Push();
    const auto var = smt_->DeclareFunction("var", string_sort);
    smt_->AssertFormula(smt_->ApplyFunction(smt::op::kEqual, var,
                                            smt_->StringConstantTerm(str)));
    EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);
    const Term value = smt_->GetValue(var);
    EXPECT_TRUE(value.IsStringConstant());
    EXPECT_EQ(value.GetStringConstant().size(), str.size());
    EXPECT_EQ(value.GetStringConstant(), str);
    smt_->Pop();
  }
}

TEST_P(SMTTest, TestOperatorStrLen) {
  if (!TrySetLogic("QF_S")) return;
  smt_->SetOption("produce-models", true);

  const Term hello = smt_->StringConstantTerm("hello");
  const Term hello_length = smt_->ApplyFunction(smt::op::kStrLen, hello);
  const Term hello_length_is_5 =
      smt_->ApplyFunction(smt::op::kEqual, hello_length, smt_->NumeralTerm(5));

  smt_->Push();
  EXPECT_TRUE(CheckValid(hello_length_is_5));
  smt_->Pop();
}

TEST_P(SMTTest, TestOperatorStrStarts) {
  if (!TrySetLogic("QF_S")) return;
  smt_->SetOption("produce-models", true);

  const Term hello = smt_->StringConstantTerm("hello");
  const Term he = smt_->StringConstantTerm("he");
  const Term hello_starts_with_he =
      smt_->ApplyFunction(smt::op::kStrStarts, he, hello);

  smt_->Push();
  EXPECT_TRUE(CheckValid(hello_starts_with_he));
  smt_->Pop();
}

TEST_P(SMTTest, TestOperatorStrEnds) {
  if (!TrySetLogic("QF_S")) return;
  smt_->SetOption("produce-models", true);

  const Term hello = smt_->StringConstantTerm("hello");
  const Term lo = smt_->StringConstantTerm("lo");
  const Term hello_ends_with_lo =
      smt_->ApplyFunction(smt::op::kStrEnds, lo, hello);
  smt_->Push();
  EXPECT_TRUE(CheckValid(hello_ends_with_lo));
  smt_->Pop();
}

TEST_P(SMTTest, TestOperatorStrConcat) {
  if (!TrySetLogic("QF_S")) return;
  smt_->SetOption("produce-models", true);

  const Term hello = smt_->StringConstantTerm("hello");
  const Term h = smt_->StringConstantTerm("h");
  const Term e = smt_->StringConstantTerm("e");
  const Term l = smt_->StringConstantTerm("l");
  const Term o = smt_->StringConstantTerm("o");
  const Term concat_h_e_l_l_o = smt_->ApplyFunction(
      smt::op::kStrConcat, std::vector<Term>{h, e, l, l, o});
  const Term hello_is_concat_h_e_l_l_o =
      smt_->ApplyFunction(smt::op::kEqual, hello, concat_h_e_l_l_o);

  smt_->Push();
  EXPECT_TRUE(CheckValid(hello_is_concat_h_e_l_l_o));
  smt_->Pop();
}

TEST_P(SMTTest, TestOperatorStrAt) {
  if (!TrySetLogic("QF_S")) return;
  smt_->SetOption("produce-models", true);

  const Term hello = smt_->StringConstantTerm("hello");
  const Term letter_e = smt_->StringConstantTerm("e");

  const Term second_letter_of_hello =
      smt_->ApplyFunction(smt::op::kStrAt, hello, smt_->NumeralTerm(1));
  const Term e_is_second_letter_of_hello =
      smt_->ApplyFunction(smt::op::kEqual, letter_e, second_letter_of_hello);

  smt_->Push();
  EXPECT_TRUE(CheckValid(e_is_second_letter_of_hello));
  smt_->Pop();
}

TEST_P(SMTTest, TestOperatorStrContains) {
  if (!TrySetLogic("QF_S")) return;
  smt_->SetOption("produce-models", true);

  const Term hello = smt_->StringConstantTerm("hello");
  const Term ell = smt_->StringConstantTerm("ell");

  const Term hello_contains_ell =
      smt_->ApplyFunction(smt::op::kStrContains, hello, ell);

  smt_->Push();
  EXPECT_TRUE(CheckValid(hello_contains_ell));
  smt_->Pop();
}

TEST_P(SMTTest, TestOperatorStrSubstr) {
  if (!TrySetLogic("QF_S")) return;
  smt_->SetOption("produce-models", true);

  const Term hello = smt_->StringConstantTerm("hello");
  const Term ell = smt_->StringConstantTerm("ell");
  const Term substr_hello_1_3 = smt_->ApplyFunction(
      smt::op::kStrSubstr, hello, smt_->NumeralTerm(1), smt_->NumeralTerm(3));
  const Term substr_hello_1_3_isell =
      smt_->ApplyFunction(smt::op::kEqual, substr_hello_1_3, ell);

  smt_->Push();
  EXPECT_TRUE(CheckValid(substr_hello_1_3_isell));
  smt_->Pop();
}

TEST_P(SMTTest, TestOperatorStrSubstrFromBeginningOfString) {
  if (!TrySetLogic("QF_S")) return;
  smt_->SetOption("produce-models", true);

  const Term hello = smt_->StringConstantTerm("hello");
  const Term he = smt_->StringConstantTerm("he");
  const Term substr_hello_0_2 = smt_->ApplyFunction(
      smt::op::kStrSubstr, hello, smt_->NumeralTerm(0), smt_->NumeralTerm(2));
  const Term substr_hello_0_2_isell =
      smt_->ApplyFunction(smt::op::kEqual, substr_hello_0_2, he);

  smt_->Push();
  EXPECT_TRUE(CheckValid(substr_hello_0_2_isell));
  smt_->Pop();
}

TEST_P(SMTTest, TestOperatorStrReplace) {
  if (!TrySetLogic("QF_S")) return;
  smt_->SetOption("produce-models", true);

  const Term hello = smt_->StringConstantTerm("hello");
  const Term ell = smt_->StringConstantTerm("ell");
  const Term er = smt_->StringConstantTerm("er");
  const Term hero = smt_->StringConstantTerm("hero");
  const Term substituted_string =
      smt_->ApplyFunction(smt::op::kStrReplace, hello, ell, er);
  const Term hero_is_substituted_string =
      smt_->ApplyFunction(smt::op::kEqual, hero, substituted_string);

  smt_->Push();
  EXPECT_TRUE(CheckValid(hero_is_substituted_string));
  smt_->Pop();
}

TEST_P(SMTTest, TestOperatorStrLt) {
  if (!TrySetLogic("QF_S")) return;
  smt_->SetOption("produce-models", true);

  const std::vector string_terms({"abc", "cde", "cdef", "abcd", ""});
  for (const std::string first_string : string_terms) {
    for (const std::string second_string : string_terms) {
      const Term first_term = smt_->StringConstantTerm(first_string);
      const Term second_term = smt_->StringConstantTerm(second_string);
      const Term comparison =
          smt_->ApplyFunction(smt::op::kStrLt, first_term, second_term);
      smt_->Push();
      EXPECT_EQ(CheckValid(comparison), first_string < second_string)
          << first_string << " < " << second_string;
      smt_->Pop();
    }
  }
}

TEST_P(SMTTest, TestOperatorStrLe) {
  if (!TrySetLogic("QF_S")) return;
  smt_->SetOption("produce-models", true);
  const std::vector string_terms({"abc", "cde", "cdef", "abcd", ""});
  for (const std::string first_string : string_terms) {
    for (const std::string second_string : string_terms) {
      const Term first_term = smt_->StringConstantTerm(first_string);
      const Term second_term = smt_->StringConstantTerm(second_string);
      const Term comparison =
          smt_->ApplyFunction(smt::op::kStrLe, first_term, second_term);
      smt_->Push();
      EXPECT_EQ(CheckValid(comparison), first_string <= second_string)
          << first_string << " <= " << second_string;
      smt_->Pop();
    }
  }
}

TEST_P(SMTTest, TestOperatorStrToRegExp) {
  if (!TrySetLogic("QF_S")) return;

  const Term test = smt_->StringConstantTerm("test");
  const Term regexp = smt_->ApplyFunction(smt::op::kStrToRe, test);

  const Term test_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, test, regexp);

  smt_->Push();
  EXPECT_TRUE(CheckValid(test_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestOperatorStrToRegExpNoMatch) {
  if (!TrySetLogic("QF_S")) return;

  const Term test = smt_->StringConstantTerm("test");
  const Term table = smt_->StringConstantTerm("table");
  const Term regexp = smt_->ApplyFunction(smt::op::kStrToRe, test);

  const Term table_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, table, regexp);

  smt_->Push();
  EXPECT_FALSE(CheckValid(table_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestOperatorStrToInt) {
  if (!TrySetLogic("QF_S")) return;

  const Term num_as_string = smt_->StringConstantTerm("32");
  const Term num_as_num = smt_->NumeralTerm(32);
  const Term conversion_matches = smt_->ApplyFunction(
      smt::op::kEqual, smt_->ApplyFunction(smt::op::kStrToInt, num_as_string),
      num_as_num);

  smt_->Push();
  EXPECT_TRUE(CheckValid(conversion_matches));
  smt_->Pop();
}

TEST_P(SMTTest, TestOperatorStrToIntNegativeValueReturnsErrorCode) {
  if (!TrySetLogic("QF_S")) return;

  // Strings representing negative values are not supported; instead -1 is
  // returned as an error code.
  // https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml
  const Term num_as_string = smt_->StringConstantTerm("-32");
  const Term expected_error_code = smt_->SignedNumeralTerm(-1);
  const Term conversion_matches_error_code = smt_->ApplyFunction(
      smt::op::kEqual, smt_->ApplyFunction(smt::op::kStrToInt, num_as_string),
      expected_error_code);

  smt_->Push();
  EXPECT_TRUE(CheckValid(conversion_matches_error_code));

  smt_->Pop();
}

TEST_P(SMTTest, TestOperatorStrFromInt) {
  if (!TrySetLogic("QF_S")) return;

  const Term num_as_string = smt_->StringConstantTerm("32");
  const Term num_as_num = smt_->NumeralTerm(32);
  const Term conversion_matches = smt_->ApplyFunction(
      smt::op::kEqual, smt_->ApplyFunction(smt::op::kStrFromInt, num_as_num),
      num_as_string);

  smt_->Push();
  EXPECT_TRUE(CheckValid(conversion_matches));
  smt_->Pop();
}

TEST_P(SMTTest, TestOperatorStrFromNegativeIntNotSupported) {
  if (!TrySetLogic("QF_S")) return;

  // Negative values cannot be converted to string, instead an empty string is
  // returned as an error code.
  // https://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml
  const Term negative_num = smt_->SignedNumeralTerm(-32);
  const Term empty_string_error_code = smt_->StringConstantTerm("");
  const Term conversion_matches_error_code = smt_->ApplyFunction(
      smt::op::kEqual, smt_->ApplyFunction(smt::op::kStrFromInt, negative_num),
      empty_string_error_code);

  smt_->Push();
  EXPECT_TRUE(CheckValid(conversion_matches_error_code));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetStringOptionRegExpMissing) {
  if (!TrySetLogic("QF_S")) return;

  const Term t = smt_->StringConstantTerm("t");
  const Term emp = smt_->StringConstantTerm("");
  const Term t_re = smt_->ApplyFunction(smt::op::kStrToRe, t);
  const Term optional_t_re = smt_->ApplyFunction(smt::op::kReOption, t_re);

  const Term emp_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, emp, optional_t_re);

  smt_->Push();
  EXPECT_TRUE(CheckValid(emp_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetStringOptionRegExpPresent) {
  if (!TrySetLogic("QF_S")) return;

  const Term t = smt_->StringConstantTerm("t");
  const Term t_re = smt_->ApplyFunction(smt::op::kStrToRe, t);
  const Term optional_t_re = smt_->ApplyFunction(smt::op::kReOption, t_re);

  const Term t_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, t, optional_t_re);

  smt_->Push();
  EXPECT_TRUE(CheckValid(t_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetStringOptionRegExpNoMatch) {
  if (!TrySetLogic("QF_S")) return;

  const Term t = smt_->StringConstantTerm("t");
  const Term ttt = smt_->StringConstantTerm("ttt");
  const Term t_re = smt_->ApplyFunction(smt::op::kStrToRe, t);
  const Term optional_t_re = smt_->ApplyFunction(smt::op::kReOption, t_re);

  const Term ttt_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, ttt, optional_t_re);

  smt_->Push();
  EXPECT_FALSE(CheckValid(ttt_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetStringStarRegExpEmptyStr) {
  if (!TrySetLogic("QF_S")) return;

  const Term t = smt_->StringConstantTerm("t");
  const Term emp = smt_->StringConstantTerm("");
  const Term t_re = smt_->ApplyFunction(smt::op::kStrToRe, t);
  const Term star_t_re = smt_->ApplyFunction(smt::op::kReStar, t_re);

  const Term emp_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, emp, star_t_re);

  smt_->Push();
  EXPECT_TRUE(CheckValid(emp_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetStringStarRegExpPresent) {
  if (!TrySetLogic("QF_S")) return;

  const Term t = smt_->StringConstantTerm("t");
  const Term tttt = smt_->StringConstantTerm("tttt");
  const Term t_re = smt_->ApplyFunction(smt::op::kStrToRe, t);
  const Term star_t_re = smt_->ApplyFunction(smt::op::kReStar, t_re);

  const Term tttt_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, tttt, star_t_re);

  smt_->Push();
  EXPECT_TRUE(CheckValid(tttt_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetStringStarRegExpNoMatch) {
  if (!TrySetLogic("QF_S")) return;

  const Term t = smt_->StringConstantTerm("t");
  const Term ttta = smt_->StringConstantTerm("ttta");
  const Term t_re = smt_->ApplyFunction(smt::op::kStrToRe, t);
  const Term star_t_re = smt_->ApplyFunction(smt::op::kReStar, t_re);

  const Term ttta_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, ttta, star_t_re);

  smt_->Push();
  EXPECT_FALSE(CheckValid(ttta_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetStringRegExpPlusSingle) {
  if (!TrySetLogic("QF_S")) return;

  const Term t = smt_->StringConstantTerm("t");
  const Term t_re = smt_->ApplyFunction(smt::op::kStrToRe, t);
  const Term plus_t_re = smt_->ApplyFunction(smt::op::kRePlus, t_re);

  const Term t_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, t, plus_t_re);

  smt_->Push();
  EXPECT_TRUE(CheckValid(t_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetStringRegExpPlusRepeated) {
  if (!TrySetLogic("QF_S")) return;

  const Term t = smt_->StringConstantTerm("t");
  const Term tttt = smt_->StringConstantTerm("tttt");
  const Term t_re = smt_->ApplyFunction(smt::op::kStrToRe, t);
  const Term plus_t_re = smt_->ApplyFunction(smt::op::kRePlus, t_re);

  const Term tttt_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, tttt, plus_t_re);

  smt_->Push();
  EXPECT_TRUE(CheckValid(tttt_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetStringRegExpPlusNoMatch) {
  if (!TrySetLogic("QF_S")) return;

  const Term t = smt_->StringConstantTerm("t");
  const Term emp = smt_->StringConstantTerm("");
  const Term t_re = smt_->ApplyFunction(smt::op::kStrToRe, t);
  const Term plus_t_re = smt_->ApplyFunction(smt::op::kRePlus, t_re);

  const Term emp_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, emp, plus_t_re);

  smt_->Push();
  EXPECT_FALSE(CheckValid(emp_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestRegExpRangeInRange) {
  if (!TrySetLogic("QF_S")) return;

  const Term p = smt_->StringConstantTerm("p");
  const Term r = smt_->StringConstantTerm("r");
  const Term q = smt_->StringConstantTerm("q");
  const Term p_r_range_re = smt_->ApplyFunction(smt::op::kReRange, p, r);

  const Term q_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, q, p_r_range_re);

  smt_->Push();
  EXPECT_TRUE(CheckValid(q_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestRegExpRangeNotInRange) {
  if (!TrySetLogic("QF_S")) return;

  const Term p = smt_->StringConstantTerm("p");
  const Term r = smt_->StringConstantTerm("r");
  const Term z = smt_->StringConstantTerm("z");
  const Term p_r_range_re = smt_->ApplyFunction(smt::op::kReRange, p, r);

  const Term z_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, z, p_r_range_re);

  smt_->Push();
  EXPECT_FALSE(CheckValid(z_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetStringRegExpIntersection) {
  const Term p_z_range_re =
      smt_->ApplyFunction(smt::op::kReRange, smt_->StringConstantTerm("p"),
                          smt_->StringConstantTerm("z"));
  const Term m_s_range_re =
      smt_->ApplyFunction(smt::op::kReRange, smt_->StringConstantTerm("m"),
                          smt_->StringConstantTerm("s"));
  const Term q = smt_->StringConstantTerm("q");

  const Term intersect =
      smt_->ApplyFunction(smt::op::kReIntersect, p_z_range_re, m_s_range_re);

  const Term q_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, q, intersect);

  smt_->Push();
  EXPECT_TRUE(CheckValid(q_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetStringRegExpIntersectionNoMatch) {
  const Term p_z_range_re =
      smt_->ApplyFunction(smt::op::kReRange, smt_->StringConstantTerm("p"),
                          smt_->StringConstantTerm("z"));
  const Term m_r_range_re =
      smt_->ApplyFunction(smt::op::kReRange, smt_->StringConstantTerm("m"),
                          smt_->StringConstantTerm("r"));
  const Term s = smt_->StringConstantTerm("s");

  const Term intersect =
      smt_->ApplyFunction(smt::op::kReIntersect, p_z_range_re, m_r_range_re);

  const Term s_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, s, intersect);

  smt_->Push();
  EXPECT_FALSE(CheckValid(s_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetStringRegExpUnion) {
  const Term p_z_range_re =
      smt_->ApplyFunction(smt::op::kReRange, smt_->StringConstantTerm("p"),
                          smt_->StringConstantTerm("z"));
  const Term m_r_range_re =
      smt_->ApplyFunction(smt::op::kReRange, smt_->StringConstantTerm("m"),
                          smt_->StringConstantTerm("r"));
  const Term s = smt_->StringConstantTerm("s");

  const Term union_re =
      smt_->ApplyFunction(smt::op::kReUnion, p_z_range_re, m_r_range_re);

  const Term s_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, s, union_re);

  smt_->Push();
  EXPECT_TRUE(CheckValid(s_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetStringRegExpUnionNoMatch) {
  const Term p_z_range_re =
      smt_->ApplyFunction(smt::op::kReRange, smt_->StringConstantTerm("p"),
                          smt_->StringConstantTerm("z"));
  const Term m_r_range_re =
      smt_->ApplyFunction(smt::op::kReRange, smt_->StringConstantTerm("m"),
                          smt_->StringConstantTerm("r"));
  const Term h = smt_->StringConstantTerm("h");

  const Term union_re =
      smt_->ApplyFunction(smt::op::kReUnion, p_z_range_re, m_r_range_re);

  const Term h_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, h, union_re);

  smt_->Push();
  EXPECT_FALSE(CheckValid(h_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetStringRegExpConcat) {
  const Term p_z_range_re =
      smt_->ApplyFunction(smt::op::kReRange, smt_->StringConstantTerm("p"),
                          smt_->StringConstantTerm("z"));
  const Term m_r_range_re =
      smt_->ApplyFunction(smt::op::kReRange, smt_->StringConstantTerm("m"),
                          smt_->StringConstantTerm("r"));
  const Term sn = smt_->StringConstantTerm("sn");

  const Term concat_re =
      smt_->ApplyFunction(smt::op::kReConcat, p_z_range_re, m_r_range_re);

  const Term sn_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, sn, concat_re);

  smt_->Push();
  EXPECT_TRUE(CheckValid(sn_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetStringRegExpConcatNoMatch) {
  const Term p_z_range_re =
      smt_->ApplyFunction(smt::op::kReRange, smt_->StringConstantTerm("p"),
                          smt_->StringConstantTerm("z"));
  const Term m_r_range_re =
      smt_->ApplyFunction(smt::op::kReRange, smt_->StringConstantTerm("m"),
                          smt_->StringConstantTerm("r"));
  const Term s = smt_->StringConstantTerm("s");

  const Term concat_re =
      smt_->ApplyFunction(smt::op::kReConcat, p_z_range_re, m_r_range_re);

  const Term s_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, s, concat_re);

  smt_->Push();
  EXPECT_FALSE(CheckValid(s_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestRegexpEmptyDoesntContainSimpleString) {
  const Term empty_re = smt_->GetTheoryConstantTerm(smt::op::kReEmpty);

  const Term s = smt_->StringConstantTerm("s");
  const Term s_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, s, empty_re);

  smt_->Push();
  EXPECT_FALSE(CheckValid(s_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestRegexpEmptyDoesntContainEmptyString) {
  const Term empty_re = smt_->GetTheoryConstantTerm(smt::op::kReEmpty);

  const Term s = smt_->StringConstantTerm("");
  const Term s_matches_regexp =
      smt_->ApplyFunction(smt::op::kStrInRe, s, empty_re);

  smt_->Push();
  EXPECT_FALSE(CheckValid(s_matches_regexp));
  smt_->Pop();
}

TEST_P(SMTTest, TestOperatorIntegerModulo) {
  if (!TrySetLogic("QF_NIA")) return;

  const smt::Term dividend = smt_->NumeralTerm("3");
  const smt::Term divisor = smt_->NumeralTerm("2");
  const smt::Term mod_operation =
      smt_->ApplyFunction(smt::op::kMod, dividend, divisor);
  const smt::Term result = smt_->NumeralTerm("1");
  const smt::Term mod_op_equals_1 =
      smt_->ApplyFunction(smt::op::kEqual, result, mod_operation);

  smt_->Push();
  EXPECT_TRUE(CheckValid(mod_op_equals_1));
  smt_->Pop();
}

TEST_P(SMTTest, TestBVUGE) {
  if (!TrySetLogic("QF_BV")) return;

  smt_->SetOption("produce-models", true);

  // Check x >= y -> (x > y or x == y)
  Sort bitvector_sort = smt_->GetTheorySort(smt::op::kBitvec, 4);
  Term x = smt_->DeclareFunction("x", bitvector_sort);
  Term y = smt_->DeclareFunction("y", bitvector_sort);
  Term x_ge_y = smt_->ApplyFunction(smt::op::kBvuge, x, y);
  Term x_gt_y = smt_->ApplyFunction(smt::op::kBvugt, x, y);
  Term x_eq_y = smt_->ApplyFunction(smt::op::kEqual, x, y);
  Term disjunction_term = smt_->ApplyFunction(smt::op::kOr, x_gt_y, x_eq_y);
  Term implication_term =
      smt_->ApplyFunction(smt::op::kImplies, x_ge_y, disjunction_term);
  EXPECT_TRUE(CheckValid(implication_term));
}

// The incremental tests are adapted from Z3/examples/c++/example.cpp.

TEST_P(SMTTest, TestIncrementalModeWithMultipleCheckSat) {
  if (!TrySetLogic("QF_UFLRA")) return;
  Sort int_sort = smt_->GetTheorySort(smt::op::kInt);
  Term xexpr = smt_->DeclareFunction("x", int_sort);

  // Formula: x > 0, should be satisfiable.
  smt_->AssertFormula(
      smt_->ApplyFunction(smt::op::kGt, xexpr, smt_->NumeralTerm(0)));
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);

  // Forumula: x > 0 && x < 0, should be unsatisfiable.
  smt_->AssertFormula(
      smt_->ApplyFunction(smt::op::kLt, xexpr, smt_->NumeralTerm(0)));
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kUnsat);
}

TEST_P(SMTTest, TestIncrementalModeWithPushPop) {
  if (!TrySetLogic("QF_UFLRA")) return;

  Sort int_sort = smt_->GetTheorySort(smt::op::kInt);
  Term xexpr = smt_->DeclareFunction("x", int_sort);

  // Formula: x > 0, should be satisfiable.
  smt_->AssertFormula(
      smt_->ApplyFunction(smt::op::kGt, xexpr, smt_->NumeralTerm(0)));
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);

  smt_->Push();

  // Forumula: x > 0 && x < 0, should be unsatisfiable.
  smt_->AssertFormula(
      smt_->ApplyFunction(smt::op::kLt, xexpr, smt_->NumeralTerm(0)));
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kUnsat);
  smt_->Pop();

  // Formula: x > 0, should be satisfiable.
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);
}

TEST_P(SMTTest, TestDisableFormulasByImplicationInIncrementalMode) {
  if (!TrySetLogic("QF_UFLRA")) return;

  Sort int_sort = smt_->GetTheorySort(smt::op::kInt);
  Term xexpr = smt_->DeclareFunction("x", int_sort);

  // Formula: x > 0, should be satisfiable.
  smt_->AssertFormula(
      smt_->ApplyFunction(smt::op::kGt, xexpr, smt_->NumeralTerm(0)));
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);

  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  Term bexpr = smt_->DeclareFunction("b", bool_sort);

  // Formula: x > 0 && b -> (x < 0), should be satisfiable.
  smt_->AssertFormula(smt_->ApplyFunction(
      smt::op::kImplies, bexpr,
      smt_->ApplyFunction(smt::op::kLt, xexpr, smt_->NumeralTerm(0))));
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);
  smt_->Push();

  // Formula: x > 0 && b -> (x < 0) && b, should be unsatisfiable.
  EXPECT_FALSE(CheckValid(bexpr));
  smt_->Pop();

  // Formula: x > 0 && b -> (x < 0), should be satisfiable.
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);
  smt_->Push();

  // Formula: x > 0 && b -> (x < 0) && !b, should be satisfiable.
  EXPECT_TRUE(CheckValid(smt_->ApplyFunction(smt::op::kNot, bexpr)));
  smt_->Pop();
}

TEST_P(SMTTest, TestGetValueUnconstrainedVar) {
  if (!TrySetLogic("AUFLIRA")) return;
  smt_->SetOption("produce-models", true);
  const Sort int_sort = smt_->GetTheorySort(smt::op::kInt);
  const Term int_term = smt_->DeclareFunction("a", int_sort);
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);
  const Term value = smt_->GetValue(int_term);
  EXPECT_EQ(value.GetSort(), int_sort);
  int dummy;
  EXPECT_TRUE(absl::SimpleAtoi(value.ToString(), &dummy));
}

TEST_P(SMTTest, IntegerConstantToInt64Succeeds) {
  if (!TrySetLogic("QF_LIA")) return;
  const Term numeral_term = smt_->NumeralTerm(55);
  EXPECT_TRUE(numeral_term.IsIntegerConstant());
  EXPECT_THAT(numeral_term.IntegerConstantToInt64(), IsOkAndHolds(55));
}

TEST_P(SMTTest, IntegerConstantToInt64SucceedsFromModel) {
  if (!TrySetLogic("QF_LIA")) return;
  smt_->SetOption("produce-models", true);
  const Term x = smt_->DeclareFunction("x", smt_->GetTheorySort(smt::op::kInt));
  smt_->AssertFormula(
      smt_->ApplyFunction(smt::op::kEqual, x, smt_->NumeralTerm(55)));
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);
  const Term x_value = smt_->GetValue(x);
  EXPECT_TRUE(x_value.IsIntegerConstant());
  EXPECT_THAT(x_value.IntegerConstantToInt64(), IsOkAndHolds(55));
}

TEST_P(SMTTest, IntegerConstantToInt64SucceedsWithNegativeValueFromModel) {
  if (!TrySetLogic("QF_LIA")) return;
  smt_->SetOption("produce-models", true);
  const Term x = smt_->DeclareFunction("x", smt_->GetTheorySort(smt::op::kInt));
  const Term neg_55 =
      smt_->ApplyFunction(smt::op::kUminus, smt_->NumeralTerm(55));
  smt_->AssertFormula(smt_->ApplyFunction(smt::op::kEqual, x, neg_55));
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);
  const Term x_value = smt_->GetValue(x);
  EXPECT_TRUE(x_value.IsIntegerConstant());
  EXPECT_THAT(x_value.IntegerConstantToInt64(), IsOkAndHolds(-55));
}

TEST_P(SMTTest, IntegerConstantToInt64FailsPreconditionForNonIntegerTerms) {
  if (!TrySetLogic("QF_BV")) return;
  const Term numeral_term = smt_->BitvectorConstantTerm(55, 10);
  EXPECT_FALSE(numeral_term.IsIntegerConstant());
  EXPECT_THAT(numeral_term.IntegerConstantToInt64(),
              StatusIs(absl::StatusCode::kFailedPrecondition,
                       "Term is not an integer constant."));
}

TEST_P(SMTTest, WidthOneBVConstantsAreBitvectorConstants) {
  if (!TrySetLogic("QF_BV")) return;
  EXPECT_TRUE(smt_->BitvectorConstantTerm(0, 1).IsBVConstant());
  EXPECT_TRUE(smt_->BitvectorConstantTerm(1, 1).IsBVConstant());
}

TEST_P(SMTTest, IntegerConstantToInt64OutOfRangeForTooLargeIntegers) {
  if (!TrySetLogic("QF_LIA")) return;
  const Term numeral_term = smt_->NumeralTerm("1234512345123451234512345");
  CHECK(numeral_term.IsIntegerConstant());
  EXPECT_EQ(numeral_term.ToString(), "1234512345123451234512345");
  EXPECT_THAT(
      numeral_term.IntegerConstantToInt64(),
      StatusIs(absl::StatusCode::kOutOfRange, "Value doesn't fit in an int64."));
}

TEST_P(SMTTest, TestBvConstantToUnsigned) {
  if (!TrySetLogic("QF_BV")) return;
  smt_->SetOption("produce-models", true);
  Term constant = smt_->BitvectorConstantTerm(1, 1);
  EXPECT_EQ(constant.BvConstantToUnsigned(), 1);
  constant = smt_->BitvectorConstantTerm(1, 1);
  EXPECT_EQ(constant.BvConstantToUnsigned(), 1);
  constant = smt_->BitvectorConstantTerm(1, 32);
  EXPECT_EQ(constant.BvConstantToUnsigned(), 1);
  constant = smt_->BitvectorConstantTerm(1234, 32);
  EXPECT_EQ(constant.BvConstantToUnsigned(), 1234);
  constant = smt_->BitvectorConstantTerm(0xFFFFFFFF, 32);
  EXPECT_EQ(constant.BvConstantToUnsigned(), 0xFFFFFFFF);
  constant = smt_->BitvectorConstantTerm(0, 64);
  EXPECT_EQ(constant.BvConstantToUnsigned(), 0);
  constant = smt_->BitvectorConstantTerm(1, 64);
  EXPECT_EQ(constant.BvConstantToUnsigned(), 1);
  constant = smt_->BitvectorConstantTerm(12345678, 64);
  EXPECT_EQ(constant.BvConstantToUnsigned(), 12345678);
  constant = smt_->BitvectorConstantTerm(0xFFFFFFFFFFFFFFFF, 64);
  EXPECT_EQ(constant.BvConstantToUnsigned(), 0xFFFFFFFFFFFFFFFF);
}

TEST_P(SMTTest, TestBvConstantToDecimalString) {
  if (!TrySetLogic("QF_BV")) return;
  smt_->SetOption("produce-models", true);
  Term constant = smt_->BitvectorConstantTerm(1, 1);
  EXPECT_EQ(constant.BvConstantToDecimalString(), "1");
  constant = smt_->BitvectorConstantTerm(1, 1);
  EXPECT_EQ(constant.BvConstantToDecimalString(), "1");
  constant = smt_->BitvectorConstantTerm(1, 32);
  EXPECT_EQ(constant.BvConstantToDecimalString(), "1");
  constant = smt_->BitvectorConstantTerm(1234, 32);
  EXPECT_EQ(constant.BvConstantToDecimalString(), "1234");
  constant = smt_->BitvectorConstantTerm(0xFFFFFFFF, 32);
  EXPECT_EQ(constant.BvConstantToDecimalString(), "4294967295");
  constant = smt_->BitvectorConstantTerm(0, 64);
  EXPECT_EQ(constant.BvConstantToDecimalString(), "0");
  constant = smt_->BitvectorConstantTerm(1, 64);
  EXPECT_EQ(constant.BvConstantToDecimalString(), "1");
  constant = smt_->BitvectorConstantTerm(12345678, 64);
  EXPECT_EQ(constant.BvConstantToDecimalString(), "12345678");
  constant = smt_->BitvectorConstantTerm(0xFFFFFFFFFFFFFFFF, 64);
  EXPECT_EQ(constant.BvConstantToDecimalString(), "18446744073709551615");
  // TODO: Z3 does not support >64 bit hex constant terms at the moment.
  // constant = smt_->HexConstantTerm("FFFFFFFFFFFFFFFFFFFFF");
  // EXPECT_EQ(constant.BvConstantToDecimalString(), "19342813113834066795298815");
}

TEST_P(SMTTest, TestDisableFormulasByImplicationInIncrementalModeForBV) {
  if (!TrySetLogic("QF_BV")) return;

  Sort bitvector_sort = smt_->GetTheorySort(smt::op::kBitvec, 32);
  Term xexpr = smt_->DeclareFunction("x", bitvector_sort);

  // Formula: x > 0, should be satisfiable.
  smt_->AssertFormula(smt_->ApplyFunction(smt::op::kBvugt, xexpr,
                                          smt_->BitvectorConstantTerm(0, 32)));
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);

  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  Term bexpr = smt_->DeclareFunction("b", bool_sort);

  // Formula: x > 0 && b -> (x < 0), should be satisfiable.
  smt_->AssertFormula(smt_->ApplyFunction(
      smt::op::kImplies, bexpr,
      smt_->ApplyFunction(smt::op::kBvult, xexpr,
                          smt_->BitvectorConstantTerm(0, 32))));
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);
  smt_->Push();

  // Formula: x > 0 && b -> (x < 0) && b, should be unsatisfiable.
  EXPECT_FALSE(CheckValid(bexpr));
  smt_->Pop();

  // Formula: x > 0 && b -> (x < 0), should be satisfiable.
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);
  smt_->Push();

  // Formula: x > 0 && b -> (x < 0) && !b, should be satisfiable.
  EXPECT_TRUE(CheckValid(smt_->ApplyFunction(smt::op::kNot, bexpr)));
  smt_->Pop();
}

TEST_P(SMTTest, IncrementalBitvectorsSupportMultipleContexts) {
  if (!TrySetLogic("QF_BV")) return;

  Sort bitvector_sort = smt_->GetTheorySort(smt::op::kBitvec, 32);
  Term xexpr = smt_->DeclareFunction("x", bitvector_sort);

  // Formula: x > 0, should be satisfiable.
  smt_->AssertFormula(smt_->ApplyFunction(smt::op::kBvugt, xexpr,
                                          smt_->BitvectorConstantTerm(0, 32)));
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);

  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  Term bexpr = smt_->DeclareFunction("b", bool_sort);

  smt_->Push();

  // Formula: {x > 0, b -> (x < 0)} should be satisfiable.
  smt_->AssertFormula(smt_->ApplyFunction(
      smt::op::kImplies, bexpr,
      smt_->ApplyFunction(smt::op::kBvult, xexpr,
                          smt_->BitvectorConstantTerm(0, 32))));
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);

  smt_->Push();
  // Formula: {x > 0, b -> (x < 0), not b} should be unsatisfiable.
  smt_->AssertFormula(bexpr);
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kUnsat);
  smt_->Pop();
  // Formula: {x > 0, b -> (x < 0)} should still be satisfiable.
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);
  smt_->Pop();
}

TEST_P(SMTTest, IncrementalSupportsMultiplePops) {
  if (!TrySetLogic("QF_BV")) return;

  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  Term bexpr = smt_->DeclareFunction("b", bool_sort);

  smt_->Push();
  smt_->Push();
  smt_->AssertFormula(bexpr);
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);

  smt_->AssertFormula(smt_->ApplyFunction(smt::op::kNot, bexpr));
  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kUnsat);

  smt_->Pop();
  smt_->Pop();

  EXPECT_EQ(smt_->CheckSat(), smt::SMTSolver::kSat);
}

TEST_P(SMTTest, TestShiftLeft) {
  if (!TrySetLogic("QF_BV")) return;
  const Sort bitvector16_sort = smt_->GetTheorySort(smt::op::kBitvec, 16);
  const Term x = smt_->DeclareFunction("x", bitvector16_sort);
  const Term bvconst_8 = smt_->BitvectorConstantTerm(8, 16);
  const Term left_shift8 = smt_->ApplyFunction(smt::op::kBvshl, x, bvconst_8);

  const Function extract_7_0 = smt_->GetTheoryFunction(smt::op::kExtract, 7, 0);
  const Term x_7_0 = smt_->ApplyFunction(extract_7_0, x);
  const Term expected = smt_->ApplyFunction(smt::op::kConcat, x_7_0,
                                            smt_->BitvectorConstantTerm(0, 8));
  EXPECT_TRUE(
      CheckValid(smt_->ApplyFunction(smt::op::kEqual, left_shift8, expected)));
}

TEST_P(SMTTest, TestShiftLeftWidthNotPowerOfTwo) {
  if (!TrySetLogic("QF_BV")) return;
  const Sort bitvector5_sort = smt_->GetTheorySort(smt::op::kBitvec, 5);
  const Term x = smt_->DeclareFunction("x", bitvector5_sort);
  const Term bvconst_2 = smt_->BitvectorConstantTerm(2, 5);
  const Term left_shift2 = smt_->ApplyFunction(smt::op::kBvshl, x, bvconst_2);

  const Function extract_2_0 = smt_->GetTheoryFunction(smt::op::kExtract, 2, 0);
  const Term x_2_0 = smt_->ApplyFunction(extract_2_0, x);
  const Term expected = smt_->ApplyFunction(smt::op::kConcat, x_2_0,
                                            smt_->BitvectorConstantTerm(0, 2));
  EXPECT_TRUE(
      CheckValid(smt_->ApplyFunction(smt::op::kEqual, left_shift2, expected)));
}

TEST_P(SMTTest, TestLogicalShiftRight) {
  if (!TrySetLogic("QF_BV")) return;
  const Sort bitvector16_sort = smt_->GetTheorySort(smt::op::kBitvec, 16);
  const Term x = smt_->DeclareFunction("x", bitvector16_sort);
  const Term bvconst_8 = smt_->BitvectorConstantTerm(8, 16);
  const Term right_shift8 = smt_->ApplyFunction(smt::op::kBvlshr, x, bvconst_8);

  const Function extract_15_8 =
      smt_->GetTheoryFunction(smt::op::kExtract, 15, 8);
  const Term x_15_8 = smt_->ApplyFunction(extract_15_8, x);
  const Term expected = smt_->ApplyFunction(
      smt::op::kConcat, smt_->BitvectorConstantTerm(0, 8), x_15_8);

  EXPECT_TRUE(
      CheckValid(smt_->ApplyFunction(smt::op::kEqual, right_shift8, expected)));
}

TEST_P(SMTTest, TestShiftRightWidthNotPowerOfTwo) {
  if (!TrySetLogic("QF_BV")) return;
  const Sort bitvector5_sort = smt_->GetTheorySort(smt::op::kBitvec, 5);
  const Term x = smt_->DeclareFunction("x", bitvector5_sort);
  const Term bvconst_2 = smt_->BitvectorConstantTerm(2, 5);
  const Term right_shift2 = smt_->ApplyFunction(smt::op::kBvlshr, x, bvconst_2);

  const Function extract_4_2 = smt_->GetTheoryFunction(smt::op::kExtract, 4, 2);
  const Term x_4_2 = smt_->ApplyFunction(extract_4_2, x);
  const Term expected = smt_->ApplyFunction(
      smt::op::kConcat, smt_->BitvectorConstantTerm(0, 2), x_4_2);
  EXPECT_TRUE(
      CheckValid(smt_->ApplyFunction(smt::op::kEqual, right_shift2, expected)));
}

TEST_P(SMTTest, TestArithmeticShiftRight) {
  if (!TrySetLogic("QF_BV")) return;
  const Sort bitvector16_sort = smt_->GetTheorySort(smt::op::kBitvec, 16);
  const Term x = smt_->DeclareFunction("x", bitvector16_sort);
  const Term bvconst_1 = smt_->BitvectorConstantTerm(1, 16);
  const Term right_shift1 = smt_->ApplyFunction(smt::op::kBvashr, x, bvconst_1);

  const Function extract_15_15 =
      smt_->GetTheoryFunction(smt::op::kExtract, 15, 15);
  const Term x_15_15 = smt_->ApplyFunction(extract_15_15, x);
  const Function extract_15_1 =
      smt_->GetTheoryFunction(smt::op::kExtract, 15, 1);
  const Term x_15_1 = smt_->ApplyFunction(extract_15_1, x);
  const Term expected = smt_->ApplyFunction(smt::op::kConcat, x_15_15, x_15_1);

  EXPECT_TRUE(
      CheckValid(smt_->ApplyFunction(smt::op::kEqual, right_shift1, expected)));
}

TEST_P(SMTTest, TestArithmeticShiftRightWidthNotPowerOfTwo) {
  if (!TrySetLogic("QF_BV")) return;
  const Sort bitvector5_sort = smt_->GetTheorySort(smt::op::kBitvec, 5);
  const Term x = smt_->DeclareFunction("x", bitvector5_sort);
  const Term bvconst_2 = smt_->BitvectorConstantTerm(2, 5);
  const Term right_shift2 = smt_->ApplyFunction(smt::op::kBvashr, x, bvconst_2);

  const Function extract_4_4 = smt_->GetTheoryFunction(smt::op::kExtract, 4, 4);
  const Term x_4_4 = smt_->ApplyFunction(extract_4_4, x);
  const Function extract_4_2 = smt_->GetTheoryFunction(smt::op::kExtract, 4, 2);
  const Term x_4_2 = smt_->ApplyFunction(extract_4_2, x);
  const Term expected =
      smt_->ApplyFunction(smt::op::kConcat, x_4_4, x_4_4, x_4_2);
  EXPECT_TRUE(
      CheckValid(smt_->ApplyFunction(smt::op::kEqual, right_shift2, expected)));
}

TEST_P(SMTTest, TestBinaryConstantTerm) {
  if (!TrySetLogic("QF_BV")) return;
  const Term expected = smt_->BitvectorConstantTerm(2, 5);
  const Term binary_2 = smt_->BinaryConstantTerm("00010");

  LOG(INFO) << expected.ToString();
  LOG(INFO) << binary_2.ToString();
  EXPECT_TRUE(
      CheckValid(smt_->ApplyFunction(smt::op::kEqual, binary_2, expected)));
}

TEST_P(SMTTest, TestHexConstantTerm) {
  if (!TrySetLogic("QF_BV")) return;
  const Term expected = smt_->BitvectorConstantTerm(0xabcdef, 24);
  const Term binary_abcdef = smt_->HexConstantTerm("abcdef");
  const Term binary_aBcDeF = smt_->HexConstantTerm("aBcDeF");
  EXPECT_TRUE(CheckValid(
      smt_->ApplyFunction(smt::op::kEqual, binary_abcdef, expected)));
  EXPECT_TRUE(CheckValid(
      smt_->ApplyFunction(smt::op::kEqual, binary_aBcDeF, expected)));
}

TEST_P(SMTTest, TestForAll) {
  const Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  const Term bound_bool = smt_->BoundVariableTerm("bound_bool", bool_sort);
  const Term all_bools_are_true_or_false = smt_->Forall(
      {bound_bool},
      smt_->ApplyFunction(smt::op::kOr,
                          smt_->ApplyFunction(smt::op::kNot, bound_bool),
                          bound_bool));
  EXPECT_TRUE(CheckValid(all_bools_are_true_or_false));
}

TEST_P(SMTTest, TestExists) {
  const Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  const Term bound_bool = smt_->BoundVariableTerm("bound_bool", bool_sort);
  const Term there_is_a_true_bool = smt_->Exists({bound_bool}, bound_bool);
  EXPECT_TRUE(CheckValid(there_is_a_true_bool));
}

// TODO: Consider adding more tests
INSTANTIATE_TEST_SUITE_P(SolverImplementations, SMTTest,
                         testing::Values(SolverName::kZ3,
                                         SolverName::kPrintingDefault,
                                         SolverName::kPrintingZ3));

TEST_P(SMTDeathTest, TestGetSortDeath) {
  if (!TrySetLogic("QF_BV")) return;
  const Term t;
  EXPECT_DEATH(t.GetSort(), "Check failed: !IsNull");
}

TEST_P(SMTDeathTest, BitvectorSortRequiresWidth) {
  if (!TrySetLogic("QF_BV")) return;
  EXPECT_DEATH(smt_->GetTheorySort(smt::op::kBitvec), "");
}

TEST_P(SMTDeathTest, IndexedBoolSortFails) {
  if (!TrySetLogic("QF_BV")) return;
  EXPECT_DEATH(smt_->GetTheorySort(smt::op::kBool, 1), "");
}

TEST_P(SMTDeathTest, ApplyBitvectorSortFails) {
  if (!TrySetLogic("QF_BV")) return;
  const Sort bitvector_16_sort = smt_->GetTheorySort(smt::op::kBitvec, 16);
  const std::vector<Sort> args;
  EXPECT_DEATH(smt_->ApplySort(bitvector_16_sort, args), "");
}

TEST_P(SMTDeathTest, ArraySortConstructorRequiresTwoArgs) {
  if (!TrySetLogic("QF_ABV")) return;
  const Sort array_sort_constructor = smt_->GetTheorySort(smt::op::kArray);
  const Sort bitvector_16_sort = smt_->GetTheorySort(smt::op::kBitvec, 16);
  EXPECT_DEATH(smt_->ApplySort(array_sort_constructor, bitvector_16_sort), "");
}

TEST_P(SMTDeathTest, PlusFunctionFailsWithOneIndex) {
  if (!TrySetLogic("QF_ABV")) return;
  EXPECT_DEATH(smt_->GetTheoryFunction(smt::op::kPlus, 0), "");
}

TEST_P(SMTDeathTest, PlusFunctionFailsWithTwoIndices) {
  if (!TrySetLogic("QF_ABV")) return;
  EXPECT_DEATH(smt_->GetTheoryFunction(smt::op::kPlus, -1, 0), "");
}

TEST_P(SMTDeathTest, RepeatFunctionFailsWithNoIndices) {
  if (!TrySetLogic("QF_ABV")) return;
  EXPECT_DEATH(smt_->GetTheoryFunction(smt::op::kRepeat), "");
}

TEST_P(SMTDeathTest, RepeatFunctionFailsWithTwoIndices) {
  if (!TrySetLogic("QF_ABV")) return;
  EXPECT_DEATH(smt_->GetTheoryFunction(smt::op::kRepeat, 0, 0), "");
}

TEST_P(SMTDeathTest, RepeatFunctionFailsWithZeroRepeats) {
  if (!TrySetLogic("QF_ABV")) return;
  EXPECT_DEATH(smt_->ApplyFunction(smt_->GetTheoryFunction(smt::op::kRepeat, 0),
                                   smt_->BitvectorConstantTerm(0, 8)),
               "");
}

TEST_P(SMTDeathTest, ExtractFunctionFailsWithNoIndices) {
  if (!TrySetLogic("QF_ABV")) return;
  EXPECT_DEATH(smt_->GetTheoryFunction(smt::op::kExtract), "");
}

TEST_P(SMTDeathTest, ExtractFunctionFailsWithOneIndex) {
  if (!TrySetLogic("QF_ABV")) return;
  EXPECT_DEATH(smt_->GetTheoryFunction(smt::op::kExtract, 0), "");
}

TEST_P(SMTDeathTest, GetTheoryConstantTermFailsWithNonConstant) {
  if (!TrySetLogic("QF_BV")) return;
  EXPECT_DEATH(smt_->GetTheoryConstantTerm(smt::op::kAnd), "");
}

TEST_P(SMTDeathTest, PopWithoutPushFails) {
  if (!TrySetLogic("QF_BV")) return;
  EXPECT_DEATH(smt_->Pop(), "");
}

TEST_P(SMTDeathTest, DiesOnNonHexString) {
  if (!TrySetLogic("QF_BV")) return;
  EXPECT_DEATH(smt_->HexConstantTerm("G"), "");
  // The following are not supported yet, but could be in the future. Update
  // these if the behavior gets updated.
  EXPECT_DEATH(smt_->HexConstantTerm("#xaa"), "");
}

TEST_P(SMTDeathTest, DiesOnNonBinaryString) {
  if (!TrySetLogic("QF_BV")) return;
  EXPECT_DEATH(smt_->BinaryConstantTerm("2"), "");
  // The following are not supported yet, but could be in the future. Update
  // these if the behavior gets updated.
  EXPECT_DEATH(smt_->BinaryConstantTerm("0b00"), "");
  EXPECT_DEATH(smt_->BinaryConstantTerm("#b01"), "");
}

TEST_P(SMTDeathTest, NumeralDiesOnRealString) {
  if (!TrySetLogic("QF_UFLIA")) return;
  EXPECT_DEATH(smt_->NumeralTerm("123.456"), "");
}

INSTANTIATE_TEST_SUITE_P(SolverImplementations, SMTDeathTest,
                         testing::Values(SolverName::kZ3,
                                         SolverName::kPrintingDefault,
                                         SolverName::kPrintingZ3));
