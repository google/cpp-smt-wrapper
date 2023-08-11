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

// Unit tests for Z3SMTSolver class.
//
// The general tests for the SMTSolver are covered by the parameterized tests in
// smt_test.cc.

#include "src/smt/z3_smt_solver.h"

#include <memory>
#include <vector>
#include <gtest/gtest.h>

#include "src/smt/smt.h"
#include "src/smt/smt_ops.h"
#include "src/smt/smt_term.h"
#include "src/smt/z3_smt_solver_factory.h"

using smt::Sort;
using smt::Function;
using smt::Term;
using smt::Z3Solver;

class Z3SMTTest : public ::testing::Test {
 protected:
  void SetUp() override {
    smt::Z3SMTSolverFactory z3_factory;
    smt_ = z3_factory.Create();
  }

  void TearDown() override {
    smt_->Reset();
    smt_.reset(nullptr);
  }

  // Casts smt_ to z3 in order to get access to Z3Function
  Z3Solver* z3_solver() { return dynamic_cast<smt::Z3Solver*>(smt_.get()); }

  std::unique_ptr<smt::SMTSolver> smt_;
};

TEST_F(Z3SMTTest, TestGetZ3DeclKindFromSimpleFunction) {
  CHECK_OK(smt_->SetLogic("QF_UF"));
  Function simp_f = smt_->GetTheoryFunction(smt::op::kNot);

  Z3Solver* z3 = z3_solver();
  const smt::Z3Function& simp_f_z3 = z3->GetZ3Function(simp_f);
  EXPECT_EQ(simp_f_z3.z3_decl_kind(), Z3_decl_kind::Z3_OP_NOT);
}

TEST_F(Z3SMTTest, TestGetZ3FuncFromSimpleFunction) {
  CHECK_OK(smt_->SetLogic("QF_LRA"));
  // Uses smt_ rather than z3 to build functions. Otherwise, the
  // z3_decl_kind_ will be initialized with an invalid kind
  // (not Z3_OP_UNINTERPRETED).
  Sort real_sort = smt_->GetTheorySort(smt::op::kReal);
  std::vector<Sort> rank{real_sort, real_sort, real_sort};
  Function nonsimp_f = smt_->DeclareFunction("g", rank);

  Z3Solver* z3 = z3_solver();
  const smt::Z3Function& nonsimp_f_z3 = z3->GetZ3Function(nonsimp_f);
  EXPECT_EQ(nonsimp_f_z3.z3_func().name().str(), "g");
  EXPECT_EQ(nonsimp_f_z3.z3_func().arity(), 2);
  EXPECT_TRUE(nonsimp_f_z3.z3_func().range().is_real());
  EXPECT_TRUE(nonsimp_f_z3.z3_func().domain(0).is_real());
  EXPECT_TRUE(nonsimp_f_z3.z3_func().domain(1).is_real());
}

TEST_F(Z3SMTTest, TestUnaryFunction) {
  CHECK_OK(smt_->SetLogic("QF_LIA"));
  Sort int_sort = smt_->GetTheorySort(smt::op::kInt);
  Term aexpr = smt_->DeclareFunction("a", int_sort);
  Term expr = smt_->ApplyFunction(smt::op::kUminus, aexpr);

  EXPECT_EQ(expr.ToString(), "(- a)");
}

TEST_F(Z3SMTTest, TestBinaryFunction) {
  CHECK_OK(smt_->SetLogic("QF_UF"));
  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  Term aexpr = smt_->DeclareFunction("a", bool_sort);
  Term bexpr = smt_->DeclareFunction("b", bool_sort);
  Term expr = smt_->ApplyFunction(smt::op::kImplies, aexpr, bexpr);

  EXPECT_EQ(expr.ToString(), "(=> a b)");
}

TEST_F(Z3SMTTest, TestExternalFunctionExpressionToString) {
  CHECK_OK(smt_->SetLogic("QF_UF"));
  Sort string_sort = smt_->GetTheorySort(smt::op::kString);
  Term aexpr = smt_->DeclareFunction("a", string_sort);
  Term bexpr = smt_->DeclareFunction("b", string_sort);
  Term str_le_expr = smt_->ApplyFunction(smt::op::kStrLe, aexpr, bexpr);
  Term str_lt_expr = smt_->ApplyFunction(smt::op::kStrLt, aexpr, bexpr);

  EXPECT_EQ(str_le_expr.ToString(), "(str.<= a b)");
  EXPECT_EQ(str_lt_expr.ToString(), "(str.< a b)");
}

TEST_F(Z3SMTTest, TestExternalFunctionToString) {
  CHECK_OK(smt_->SetLogic("QF_UF"));
  Function le_function = smt_->GetTheoryFunction(smt::op::kStrLe);
  Function lt_function = smt_->GetTheoryFunction(smt::op::kStrLt);
  EXPECT_EQ(le_function.ToString(), "ExternalInterpretedFunction::kStrLe");
  EXPECT_EQ(lt_function.ToString(), "ExternalInterpretedFunction::kStrLt");
}

TEST_F(Z3SMTTest, TestExternalFunctionReturnsCorrectFunction) {
  CHECK_OK(smt_->SetLogic("QF_UF"));
  Function le_function = smt_->GetTheoryFunction(smt::op::kStrLe);
  Function lt_function = smt_->GetTheoryFunction(smt::op::kStrLt);
  Z3Solver* z3 = z3_solver();
  const smt::Z3Function& z3_le_function = z3->GetZ3Function(le_function);
  const smt::Z3Function& z3_lt_function = z3->GetZ3Function(lt_function);
  EXPECT_EQ(z3_le_function.external_interpreted_function(),
            smt::Z3Function::ExternalInterpretedFunction::kStrLe);
  EXPECT_EQ(z3_lt_function.external_interpreted_function(),
            smt::Z3Function::ExternalInterpretedFunction::kStrLt);
}

TEST_F(Z3SMTTest, TestExternalFunctionEquality) {
  CHECK_OK(smt_->SetLogic("QF_UF"));
  Function le_function1 = smt_->GetTheoryFunction(smt::op::kStrLe);
  Function le_function2 = smt_->GetTheoryFunction(smt::op::kStrLe);
  Function lt_function = smt_->GetTheoryFunction(smt::op::kStrLt);
  EXPECT_EQ(le_function1, le_function1);
  EXPECT_EQ(le_function1, le_function2);
  EXPECT_NE(le_function1, lt_function);
  EXPECT_NE(lt_function, le_function1);
  EXPECT_EQ(lt_function, lt_function);
}

TEST_F(Z3SMTTest, TestTenaryFunction) {
  CHECK_OK(smt_->SetLogic("QF_LIA"));
  Sort bool_sort = smt_->GetTheorySort(smt::op::kBool);
  Term cexpr = smt_->DeclareFunction("c", bool_sort);
  Sort int_sort = smt_->GetTheorySort(smt::op::kInt);
  Term aexpr = smt_->DeclareFunction("a", int_sort);
  Term bexpr = smt_->DeclareFunction("b", int_sort);
  Term expr = smt_->ApplyFunction(smt::op::kIte, cexpr, aexpr, bexpr);

  EXPECT_EQ(expr.ToString(), "(ite c a b)");
}

TEST_F(Z3SMTTest, TestTenaryFunctionWithIndexParams) {
  CHECK_OK(smt_->SetLogic("QF_BV"));
  Sort bitvector_sort = smt_->GetTheorySort(smt::op::kBitvec, 4);
  Term x = smt_->DeclareFunction("x", bitvector_sort);
  Term expr =
      smt_->ApplyFunction(smt_->GetTheoryFunction(smt::op::kZeroExtend, 8), x);

  EXPECT_EQ(expr.ToString(), "((_ zero_extend 8) x)");
}

TEST_F(Z3SMTTest, TestSetTimeout) {
  // Simply test to make sure this function passes.
  // In general timeouts are more "advisory" than "reliable".
  smt_->SetEngineTimeout(1000);
}

using Z3SMTDeathTest = Z3SMTTest;

TEST_F(Z3SMTDeathTest,
       TestSimpleFuncCheckFailsWhenCallingOtherRepresentations) {
  CHECK_OK(smt_->SetLogic("QF_UF"));
  Function simp_f = smt_->GetTheoryFunction(smt::op::kNot);

  Z3Solver* z3 = z3_solver();
  const smt::Z3Function& simp_f_z3 = z3->GetZ3Function(simp_f);
  EXPECT_DEATH(simp_f_z3.z3_func(),
               "Cannot return Z3 function decl for simple functions");
  EXPECT_DEATH(simp_f_z3.external_interpreted_function(),
               "Cannot get an ExternalInterpretedFunction for a simple or "
               "uninterpreted function.");
}

TEST_F(Z3SMTDeathTest,
       TestNonSimpleFuncCheckFailsWhenCallingOtherRepresentations) {
  CHECK_OK(smt_->SetLogic("QF_LRA"));
  // Uses smt_ rather than z3 to build functions. Otherwise, the
  // z3_decl_kind_ will be initialized with an invalid kind
  // (not Z3_OP_UNINTERPRETED).
  Sort real_sort = smt_->GetTheorySort(smt::op::kReal);
  std::vector<Sort> rank{real_sort, real_sort, real_sort};
  Function nonsimp_f = smt_->DeclareFunction("g", rank);

  Z3Solver* z3 = z3_solver();
  const smt::Z3Function& nonsimp_f_z3 = z3->GetZ3Function(nonsimp_f);

  EXPECT_DEATH(nonsimp_f_z3.z3_decl_kind(),
               "Cannot return Z3_decl_kind for non-simple or externally "
               "interpreted functions");
  EXPECT_DEATH(nonsimp_f_z3.external_interpreted_function(),
               "Cannot get an ExternalInterpretedFunction for a simple or "
               "uninterpreted function.");
}

TEST_F(Z3SMTDeathTest,
       ExternalInterpretedFunctionFailsWhenCallingOtherRepresentations) {
  CHECK_OK(smt_->SetLogic("QF_LRA"));
  Function external_interpreted_f = smt_->GetTheoryFunction(smt::op::kStrLe);
  Z3Solver* z3 = z3_solver();
  const smt::Z3Function& external_interpreted_f_z3 =
      z3->GetZ3Function(external_interpreted_f);
  EXPECT_DEATH(external_interpreted_f_z3.z3_decl_kind(),
               "Cannot return Z3_decl_kind for non-simple or externally "
               "interpreted functions");
  EXPECT_DEATH(external_interpreted_f_z3.z3_func(),
               "Cannot return Z3 function decl for simple functions");
}

TEST_F(Z3SMTDeathTest, TestUnaryFuncCheckFailedWithInvalidNumArgs) {
  CHECK_OK(smt_->SetLogic("QF_LIA"));
  Sort int_sort = smt_->GetTheorySort(smt::op::kInt);
  Term aexpr = smt_->DeclareFunction("a", int_sort);
  Term bexpr = smt_->DeclareFunction("b", int_sort);

  EXPECT_DEATH(smt_->ApplyFunction(smt::op::kNot, aexpr, bexpr),
               "Check failed: size == 1");
  EXPECT_DEATH(smt_->ApplyFunction(smt::op::kBvnot, aexpr, bexpr),
               "Check failed: size == 1");
  EXPECT_DEATH(smt_->ApplyFunction(smt::op::kBvneg, aexpr, bexpr),
               "Check failed: size == 1");
  EXPECT_DEATH(smt_->ApplyFunction(smt::op::kUminus, aexpr, bexpr),
               "Check failed: size == 1");
  EXPECT_DEATH(smt_->ApplyFunction(smt::op::kToReal, aexpr, bexpr),
               "Check failed: size == 1");
  EXPECT_DEATH(smt_->ApplyFunction(smt::op::kToInt, aexpr, bexpr),
               "Check failed: size == 1");
  EXPECT_DEATH(smt_->ApplyFunction(smt::op::kIsInt, aexpr, bexpr),
               "Check failed: size == 1");
}

TEST_F(Z3SMTDeathTest, TestBinaryFuncCheckFailedWithInvalidNumArgs) {
  CHECK_OK(smt_->SetLogic("QF_LIA"));
  Sort int_sort = smt_->GetTheorySort(smt::op::kInt);
  Term aexpr = smt_->DeclareFunction("a", int_sort);

  EXPECT_DEATH(smt_->ApplyFunction(smt::op::kImplies, aexpr),
               "Check failed: size == 2");
  EXPECT_DEATH(smt_->ApplyFunction(smt::op::kSelect, aexpr),
               "Check failed: size == 2");
  EXPECT_DEATH(smt_->ApplyFunction(smt::op::kBvshl, aexpr),
               "Check failed: size == 2");
  EXPECT_DEATH(smt_->ApplyFunction(smt::op::kLt, aexpr),
               "Check failed: size == 2");
  EXPECT_DEATH(smt_->ApplyFunction(smt::op::kBvcomp, aexpr),
               "Check failed: size == 2");
  EXPECT_DEATH(smt_->ApplyFunction(smt::op::kXor, aexpr),
               "Check failed: size == 2");
}

TEST_F(Z3SMTDeathTest, TestTenaryFuncCheckFailedWithInvalidNumArgs) {
  CHECK_OK(smt_->SetLogic("QF_LIA"));
  Sort int_sort = smt_->GetTheorySort(smt::op::kInt);
  Term aexpr = smt_->DeclareFunction("a", int_sort);
  Term bexpr = smt_->DeclareFunction("b", int_sort);

  EXPECT_DEATH(smt_->ApplyFunction(smt::op::kIte, aexpr, bexpr),
               "Check failed: size == 3");
  EXPECT_DEATH(smt_->ApplyFunction(smt::op::kStore, aexpr, bexpr),
               "Check failed: size == 3");
}

TEST_F(Z3SMTDeathTest, TestTheoryFunctionCheckFailedWithInvalidIndexParams) {
  CHECK_OK(smt_->SetLogic("QF_BV"));
  Z3Solver* z3 = z3_solver();

  EXPECT_DEATH(z3->GetTheoryFunction(smt::op::kRepeat),
               "Function index parameter expected");
  EXPECT_DEATH(z3->GetTheoryFunction(smt::op::kZeroExtend),
               "Function index parameter expected");
  EXPECT_DEATH(z3->GetTheoryFunction(smt::op::kSignExtend),
               "Function index parameter expected");
  EXPECT_DEATH(z3->GetTheoryFunction(smt::op::kRotateLeft),
               "Function index parameter expected");
  EXPECT_DEATH(z3->GetTheoryFunction(smt::op::kRotateRight),
               "Function index parameter expected");
  EXPECT_DEATH(z3->GetTheoryFunction(smt::op::kExtract, 8),
               "Unknown indexed theory function");
}

// TODO: more tests
