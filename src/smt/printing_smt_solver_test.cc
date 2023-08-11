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

#include <memory>
#include <sstream>
#include <string>
#include <gtest/gtest.h>

#include "src/smt/z3_smt_solver_factory.h"
#include "src/smt/printing_smt_solver_factory.h"
#include "src/smt/smt_ops.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"

namespace smt {
namespace {

class PrintingSolverTestkAll : public ::testing::Test {
 protected:
  PrintingSolverTestkAll() : output_stream_(), printing_solver_() {
    PrintingSMTSolverFactory factory;
    printing_solver_ = factory.Create(
        PrintingMode::kAll,
        [this](std::string str) { this->output_stream_ << str; },
        Z3SMTSolverFactory().Create());
  }

  bool CheckValid(const Term& formula) {
    printing_solver_->AssertFormula(
        printing_solver_->ApplyFunction(smt::op::kNot, formula));
    smt::SMTSolver::CheckSatResponse response = printing_solver_->CheckSat();
    return response == smt::SMTSolver::kUnsat;
  }

 protected:
  std::stringstream output_stream_;
  std::unique_ptr<SMTSolver> printing_solver_;
};

TEST_F(PrintingSolverTestkAll, BasicSetLogicTest) {
  ASSERT_TRUE(printing_solver_->SetLogic("QF_UF").ok());
  EXPECT_EQ(output_stream_.str(), "(set-logic \"QF_UF\")\n");
}

// TODO: At the moment, the Z3 implementation of this just outputs numbers for
// function identifiers when you're building up an expression, which is a little
// confusing (e.g. (1562 "hello" 5)).
TEST_F(PrintingSolverTestkAll, TestOperatorStrAtOutOfBounds) {
  ASSERT_TRUE(printing_solver_->SetLogic("QF_S").ok());
  printing_solver_->SetOption("produce-models", true);

  const Term hello = printing_solver_->StringConstantTerm("hello");
  const Term letter_o = printing_solver_->StringConstantTerm("o");
  const Term empty_string = printing_solver_->StringConstantTerm("");
  const Term sixth_letter_of_hello = printing_solver_->ApplyFunction(
      smt::op::kStrAt, hello, printing_solver_->NumeralTerm(5));
  const Term sixth_letter_of_hello_is_o = printing_solver_->ApplyFunction(
      smt::op::kEqual, sixth_letter_of_hello, letter_o);
  const Term sixth_letter_of_hello_is_empty = printing_solver_->ApplyFunction(
      smt::op::kEqual, sixth_letter_of_hello, empty_string);

  printing_solver_->Push();
  EXPECT_FALSE(CheckValid(sixth_letter_of_hello_is_o));
  printing_solver_->Pop();

  printing_solver_->Push();
  EXPECT_TRUE(CheckValid(sixth_letter_of_hello_is_empty));
  printing_solver_->Pop();

  // Annoyance: Some text editors seem to feel that a trailing space in a fixed
  // string should be "cleaned up", leading to this test failing when those
  // editors autmoatically cleans up the trailing space in "; string term = \n"
  EXPECT_EQ(output_stream_.str(),
            absl::StrCat(R"((set-logic "QF_S")
(set-option :produce-models 1)
; string term = hello
; string term = o
)", "; string term = \n",
R"(; numeral term = 5
; get-function 62
; (1562 "hello" 5 )
; get-function 7
; (258 (str.at "hello" 5) "o" )
; get-function 7
; (258 (str.at "hello" 5) "" )
(push)
; get-function 2
; (265 (= (str.at "hello" 5) "o") )
(assert (not (= (str.at "hello" 5) "o")))
(check-sat)
(pop)
(push)
; get-function 2
; (265 (= (str.at "hello" 5) "") )
(assert (not (= (str.at "hello" 5) "")))
(check-sat)
(pop)
)"));
}

TEST(PrintingSolverTestkSMT, TestOperatorStrAtOutOfBounds) {
  PrintingSMTSolverFactory factory;
  std::string logresult;
  auto printing_solver = factory.Create(
      PrintingMode::kSMT,
      [&logresult](absl::string_view str) { absl::StrAppend(&logresult, str); },
      Z3SMTSolverFactory().Create());
  CHECK_OK(printing_solver->SetLogic("QF_S"));
  printing_solver->SetOption("produce-models", true);

  const Term hello = printing_solver->StringConstantTerm("hello");
  const Term letter_o = printing_solver->StringConstantTerm("o");
  const Term empty_string = printing_solver->StringConstantTerm("");
  const Term sixth_letter_of_hello = printing_solver->ApplyFunction(
      smt::op::kStrAt, hello, printing_solver->NumeralTerm(5));
  const Term sixth_letter_of_hello_is_o = printing_solver->ApplyFunction(
      smt::op::kEqual, sixth_letter_of_hello, letter_o);
  const Term sixth_letter_of_hello_is_empty = printing_solver->ApplyFunction(
      smt::op::kEqual, sixth_letter_of_hello, empty_string);

  printing_solver->Push();
  printing_solver->AssertFormula(printing_solver->ApplyFunction(
      smt::op::kNot, sixth_letter_of_hello_is_o));
  smt::SMTSolver::CheckSatResponse responseOne = printing_solver->CheckSat();
  EXPECT_FALSE(responseOne == smt::SMTSolver::kUnsat);
  printing_solver->Pop();

  printing_solver->Push();

  printing_solver->AssertFormula(printing_solver->ApplyFunction(
      smt::op::kNot, sixth_letter_of_hello_is_empty));
  smt::SMTSolver::CheckSatResponse responseTwo = printing_solver->CheckSat();
  EXPECT_TRUE(responseTwo == smt::SMTSolver::kUnsat);
  printing_solver->Pop();

  EXPECT_EQ(logresult,
            R"((set-logic "QF_S")
(set-option :produce-models 1)
(push)
(assert (not (= (str.at "hello" 5) "o")))
(check-sat)
(pop)
(push)
(assert (not (= (str.at "hello" 5) "")))
(check-sat)
(pop)
)");
}

TEST(PrintingSolverTestkSMT, TestFunctionIndex) {
  PrintingSMTSolverFactory factory;
  std::string logresult;
  auto printing_solver = factory.Create(
      PrintingMode::kAll,
      [&logresult](absl::string_view str) { absl::StrAppend(&logresult, str); },
      Z3SMTSolverFactory().Create());
  printing_solver->GetTheoryFunction(op::kExtract, 1, 10);

  EXPECT_EQ(logresult, "; get-function 13(1, 10)\n");
}

TEST_F(PrintingSolverTestkAll, TestSetTimeout) {
  printing_solver_->SetEngineTimeout(1000);
  EXPECT_EQ(output_stream_.str(), "; set-timeout=1000\n");
}

// TODO: It would be good to implement more unit tests.

}  // namespace
}  // namespace smt
