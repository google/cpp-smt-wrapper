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

// Unit tests for SMT operators.

#include "src/smt/smt_ops.h"

#include <optional>
#include <vector>
#include <gtest/gtest.h>

namespace smt {
namespace op {

namespace {

class SMTOpTest : public ::testing::Test {};

TEST_F(SMTOpTest, UnindexedSortToSMTString) {
  const std::vector<unsigned> indices;
  EXPECT_EQ(ToSMTString(smt::op::kBool, indices), "Bool");
  EXPECT_EQ(ToSMTString(smt::op::kArray, indices), "Array");
  EXPECT_EQ(ToSMTString(smt::op::kInt, indices), "Int");
  EXPECT_EQ(ToSMTString(smt::op::kReal, indices), "Real");
  EXPECT_EQ(ToSMTString(smt::op::kString, indices), "String");
  EXPECT_EQ(ToSMTString(smt::op::kRegExp, indices), "RegExp");
}

TEST_F(SMTOpTest, IndexedSortToSMTString) {
  const std::vector<unsigned> indices({32});
  EXPECT_EQ(ToSMTString(smt::op::kBitvec, indices), "(_ BitVec 32)");
}

TEST_F(SMTOpTest, GetIndexCountForSort) {
  EXPECT_EQ(GetIndexCountForSort(smt::op::kBool), 0);
  EXPECT_EQ(GetIndexCountForSort(smt::op::kArray), 0);
  EXPECT_EQ(GetIndexCountForSort(smt::op::kInt), 0);
  EXPECT_EQ(GetIndexCountForSort(smt::op::kReal), 0);
  EXPECT_EQ(GetIndexCountForSort(smt::op::kString), 0);

  EXPECT_EQ(GetIndexCountForSort(smt::op::kBitvec), 1);
}

TEST_F(SMTOpTest, UnindexedFunctionToSMTString) {
  const std::vector<unsigned> indices;
  EXPECT_EQ(ToSMTString(smt::op::kTrue, indices), "true");
  EXPECT_EQ(ToSMTString(smt::op::kTrue, indices), "true");
  EXPECT_EQ(ToSMTString(smt::op::kFalse, indices), "false");
  EXPECT_EQ(ToSMTString(smt::op::kNot, indices), "not");
  EXPECT_EQ(ToSMTString(smt::op::kImplies, indices), "=>");
  EXPECT_EQ(ToSMTString(smt::op::kAnd, indices), "and");
  EXPECT_EQ(ToSMTString(smt::op::kOr, indices), "or");
  EXPECT_EQ(ToSMTString(smt::op::kXor, indices), "xor");
  EXPECT_EQ(ToSMTString(smt::op::kEqual, indices), "=");
  EXPECT_EQ(ToSMTString(smt::op::kDistinct, indices), "distinct");
  EXPECT_EQ(ToSMTString(smt::op::kIte, indices), "ite");
  EXPECT_EQ(ToSMTString(smt::op::kSelect, indices), "select");
  EXPECT_EQ(ToSMTString(smt::op::kStore, indices), "store");
  EXPECT_EQ(ToSMTString(smt::op::kConcat, indices), "concat");
  EXPECT_EQ(ToSMTString(smt::op::kBvnot, indices), "bvnot");
  EXPECT_EQ(ToSMTString(smt::op::kBvand, indices), "bvand");
  EXPECT_EQ(ToSMTString(smt::op::kBvor, indices), "bvor");
  EXPECT_EQ(ToSMTString(smt::op::kBvneg, indices), "bvneg");
  EXPECT_EQ(ToSMTString(smt::op::kBvadd, indices), "bvadd");
  EXPECT_EQ(ToSMTString(smt::op::kBvmul, indices), "bvmul");
  EXPECT_EQ(ToSMTString(smt::op::kBvudiv, indices), "bvudiv");
  EXPECT_EQ(ToSMTString(smt::op::kBvurem, indices), "bvurem");
  EXPECT_EQ(ToSMTString(smt::op::kBvshl, indices), "bvshl");
  EXPECT_EQ(ToSMTString(smt::op::kBvlshr, indices), "bvlshr");
  EXPECT_EQ(ToSMTString(smt::op::kBvnand, indices), "bvnand");
  EXPECT_EQ(ToSMTString(smt::op::kBvnor, indices), "bvnor");
  EXPECT_EQ(ToSMTString(smt::op::kBvxor, indices), "bvxor");
  EXPECT_EQ(ToSMTString(smt::op::kBvcomp, indices), "bvcomp");
  EXPECT_EQ(ToSMTString(smt::op::kBvsub, indices), "bvsub");
  EXPECT_EQ(ToSMTString(smt::op::kBvsdiv, indices), "bvsdiv");
  EXPECT_EQ(ToSMTString(smt::op::kBvsrem, indices), "bvsrem");
  EXPECT_EQ(ToSMTString(smt::op::kBvsmod, indices), "bvsmod");
  EXPECT_EQ(ToSMTString(smt::op::kBvashr, indices), "bvashr");
  EXPECT_EQ(ToSMTString(smt::op::kBvult, indices), "bvult");
  EXPECT_EQ(ToSMTString(smt::op::kBvule, indices), "bvule");
  EXPECT_EQ(ToSMTString(smt::op::kBvugt, indices), "bvugt");
  EXPECT_EQ(ToSMTString(smt::op::kBvuge, indices), "bvuge");
  EXPECT_EQ(ToSMTString(smt::op::kBvslt, indices), "bvslt");
  EXPECT_EQ(ToSMTString(smt::op::kBvsle, indices), "bvsle");
  EXPECT_EQ(ToSMTString(smt::op::kBvsgt, indices), "bvsgt");
  EXPECT_EQ(ToSMTString(smt::op::kBvsge, indices), "bvsge");
  EXPECT_EQ(ToSMTString(smt::op::kUminus, indices), "-");
  EXPECT_EQ(ToSMTString(smt::op::kMinus, indices), "-");
  EXPECT_EQ(ToSMTString(smt::op::kPlus, indices), "+");
  EXPECT_EQ(ToSMTString(smt::op::kMult, indices), "*");
  EXPECT_EQ(ToSMTString(smt::op::kLe, indices), "<=");
  EXPECT_EQ(ToSMTString(smt::op::kLt, indices), "<");
  EXPECT_EQ(ToSMTString(smt::op::kGe, indices), ">=");
  EXPECT_EQ(ToSMTString(smt::op::kGt, indices), ">");
  EXPECT_EQ(ToSMTString(smt::op::kIntDiv, indices), "div");
  EXPECT_EQ(ToSMTString(smt::op::kMod, indices), "mod");
  EXPECT_EQ(ToSMTString(smt::op::kAbs, indices), "abs");
  EXPECT_EQ(ToSMTString(smt::op::kToReal, indices), "to_real");
  EXPECT_EQ(ToSMTString(smt::op::kRealDiv, indices), "/");
  EXPECT_EQ(ToSMTString(smt::op::kToInt, indices), "to_int");
  EXPECT_EQ(ToSMTString(smt::op::kIsInt, indices), "is_int");
  EXPECT_EQ(ToSMTString(smt::op::kStrAt, indices), "str.at");
  EXPECT_EQ(ToSMTString(smt::op::kStrConcat, indices), "str.++");
  EXPECT_EQ(ToSMTString(smt::op::kStrContains, indices), "str.contains");
  EXPECT_EQ(ToSMTString(smt::op::kStrEnds, indices), "str.ends");
  EXPECT_EQ(ToSMTString(smt::op::kStrIndexOf, indices), "str.indexof");
  EXPECT_EQ(ToSMTString(smt::op::kStrLen, indices), "str.len");
  EXPECT_EQ(ToSMTString(smt::op::kStrReplace, indices), "str.replace");
  EXPECT_EQ(ToSMTString(smt::op::kStrStarts, indices), "str.starts");
  EXPECT_EQ(ToSMTString(smt::op::kStrSubstr, indices), "str.substr");
  EXPECT_EQ(ToSMTString(smt::op::kStrLe, indices), "str.<=");
  EXPECT_EQ(ToSMTString(smt::op::kStrLt, indices), "str.<");
  EXPECT_EQ(ToSMTString(smt::op::kStrToRe, indices), "str.to.re");
  EXPECT_EQ(ToSMTString(smt::op::kStrInRe, indices), "str.in.re");
  EXPECT_EQ(ToSMTString(smt::op::kStrToInt, indices), "str.to_int");
  EXPECT_EQ(ToSMTString(smt::op::kStrFromInt, indices), "str.from_int");
  EXPECT_EQ(ToSMTString(smt::op::kRePlus, indices), "re.+");
  EXPECT_EQ(ToSMTString(smt::op::kReStar, indices), "re.*");
  EXPECT_EQ(ToSMTString(smt::op::kReOption, indices), "re.opt");
  EXPECT_EQ(ToSMTString(smt::op::kReIntersect, indices), "re.inter");
  EXPECT_EQ(ToSMTString(smt::op::kReConcat, indices), "re.++");
  EXPECT_EQ(ToSMTString(smt::op::kReUnion, indices), "re.union");
  EXPECT_EQ(ToSMTString(smt::op::kReEmpty, indices), "re.none");
}

TEST_F(SMTOpTest, DoubleIndexedFunctionToSMTString) {
  const std::vector<unsigned> indices({31, 0});
  EXPECT_EQ(ToSMTString(smt::op::kExtract, indices), "(_ extract 31 0)");
}

TEST_F(SMTOpTest, SingleIndexedFunctionToSMTString) {
  const std::vector<unsigned> indices({10});
  EXPECT_EQ(ToSMTString(smt::op::kRepeat, indices), "(_ repeat 10)");
  EXPECT_EQ(ToSMTString(smt::op::kZeroExtend, indices), "(_ zero_extend 10)");
  EXPECT_EQ(ToSMTString(smt::op::kSignExtend, indices), "(_ sign_extend 10)");
  EXPECT_EQ(ToSMTString(smt::op::kRotateLeft, indices), "(_ rotate_left 10)");
  EXPECT_EQ(ToSMTString(smt::op::kRotateRight, indices), "(_ rotate_right 10)");
  EXPECT_EQ(ToSMTString(smt::op::kDivisible, indices), "(_ divisible 10)");
}

TEST_F(SMTOpTest, GetIndexCountForFunction) {
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kTrue), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kFalse), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kNot), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kImplies), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kAnd), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kOr), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kXor), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kEqual), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kDistinct), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kIte), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kSelect), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kStore), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kConcat), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvnot), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvand), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvor), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvneg), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvadd), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvmul), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvudiv), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvurem), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvshl), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvlshr), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvnand), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvnor), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvxor), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvcomp), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvsub), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvsdiv), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvsrem), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvsmod), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvashr), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvult), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvule), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvugt), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvuge), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvslt), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvsle), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvsgt), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kBvsge), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kUminus), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kMinus), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kPlus), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kMult), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kLe), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kLt), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kGe), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kGt), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kIntDiv), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kMod), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kAbs), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kToReal), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kRealDiv), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kToInt), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kIsInt), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kStrAt), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kStrConcat), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kStrContains), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kStrEnds), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kStrIndexOf), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kStrLen), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kStrReplace), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kStrStarts), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kStrSubstr), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kStrLe), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kStrLt), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kStrToRe), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kStrInRe), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kReRange), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kRePlus), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kReStar), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kReOption), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kReIntersect), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kReConcat), 0);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kReUnion), 0);

  EXPECT_EQ(GetIndexCountForFunction(smt::op::kRepeat), 1);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kZeroExtend), 1);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kSignExtend), 1);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kRotateLeft), 1);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kRotateRight), 1);
  EXPECT_EQ(GetIndexCountForFunction(smt::op::kDivisible), 1);

  EXPECT_EQ(GetIndexCountForFunction(smt::op::kExtract), 2);
}

TEST_F(SMTOpTest, GetArityForFunction) {
  EXPECT_EQ(GetArityForFunction(smt::op::kTrue), 0);
  EXPECT_EQ(GetArityForFunction(smt::op::kFalse), 0);
  EXPECT_EQ(GetArityForFunction(smt::op::kNot), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kImplies), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kAnd), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kOr), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kXor), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kEqual), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kDistinct), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kIte), 3);
  EXPECT_EQ(GetArityForFunction(smt::op::kSelect), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kStore), 3);
  EXPECT_EQ(GetArityForFunction(smt::op::kConcat), std::nullopt);
  EXPECT_EQ(GetArityForFunction(smt::op::kExtract), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvnot), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvand), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvor), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvneg), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvadd), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvmul), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvudiv), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvurem), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvshl), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvlshr), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvnand), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvnor), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvxor), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvcomp), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvsub), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvsdiv), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvsrem), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvsmod), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvashr), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kRepeat), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kZeroExtend), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kSignExtend), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kRotateLeft), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kRotateRight), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvult), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvule), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvugt), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvuge), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvslt), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvsle), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvsgt), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kBvsge), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kUminus), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kMinus), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kPlus), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kMult), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kLe), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kLt), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kGe), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kGt), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kIntDiv), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kMod), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kAbs), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kDivisible), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kToReal), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kRealDiv), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kToInt), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kIsInt), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kStrAt), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kStrConcat), std::nullopt);
  EXPECT_EQ(GetArityForFunction(smt::op::kStrContains), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kStrEnds), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kStrIndexOf), 3);
  EXPECT_EQ(GetArityForFunction(smt::op::kStrLen), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kStrReplace), 3);
  EXPECT_EQ(GetArityForFunction(smt::op::kStrStarts), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kStrSubstr), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kStrLe), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kStrLt), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kStrToRe), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kStrInRe), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kReRange), 2);
  EXPECT_EQ(GetArityForFunction(smt::op::kRePlus), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kReStar), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kReOption), 1);
  EXPECT_EQ(GetArityForFunction(smt::op::kReIntersect), std::nullopt);
  EXPECT_EQ(GetArityForFunction(smt::op::kReConcat), std::nullopt);
  EXPECT_EQ(GetArityForFunction(smt::op::kReUnion), std::nullopt);
  EXPECT_EQ(GetArityForFunction(smt::op::kReEmpty), 0);
}

class SMTOpFunctionTest : public ::testing::TestWithParam<Function> {};

TEST_P(SMTOpFunctionTest, TestGetArityForAllFunctions) {
  std::optional<int> arity = GetArityForFunction(GetParam());
  if (arity != std::nullopt) {
    EXPECT_GE(arity, 0);
  }
}

INSTANTIATE_TEST_SUITE_P(FunctionTests, SMTOpFunctionTest,
                         ::testing::Range(kFirstFunction,
                                          kLastFunctionPlusOne));

using SMTOpDeathTest = SMTOpTest;

TEST_F(SMTOpDeathTest, UnindexedSortExpectsNoIndices) {
  const std::vector<unsigned> indices({0});
  EXPECT_DEATH(ToSMTString(smt::op::kBool, indices), "Check failed");
}

TEST_F(SMTOpDeathTest, IndexedSortExpectsMatchingNumIndices) {
  const std::vector<unsigned> indices;
  EXPECT_DEATH(ToSMTString(smt::op::kBitvec, indices), "Check failed");
}

TEST_F(SMTOpDeathTest, UnindexedFunctionExpectsNoIndices) {
  const std::vector<unsigned> indices({0});
  EXPECT_DEATH(ToSMTString(smt::op::kTrue, indices), "Check failed");
}

TEST_F(SMTOpDeathTest, IndexedFunctionExpectsMatchingNumIndices) {
  const std::vector<unsigned> indices;
  EXPECT_DEATH(ToSMTString(smt::op::kExtract, indices), "Check failed");
}

}  // namespace

}  // namespace op
}  // namespace smt
