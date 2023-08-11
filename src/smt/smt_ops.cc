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

// Implementation of methods for SMT operators

#include "src/smt/smt_ops.h"

#include <optional>
#include <string>
#include <vector>

#include "absl/container/node_hash_map.h"
#include "absl/strings/str_cat.h"
#include "absl/types/optional.h"
#include "absl/log/check.h"

namespace smt {

namespace op {

static std::string IndexedIdentifier(const std::string& identifier,
                                     const std::vector<unsigned>& indices) {
  std::string result = "(_ " + identifier;
  for (unsigned index : indices) {
    result += " " + absl::StrCat(index);
  }
  result += ")";
  return result;
}

int GetIndexCountForSort(Sort sort) {
  // Note that any sort not in the map below is implicitly assumed to have
  // no indices.
  static const auto sort_to_num_indices_map_ =
      new absl::node_hash_map<Sort, int>({{kBitvec, 1}});
  auto indices_it = sort_to_num_indices_map_->find(sort);
  if (indices_it == sort_to_num_indices_map_->end()) {
    return 0;
  } else {
    return (*indices_it).second;
  }
}

std::string ToSMTString(Sort sort, const std::vector<unsigned>& indices) {
  static const auto sort_to_string_map_ =
      new absl::node_hash_map<Sort, std::string>({{kBool, "Bool"},
                                                  {kArray, "Array"},
                                                  {kBitvec, "BitVec"},
                                                  {kInt, "Int"},
                                                  {kReal, "Real"},
                                                  {kString, "String"},
                                                  {kRegExp, "RegExp"}});
  auto it = sort_to_string_map_->find(sort);
  CHECK(it != sort_to_string_map_->end());
  const std::string name = (*it).second;
  if (indices.empty()) {
    CHECK_EQ(GetIndexCountForSort(sort), 0);
    return name;
  } else {
    CHECK_EQ(static_cast<long unsigned int>(GetIndexCountForSort(sort)), indices.size());
    return IndexedIdentifier(name, indices);
  }
}

int GetIndexCountForFunction(Function function) {
  // Note that any function not in the map below is implicitly assumed to have
  // no indices.
  static const auto function_to_num_indices_map_ =
      new absl::node_hash_map<Function, int>({{kExtract, 2},
                                              {kRepeat, 1},
                                              {kZeroExtend, 1},
                                              {kSignExtend, 1},
                                              {kRotateLeft, 1},
                                              {kRotateRight, 1},
                                              {kDivisible, 1}});
  auto indices_it = function_to_num_indices_map_->find(function);
  if (indices_it == function_to_num_indices_map_->end()) {
    return 0;
  } else {
    return (*indices_it).second;
  }
}

std::optional<int> GetArityForFunction(Function function) {
  static const auto function_to_arity_map_ =
      new absl::node_hash_map<Function, int>(
          {{kTrue, 0},         {kFalse, 0},       {kNot, 1},
           {kImplies, 2},      {kAnd, 2},         {kOr, 2},
           {kXor, 2},          {kEqual, 2},       {kDistinct, 2},
           {kIte, 3},          {kSelect, 2},      {kStore, 3},
           {kConcat, -1},      {kExtract, 1},     {kBvnot, 1},
           {kBvand, 2},        {kBvor, 2},        {kBvneg, 1},
           {kBvadd, 2},        {kBvmul, 2},       {kBvudiv, 2},
           {kBvurem, 2},       {kBvshl, 2},       {kBvlshr, 2},
           {kBvnand, 2},       {kBvnor, 2},       {kBvxor, 2},
           {kBvcomp, 2},       {kBvsub, 2},       {kBvsdiv, 2},
           {kBvsrem, 2},       {kBvsmod, 2},      {kBvashr, 2},
           {kRepeat, 1},       {kZeroExtend, 1},  {kSignExtend, 1},
           {kRotateLeft, 1},   {kRotateRight, 1}, {kBvult, 2},
           {kBvule, 2},        {kBvugt, 2},       {kBvuge, 2},
           {kBvslt, 2},        {kBvsle, 2},       {kBvsgt, 2},
           {kBvsge, 2},        {kUminus, 1},      {kMinus, 2},
           {kPlus, 2},         {kMult, 2},        {kLe, 2},
           {kLt, 2},           {kGe, 2},          {kGt, 2},
           {kIntDiv, 2},       {kMod, 2},         {kAbs, 1},
           {kDivisible, 1},    {kToReal, 1},      {kRealDiv, 2},
           {kToInt, 1},        {kIsInt, 1},       {kStrAt, 2},
           {kStrConcat, -1},   {kStrContains, 2}, {kStrEnds, 2},
           {kStrIndexOf, 3},   {kStrLen, 1},      {kStrReplace, 3},
           {kStrStarts, 2},    {kStrSubstr, 2},   {kStrLe, 2},
           {kStrLt, 2},        {kStrToRe, 1},     {kStrInRe, 2},
           {kStrToInt, 1},     {kStrFromInt, 1},  {kReRange, 2},
           {kRePlus, 1},       {kReStar, 1},      {kReOption, 1},
           {kReIntersect, -1}, {kReConcat, -1},   {kReUnion, -1},
           {kReEmpty, 0}});
  auto it = function_to_arity_map_->find(function);
  CHECK(it != function_to_arity_map_->end());
  if ((*it).second == -1) {
    return std::nullopt;
  } else {
    return (*it).second;
  }
}

std::string ToSMTString(Function function,
                        const std::vector<unsigned>& indices) {
  static const auto function_to_string_map_ =
      new absl::node_hash_map<Function, std::string>(
          {{kTrue, "true"},
           {kFalse, "false"},
           {kNot, "not"},
           {kImplies, "=>"},
           {kAnd, "and"},
           {kOr, "or"},
           {kXor, "xor"},
           {kEqual, "="},
           {kDistinct, "distinct"},
           {kIte, "ite"},
           {kSelect, "select"},
           {kStore, "store"},
           {kConcat, "concat"},
           {kExtract, "extract"},
           {kBvnot, "bvnot"},
           {kBvand, "bvand"},
           {kBvor, "bvor"},
           {kBvneg, "bvneg"},
           {kBvadd, "bvadd"},
           {kBvmul, "bvmul"},
           {kBvudiv, "bvudiv"},
           {kBvurem, "bvurem"},
           {kBvshl, "bvshl"},
           {kBvlshr, "bvlshr"},
           {kBvnand, "bvnand"},
           {kBvnor, "bvnor"},
           {kBvxor, "bvxor"},
           {kBvcomp, "bvcomp"},
           {kBvsub, "bvsub"},
           {kBvsdiv, "bvsdiv"},
           {kBvsrem, "bvsrem"},
           {kBvsmod, "bvsmod"},
           {kBvashr, "bvashr"},
           {kRepeat, "repeat"},
           {kZeroExtend, "zero_extend"},
           {kSignExtend, "sign_extend"},
           {kRotateLeft, "rotate_left"},
           {kRotateRight, "rotate_right"},
           {kBvult, "bvult"},
           {kBvule, "bvule"},
           {kBvugt, "bvugt"},
           {kBvuge, "bvuge"},
           {kBvslt, "bvslt"},
           {kBvsle, "bvsle"},
           {kBvsgt, "bvsgt"},
           {kBvsge, "bvsge"},
           {kUminus, "-"},
           {kMinus, "-"},
           {kPlus, "+"},
           {kMult, "*"},
           {kLe, "<="},
           {kLt, "<"},
           {kGe, ">="},
           {kGt, ">"},
           {kIntDiv, "div"},
           {kMod, "mod"},
           {kAbs, "abs"},
           {kDivisible, "divisible"},
           {kToReal, "to_real"},
           {kRealDiv, "/"},
           {kToInt, "to_int"},
           {kIsInt, "is_int"},
           {kStrAt, "str.at"},
           {kStrConcat, "str.++"},
           {kStrContains, "str.contains"},
           {kStrEnds, "str.ends"},
           {kStrIndexOf, "str.indexof"},
           {kStrLen, "str.len"},
           {kStrReplace, "str.replace"},
           {kStrStarts, "str.starts"},
           {kStrSubstr, "str.substr"},
           {kStrLe, "str.<="},
           {kStrLt, "str.<"},
           {kStrToRe, "str.to.re"},
           {kStrInRe, "str.in.re"},
           {kStrToInt, "str.to_int"},
           {kStrFromInt, "str.from_int"},
           {kReRange, "re.range"},
           {kRePlus, "re.+"},
           {kReStar, "re.*"},
           {kReOption, "re.opt"},
           {kReIntersect, "re.inter"},
           {kReConcat, "re.++"},
           {kReUnion, "re.union"},
           {kReEmpty, "re.none"}});
  auto it = function_to_string_map_->find(function);
  CHECK(it != function_to_string_map_->end());
  const std::string name = (*it).second;
  if (indices.empty()) {
    CHECK_EQ(GetIndexCountForFunction(function), 0);
    return name;
  } else {
    CHECK_EQ(static_cast<long unsigned int>(GetIndexCountForFunction(function)), indices.size());
    return IndexedIdentifier(name, indices);
  }
}

}  //  namespace op

}  //  namespace smt
