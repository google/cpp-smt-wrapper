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

// Enums for sorts and functions defined in various SMT-LIB theories.  These
// are provided to make term creation faster and easier (e.g., to avoid having
// to lookup names).
//
// See the language standard documents at www.smtlib.org for details on the
// SMT-LIB language standard and its supported theories.

#ifndef SRC_SMT_SMT_OPS_H_
#define SRC_SMT_SMT_OPS_H_

#include <optional>
#include <string>
#include <vector>

#include "absl/types/optional.h"

namespace smt {

namespace op {

enum Sort {
  // Sorts from Theory Core.
  kBool,

  // Sorts from Theory ArraysEx.
  kArray,

  // Sorts from Theory FixedSizeBitVectors.
  kBitvec,  // Indexed by one numeral

  // Sorts from the various arithmetic theories
  kInt,
  kReal,

  // Sorts for String theory
  kString,
  // Regular expressions over strings.
  // This corresponds to the RegLan sort in the String theory in SMT-LIBv2.6,
  // with the exception that the singletons are bytes.
  // Some solvers (Z3 as of writing) support regular expressions over general
  // sequences, but for compatibility we currently only support regular
  // expressions over strings.
  kRegExp,
};

enum Function {
  // Functions/Constants from Theory Core.
  kFirstFunction,
  kTrue = kFirstFunction,
  kFalse,
  kNot,
  kImplies,
  kAnd,
  kOr,
  kXor,
  kEqual,
  kDistinct,
  kIte,

  // Functions/Constants from Theory ArraysEx.
  kSelect,
  kStore,

  // Functions/Constants from Theory FixedSizeBitVectors.
  // Note: bitvector constants are created using the BitvectorConst(),
  // BinaryConst(), or HexConst() methods.
  kConcat,
  kExtract,  // Indexed by two numerals.
  kBvnot,
  kBvand,
  kBvor,
  kBvneg,
  kBvadd,
  kBvmul,
  kBvudiv,
  kBvurem,
  kBvshl,
  kBvlshr,
  kBvnand,
  kBvnor,
  kBvxor,
  kBvcomp,
  kBvsub,
  kBvsdiv,
  kBvsrem,
  kBvsmod,
  kBvashr,
  kRepeat,       // Requires one index, number of copies.
  kZeroExtend,   // Requires one index, number of bits to extend by.
  kSignExtend,   // Requires one index, number of bits to extend by.
  kRotateLeft,   // Requires one index, number of bits to rotate by.
  kRotateRight,  // Requires one index, number of bits to rotate by.
  kBvult,
  kBvule,
  kBvugt,
  kBvuge,
  kBvslt,
  kBvsle,
  kBvsgt,
  kBvsge,

  // Functions/Constants from the arithmetic theories.
  // Note: arithmetic constants are created using the Numeral()
  // or Decimal() methods.

  // The following can be applied to both Ints and Reals.
  kUminus,
  kMinus,
  kPlus,
  kMult,
  kLe,
  kLt,
  kGe,
  kGt,

  // Operations on Ints only.
  kIntDiv,
  kMod,
  kAbs,
  kDivisible,  // Requires one index, the number to check if divisible by.
  kToReal,

  // Operations on Reals only.
  kRealDiv,
  kToInt,
  kIsInt,

  // Operations on String
  kStrAt,
  kStrConcat,
  kStrContains,
  kStrEnds,
  kStrIndexOf,
  kStrLen,
  kStrReplace,
  kStrStarts,
  kStrSubstr,
  kStrLe,
  kStrLt,
  kStrToInt,
  kStrFromInt,

  // RegExp Operations on Strings
  kStrToRe,
  kStrInRe,
  kReRange,
  kRePlus,
  kReStar,
  kReOption,
  kReIntersect,
  kReConcat,
  kReUnion,
  // The regex that matches no strings.  Use via GetTheoryConstantTerm.
  kReEmpty,

  kLastFunction = kReEmpty,
  kLastFunctionPlusOne,
};

// Returns the number of indices required for a given Sort.
int GetIndexCountForSort(Sort sort);

// Converts (indexed) sort constructor to the corresponding string in the
// SMT-LIB format.  Check fails if size of indices does not match the expected
// number of indices for the given sort.
std::string ToSMTString(Sort sort, const std::vector<unsigned>& indices);

// Returns the number of indices required for a given Function.
int GetIndexCountForFunction(Function function);

// Returns the number of arguments that a function expects.  Returns nullopt if
// the function can be applied to any (positive) number of arguments.
std::optional<int> GetArityForFunction(Function function);

// Converts (indexed) function to the corresponding string in the SMT-LIB
// format.  Check fails if size of indices does not match the expected number of
// indices for the given function.
std::string ToSMTString(Function function,
                        const std::vector<unsigned>& indices);
}  //  namespace op

}  //  namespace smt

#endif  // SRC_SMT_SMT_OPS_H_
