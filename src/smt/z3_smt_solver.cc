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

// Implements of methods for Z3Solver.  See z3_smt_solver.h for main
// documentation.

#include "src/smt/z3_smt_solver.h"

#include <cctype>
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "src/smt/smt.h"
#include "absl/container/node_hash_map.h"
#include "absl/memory/memory.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_format.h"
#include "absl/strings/str_replace.h"
#include "absl/strings/numbers.h"
#include "z3_api.h"
#include "re2/re2.h"

namespace smt {

namespace {

// Converts a numeral in `base` within `str` into a numeral and stores a base 10
// numeral into `result`. Return true on success.
// Only supports base in {2, 10, 16} at the moment.
// TODO: Evaluate supporting >64 bit terms (either: cap at 128 with Abseil
// implementations, or find a way to consume GMP or some other ~arbitrary
// precision integer parsing implementation.
bool ConvertNumeralToBase10(const std::string& str, int base, std::string* result) {
  if (base <= 0 || !result) {
    return false;
  }
  bool parsed = false;
  if (base == 2) {
    // Replace this if we need extra long bitvectors.
    long unsigned int intermediate = 0;
    for (long unsigned int i = 0; i < str.size(); ++i) {
      if (str.at(i) == '0') {
        intermediate *= 2;
      } else if (str.at(i) == '1') {
        intermediate = intermediate * 2 + 1;
      } else {
        return false;
      }
    }
    *result = absl::StrCat(intermediate);
    return true;
  } else if (base == 10) {
    long int intermediate;
    parsed = absl::SimpleAtoi(str, &intermediate);
    if (parsed) {
      *result = absl::StrCat(intermediate);
    }
    return parsed;
  } else if (base == 16) {
    long int intermediate;
    parsed = absl::SimpleHexAtoi(str, &intermediate);
    if (parsed) {
      *result = absl::StrCat(intermediate);
    }
    return parsed;
  }
  return parsed;
}

std::string ExternalInterpretedFunctionToString(
    const Z3Function::ExternalInterpretedFunction& function,
    const Z3Solver& solver) {
  switch (function) {
    case Z3Function::ExternalInterpretedFunction::kStrLe:
      return "ExternalInterpretedFunction::kStrLe";
    case Z3Function::ExternalInterpretedFunction::kStrLt:
      return "ExternalInterpretedFunction::kStrLt";
    case Z3Function::ExternalInterpretedFunction::None:
      solver.HandleError(SMTSolver::kError,
                         "Asked to return a string on an external interpreted "
                         "function type of None, which should not happen.");
      return "";
  }
  return "";
}

}  // namespace

std::string Z3Sort::ToString() const {
  try {
    return solver_.Z3ToString(z3_sort());
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return "";
  }
}

bool Z3Sort::Equals(const SortImplementation& rhs) const {
  try {
    const Z3Sort& sort = dynamic_cast<const Z3Sort&>(rhs);
    return eq(z3_sort(), sort.z3_sort());
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return false;
  }
}

Z3Function::Z3Function(const z3::func_decl& z3_func, const Z3Solver& solver)
    : z3_func_(new z3::func_decl(z3_func)),
      z3_decl_kind_(Z3_decl_kind::Z3_OP_UNINTERPRETED),
      solver_(solver) {}

Z3Function::Z3Function(const Z3Function::ExternalInterpretedFunction& kind,
                       const Z3Solver& solver)
    : z3_func_(nullptr),
      z3_decl_kind_(Z3_decl_kind::Z3_OP_UNINTERPRETED),
      external_interpreted_function_(kind),
      solver_(solver) {
  CHECK_NE(kind, Z3Function::ExternalInterpretedFunction::None)
      << "Cannot construct an external interpreted function with a type of "
         "'None'";
}

Z3Function::Z3Function(const Z3_decl_kind& kind, const Z3Solver& solver)
    : z3_func_(nullptr), z3_decl_kind_(kind), solver_(solver) {
  CHECK_NE(Z3_decl_kind::Z3_OP_UNINTERPRETED, kind)
      << "Cannot construct a simple function marked as an uninterpreted "
      << "function";
}

Z3Function::Z3Function(const Z3_decl_kind& kind, unsigned index,
                       const Z3Solver& solver)
    : z3_func_(nullptr),
      z3_decl_kind_(kind),
      indices_({index}),
      solver_(solver) {
  CHECK_NE(Z3_decl_kind::Z3_OP_UNINTERPRETED, kind)
      << "Cannot construct a simple function marked as an uninterpreted "
      << "function";
}

Z3Function::Z3Function(const Z3_decl_kind& kind, unsigned index1,
                       unsigned index2, const Z3Solver& solver)
    : z3_func_(nullptr),
      z3_decl_kind_(kind),
      indices_({index1, index2}),
      solver_(solver) {
  CHECK_NE(Z3_decl_kind::Z3_OP_UNINTERPRETED, kind)
      << "Cannot construct a simple function marked as an uninterpreted "
      << "function";
}

std::string Z3Function::ToString() const {
  try {
    if (IsSimpleFunction()) {
      return std::to_string(z3_decl_kind());
    } else if (IsExternalInterpretedFunction()) {
      return ExternalInterpretedFunctionToString(external_interpreted_function_,
                                                 solver_);
    } else {
      return solver_.Z3ToString(z3_func());
    }
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return "";
  }
}

bool Z3Function::Equals(const FunctionImplementation& function) const {
  try {
    const Z3Function& z3_function = dynamic_cast<const Z3Function&>(function);
    if (IsSimpleFunction() && z3_function.IsSimpleFunction()) {
      return z3_decl_kind() == z3_function.z3_decl_kind() &&
             indices() == z3_function.indices();
    } else if (IsExternalInterpretedFunction() &&
               z3_function.IsExternalInterpretedFunction()) {
      return external_interpreted_function() ==
             z3_function.external_interpreted_function();
    } else if (IsUninterpretedFunction() &&
               z3_function.IsUninterpretedFunction()) {
      return eq(z3_func(), z3_function.z3_func());
    } else {
      return false;
    }
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return false;
  }
}

std::string Z3Term::ToString() const {
  try {
    return solver_.Z3ToString(z3_expr());
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return "";
  }
}

unsigned Z3Term::NumChildren() const {
  try {
    return z3_expr().num_args();
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return 0;
  }
}

Term Z3Term::operator[](unsigned index) const {
  try {
    if (NumChildren() == 0 || index > NumChildren() - 1) {
      solver_.HandleError(SMTSolver::kError,
                          "Attempt to get out-of-bounds child");
      return Term();
    } else {
      return solver_.mkTerm(z3_expr().arg(index));
    }
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

bool Z3Term::Equals(const TermImplementation& t) const {
  try {
    const Z3Term& t_z3 = dynamic_cast<const Z3Term&>(t);
    return eq(z3_expr(), t_z3.z3_expr());
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return false;
  }
}

bool Z3Term::IsBoolConstant() const {
  try {
    if (z3_expr().is_const() && z3_expr().is_bool()) {
      const Z3_decl_kind kind = z3_expr().decl().decl_kind();
      return kind == Z3_OP_TRUE || kind == Z3_OP_FALSE;
    }
    return false;
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return false;
  }
}

bool Z3Term::GetBoolConstant() const {
  try {
    if (!IsBoolConstant()) {
      solver_.HandleError(SMTSolver::kError,
                          "GetBoolConstant called on non-bool-const");
      return false;
    } else {
      return solver_.GetBoolValue(z3_expr());
    }
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return false;
  }
}

bool Z3Term::IsIntegerConstant() const {
  try {
    return z3_expr().is_numeral() && z3_expr().is_int();
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return false;
  }
}

absl::StatusOr<uint64_t> Z3Term::IntegerConstantToUint64() const {
  try {
    if (!IsIntegerConstant()) {
      return absl::FailedPreconditionError("Term is not an integer constant.");
    }
    return solver_.GetIntegerValueAsUint64(z3_expr());
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return absl::UnknownError(e.msg());
  }
}

absl::StatusOr<int64_t> Z3Term::IntegerConstantToInt64() const {
  try {
    if (!IsIntegerConstant()) {
      return absl::FailedPreconditionError("Term is not an integer constant.");
    }
    return solver_.GetIntegerValueAsInt64(z3_expr());
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return absl::UnknownError(e.msg());
  }
}

bool Z3Term::IsBVConstant() const {
  try {
    if ( z3_expr().is_const() && z3_expr().is_bv() ) {
      // It does not seem to be necessary to check Z3_OP_BIT1 and Z3_OP_BIT0.
      const Z3_decl_kind kind = z3_expr().decl().decl_kind();
      return kind == Z3_OP_BNUM;
    }
    return false;
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return false;
  }
}

uint64_t Z3Term::BvConstantToUnsigned() const {
  try {
    if (!IsBVConstant()) {
      solver_.HandleError(SMTSolver::kError,
                          "BvConstantToUnsigned called on non-bitvector-const");
      return 0;
    } else if (GetBVSize() / kBitsPerByte > sizeof(uint64_t)) {
      solver_.HandleError(SMTSolver::kError,
                          "BvConstantToUnsigned called on a "
                          "Bitvector number that is larger than uint64");
      return 0;
    } else {
      return solver_.GetBitVectorValue(z3_expr());
    }
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return 0;
  }
}

std::string Z3Term::BvConstantToDecimalString() const {
  try {
    if (!IsBVConstant()) {
      solver_.HandleError(
          SMTSolver::kError,
          "BvConstantToDecimalString called on non-bitvector-const");
      return "";
    } else {
      if (!z3_expr_.is_numeral()) {
        solver_.HandleError(SMTSolver::kError,
                            "BitVector Laser Smt Type was not wrapping a Z3 "
                            "Numeric type. This should never happen.");
      }
      return z3_expr_.get_decimal_string(0);
    }
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return "";
  }
}

bool Z3Term::IsStringConstant() const {
  try {
    return solver_.IsStringConstant(z3_expr());
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return false;
  }
}

std::string Z3Term::GetStringConstant() const {
  try {
    if (!IsStringConstant()) {
      solver_.HandleError(SMTSolver::kError,
                          "GetStringConstant called on non-string-const");
      return "";
    } else {
      return solver_.GetStringValue(z3_expr());
    }
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return "";
  }
}

unsigned Z3Term::GetBVSize() const {
  try {
    const z3::sort z3_sort = z3_expr().get_sort();
    if (!z3_sort.is_bv()) {
      solver_.HandleError(SMTSolver::kError,
                          "Can't get size of non-bitvector term");
    }
    return z3_sort.bv_size();
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return 0;
  }
}

// TODO: allow index >= 64.
bool Z3Term::GetBit(unsigned index) const {
  if (!IsBVConstant()) {
    solver_.HandleError(SMTSolver::kError, "GetBit called on non-bv-const");
    return false;
  } else if (index >= GetBVSize() || index >= sizeof(uint64_t) * kBitsPerByte) {
    solver_.HandleError(SMTSolver::kError,
                        "GetBit called with out-of-bounds index");
    return false;
  } else {
    uint64_t value = BvConstantToUnsigned();
    return (value & (1 << index)) == 1;
  }
}

Sort Z3Term::GetSort() const {
  try {
    return solver_.mkSort(z3_expr().get_sort());
  } catch (const z3::exception& e) {
    solver_.HandleError(SMTSolver::kError, e.msg());
    return Sort();
  }
}

Z3Solver::Z3Solver()
    : SMTSolver("Z3"),
      context_(),
      params_(context_),
      logic_(""),
      solver_(nullptr) {}

bool Z3Solver::GetBoolValue(const z3::expr& expr) const {
  try {
    switch (Z3_get_bool_value(context_, expr)) {
      case Z3_L_TRUE:
        return true;
      case Z3_L_FALSE:
        return false;
      case Z3_L_UNDEF:
        HandleError(SMTSolver::kError,
                    "GetBoolValue called on undefined bool value");
        return false;
      // UNREACHABLE
      default:
        HandleError(SMTSolver::kError,
                    "GetBoolValue called on unknown bool value");
        return false;
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return false;
  }
}

uint64_t Z3Solver::GetBitVectorValue(const z3::expr& expr) const {
  try {
    uint64_t uint_value;
    if (Z3_get_numeral_uint64(context_, expr, &uint_value)) {
      return uint_value;
    } else {
      HandleError(SMTSolver::kError, "Failed to read uint64");
      return 0;
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return 0;
  }
}

absl::StatusOr<uint64_t> Z3Solver::GetIntegerValueAsUint64(
    const z3::expr& expr) const {
  try {
    uint64_t uint64_value = 0;
    bool fits = Z3_get_numeral_uint64(context_, expr, &uint64_value);
    if (fits) {
      return uint64_value;
    } else {
      return absl::OutOfRangeError("Value doesn't fit in an int64.");
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return absl::UnknownError(e.msg());
  }
}

absl::StatusOr<int64_t> Z3Solver::GetIntegerValueAsInt64(
    const z3::expr& expr) const {
  try {
    int64_t int64_value = 0;
    bool fits = Z3_get_numeral_int64(context_, expr, &int64_value);
    if (fits) {
      return int64_value;
    } else {
      return absl::OutOfRangeError("Value doesn't fit in an int64.");
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return absl::UnknownError(e.msg());
  }
}

bool Z3Solver::IsStringConstant(const z3::expr& expr) const {
  try {
    return Z3_is_string(context_, expr);
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return false;
  }
}

// The function assumes a hex digit as input.
static unsigned char HexToDec(unsigned char c) {
  if (c >= '0' && c <= '9') {
    return c - '0';
  } else if (c >= 'a' && c <= 'f') {
    return c - 'a' + 10;
  }
  return c - 'A' + 10;
}

static std::optional<unsigned char> UnescapeZ3(std::string_view subject) {
  if (RE2::FullMatch(subject, R"(\\u{([[:xdigit:]][[:xdigit:]])})", &subject)) {
    return HexToDec(subject[0]) * 16 + HexToDec(subject[1]);
  }
  return std::nullopt;
}

// As stated in https://github.com/Z3Prover/z3/issues/6490, Z3 uses `\u{..}` to
// wrap an escape sequence. For ASCII, Z3 escapes non-printable characters.
static std::string ConvertFromZ3StringEncoding(std::string str) {
  // ASCII escape sequences in Z3 are one or two characters in length. Normalize
  // the sequence to be two characters in length.
  RE2::GlobalReplace(&str, R"(\\u{([[:xdigit:]])})", R"(\\u{0\1})");

  std::string encoding;
  for (int64_t i = 0; i < str.size(); ++i) {
    unsigned char c = str[i];
    // Process the Z3 escape sequence.
    if ((str.size() - i) >= 6) {
      std::optional<unsigned char> escaped = UnescapeZ3(str.substr(i, 6));
      if (escaped.has_value()) {
        c = escaped.value();
        i = i + 5;
      }
    }
    encoding.push_back(c);
  }
  return encoding;
}

std::string Z3Solver::GetStringValue(const z3::expr& expr) const {
  try {
    return ConvertFromZ3StringEncoding(expr.get_string());
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return "";
  }
}

// Z3 does not support the non-zero arity sort.
Sort Z3Solver::DeclareSort(std::string name, int arity) {
  try {
    if (arity == 0) {
      const z3::symbol z3_symbol = context_.str_symbol(name.c_str());
      const Z3_sort z3_sort = Z3_mk_uninterpreted_sort(context_, z3_symbol);
      return mkSort(z3::sort(context_, z3_sort));
    } else {
      HandleError(SMTSolver::kUnsupported,
                  "Z3 does not support the non-zero arity sort");
      return Sort();
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Sort();
  }
}

Sort Z3Solver::GetTheorySort(op::Sort op_sort) {
  try {
    switch (op_sort) {
      case op::kBool:
        return mkSort(context_.bool_sort());
      case op::kInt:
        return mkSort(context_.int_sort());
      case op::kReal:
        return mkSort(context_.real_sort());
      case op::kArray:
        // This is a place-holder for the array sort constructor.
        return Sort();
      case op::kBitvec:
        HandleError(SMTSolver::kError, "BitVec sort requires index");
        return Sort();
      case op::kString:
        return mkSort(context_.string_sort());
      default:
        HandleError(SMTSolver::kError, "Unknown theory sort");
        return Sort();
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Sort();
  }
}

Sort Z3Solver::GetTheorySort(op::Sort op_sort, unsigned num) {
  try {
    switch (op_sort) {
      case op::kBitvec:
        return mkSort(context_.bv_sort(num));
      default:
        HandleError(SMTSolver::kError, "Unknown indexed theory sort");
        return Sort();
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Sort();
  }
}

// Z3 API does not support parameterized sorts.
// This function is only used to create array sort.
Sort Z3Solver::ApplySort(Sort sort_constructor, const std::vector<Sort>& args) {
  try {
    // sort_constructor is just a place holder for array sort.
    if (args.size() != 2) {
      HandleError(SMTSolver::kError,
                  "Array sort constructor expects exactly 2 arguments");
      return Sort();
    } else {
      return mkSort(context_.array_sort(GetZ3Sort(args[0]).z3_sort(),
                                        GetZ3Sort(args[1]).z3_sort()));
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Sort();
  }
}

Term Z3Solver::DeclareFunction(std::string name, Sort sort) {
  try {
    const z3::symbol z3_symbol = context_.str_symbol(name.c_str());
    const z3::sort z3_sort = GetZ3Sort(sort).z3_sort();
    return mkTerm(context_.constant(z3_symbol, z3_sort));
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

Function Z3Solver::DeclareFunction(std::string name,
                                   const std::vector<Sort>& rank) {
  if (rank.size() == 1) {
    HandleError(SMTSolver::kError, "Cannot create Function with no args");
    return Function();
  } else {
    try {
      z3::sort_vector z3_domains(context_);
      // The last rank is the sort of the returned value of the function.
      for (auto itr = rank.begin(); itr != rank.end() - 1; ++itr) {
        z3_domains.push_back(GetZ3Sort(*itr).z3_sort());
      }
      const z3::sort z3_codomain(GetZ3Sort(rank.back()).z3_sort());
      return mkFunction(
          context_.function(name.c_str(), z3_domains, z3_codomain));
    } catch (const z3::exception& e) {
      HandleError(SMTSolver::kError, e.msg());
      return Function();
    }
  }
}

// Z3 does not support abs and divisible func_decl_kinds.
Function Z3Solver::GetTheoryFunction(op::Function op_function) {
  try {
    switch (op_function) {
      case op::kNot:
      case op::kImplies:
      case op::kAnd:
      case op::kOr:
      case op::kXor:
      case op::kEqual:
      case op::kDistinct:
      case op::kIte:
      case op::kSelect:
      case op::kStore:
      case op::kConcat:
      case op::kBvnot:
      case op::kBvand:
      case op::kBvor:
      case op::kBvneg:
      case op::kBvadd:
      case op::kBvmul:
      case op::kBvudiv:
      case op::kBvurem:
      case op::kBvshl:
      case op::kBvlshr:
      case op::kBvult:
      case op::kBvnand:
      case op::kBvnor:
      case op::kBvxor:
      case op::kBvcomp:
      case op::kBvsub:
      case op::kBvsdiv:
      case op::kBvsrem:
      case op::kBvsmod:
      case op::kBvashr:
      case op::kBvule:
      case op::kBvugt:
      case op::kBvuge:
      case op::kBvslt:
      case op::kBvsle:
      case op::kBvsgt:
      case op::kBvsge:
      case op::kUminus:
      case op::kMinus:
      case op::kPlus:
      case op::kMult:
      case op::kLe:
      case op::kLt:
      case op::kGe:
      case op::kGt:
      case op::kIntDiv:
      case op::kMod:
      case op::kToReal:
      case op::kRealDiv:
      case op::kToInt:
      case op::kIsInt:
      case op::kStrAt:
      case op::kStrConcat:
      case op::kStrContains:
      case op::kStrEnds:
      case op::kStrIndexOf:
      case op::kStrLen:
      case op::kStrReplace:
      case op::kStrStarts:
      case op::kStrSubstr:
      case op::kStrToRe:
      case op::kStrInRe:
      case op::kStrToInt:
      case op::kStrFromInt:
      case op::kReOption:
      case op::kReStar:
      case op::kRePlus:
      case op::kReRange:
      case op::kReIntersect:
      case op::kReUnion:
      case op::kReConcat: {
        Z3_decl_kind z3_decl_kind = LookupZ3DeclKind(op_function);
        return mkFunction(z3_decl_kind);
      } break;
      case op::kExtract:
      case op::kRepeat:
      case op::kZeroExtend:
      case op::kSignExtend:
      case op::kRotateLeft:
      case op::kRotateRight: {
        HandleError(SMTSolver::kError, "Function index parameter expected");
        return Function();
      } break;
      case op::kStrLe: {
        return mkFunction(Z3Function::ExternalInterpretedFunction::kStrLe);
      } break;
      case op::kStrLt: {
        return mkFunction(Z3Function::ExternalInterpretedFunction::kStrLt);
      } break;
      default:
        HandleError(SMTSolver::kError, "Unknown theory function");
        return Function();
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Function();
  }
}

Function Z3Solver::GetTheoryFunction(op::Function op_function, unsigned index) {
  try {
    switch (op_function) {
      case op::kRepeat:
        CHECK_GT(index, 0);
        ABSL_FALLTHROUGH_INTENDED;
      case op::kZeroExtend:
      case op::kSignExtend:
      case op::kRotateLeft:
      case op::kRotateRight: {
        Z3_decl_kind z3_decl_kind = LookupZ3DeclKind(op_function);
        return mkFunction(z3_decl_kind, index);
      } break;
      default:
        HandleError(SMTSolver::kError, "Unknown indexed theory function");
        return Function();
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Function();
  }
}

Function Z3Solver::GetTheoryFunction(op::Function op_function, unsigned index1,
                                     unsigned index2) {
  try {
    switch (op_function) {
      case op::kExtract: {
        Z3_decl_kind z3_decl_kind = LookupZ3DeclKind(op_function);
        return mkFunction(z3_decl_kind, index1, index2);
      } break;
      default:
        HandleError(SMTSolver::kError, "Unknown indexed theory function");
        return Function();
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Function();
  }
}

Term Z3Solver::GetTheoryConstantTerm(op::Function op_function) {
  try {
    switch (op_function) {
      case op::kTrue:
        return mkTerm(context_.bool_val(true));
      case op::kFalse:
        return mkTerm(context_.bool_val(false));
      case op::kReEmpty: {
        // Z3 supports regular expressions over general sequence sorts, but
        // we just support regular expressions of string.
        z3::sort str_sort = context_.string_sort();
        return mkTerm(z3::to_expr(
            context_, Z3_mk_re_empty(context_, context_.re_sort(str_sort))));
      }
      default:
        HandleError(SMTSolver::kError, "Unknown theory constant");
        return Term();
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

Term Z3Solver::BooleanTerm(bool b) {
  try {
    return mkTerm(context_.bool_val(b));
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

Term Z3Solver::NumeralTerm(uint64_t num) {
  try {
    return mkTerm(context_.int_val(static_cast<uint64_t>(num)));
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

Term Z3Solver::NumeralTerm(std::string num) {
  try {
    auto term = context_.int_val(num.c_str());
    if (term.is_int()) {
      return mkTerm(term);
    } else {
      HandleError(SMTSolver::kError, "Must pass in an integer string.");
      return Term();
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

Term Z3Solver::SignedNumeralTerm(int64_t num) {
  try {
    return mkTerm(context_.int_val(static_cast<int64_t>(num)));
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

Term Z3Solver::DecimalTerm(double dec) {
  try {
    return mkTerm(context_.real_val(std::to_string(dec).c_str()));
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

Term Z3Solver::DecimalTerm(std::string dec) {
  try {
    return mkTerm(context_.real_val(dec.c_str()));
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

Term Z3Solver::BitvectorConstantTerm(uint64_t num, int width) {
  try {
    unsigned size = width;
    return mkTerm(context_.bv_val(static_cast<uint64_t>(num), size));
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

Term Z3Solver::BinaryConstantTerm(std::string bin_str) {
  try {
    unsigned size = bin_str.size();
    std::string as_decimal;
    if (!ConvertNumeralToBase10(bin_str, 2, &as_decimal)) {
      HandleError(SMTSolver::kError, "Cannot convert from binary string");
      return Term();
    }
    return mkTerm(context_.bv_val(as_decimal.c_str(), size));
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

Term Z3Solver::HexConstantTerm(std::string hex_str) {
  try {
    unsigned size = hex_str.size() * 4;
    std::string as_decimal;
    if (!ConvertNumeralToBase10(hex_str, 16, &as_decimal)) {
      HandleError(SMTSolver::kError, "Cannot convert from hex string");
      return Term();
    }
    return mkTerm(context_.bv_val(as_decimal.c_str(), size));
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

Term Z3Solver::StringConstantTerm(std::string str) {
  try {
    // Using the method that takes `(char*, unsigned)` method here which
    // properly handles null characters and doesn't do extra escaping. The
    // method that takes just `std::string` throws away the length information
    // and does extra escaping (http://github.com/Z3Prover/z3/issues/2286).
    return mkTerm(context_.string_val(str.c_str(), str.size()));
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

// Note that we don't yet support any terms that do not uniquely determine their
// own sort.  So, for now, we just check that the sort matches the term's sort
// and return.  If we add the theory of sets or datatypes, we will have to do
// actual work here.
Term Z3Solver::SetSortOfTerm(Term t, Sort sort) {
  try {
    const Z3Term& z3_term = GetZ3Term(t);
    if (!(z3_term.z3_expr().get_sort() = GetZ3Sort(sort).z3_sort())) {
      HandleError(SMTSolver::kError,
                  "Qualified sort does not match internal sort");
      return Term();
    } else {
      return t;
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

Term Z3Solver::ApplyFunction(Function f, const std::vector<Term>& args) {
  try {
    unsigned size = args.size();
    const Z3Function& z3_function = GetZ3Function(f);
    if (z3_function.IsUninterpretedFunction()) {
      std::vector<z3::expr> z3_args;
      z3_args.reserve(args.size());
      for (auto const& arg : args) {
        z3_args.push_back(GetZ3Term(arg).z3_expr());
      }
      return mkTerm(z3_function.z3_func()(size, z3_args.data()));
    } else if (z3_function.IsExternalInterpretedFunction()) {
      const auto external_function =
          z3_function.external_interpreted_function();
      const bool is_le =
          external_function == Z3Function::ExternalInterpretedFunction::kStrLe;
      const bool is_lt =
          external_function == Z3Function::ExternalInterpretedFunction::kStrLt;
      if (!is_lt && !is_le) {
        HandleError(SMTSolver::kError,
                    "Unsupported ExternalInterpretedFunction");
        return Term();
      }
      CHECK_EQ(size, 2);
      const auto mkcmp = [this](bool is_lt, const Term& l, const Term& r) {
        const auto left = GetZ3Term(l).z3_expr(),
                   right = GetZ3Term(r).z3_expr();
        if (is_lt) {
          return Z3_mk_str_lt(context_, left, right);
        }
        return Z3_mk_str_le(context_, left, right);
      };
      return mkTerm(z3::to_expr(context_, mkcmp(is_lt, args[0], args[1])));
    } else {
      switch (z3_function.z3_decl_kind()) {
        case Z3_decl_kind::Z3_OP_NOT: {
          CHECK_EQ(size, 1);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_not(context_, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_IMPLIES: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_implies(context_, GetZ3Term(args[0]).z3_expr(),
                                      GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_AND: {
          std::vector<Z3_ast> z3_asts;
          z3_asts.reserve(args.size());
          for (auto const& arg : args) {
            z3_asts.push_back(GetZ3Term(arg).z3_expr());
          }
          return mkTerm(
              z3::to_expr(context_, Z3_mk_and(context_, size, &(z3_asts[0]))));
        } break;
        case Z3_decl_kind::Z3_OP_OR: {
          std::vector<Z3_ast> z3_asts;
          z3_asts.reserve(args.size());
          for (auto const& arg : args) {
            z3_asts.push_back(GetZ3Term(arg).z3_expr());
          }
          return mkTerm(
              z3::to_expr(context_, Z3_mk_or(context_, size, &(z3_asts[0]))));
        } break;
        case Z3_decl_kind::Z3_OP_XOR: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_xor(context_, GetZ3Term(args[0]).z3_expr(),
                                  GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_EQ: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_eq(context_, GetZ3Term(args[0]).z3_expr(),
                                 GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_DISTINCT: {
          std::vector<Z3_ast> z3_asts;
          z3_asts.reserve(args.size());
          for (auto const& arg : args) {
            z3_asts.push_back(GetZ3Term(arg).z3_expr());
          }
          return mkTerm(z3::to_expr(
              context_, Z3_mk_distinct(context_, size, &(z3_asts[0]))));
        } break;
        case Z3_decl_kind::Z3_OP_ITE: {
          CHECK_EQ(size, 3);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_ite(context_, GetZ3Term(args[0]).z3_expr(),
                                  GetZ3Term(args[1]).z3_expr(),
                                  GetZ3Term(args[2]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SELECT: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_select(context_, GetZ3Term(args[0]).z3_expr(),
                                     GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_STORE: {
          CHECK_EQ(size, 3);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_store(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr(),
                                    GetZ3Term(args[2]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_CONCAT: {
          CHECK_GE(size, 1);
          z3::expr arg = GetZ3Term(args[0]).z3_expr();
          for (size_t i = 1; i < args.size(); i++) {
            arg = z3::to_expr(
                context_,
                Z3_mk_concat(context_, arg, GetZ3Term(args[i]).z3_expr()));
          }
          return mkTerm(arg);
        } break;
        case Z3_decl_kind::Z3_OP_BNOT: {
          CHECK_EQ(size, 1);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvnot(context_, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BAND: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvand(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BOR: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvor(context_, GetZ3Term(args[0]).z3_expr(),
                                   GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BNEG: {
          CHECK_EQ(size, 1);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvneg(context_, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BADD: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvadd(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BMUL: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvmul(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BUDIV: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvudiv(context_, GetZ3Term(args[0]).z3_expr(),
                                     GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BUREM: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvurem(context_, GetZ3Term(args[0]).z3_expr(),
                                     GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BSHL: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvshl(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BLSHR: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvlshr(context_, GetZ3Term(args[0]).z3_expr(),
                                     GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_ULT: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvult(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BNAND: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvnand(context_, GetZ3Term(args[0]).z3_expr(),
                                     GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BNOR: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvnor(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BXOR: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvxor(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BCOMP: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_eq(context_, GetZ3Term(args[0]).z3_expr(),
                                 GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BSUB: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvsub(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BSDIV: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvsdiv(context_, GetZ3Term(args[0]).z3_expr(),
                                     GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BSREM: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvsrem(context_, GetZ3Term(args[0]).z3_expr(),
                                     GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BSMOD: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvsmod(context_, GetZ3Term(args[0]).z3_expr(),
                                     GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_BASHR: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvashr(context_, GetZ3Term(args[0]).z3_expr(),
                                     GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_ULEQ: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvule(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_UGT: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvugt(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_UGEQ: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvuge(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SLT: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvslt(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SLEQ: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvsle(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SGT: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvsgt(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SGEQ: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_bvsge(context_, GetZ3Term(args[0]).z3_expr(),
                                    GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_UMINUS: {
          CHECK_EQ(size, 1);
          return mkTerm(z3::to_expr(
              context_,
              Z3_mk_unary_minus(context_, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SUB: {
          std::vector<Z3_ast> z3_asts;
          z3_asts.reserve(args.size());
          for (auto const& arg : args) {
            z3_asts.push_back(GetZ3Term(arg).z3_expr());
          }
          return mkTerm(
              z3::to_expr(context_, Z3_mk_sub(context_, size, &(z3_asts[0]))));
        } break;
        case Z3_decl_kind::Z3_OP_ADD: {
          std::vector<Z3_ast> z3_asts;
          z3_asts.reserve(args.size());
          for (auto const& arg : args) {
            z3_asts.push_back(GetZ3Term(arg).z3_expr());
          }
          return mkTerm(
              z3::to_expr(context_, Z3_mk_add(context_, size, &(z3_asts[0]))));
        } break;
        case Z3_decl_kind::Z3_OP_MUL: {
          std::vector<Z3_ast> z3_asts;
          z3_asts.reserve(args.size());
          for (auto const& arg : args) {
            z3_asts.push_back(GetZ3Term(arg).z3_expr());
          }
          return mkTerm(
              z3::to_expr(context_, Z3_mk_mul(context_, size, &(z3_asts[0]))));
        } break;
        case Z3_decl_kind::Z3_OP_LE: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_le(context_, GetZ3Term(args[0]).z3_expr(),
                                 GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_LT: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_lt(context_, GetZ3Term(args[0]).z3_expr(),
                                 GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_GE: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_ge(context_, GetZ3Term(args[0]).z3_expr(),
                                 GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_GT: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_gt(context_, GetZ3Term(args[0]).z3_expr(),
                                 GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_DIV: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_div(context_, GetZ3Term(args[0]).z3_expr(),
                                  GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_MOD: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_mod(context_, GetZ3Term(args[0]).z3_expr(),
                                  GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_TO_REAL: {
          CHECK_EQ(size, 1);
          return mkTerm(z3::to_expr(
              context_,
              Z3_mk_int2real(context_, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_TO_INT: {
          CHECK_EQ(size, 1);
          return mkTerm(z3::to_expr(
              context_,
              Z3_mk_real2int(context_, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_IS_INT: {
          CHECK_EQ(size, 1);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_is_int(context_, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_EXTRACT: {
          CHECK_EQ(size, 1);
          CHECK_EQ(z3_function.indices().size(), 2);
          unsigned index1 = z3_function.indices()[0];
          unsigned index2 = z3_function.indices()[1];
          return mkTerm(z3::to_expr(
              context_, Z3_mk_extract(context_, index1, index2,
                                      GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_REPEAT: {
          CHECK_EQ(size, 1);
          CHECK_EQ(z3_function.indices().size(), 1);
          unsigned index = z3_function.indices()[0];
          return mkTerm(z3::to_expr(
              context_,
              Z3_mk_repeat(context_, index, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_ZERO_EXT: {
          CHECK_EQ(size, 1);
          CHECK_EQ(z3_function.indices().size(), 1);
          unsigned index = z3_function.indices()[0];
          return mkTerm(z3::to_expr(
              context_,
              Z3_mk_zero_ext(context_, index, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SIGN_EXT: {
          CHECK_EQ(size, 1);
          CHECK_EQ(z3_function.indices().size(), 1);
          unsigned index = z3_function.indices()[0];
          return mkTerm(z3::to_expr(
              context_,
              Z3_mk_sign_ext(context_, index, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_ROTATE_LEFT: {
          CHECK_EQ(size, 1);
          CHECK_EQ(z3_function.indices().size(), 1);
          unsigned index = z3_function.indices()[0];
          return mkTerm(z3::to_expr(
              context_, Z3_mk_rotate_left(context_, index,
                                          GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_ROTATE_RIGHT: {
          CHECK_EQ(size, 1);
          CHECK_EQ(z3_function.indices().size(), 1);
          unsigned index = z3_function.indices()[0];
          return mkTerm(z3::to_expr(
              context_, Z3_mk_rotate_right(context_, index,
                                           GetZ3Term(args[0]).z3_expr())));
        } break;

          // String operators

        case Z3_decl_kind::Z3_OP_SEQ_AT: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_seq_at(context_, GetZ3Term(args[0]).z3_expr(),
                                     GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SEQ_CONCAT: {
          std::vector<Z3_ast> z3_asts;
          z3_asts.reserve(args.size());
          for (auto const& arg : args) {
            z3_asts.push_back(GetZ3Term(arg).z3_expr());
          }
          return mkTerm(z3::to_expr(
              context_, Z3_mk_seq_concat(context_, size, &(z3_asts[0]))));
        } break;
        case Z3_decl_kind::Z3_OP_SEQ_CONTAINS: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_,
              Z3_mk_seq_contains(context_, GetZ3Term(args[0]).z3_expr(),
                                 GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SEQ_INDEX: {
          CHECK_EQ(size, 3);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_seq_index(context_, GetZ3Term(args[0]).z3_expr(),
                                        GetZ3Term(args[1]).z3_expr(),
                                        GetZ3Term(args[2]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SEQ_LENGTH: {
          CHECK_EQ(size, 1);
          return mkTerm(z3::to_expr(
              context_,
              Z3_mk_seq_length(context_, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SEQ_PREFIX: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_seq_prefix(context_, GetZ3Term(args[0]).z3_expr(),
                                         GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SEQ_REPLACE: {
          CHECK_EQ(size, 3);
          return mkTerm(z3::to_expr(
              context_,
              Z3_mk_seq_replace(context_, GetZ3Term(args[0]).z3_expr(),
                                GetZ3Term(args[1]).z3_expr(),
                                GetZ3Term(args[2]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SEQ_EXTRACT: {
          CHECK_EQ(size, 3);
          return mkTerm(z3::to_expr(
              context_,
              Z3_mk_seq_extract(context_, GetZ3Term(args[0]).z3_expr(),
                                GetZ3Term(args[1]).z3_expr(),
                                GetZ3Term(args[2]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SEQ_SUFFIX: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_seq_suffix(context_, GetZ3Term(args[0]).z3_expr(),
                                         GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SEQ_TO_RE: {
          CHECK_EQ(size, 1);
          return mkTerm(z3::to_expr(
              context_,
              Z3_mk_seq_to_re(context_, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_SEQ_IN_RE: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_seq_in_re(context_, GetZ3Term(args[0]).z3_expr(),
                                        GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_STR_TO_INT: {
          CHECK_EQ(size, 1);
          return mkTerm(z3::to_expr(
              context_,
              Z3_mk_str_to_int(context_, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_INT_TO_STR: {
          CHECK_EQ(size, 1);
          return mkTerm(z3::to_expr(
              context_,
              Z3_mk_int_to_str(context_, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_RE_OPTION: {
          CHECK_EQ(size, 1);
          return mkTerm(z3::to_expr(
              context_,
              Z3_mk_re_option(context_, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_RE_STAR: {
          CHECK_EQ(size, 1);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_re_star(context_, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_RE_PLUS: {
          CHECK_EQ(size, 1);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_re_plus(context_, GetZ3Term(args[0]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_RE_RANGE: {
          CHECK_EQ(size, 2);
          return mkTerm(z3::to_expr(
              context_, Z3_mk_re_range(context_, GetZ3Term(args[0]).z3_expr(),
                                       GetZ3Term(args[1]).z3_expr())));
        } break;
        case Z3_decl_kind::Z3_OP_RE_INTERSECT: {
          std::vector<Z3_ast> z3_asts;
          z3_asts.reserve(args.size());
          for (auto const& arg : args) {
            z3_asts.push_back(GetZ3Term(arg).z3_expr());
          }
          return mkTerm(z3::to_expr(
              context_, Z3_mk_re_intersect(context_, size, &(z3_asts[0]))));
        } break;
        case Z3_decl_kind::Z3_OP_RE_UNION: {
          std::vector<Z3_ast> z3_asts;
          z3_asts.reserve(args.size());
          for (auto const& arg : args) {
            z3_asts.push_back(GetZ3Term(arg).z3_expr());
          }
          return mkTerm(z3::to_expr(
              context_, Z3_mk_re_union(context_, size, &(z3_asts[0]))));
        } break;
        case Z3_decl_kind::Z3_OP_RE_CONCAT: {
          std::vector<Z3_ast> z3_asts;
          z3_asts.reserve(args.size());
          for (auto const& arg : args) {
            z3_asts.push_back(GetZ3Term(arg).z3_expr());
          }
          return mkTerm(z3::to_expr(
              context_, Z3_mk_re_concat(context_, size, &(z3_asts[0]))));
        } break;
        default:
          HandleError(SMTSolver::kError, "Unsupported Z3_decl_kind");
          return Term();
      }
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}  // NOLINT -- disable linting for function length

Term Z3Solver::BoundVariableTerm(std::string name, Sort sort) {
  try {
    return mkTerm(context_.constant(name.c_str(), GetZ3Sort(sort).z3_sort()));
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

Term Z3Solver::Forall(const std::vector<Term>& vars, Term body) {
  try {
    z3::expr_vector z3_args(context_);
    for (auto const& term : vars) {
      z3_args.push_back(GetZ3Term(term).z3_expr());
    }
    z3::expr z3_body = GetZ3Term(body).z3_expr();
    return mkTerm(forall(z3_args, z3_body));
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

Term Z3Solver::Exists(const std::vector<Term>& vars, Term body) {
  try {
    z3::expr_vector z3_args(context_);
    for (auto const& term : vars) {
      z3_args.push_back(GetZ3Term(term).z3_expr());
    }
    z3::expr z3_body = GetZ3Term(body).z3_expr();
    return mkTerm(exists(z3_args, z3_body));
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

// TODO: Properly handle unimplemented logic by returning
// absl::UnimplementedError instead of an Unknown error.
absl::Status Z3Solver::SetLogic(std::string logic_name) {
  logic_ = logic_name;
  try {
    solver_ = std::make_unique<z3::solver>(context_, logic_.c_str());
    solver_->set(params_);
  } catch (const z3::exception& e) {
    return absl::UnknownError(e.msg());
  }
  return absl::OkStatus();
}

const absl::node_hash_map<std::string, std::string> Z3Solver::option_map_ = {
    {"produce-models", "model"},
    {"produce-unsat-cores", "unsat_core"},
    {"produce-proofs", "proof"}};

std::string Z3Solver::LookupZ3Option(const std::string& smt_option) const {
  auto it = option_map_.find(smt_option);
  CHECK(it != option_map_.end()) << "Invalid smt option: " << smt_option;
  return it->second;
}

void Z3Solver::SetOption(std::string option_name, bool value) {
  try {
    std::string z3_option = LookupZ3Option(option_name);
    params_.set(z3_option.c_str(), value);
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
  }
}

void Z3Solver::SetOption(std::string option_name, unsigned num) {
  try {
    std::string z3_option = LookupZ3Option(option_name);
    params_.set(z3_option.c_str(), num);
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
  }
}

void Z3Solver::SetOption(std::string option_name, std::string value) {
  try {
    std::string z3_option = LookupZ3Option(option_name);
    const z3::symbol symbol = context_.str_symbol(value.c_str());
    params_.set(z3_option.c_str(), symbol);
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
  }
}

void Z3Solver::SetEngineTimeout(unsigned timeout_ms) {
  try {
    params_.set("timeout", timeout_ms);
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
  }
}

void Z3Solver::AssertFormula(Term assertion) {
  try {
    solver()->add(GetZ3Term(assertion).z3_expr());
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
  }
}

SMTSolver::CheckSatResponse Z3Solver::CheckSat() {
  try {
    z3::check_result result = solver()->check();
    switch (result) {
      case z3::check_result::sat:
        return kSat;
      case z3::check_result::unsat:
        return kUnsat;
      case z3::check_result::unknown:
        return kUnknown;
      default:
        HandleError(SMTSolver::kError, "Unknown result.");
        return kUnknown;
    }
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return kUnknown;
  }
}

Term Z3Solver::GetValue(Term t) {
  try {
    return mkTerm(solver()->get_model().eval(GetZ3Term(t).z3_expr(), true));
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
    return Term();
  }
}

void Z3Solver::Push() {
  try {
    solver()->push();
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
  }
}

void Z3Solver::Pop() {
  try {
    solver()->pop();
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
  }
}

void Z3Solver::Reset() {
  try {
    solver()->reset();
  } catch (const z3::exception& e) {
    HandleError(SMTSolver::kError, e.msg());
  }
}

void Z3Solver::ResetAssertions() { Reset(); }

Sort Z3Solver::mkSort(const z3::sort& z3_sort) const {
  return Sort(std::make_shared<Z3Sort>(z3_sort, *this));
}

Function Z3Solver::mkFunction(const z3::func_decl& z3_func) const {
  return Function(std::make_shared<Z3Function>(z3_func, *this));
}

Function Z3Solver::mkFunction(
    const Z3Function::ExternalInterpretedFunction& function) const {
  return Function(std::make_shared<Z3Function>(function, *this));
}

Function Z3Solver::mkFunction(const Z3_decl_kind& z3_decl_kind) const {
  return Function(std::make_shared<Z3Function>(z3_decl_kind, *this));
}

Function Z3Solver::mkFunction(const Z3_decl_kind& z3_decl_kind,
                              unsigned index) const {
  return Function(std::make_shared<Z3Function>(z3_decl_kind, index, *this));
}

Function Z3Solver::mkFunction(const Z3_decl_kind& z3_decl_kind, unsigned index1,
                              unsigned index2) const {
  return Function(
      std::make_shared<Z3Function>(z3_decl_kind, index1, index2, *this));
}

Term Z3Solver::mkTerm(const z3::expr& expr) const {
  return Term(std::make_shared<Z3Term>(expr, *this));
}

const Z3Sort& Z3Solver::GetZ3Sort(const Sort& sort) const {
  return *dynamic_cast<const Z3Sort*>(sort.GetImplementation());
}

const Z3Function& Z3Solver::GetZ3Function(const Function& f) const {
  return *dynamic_cast<const Z3Function*>(f.GetImplementation());
}

const Z3Term& Z3Solver::GetZ3Term(const Term& term) const {
  return *dynamic_cast<const Z3Term*>(term.GetImplementation());
}

std::string Z3Solver::Z3ToString(const z3::expr& expr) const {
  return Z3_ast_to_string(context_, expr);
}

std::string Z3Solver::Z3ToString(const z3::sort& sort) const {
  return Z3_sort_to_string(context_, sort);
}

std::string Z3Solver::Z3ToString(const z3::func_decl& func) const {
  return Z3_func_decl_to_string(context_, func);
}

// If the Z3 solver is initialized, returns the pointer to the Z3 solver.
// Otherwise, initializes the solver with the Z3 context and logic (if any),
// and configures the solver with the global parameters.
z3::solver* const Z3Solver::solver() {
  if (!solver_) {
    if (!logic_.empty()) {
      solver_ = std::make_unique<z3::solver>(context_, logic_.c_str());
    } else {
      solver_ = std::make_unique<z3::solver>(context_);
    }
    solver_->set(params_);
  }
  return solver_.get();
}

Z3_decl_kind Z3Solver::LookupZ3DeclKind(op::Function op_function) const {
  switch (op_function) {
    case op::kNot:
      return Z3_decl_kind::Z3_OP_NOT;
    case op::kImplies:
      return Z3_decl_kind::Z3_OP_IMPLIES;
    case op::kAnd:
      return Z3_decl_kind::Z3_OP_AND;
    case op::kOr:
      return Z3_decl_kind::Z3_OP_OR;
    case op::kXor:
      return Z3_decl_kind::Z3_OP_XOR;
    case op::kEqual:
      return Z3_decl_kind::Z3_OP_EQ;
    case op::kDistinct:
      return Z3_decl_kind::Z3_OP_DISTINCT;
    case op::kIte:
      return Z3_decl_kind::Z3_OP_ITE;
    case op::kSelect:
      return Z3_decl_kind::Z3_OP_SELECT;
    case op::kStore:
      return Z3_decl_kind::Z3_OP_STORE;
    case op::kConcat:
      return Z3_decl_kind::Z3_OP_CONCAT;
    case op::kBvnot:
      return Z3_decl_kind::Z3_OP_BNOT;
    case op::kBvand:
      return Z3_decl_kind::Z3_OP_BAND;
    case op::kBvor:
      return Z3_decl_kind::Z3_OP_BOR;
    case op::kBvneg:
      return Z3_decl_kind::Z3_OP_BNEG;
    case op::kBvadd:
      return Z3_decl_kind::Z3_OP_BADD;
    case op::kBvmul:
      return Z3_decl_kind::Z3_OP_BMUL;
    case op::kBvudiv:
      return Z3_decl_kind::Z3_OP_BUDIV;
    case op::kBvurem:
      return Z3_decl_kind::Z3_OP_BUREM;
    case op::kBvshl:
      return Z3_decl_kind::Z3_OP_BSHL;
    case op::kBvlshr:
      return Z3_decl_kind::Z3_OP_BLSHR;
    case op::kBvult:
      return Z3_decl_kind::Z3_OP_ULT;
    case op::kBvnand:
      return Z3_decl_kind::Z3_OP_BNAND;
    case op::kBvnor:
      return Z3_decl_kind::Z3_OP_BNOR;
    case op::kBvxor:
      return Z3_decl_kind::Z3_OP_BXOR;
    case op::kBvcomp:
      return Z3_decl_kind::Z3_OP_BCOMP;
    case op::kBvsub:
      return Z3_decl_kind::Z3_OP_BSUB;
    case op::kBvsdiv:
      return Z3_decl_kind::Z3_OP_BSDIV;
    case op::kBvsrem:
      return Z3_decl_kind::Z3_OP_BSREM;
    case op::kBvsmod:
      return Z3_decl_kind::Z3_OP_BSMOD;
    case op::kBvashr:
      return Z3_decl_kind::Z3_OP_BASHR;
    case op::kBvule:
      return Z3_decl_kind::Z3_OP_ULEQ;
    case op::kBvugt:
      return Z3_decl_kind::Z3_OP_UGT;
    case op::kBvuge:
      return Z3_decl_kind::Z3_OP_UGEQ;
    case op::kBvslt:
      return Z3_decl_kind::Z3_OP_SLT;
    case op::kBvsle:
      return Z3_decl_kind::Z3_OP_SLEQ;
    case op::kBvsgt:
      return Z3_decl_kind::Z3_OP_SGT;
    case op::kBvsge:
      return Z3_decl_kind::Z3_OP_SGEQ;
    case op::kUminus:
      return Z3_decl_kind::Z3_OP_UMINUS;
    case op::kMinus:
      return Z3_decl_kind::Z3_OP_SUB;
    case op::kPlus:
      return Z3_decl_kind::Z3_OP_ADD;
    case op::kMult:
      return Z3_decl_kind::Z3_OP_MUL;
    case op::kLe:
      return Z3_decl_kind::Z3_OP_LE;
    case op::kLt:
      return Z3_decl_kind::Z3_OP_LT;
    case op::kGe:
      return Z3_decl_kind::Z3_OP_GE;
    case op::kGt:
      return Z3_decl_kind::Z3_OP_GT;
    case op::kIntDiv:
      return Z3_decl_kind::Z3_OP_DIV;
    case op::kMod:
      return Z3_decl_kind::Z3_OP_MOD;
    case op::kToReal:
      return Z3_decl_kind::Z3_OP_TO_REAL;
    case op::kRealDiv:
      return Z3_decl_kind::Z3_OP_DIV;
    case op::kToInt:
      return Z3_decl_kind::Z3_OP_TO_INT;
    case op::kIsInt:
      return Z3_decl_kind::Z3_OP_IS_INT;
    case op::kRepeat:
      return Z3_decl_kind::Z3_OP_REPEAT;
    case op::kZeroExtend:
      return Z3_decl_kind::Z3_OP_ZERO_EXT;
    case op::kSignExtend:
      return Z3_decl_kind::Z3_OP_SIGN_EXT;
    case op::kRotateLeft:
      return Z3_decl_kind::Z3_OP_ROTATE_LEFT;
    case op::kRotateRight:
      return Z3_decl_kind::Z3_OP_ROTATE_RIGHT;
    case op::kExtract:
      return Z3_decl_kind::Z3_OP_EXTRACT;

    // String operators
    case op::kStrAt:
      return Z3_decl_kind::Z3_OP_SEQ_AT;
    case op::kStrConcat:
      return Z3_decl_kind::Z3_OP_SEQ_CONCAT;
    case op::kStrContains:
      return Z3_decl_kind::Z3_OP_SEQ_CONTAINS;
    case op::kStrIndexOf:
      return Z3_decl_kind::Z3_OP_SEQ_INDEX;
    case op::kStrLen:
      return Z3_decl_kind::Z3_OP_SEQ_LENGTH;
    case op::kStrStarts:
      return Z3_decl_kind::Z3_OP_SEQ_PREFIX;
    case op::kStrReplace:
      return Z3_decl_kind::Z3_OP_SEQ_REPLACE;
    case op::kStrSubstr:
      return Z3_decl_kind::Z3_OP_SEQ_EXTRACT;
    case op::kStrEnds:
      return Z3_decl_kind::Z3_OP_SEQ_SUFFIX;
    case op::kStrToInt:
      return Z3_decl_kind::Z3_OP_STR_TO_INT;
    case op::kStrFromInt:
      return Z3_decl_kind::Z3_OP_INT_TO_STR;

    // RegExp operators
    case op::kStrToRe:
      return Z3_decl_kind::Z3_OP_SEQ_TO_RE;
    case op::kStrInRe:
      return Z3_decl_kind::Z3_OP_SEQ_IN_RE;
    case op::kReOption:
      return Z3_decl_kind::Z3_OP_RE_OPTION;
    case op::kReStar:
      return Z3_decl_kind::Z3_OP_RE_STAR;
    case op::kRePlus:
      return Z3_decl_kind::Z3_OP_RE_PLUS;
    case op::kReRange:
      return Z3_decl_kind::Z3_OP_RE_RANGE;
    case op::kReIntersect:
      return Z3_decl_kind::Z3_OP_RE_INTERSECT;
    case op::kReUnion:
      return Z3_decl_kind::Z3_OP_RE_UNION;
    case op::kReConcat:
      return Z3_decl_kind::Z3_OP_RE_CONCAT;

    default:
      HandleError(SMTSolver::kError, "Unknown theory function");
      return Z3_decl_kind::Z3_OP_UNINTERPRETED;
  }
}

}  // namespace smt
