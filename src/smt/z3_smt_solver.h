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

// Implementation of an SMTSolver abstract interface for the Z3 Solver.  See
// smt.h for documentation of the interface.

#ifndef SRC_SMT_Z3_SMT_SOLVER_H_
#define SRC_SMT_Z3_SMT_SOLVER_H_

#include <cstdint>
#include <memory>
#include <ostream>
#include <string>
#include <vector>

#include "src/smt/smt.h"
#include "src/smt/smt_term.h"
#include "absl/container/node_hash_map.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "z3++.h"

namespace smt {

// Forward declaration needed below.
class Z3Solver;

// The Z3Sort class encapsulates the Z3::sort.
class Z3Sort final : public SortImplementation {
 public:
  // Constructs a wrapper for the z3_sort with a constant reference to
  // the Z3Solver.
  Z3Sort(const z3::sort& z3_sort, const Z3Solver& solver)
      : z3_sort_(z3_sort), solver_(solver) {}

  // Returns a constant reference of the z3_sort_.
  const z3::sort& z3_sort() const { return z3_sort_; }

  std::string ToString() const final;

  friend std::ostream& operator<<(std::ostream& out, const Z3Sort& sort) {
    return out << sort.ToString();
  }

  bool Equals(const SortImplementation& rhs) const override;

 private:
  // The z3::sort of the Z3Sort.
  const z3::sort z3_sort_;

  // Reference to the main Z3 solver class.
  const Z3Solver& solver_;
};

// The Z3Function class encapsulates three possible representations.
// Some functions (simple functions) can be represented just as a
// Z3_decl_kind enum.  The others (non-simple functions) require a
// z3::func_decl.
// The last case is addresses the case where functionality exists in Z3,
// but hasn't made it into the z3_func_decl enumeration. These are still
// possible to use via the API, however, so we special-case these via an
// internal identifier. https://github.com/Z3Prover/z3/issues/4721 tracks one
// case of this.
// TODO: It may be possible to remove that case if the Z3 API now implements
// all of the primitives we implement in the full API.  Note that simple
// functions are interpreted functions with an explicit function declaration
// kind, and non-simple functions are uninterpreted functions.
class Z3Function final : public FunctionImplementation {
 public:
  // Interpreted functions that we can actually access via the Z3 API, but which
  // don't have a simple function type in Z3.
  enum ExternalInterpretedFunction { None, kStrLe, kStrLt };

  // Constructs a wrapper for a z3::func_decl with a constant
  // reference to the Z3Solver. It creates a non-simple function.
  Z3Function(const z3::func_decl& z3_func, const Z3Solver& solver);

  // Constructs a wrapper for a Z3_decl_kind with a constant
  // reference to the Z3Solver. It creates a simple function.
  Z3Function(const Z3_decl_kind& kind, const Z3Solver& solver);

  // Constructs a wrapper for an 'ExternalInterpretedFunction' with a constant
  // reference to the Z3Solver for interpreted functions that are supported in
  // Z3 but not in Z3_decl_kind. We have not implemented the various indexed
  // constructors for this now as they are not needed by the functions in this
  // category.
  Z3Function(const ExternalInterpretedFunction& kind, const Z3Solver& solver);

  // Constructs a wrapper for a Z3_decl_kind with a constant
  // reference to the Z3Solver.
  // It creates a simple function with an index parameter,
  // which is used for operators like the bit-vector sign extension.
  Z3Function(const Z3_decl_kind& kind, unsigned index, const Z3Solver& solver);

  // Constructs a wrapper for a Z3_decl_kind with a constant
  // reference to the Z3Solver.
  // It creates a simple function with two index parameters,
  // which is only for the bit-vector extract operator.
  Z3Function(const Z3_decl_kind& kind, unsigned index1, unsigned index2,
             const Z3Solver& solver);

  // Returns true if this function is NOT uninterpreted,
  // which is used to tag simple functions.
  bool IsSimpleFunction() const {
    return z3_decl_kind_ != Z3_decl_kind::Z3_OP_UNINTERPRETED;
  }

  // Returns true if this function is interpreted, but not supported via
  // z3_decl_kind.
  bool IsExternalInterpretedFunction() const {
    return external_interpreted_function_ != ExternalInterpretedFunction::None;
  }

  // Returns true if this function is uninterpreted.
  bool IsUninterpretedFunction() const {
    return z3_decl_kind_ == Z3_decl_kind::Z3_OP_UNINTERPRETED &&
           !IsExternalInterpretedFunction();
  }

  // Returns a constant reference of the func_decl for non-simple functions.
  // Check-fails for simple functions.
  const z3::func_decl& z3_func() const {
    CHECK(IsUninterpretedFunction())
        << "Cannot return Z3 function decl for simple functions";
    return *z3_func_;
  }

  // Returns a constant reference to the z3_decl_kind_ for simple functions.
  // Check-fails for non-simple functions.
  const Z3_decl_kind& z3_decl_kind() const {
    CHECK(IsSimpleFunction()) << "Cannot return Z3_decl_kind for non-simple or "
                                 "externally interpreted functions";
    return z3_decl_kind_;
  }

  const ExternalInterpretedFunction& external_interpreted_function() const {
    CHECK(IsExternalInterpretedFunction())
        << "Cannot get an ExternalInterpretedFunction for a simple or "
           "uninterpreted function.";
    return external_interpreted_function_;
  }

  // Returns a constant vector of index parameters.
  const std::vector<unsigned> indices() const { return indices_; }

  std::string ToString() const final;

  friend std::ostream& operator<<(std::ostream& out, const Z3Function& func) {
    return out << func.ToString();
  }

  bool Equals(const FunctionImplementation& function) const override;

 private:
  // The pointer to z3::func_decl for non-simple functions.
  std::unique_ptr<z3::func_decl> z3_func_;

  // The Z3_decl_kind for simple functions.  Note that a value of
  // Z3_decl_kind::Z3_OP_UNINTERPRETED denotes that this is *not* a simple
  // function.
  const Z3_decl_kind z3_decl_kind_;

  // For interpreted functions in Z3 that are not supported via z3_func_decl.
  const ExternalInterpretedFunction external_interpreted_function_ =
      ExternalInterpretedFunction::None;

  // The index parameters of parameterized simple functions such as
  // the bitvector extract operator with high and low index parameters.
  const std::vector<unsigned> indices_;

  // The reference to the main Z3 solver class.
  const Z3Solver& solver_;
};

// The Z3Term class encapsulates the z3:expr class.
class Z3Term final : public TermImplementation {
 public:
  // Constructs a wrapper for the z3_expr with a constant reference
  // to the Z3Solver.
  Z3Term(const z3::expr& z3_expr, const Z3Solver& solver)
      : z3_expr_(z3_expr), solver_(solver) {}

  // The following are implementations of interface methods.
  unsigned NumChildren() const final;
  Term operator[](unsigned index) const final;
  bool Equals(const TermImplementation& t) const final;
  bool IsBoolConstant() const final;
  bool GetBoolConstant() const final;
  bool IsIntegerConstant() const final;
  absl::StatusOr<int64_t> IntegerConstantToInt64() const final;
  absl::StatusOr<uint64_t> IntegerConstantToUint64() const final;
  bool IsBVConstant() const final;
  uint64_t BvConstantToUnsigned() const final;
  std::string BvConstantToDecimalString() const final;
  bool IsStringConstant() const final;
  std::string GetStringConstant() const final;
  unsigned GetBVSize() const final;
  bool GetBit(unsigned index) const final;
  Sort GetSort() const final;

  // Returns the z3_expr_.
  const z3::expr& z3_expr() const { return z3_expr_; }

  std::string ToString() const final;

  friend std::ostream& operator<<(std::ostream& out, const Z3Term& term) {
    return out << term.ToString();
  }

 private:
  // The z3::expr.
  const z3::expr z3_expr_;

  // Reference to the main Z3 solver class.
  const Z3Solver& solver_;
};

class Z3Solver final : public SMTSolver {
 public:
  // Creates a Z3Solver with a fresh Z3 context and empty Z3
  // parameters setting for the context.
  // Note that the Z3 logic is initialized to be empty string
  // and the Z3 solver is initialized to be null.
  Z3Solver();

  // The following are implementations of interface methods.
  Sort DeclareSort(std::string name, int arity) final;
  Sort GetTheorySort(op::Sort op_sort) final;
  Sort GetTheorySort(op::Sort op_sort, unsigned num) final;
  Sort ApplySort(Sort sort_constructor, const std::vector<Sort>& args) final;
  Term DeclareFunction(std::string name, Sort sort) final;
  Function DeclareFunction(std::string name,
                           const std::vector<Sort>& rank) final;
  Function GetTheoryFunction(op::Function op_function) final;
  Function GetTheoryFunction(op::Function op_function, unsigned index) final;
  Function GetTheoryFunction(op::Function op_function, unsigned index1,
                             unsigned index2) final;
  Term GetTheoryConstantTerm(op::Function op_function) final;
  Term BooleanTerm(bool b) final;
  Term NumeralTerm(uint64_t num) final;
  Term NumeralTerm(std::string num) final;
  Term SignedNumeralTerm(int64_t num) final;
  Term DecimalTerm(double dec) final;
  Term DecimalTerm(std::string dec) final;
  Term BitvectorConstantTerm(uint64_t num, int width) final;
  Term BinaryConstantTerm(std::string bin_str) final;
  Term HexConstantTerm(std::string hex_str) final;
  Term StringConstantTerm(std::string str) final;
  Term SetSortOfTerm(Term t, Sort sort) final;
  Term ApplyFunction(Function f, const std::vector<Term>& args) final;
  Term BoundVariableTerm(std::string name, Sort sort) final;
  Term Forall(const std::vector<Term>& vars, Term body) final;
  Term Exists(const std::vector<Term>& vars, Term body) final;
  absl::Status SetLogic(std::string logic_name) final;
  void SetOption(std::string option_name, bool value) final;
  void SetOption(std::string option_name, unsigned num) final;
  void SetOption(std::string option_name, std::string value) final;
  void SetEngineTimeout(unsigned timeout_ms) final;
  void AssertFormula(Term assertion) final;
  CheckSatResponse CheckSat() final;
  Term GetValue(Term t) final;
  void Push() final;
  void Pop() final;
  void Reset() final;
  void ResetAssertions() final;

  // These are methods for building Sorts, Functions, and Terms.
  Sort mkSort(const z3::sort& z3_sort) const;
  Function mkFunction(const z3::func_decl& z3_func) const;
  Function mkFunction(
      const Z3Function::ExternalInterpretedFunction& function) const;
  Function mkFunction(const Z3_decl_kind& z3_decl_kind) const;
  Function mkFunction(const Z3_decl_kind& z3_decl_kind, unsigned index) const;
  Function mkFunction(const Z3_decl_kind& z3_decl_kind, unsigned index1,
                      unsigned index2) const;
  Term mkTerm(const z3::expr& expr) const;

  // These are getter methods for obtaining the constant value from expressions.
  bool GetBoolValue(const z3::expr& expr) const;
  uint64_t GetBitVectorValue(const z3::expr& expr) const;
  absl::StatusOr<uint64_t> GetIntegerValueAsUint64(const z3::expr& expr) const;
  absl::StatusOr<int64_t> GetIntegerValueAsInt64(const z3::expr& expr) const;
  bool IsStringConstant(const z3::expr& expr) const;
  std::string GetStringValue(const z3::expr& expr) const;

  // Returns the Z3 implementation classes associated with the interface
  // classes.
  const Z3Sort& GetZ3Sort(const Sort& sort) const;
  const Z3Function& GetZ3Function(const Function& f) const;
  const Z3Term& GetZ3Term(const Term& term) const;

  std::string Z3ToString(const z3::expr& expr) const;
  std::string Z3ToString(const z3::sort& sort) const;
  std::string Z3ToString(const z3::func_decl& func) const;

 private:
  // Returns the constant pointer to the Z3 solver.
  z3::solver* const solver();

  // Looks up the Z3_decl_kind related the op::Function.
  Z3_decl_kind LookupZ3DeclKind(op::Function op_function) const;

  // Looks up the Z3 option related the smt_option.
  std::string LookupZ3Option(const std::string& smt_option) const;

  // The Z3 context for creating new Z3 expressions, function declarators
  // and sorts.
  z3::context context_;

  // The global parameters used to configure the Z3 solver.
  z3::params params_;

  // The SMT theory used to configure the Z3 solver.
  std::string logic_;

  // The pointer to the main Z3 solver.
  std::unique_ptr<z3::solver> solver_;

  // The map from smt options to Z3 options
  static const absl::node_hash_map<std::string, std::string> option_map_;
};

}  // namespace smt

#endif  // SRC_SMT_Z3_SMT_SOLVER_H_
