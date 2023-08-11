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

// Abstract interface for the SMT-LIB v2.5 language.  Clients can use this class
// (and the classes defined in smt_term.h) with the expectation that any new or
// future SMT solver supporting the SMT-LIB standard can be added as a new
// instance using the same API.
//
// See the language standard document at www.smtlib.org for details on the
// SMT-LIB language standard.

#ifndef SRC_SMT_SMT_H_
#define SRC_SMT_SMT_H_

#include <cstdint>
#include <functional>
#include <string>
#include <utility>
#include <vector>

#include "src/smt/smt_ops.h"
#include "src/smt/smt_term.h"
#include "absl/container/node_hash_map.h"
#include "absl/status/status.h"
#include "absl/strings/string_view.h"
#include "src/base/source_location.h"

namespace smt {

// An abstract class API for SMT solvers (based on SMT-LIB v2.5).
// Abstract classes for the data objects (Identifier, Sort, Function, Term) are
// defined in "smt_term.h".
// The list of built-in SMT operators is defined in "smt_ops.h".
//
// To use the API, follow the steps below.  For a more detailed understanding,
// consult the SMT-LIB standard document at www.smtlib.org.  The names
// and layout of the API were chosen to closely follow the standard document.
// 1. Use SMTSolverFactory to create one of the supported solvers.
// 2. Call SetLogic to set the logic (see "Logics" link at www.smtlib.org for
//    the list of available SMT-LIB logics).
// 3. Call SetOption for each option you want to set.  See Section 4.1.6 of the
//    SMT-LIB standard document for a list of standard options (note that the
//    option_name parameter should omit the leading ':' character).
// 4. Create the sorts you need (a sort is the logic-equivalent of a type):
//    a) A new sort is declared using DeclareSort.
//    b) An SMT-LIB theory sort or sort constructor is obtained using
//       GetTheorySort.
//    c) A new application of a sort constructor is obtained using ApplySort.
// 5. Build some terms.  A term is either:
//    a) a constant created by NumeralTerm, DecimalTerm, BitvectorConstantTerm,
//       BinaryConstantTerm, HexConstantTerm, or StringConstantTerm;
//    b) a theory constant obtained by calling GetTheoryConstantTerm;
//    c) a bound variable obtained by calling BoundVariableTerm (which also
//       assigns a sort to the variable);
//    d) a new 0-ary function/constant created by calling DeclareFunction with a
//       single sort argument.
//    e) a function applied to one or more terms using ApplyFunction; functions
//       are either declared using DeclareFunction or are theory functions
//       obtained by calling GetTheoryFunction; or
//    f) a quantified formula created using Forall or Exists.
// 6. Use SMT solver commands to push and pop, assert formulas, check
//    satisfiability, and get values when the result is satisfiable.  See
//    Section 4.2 of the SMT-LIB standard document for a detailed description
//    of SMT-LIB commands.  Though not all commands are supported by this API,
//    the key commands are, and it should be straightforward to extend the API
//    to support others as needed.
class SMTSolver {
 public:
  // If any operation done within the solver fails, a handler function is called
  // and passed one of the following enum values.
  enum ErrorType {
    kError,
    kUnsupported,
    kOther,
  };

  // Possible responses from a call to CheckSat
  enum CheckSatResponse {
    kUnsat,
    kUnknown,
    kSat,
  };

  using HandlerFunctionType =
      std::function<void(ErrorType err, std::string msg)>;

  /////////////////////////////////////////////////////////////////////////////
  // Constructors and Destructor                                             //
  /////////////////////////////////////////////////////////////////////////////

  explicit SMTSolver(std::string solver_name);
  virtual ~SMTSolver() {}

  /////////////////////////////////////////////////////////////////////////////
  // Member data access                                                      //
  /////////////////////////////////////////////////////////////////////////////

  /////////////////////////////////////////////////////////////////////////////
  // Error handling                                                          //
  /////////////////////////////////////////////////////////////////////////////

  // Registers a function to be called if a failure occurs inside the solver.
  // Note: if no function is registered, the default behavior is
  // to print an error message and exit
  virtual void RegisterErrorHandler(HandlerFunctionType handler_function) {
    handler_function_ = std::move(handler_function);
  }

  // Calls the error handling function.
  void HandleError(
      ErrorType err, absl::string_view message,
      smt::base::SourceLocation loc = smt::base::SourceLocation::current()) const {
    handler_function_(
        err, absl::StrCat(loc.file_name(), ":", loc.line(), ": ", message));
  }

  /////////////////////////////////////////////////////////////////////////////
  // Sorts                                                                   //
  /////////////////////////////////////////////////////////////////////////////

  // Declares a new Sort (if arity=0) or declares a new Sort
  // constructor (if arity > 0).
  virtual Sort DeclareSort(std::string name, int arity) = 0;

  // Gets a Sort object corresponding to a sort declared in some SMT-LIB theory
  // specified by name, which may be an indexed identifier.
  virtual Sort GetTheorySort(Identifier name);

  // Gets a Sort object corresponding to a sort declared in some SMT-LIB theory
  // specified by an opcode from smt_ops.h.
  virtual Sort GetTheorySort(op::Sort op_sort) = 0;

  // Gets a Sort object corresponding to an indexed sort declared in an SMT-LIB
  // theory specified by an opcode from smt_ops.h.  This method is specifically
  // for getting sorts that are indexed by a single numeral.
  virtual Sort GetTheorySort(op::Sort op_sort, unsigned index) = 0;

  // Applies a sort constructor of arity 1 to one sort argument.  Note that the
  // default implementation is not particularly efficient: subclasses should
  // re-implement if an efficient implementation is desired.
  virtual Sort ApplySort(Sort sort_constructor, Sort arg);

  // Applies a sort constructor of arity 2 to two sort arguments.  Note that the
  // default implementation is not particularly efficient: subclasses should
  // re-implement if an efficient implementation is desired.
  virtual Sort ApplySort(Sort sort_constructor, Sort arg1, Sort arg2);

  // Applies a sort constructor of arbitrary arity to given sort arguments.
  virtual Sort ApplySort(Sort sort_constructor,
                         const std::vector<Sort>& args) = 0;

  /////////////////////////////////////////////////////////////////////////////
  // Functions and Constants                                                 //
  /////////////////////////////////////////////////////////////////////////////

  // Declares a new function of arity 0 (also sometimes called a symbolic
  // constant or variable) with a given sort.  Note that there is no guarantee
  // that two calls to DeclareFunction with the same name and sort return equal
  // Terms.  Doing so should be avoided.
  virtual Term DeclareFunction(std::string name, Sort sort) = 0;

  // Declares a new function of arity 1 with an input and output sort.  Note
  // that the default implementation is not particularly efficient: subclasses
  // should re-implement if an efficient implementation is desired.  Note also
  // that there is no guarantee that two calls to DeclareFunction with the same
  // name and sorts return equal Terms.  Doing so should be avoided.
  virtual Function DeclareFunction(std::string name, Sort arg_sort,
                                   Sort return_sort);

  // Declares a new function of arity 2 with input and output sorts.  Note that
  // the default implementation is not particularly efficient: subclasses should
  // re-implement if an efficient implementation is desired.  Note also that
  // there is no guarantee that two calls to DeclareFunction with the same name
  // and sorts return equal Terms.  Doing so should be avoided.
  virtual Function DeclareFunction(std::string name, Sort arg1_sort,
                                   Sort arg2_sort, Sort return_sort);

  // Declares a new function of abitrary arity and with a given rank (here, we
  // use "rank" in the mathematical logic sense): a list of n sorts, where the
  // first n-1 are the sorts of the function arguments and the last is the
  // return sort.  Note also that there is no guarantee that two calls to
  // DeclareFunction with the same name and rank return equal Terms.  Doing so
  // should be avoided.
  virtual Function DeclareFunction(std::string name,
                                   const std::vector<Sort>& rank) = 0;

  // Gets a Function object corresponding to a function declared in some SMT-LIB
  // theory specified by name, which may be an indexed identifier.
  virtual Function GetTheoryFunction(Identifier name);

  // Gets a Function object corresponding to a function declared in some SMT-LIB
  // theory specified by an opcode from smt_ops.h.
  virtual Function GetTheoryFunction(op::Function op_function) = 0;

  // Gets a Function object corresponding to an indexed function declared in an
  // SMT-LIB theory specified by an opcode from smt_ops.h.  This method is
  // specifically for getting functions that are indexed by a single numeral.
  virtual Function GetTheoryFunction(op::Function op_function,
                                     unsigned index) = 0;

  // Gets a Function object corresponding to an indexed function declared in an
  // SMT-LIB theory specified by an opcode from smt_ops.h.  This method is
  // specifically for getting functions that are indexed by two numerals.
  virtual Function GetTheoryFunction(op::Function op_function, unsigned index1,
                                     unsigned index2) = 0;

  // Gets a Term object corresponding to a 0-arity function (i.e. a constant)
  // declared in some SMT-LIB theory specified by name, which may be an indexed
  // identifier.
  virtual Term GetTheoryConstantTerm(Identifier name);

  // Gets a Term object corresponding to a 0-arity function (i.e. a constant)
  // declared in some SMT-LIB theory specified by an opcode from smt_ops.h.
  virtual Term GetTheoryConstantTerm(op::Function op_function) = 0;

  // Creates a Term corresponding to a boolean constant from a bool.
  virtual Term BooleanTerm(bool b) = 0;

  // Creates a Term corresponding to a numeric constant from an unsigned int64.
  virtual Term NumeralTerm(uint64_t num) = 0;

  // Creates a Term corresponding to a numeric constant from a string.  The
  // string is expected to be a sequence of digits.  If not, the error handler
  // function is called with an error.
  virtual Term NumeralTerm(std::string num) = 0;

  // Creates a Term corresponding to a numeric constant from an int64.
  virtual Term SignedNumeralTerm(int64_t num) = 0;

  // Creates a Term corresponding to a decimal constant from a double.
  virtual Term DecimalTerm(double decimal_value) = 0;

  // Creates a Term corresponding to a decimal constant from a string.  The
  // string is expected to be a sequence of digits with optionally a decimal
  // followed by another sequence of digits.  If not, the error handler function
  // is called with an error.
  virtual Term DecimalTerm(std::string decimal_str) = 0;

  // Creates a Term corresponding to a bitvector constant from an unsigned.  The
  // number of bits in the bitvector constant is width.  If width is not enough
  // to represent num, the error handler is called with an error.
  virtual Term BitvectorConstantTerm(uint64_t num, int width) = 0;

  // Creates a Term corresponding to a bitvector constant from a string.  The
  // string should be a sequence of 1's and 0's.  If not, the error handler
  // function is called with an error.
  virtual Term BinaryConstantTerm(std::string bin_str) = 0;

  // Creates a Term corresponding to a bitvector constant from a string.  The
  // string should be a sequence of hex digits.  If not, the error handler
  // function is called with an error.
  virtual Term HexConstantTerm(std::string hex_str) = 0;

  // Creates a Term corresponding to the given string.
  virtual Term StringConstantTerm(std::string str) = 0;

  /////////////////////////////////////////////////////////////////////////////
  // Creating new Terms from old                                             //
  /////////////////////////////////////////////////////////////////////////////

  // Sets the sort of t to be the given sort (only needed in the rare case that
  // the term itself does not uniquely determine the sort).
  virtual Term SetSortOfTerm(Term t, Sort sort) = 0;

  // Creates a Term by applying the unary function f to one argument.  Note that
  // the default implementation is not particularly efficient: subclasses should
  // re-implement if an efficient implementation is desired.
  virtual Term ApplyFunction(Function f, Term arg);

  // Creates a Term by applying the binary function f to two arguments.  Note
  // that the default implementation is not particularly efficient: subclasses
  // should re-implement if an efficient implementation is desired.
  virtual Term ApplyFunction(Function f, Term arg1, Term arg2);

  // Creates a Term by applying the ternary function f to three arguments.  Note
  // that the default implementation is not particularly efficient: subclasses
  // should re-implement if an efficient implementation is desired.
  virtual Term ApplyFunction(Function f, Term arg1, Term arg2, Term arg3);

  // Creates a Term by applying the n-ary function f to n arguments.
  virtual Term ApplyFunction(Function f, const std::vector<Term>& args) = 0;

  // Creates a Term by applying a unary function to one argument.  The function
  // is specified by an opcode from smt_ops.h (this is a shortcut to avoid
  // having to call GetTheoryFunction).  Note that the default implementation is
  // not particularly efficient: subclasses should re-implement if an efficient
  // implementation is desired.
  virtual Term ApplyFunction(op::Function op_function, Term arg);

  // Creates a Term by applying a binary function to two arguments.  The
  // function is specified by an opcode from smt_ops.h (this is a shortcut to
  // avoid having to call GetTheoryFunction).  Note that the default
  // implementation is not particularly efficient: subclasses should
  // re-implement if an efficient implementation is desired.
  virtual Term ApplyFunction(op::Function op_function, Term arg1, Term arg2);

  // Creates a Term by applying a ternary function to three arguments.  The
  // function is specified by an opcode from smt_ops.h (this is a shortcut to
  // avoid having to call GetTheoryFunction).  Note that the default
  // implementation is not particularly efficient: subclasses should
  // re-implement if an efficient implementation is desired.
  virtual Term ApplyFunction(op::Function op_function, Term arg1, Term arg2,
                             Term arg3);

  // Creates a Term by applying an n-ary function to n arguments.  The function
  // is specified by an opcode from smt_ops.h (this is a shortcut to avoid
  // having to call GetTheoryFunction).  Note that the default implementation is
  // not particularly efficient: subclasses should re-implement if an efficient
  // implementation is desired.
  virtual Term ApplyFunction(op::Function op_function,
                             const std::vector<Term>& args);

  /////////////////////////////////////////////////////////////////////////////
  // Quantified formulas                                                     //
  /////////////////////////////////////////////////////////////////////////////

  // Creates a bound variable with a given name and sort
  virtual Term BoundVariableTerm(std::string name, Sort sort) = 0;

  // Creates a new quantified Term.  The parameter vars must be a vector of
  // boundVar terms.  Any occurrences of these boundVar terms (that are free)
  // in body are bound.
  virtual Term Forall(const std::vector<Term>& vars, Term body) = 0;
  virtual Term Exists(const std::vector<Term>& vars, Term body) = 0;

  /////////////////////////////////////////////////////////////////////////////
  // SMT Solver commands                                                     //
  /////////////////////////////////////////////////////////////////////////////

  // Sets the SMT-LIB logic. In most circumstances, this will be the first
  // command sent to the SMT solver after starting the solver and after each
  // Reset.
  // See the automaton in Section 4.1 in the proposed SMT-LIB standard v2.6 for
  // more details on conforming to the standard:
  // http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.5-draft-2.pdf
  // Returns OK if successful, Unimplemented if the logic is not supported,
  // and some other error status if another error occurred.
  virtual absl::Status SetLogic(std::string logic_name) = 0;

  // Sets a Boolean option.  The option_name parameter is the name of an option
  // from the SMT-LIB standard without the leading ':'.
  virtual void SetOption(std::string option_name, bool value) = 0;

  // Sets a numeric option.  The option_name parameter is the name of an option
  // from the SMT-LIB standard without the leading ':'.
  virtual void SetOption(std::string option_name, unsigned num) = 0;

  // Sets a string option.  The option_name parameter is the name of an option
  // from the SMT-LIB standard without the leading ':'.
  virtual void SetOption(std::string option_name, std::string value) = 0;

  // Set the timeout in milliseconds for the SMT Engine.
  // If the engine times out, it should return a kUnknown status.
  // Note that timeouts are a slightly riskier feature in the solvers, with
  // no guarantee that the solver, or globals in the solver, will be in a
  // healthy state after a timeout occurs.
  // Users may want to isolate SMT solvers with a timeout in their own thread or
  // process and treat a timeout as an unrecoverable error.
  virtual void SetEngineTimeout(unsigned timeout_ms) = 0;

  // Asserts a formula to the SMT solver.  The variable assertion must be a Term
  // of sort Bool.
  virtual void AssertFormula(Term assertion) = 0;

  // Checks that the conjunction of all asserted formulas so far is satisfiable.
  // Returns kSat if so, kUnsat if provably not satisfiable, and kUnknown when
  // the solver is unable to determine satisfiability.
  virtual CheckSatResponse CheckSat() = 0;

  // Only valid after a call to CheckSat that returns kSat.  Otherwise calls the
  // error handling function.  Returns the value of any Term in the solution
  // computed by CheckSat.  The Term returned is guaranteed to be a constant of
  // the same sort as t.
  virtual Term GetValue(Term t) = 0;

  // Sets a checkpoint.
  virtual void Push() = 0;

  // Discards the effects of all SMTSolver commands executed since the last
  // checkpoint.
  virtual void Pop() = 0;

  // Resets solver to its initial state (i.e. before initial call to SetLogic).
  virtual void Reset() = 0;

  // Pops all saved checkpoints and clears any assertions in the top-most state.
  // However, changes made by calling Setlogic or SetOption are retained.
  virtual void ResetAssertions() = 0;

 private:
  // Function to call if an error occurs inside the SMT solver.  See comment for
  // RegisterErrorHandler.
  HandlerFunctionType handler_function_;

  // Inserts a sort in the symbol table.
  void AddSort(std::string name, op::Sort sort);

  // Inserts a function in the symbol table.
  void AddFunction(std::string name, op::Function function);

  // Name of this solver
  const std::string solver_name_;

  // Symbol table for sorts declared by theories in SMT-LIB.  Maps name of
  // sort to its opcode from smt_ops.h.
  absl::node_hash_map<std::string, op::Sort> sort_symbols_;

  // Symbol table for functions declared by theories in SMT-LIB.  Maps name of
  // function to its opcode from smt_ops.h.
  absl::node_hash_map<std::string, op::Function> function_symbols_;
};

}  // namespace smt

#endif  // SRC_SMT_SMT_H_
