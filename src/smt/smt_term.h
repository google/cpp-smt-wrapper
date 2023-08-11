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

// Abstract classes for sorts, terms, functions, and identifiers used in
// smt.h.  See comments there for more information.
//
// See the language standard document at www.smtlib.org for details on the
// SMT-LIB language standard.

#ifndef SRC_SMT_SMT_TERM_H_
#define SRC_SMT_SMT_TERM_H_

#include <cstdint>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "absl/log/check.h"
#include "absl/log/log.h"
#include "absl/status/statusor.h"
#include "absl/strings/string_view.h"

namespace smt {

// Abstract interface classes for SMT-LIB sorts, terms, and functions.  There
// are several design objectives:
// 1. Objects of the class should be small so they can be easily passed around
//    and stored in containers.
// 2. The client should not have to worry about pointer ownership.
// 3. It should be possible to support multiple implementations without changes
//    to client code.
// 4. The class should provide a basic set of methods for manipulating and
//    examining the underlying data.
//
// These objectives led to the current design:
// 1. We use abstract <Sort|Function|Term>Implementation classes which provide
//    an interface that should be inherited and implemented by each solver
//    implementation.
// 2. We then use wrapper classes that wrap a smart pointer around the
//    <*>Implementation classes.  The wrapper classes take care of reference
//    counting (via shared_ptr) and simply pass method calls on to the
//    implementation classes.

// Abstract interface class for solver-specific implementation of SMT-LIB sorts.
class SortImplementation {
 public:
  virtual ~SortImplementation() {}
  virtual std::string ToString() const = 0;
  virtual bool Equals(const SortImplementation& rhs) const = 0;

 private:
  friend bool operator==(const SortImplementation& lhs,
                         const SortImplementation& rhs);
};

inline bool operator==(const SortImplementation& lhs,
                       const SortImplementation& rhs) {
  return lhs.Equals(rhs);
}

// Wrapper class for use by clients.  Handles reference counting and
// provides some useful methods.
class Sort {
 public:
  Sort() : sort_implementation_(nullptr) {}

  explicit Sort(std::shared_ptr<SortImplementation> sort_implementation)
      : sort_implementation_(std::move(sort_implementation)) {}

  bool IsNull() const { return sort_implementation_ == nullptr; }

  // Generates a string representation of this sort.
  std::string ToString() const {
    CHECK(!IsNull());
    return sort_implementation_->ToString();
  }

  // Returns a pointer to the implementation.
  const SortImplementation* GetImplementation() const {
    return sort_implementation_.get();
  }

 private:
  friend bool operator==(const Sort& lhs, const Sort& rhs);
  friend bool operator!=(const Sort& lhs, const Sort& rhs);

  // Pointer to the implementation class.
  std::shared_ptr<SortImplementation> sort_implementation_;
};

inline bool operator==(const Sort& lhs, const Sort& rhs) {
  if (lhs.GetImplementation() == rhs.GetImplementation()) return true;
  if (lhs.IsNull() || rhs.IsNull()) return false;
  return (*lhs.GetImplementation()) == (*rhs.GetImplementation());
}

inline bool operator!=(const Sort& lhs, const Sort& rhs) {
  return !(lhs == rhs);
}

// Abstract interface class for solver-specific implementation of SMT-LIB
// functions.
class FunctionImplementation {
 public:
  virtual ~FunctionImplementation() {}
  virtual std::string ToString() const = 0;
  virtual bool Equals(const FunctionImplementation& rhs) const = 0;

 private:
  friend bool operator==(const FunctionImplementation& lhs,
                         const FunctionImplementation& rhs);
};

inline bool operator==(const FunctionImplementation& lhs,
                       const FunctionImplementation& rhs) {
  return lhs.Equals(rhs);
}

// Wrapper class for use by clients.  Handles reference counting and
// provides some useful methods.
class Function {
 public:
  Function() :function_implementation_(nullptr) {}

  explicit Function(
      std::shared_ptr<FunctionImplementation> function_implementation)
      : function_implementation_(std::move(function_implementation)) {}

  bool IsNull() const { return function_implementation_ == nullptr; }

  // Generates a string representation of this function.
  std::string ToString() const {
    CHECK(!IsNull());
    return function_implementation_->ToString();
  }

  // Returns a pointer to the implementation.
  const FunctionImplementation* GetImplementation() const {
    return function_implementation_.get();
  }

 private:
  friend bool operator==(const Function& lhs, const Function& rhs);
  friend bool operator!=(const Function& lhs, const Function& rhs);

  // Pointer to the implementation class.
  std::shared_ptr<FunctionImplementation> function_implementation_;
};

inline bool operator==(const Function& lhs, const Function& rhs) {
  if (lhs.GetImplementation() == rhs.GetImplementation()) return true;
  if (lhs.IsNull() || rhs.IsNull()) return false;
  return (*lhs.GetImplementation()) == (*rhs.GetImplementation());
}

inline bool operator!=(const Function& lhs, const Function& rhs) {
  return !(lhs == rhs);
}

// Forward declaration needed in implementation class below.
class Term;

// Abstract interface class for solver-specific implementation of SMT-LIB terms.
// See comments for class Term for a description of the methods.
//
// TODO: Open question: should the getter methods in smt::Term use
// std::optional or absl::StatusOr instead of CHECK-failing when used
// incorrectly? Or should we provide both options?
class TermImplementation {
 public:
  virtual ~TermImplementation() {}
  virtual std::string ToString() const = 0;
  virtual unsigned NumChildren() const = 0;
  virtual Term operator[](unsigned index) const = 0;
  virtual bool Equals(const TermImplementation& rhs) const = 0;
  virtual bool IsBoolConstant() const = 0;
  virtual bool GetBoolConstant() const = 0;
  virtual bool IsIntegerConstant() const = 0;
  virtual absl::StatusOr<int64_t> IntegerConstantToInt64() const = 0;
  virtual absl::StatusOr<uint64_t> IntegerConstantToUint64() const = 0;
  virtual bool IsBVConstant() const = 0;
  virtual uint64_t BvConstantToUnsigned() const = 0;
  virtual std::string BvConstantToDecimalString() const = 0;
  virtual bool IsStringConstant() const = 0;
  virtual std::string GetStringConstant() const = 0;
  virtual unsigned GetBVSize() const = 0;
  virtual bool GetBit(unsigned index) const = 0;
  virtual Sort GetSort() const = 0;

 protected:
  // The number of bits in a byte.
  static constexpr size_t kBitsPerByte = 8;

 private:
  friend bool operator==(const TermImplementation& lhs,
                         const TermImplementation& rhs);
};

inline bool operator==(const TermImplementation& lhs,
                       const TermImplementation& rhs) {
  return lhs.Equals(rhs);
}

// Wrapper around TermImplementation* to handle reference counting and
// support useful methods.
class Term {
 public:
  Term() : term_implementation_(nullptr) {}

  explicit Term(std::shared_ptr<TermImplementation> term_implementation)
      : term_implementation_(std::move(term_implementation)) {}

  bool IsNull() const { return term_implementation_ == nullptr; }

  // Generates a string representation of this term.
  std::string ToString() const {
    CHECK(!IsNull());
    return term_implementation_->ToString();
  }

  // Returns a pointer to the implementation.
  const TermImplementation* GetImplementation() const {
    return term_implementation_.get();
  }

  // Returns the number of children for this term (e.g. the number of arguments
  // for a function application).
  unsigned NumChildren() const {
    CHECK(!IsNull());
    return term_implementation_->NumChildren();
  }

  // Returns the child indexed by index.  Calls error handler if index is out of
  // bounds.
  Term operator[](unsigned index) const {
    CHECK(!IsNull());
    return term_implementation_->operator[](index);
  }

  // Returns whether this term is the constant true or the constant false.
  bool IsBoolConstant() const {
    CHECK(!IsNull());
    return term_implementation_->IsBoolConstant();
  }

  // Gets the Boolean value from the Boolean constant true or false.  Calls
  // error handler if this term is not a Boolean constant.
  bool GetBoolConstant() const {
    CHECK(!IsNull());
    return term_implementation_->GetBoolConstant();
  }

  // Returns whether this term is an integer constant (a numeral).
  bool IsIntegerConstant() const {
    CHECK(!IsNull());
    return term_implementation_->IsIntegerConstant();
  }

  // Gets uint64 value from an integer constant.
  // Returns FAILED_PRECONDITION if Term is not an integer constant.
  // Returns OUT_OF_RANGE if value doesn't fit in an uint64.
  // May return other error codes.
  absl::StatusOr<uint64_t> IntegerConstantToUint64() const {
    CHECK(!IsNull());
    return term_implementation_->IntegerConstantToUint64();
  }

  // Gets int64 value from an integer constant.
  // Returns FAILED_PRECONDITION if Term is not an integer constant.
  // Returns OUT_OF_RANGE if value doesn't fit in an int64.
  // May return other error codes.
  absl::StatusOr<int64_t> IntegerConstantToInt64() const {
    CHECK(!IsNull());
    return term_implementation_->IntegerConstantToInt64();
  }

  // Returns whether this term is a bitvector constant.
  bool IsBVConstant() const {
    CHECK(!IsNull());
    return term_implementation_->IsBVConstant();
  }

  // Gets the unsigned value of a bitvector constant. Bitvector size must be
  // less than or equal to the size of an unsigned.  Calls error handler if not,
  // or if this term is not a bitvector constant.
  uint64_t BvConstantToUnsigned() const {
    CHECK(!IsNull());
    return term_implementation_->BvConstantToUnsigned();
  }

  // Gets a decimal string representation of a bitvector constant (unsigned).
  // Calls error handler if this term is not a bitvector constant.
  std::string BvConstantToDecimalString() const {
    CHECK(!IsNull());
    return term_implementation_->BvConstantToDecimalString();
  }

  // Returns whether this term is a string constant.
  bool IsStringConstant() const {
    CHECK(!IsNull());
    return term_implementation_->IsStringConstant();
  }

  // Gets the String value of a String constant.  Calls error handler if this
  // term is not a String constant.
  std::string GetStringConstant() const {
    CHECK(!IsNull());
    return term_implementation_->GetStringConstant();
  }

  // Gets the size (in bits) of a term of sort bitvector.  Calls error handler
  // if this term is not of bitvector type.
  unsigned GetBVSize() const {
    CHECK(!IsNull());
    return term_implementation_->GetBVSize();
  }

  // Gets the Boolean value of a bitvector constant at a particular index (where
  // 0 is the least significant bit).  Calls error handler if this term is not a
  // bitvector constant or if index is out of bounds.
  bool GetBit(unsigned index) const {
    CHECK(!IsNull());
    return term_implementation_->GetBit(index);
  }

  // Returns the Sort associated with this Term.  Check fails if Sort is null.
  Sort GetSort() const {
    CHECK(!IsNull());
    return term_implementation_->GetSort();
  }

 private:
  friend bool operator==(const Term& lhs, const Term& rhs);
  friend bool operator!=(const Term& lhs, const Term& rhs);

  // Pointer to the implementation class.
  std::shared_ptr<TermImplementation> term_implementation_;
};

inline bool operator==(const Term& lhs, const Term& rhs) {
  if (lhs.GetImplementation() == rhs.GetImplementation()) return true;
  if (lhs.IsNull() || rhs.IsNull()) return false;
  return (*lhs.GetImplementation()) == (*rhs.GetImplementation());
}

inline bool operator!=(const Term& lhs, const Term& rhs) {
  return !(lhs == rhs);
}

// An identifier is usually just a name.  However, SMT-LIB also allows
// identifiers to be indexed by a list of indexes, each of which is
// either a symbol (a string) or a numeral.  This class is used as a
// generic interface that supports both.
class Identifier {
 public:
  // Base class for identifier indexes.  Index can either be a symbol or a
  // numeral, each implemented by a different subclass.
  class Index {
   public:
    explicit Index(bool is_symbol) : is_symbol_(is_symbol) {}

    virtual ~Index() {}

    bool IsSymbol() const { return is_symbol_; }

    // Gets the symbol; only valid for SymbolIndex subclass.
    virtual const std::string& GetSymbol() const = 0;

    // Gets the numeral; only valid for SymbolIndex subclass.
    virtual unsigned GetNum() const = 0;

   private:
    // is_symbol_ is true iff this is a SymbolIndex object.
    const bool is_symbol_;
  };

  // Class representing symbolic indexes for SMT-LIB identifiers.
  class SymbolIndex : public Index {
   public:
    explicit SymbolIndex(absl::string_view symbol)
        : Index(true), symbol_(symbol) {}

    const std::string& GetSymbol() const final { return symbol_; }

    unsigned GetNum() const final {
      LOG(FATAL) << "Called GetNum on non-numeral Index object";
    }

   private:
    // The symbol for this index.
    const std::string symbol_;
  };

  // Class representing numeral indexes for SMT-LIB identifiers.
  class NumIndex : public Index {
   public:
    explicit NumIndex(unsigned num) : Index(false), num_(num) {}

    const std::string& GetSymbol() const final {
      LOG(FATAL) << "Called GetSymbol on non-symbol Index object";
    }

    unsigned GetNum() const final { return num_; }

   private:
    // The numeral for this index.
    const unsigned num_;
  };

  // This is not explicit so that clients can pass string literals to
  // SMTSolver API methods.
  Identifier(const char* symbol) : symbol_(symbol) {}  // NOLINT

  explicit Identifier(std::string symbol) : symbol_(std::move(symbol)) {}

  virtual ~Identifier() {}

  // Gets the symbol for this Identifier.
  const std::string& symbol() const { return symbol_; }

  // Gets the number of indexes for this Identifier (0 for none).
  virtual unsigned GetSize() const { return 0; }

  // Returns whether this is an indexed identifier.
  bool IsIndexed() const { return GetSize() != 0; }

  // Returns Index object at index if there is one (nullptr otherwise).
  virtual const Identifier::Index& GetIndex(unsigned index) const {
    LOG(FATAL) << "Called GetIndex on non-IndexedIdentifier";
  }

 private:
  // Symbol for this identifier.
  const std::string symbol_;
};

// Subclass of Identifier for indexed identifiers.
class IndexedIdentifier : public Identifier {
 public:
  explicit IndexedIdentifier(std::string symbol) : Identifier(symbol) {}

  // Add a numeric index to this identifier.
  void AddNumIndex(unsigned num) { index_vec_.emplace_back(new NumIndex(num)); }

  // Add a symbolic index to this identifier.
  void AddSymbolIndex(absl::string_view symbol) {
    index_vec_.emplace_back(new SymbolIndex(symbol));
  }

  unsigned GetSize() const final { return index_vec_.size(); }

  const Index& GetIndex(unsigned position) const final {
    CHECK_LT(position, index_vec_.size());
    return *(index_vec_[position].get());
  }

 private:
  // This vector contains all indices attached to the identifier.
  std::vector<std::unique_ptr<Index>> index_vec_;
};

}  // namespace smt

#endif  // SRC_SMT_SMT_TERM_H_
