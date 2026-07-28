/**
 * @file Constraint.cpp
 * @brief Concrete implementations of constraint evaluation routines.
 */

#include "Constraint.h"
#include "AbstractValue.h"
#include <algorithm>
#include <cmath>
#include <cassert>
#include <iostream>

// --- Base Constraint ---
Constraint::Constraint(std::string name) : def(std::move(name)) {}

// --- InitializationConstraint (v = c) ---
InitializationConstraint::InitializationConstraint(std::string var, int c)
    : Constraint(std::move(var)), constant(c) {}

bool InitializationConstraint::eval(AbstractState& A) {
    IV old_val = std::get<IV>(A[def]);

    std::vector<int> vals = {constant};
    std::get<IV>(A[def]).addConstant(vals);
    return old_val != std::get<IV>(A[def]); // Leverages your custom equality operator!
}

// --- PhiConstraint (v0 = phi(v1, v2, ...)) ---
PhiConstraint::PhiConstraint(std::string var, std::vector<std::string> ops)
    : Constraint(std::move(var)), operands(std::move(ops)) {}

bool PhiConstraint::eval(AbstractState& A) {
    if (std::holds_alternative<BV>(A[def])) {
        BV old_val = std::get<BV>(A[def]);
        BV accumulated_join; // Starts at bottom element
    
        for (const auto &op : operands) {
          accumulated_join.join(std::get<BV>(A[op]));
        }
    
        std::get<BV>(A[def]) = accumulated_join;
        return old_val != accumulated_join;
    } else {
        IV old_val = std::get<IV>(A[def]);
        IV accumulated_join; // Starts at bottom element
    
        for (const auto &op : operands) {
          accumulated_join.join(std::get<IV>(A[op]));
        }
    
        std::get<IV>(A[def]) = accumulated_join;
        return old_val != accumulated_join;
    }
}

// --- IntersectionConstraint (v0 = v1 intersection [low, up]) ---
IntersectionConstraint::IntersectionConstraint(std::string dest,
                                               std::string src,
                                               IntersectionBound low,
                                               IntersectionBound up)
    : Constraint(std::move(dest)), operand(std::move(src)),
      lower_bound(std::move(low)), upper_bound(std::move(up)) {}

Bound
IntersectionConstraint::resolveBound(const IntersectionBound &b,
                                     const bool isLower,
                                     const AbstractState &) const {

  if (std::holds_alternative<Bound>(b))
    return std::get<Bound>(b);

  // Growth phase:
  // ignore symbolic references
  Bound result;

  if (isLower)
    result = Bound::minusInfinity();
  else
    result = Bound::plusInfinity();

  return result;
}

IntersectionConstraint
IntersectionConstraint::resolveFutures(const AbstractState &state) const {
    auto resolve = [&](const IntersectionBound &bound,
      bool isLower) -> IntersectionBound {
    if (std::holds_alternative<Bound>(bound))
      return bound;

    const Future &future = std::get<Future>(bound);

    auto it = state.find(future.target_variable);
    assert(it != state.end());

    IV futureVariable = std::get<IV>(it->second);

    Bound result =
      isLower ? futureVariable.getLower()
      : futureVariable.getUpper();

    if (result.isConstant())
      result.setConstant(result.getConstant() + future.offset);

    return result;
  };

  return IntersectionConstraint(
      def,
      operand,
      resolve(lower_bound, true),
      resolve(upper_bound, false));
}

bool IntersectionConstraint::eval(AbstractState &A) {

    IV oldValue = std::get<IV>(A[def]);
    const IV& src = std::get<IV>(A[operand]);

  // Bottom stays bottom.
  if (src.getKind() == IV::Kind::Set && src.getValues().empty()) {
    return false;
  }

  auto low = resolveBound(lower_bound, true, A);
  auto up = resolveBound(upper_bound, false, A);

  // AnalyzedValue result;

  // Source is a finite set.
  if (src.getKind() == IV::Kind::Set) {

    std::vector<int> vals;
    for (int v : src.getValues()) {
      bool keep = true;
      if (low.isConstant())
        keep &= (v >= low.getConstant());
      if (up.isConstant())
        keep &= (v <= up.getConstant());
      if (keep)
        vals.emplace_back(v);
    }

    if (!vals.empty())
      std::get<IV>(A[def]).addConstant(vals);
  }

  // Source is already an interval.
  else {
    auto lower = src.getLower();
    auto upper = src.getUpper();

    // max(lower, low)
    if (low.isConstant()) {
      if (lower.isMinusInfinity())
        lower = low;
      else if (lower.isConstant())
        lower.setConstant(std::max(lower.getConstant(), low.getConstant()));
    }

    // min(upper, up)
    if (up.isConstant()) {
      if (upper.isPlusInfinity())
        upper = up;
      else if (upper.isConstant())
        upper.setConstant(std::min(upper.getConstant(), up.getConstant()));
    }

    // Empty interval?
    if (lower.isConstant() &&
        upper.isConstant() &&
        lower.getConstant() > upper.getConstant()) {
      // Leave result as bottom.
    } else {
      std::get<IV>(A[def]).setAsInterval(lower, upper, src.getStride());
    }
  }

    return oldValue != std::get<IV>(A[def]);
}

// --- ArithmeticConstraint Base ---
ArithmeticConstraint::ArithmeticConstraint(std::string dest, std::string lhs,
                                           std::string rhs)
    : Constraint(std::move(dest)), op1(std::move(lhs)), op2(std::move(rhs)) {}

bool AddConstraint::eval(AbstractState& A) {
    IV old_val = std::get<IV>(A[def]);
    
    const IV &lhs = std::get<IV>(A[op1]);
    const IV &rhs = std::get<IV>(A[op2]);
    
    // AnalyzedValue result; // Starts at bottom (empty set)

    // Exact evaluation: finite set × finite set
    if (lhs.getKind() == IV::Kind::Set &&
        rhs.getKind() == IV::Kind::Set) {

        // Bottom propagates.
        if (lhs.getValues().empty() || rhs.getValues().empty()) {
            std::get<IV>(A[def]).setAsBottom();
            return old_val != std::get<IV>(A[def]);
        }

        std::vector<int> consts;

        for (int l : lhs.getValues()) {
            for (int r : rhs.getValues()) {
                consts.emplace_back(l + r);
            }
        }

        std::get<IV>(A[def]).addConstant(consts);

    return old_val != std::get<IV>(A[def]);
  }

  // Otherwise treat every operand as a strided interval.
  auto getLower = [](const IV &v) -> Bound {
    if (v.getKind() == IV::Kind::Set) {
      return Bound::constant(*v.getValues().begin());
    }
    return v.getLower();
  };

  auto getUpper = [](const IV &v) -> Bound {
    if (v.getKind() == IV::Kind::Set) {
      if (v.getValues().empty())
        return Bound::constant(*v.getValues().begin());
              
      return Bound::constant(*v.getValues().rbegin());
    }
    return v.getUpper();
  };

  auto addLower =
      [](const Bound &a,
         const Bound &b) -> Bound {

    if (a.isMinusInfinity() ||
        b.isMinusInfinity())
      return Bound::minusInfinity();

    return Bound::constant(a.getConstant() + b.getConstant());
  };

  auto addUpper =
      [](const Bound &a,
         const Bound &b) -> Bound {

    if (a.isPlusInfinity() ||
        b.isPlusInfinity())
      return Bound::plusInfinity();

    return Bound::constant(a.getConstant() + b.getConstant());
  };

  auto lower = addLower(getLower(lhs), getLower(rhs));
  auto upper = addUpper(getUpper(lhs), getUpper(rhs));

  unsigned s1 =
      (lhs.getKind() == IV::Kind::StridedInterval)
          ? lhs.getStride()
          : 1;

  unsigned s2 =
      (rhs.getKind() == IV::Kind::StridedInterval)
          ? rhs.getStride()
          : 1;

  std::get<IV>(A[def]).setAsInterval(lower, upper, std::gcd(s1, s2));

  return old_val != std::get<IV>(A[def]);
}

bool SubConstraint::eval(AbstractState& A) {
  IV av;

  std::vector<int> values;
  for(int value : std::get<IV>(A[op2]).getValues()) values.push_back(value*(-1));
  av.addConstant(values);
  A[op2] = std::move(av);

  AddConstraint add(def,op1, op2);
  return add.eval(A);
}

bool MultiplyConstraint::eval(AbstractState &A)
{
  IV old = std::get<IV>(A[this->def]);

  IV lhs = std::get<IV>(A[this->op1]);
  IV rhs = std::get<IV>(A[this->op2]);

  IV result;

  if(lhs.getKind() == IV::Kind::Set && rhs.getKind() == IV::Kind::Set)
  {
    if (lhs.getValues().empty() || rhs.getValues().empty()) {
      std::get<IV>(A[def]) = result;
      return old != result;
    }

    std::vector<int> consts;
    for (int l : lhs.getValues()) {
        for (int r : rhs.getValues()) {
            consts.emplace_back(l * r);
        }
    }
    result.addConstant(consts);
  } else {

    // Otherwise treat every operand as a strided interval.
    auto getLower = [](const IV &v) -> Bound {
      if (v.getKind() == IV::Kind::Set) {
        return Bound::constant(*v.getValues().begin());
      }
      return v.getLower();
    };

    auto getUpper = [](const IV &v) -> Bound {
      if (v.getKind() == IV::Kind::Set) {
        if (v.getValues().empty())
          return Bound::constant(*v.getValues().begin());
                
        return Bound::constant(*v.getValues().rbegin());
      }
      return v.getUpper();
    };

    auto multiplyBounds = [](const Bound &x, const Bound &y) {
      Bound l = std::min(x,y);
      Bound h = std::max(x,y);

      if (l.isMinusInfinity()) {
        if (h.isMinusInfinity()) {        // -inf * -inf = +inf
          return Bound::plusInfinity();
        } else if (h.isConstant()) {
          if (h.getConstant() < 0)        // -inf * -C = +inf
            return Bound::plusInfinity();
          else if (h.getConstant() == 0)  // -inf * 0 = 0
            return Bound::constant(0);
          else                            // -inf * +C = -inf
            return Bound::minusInfinity();
        } else {                          // -inf * +inf = -inf
          return Bound::minusInfinity();
        }
      } else if (l.isConstant()) {
        if (h.isConstant()) {             // C * C
          return Bound::constant(
            l.getConstant() * h.getConstant()
          );
        } else {
          if (l.getConstant() < 0)        // -C * +inf = -inf
            return Bound::minusInfinity();
          else if (l.getConstant() == 0)  // 0 * +inf = 0
            return Bound::constant(0);
          else                            // C * +inf = +inf
            return Bound::plusInfinity();
        }
      } else {                            // +inf * +inf = +inf
        return Bound::plusInfinity();
      }
    };

    Bound l1 = getLower(lhs);
    Bound l2 = getLower(rhs);
    Bound u1 = getUpper(lhs);
    Bound u2 = getUpper(rhs);

    Bound p1 = multiplyBounds(l1,l2);
    Bound p2 = multiplyBounds(l1,u2);
    Bound p3 = multiplyBounds(u1,l2);
    Bound p4 = multiplyBounds(u1,u2);

    Bound min = std::min({p1, p2, p3, p4});
    Bound max = std::max({p1, p2, p3, p4});

    result.setAsInterval(min,max,1); // FIXME: Interval stride
}

  A[this->def] = result;
  return old != result;
}

bool LinearConstraint::eval(AbstractState &A)
{
  IV old = std::get<IV>(A[this->def]);
  IV src = std::get<IV>(A[this->operand]);

  IV result;

  if(src.getKind() == IV::Kind::Set)
  {
    std::vector<int> consts;
    for (int v : src.getValues()) {
      consts.emplace_back((a * v) + b);
    }
    result.addConstant(consts);
  }else{
    Bound srcLower = src.getLower();
    Bound srcUpper = src.getUpper();
    
    Bound lower, upper;
    
    if (this->a == 0)
        result.setAsInterval(Bound::constant(b), Bound::constant(b), src.getStride());
    else if (srcLower.isConstant() && srcUpper.isConstant()) {
      int k1 = (this->a * srcLower.getConstant() + this->b);
      int ku = (this->a * srcUpper.getConstant() + this->b);
      int min = std::min(k1,ku);
      int max = std::max(k1,ku);
      result.setAsInterval(Bound::constant(min), Bound::constant(max), src.getStride());
    } else {
      if (srcLower.isMinusInfinity() && srcUpper.isPlusInfinity()) {
        result.setAsInterval(Bound::minusInfinity(), Bound::plusInfinity(), 1);
      } else if (srcLower.isMinusInfinity()) {
        int k = (this->a * srcUpper.getConstant() + this->b);
        if (this->a > 0)
          result.setAsInterval(Bound::minusInfinity(), Bound::constant(k), 1);
        else
          result.setAsInterval(Bound::constant(k), Bound::plusInfinity(), 1);
      } else {
        int k = (this->a * srcLower.getConstant() + this->b);
        if (this->a > 0)
          result.setAsInterval(Bound::constant(k), Bound::plusInfinity(), 1);
        else
          result.setAsInterval(Bound::minusInfinity(), Bound::constant(k), 1);
      }
    }
  }

  A[this->def] = result;
  return old != result;
}

// --- InitializationConstraint (v = c) ---
InitializationBoolConstraint::InitializationBoolConstraint(std::string var, bool c)
    : Constraint(std::move(var)), constant(c) {}

bool InitializationBoolConstraint::eval(AbstractState& A) {
    BV old_val = std::get<BV>(A[def]);

    std::vector<bool> vals = {constant};
    std::get<BV>(A[def]).addConstant(vals);
    return old_val != std::get<BV>(A[def]); // Leverages your custom equality operator!
}

// --- EqualConstraint (v0 = v1 == v2) ---
bool EqualConstraint::eval(AbstractState& A) {
  // Emplace a BoolValue if def is undefined in the Abstract State
  A.try_emplace(def, BV());

  BV old_val = std::get<BV>(A[def]);
  const IV &lhs = std::get<IV>(A[op1]);
  const IV &rhs = std::get<IV>(A[op2]);


  std::vector<bool> vals;
  if (lhs.getKind() == IV::Kind::Set && rhs.getKind() == IV::Kind::Set) {
    std::set<int> aux;

    // If the intersection is not empty, then v1 == v2 can be true
    std::set_intersection(lhs.getValues().begin(), lhs.getValues().end(),
                  rhs.getValues().begin(), rhs.getValues().end(),
                  std::inserter(aux, aux.begin()));

    if (!aux.empty()) vals.push_back(true);

    aux.clear();
    // If the difference is not empty, then v1 == v2 can be false
    std::set_difference(lhs.getValues().begin(), lhs.getValues().end(),
                  rhs.getValues().begin(), rhs.getValues().end(),
                  std::inserter(aux, aux.begin()));
    
    if (!aux.empty()) vals.push_back(false);
  } else if (lhs == rhs) {
    vals.push_back(true);
    if (lhs.getLower() != lhs.getUpper())
      vals.push_back(false);
  } else if (lhs < rhs || lhs > rhs) {
    vals.push_back(false);
  } else {
    vals.push_back(true);
    vals.push_back(false);
  }
  std::get<BV>(A[def]).addConstant(vals);
  return old_val != std::get<BV>(A[def]);
}

// --- LogicalAndConstraint (v0 = v1 && v2) ---
bool LogicalAndConstraint::eval(AbstractState& A) {
  // Emplace a BoolValue if def is undefined in the Abstract State
  A.try_emplace(def, BV());
  
  BV old_val = std::get<BV>(A[def]);
  const BV &lhs = std::get<BV>(A[op1]);
  const BV &rhs = std::get<BV>(A[op2]);

  std::vector<bool> vals;

  // If v1 or v2 can be false, then v0 can be false
  if (lhs.getValues().count(false) || rhs.getValues().count(false))
    vals.push_back(false);
  
  // If v1 and v2 can be true, then v0 can be true
  if (lhs.getValues().count(true) && rhs.getValues().count(true))
    vals.push_back(true);

  std::get<BV>(A[def]).addConstant(vals);

  return old_val != std::get<BV>(A[def]);
}