//
// Copyright (c) 2012, Michael Goerner
// Copyright (c) 2012-2013, Dominik Moritz
//
// This file is part of Clasp. See http://www.cs.uni-potsdam.de/clasp/
//
// Clasp is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2 of the License, or
// (at your option) any later version.
//
// Clasp is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with Clasp; if not, write to the Free Software
// Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA  02110-1301  USA
//
#pragma once

#ifdef _MSC_VER
#pragma warning (disable : 4200) // nonstandard extension used : zero-sized array
#pragma once
#endif

#include <tr1/unordered_map>
#include <algorithm>
#include <clasp/constraint.h>
#include <clasp/weight_constraint.h>
#include <clasp/solver.h>
#include <clasp/clause.h>
#include <clasp/util/ite/FEnv.h>

// from boost functional
template <class T>
inline void hash_combine(std::size_t & seed, const T & v)
{
	std::tr1::hash<T> hasher;
	seed ^= hasher(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
}

namespace std
{
namespace tr1
{
template<typename S, typename T> struct hash<pair<S, T> >
{
	inline size_t operator()(const pair<S, T> & v) const
	{
		size_t seed = 0;
		::hash_combine(seed, v.first);
		::hash_combine(seed, v.second);
		return seed;
	}
};
}} // namespace

namespace Clasp {

typedef std::pair<uint32, wsum_t> BDDKey;
typedef std::tr1::unordered_map<BDDKey, Formula> BDDCache;

//! Class implementing learnt Pseudo-Boolean constraints
/*!
 * \ingroup constraint
 * This class represents a constraint of type w1*x1 ... wn*xn >= B,
 * where each xi is a literal and B and each wi are strictly positive integers.
 */
class PBConstraint : public LearntConstraint {
public:
	/*!
	 * The constructor does not take a number of (weighted) literals and a lower bound, because
	 * PB constraints are created from conflicts
	 */
	PBConstraint(Solver& s, const Literal, const Antecedent&, bool conflict= false);

	/*!
	 * Directly construct PBConstraints
	 */
	PBConstraint(Solver&, WeightLitVec lits, wsum_t bound);

	ConstraintType type() const { return Constraint_t::learnt_pb; }

	//! constraint interface
	Constraint* cloneAttach(Solver&) { return 0; }

	//! ignore simplify for now
	bool simplify(Solver&, bool = false){ return false; }

	//uint32 estimateComplexity(const Solver& s) const { return 1; }

	void destroy(Solver*, bool);

	PropResult propagate(Solver& s, Literal p, uint32& data);
	void reason(Solver&, Literal p, LitVec& lits);
	void undoLevel(Solver& s);

	bool minimize(Solver& s, Literal p, CCMinRecursive* r);

	//! Returns the literal at position i
	Literal lit(uint32 i) const {
		return lits_[i].first;
	}
	//! Returns the weight of the i'th literal
	weight_t weight(uint32 i) const {
		return lits_[i].second;
	}
	weight_t weight(Literal p) const {
		for (LitVec::size_type i= 0; i != lits_.size(); ++i) {
			if (lits_[i].first == p){
				return lits_[i].second;
			}
		};
		return 0;
	}

	//! Returns the number of literals in this constraint.
	uint32   size() const { return lits_.size(); }

	//! Returns the lower bound
	wsum_t   bound() const { return bound_; }

	//! Returns how much the constraint is oversatisfied if all undecided literals were mapped to true
	wsum_t   slack() const { return slack_; }

	// learnt constraint interface
	/*!
	 * Shall return true if this constraint can't be deleted because it
	 * currently implies one ore more literals and false otherwise.
	 */
	bool locked(const Solver& s) const;

	//! Shall return 0 if either !t.inSet(type()) or this constraint is satisfied w.r.t the current assignment.
	/*!
	 * If this constraint is currently not satisfied and t.inSet(type()), shall return type()
	 * and freeLits shall contain all currently unassigned literals of this constraint.
	 */
	uint32 isOpen(const Solver& s, const TypeSet& t, LitVec& freeLits);

	//! Add *this to learnt constraints of solver and integrate into current search
	bool integrate(Solver& s);

	//! Eliminate variable from constraint using the reason of l being true
	/*! assert this->integrate() has not been called yet */
	void varElimination(Solver& s, Literal l);

	//! Weaken constraint to clause of false literals (and p if it is specified)
	void weaken(Solver& s, Literal p= Literal(0, true));

	//! Multiply constraint with given factor
	bool multiply(weight_t);

	//! Get the clauses that represent this PBC using BDDs
	Formula extractClauses() const;

private:
	PBConstraint(Solver& s, const PBConstraint& other);
	~PBConstraint() {}

	//! Returns the literal at position i
	inline Literal&  lit(uint32 i) { return lits_[i].first; }

	//! Returns the weight of the i'th literal
	inline weight_t& weight(uint32 i) { return lits_[i].second; }

	wsum_t canonicalize(Solver& s);

	// Represents a literal on the undo stack.
	// idx()        returns the index of the literal.
	// Note: Only 31-bits are used for undo info.
	// The remaining bit is used as a flag for marking processed literals.
	struct UndoInfo {
		explicit UndoInfo(uint32 d = 0) : data(d) {}
		uint32 idx() const { return data >> 1; }
		uint32 data;
	};

	//! Is literal idx contained as reason lit in the undo stack?
	bool litSeen(uint32 idx) const {
		assert(undo_ != 0);
		return (undo_[idx].data & 1) != 0;
	}

	//! Mark/unmark literal idx.
	void toggleLitSeen(uint32 idx) {
		assert(undo_ != 0);
		undo_[idx].data ^= 1;
	}

	//! Add watch for idx'th literal of c to the solver.
	void addWatch(Solver& s, uint32 idx);

	UndoInfo undoTop() const {
		assert(up_ > 0 && undo_ != 0);
		return undo_[up_-1];
	}

	Formula extractClauses(uint32 size, wsum_t sum, wsum_t material_left) const;

	//! Returns the decision level of the last assigned literal
	//! or 0 if no literal was assigned yet.
	inline uint32	highestUndoLevel(Solver&) const;

	//! Updates slack_ and adds an undo watch to the solver if necessary.
	//! Then adds the literal at position idx to the reason set (and the undo stack).
	void updateConstraint(Solver& s, uint32 idx);

	//! Returns the index of next literal to look at during propagation.
	uint32   getPIndex() const  { return pidx_; }
	void     setPIndex(uint32 n){ pidx_ = n; }

	WeightLitVec  lits_;   // literals of constraint
	wsum_t   bound_;       // lower bound
	wsum_t   slack_;       // slack of PB constraint
	uint32   pidx_;        // next literal index to look at in propagation
	uint32   up_;          // undo position; undo_[undoStart(), up_] is the undo stack
	uint32   firstImpl_;   // decision level of first implied variable

	// this is allocated only on integrate()
	UndoInfo* undo_;     // undo stack + seen flag for each literal

	//internals.. needed in integrate
	struct SmallerLevel {
		public:
			SmallerLevel(const Solver& s, WeightLitVec& wlv) : solver_(s), wlv_(wlv) {}
			bool operator()(const PBConstraint::UndoInfo& p1, const PBConstraint::UndoInfo& p2) const {
				assert(solver_.value(wlv_[p1.idx()].first.var()) != value_free && solver_.value(wlv_[p2.idx()].first.var()) != value_free);
				return solver_.level(wlv_[p1.idx()].first.var()) < solver_.level(wlv_[p2.idx()].first.var());
			}
		private:
			SmallerLevel& operator=(const SmallerLevel&);
			const Solver& solver_;
			const WeightLitVec& wlv_;
	};

	// used to cache BDDs
	mutable BDDCache* memo_;
};

/*
Literal buildBDD(const PBConstraint& c, int size, int64 sum, int64 material_left, std::tr1::unordered_map<std::pair<int,int64>,Literal>& memo, int max_cost)
{
	int64 lower_limit = (c.lo == Int_MIN) ? Int_MIN : c.lo - sum;
	int64 upper_limit = (c.hi == Int_MAX) ? Int_MAX : c.hi - sum;

	if (lower_limit <= 0 && upper_limit >= material_left)
		return true;
	else if (lower_limit > material_left || upper_limit < 0)
		return false;
	else if (FEnv::topSize() > max_cost)
		return _undef_;     // (mycket elegant!)

	std::pair<int,int64>   key = Pair_new(size, lower_limit);
	Formula         ret;

	if (!memo.peek(key, ret)){
		assert(size != 0);
		size--;
		material_left -= c(size);
		int64 hi_sum = sign(c[size]) ? sum : sum + c(size);
		int64 lo_sum = sign(c[size]) ? sum + c(size) : sum;
		Literal hi = buildBDD(c, size, hi_sum, material_left, memo, max_cost);
		if (hi == _undef_) return _undef_;
		Literal lo = buildBDD(c, size, lo_sum, material_left, memo, max_cost);
		if (lo == _undef_) return _undef_;
		ret = ITE(var(var(c[size])), hi, lo);
		memo.set(key, ret);
	}
	return ret;
}

Formula convertToBdd(const Linear& c, int max_cost)
{
	std::tr1::unordered_map<Pair<int,int64>, Formula> memo;

	int64 sum = 0;
	for (int j = 0; j < c.size; j++)
		sum += c(j);

	FEnv::push();
	Literal ret = buildBDD(c, c.size, 0, sum, memo, max_cost);
	if (ret == _undef_)
		FEnv::pop();
	else{
		if (opt_verbosity >= 1)
			reportf("BDD-cost:%5d\n", FEnv::topSize());
		FEnv::keep();
	}
	return ret;
}
*/

} //namespace Clasp
