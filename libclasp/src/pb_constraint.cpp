//
// Copyright (c) 2006-2010, Benjamin Kaufmann
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

#include <clasp/solver.h>
#include <clasp/pb_constraint.h>
#include <clasp/util/ite/Hardware.h>
#include <clasp/util/streamhelper.h>
#include <iostream>

#include <math.h>

namespace Clasp {

PBConstraint::PBConstraint(Solver& s, const Literal p, const Antecedent& ant, bool conflict):
bound_(1), slack_(0), pidx_(0), up_(0), undo_(0)
{
	buildPBConstraint(*this, s, p, ant, conflict);
}

PBConstraint::PBConstraint(WeightLitVec lits, wsum_t bound, wsum_t slack):
lits_(lits), bound_(bound), slack_(slack), pidx_(0), up_(0), undo_(0) {}

PBConstraint::PBConstraint(wsum_t bound, wsum_t slack):
bound_(bound), slack_(slack), pidx_(0), up_(0), undo_(0) {}

void PBConstraint::destroy(Solver* s, bool detach) {
	if (this->undo_) {
		if (s && detach) {
			for (WeightLitVec::const_iterator it = lits_.begin(), end = lits_.end(); it != end; ++it) {
				s->removeWatch(~it->first, this);
			}
			for (uint32 i = 0, dl = 0; i != up_; ++i) {
				uint32 idx= undo_[i].idx();
				if (s->level(lit(idx).var()) > dl ){
					dl= s->level(lit(idx).var());
					s->removeUndoWatch(dl, this);
				}
			}
		}
		delete [] undo_;
	}
	void* mem    = static_cast<Constraint*>(this);
	this->~PBConstraint();
	::operator delete(mem);
}

void PBConstraint::buildPBConstraint(PBConstraint& pbc, Solver& s, const Literal p, const Antecedent& ant, bool conflict) {
	const bool generic= (ant.type() == Antecedent::generic_constraint);
	WeightConstraint* wc;

	if( generic && ant.constraint()->type() == Constraint_t::learnt_pb){
		PBConstraint* ant_pbc= static_cast<PBConstraint*>(ant.constraint());

		pbc.bound_= ant_pbc->bound_;
		pbc.slack_= ant_pbc->slack_;

		for (uint32 i = 0; i != ant_pbc->size(); ++i) {
			Literal l= ant_pbc->lit(i);

			if (s.value(l.var()) == value_free || s.level(l.var()) != 0 || l == p){
				pbc.lits_.push_back(ant_pbc->lits_[i]);
			}
			else if (s.isTrue(l)){
				pbc.bound_-= ant_pbc->weight(i);
			}
			else if (s.isFalse(l) && !ant_pbc->litSeen(i)){
				pbc.slack_-= ant_pbc->weight(i);
			}
		}
		if (conflict){
			// this is a conflicting constraint but hasn't updated its slack!
			pbc.slack_-= pbc.weight(p);
		}
	}
	else if ( generic && (wc= dynamic_cast<WeightConstraint*>(ant.constraint())) != 0 ){
		wc->extractActivePB(s, pbc.lits_, pbc.bound_, pbc.slack_, p);

		if (conflict){
			// this is a conflicting constraint, but hasn't updated its slack!
			pbc.slack_-= pbc.weight(p);
		}
	}
	else {
		// This could be a clause, or about anything else...
		// Let's just use the reason it provides and build a PB constraint from that
		LitVec reasons;
		ant.reason(s, p, reasons);

		pbc.slack_= -1;
		pbc.lits_.reserve(reasons.size()+1);
		pbc.lits_.push_back(WeightLiteral(p, 1));
		for(LitVec::size_type i= 0; i != reasons.size(); ++i){
			pbc.lits_.push_back(WeightLiteral(~reasons[i],1));
			if(s.isTrue(pbc.lit(i))) ++pbc.slack_;
		}
	}
}

void PBConstraint::reset()
{
	bound_ = 1;
	slack_ = 0;
	pidx_ = 0;
	up_ = 0;
	undo_ = 0;
	lits_.clear();
}

bool PBConstraint::integrate(Solver& s) {
	assert(up_ == 0 && undo_ == 0);
	// 1. init watches & slack
	// assume level 0 but remember all currently
	// false literals to be propagated in the next step
	uint32 todo= 0;
	uint32 n   = getPIndex();
	slack_     = -bound_;
	undo_      = new UndoInfo[lits_.size()];
	memset(undo_, 0, sizeof(UndoInfo)*lits_.size() );

	for (LitVec::size_type i= 0; i != lits_.size(); ++i){
		slack_+= lits_[i].second;
		addWatch(s, i);
		if (s.isFalse(lit(i))) {
			undo_[todo++]= UndoInfo(i<<1);
		}
		s.assign_.requestData(lit(i).var()+1);
	}
	s.addLearnt(this, lits_.size());

	// 2. propagate false literals in correct level-order
	std::stable_sort(undo_, undo_+todo, SmallerLevel(s, this->lits_));
	// this didn't necessarily sort them in the way, the solver would
	// propagate them, but it's still sound

	firstImpl_= UINT32_MAX;
	for (uint32 end= size(), lastDL= 0, thisDL= 0;; ++up_) {
		for (; n != end && weight(n) > slack_; ++n) {
			// constraint is unit on thisDL
			if (!litSeen(n)) {
				firstImpl_= std::min(thisDL, firstImpl_);
				// NOTE: forcing lit(idx) might go back to a level >= thisDL
				if (!s.force(lit(n), thisDL, this, up_)) {
					return false;
				}
			}
		}
		// force might have undone any further false literals
		if (up_ == todo || !s.isFalse(lit(undo_[up_].idx())))
			break;
		uint32 idx = undo_[up_].idx();
		Var    var = lit(idx).var();
		thisDL     = s.level(var);
		if (thisDL!= lastDL) {
			s.addUndoWatch(lastDL= thisDL, this);
		}
		assert(!litSeen(idx));
		slack_ -= weight(idx);
		toggleLitSeen(idx);
	}
	setPIndex(n);
	return true;
}

void PBConstraint::varElimination(Solver& s, Literal l){
	assert( undo_ == 0 && "the constraint is not integrated into a solver yet");
	assert( weight(~l) > 0 && "can't eliminate non-existing literal");
	assert( slack_ < 0 && "the constraint should be violated");

#define STATIC_VAR_ELIMINATION 1
#if STATIC_VAR_ELIMINATION
	static PBConstraint eliminator;
	eliminator.reset();
	buildPBConstraint(eliminator, s, l, s.reason(l));
#else
	PBConstraint eliminator(s, l, s.reason(l));
#endif

	weight_t mel= eliminator.weight(l);
	weight_t mag= weight(~l);
	weight_t mgcd= gcd(mel, mag);

	mel= mel/mgcd;
	mag= mag/mgcd;

	if ( (bound_ > static_cast<wsum_t>(UINT64_MAX / 4)/mel )        ||
		 (slack_ < (std::numeric_limits<wsum_t>::min() / mel) / 2)  ||
		 (static_cast<wsum_t>(lits_[0].second)*mel > static_cast<wsum_t>(UINT32_MAX / 4) )){
		// we can't guarantee that the added values do not overflow!
		// this is a really crude version of overflow handling
		weaken(s);
		mag= 1;
		mel= eliminator.weight(l);
	}
	if ((eliminator.bound_ > static_cast<wsum_t>(UINT64_MAX / 4)/mag )  ||
		(slack_ > (std::numeric_limits<wsum_t>::max() / mag) / 2)       ||
		(static_cast<wsum_t>(eliminator.lits_[0].second)*mag > static_cast<wsum_t>(UINT32_MAX / 4) )){
		eliminator.weaken(s,l);
		mel= 1;
		mag= weight(~l);
	}

	// TODO: From thesis: "Checks if the sum of the slacks is non-negative and applies weakening if it is not"
	if (mag*eliminator.slack_ + mel*slack_ >= 0 ){
		eliminator.weaken(s,l);
		mel= 1;
		mag= weight(~l);
	}

	bool mult= multiply(mel);
	assert( mult );
	mult= eliminator.multiply(mag);
	assert( mult );

	// this might be overestimated and is adjusted via canonicalize
	slack_+= eliminator.slack_;

	bound_+= eliminator.bound_;

	// add up literals and adjust slack as needed
	lits_.insert(lits_.end(), eliminator.lits_.begin(), eliminator.lits_.end());
	slack_-= canonicalize(s);
	assert( slack_ < 0 && "the constraint should be violated");
}

bool PBConstraint::multiply(weight_t x){
	if (x == 1)
		return true;

	//check for overflow
#ifndef NDEBUG
	if((bound_ > static_cast<wsum_t>(UINT64_MAX>>1)/x)                                 ||
	   (static_cast<wsum_t>(lits_[0].second)*x > static_cast<wsum_t>(UINT32_MAX >> 1)) ||
	   (slack_ > 0 && slack_ > std::numeric_limits<wsum_t>::max()/x)                   ||
	   (slack_ < 0 && slack_ < std::numeric_limits<wsum_t>::min()/x) ){
		return false;
	}
#endif

	for(LitVec::size_type i= 0; i != lits_.size(); ++i){
		lits_[i].second*= x;
	}
	slack_ *= x;
	bound_ *= x;

	return true;
}

bool PBConstraint::isClause() const
{
	// 1a + 1b + 1c >= 1 is [a,b,c]
	if (bound() <= 1)
		return true;

	// 3a + 1b + 1c >= 3 is [a]
	if (weight(0) == bound()){
		wsum_t sum = 0;
		LitVec::size_type i = 1;
		for (;i < size(); ++i) {
			sum += weight(i);
			if (sum >= bound())
				break;
		}
		if (i == size()) {
			//std::cout << *this << std::endl;
			return true;
		}
	}

	return false;
}

weight_t PBConstraint::calculateSlack(const Solver &s) const
{
	weight_t slack = 0;
	for (LitVec::size_type i= 0; i != lits_.size(); ++i){
		if (s.isFalse(lits_[i].first))
			continue;
		slack += lits_[i].second;
	}
	slack -= bound_;
	return slack;
}

void PBConstraint::weaken(Solver& s, Literal p){
	assert( weight(p) > 0 || p == Literal(0, true) );
	assert( undo_ == 0 && "this should not be integrated yet");
	WeightLitVec tmp;
	for (LitVec::size_type i= 0; i != lits_.size(); ++i){
		Literal l= lits_[i].first;
		if ( s.isFalse(l) || l == p ){
			tmp.push_back(WeightLiteral(l, 1));
		}
	}
	lits_= tmp;
	bound_= 1;
	slack_= s.isTrue(p) ? 0 : -1;
}

//! Simplify and sort lits with bound as the rhs of an PB constraint
/*! Note that we can't use s.mark in here, because we run this function
 *  in conflict analysis. The marks are already in use!
 *
 * returns \sum_{i,j\\lit(i) = ~lit(j)\\value(lit(i).var()) = value_free}[min(weight(i),weight(j)]
 * This corresponds to the amount by which we overestimated the resulting slack in a VE
 * iff we assume that the operands are canonic
*/
wsum_t PBConstraint::canonicalize(Solver& s) {
	std::vector<bool>& tag= s.pb_tag_;

	// tag is cleared in step 2
	tag.resize( s.numVars()+1, false );

	wsum_t slack_adjust= 0;

	// Step 1: remove superfluous literals and merge duplicate/complementary ones
	LitVec::size_type j= 0, other;
	for (LitVec::size_type i= 0; i != lits_.size(); ++i) {
		lit(i).clearWatch();
		assert (weight(i) > 0 );

		if( tag[lit(i).var()] ){
			// TODO: Use index, rather than bool vector
			// there is a previous occurance of lit(i) or ~lit(i)
			for (other= 0; other < j && lit(other).var() != lit(i).var(); ++other) { ; }

			if ( lit(i) == lit(other) ){
				// merge multiple occurances of the same literal
				weight(other) += weight(i);
				assert( weight(other) > 0 );
			}
			else {
				if( s.value(lit(i).var()) == value_free ){
					// we double counted this amount when we calculated the slack
					slack_adjust+= std::min(weight(i), weight(other));
					assert( slack_adjust >= 0 );
				}
				bound_        -= weight(i); // assume weight(other) >= weight(i)
				weight(other) -= weight(i);
				if ( weight(other) < 0 ){ // assumption was wrong
					lit(other)= lit(i);
					weight(other)= -weight(other);
					bound_+= weight(other);
				}
				else if (weight(other) == 0) {
					tag[lit(other).var()]= false;
					std::memmove(&lits_[0]+other, &lits_[0]+other+1, (j-other-1)*sizeof(lits_[other]));
					--j;
				}
			}
		}
		else {
			if(i != j){
				lits_[j]= lits_[i];
			}
			++j;

			tag[lit(i).var()]= true;
		}
	}
	lits_.erase(lits_.begin()+j, lits_.end());
	if (bound_ < 0) {
		bound_ = 0;
	}
	// Step 2: compute min,max, achievable weight and saturate coefficients
	uint32 minW   = std::numeric_limits<uint32>::max(), maxW = 0;
	for (LitVec::size_type i = 0; i != lits_.size(); ++i) {
		assert( weight(i) > 0 );
		// saturate coefficients
		if (uint64(weight(i)) > uint64(bound_)) {
			// if this variable is not false that changes the slack
			if (!s.isFalse(lit(i)))	slack_adjust+= (weight(i)-bound_);
			weight(i)= bound_;
		}

		if (uint32(weight(i)) > maxW) { maxW = weight(i); }
		if (uint32(weight(i)) < minW) { minW = weight(i); }

		tag[lit(i).var()]= false;
	}
	// Step 3: sort by decreasing weight
	if (maxW != minW) {
		std::stable_sort(lits_.begin(), lits_.end(), compose22(
			std::greater<weight_t>(),
			select2nd<WeightLiteral>(),
			select2nd<WeightLiteral>()));
	}
	else if (minW > 1) {
		// disguised cardinality constraint
		bound_ = (bound_+(minW-1))/minW;
		wsum_t slack= (slack_-slack_adjust-(minW-1))/minW;

		for (LitVec::size_type i= 0; i != lits_.size(); ++i) {
			weight(i)= 1;
		}
		slack_adjust= slack_-slack;
	}
	return slack_adjust;
}

void PBConstraint::updateConstraint(Solver& s, uint32 idx){
	slack_ -= weight(idx);

	if (highestUndoLevel(s) != s.decisionLevel()) {
		s.addUndoWatch(s.decisionLevel(), this);
	}
	undo_[up_].data = (idx<<1) + (undo_[up_].data & 1);
	++up_;
	assert(!litSeen(idx));
	toggleLitSeen(idx);
}

Constraint::PropResult PBConstraint::propagate(Solver& s, Literal, uint32& data){
	assert(s.isFalse(lit(data)));

	updateConstraint(s, data);

	uint32 reasonData= up_;
	uint32 n= getPIndex();

	for (const uint32 end = size(); n != end && (weight(n) > slack_); ++n) {
		if (!litSeen(n)) {
			uint32 dl= s.decisionLevel();
			if( dl < firstImpl_ ){
				firstImpl_= dl;
			}
			if (!s.force(lit(n), this, reasonData)) {
				return PropResult(false, true);
			}
		}
	}
	setPIndex(n);

	return PropResult(true, true);
}

void PBConstraint::reason(Solver& s, Literal p, LitVec& lits){
	assert( undo_ != 0 );
	uint32 stop = s.reasonData(p);
	assert(stop <= up_);
	for (uint32 i = 0; i != stop; ++i) {
		Literal x = lit(undo_[i].idx());
		lits.push_back( ~x );
	}
}

void PBConstraint::addWatch(Solver& s, uint32 idx)
{
	// watch negated literal, so we can reduce slack when lit(idx) is set to false
	s.addWatch(~lit(idx), this, idx);
}

void PBConstraint::undoLevel(Solver& s) {
	// We don't know where to set pidx to exactly, so reset it
	setPIndex(0);
	for (UndoInfo u; up_ != 0 && s.value(lit((u=undoTop()).idx()).var()) == value_free;) {
		assert(litSeen(u.idx()));
		toggleLitSeen(u.idx());
		slack_+= weight(u.idx());
		--up_;
	}
	if(s.decisionLevel() <= firstImpl_){
		firstImpl_= UINT32_MAX;
	}
}


inline uint32 PBConstraint::highestUndoLevel(Solver& s) const {
	return up_ == 0 ? 0 : s.level( lit(undo_[up_-1].idx()).var() );
}

bool PBConstraint::locked(const Solver& s) const {
	return firstImpl_ <= s.decisionLevel();
}

uint32 PBConstraint::isOpen(const Solver& s, const TypeSet& t, LitVec& freeLits)
{
	if (!t.inSet(PBConstraint::type())) {
		return 0;
	}

	LitVec tmpl;
	int32 sum= 0;
	for(LitVec::size_type i= 0; i != size(); ++i){
		// litSeen(i) means it's false
		if(!litSeen(i)){
			if( s.isTrue(lit(i)) ){
				sum+= weight(i);
				if( sum >= bound_ )	return 0;
			} else {
				assert( s.value(lit(i).var()) == value_free );
				tmpl.push_back( lit(i) );
			}
		}
	}
	freeLits= tmpl;
	return PBConstraint::type();
}

bool PBConstraint::minimize(Solver& s, Literal p, CCMinRecursive* r){
	uint32 stop = s.reasonData(p);
	assert(stop <= up_);
	for (uint32 i = 0; i < stop; ++i) {
		UndoInfo u = undo_[i];
		if (!s.ccMinimize(~lit(u.idx()), r)) {
			return false;
		}
	}
	return true;
}


PBCAggregator::PBCAggregator(Solver& s) :
	pbc_(NULL)
{
	weights_.resize(s.numVars());
	signs_.resize(s.numVars());
}

void PBCAggregator::reset()
{
	vars_.clear();
	std::fill(weights_.begin(), weights_.end(), 0);
	std::fill(signs_.begin(), signs_.end(), false);
}

uint32 PBCAggregator::size() const
{
	return vars_.size();
}

WeightLitVec PBCAggregator::weightLits() const
{
	WeightLitVec vec;
	weightLits(vec);
	return vec;
}

void PBCAggregator::weightLits(WeightLitVec& vec) const
{
	vec.reserve(size() + vec.size());
	for (VarDeque::const_iterator it = vars_.begin(); it != vars_.end(); ++it) {
		const Literal l(*it, sign(*it));
		vec.push_back(WeightLiteral(l, weight(*it)));
	}
}

void PBCAggregator::varElimination(Solver &s, Literal l)
{
	//std::cout << "============" << std::endl;
    std::cout << "Before: " << weightLits() << " >= " << pbc_->bound() << std::endl;
    std::cout << "Eliminate: " << l << " weight:" << weight(l.var()) << std::endl;
	assert(initialized());

	assert(pbc_->undo_ == 0 && "the constraint is not integrated into a solver yet");
	assert(pbc_->slack_ < 0 && "the constraint should be violated");

	// sometimes we are asked to eliminate variables that are
	// already eliminated
	if (!(weight(l.var()) && sign(l.var()) == (~l).sign())) {
		eliminator_.reset();
		PBConstraint::buildPBConstraint(eliminator_, s, l, s.reason(l));
		//std::cout << eliminator_ << std::endl;
		//std::cout << "var does not exist " << ~l << " " << weightLits() << std::endl;
		return;
	}

	eliminator_.reset();
	PBConstraint::buildPBConstraint(eliminator_, s, l, s.reason(l));

	weight_t mel= eliminator_.weight(l);
	weight_t mag= weight(~l);
	weight_t mgcd= gcd(mel, mag);

	assert(mag);
	assert(mel);

	mel= mel/mgcd;
	mag= mag/mgcd;

	if ( (pbc_->bound_ > static_cast<wsum_t>(UINT64_MAX / 4)/mel )        ||
		 (pbc_->slack_ < (std::numeric_limits<wsum_t>::min() / mel) / 2)  ||
		 (static_cast<wsum_t>(maxWeight())*mel > static_cast<wsum_t>(UINT32_MAX / 4) )){
		// we can't guarantee that the added values do not overflow!
		// this is a really crude version of overflow handling
		//std::cout << "Weaken" << weightLits() << std::endl;
		weaken(s);
		mag = 1;
		mel = eliminator_.weight(l);
	}
	if ((eliminator_.bound_ > static_cast<wsum_t>(UINT64_MAX / 4)/mag )  ||
		(pbc_->slack_ > (std::numeric_limits<wsum_t>::max() / mag) / 2)       ||
		(static_cast<wsum_t>(eliminator_.lits_[0].second)*mag > static_cast<wsum_t>(UINT32_MAX / 4) )){
		//std::cout << "Weaken" << eliminator_ << std::endl;
		eliminator_.weaken(s,l);
		mel = 1;
		mag = weight(~l);
	}

	// TODO: From thesis: "Checks if the sum of the slacks is negative and applies weakening if it is not"
	if (mag*eliminator_.slack_ + mel*pbc_->slack_ >= 0 ){
		//std::cout << "Weaken" << weightLits() << " ";
		eliminator_.weaken(s,l);
		mel= 1;
		mag= weight(~l);
		//std::cout << "to" << weightLits();
	}

	//std::cout << "Eliminator: " << eliminator_ << " mag: " << mag << " mel: " << mel << " mgcd: " << mgcd << " " << std::endl;

	bool mult= multiply(mel);
	assert( mult );
	mult= eliminator_.multiply(mag);
	assert( mult );

	// this might be overestimated and is adjusted later
	pbc_->bound_ += eliminator_.bound_;
	pbc_->slack_ += eliminator_.slack_;

	//std::cout << "Before elimination: " << weightLits() << " >= " << pbc_->bound() << std::endl;

	// cutting planes inference
	for (LitVec::size_type i = 0; i < eliminator_.size(); ++i) {
		const WeightLiteral wl = eliminator_.lits_[i];
		const Literal lit = wl.first;
		const Var v = lit.var();
		weight_t w = wl.second;
		assert(w > 0);
		if (!weight(lit.var())) {
			// new variable
			//std::cout << "Added " << lit << std::endl;
			vars_.push_back(v);
			weights_[v] = w;
			signs_[v] = lit.sign();
		} else {
			//std::cout << "Found " << lit << std::endl;
			// found variable in pbc

			if (lit.sign() == sign(lit)) {
				weights_[v] += w;
			} else {
				if (s.value(v) == value_free) {
					//pbc_->slack_ -= w;
					// we double counted this amount when we calculated the slack
					pbc_->slack_ -= std::min(w, weight(v));
					//assert( slack_adjust >= 0 );
				}

				// weight(other) == weight in pbc aka weights_[v]
				// weight(i) == w (eliminator)

				pbc_->bound_ -= w; // assume weights_[v] >= w
				weights_[v] -= w;
				if (weight(v) < 0) { // assumption was wrong
					signs_[v] = lit.sign();
					weights_[v] = -weight(v);
					pbc_->bound_ += weight(v);
				} else if (weight(v) == 0) {
					//std::cout << "Eliminated " << lit << std::endl;
					VarDeque::iterator it = std::find(vars_.begin(), vars_.end(), v);
					vars_.erase(it);
					continue;
				}

				assert(weight(v) > 0);
			}
		}
	}

	if (pbc_->bound() < 0) {
		pbc_->bound_ = 0;
	}

	assert(pbc_->bound_ > 0);

	for (VarDeque::const_iterator it = vars_.begin(); it!=vars_.end(); ++it) {
		const Var v = *it;

		assert(weight(v) > 0);

		if (static_cast<wsum_t>(weight(v)) > pbc_->bound()) {
			const Literal lit(*it, sign(*it));
			if (!s.isFalse(lit))
				pbc_->slack_ -= (weight(v) - pbc_->bound());
			weights_[v] = pbc_->bound();
		}
	}

    std::cout << "After: " << weightLits() << " >= " << pbc_->bound() <<  std::endl;

	//std::cout << "calculated: " << calculateSlack(s) << " set: " << pbc_->slack() << std::endl;
	//pbc_->slack_ = pbc_->calculateSlack(s);
	//if (size())
	//	assert(calculateSlack(s) == pbc_->slack());

	assert(pbc_->slack_ < 0 && "the constraint should still be violated");

	//std::cout << "===========" << std::endl;
}

PBConstraint *PBCAggregator::finalize(Solver &s)
{
	assert(initialized());

	pbc_->lits_.clear();
	weightLits(pbc_->lits_);
	//std::cout << "===========\nFinalize: " << *pbc_ << std::endl;
	pbc_->canonicalize(s);
	pbc_->slack_ = pbc_->slack();
	//std::cout << "Canonicalized: " << *pbc_ << std::endl;
	// TODO: Think about this: Why can we not use the previous slack? Does it matter?
	//assert(pbc_->calculateSlack(s) == pbc_->slack());
	PBConstraint* p = pbc_;
	pbc_ = NULL;
	//std::cout << "++++++++++++++" << std::endl;
	return p;
}

bool PBCAggregator::initialized() const
{
	return pbc_;
}

bool PBCAggregator::multiply(weight_t x)
{
	if (x == 1)
		return true;

	// ToDo: checks

	for (VarDeque::const_iterator it = vars_.begin(); it!=vars_.end(); ++it) {
		weights_[*it] *= x;
	}
	pbc_->slack_ *= x;
	pbc_->bound_ *= x;

	return true;
}

void PBCAggregator::weaken(Solver& s, Literal p)
{
	assert( p == Literal(0, true) || weight(p) > 0 );
	assert( pbc_->undo_ == 0 && "this should not be integrated yet");
	VarDeque tmp;
	for (VarDeque::const_iterator it = vars_.begin(); it!=vars_.end(); ++it) {
		Literal l(*it, sign(*it));
		if ( s.isFalse(l) || l == p ){
			weights_[*it] = 1;
			tmp.push_back(*it);
		}
	}
	vars_ = tmp;
	pbc_->bound_ = 1;
	pbc_->slack_ = s.isTrue(p) ? 0 : -1;
}

weight_t PBCAggregator::calculateSlack(const Solver &s) const
{
	weight_t slack = 0;
	for (VarDeque::const_iterator it = vars_.begin(); it!=vars_.end(); ++it) {
		Literal l(*it, sign(*it));
		if (s.isFalse(l))
			continue;
		slack += weight(*it);
	}
	slack -= pbc_->bound();
	return slack;
}

void PBCAggregator::setPBC(PBConstraint *pbc) {
	reset();
	assert(!initialized());

	//std::cout << "Initialize with: " << *pbc << std::endl;

	pbc_ = pbc;

	for (LitVec::size_type i = 0; i < pbc_->size(); ++i) {
		Var v = pbc_->lit(i).var();
		vars_.push_back(v);
		weights_[v] = pbc_->weight(i);
		signs_[v] = pbc_->lit(i).sign();
		assert(weight(v) > 0);
		assert(weight(v) == pbc_->weight(i));
		assert(sign(v) == pbc_->lit(i).sign());
	}

	//std::cout << "WeightLits: " << weightLits() << std::endl;
}


PbcClauseConverter::PbcClauseConverter(const PBConstraint &pbc):
	pbc_(pbc)
{
}

bool PbcClauseConverter::convert(Solver &s, const PBConstraint &pbc, ClauseVec &clauses)
{
	PbcClauseConverter conv(pbc);
	return conv.convert(s, clauses);
}

void PbcClauseConverter::convertDirectly(const PBConstraint &pbc, ClauseVec &clauses)
{
	PbcClauseConverter conv(pbc);
	conv.convertDirectly(clauses);
}

bool PbcClauseConverter::convert(Solver& s, ClauseVec &clauses)
{
	// we need the max size to encode true and false
	assert(pbc_.size() < std::numeric_limits<uint32>::max());

	wsum_t material_left = 0;
	for(LitVec::size_type i= 0; i != pbc_.size(); ++i){
		material_left += pbc_.weight(i);
	}
	memo.clear();
	Formula formula = buildBDD(pbc_.size(), 0UL, material_left, 4000);

	assert(formula != _error_);
	if (formula == _undef_) {
		return false;
	}

	Clasp::ClauseCollector collector(s);
	clausify(collector, formula);
	clauses = collector.clauses();
	return true;
}

Formula PbcClauseConverter::buildBDD(uint32 size, wsum_t sum, wsum_t material_left, uint max_cost)
{
	if (sum >= pbc_.bound()) {
		return _1_;
	} else if (sum + material_left < pbc_.bound()) {
		return _0_;
	} else if (FEnv::topSize() > max_cost) {
		return _undef_;
	}

	BDDKey key = std::make_pair<uint32, wsum_t>(size, sum);
	BDDCache::const_iterator it = memo.find(key);

	if (it == memo.end()) {
		assert(size != 0);
		Formula formula;
		size--;
		material_left -= pbc_.weight(size);
		wsum_t hi_sum = pbc_.lit(size).sign() ? sum : sum + pbc_.weight(size);
		wsum_t lo_sum = pbc_.lit(size).sign() ? sum + pbc_.weight(size) : sum;
		Formula hi_result = buildBDD(size, hi_sum, material_left, max_cost);
		if (hi_result == _undef_) return _undef_;
		Formula lo_result = buildBDD(size, lo_sum, material_left, max_cost);
		if (lo_result == _undef_) return _undef_;

		Lit l(pbc_.lit(size).index());
		formula = ITE(var(var(l)), hi_result, lo_result);
		memo[key] = formula;
		return formula;
	} else {
		return it->second;
	}
}

void PbcClauseConverter::convertDirectly(ClauseVec &clauses)
{
	assert(pbc_.size() <= 32);
	uint32 mask = 0;

	// generate all subsets
	for (int i = 0; i < ::pow(2, pbc_.size()); ++i) {
		//show_binrep(mask);
		mask += 1;

		wsum_t sum = 0;
		for (uint j = 0; j < pbc_.size(); ++j) {
			if ((mask&(1<<j)) == 0) {
				sum += pbc_.weight(j);
			}
		}
		sum -= pbc_.bound();
		LightClause c;
		if (sum < 0) {
			for (uint j = 0; j < pbc_.size(); ++j) {
				if ((mask&(1<<j)) != 0) {
					c.push_back(Lit(pbc_.lit(j).var(), pbc_.lit(j).sign()));
				}
			}
			clauses.push_back(c);
		}
	}
}

} //namespace Clasp
