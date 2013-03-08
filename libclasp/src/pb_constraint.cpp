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

namespace Clasp {

PBConstraint::PBConstraint(Solver& s, const Literal p, const Antecedent& ant, bool conflict):
bound_(1), slack_(0), pidx_(0), up_(0), undo_(0)
{
	const bool generic= (ant.type() == Antecedent::generic_constraint);
	WeightConstraint* wc;

	if( generic && ant.constraint()->type() == Constraint_t::learnt_pb){
		PBConstraint* pbc= static_cast<PBConstraint*>(ant.constraint());

		bound_= pbc->bound_;
		slack_= pbc->slack_;

		lits_.reserve(pbc->lits_.size());
		for (uint32 i = 0; i != pbc->size(); ++i) {
			Literal l= pbc->lit(i);

			if (s.value(l.var()) == value_free || s.level(l.var()) != 0 || l == p){
				lits_.push_back(pbc->lits_[i]);
			}
			else if (s.isTrue(l)){
				bound_-= pbc->weight(i);
			}
			else if (s.isFalse(l) && !pbc->litSeen(i)){
				slack_-= pbc->weight(i);
			}
		}
		if(conflict){
			// this is a conflicting constraint, but hasn't updated its slack!
			slack_-= weight(p);
		}
	}
	else if ( generic && (wc= dynamic_cast<WeightConstraint*>(ant.constraint())) != 0 ){
		wc->extractActivePB(s, lits_, bound_, slack_, p);

		if(conflict){
			// this is a conflicting constraint, but hasn't updated its slack!
			slack_-= weight(p);
		}
	}
	else {
		// This could be a clause, or about anything else...
		// Let's just use the reason it provides and build a PB constraint from that
		LitVec reasons;
		ant.reason(s, p, reasons);

		slack_= -1;
		lits_.reserve(reasons.size()+1);
		lits_.push_back(WeightLiteral(p, 1));
		for(LitVec::size_type i= 0; i != reasons.size(); ++i){
			lits_.push_back(WeightLiteral(~reasons[i],1));
			if(s.isTrue(lit(i))) ++slack_;
		}
	}
}

PBConstraint::PBConstraint(Solver &, WeightLitVec lits, wsum_t bound):
lits_(lits), bound_(bound), slack_(0), pidx_(0), up_(0), undo_(0) {}

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

namespace {
	int32 gcd(int32 x, int32 y){
		assert(x != 0 && y != 0);
		while ( true ) {
			if ( !x )
				return y;
			y %= x;

			if ( !y )
				return x;
			x %= y;
		}
	}
}

void PBConstraint::varElimination(Solver& s, Literal l){
	// TODO: was soll das hier?
	assert( undo_ == 0 && "the constraint is not integrated into a solver yet");
	assert( weight(~l) > 0 && "can't eliminate non-existing literal");
	assert( slack_ < 0 && "the constraint should be violated");

	PBConstraint eliminator(s, l, s.reason(l));

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

	tag.resize( s.numVars()+1, false );

	wsum_t slack_adjust= 0;

	// Step 1: remove superfluous literals and merge duplicate/complementary ones
	LitVec::size_type j= 0, other;
	for (LitVec::size_type i= 0; i != lits_.size(); ++i) {
		lit(i).clearWatch();
		assert (weight(i) > 0 );

		if( tag[lit(i).var()] ){
			// there is a previous occurance of lit(i) or ~lit(i)
			for (other= 0; other < j && lit(other).var() != lit(i).var(); ++other) { ; }

			if ( lit(i) == lit(other) ){
				// merge multiple occurances of the same literal
				weight(other) += weight(i);
				assert( weight(other) > 0 );
			}
			else {
				if( s.value(lit(i).var()) == value_free ){
					// we double counted this amount if we calculated the slack
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

uint32 PBConstraint::isOpen(const Solver &s, const TypeSet &t, LitVec &freeLits)
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
			}
			else {
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

} //namespace Clasp
