#ifndef CLAUSECOLLECTOR_H
#define CLAUSECOLLECTOR_H

#include "Global.h"
#include "SolverTypes.h"
#include "clasp/solver.h"

#include <iostream>

namespace Clasp {

// TODO: use std::vector
typedef vec<Lit> LightClause;
typedef vec<LightClause> ClauseVec;

/**
 * A class to aggregate the clauses that were extracted during the
 * PBC to clause transformation
 */
class ClauseCollector
{
public:
	ClauseCollector(Solver& s) :
		vars_(0),
		solver_(s)
	{}
	~ClauseCollector() {}

	void addClause(LightClause &clause) {
		std::cout << "push clause of size " << clause.size() << ":";
		for (int i = 0; i < clause.size(); ++i) {
			std::cout << " " << (sign(clause[i]) ? "-" : "") << var(clause[i]) ;
		}
		std::cout << std::endl;
		clauses_.push(clause);
	}

	Var newVar() {
		std::cout << "new var " << solver_.numVars() + 1 << std::endl;
		return solver_.numVars() + 1;
	}

	bool varElimed(Var) const {
		return false;
	}

	void addUnit(Lit l) {
		LightClause unitClause;
		unitClause.push(l);
		addClause(unitClause);
	}

	ClauseVec clauses() {
		for (int i = 0; i < clauses_.size(); ++i) {
			std::cout << "clause: " << clauses_[i].size() << std::endl;
		}
		return clauses_;
	}

protected:
	ClauseVec clauses_;
	int vars_;
	Solver& solver_;
};

}

#endif // CLAUSECOLLECTOR_H
