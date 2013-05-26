#ifndef CLAUSECOLLECTOR_H
#define CLAUSECOLLECTOR_H

#include "Global.h"
#include "SolverTypes.h"
#include "clasp/solver.h"

#include <iostream>

namespace Clasp {

typedef std::vector<Lit> LightClause;
typedef std::vector<LightClause> ClauseVec;

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
		for (uint i = 0; i < clause.size(); ++i) {
			std::cout << " " << (sign(clause[i]) ? "-" : "") << var(clause[i]) ;
		}
		std::cout << std::endl;
		clauses_.push_back(clause);
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
		unitClause.push_back(l);
		addClause(unitClause);
	}

	ClauseVec clauses() {
		return clauses_;
	}

protected:
	ClauseVec clauses_;
	int vars_;
	Solver& solver_;
};

}

#endif // CLAUSECOLLECTOR_H
