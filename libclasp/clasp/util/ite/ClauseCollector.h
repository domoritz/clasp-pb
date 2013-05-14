#ifndef CLAUSECOLLECTOR_H
#define CLAUSECOLLECTOR_H

#include "Global.h"
#include "SolverTypes.h"

typedef vec<Lit> LightClause;
typedef vec<LightClause> ClauseVec;

/**
 * A class to aggregate the clauses that were extracted during the
 * PBC to clause transformation
 */
class ClauseCollector
{
public:
	ClauseCollector() {}
	~ClauseCollector() {
		clauses_.clear(false);
	}

	void addClause(LightClause &clause) {
		clauses_.push(clause);
	}

	Var newVar() {
		return ++vars_;
	}

	bool varElimed(Var) const {
		return false;
	}

	void addUnit(Lit l) {
		LightClause unitClause;
		unitClause.push(l);
		clauses_.push(unitClause);
	}

	ClauseVec clauses() {
		return clauses_;
	}

protected:
	ClauseVec clauses_;
	int vars_;
};

#endif // CLAUSECOLLECTOR_H
