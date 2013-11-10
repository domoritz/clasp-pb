//
// Copyright (c) 2012, Dominik Moritz
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

#include <cppunit/TestFixture.h>
#include <cppunit/TestAssert.h>
#include <cppunit/extensions/HelperMacros.h>
#include <algorithm> 
#include <clasp/solver.h>
#include <clasp/clause.h>
#include <clasp/solver_strategies.h>
#define private public
#include <clasp/pb_constraint.h>
#undef private
#include "test.h"

#ifdef _MSC_VER
#pragma warning (disable : 4267) //  conversion from 'size_t' to unsigned int
#pragma once
#endif


namespace Clasp { namespace Test {

class PbConstraintTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(PbConstraintTest);
	CPPUNIT_TEST(testSimpleConstructor);
	CPPUNIT_TEST(testCanonicalizeMerge);
	CPPUNIT_TEST(testCanonicalizeSort);
	CPPUNIT_TEST(testCanonicalizeOversaturated);
	CPPUNIT_TEST(testCanonicalizeCardinalityConstraint);
	CPPUNIT_TEST(testIntegrateAddsLearntConstraint);
	CPPUNIT_TEST(testMultiply);
	CPPUNIT_TEST(testWeakenWithProvidedLiteral);
	CPPUNIT_TEST(testWeakenWithoutProvidedLiteral);
	CPPUNIT_TEST(testReason);
	CPPUNIT_TEST(testCalculateSlack);
	CPPUNIT_TEST(testIsSingleClause);
	CPPUNIT_TEST(testIsNotSingleClause);
	CPPUNIT_TEST(testIsSingleClauseDisguised);
	CPPUNIT_TEST(testUpdateConstraint);
	CPPUNIT_TEST(testClauseExtractionFromPB);
	CPPUNIT_TEST(testClauseExtractionFromDisguisedClause);
	CPPUNIT_TEST(testDirectClauseExtraction);
	CPPUNIT_TEST(testSimplePropagation);
	CPPUNIT_TEST(testSimplePbPropagation);
	CPPUNIT_TEST(testExtractionFromWeightConstraint);
	CPPUNIT_TEST(testConstructionFromConflict);
	CPPUNIT_TEST(testGcd);
	CPPUNIT_TEST(testNcK);
	CPPUNIT_TEST_SUITE_END();

public:
	PbConstraintTest() {
		a = posLit(ctx.addVar(Var_t::atom_var));
		b = posLit(ctx.addVar(Var_t::atom_var));
		c = posLit(ctx.addVar(Var_t::atom_var));
		d = posLit(ctx.addVar(Var_t::atom_var));

		ctx.startAddConstraints();

		solver = ctx.master();
		solver->strategies().analyze = SolverStrategies::res_learning;
	}

	void testSimpleConstructor() {
		PBConstraint::PBConstraint* pbc = createPbConstraint();
		CPPUNIT_ASSERT(pbc);
		CPPUNIT_ASSERT_EQUAL(3LL, pbc->bound());

		//std::cout << *pbc << std::endl;

		delete pbc;
	}

	void testCanonicalizeMerge() {
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 3));
		wlits.push_back(WeightLiteral(b, 1));
		wlits.push_back(WeightLiteral(~c, 1));
		wlits.push_back(WeightLiteral(b, 1));
		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(wlits, 3);

		assert(4U == pbc->size());
		assert(1 == pbc->weight(1));

		CPPUNIT_ASSERT_EQUAL(0LL, pbc->canonicalize(*solver));
		// b should have been merged
		CPPUNIT_ASSERT_EQUAL(3U, pbc->size());
		CPPUNIT_ASSERT_EQUAL(2, pbc->weight(1));

		CPPUNIT_ASSERT_EQUAL(3LL, pbc->bound());

		delete pbc;
	}

	void testCanonicalizeSort() {
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 7));
		wlits.push_back(WeightLiteral(b, 2));
		wlits.push_back(WeightLiteral(~c, 1));
		wlits.push_back(WeightLiteral(d, 3));
		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(wlits, 7);

		pbc->canonicalize(*solver);

		CPPUNIT_ASSERT_EQUAL(4U, pbc->size());
		CPPUNIT_ASSERT_EQUAL(7, pbc->weight(0));
		CPPUNIT_ASSERT_EQUAL(3, pbc->weight(1));
		CPPUNIT_ASSERT_EQUAL(2, pbc->weight(2));
		CPPUNIT_ASSERT_EQUAL(1, pbc->weight(3));

		CPPUNIT_ASSERT_EQUAL(7LL, pbc->bound());

		delete pbc;
	}

	void testCanonicalizeOversaturated() {
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 5));
		wlits.push_back(WeightLiteral(b, 1));
		wlits.push_back(WeightLiteral(~c, 4));
		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(wlits, 3);

		assert(5 == pbc->weight(0));
		pbc->slack_ = 7LL;
		CPPUNIT_ASSERT_EQUAL(3LL, pbc->canonicalize(*solver));
		CPPUNIT_ASSERT_EQUAL(3, pbc->weight(0));
		// canonicalize does not adjust the slack
		CPPUNIT_ASSERT_EQUAL(7LL, pbc->slack());

		CPPUNIT_ASSERT_EQUAL(3LL, pbc->bound());

		delete pbc;
	}

	void testCanonicalizeCardinalityConstraint() {
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 3));
		wlits.push_back(WeightLiteral(b, 3));
		wlits.push_back(WeightLiteral(~c, 3));
		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(wlits, 6);

		CPPUNIT_ASSERT_EQUAL(0LL, pbc->canonicalize(*solver));

		CPPUNIT_ASSERT_EQUAL(1, pbc->weight(0));
		CPPUNIT_ASSERT_EQUAL(1, pbc->weight(1));
		CPPUNIT_ASSERT_EQUAL(1, pbc->weight(2));

		CPPUNIT_ASSERT_EQUAL(2LL, pbc->bound());

		delete pbc;
	}

	void testIntegrateAddsLearntConstraint() {
		ctx.endInit();
		CPPUNIT_ASSERT_EQUAL(0U, solver->numLearntConstraints());
		CPPUNIT_ASSERT_EQUAL(0U, solver->numConstraints());
		PBConstraint* pbc = createPbConstraint();
		pbc->integrate(*solver);
		CPPUNIT_ASSERT_EQUAL(1U, solver->numLearntConstraints());
		CPPUNIT_ASSERT_EQUAL(0U, solver->numConstraints());
	}

	void testMultiply() {
		PBConstraint::PBConstraint* pbc = createPbConstraint();

		ctx.endInit();
		pbc->integrate(*solver);

		CPPUNIT_ASSERT_EQUAL(7LL, pbc->slack());

		pbc->multiply(2);

		CPPUNIT_ASSERT_EQUAL(6, pbc->weight(0));
		CPPUNIT_ASSERT_EQUAL(10, pbc->weight(1));
		CPPUNIT_ASSERT_EQUAL(4, pbc->weight(2));

		CPPUNIT_ASSERT_EQUAL(6LL, pbc->bound());

		CPPUNIT_ASSERT_EQUAL(14LL, pbc->slack());
	}

	void testWeakenWithProvidedLiteral() {
		ctx.endInit();

		PBConstraint::PBConstraint* pbc = createPbConstraint();
		CPPUNIT_ASSERT_EQUAL(3U, pbc->size());
		solver->assume(~a);
		solver->assume(b);
		solver->assume(c);
		pbc->weaken(*solver, b);
		CPPUNIT_ASSERT_EQUAL(3U, pbc->size());
		CPPUNIT_ASSERT_EQUAL(1LL, pbc->bound());
		CPPUNIT_ASSERT_EQUAL(1, pbc->weight(0));
		CPPUNIT_ASSERT_EQUAL(1, pbc->weight(1));
		CPPUNIT_ASSERT_EQUAL(0LL, pbc->slack());

		delete pbc;
	}

	void testWeakenWithoutProvidedLiteral() {
		ctx.endInit();

		PBConstraint::PBConstraint* pbc = createPbConstraint();
		assert(3UL == pbc->size());
		solver->assume(~a);
		solver->assume(b);
		solver->assume(c);
		pbc->weaken(*solver);
		CPPUNIT_ASSERT_EQUAL(2U, pbc->size());
		CPPUNIT_ASSERT_EQUAL(1LL, pbc->bound());
		CPPUNIT_ASSERT_EQUAL(1, pbc->weight(0));
		CPPUNIT_ASSERT_EQUAL(1, pbc->weight(1));
		CPPUNIT_ASSERT_EQUAL(-1LL, pbc->slack());

		delete pbc;
	}

	void testUpdateConstraint() {
		PBConstraint::PBConstraint* pbc = createPbConstraint();
		pbc->integrate(*solver);
		assert(7LL == pbc->slack());
		assert(0U == pbc->undo_->idx());
		assert(0U == pbc->up_);
		pbc->updateConstraint(*solver, 2);
		CPPUNIT_ASSERT_EQUAL(5LL, pbc->slack());
		CPPUNIT_ASSERT_EQUAL(2U, pbc->undo_->idx());
		CPPUNIT_ASSERT_EQUAL(1U, pbc->up_);
		CPPUNIT_ASSERT_EQUAL(1U, pbc->undo_[2].data);
	}

	void testReason() {
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 2));
		wlits.push_back(WeightLiteral(b, 1));
		wlits.push_back(WeightLiteral(~c, 1));

		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(wlits, 3);
		ctx.endInit();
		pbc->integrate(*solver);

		LitVec lits;
		assert(0UL == lits.size());
		pbc->reason(*solver, a, lits);
		// a has no reason, it is implied by the pbc
		CPPUNIT_ASSERT_EQUAL(0UL, lits.size());

		solver->assume(~b);
		solver->propagate();

		pbc->reason(*solver, ~c, lits);
		CPPUNIT_ASSERT_EQUAL(1UL, lits.size());
		CPPUNIT_ASSERT(~b == lits[0]);
	}

	void testCalculateSlack() {
		ctx.endInit();

		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 1));
		wlits.push_back(WeightLiteral(b, 2));
		wlits.push_back(WeightLiteral(~c, 5));
		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(wlits, 2L);
		CPPUNIT_ASSERT_EQUAL(6, pbc->calculateSlack(*solver));

		solver->assume(~a);
		CPPUNIT_ASSERT_EQUAL(5, pbc->calculateSlack(*solver));

		solver->assume(c);
		CPPUNIT_ASSERT_EQUAL(0, pbc->calculateSlack(*solver));

		solver->assume(b);
		CPPUNIT_ASSERT_EQUAL(0, pbc->calculateSlack(*solver));
	}

	void testIsSingleClause() {
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 1));
		wlits.push_back(WeightLiteral(b, 1));
		wlits.push_back(WeightLiteral(c, 1));
		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(wlits, 1L);
		CPPUNIT_ASSERT(pbc->isClause());
	}

	void testIsSingleClauseDisguised() {
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 4));
		wlits.push_back(WeightLiteral(b, 2));
		wlits.push_back(WeightLiteral(c, 1));
		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(wlits, 4L);
		CPPUNIT_ASSERT(pbc->isClause());
	}

	void testIsNotSingleClause() {
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 4));
		wlits.push_back(WeightLiteral(b, 2));
		wlits.push_back(WeightLiteral(c, 2));
		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(wlits, 4L);
		CPPUNIT_ASSERT(!pbc->isClause());
	}

	void testClauseExtractionFromPB() {
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 1));
		wlits.push_back(WeightLiteral(b, 2));
		wlits.push_back(WeightLiteral(c, 3));
		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(wlits, 4L);
		//std::cout << *pbc << std::endl;
		ClauseVec clauses;
		bool ret = PbcClauseConverter::convert(*solver, *pbc, clauses);
		CPPUNIT_ASSERT(ret);
		CPPUNIT_ASSERT_EQUAL(4UL, clauses.size());
		CPPUNIT_ASSERT_EQUAL(3UL, clauses[0].size());
	}

	void testClauseExtractionFromDisguisedClause() {
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 1));
		wlits.push_back(WeightLiteral(b, 1));
		wlits.push_back(WeightLiteral(c, 1));
		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(wlits, 1L);
		//std::cout << *pbc << std::endl;
		ClauseVec clauses;
		bool ret = PbcClauseConverter::convert(*solver, *pbc, clauses);
		CPPUNIT_ASSERT(ret);
		CPPUNIT_ASSERT_EQUAL(2UL, clauses.size());
		CPPUNIT_ASSERT_EQUAL(4UL, clauses[0].size());
		CPPUNIT_ASSERT_EQUAL(1UL, clauses[1].size());
	}

	void testDirectClauseExtraction() {
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(~a, 1));
		wlits.push_back(WeightLiteral(b, 2));
		wlits.push_back(WeightLiteral(c, 3));
		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(wlits, 4L);
		ClauseVec clauses;
		PbcClauseConverter::convertDirectly(*pbc, clauses);
		//std::cout << clauses;
		CPPUNIT_ASSERT_EQUAL(5UL, clauses.size());
	}

	void testSimplePropagation() {
		// a :- b.
		// b.
		// c.
		ctx.addUnary(~b);
		ctx.addUnary(~c);
		ctx.addBinary(~a, b);
		ctx.addBinary(a, ~b);

		CPPUNIT_ASSERT_EQUAL(4U, solver->numVars());

		CPPUNIT_ASSERT(!solver->hasConflict());

		solver->force(b, 0);
		CPPUNIT_ASSERT(solver->hasConflict());

		CPPUNIT_ASSERT_EQUAL(1ULL, solver->stats.conflicts);
	}

	void testSimplePbPropagation() {
		/*
		 * 2*a + 1*b + 1* not c >= 3 can propagate a
		 * because the factor for a is larger than
		 * the constraint's slack (1)
		 */
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 2));
		wlits.push_back(WeightLiteral(b, 1));
		wlits.push_back(WeightLiteral(~c, 1));

		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(wlits, 3);
		ctx.endInit();
		CPPUNIT_ASSERT_EQUAL(false, solver->isTrue(a));
		pbc->integrate(*solver);
		CPPUNIT_ASSERT_EQUAL(true, solver->isTrue(a));
		CPPUNIT_ASSERT_EQUAL(true, solver->isUndecided(b));
		CPPUNIT_ASSERT_EQUAL(true, solver->isUndecided(c));
		CPPUNIT_ASSERT_EQUAL(1LL, pbc->slack());

		/*
		 * When b is set to false, the slack becomes 0,
		 * and all variables have to be decided
		 */
		solver->assume(~b);
		solver->propagate();
		CPPUNIT_ASSERT_EQUAL(true, solver->isTrue(a));
		CPPUNIT_ASSERT_EQUAL(true, solver->isFalse(b));
		CPPUNIT_ASSERT_EQUAL(true, solver->isFalse(c));
		CPPUNIT_ASSERT_EQUAL(0LL, pbc->slack());
	}

	void testConstructionFromConflict() {
		ctx.addUnary(a);
		ctx.addUnary(~a);

		ctx.endInit();

		solver->assume(a);
	}

	void testExtractionFromWeightConstraint() {
		Constraint* co;
		WeightLitVec lits;
		wsum_t bound = 0;
		wsum_t slack = 0;

		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 3));
		wlits.push_back(WeightLiteral(b, 3));
		wlits.push_back(WeightLiteral(c, 1));

		WeightConstraint::newWeightConstraint(ctx, a, wlits, 5, &co);
		WeightConstraint* wc = dynamic_cast<WeightConstraint*>(co);

		ctx.endInit();
		solver->assume(~b);
		solver->propagate();

		assert(ctx.numConstraints() == 1);
		assert(wc);
		wc->extractActivePB(*solver, lits, bound, slack, d);

		CPPUNIT_ASSERT_EQUAL(5LL, bound);
		CPPUNIT_ASSERT_EQUAL(4LL, slack);
		CPPUNIT_ASSERT_EQUAL(4UL, lits.size());
		CPPUNIT_ASSERT(std::find(lits.begin(), lits.end(), WeightLiteral(a, 1)) == lits.end());
		CPPUNIT_ASSERT(std::find(lits.begin(), lits.end(), WeightLiteral(b, 2)) == lits.end());
		CPPUNIT_ASSERT(std::find(lits.begin(), lits.end(), WeightLiteral(c, 3)) == lits.end());
		CPPUNIT_ASSERT(std::find(lits.begin(), lits.end(), WeightLiteral(d, 4)) == lits.end());
	}

	void testGcd() {
		CPPUNIT_ASSERT_EQUAL(2, gcd(1527394542, 244));
		CPPUNIT_ASSERT_EQUAL(1, gcd(17, 11));
		CPPUNIT_ASSERT_EQUAL(57, gcd(77577, 7923));
		CPPUNIT_ASSERT_EQUAL(57, gcd(7923, 77577));
		CPPUNIT_ASSERT_EQUAL(10, gcd(10, 1000));
		CPPUNIT_ASSERT_EQUAL(17, gcd(45645, 34));
	}

	void testNcK() {
		CPPUNIT_ASSERT_EQUAL(0ULL, nChooseK(1, 2));
		CPPUNIT_ASSERT_EQUAL(2ULL, nChooseK(2, 1));
		CPPUNIT_ASSERT_EQUAL(1ULL, nChooseK(2, 2));
		CPPUNIT_ASSERT_EQUAL(1ULL, nChooseK(7, 7));
		CPPUNIT_ASSERT_EQUAL(120ULL, nChooseK(10, 3));
		CPPUNIT_ASSERT_EQUAL(10618005270ULL, nChooseK(712, 4));
	}

private:
	SharedContext ctx;
	Solver*       solver;

	PBConstraint::PBConstraint* createPbConstraint() {
		WeightLitVec wlits = makeWeightLits();
		return new PBConstraint::PBConstraint(wlits, 3);
	}

	WeightLitVec makeWeightLits() {
		WeightLitVec res;
		res.push_back(WeightLiteral(a, 3));
		res.push_back(WeightLiteral(b, 5));
		res.push_back(WeightLiteral(~c, 2));
		return res;
	}

	Literal a, b, c, d;
};

CPPUNIT_TEST_SUITE_REGISTRATION(PbConstraintTest);
} }
