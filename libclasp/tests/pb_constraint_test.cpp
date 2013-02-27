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

#ifdef _MSC_VER
#pragma warning (disable : 4267) //  conversion from 'size_t' to unsigned int
#pragma once
#endif


namespace Clasp { namespace Test {

class PbConstraintTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(PbConstraintTest);
	CPPUNIT_TEST(testTrivial);
	CPPUNIT_TEST(testSimpleConstructor);
	CPPUNIT_TEST(testCanonicalizeMerge);
	CPPUNIT_TEST(testCanonicalizeSort);
	CPPUNIT_TEST(testCanonicalizeOversaturated);
	CPPUNIT_TEST(testCanonicalizeCardinalityConstraint);
	CPPUNIT_TEST(testIntegrateAddsLearntConstraint);
	CPPUNIT_TEST(testMultiply);
	CPPUNIT_TEST(testSimplePropagation);
	CPPUNIT_TEST(testSimplePbPropagation);
	CPPUNIT_TEST(testExtractionFromWeightConstraint);
	CPPUNIT_TEST(testConstructionFromConflict);
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

	void testTrivial() {
		CPPUNIT_ASSERT(true);
	}

	void testSimpleConstructor() {
		PBConstraint::PBConstraint* pbc = createPbConstraint();
		CPPUNIT_ASSERT(pbc);
		CPPUNIT_ASSERT_EQUAL(3LL, pbc->bound());
	}

	void testCanonicalizeMerge() {
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 3));
		wlits.push_back(WeightLiteral(b, 1));
		wlits.push_back(WeightLiteral(~c, 1));
		wlits.push_back(WeightLiteral(b, 1));
		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(*solver, wlits, 3);

		assert(4U == pbc->size());
		assert(1 == pbc->weight(1));

		CPPUNIT_ASSERT_EQUAL(0LL, pbc->canonicalize(*solver));
		// b should have been merged
		CPPUNIT_ASSERT_EQUAL(3U, pbc->size());
		CPPUNIT_ASSERT_EQUAL(2, pbc->weight(1));

		CPPUNIT_ASSERT_EQUAL(3LL, pbc->bound());
	}

	void testCanonicalizeSort() {
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 7));
		wlits.push_back(WeightLiteral(b, 2));
		wlits.push_back(WeightLiteral(~c, 1));
		wlits.push_back(WeightLiteral(d, 3));
		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(*solver, wlits, 7);

		pbc->canonicalize(*solver);

		CPPUNIT_ASSERT_EQUAL(4U, pbc->size());
		CPPUNIT_ASSERT_EQUAL(7, pbc->weight(0));
		CPPUNIT_ASSERT_EQUAL(3, pbc->weight(1));
		CPPUNIT_ASSERT_EQUAL(2, pbc->weight(2));
		CPPUNIT_ASSERT_EQUAL(1, pbc->weight(3));

		CPPUNIT_ASSERT_EQUAL(7LL, pbc->bound());
	}

	void testCanonicalizeOversaturated() {
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 5));
		wlits.push_back(WeightLiteral(b, 1));
		wlits.push_back(WeightLiteral(~c, 4));
		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(*solver, wlits, 3);

		assert(5 == pbc->weight(0));
		pbc->slack_ = 7LL;
		CPPUNIT_ASSERT_EQUAL(3LL, pbc->canonicalize(*solver));
		CPPUNIT_ASSERT_EQUAL(3, pbc->weight(0));
		// canonicalize does not adjust the slack
		CPPUNIT_ASSERT_EQUAL(7LL, pbc->slack());

		CPPUNIT_ASSERT_EQUAL(3LL, pbc->bound());
	}

	void testCanonicalizeCardinalityConstraint() {
		WeightLitVec wlits;
		wlits.push_back(WeightLiteral(a, 3));
		wlits.push_back(WeightLiteral(b, 3));
		wlits.push_back(WeightLiteral(~c, 3));
		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(*solver, wlits, 6);

		CPPUNIT_ASSERT_EQUAL(0LL, pbc->canonicalize(*solver));

		CPPUNIT_ASSERT_EQUAL(1, pbc->weight(0));
		CPPUNIT_ASSERT_EQUAL(1, pbc->weight(1));
		CPPUNIT_ASSERT_EQUAL(1, pbc->weight(2));

		CPPUNIT_ASSERT_EQUAL(2LL, pbc->bound());
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

		PBConstraint::PBConstraint* pbc = new PBConstraint::PBConstraint(*solver, wlits, 3);
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
		Constraint* c;
		WeightLitVec lits;
		wsum_t bound;
		wsum_t slack;

		WeightLitVec wlits = makeWeightLits();

		ctx.addUnary(a);
		ctx.endInit();
		solver->propagate();

		WeightConstraint::newWeightConstraint(ctx, a, wlits, 3, &c);

		WeightConstraint* wc = dynamic_cast<WeightConstraint*>(c);
		//wc->extractActivePB(*solver, lits, bound, slack, a);

		//CPPUNIT_ASSERT_EQUAL(bound, 3LL);
	}

private:
	SharedContext ctx;
	Solver*       solver;

	PBConstraint::PBConstraint* createPbConstraint() {
		WeightLitVec wlits = makeWeightLits();
		return new PBConstraint::PBConstraint(*solver, wlits, 3);
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
