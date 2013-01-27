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
#include <clasp/pb_constraint.h>
#include <clasp/solver_strategies.h>

#ifdef _MSC_VER
#pragma warning (disable : 4267) //  conversion from 'size_t' to unsigned int
#pragma once
#endif


namespace Clasp { namespace Test {

class PbConstraintTest : public CppUnit::TestFixture {
	CPPUNIT_TEST_SUITE(PbConstraintTest);
	CPPUNIT_TEST(testTrivial);
	CPPUNIT_TEST(testSimpleConstructor);
	CPPUNIT_TEST(testSimplePropagation);
	CPPUNIT_TEST(testExtractionFromWeightConstraint);
	CPPUNIT_TEST(testConstructionFromConflict);
	CPPUNIT_TEST_SUITE_END();

public:
	PbConstraintTest() {
		a = posLit(ctx.addVar(Var_t::atom_var));
		b = posLit(ctx.addVar(Var_t::atom_var));
		c = posLit(ctx.addVar(Var_t::atom_var));

		solver = ctx.master();
		solver->strategies().analyze = SolverStrategies::res_learning;

		ctx.startAddConstraints();
	}

	void testTrivial() {
		CPPUNIT_ASSERT(true);
	}

	void testSimpleConstructor() {
		PBConstraint::PBConstraint* pbc = createPbConstraint();
		CPPUNIT_ASSERT(pbc);
		CPPUNIT_ASSERT_EQUAL(3LL, pbc->bound());
	}

	void testSimplePropagation() {
		// a :- b.
		// b.
		// c.
		ctx.addUnary(~b);
		ctx.addUnary(~c);
		ctx.addBinary(~a, b);
		ctx.addBinary(a, ~b);

		CPPUNIT_ASSERT_EQUAL(3U, solver->numVars());

		CPPUNIT_ASSERT(!solver->hasConflict());

		solver->force(b, 0);
		CPPUNIT_ASSERT(solver->hasConflict());

		CPPUNIT_ASSERT_EQUAL(1ULL, solver->stats.conflicts);
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
		res.push_back(WeightLiteral(a, 2));
		res.push_back(WeightLiteral(b, 1));
		res.push_back(WeightLiteral(~c, 1));
		return res;
	}

	Literal a, b, c;
};

CPPUNIT_TEST_SUITE_REGISTRATION(PbConstraintTest);
} }
