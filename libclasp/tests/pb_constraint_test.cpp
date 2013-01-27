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
	CPPUNIT_TEST(testConstructor);
	CPPUNIT_TEST(testSimplePropagation);
	CPPUNIT_TEST_SUITE_END();

public:
	PbConstraintTest() {
		body  = posLit(ctx.addVar(Var_t::body_var));
		a     = posLit(ctx.addVar(Var_t::atom_var));
		b     = posLit(ctx.addVar(Var_t::atom_var));
		c     = posLit(ctx.addVar(Var_t::atom_var));

		solver = ctx.master();
		solver->strategies().analyze = SolverStrategies::res_learning;

		ctx.startAddConstraints();
	}

	void testTrivial() {
		CPPUNIT_ASSERT(true);
	}

	void testConstructor() {
		PBConstraint::PBConstraint* pbc = createPbConstraint();
		CPPUNIT_ASSERT(pbc);
		CPPUNIT_ASSERT_EQUAL(pbc->bound(), static_cast<wsum_t>(3));
	}

	void testSimplePropagation() {
		// a :- b.
		// b.
		ctx.addUnary(~b);
		ctx.addBinary(~a, b);
		ctx.addBinary(a, ~b);

		CPPUNIT_ASSERT(!solver->hasConflict());

		solver->force(b, 0);
		CPPUNIT_ASSERT(solver->hasConflict());
	}

private:
	SharedContext ctx;
	Solver*       solver;

	PBConstraint::PBConstraint* createPbConstraint() {
		WeightLitVec lits = makeWeightLits();
		wsum_t bound = 3;
		return new PBConstraint::PBConstraint(*solver, lits, bound);
	}

	WeightLitVec makeWeightLits() {
		WeightLitVec res;
		res.push_back(WeightLiteral(a, 2));
		res.push_back(WeightLiteral(b, 1));
		res.push_back(WeightLiteral(~c, 1));
		return res;
	}

	Literal body;
	Literal a, b, c;
};

CPPUNIT_TEST_SUITE_REGISTRATION(PbConstraintTest);
} }
