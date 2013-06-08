//
// Copyright (c) 2013, Benjamin Kaufmann
// Copyright (c) 2013, Dominik Moritz
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

#ifndef CLASP_UTIL_STREAMHELPER_H
#define CLASP_UTIL_STREAMHELPER_H

#ifdef _MSC_VER
#pragma once
#endif

#include <algorithm>
#include <iterator>
#include <vector>
#include <clasp/pb_constraint.h>
#include <clasp/literal.h>

namespace Clasp {

inline std::ostream& operator<<(std::ostream& cout, const Literal& p) {
	if (p.sign())
		cout << "-";
	cout << p.var();
	return cout;
}

inline std::ostream& operator<<(std::ostream& cout, const Clasp::PBConstraint& pbc)
{
	cout << "PB Constraint [ ";
	for (uint32 i = 0; i < pbc.size(); ++i) {
		cout << std::showpos << pbc.weight(i) << "*x" << pbc.lit(i).var() << " ";
	}
	cout << std::noshowpos << ">= " << pbc.bound() << " ], Slack: " << pbc.slack();
	return cout;
}

template<typename T>
inline std::ostream &operator <<(std::ostream& cout, const std::vector<T>& value)
{
	cout << "[ ";
	for (typename std::vector<T>::const_iterator ii = value.begin(); ii != value.end();)
	{
		cout << *ii;
		if (++ii != value.end()) {
			cout << " ";
		}
	}
	cout << " ]";
	return cout;
}

}

#endif // CLASP_UTIL_STREAMHELPER_H
