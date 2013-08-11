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

#include <clasp/pb_constraint.h>
#include <clasp/literal.h>
#include <algorithm>
#include <iterator>
#include <vector>
#include <bitset>

namespace Clasp {

inline std::ostream& operator<<(std::ostream& cout, const Literal& p) {
	if (p.sign())
		cout << "-";
	cout << p.var();
	return cout;
}

inline std::ostream& operator<<(std::ostream& cout, const Lit& p) {
	if (sign(p))
		cout << "-";
	cout << var(p);
	return cout;
}

inline std::ostream& operator<<(std::ostream& cout, const Clasp::PBConstraint& pbc)
{
	cout << "PB Constraint [ ";
	for (uint32 i = 0; i < pbc.size(); ++i) {
		cout << std::showpos << pbc.weight(i) << "*x" << pbc.lit(i) << " ";
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

template<typename T>
void show_binrep(const T& a)
{
	const char* beg = reinterpret_cast<const char*>(&a);
	const char* end = beg + sizeof(a);
	while(beg != end)
		std::cout << std::bitset<CHAR_BIT>(*beg++) << ' ';
	std::cout << '\n';
}

}

#endif // CLASP_UTIL_STREAMHELPER_H
