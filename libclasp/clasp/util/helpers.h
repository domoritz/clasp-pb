//
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

#ifndef CLASP_HELPERS_H
#define CLASP_HELPERS_H
#ifdef _MSC_VER
#pragma once
#endif

namespace Clasp {

inline int32 gcd(int32 x, int32 y){
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

inline uint64 nChooseK(uint32 n, uint32 k){
	if (k > n) {
		return 0;
	}
	uint64 r = 1;
	for (uint32 d = 1; d <= k; ++d) {
		r *= n--;
		r /= d;
	}
	return r;
}

}

#endif // CLASP_HELPERS_H
