/****************************************************************************************[Global.h]
Copyright (c) 2005-2010, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

/**************************************************************************************************

Contains types, macros, and inline functions generally useful in a C++ program. 

**************************************************************************************************/

#ifndef Global_h
#define Global_h

#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <climits>
#include <cfloat>
#include <utility>
#include <vector>
#include <new>
#include <clasp/util/platform.h>


//=================================================================================================
// Basic Types & Minor Things:

typedef unsigned int   uint;
typedef unsigned long  ulong;
typedef const char     cchar;
typedef unsigned short ushort;


#ifdef __LP64__
#define LP64        // LP : int=32 long,ptr=64 (unix model -- the windows model is LLP : int,long=32 ptr=64)
#endif

#define macro static inline

template<class T> macro T min(T x, T y) { return (x < y) ? x : y; }
template<class T> macro T max(T x, T y) { return (x > y) ? x : y; }

template <bool> struct STATIC_ASSERTION_FAILURE;
template <> struct STATIC_ASSERTION_FAILURE<true>{};
#define TEMPLATE_FAIL STATIC_ASSERTION_FAILURE<false>()

#define PANIC(msg) assert((fprintf(stderr, "%s\n", msg), fflush(stderr), false))
#define Ping  (fflush(stdout), fprintf(stderr, "%s %d\n", __FILE__, __LINE__), fflush(stderr))

#define INITIALIZER(tag) struct Initializer_ ## tag {  Initializer_ ## tag(); } static Initializer_ ## tag ## _instance; Initializer_ ## tag:: Initializer_ ## tag(void)
#define FINALIZER(  tag) struct Finalizer_   ## tag { ~Finalizer_   ## tag(); } static Finalizer_   ## tag ## _instance; Finalizer_   ## tag::~Finalizer_   ## tag(void)

#define elemsof(x) (sizeof(x)/sizeof(*(x)))

template <class T>
macro void swp(T& x, T& y) {        // 'swap' is used by STL
	T tmp = x; x = y; y = tmp; }

// Some GNUC extensions:
//
#ifdef __GNUC__
#define ___noreturn    __attribute__ ((__noreturn__))
#define ___unused      __attribute__ ((__unused__))
#define ___const       __attribute__ ((__const__))
#define ___format(type,fmt,arg) __attribute__ ((__format__(type, fmt, arg) ))
#if (__GNUC__ > 2) || (__GNUC__ >= 2 && __GNUC_MINOR__ > 95)
#define ___malloc      __attribute__ ((__malloc__))
#else
#define ___malloc
#endif
#else
#define ___noreturn
#define ___unused
#define ___const
#define ___format(type,fmt,arg)
#define ___malloc
#endif

// The right 'sprintf()' -- allocating the string itself!
char* nsprintf (cchar* format, ...) ___format(printf, 1, 2) ___malloc;
char* vnsprintf(const char* format, va_list args) ___malloc;


//=================================================================================================
// 'malloc()'-style memory allocation -- never returns NULL; aborts instead:


template<class T> macro T* xmalloc(size_t size) {
	T*   tmp = (T*)malloc(size * sizeof(T));
	assert(size == 0 || tmp != NULL);
	return tmp; }

template<class T> macro T* xrealloc(T* ptr, size_t size) {
	T*   tmp = (T*)realloc((void*)ptr, size * sizeof(T));
	assert(size == 0 || tmp != NULL);
	return tmp; }

template<class T> macro void xfree(T *ptr) {
	if (ptr != NULL) free((void*)ptr); }

macro char* Xstrdup(cchar* src);
macro char* Xstrdup(cchar* src) {
	int     size = strlen(src)+1;
	char*   tmp = xmalloc<char>(size);
	memcpy(tmp, src, size);
	return tmp; }
#define xstrdup(s) Xstrdup(s)

macro char* xstrndup(cchar* src, int len) ___malloc;
macro char* xstrndup(cchar* src, int len) {
	int     size; for (size = 0; size < len && src[size] != '\0'; size++);
	char*   tmp = xmalloc<char>(size+1);
	memcpy(tmp, src, size); tmp[size] = '\0';
	return tmp; }


//=================================================================================================
// Random numbers:


// Returns a random float 0 <= x < 1. Seed must never be 0.
macro double drand(double& seed) {
	seed *= 1389796;
	int q = (int)(seed / 2147483647);
	seed -= (double)q * 2147483647;
	return seed / 2147483647; }

// Returns a random integer 0 <= x < size. Seed must never be 0.
macro int irand(double& seed, int size) {
	return (int)(drand(seed) * size); }


//=================================================================================================
// Time:


#ifdef _MSC_VER
#include <ctime>
macro double cpuTime(void) {
	return (double)clock() / CLOCKS_PER_SEC; }
#else
#include <sys/time.h>
#include <sys/resource.h>
macro double cpuTime(void) {
	struct rusage ru;
	getrusage(RUSAGE_SELF, &ru);
	return (double)ru.ru_utime.tv_sec + (double)ru.ru_utime.tv_usec / 1000000; }
#endif

//=================================================================================================
// Lifted booleans:


class lbool {
	int     value;
	explicit lbool(int v) : value(v) { }

public:
	lbool()       : value(0) { }
	lbool(bool x) : value((int)x*2-1) { }
	int toInt(void) const { return value; }

	bool  operator == (const lbool& other) const { return value == other.value; }
	bool  operator != (const lbool& other) const { return value != other.value; }
	lbool operator ~  (void)               const { return lbool(-value); }

	friend int   toInt  (lbool l);
	friend lbool toLbool(int   v);
	friend char  name   (lbool l);
};
inline int   toInt  (lbool l) { return l.toInt(); }
inline lbool toLbool(int   v) { return lbool(v); }
inline char  name   (lbool l) { static char name[4] = {'!','0','?','1'}; int x = l.value; x = 2 + ((x >> (sizeof(int)*8-2)) | (x & ~(1 << (sizeof(int)*8-1)))); return name[x]; }

const lbool l_True  = toLbool( 1);
const lbool l_False = toLbool(-1);
const lbool l_Undef = toLbool( 0);
const lbool l_Error = toLbool(1 << (sizeof(int)*8-1));


//=================================================================================================
// Relation operators -- extend definitions from '==' and '<'


#ifndef __SGI_STL_INTERNAL_RELOPS   // (be aware of SGI's STL implementation...)
#define __SGI_STL_INTERNAL_RELOPS
template <class T> macro bool operator != (const T& x, const T& y) { return !(x == y); }
template <class T> macro bool operator >  (const T& x, const T& y) { return y < x;     }
template <class T> macro bool operator <= (const T& x, const T& y) { return !(y < x);  }
template <class T> macro bool operator >= (const T& x, const T& y) { return !(x < y);  }
#endif


//=================================================================================================
#endif
