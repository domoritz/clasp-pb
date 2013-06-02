/*****************************************************************************[Hardware_clausify.C]
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

#include "clasp/util/ite/Hardware.h"

struct Clausifier
{
	Clasp::ClauseCollector&      s;
	std::vector<Lit>     tmp_clause;
	formulaVec           tmp_marked;

	Clausifier(Clasp::ClauseCollector& _s) : s(_s) {}

    static /*WARNING*/ CMap<int>      occ;
    static /*WARNING*/ CMap<Var>      vmap;
    static /*WARNING*/ CMap<Lit,true> vmapp;
    FMap<bool>   seen;

    inline void clause(Lit a, Lit b) {
		tmp_clause.clear(); tmp_clause.push_back(a); tmp_clause.push_back(b); s.addClause(tmp_clause); }
    inline void clause(Lit a, Lit b, Lit c) {
		tmp_clause.clear(); tmp_clause.push_back(a); tmp_clause.push_back(b); tmp_clause.push_back(c); s.addClause(tmp_clause); }
    inline void clause(Lit a, Lit b, Lit c, Lit d) {
		tmp_clause.clear(); tmp_clause.push_back(a); tmp_clause.push_back(b); tmp_clause.push_back(c); tmp_clause.push_back(d); s.addClause(tmp_clause); }


    void  usage  (Formula f);
	void _collect(Formula f, std::vector<Formula>& out);
	void  collect(Formula f, std::vector<Formula> &out);

    Lit   basicClausify   (Formula f);
    Lit   polarityClausify(Formula f);
};

CMap<int>      Clausifier::occ  (0);
CMap<Var>      Clausifier::vmap (var_Undef);
CMap<Lit,true> Clausifier::vmapp(lit_Undef);

void Clausifier::usage(Formula f)
{
    if (Atom_p(f))
        return;

    occ.set(f,occ.at(f)+1);

    if (occ.at(f) == 1){
        if (Bin_p(f)){
            usage(left(f)); usage(right(f));
        }else if (ITE_p(f)){
            usage(cond(f)); usage(tt(f)); usage(ff(f));
        }else{
            assert(FA_p(f));
            usage(FA_x(f)); usage(FA_y(f)); usage(FA_c(f));
        }
    }
}

void Clausifier::collect(Formula f, std::vector<Formula>& out)
{
    tmp_marked.clear();
    _collect(left(f), out);
    _collect(right(f),out);
	for (formulaVec::size_type i = 0; i < tmp_marked.size(); i++)
        seen.set(tmp_marked[i],false);
}

void Clausifier::_collect(Formula f, std::vector<Formula> &out)
{
    if (!seen.at(f)){
        seen.set(f,true);
		tmp_marked.push_back(f);
        if (Bin_p(f) && op(f) == op_And && !sign(f) && occ.at(f) == 1){
            _collect(left(f) ,out);
            _collect(right(f),out);
        }
        else
			out.push_back(f);
    }
}

Lit Clausifier::polarityClausify(Formula f)
{
	Lit result = lit_Undef;

	if (Atom_p(f)){
	  #if 0
		assert(!Const_p(f));
	  #else
		if (Const_p(f)){
			Var x = s.newVar();
			s.addUnit(Lit(x, (f == _0_)));
			result = Lit(x);
		}else
	  #endif
		result = Lit(index(f),sign(f));
	}else if (vmapp.at(f) != lit_Undef && !s.varElimed(var(vmapp.at(f)))){
		result = vmapp.at(f);
	}else{
#if 1
		result = vmapp.at(~f) != lit_Undef && !s.varElimed(var(vmapp.at(~f))) ?
			Lit(var(vmapp.at(~f))) : Lit(s.newVar());
#else
		result = Lit(s.newVar());
#endif
		if (Bin_p(f)){
			if (op(f) == op_And){
				formulaVec conj;
				collect(f, conj);
				assert(conj.size() > 1);
				if (!sign(f)){
					for (formulaVec::size_type i = 0; i < conj.size(); i++)
						clause(~result,polarityClausify(conj[i]));
				}else{
					std::vector<Lit> ls;
					ls.push_back(result);
					for (formulaVec::size_type i = 0; i < conj.size(); i++)
						ls.push_back(polarityClausify(~conj[i]));
					s.addClause(ls);
				}
				//printf("and: %d = ", var(result));
				//for (int i = 0; i < conj.size(); i++)
				//    printf("%c%d ", sign(polarityClausify(conj[i])) ? '-' : ' ',
				//           var(polarityClausify(conj[i])));
				//printf("\n");
			}else{
				Lit l  = polarityClausify( left (f));
				Lit r  = polarityClausify( right(f));
				Lit nl = polarityClausify(~left (f));
				Lit nr = polarityClausify(~right(f));

				//printf("equiv:\n");
				assert(op(f) == op_Equiv);
				if (!sign(f)){
					clause(~result, nl,  r);
					clause(~result,  l, nr);
				}else{
					clause( result, nl, nr);
					clause( result,  l,  r);
				}
			}
		}else if (ITE_p(f)){
			Lit  c = polarityClausify( cond(f));
			Lit nc = polarityClausify(~cond(f));

			if (!sign(f)){
				Lit  a = polarityClausify( tt  (f));
				Lit  b = polarityClausify( ff  (f));
				clause(~result, nc,  a);
				clause(~result,  c,  b);
				clause( a,  b, ~result);
			}else{
				Lit na = polarityClausify(~tt  (f));
				Lit nb = polarityClausify(~ff  (f));
				clause( result, nc, na);
				clause( result,  c, nb);
				clause(na, nb,  result);
			}
		}else{
			assert(FA_p(f));

			if (isCarry(f)){
				//printf("carry:\n");
				if (!sign(f)){
					Lit  a = polarityClausify( FA_x(f));
					Lit  b = polarityClausify( FA_y(f));
					Lit  c = polarityClausify( FA_c(f));
					clause(~result,  a,  b);
					clause(~result,  c,  a);
					clause(~result,  c,  b);
				}else{
					Lit na = polarityClausify(~FA_x(f));
					Lit nb = polarityClausify(~FA_y(f));
					Lit nc = polarityClausify(~FA_c(f));
					clause( result, na, nb);
					clause( result, nc, na);
					clause( result, nc, nb);
				}
			}else{
				Lit  a = polarityClausify( FA_x(f));
				Lit  b = polarityClausify( FA_y(f));
				Lit  c = polarityClausify( FA_c(f));
				Lit na = polarityClausify(~FA_x(f));
				Lit nb = polarityClausify(~FA_y(f));
				Lit nc = polarityClausify(~FA_c(f));

				//printf("sum:\n");
				if (!sign(f)){
					clause(~result, nc,  na,  b);
					clause(~result, nc,   a, nb);
					clause(~result,  c,  na, nb);
					clause(~result,  c,   a,  b);
				}else{
					clause( result, nc,  na, nb);
					clause( result, nc,   a,  b);
					clause( result,  c,  na,  b);
					clause( result,  c,   a, nb);
				}
			}
		}
		result = Lit(var(result),sign(f));
		vmapp.set(f,result);
	}

	assert(result != lit_Undef);

	return result;
}


Lit Clausifier::basicClausify(Formula f)
{
    Var result = var_Undef;

    if (Atom_p(f)){
        assert(!Const_p(f));
        result = index(f);
    }else if (vmap.at(f) != var_Undef && !s.varElimed(vmap.at(f))){
        result = vmap.at(f);
    }else{
		result = s.newVar();
        Lit p  = Lit(result);
        if (Bin_p(f)){

            if (op(f) == op_And){
				formulaVec conj;
                collect(f, conj);
                assert(conj.size() > 1);
				for (formulaVec::size_type i = 0; i < conj.size(); i++)
                    clause(~p,basicClausify(conj[i]));

                tmp_clause.clear();
				tmp_clause.push_back(p);
				for (formulaVec::size_type i = 0; i < conj.size(); i++)
					tmp_clause.push_back(~basicClausify(conj[i]));
                s.addClause(tmp_clause);
            }else{

                Lit l = basicClausify(left (f));
                Lit r = basicClausify(right(f));

                //printf("equiv:\n");
                assert(op(f) == op_Equiv);
                clause(~p, ~l,  r);
                clause(~p,  l, ~r);
                clause( p, ~l, ~r);
                clause( p,  l,  r);
            }
        }else if (ITE_p(f)){
            Lit c = basicClausify(cond(f));
            Lit a = basicClausify(tt  (f));
            Lit b = basicClausify(ff  (f));

            clause(~p, ~c,  a);
            clause(~p,  c,  b);
            clause( p, ~c, ~a);
            clause( p,  c, ~b);

			// not neccessary but increase strength of unit propagation !!
			clause(~a, ~b,  p);
			clause( a,  b, ~p);
        }else{
            assert(FA_p(f));

            Lit a = basicClausify(FA_x(f));
            Lit b = basicClausify(FA_y(f));
            Lit c = basicClausify(FA_c(f));

            if (isCarry(f)){
				//printf("carry:\n");
                clause(~p,  a,  b);
                clause(~p,  c,  a);
                clause(~p,  c,  b);
                clause( p, ~c, ~a);
                clause( p, ~c, ~b);
                clause( p, ~a, ~b);
            }else{
                //printf("sum:\n");
                clause(~p, ~c,  ~a,  b);
                clause(~p, ~c,   a, ~b);
                clause(~p,  c,  ~a, ~b);
                clause(~p,  c,   a,  b);
                clause( p, ~c,  ~a, ~b);
                clause( p, ~c,   a,  b);
                clause( p,  c,  ~a,  b);
                clause( p,  c,   a, ~b);
            }
        }
        vmap.set(f,result);
    }

    assert(result != var_Undef);

    return Lit(result,sign(f));
}


void clausify(Clasp::ClauseCollector& s, const Formula& f, Lit& out)
{
    Clausifier c(s);
	c.usage(f);
	//out = c.basicClausify(f);
	out = c.polarityClausify(f);
}


void clausify(Clasp::ClauseCollector& s, const Formula& f)
{
	Lit out;
	clausify(s, f, out);
	s.addUnit(out);
}

