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
	ClauseCollector&      s;
    vec<Lit>     tmp_clause;
    vec<Formula> tmp_marked;

	Clausifier(ClauseCollector& _s) : s(_s) {}

    static /*WARNING*/ CMap<int>      occ;
    static /*WARNING*/ CMap<Var>      vmap;
    static /*WARNING*/ CMap<Lit,true> vmapp;
    FMap<bool>   seen;

    inline void clause(Lit a, Lit b) {
        tmp_clause.clear(); tmp_clause.push(a); tmp_clause.push(b); s.addClause(tmp_clause); }
    inline void clause(Lit a, Lit b, Lit c) {
        tmp_clause.clear(); tmp_clause.push(a); tmp_clause.push(b); tmp_clause.push(c); s.addClause(tmp_clause); }
    inline void clause(Lit a, Lit b, Lit c, Lit d) {
        tmp_clause.clear(); tmp_clause.push(a); tmp_clause.push(b); tmp_clause.push(c); tmp_clause.push(d); s.addClause(tmp_clause); }


    void  usage  (Formula f);
    void _collect(Formula f, vec<Formula>& out);
    void  collect(Formula f, vec<Formula>& out);

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

void Clausifier::collect(Formula f, vec<Formula>& out)
{
    tmp_marked.clear();
    _collect(left(f), out);
    _collect(right(f),out);
    for (int i = 0; i < tmp_marked.size(); i++)
        seen.set(tmp_marked[i],false);
}

void Clausifier::_collect(Formula f, vec<Formula>& out)
{
    if (!seen.at(f)){
        seen.set(f,true);
        tmp_marked.push(f);
        if (Bin_p(f) && op(f) == op_And && !sign(f) && occ.at(f) == 1){
            _collect(left(f) ,out);
            _collect(right(f),out);
        }
        else
            out.push(f);
    }
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
                vec<Formula> conj;
                collect(f, conj);
                assert(conj.size() > 1);
                for (int i = 0; i < conj.size(); i++)
                    clause(~p,basicClausify(conj[i]));

                tmp_clause.clear();
                tmp_clause.push(p);
                for (int i = 0; i < conj.size(); i++)
                    tmp_clause.push(~basicClausify(conj[i]));
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

            // not neccessary !!
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


void clausify(ClauseCollector& s, const vec<Formula>& fs, vec<Lit>& out)
{
    Clausifier c(s);

    for (int i = 0; i < fs.size(); i++)
        c.usage(fs[i]);

	for (int i = 0; i < fs.size(); i++)
		out.push(c.basicClausify(fs[i]));
}


void clausify(ClauseCollector& s, const vec<Formula>& fs)
{
    vec<Lit>  out;
    clausify(s, fs, out);
	//for (int i = 0; i < out.size(); i++)
	//    s.addUnit(out[i]);
}

