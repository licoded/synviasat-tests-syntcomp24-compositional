#pragma once

#include <vector>
#include <iostream>
#include "formula/aalta_formula.h"
#include "carchecker.h"

using namespace aalta;
using namespace std;
// if swin directly, return NULL
// else, return some accepting edge
aalta::aalta_formula *preprocessAcc(aalta::aalta_formula *state_af);

aalta::aalta_formula *edgeNotToFalse(aalta::aalta_formula *state_af);

aalta::aalta_formula *mySimplify(aalta::aalta_formula *state_af);

enum Ternary
{
    Tt,
    Ff,
    Un
};
inline Ternary Calculate(int op, Ternary l_val, Ternary r_val)
{
    if (op == aalta_formula::And)
    {
        if (l_val == Tt)
            return r_val;
        if (r_val == Tt)
            return l_val;
        if (l_val == Ff || r_val == Ff)
            return Ff;
    }
    else
    {
        if (l_val == Ff)
            return r_val;
        if (r_val == Ff)
            return l_val;
        if (l_val == Tt || r_val == Tt)
            return Tt;
    }
    return Un;
}

inline aalta::aalta_formula *int_to_aalta(int lit)
{
    if (lit > 0)
        return aalta_formula(lit, NULL, NULL).unique();
    else
        return aalta_formula(aalta_formula::Not, NULL,
                             aalta_formula(-lit, NULL, NULL).unique())
            .unique();
}

inline const std::vector<std::pair<aalta::aalta_formula *, aalta::aalta_formula *>> *
isSat(aalta_formula *s, aalta_formula *b)
{ // cout<<s->to_string()<<", "<<b->to_string()<<endl;
    s = (aalta_formula(aalta_formula::And, s, b).unique())->simplify();
    s = s->add_tail();
    s = s->remove_wnext();
    s = s->simplify();
    s = s->split_next();
    // cout<<s->to_string()<<endl;
    CARChecker checker(s, false, true);
    if (checker.check())
        return checker.get_model_for_synthesis();
    return NULL;
}

inline bool isFG(aalta_formula *af)
{
    return af->is_future() && af->r_af()->is_globally();
}

inline aalta_formula *mk_FG(aalta_formula *f)
{
    return aalta_formula(aalta_formula::Until,
                         aalta_formula::TRUE(),
                         aalta_formula(aalta_formula::Release, aalta_formula::FALSE(), f).unique())
        .unique();
}