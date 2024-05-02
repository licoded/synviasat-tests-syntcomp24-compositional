#include "preprocessAcc.h"
#include <cassert>
#include <unordered_set>
#include "formula/af_utils.h"
#include "synthesis.h"

using namespace std;

aalta_formula *projectOneStep(aalta_formula *af)
{
    if (af == NULL)
        return NULL;
    switch (af->oper())
    {
    case aalta_formula::True:
    case aalta_formula::False:
    case aalta_formula::Not: // nnf
        return af;
    case aalta_formula::And:
    {
        aalta_formula *p_l = projectOneStep(af->l_af());
        if (p_l == aalta_formula::FALSE())
            return aalta_formula::FALSE();
        aalta_formula *p_r = projectOneStep(af->r_af());
        if (p_r == aalta_formula::FALSE())
            return aalta_formula::FALSE();
        if (p_l == aalta_formula::TRUE())
            return p_r;
        if (p_r == aalta_formula::TRUE())
            return p_l;
        return aalta_formula(aalta_formula::And, p_l, p_r).unique();
    }
    case aalta_formula::Or:
    {
        aalta_formula *p_l = projectOneStep(af->l_af());
        if (p_l == aalta_formula::TRUE())
            return aalta_formula::TRUE();
        aalta_formula *p_r = projectOneStep(af->r_af());
        if (p_r == aalta_formula::TRUE())
            return aalta_formula::TRUE();
        if (p_l == aalta_formula::FALSE())
            return p_r;
        if (p_r == aalta_formula::FALSE())
            return p_l;
        return aalta_formula(aalta_formula::Or, p_l, p_r).unique();
    }
    case aalta_formula::Next:
        return aalta_formula::FALSE();
    case aalta_formula::WNext:
        return aalta_formula::TRUE();
    case aalta_formula::Until:
    case aalta_formula::Release:
        return projectOneStep(af->r_af());
    default:
        return af;
    }
}

Ternary testAcc(aalta_formula *s, unordered_set<int> &to_reduce, unordered_set<int> &reduced, int test_lit)
{
    assert(s != NULL);
    auto op = s->oper();
    if (op == aalta_formula::True)
        return Tt;
    else if (op == aalta_formula::False)
        return Ff;
    else if (op == aalta_formula::And || op == aalta_formula::Or)
    {
        Ternary l_val = testAcc(s->l_af(), to_reduce, reduced, test_lit);
        Ternary r_val = testAcc(s->r_af(), to_reduce, reduced, test_lit);
        return Calculate(op, l_val, r_val);
    }
    else if (op == aalta_formula::Not || op >= 11)
    { // literal
        int lit = (op >= 11) ? op : (-((s->r_af())->oper()));
        if (lit == test_lit || (-lit) == test_lit || reduced.find(lit) != reduced.end() || reduced.find(-lit) != reduced.end())
            return Un;
        else if (to_reduce.find(lit) != to_reduce.end())
            return Tt;
        else if (to_reduce.find(-lit) != to_reduce.end())
            return Ff;
        else
            return (op >= 11) ? Tt : Ff;
    }
    assert(false);
}

aalta_formula *reduceX(aalta_formula *s, aalta_formula *x)
{
    unordered_set<int> xset, reduced;
    x->to_set(xset);
    fill_in_X_edgeset(xset);
    for (auto it = xset.begin(); it != xset.end();)
    {
        if (testAcc(s, xset, reduced, (*it)) != Un)
        {
            reduced.insert(*it);
            it = xset.erase(it);
        }
        else
            ++it;
    }
    if (xset.empty())
        return aalta_formula::TRUE();
    auto it = xset.begin();
    aalta_formula *reduced_formula = int_to_aalta(*it);
    for (++it; it != xset.end(); ++it)
        reduced_formula = aalta_formula(aalta_formula::And, reduced_formula, int_to_aalta(*it)).unique();
    return reduced_formula;
}

aalta_formula *preprocessAcc(aalta_formula *state_af)
{
    aalta_formula *projected_af = projectOneStep(state_af);
    aalta_formula *blocked_X = aalta_formula::TRUE();
    const vector<pair<aalta::aalta_formula *, aalta::aalta_formula *>> *m;
    m = isSat(projected_af, blocked_X);
    aalta_formula *x, *y, *s_eliminate_y, *not_rx;
    unordered_set<int> yset;
    while (m != NULL)
    {//cout<<state_af->to_string()<<endl;
        assert(m->size() == 1);
        x = m->front().first;//cout<<x->to_string()<<endl;
        y = m->front().second;//cout<<y->to_string()<<endl;
        y->to_set(yset);
        // fill_in_Y_edgeset(yset);
        s_eliminate_y = eliminateY(projected_af, yset);//cout<<s_eliminate_y->to_string()<<endl;
        yset.clear();
        x = reduceX(s_eliminate_y, x);//cout<<x->to_string()<<endl;
        not_rx = aalta_formula(aalta_formula::Not, NULL, x).nnf();
        blocked_X = aalta_formula(aalta_formula::And, blocked_X, not_rx).unique();
        m = isSat(projected_af, blocked_X);
    }
    blocked_X = blocked_X->simplify();
    CARChecker checker(blocked_X, false, false);
    return (checker.check()) ? blocked_X : NULL;
}