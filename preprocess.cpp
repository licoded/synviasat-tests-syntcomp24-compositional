#include "preprocess.h"
#include <cassert>
#include <cmath>
#include <unordered_set>
#include "formula/af_utils.h"
#include "synthesis.h"
#include "formula_in_bdd.h"
#include "utility.h"

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

// aalta_formula *preprocessAcc(aalta_formula *state_af)
// {
//     aalta_formula *projected_af = projectOneStep(state_af)->simplify();
//     DdNode *af_bdd = FormulaInBdd::ConstructBdd(projected_af);
//     DdNode *neg_af_bdd = Cudd_Not(af_bdd);
//     Cudd_Ref(neg_af_bdd);
//     Cudd_RecursiveDeref(FormulaInBdd::global_bdd_manager_, af_bdd);
//     DdNode *exist_Y = Cudd_bddExistAbstract(FormulaInBdd::global_bdd_manager_, neg_af_bdd, FormulaInBdd::Y_cube);
//     Cudd_Ref(exist_Y);
//     bool baseSwin = (exist_Y != FormulaInBdd::TRUE_bddP_);
//     Cudd_RecursiveDeref(FormulaInBdd::global_bdd_manager_, exist_Y);
//     Cudd_RecursiveDeref(FormulaInBdd::global_bdd_manager_, neg_af_bdd);
//     return baseSwin ? NULL : projected_af;
// }

aalta::aalta_formula *edgeNotToFalse(aalta::aalta_formula *state_af)
{
    if (state_af == NULL)
        return NULL;
    switch (state_af->oper())
    {
    case aalta_formula::True:
    case aalta_formula::False:
    case aalta_formula::Not: // nnf
        return state_af;
    case aalta_formula::And:
    {
        aalta_formula *p_l = edgeNotToFalse(state_af->l_af());
        if (p_l == aalta_formula::FALSE())
            return aalta_formula::FALSE();
        aalta_formula *p_r = edgeNotToFalse(state_af->r_af());
        if (p_r == aalta_formula::FALSE())
            return aalta_formula::FALSE();
        if (p_l == aalta_formula::TRUE())
            return p_r;
        if (p_r == aalta_formula::TRUE())
            return p_l;
        return aalta_formula(aalta_formula::And, p_l, p_r).unique();
    }
    case aalta_formula::Or:
    case aalta_formula::Until:
    {
        aalta_formula *p_l = edgeNotToFalse(state_af->l_af());
        if (p_l == aalta_formula::TRUE())
            return aalta_formula::TRUE();
        aalta_formula *p_r = edgeNotToFalse(state_af->r_af());
        if (p_r == aalta_formula::TRUE())
            return aalta_formula::TRUE();
        if (p_l == aalta_formula::FALSE())
            return p_r;
        if (p_r == aalta_formula::FALSE())
            return p_l;
        return aalta_formula(aalta_formula::Or, p_l, p_r).unique();
    }
    case aalta_formula::Next:
    case aalta_formula::WNext:
        return aalta_formula::TRUE();
    case aalta_formula::Release:
        return edgeNotToFalse(state_af->r_af());
    default:
        return state_af;
    }
}

// aalta_formula *preprocessFalseState(aalta_formula *state_af)
// {
//     aalta_formula *edge_not_to_ff = edgeNotToFalse(state_af)->simplify();
//     DdNode *edge_not_to_ff_bdd = FormulaInBdd::ConstructBdd(edge_not_to_ff);
//     DdNode *forall_X = Cudd_bddUnivAbstract(FormulaInBdd::global_bdd_manager_, edge_not_to_ff_bdd, FormulaInBdd::X_cube);
//     Cudd_Ref(forall_X);
//     Cudd_RecursiveDeref(FormulaInBdd::global_bdd_manager_, edge_not_to_ff_bdd);
//     DdNode *exist_Y = Cudd_bddExistAbstract(FormulaInBdd::global_bdd_manager_, forall_X, FormulaInBdd::Y_cube);
//     Cudd_Ref(exist_Y);
//     bool ewinRightNow = (exist_Y == FormulaInBdd::FALSE_bddP_);
//     Cudd_RecursiveDeref(FormulaInBdd::global_bdd_manager_, forall_X);
//     Cudd_RecursiveDeref(FormulaInBdd::global_bdd_manager_, exist_Y);
//     return ewinRightNow ? NULL : edge_not_to_ff;
// }

aalta::aalta_formula *mySimplify_And(aalta::aalta_formula *state_af)
{
    set<aalta_formula *> conjuncts;
    vector<aalta_formula *> next, wnext, fg, global, other;
    to_conjunts(state_af, conjuncts);
    for (auto ele : conjuncts)
    {
        aalta_formula *simp = mySimplify(ele);
        auto op = simp->oper();
        if (op == aalta_formula::Next)
            next.push_back(simp->r_af());
        else if (op == aalta_formula::WNext)
            wnext.push_back(simp->r_af());
        else if (isFG(simp))
            fg.push_back(simp->r_af()->r_af());
        else if (simp->is_globally())
            global.push_back(simp->r_af());
        else
            other.push_back(simp);
    }
    aalta_formula *res = NULL;
    if (next.empty())
    {
        if (!wnext.empty())
            res = aalta_formula(aalta_formula::WNext, NULL, formula_from(wnext)).unique();
        if (!fg.empty())
        {
            aalta_formula *fg_af = mk_FG(formula_from(fg));
            res = (res == NULL) ? fg_af : aalta_formula(aalta_formula::And, res, fg_af).unique();
        }
    }
    else
    {
        if (!wnext.empty())
            next.push_back(formula_from(wnext));
        if (!fg.empty())
            next.push_back(mk_FG(formula_from(fg)));
        res = aalta_formula(aalta_formula::Next, NULL, formula_from(next)).unique();
    }
    if (!global.empty())
    {
        aalta_formula *global_af = aalta_formula(aalta_formula::Release, aalta_formula::FALSE(), formula_from(global)).unique();
        res = (res == NULL) ? global_af : aalta_formula(aalta_formula::And, res, global_af).unique();
    }
    if (!other.empty())
    {
        aalta_formula *other_af = formula_from(other);
        res = (res == NULL) ? other_af : aalta_formula(aalta_formula::And, res, other_af).unique();
    }
    return res == NULL ? aalta_formula::TRUE() : res;
}

aalta::aalta_formula *mySimplify_Or(aalta::aalta_formula *state_af)
{

    set<aalta_formula *> disjuncts;
    vector<aalta_formula *> next, wnext, fg, futrue, other;
    to_disjunts(state_af, disjuncts);
    for (auto ele : disjuncts)
    {
        aalta_formula *simp = mySimplify(ele);
        auto op = simp->oper();
        if (op == aalta_formula::Next)
            next.push_back(simp->r_af());
        else if (op == aalta_formula::WNext)
            wnext.push_back(simp->r_af());
        else if (isFG(simp))
            fg.push_back(simp->r_af()->r_af());
        else if (simp->is_future())
            futrue.push_back(simp->r_af());
        else
            other.push_back(simp);
    }
    aalta_formula *res = NULL;
    if (wnext.empty())
    {
        if (!next.empty())
            res = aalta_formula(aalta_formula::Next, NULL, formula_from_or(next)).unique();
        if (!fg.empty())
        {
            aalta_formula *fg_af = mk_FG(formula_from_or(fg));
            res = (res == NULL) ? fg_af : aalta_formula(aalta_formula::Or, res, fg_af).unique();
        }
    }
    else
    {
        if (!next.empty())
            wnext.push_back(formula_from_or(next));
        if (!fg.empty())
            wnext.push_back(mk_FG(formula_from_or(fg)));
        res = aalta_formula(aalta_formula::WNext, NULL, formula_from_or(wnext)).unique();
    }
    if (!futrue.empty())
    {
        aalta_formula *futrue_af = aalta_formula(aalta_formula::Until, aalta_formula::TRUE(), formula_from_or(futrue)).unique();
        res = (res == NULL) ? futrue_af : aalta_formula(aalta_formula::Or, res, futrue_af).unique();
    }
    if (!other.empty())
    {
        aalta_formula *other_af = formula_from_or(other);
        res = (res == NULL) ? other_af : aalta_formula(aalta_formula::Or, res, other_af).unique();
    }
    return res == NULL ? aalta_formula::FALSE() : res;
}

aalta::aalta_formula *mySimplify_Global(aalta::aalta_formula *state_af)
{
    aalta::aalta_formula *raf = state_af->r_af();
    switch (raf->oper())
    {
    case aalta_formula::WNext: // G N f = N G f
        return aalta_formula(aalta_formula::WNext, NULL,
                             aalta_formula(aalta_formula::Release, aalta_formula::FALSE(), mySimplify(raf->r_af())).unique())
            .unique();
    case aalta_formula::Until: // G F f = F G f
    {
        if (raf->l_af()->oper() == aalta_formula::True)
            return mk_FG(mySimplify(raf->r_af()));
        else
            break;
    }
    case aalta_formula::Release: // G(f1 R f2) = G f2
        return aalta_formula(aalta_formula::Release, aalta_formula::FALSE(), mySimplify(raf->r_af())).unique();
    default:
        break;
    }
    return aalta_formula(aalta_formula::Release, aalta_formula::FALSE(), mySimplify(raf)).unique();
}

aalta::aalta_formula *mySimplify_Futrue(aalta::aalta_formula *state_af)
{
    aalta::aalta_formula *raf = state_af->r_af();
    switch (raf->oper())
    {
    case aalta_formula::Next: // F X f = X F f
        return aalta_formula(aalta_formula::Next, NULL,
                             aalta_formula(aalta_formula::Until, aalta_formula::TRUE(), mySimplify(raf->r_af())).unique())
            .unique();
    case aalta_formula::Until: // F(f1 U f2) = F f2
        return aalta_formula(aalta_formula::Until, aalta_formula::TRUE(), mySimplify(raf->r_af())).unique();
    default:
        break;
    }
    return aalta_formula(aalta_formula::Until, aalta_formula::TRUE(), mySimplify(raf)).unique();
}

aalta::aalta_formula *mySimplify(aalta::aalta_formula *state_af)
{
    auto op = state_af->oper();
    switch (op)
    {
    case aalta_formula::True:
    case aalta_formula::False:
    case aalta_formula::Not:
        return state_af;
    case aalta_formula::And:
        return mySimplify_And(state_af);
    case aalta_formula::Or:
        return mySimplify_Or(state_af);
    case aalta_formula::Next:
    case aalta_formula::WNext:
        return aalta_formula(op, NULL, mySimplify(state_af->r_af())).unique();
    case aalta_formula::Until:
        return (state_af->l_af())->oper() == aalta_formula::True
                   ? mySimplify_Futrue(state_af)
                   : aalta_formula(op, mySimplify(state_af->l_af()), mySimplify(state_af->r_af())).unique();
    case aalta_formula::Release:
        return (state_af->l_af())->oper() == aalta_formula::False
                   ? mySimplify_Global(state_af)
                   : aalta_formula(op, mySimplify(state_af->l_af()), mySimplify(state_af->r_af())).unique();
    default:
        return state_af;
    }
}