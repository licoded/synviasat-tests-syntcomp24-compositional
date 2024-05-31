#include "formula_in_bdd.h"
#include <iostream>
#include <cassert>
#include <queue>
#include <vector>
#include <algorithm>

#include "formula/aalta_formula.h"
#include "deps/CUDD-install/include/cudd.h"

using namespace std;
using namespace aalta;

DdManager *FormulaInBdd::global_bdd_manager_ = NULL;
unordered_map<ull, ull> FormulaInBdd::aaltaP_to_bddP_;
// unordered_map<ull, DdNode *> FormulaInBdd::temporal_afp_to_bddP_;
// unordered_map<ull, ull> FormulaInBdd::bddP_to_afP;
unordered_map<int, ull> FormulaInBdd::bddIdx_to_aaltaP_;
unordered_set<ull> FormulaInBdd::aaltaP_map_created;
aalta_formula *FormulaInBdd::src_formula_ = NULL;
DdNode *FormulaInBdd::TRUE_bddP_;
DdNode *FormulaInBdd::FALSE_bddP_;
unsigned int FormulaInBdd::X_var_nums;
unsigned int FormulaInBdd::Y_var_nums;
unsigned int FormulaInBdd::total_var_nums;

void FormulaInBdd::InitBdd4LTLf(aalta_formula *src_formula, std::set<int> &X_vars, std::set<int> &Y_vars)
{
    src_formula_ = src_formula;
    global_bdd_manager_ = Cudd_Init(0, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    TRUE_bddP_ = Cudd_ReadOne(global_bdd_manager_);
    FALSE_bddP_ = Cudd_ReadLogicZero(global_bdd_manager_);
    Cudd_Ref(TRUE_bddP_);
    Cudd_Ref(FALSE_bddP_);
    // PrintMapInfo();
    fixXYOrder(X_vars, Y_vars);
    CreatedMap4AaltaP2BddP(src_formula_);
}

void FormulaInBdd::CreatedMap4AaltaP2BddP(aalta_formula *af)
{
    if (af == NULL)
        return;
    if (aaltaP_map_created.find(ull(af)) == aaltaP_map_created.end())
        aaltaP_map_created.insert(ull(af));
    else
        return;
    int op = af->oper();
    if (op >= 11)
        return;

    switch (op)
    {
    case aalta_formula::True:
    case aalta_formula::False:
        return;
    case aalta_formula::And:
    case aalta_formula::Or:
    {
        CreatedMap4AaltaP2BddP(af->l_af());
        CreatedMap4AaltaP2BddP(af->r_af());
        return;
    }
    case aalta_formula::Not:
    {
        CreatedMap4AaltaP2BddP(af->r_af());
        return;
    }
    }

    switch (op)
    {
    case aalta_formula::Next:
    case aalta_formula::WNext:
    {
        if (aaltaP_to_bddP_.find(ull(af)) == aaltaP_to_bddP_.end())
        {
            aaltaP_to_bddP_[ull(af)] = ull(Cudd_bddNewVar(global_bdd_manager_));
            Cudd_Ref((DdNode *)(aaltaP_to_bddP_[ull(af)]));
        }
        CreatedMap4AaltaP2BddP(af->r_af());
        return;
    }
    case aalta_formula::Until:
    case aalta_formula::Release:
    {
        aalta_formula *next_af = aalta_formula(
                                     op == aalta_formula::Until ? aalta_formula::Next : aalta_formula::WNext,
                                     NULL, af)
                                     .unique();
        if (aaltaP_to_bddP_.find(ull(next_af)) == aaltaP_to_bddP_.end())
        {
            aaltaP_to_bddP_[ull(next_af)] = ull(Cudd_bddNewVar(global_bdd_manager_));
            // bddIdx_to_aaltaP_.push_back(af);
            // bddP_to_afP[aaltaP_to_bddP_[ull(af)]] = ull(af);
            Cudd_Ref((DdNode *)(aaltaP_to_bddP_[ull(next_af)]));
        }
        CreatedMap4AaltaP2BddP(af->l_af());
        CreatedMap4AaltaP2BddP(af->r_af());
        return;
    }
    }
}

void FormulaInBdd::fixXYOrder(std::set<int> &X_vars, std::set<int> &Y_vars)
{
    X_var_nums = X_vars.size();
    Y_var_nums = Y_vars.size();
    total_var_nums = X_var_nums + Y_var_nums;
    int var_cnt = 0;
    for (auto item : Y_vars)
    {
        aalta_formula *af = aalta_formula(item, NULL, NULL).unique();
        aaltaP_map_created.insert(ull(af));
        aaltaP_to_bddP_[ull(af)] = ull(Cudd_bddNewVar(global_bdd_manager_));
        // bddP_to_afP[aaltaP_to_bddP_[ull(af)]] = ull(af);
        DdNode *ithVar = Cudd_bddIthVar(global_bdd_manager_, var_cnt);
        assert(ithVar == (DdNode *)(aaltaP_to_bddP_[ull(af)]));
        bddIdx_to_aaltaP_[var_cnt++] = ull(af);
        Cudd_Ref((DdNode *)(aaltaP_to_bddP_[ull(af)]));
    }
    for (auto item : X_vars)
    {
        aalta_formula *af = aalta_formula(item, NULL, NULL).unique();
        aaltaP_map_created.insert(ull(af));
        aaltaP_to_bddP_[ull(af)] = ull(Cudd_bddNewVar(global_bdd_manager_));
        // bddP_to_afP[aaltaP_to_bddP_[ull(af)]] = ull(af);
        DdNode *ithVar = Cudd_bddIthVar(global_bdd_manager_, var_cnt);
        assert(ithVar == (DdNode *)(aaltaP_to_bddP_[ull(af)]));
        bddIdx_to_aaltaP_[var_cnt++] = ull(af);
        Cudd_Ref((DdNode *)(aaltaP_to_bddP_[ull(af)]));
    }
}

FormulaInBdd::FormulaInBdd(aalta_formula *af) : formula_(af)
{
    aalta_formula *xnf_af = xnf(af);
    if (aaltaP_to_bddP_.find(ull(xnf_af)) == aaltaP_to_bddP_.end())
    {
        vector<aalta_formula *> conjuncts;
        to_conjunts(xnf_af, conjuncts);
        for (auto it : conjuncts)
            if (aaltaP_to_bddP_.find(ull(it)) == aaltaP_to_bddP_.end())
                aaltaP_to_bddP_[ull(it)] = ull(ConstructBdd(it));

        if (aaltaP_to_bddP_.find(ull(xnf_af)) == aaltaP_to_bddP_.end())
            aaltaP_to_bddP_[ull(xnf_af)] = ull(ConstructBdd(xnf_af));
    }
    bdd_ = (DdNode *)aaltaP_to_bddP_[ull(xnf_af)];
    // aalta_formula *xnf_af = xnf(af);
    // if (aaltaP_to_bddP_.find(ull(xnf_af)) == aaltaP_to_bddP_.end())
    //     aaltaP_to_bddP_[ull(xnf_af)] = ull(getXnfBdd(af));
    // bdd_ = (DdNode *)aaltaP_to_bddP_[ull(xnf_af)];
}

// DdNode *FormulaInBdd::getXnfBdd(aalta_formula *af)
// {
//     if (af->oper() == aalta_formula::And)
//     {
//         DdNode *l_bdd = getXnfBdd(af->l_af());
//         DdNode *r_bdd = getXnfBdd(af->r_af());
//         DdNode *cur = Cudd_bddAnd(global_bdd_manager_, l_bdd, r_bdd);
//         Cudd_Ref(cur);
//         Cudd_RecursiveDeref(global_bdd_manager_, l_bdd);
//         Cudd_RecursiveDeref(global_bdd_manager_, r_bdd);
//         return cur;
//     }
//     else if (af->oper() == aalta_formula::Or)
//     {
//         DdNode *l_bdd = getXnfBdd(af->l_af());
//         DdNode *r_bdd = getXnfBdd(af->r_af());
//         DdNode *cur = Cudd_bddOr(global_bdd_manager_, l_bdd, r_bdd);
//         Cudd_Ref(cur);
//         Cudd_RecursiveDeref(global_bdd_manager_, l_bdd);
//         Cudd_RecursiveDeref(global_bdd_manager_, r_bdd);
//         return cur;
//     }
//     else if (af->oper() == aalta_formula::Not)
//     {
//         DdNode *r_bdd = getXnfBdd(af->r_af());
//         DdNode *cur = Cudd_Not(r_bdd);
//         Cudd_Ref(cur);
//         Cudd_RecursiveDeref(global_bdd_manager_, r_bdd);
//         return cur;
//     }
//     else
//     {
//         if (temporal_afp_to_bddP_.find(ull(af)) == temporal_afp_to_bddP_.end())
//             temporal_afp_to_bddP_.insert({ull(af), ConstructBdd(xnf(af))});
//         Cudd_Ref(temporal_afp_to_bddP_[ull(af)]);
//         return temporal_afp_to_bddP_[ull(af)];
//     }
// }

DdNode *FormulaInBdd::ConstructBdd(aalta_formula *af)
{
    if (af == NULL)
        return NULL;
    if (aaltaP_to_bddP_.find(ull(af)) != aaltaP_to_bddP_.end())
    {
        Cudd_Ref((DdNode *)(aaltaP_to_bddP_[ull(af)]));
        return (DdNode *)(aaltaP_to_bddP_[ull(af)]);
    }
    int op = af->oper();
    switch (op)
    {
    case aalta_formula::True:
    {
        Cudd_Ref(TRUE_bddP_);
        return TRUE_bddP_;
    }
    case aalta_formula::False:
    {
        Cudd_Ref(FALSE_bddP_);
        return FALSE_bddP_;
    }
    case aalta_formula::Not:
    {
        DdNode *tmp = ConstructBdd(af->r_af());
        DdNode *cur = Cudd_Not(tmp);
        Cudd_Ref(cur);
        Cudd_RecursiveDeref(global_bdd_manager_, tmp);
        return cur;
    }
    case aalta_formula::Or:
    {
        DdNode *tmpL = ConstructBdd(af->l_af());
        if (tmpL == TRUE_bddP_)
        {
            Cudd_Ref(TRUE_bddP_);
            return TRUE_bddP_;
        }
        DdNode *tmpR = ConstructBdd(af->r_af());
        DdNode *cur = Cudd_bddOr(global_bdd_manager_, tmpL, tmpR);
        Cudd_Ref(cur);
        Cudd_RecursiveDeref(global_bdd_manager_, tmpL);
        Cudd_RecursiveDeref(global_bdd_manager_, tmpR);
        return cur;
    }
    case aalta_formula::And:
    {
        DdNode *tmpL = ConstructBdd(af->l_af());
        if (tmpL == FALSE_bddP_)
        {
            Cudd_Ref(FALSE_bddP_);
            return FALSE_bddP_;
        }
        DdNode *tmpR = ConstructBdd(af->r_af());
        DdNode *cur = Cudd_bddAnd(global_bdd_manager_, tmpL, tmpR);
        Cudd_Ref(cur);
        Cudd_RecursiveDeref(global_bdd_manager_, tmpL);
        Cudd_RecursiveDeref(global_bdd_manager_, tmpR);
        // if(aaltaP_to_bddP_.size()<50)
        // {
        //     Cudd_Ref(cur);
        //     aaltaP_to_bddP_.insert({ull(af),ull(cur)});
        // }
        return cur;
    }
    default:
    {
        DdNode *cur_bdd_ptr = (DdNode *)(aaltaP_to_bddP_[ull(af)]);
        Cudd_Ref(cur_bdd_ptr);
        return cur_bdd_ptr;
    }
    }
}

// check whether af1 implies af2
bool FormulaInBdd::Implies(aalta_formula *af1, aalta_formula *af2)
{
    DdNode *f1 = ConstructBdd(af1);
    DdNode *f2 = ConstructBdd(af2);
    DdNode *not_f2 = Cudd_Not(f2);
    Cudd_Ref(not_f2);
    Cudd_RecursiveDeref(global_bdd_manager_, f2);
    DdNode *f1_and_not_f2 = Cudd_bddAnd(global_bdd_manager_, f1, not_f2);
    Cudd_Ref(f1_and_not_f2);
    Cudd_RecursiveDeref(global_bdd_manager_, f1);
    Cudd_RecursiveDeref(global_bdd_manager_, not_f2);
    Cudd_RecursiveDeref(global_bdd_manager_, f1_and_not_f2);
    return (f1_and_not_f2 == FALSE_bddP_);
}

bool FormulaInBdd::Implies(DdNode *f1, DdNode *f2)
{
    DdNode *not_f2 = Cudd_Not(f2);
    Cudd_Ref(not_f2);
    DdNode *f1_and_not_f2 = Cudd_bddAnd(global_bdd_manager_, f1, not_f2);
    Cudd_Ref(f1_and_not_f2);
    Cudd_RecursiveDeref(global_bdd_manager_, not_f2);
    Cudd_RecursiveDeref(global_bdd_manager_, f1_and_not_f2);
    return (f1_and_not_f2 == FALSE_bddP_);
}

void FormulaInBdd::PrintMapInfo()
{
    cout << "src formula:" << src_formula_->to_string() << "\nPropositional Atoms:\n";
    for (auto it = FormulaInBdd::aaltaP_to_bddP_.begin(); it != FormulaInBdd::aaltaP_to_bddP_.end(); ++it)
        cout << ((aalta_formula *)(it->first))->to_string() << endl;
}

bool FormulaInBdd::check_conflict(aalta_formula *af1, aalta_formula *af2)
{
    // CreatedMap4AaltaP2BddP(af1, false);
    DdNode *f1 = ConstructBdd(af1);
    // CreatedMap4AaltaP2BddP(af2, false);
    DdNode *f2 = ConstructBdd(af2);
    DdNode *f1_and_f2 = Cudd_bddAnd(global_bdd_manager_, f1, f2);
    Cudd_Ref(f1_and_f2);
    Cudd_RecursiveDeref(global_bdd_manager_, f1);
    Cudd_RecursiveDeref(global_bdd_manager_, f2);
    Cudd_RecursiveDeref(global_bdd_manager_, f1_and_f2);
    return f1_and_f2 == FALSE_bddP_;
}
