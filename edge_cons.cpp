#include "edge_cons.h"
#include <cassert>
#include <iostream>
#include <tuple>
#include <algorithm>

#include "formula_in_bdd.h"
#include "formula/af_utils.h"
#include "carchecker.h"
#include "preprocess.h"

edgeCons::edgeCons(DdNode *src_bdd, aalta_formula *state_af, aalta_formula *acc_edge)
    : state_af_(state_af), blocked_Y_(aalta_formula::TRUE()),
      status_(Dfs_incomplete), current_Y_idx_(-1)
{
    unordered_map<ull, XCons *> bdd_XCons;
    unordered_map<ull, vector<DdNode *> *> XCons_related_succ;
    queue<tuple<DdNode *, aalta_formula *, bool>> q;
    aalta_formula *acc_or_s = aalta_formula(aalta_formula::Or, acc_edge, state_af).unique();
    aalta_formula *xxxx = aalta_formula(aalta_formula::And, edgeNotToFalse(state_af)->simplify(), acc_or_s).unique();
    q.push({src_bdd, NULL, false});

    while (!q.empty()) /* do BFS!!! */
    {
        DdNode *node = std::get<0>(q.front());
        aalta_formula *af_Y = std::get<1>(q.front());
        bool is_complement = std::get<2>(q.front());
        q.pop();

        if (!FormulaInBdd::is_Y_var(node))
        {
            DdNode *true_node = is_complement ? Cudd_Not(node) : node;

            if (af_Y == NULL)
                af_Y = aalta_formula::TRUE();
            Y_parts_.push_back(af_Y);

            if (bdd_XCons.find(ull(true_node)) == bdd_XCons.end())
            {
                XCons *x_cons = new XCons(true_node, src_bdd, xxxx, af_Y);
                bdd_XCons.insert({ull(true_node), x_cons});
                vector<DdNode *> *related_succ = new vector<DdNode *>();
                x_cons->get_related_succ(*related_succ);
                XCons_related_succ[ull(x_cons)] = related_succ;
            }
            X_cons_.push_back(bdd_XCons[ull(true_node)]);
            for (auto it : *XCons_related_succ[ull(X_cons_.back())])
                succ_bddP_to_idx_.insert({ull(it), X_cons_.size() - 1});
            continue;
        }

        aalta_formula *cur_Y = FormulaInBdd::get_af_var(Cudd_NodeReadIndex(node));
        aalta_formula *not_cur_Y = aalta_formula(aalta_formula::Not, NULL, cur_Y).unique();
        aalta_formula *T_afY = af_Y == NULL ? cur_Y : aalta_formula(aalta_formula::And, af_Y, cur_Y).unique();
        aalta_formula *E_afY = af_Y == NULL ? not_cur_Y : aalta_formula(aalta_formula::And, af_Y, not_cur_Y).unique();

        q.push({Cudd_T(node), T_afY, is_complement ^ Cudd_IsComplement(node)});
        q.push({Cudd_E(node), E_afY, is_complement ^ Cudd_IsComplement(node)});
    }
    for (const auto &it : XCons_related_succ)
        delete it.second;
    for (int i = 0; i < X_cons_.size(); ++i)
        if (X_cons_[i]->get_status() == Ewin)
            // ewin_Y_idx_.insert(i);
            insert_ewin_Y_idx(i);
        else if (X_cons_[i]->get_status() == Swin)
        {
            status_ = Swin;
            return;
        }
        else if (X_cons_[i]->get_status() == Dfs_complete)
            insert_dfs_complete_Y_idx(i);
    if (ewin_Y_idx_.size() == Y_parts_.size())
        status_ = Ewin;
    else if (ewin_Y_idx_.size() + dfs_complete_Y_idx_.size() == Y_parts_.size())
        status_ = Dfs_complete;
    else
        resizeContainers();
}

edgeCons::~edgeCons()
{
    vector<ull> tmp;
    for (auto it : X_cons_)
        tmp.push_back(ull(it));
    sort(tmp.begin(), tmp.end());
    auto uit = unique(tmp.begin(), tmp.end());
    for (auto it = tmp.begin(); it < uit; ++it)
        delete (XCons *)(*it);
}

XCons::XCons(DdNode *root, DdNode *state_bddp, aalta_formula *state_af, aalta_formula *af_Y)
    : current_X_idx_(-1), status_(Dfs_incomplete) // blocked_X_(aalta_formula::TRUE())
{
    queue<tuple<DdNode *, aalta_formula *, bool>> q;
    q.push({root, NULL, false});

    while (!q.empty()) /* do BFS!!! */
    {
        DdNode *node = std::get<0>(q.front());
        aalta_formula *af_X = std::get<1>(q.front());
        bool is_complement = std::get<2>(q.front());
        q.pop();

        if (!FormulaInBdd::is_X_var(node))
        {
            if (af_X == NULL)
                af_X = aalta_formula::TRUE();
            X_parts_.push_back(af_X);

            aalta_formula *edge_af = aalta_formula(aalta_formula::And, af_X, af_Y).unique();
            unordered_set<int> edge_var_set;
            edge_af->to_set(edge_var_set);
            fill_in_edgeset(edge_var_set);
            aalta_formula *succ_state_af;
            if (IsAcc(state_af, edge_var_set))
                succ_state_af = aalta_formula::TRUE();
            else
                succ_state_af = FormulaProgression(state_af, edge_var_set); //->simplify();
            DdNode *succ_state_bdd = FormulaInBdd(succ_state_af).GetBddPointer();
            successors_.push_back(succ_state_bdd);

            if (succ_state_bdd == state_bddp ||
                Syn_Frame::ewin_state_bdd_set.find(ull(succ_state_bdd)) != Syn_Frame::ewin_state_bdd_set.end())
            {
                status_ = Ewin;
                return;
            }
            else if (Syn_Frame::swin_state_bdd_set.find(ull(succ_state_bdd)) != Syn_Frame::swin_state_bdd_set.end())
                insert_swin_X_idx(X_parts_.size() - 1);
            else if (Syn_Frame::dfs_complete_state_bdd_set.find(ull(succ_state_bdd)) != Syn_Frame::dfs_complete_state_bdd_set.end())
                insert_searched_X_idx(X_parts_.size() - 1);

            succ_bddP_to_idx_.insert({ull(succ_state_bdd), successors_.size() - 1});
            continue;
        }

        aalta_formula *cur_X = FormulaInBdd::get_af_var(Cudd_NodeReadIndex(node));
        aalta_formula *not_cur_X = aalta_formula(aalta_formula::Not, NULL, cur_X).unique();
        aalta_formula *T_afX = af_X == NULL ? cur_X : aalta_formula(aalta_formula::And, af_X, cur_X).unique();
        aalta_formula *E_afX = af_X == NULL ? not_cur_X : aalta_formula(aalta_formula::And, af_X, not_cur_X).unique();

        q.push({Cudd_T(node), T_afX, is_complement ^ Cudd_IsComplement(node)});
        q.push({Cudd_E(node), E_afX, is_complement ^ Cudd_IsComplement(node)});
    }
    if (swin_X_idx_.size() == X_parts_.size())
        status_ = Swin;
    else if (swin_X_idx_.size() + searched_X_idx_.size() == X_parts_.size())
        status_ = Dfs_complete;
    else
        resizeContainers();
}

void XCons::get_related_succ(vector<DdNode *> &related_succ)
{
    for (const auto &p : succ_bddP_to_idx_)
        related_succ.push_back((DdNode *)(p.first));
}

void edgeCons::processSignal(Signal sig, DdNode *succ)
{
    if (sig == To_ewin)
    {
        auto range = succ_bddP_to_idx_.equal_range(ull(succ));
        for (auto it = range.first; it != range.second; ++it)
            insert_ewin_Y_idx(it->second);
        if (ewin_Y_idx_.size() == Y_parts_.size())
            status_ = Ewin;
        else if ((ewin_Y_idx_.size() + dfs_complete_Y_idx_.size()) ==
                 Y_parts_.size())
            status_ = Dfs_complete;
        current_Y_idx_ = -1;
    }
    else if (sig == To_swin)
    {
        auto range = succ_bddP_to_idx_.equal_range(ull(succ));
        for (auto it = range.first; it != range.second; ++it)
        {
            X_cons_[it->second]->processSignal(To_swin, succ);
            if (X_cons_[it->second]->get_status() == Swin)
            {
                status_ = Swin;
                current_Y_idx_ = -1;
                return;
            }
            else if (X_cons_[it->second]->get_status() == Dfs_complete)
            {
                insert_dfs_complete_Y_idx(it->second);
            }
        }
        if ((ewin_Y_idx_.size() + dfs_complete_Y_idx_.size()) ==
            Y_parts_.size())
            status_ = Dfs_complete;
        if (X_cons_[current_Y_idx_]->get_status() != Dfs_incomplete)
            current_Y_idx_ = -1;
    }
    else if (sig == Pending)
    {
        auto range = succ_bddP_to_idx_.equal_range(ull(succ));
        for (auto it = range.first; it != range.second; ++it)
        {
            X_cons_[it->second]->processSignal(Pending, succ);
            if (X_cons_[it->second]->get_status() == Dfs_complete)
                insert_dfs_complete_Y_idx(it->second);
        }
        if ((ewin_Y_idx_.size() + dfs_complete_Y_idx_.size()) ==
            Y_parts_.size())
            status_ = Dfs_complete;
        if (X_cons_[current_Y_idx_]->get_status() != Dfs_incomplete)
            current_Y_idx_ = -1;
    }
    else
    {
        assert(current_Y_idx_ == -1);
        status_ = dfs_complete_Y_idx_.empty() ? Ewin : Dfs_complete;
        // else
        // {
        //     assert(X_cons_[current_Y_idx_]->get_status() == Dfs_incomplete);
        //     for (int i = 0; i < X_cons_.size(); ++i)
        //         if (X_cons_[i] == X_cons_[current_Y_idx_])
        //             insert_ewin_Y_idx(i);
        // }
        current_Y_idx_ = -1;
    }
}

void XCons::processSignal(Signal sig, DdNode *succ)
{
    assert(sig != To_ewin && sig != Unsat);
    if (sig == To_swin)
    {
        auto range = succ_bddP_to_idx_.equal_range(ull(succ));
        for (auto it = range.first; it != range.second; ++it)
            insert_swin_X_idx(it->second);
        if (swin_X_idx_.size() == X_parts_.size())
            status_ = Swin;
        else if (swin_X_idx_.size() + searched_X_idx_.size() == X_parts_.size())
            status_ = Dfs_complete;
    }
    else if (sig == Pending)
    {
        auto range = succ_bddP_to_idx_.equal_range(ull(succ));
        for (auto it = range.first; it != range.second; ++it)
            insert_searched_X_idx(it->second);
        if (swin_X_idx_.size() + searched_X_idx_.size() == X_parts_.size())
            status_ = Dfs_complete;
    }
    // else
    // {
    //     if (searched_Y_idx_.empty())
    //         status_ = Ewin;
    //     else
    //         status_ = Dfs_complete;
    // }
    current_X_idx_ = -1;
}

bool edgeCons::getEdge(unordered_set<int> &edge,
                       queue<pair<aalta_formula *, aalta_formula *>> &model)
{
    aalta_formula *edge_af = NULL;
    if (current_Y_idx_ == -1)
    {
        if (SAT_TRACE_FLAG)
        {
            if (!model.empty() && checkConflict(model.front()))
            {
                while (!model.empty())
                    model.pop();
            }
            if (model.empty())
            {
                aalta_formula *to_check = state_af_;
                // cout << "state: " << to_check->to_string() << endl;
                // cout << "constraint: " << (get_edge_cons_for_aaltaf())->to_string() << endl;
                to_check = aalta_formula(aalta_formula::And,
                                         to_check,
                                         blocked_Y_)
                               .unique();
                // to_check = to_check->nnf();
                to_check = to_check->add_tail();
                to_check = to_check->remove_wnext();
                to_check = to_check->simplify();
                to_check = to_check->split_next();
                CARChecker checker(to_check, false, true);
                if (checker.check())
                {
                    const vector<pair<aalta_formula *, aalta_formula *>> *evidence = checker.get_model_for_synthesis();
                    // checker.print_evidence();
                    for (auto it = evidence->begin(); it < evidence->end(); ++it)
                        model.push(*it);
                }
                else
                {
                    processSignal(Unsat, NULL);
                    return false;
                }
            }
            assert(!model.empty());
            current_Y_idx_ = find_match_Y_idx((model.front()).second);
            model.pop();
        }
        else
        {
            if (current_Y_idx_ == -1)
                for (int i = 0; i < Y_parts_.size(); ++i)
                    if (ewin_Y_idx_.find(i) == ewin_Y_idx_.end() &&
                        dfs_complete_Y_idx_.find(i) == dfs_complete_Y_idx_.end())
                    {
                        current_Y_idx_ = i;
                        break;
                    }
        }
    }
    aalta_formula *af_Y = Y_parts_[current_Y_idx_];
    aalta_formula *af_X = X_cons_[current_Y_idx_]->getEdge();
    edge_af = aalta_formula(aalta_formula::And, af_X, af_Y).unique()->simplify();
    edge_af->to_set(edge);
    // cout<<edge_af->to_string()<<endl;
    fill_in_edgeset(edge);
    return true;
}

aalta_formula *XCons::getEdge()
{
    assert(current_X_idx_ == -1);
    for (int i = 0; i < X_parts_.size(); ++i)
        if (swin_X_idx_.find(i) == swin_X_idx_.end() &&
            searched_X_idx_.find(i) == searched_X_idx_.end())
        {
            current_X_idx_ = i;
            break;
        }
    return X_parts_[current_X_idx_];
}

// aalta_formula *edgeCons::set_search_direction(const pair<aalta_formula *, aalta_formula *> &XY)
// {
//     assert(SAT_TRACE_FLAG && current_Y_idx_ == -1);
//     current_Y_idx_ = find_match_Y_idx(XY.second);
//     aalta_formula *X = X_cons_[current_Y_idx_]->set_search_direction(XY.first);
//     if (X == NULL)
//         return NULL;
//     else
//         return aalta_formula(aalta_formula::And, Y_parts_[current_Y_idx_], X).unique();
// }

bool edgeCons::checkSwinForBackwardSearch()
{
    bool is_swin = false;
    for (auto it : dfs_complete_Y_idx_)
        if ((X_cons_[it]->checkSwinForBackwardSearch()))
        {
            is_swin = true;
            break;
        }
    return is_swin;
}

bool XCons::checkSwinForBackwardSearch()
{
    bool is_swin = true;
    for (auto it : searched_X_idx_)
        if (Syn_Frame::swin_state_bdd_set.find(ull(successors_[it])) ==
            Syn_Frame::swin_state_bdd_set.end())
        {
            is_swin = false;
            break;
        }
    return is_swin;
}

int edgeCons::find_match_Y_idx(aalta_formula *Y)
{
    // get_edge_cons_for_aaltaf() guarantee that
    // Dfs_complete X will not appear again.
    unordered_set<int> target_y;
    Y->to_set(target_y);
    for (int i = 0; i < Y_parts_.size(); ++i)
        if (ewin_Y_idx_.find(i) == ewin_Y_idx_.end() &&
            dfs_complete_Y_idx_.find(i) == dfs_complete_Y_idx_.end())
        {
            unordered_set<int> tmp;
            Y_parts_[i]->to_set(tmp);
            if (isCompatible(&target_y, &tmp))
                return i;
        }
    assert(false);
}

void edgeCons::insert_ewin_Y_idx(int y)
{
    if (ewin_Y_idx_.find(y) == ewin_Y_idx_.end())
    {
        ewin_Y_idx_.insert(y);
        aalta_formula *not_Y = aalta_formula(aalta_formula::Not, NULL, Y_parts_[y]).nnf();
        blocked_Y_ = (aalta_formula(aalta_formula::And, blocked_Y_, not_Y).simplify())->unique();
    }
}

void edgeCons::insert_dfs_complete_Y_idx(int y)
{
    if (dfs_complete_Y_idx_.find(y) == dfs_complete_Y_idx_.end())
    {
        dfs_complete_Y_idx_.insert(y);
        aalta_formula *not_Y = aalta_formula(aalta_formula::Not, NULL, Y_parts_[y]).nnf();
        blocked_Y_ = (aalta_formula(aalta_formula::And, blocked_Y_, not_Y).simplify())->unique();
    }
}

void XCons::insert_swin_X_idx(int x)
{
    if (swin_X_idx_.find(x) == swin_X_idx_.end())
    {
        swin_X_idx_.insert(x);
        // aalta_formula *not_X = aalta_formula(aalta_formula::Not, NULL, X_parts_[x]).nnf();
        // blocked_X_ = (aalta_formula(aalta_formula::And, blocked_X_, not_X).simplify())->unique();
    }
}
void XCons::insert_searched_X_idx(int x)
{
    if (searched_X_idx_.find(x) == searched_X_idx_.end())
    {
        searched_X_idx_.insert(x);
        // aalta_formula *not_X = aalta_formula(aalta_formula::Not, NULL, X_parts_[x]).nnf();
        // blocked_X_ = (aalta_formula(aalta_formula::And, blocked_X_, not_X).simplify())->unique();
    }
}

bool isCompatible(unordered_set<int> *edge1, unordered_set<int> *edge2)
{
    unordered_set<int> *smaller_set = edge1, *bigger_set = edge2;
    if ((smaller_set->size()) > (bigger_set->size()))
        smaller_set = edge2, bigger_set = edge1;
    for (auto it : (*smaller_set))
        if (bigger_set->find(-it) != bigger_set->end())
            return false;
    return true;
}

// aalta_formula *edgeCons::get_edge_cons_for_aaltaf()
// {
//     if (current_Y_idx_ == -1)
//         return blocked_Y_;
//     return aalta_formula(aalta_formula::And,
//                          Y_parts_[current_Y_idx_],
//                          X_cons_[current_Y_idx_]->get_blocked_X())
//         .unique();
// }

aalta_formula *XCons::set_search_direction(aalta_formula *X)
{
    assert(SAT_TRACE_FLAG && current_X_idx_ == -1);
    current_X_idx_ = find_match_X_idx(X);
    if (current_X_idx_ == -1)
        return NULL;
    return X_parts_[current_X_idx_];
}

int XCons::find_match_X_idx(aalta_formula *X)
{
    unordered_set<int> target_x;
    X->to_set(target_x);
    for (int i = 0; i < X_parts_.size(); ++i)
        if (swin_X_idx_.find(i) == swin_X_idx_.end() &&
            searched_X_idx_.find(i) == searched_X_idx_.end())
        {
            unordered_set<int> tmp;
            X_parts_[i]->to_set(tmp);
            if (isCompatible(&target_x, &tmp))
                return i;
        }
    return -1; // fail to find
}
