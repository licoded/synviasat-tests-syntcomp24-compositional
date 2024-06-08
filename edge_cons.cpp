#include "edge_cons.h"
#include <cassert>
#include <iostream>
#include <tuple>
#include <algorithm>

#include "formula_in_bdd.h"
#include "formula/af_utils.h"
#include "carchecker.h"

edgeCons::edgeCons(DdNode *src_bdd, aalta_formula *state_af, aalta_formula *neg_acc_X)
    : state_af_(state_af), blocked_X_(neg_acc_X), traved_X_(aalta_formula::FALSE()),
      status_(Dfs_incomplete), current_X_idx_(-1)
{
    unordered_map<ull, YCons *> bdd_YCons;
    unordered_map<ull, vector<DdNode *> *> YCons_related_succ;
    queue<tuple<DdNode *, aalta_formula *, bool>> q;
    aalta_formula*acc_X=aalta_formula(aalta_formula::Not,NULL,neg_acc_X).nnf();
    aalta_formula*acc_X_or_s=aalta_formula(aalta_formula::Or,acc_X,state_af).unique();
    q.push({src_bdd, NULL, false});

    while (!q.empty()) /* do BFS!!! */
    {
        DdNode *node = std::get<0>(q.front());
        aalta_formula *af_X = std::get<1>(q.front());
        bool is_complement = std::get<2>(q.front());
        q.pop();

        if (!FormulaInBdd::is_X_var(node))
        {
            DdNode *true_node = is_complement ? Cudd_Not(node) : node;

            if (af_X == NULL)
                af_X = aalta_formula::TRUE();
            X_parts_.push_back(af_X);

            if (bdd_YCons.find(ull(true_node)) == bdd_YCons.end())
            {
                YCons *y_cons = new YCons(true_node, src_bdd, acc_X_or_s, af_X);
                bdd_YCons.insert({ull(true_node), y_cons});
                vector<DdNode *> *related_succ = new vector<DdNode *>();
                y_cons->get_related_succ(*related_succ);
                YCons_related_succ[ull(y_cons)] = related_succ;
            }
            Y_cons_.push_back(bdd_YCons[ull(true_node)]);
            if (Y_cons_.back()->hasTravAllEdges())
                insert_trav_all_afX_X_idx(Y_cons_.size() - 1);
            for (auto it : *YCons_related_succ[ull(Y_cons_.back())])
                succ_bddP_to_idx_.insert({ull(it), Y_cons_.size() - 1});
            for (auto it : *YCons_related_succ[ull(Y_cons_.back())])
                succ_bddP_to_idx_vec_.push_back({ull(it), Y_cons_.size() - 1});
            continue;
        }

        aalta_formula *cur_X = FormulaInBdd::get_af_var(Cudd_NodeReadIndex(node));
        aalta_formula *not_cur_X = aalta_formula(aalta_formula::Not, NULL, cur_X).unique();
        aalta_formula *T_afX = af_X == NULL ? cur_X : aalta_formula(aalta_formula::And, af_X, cur_X).unique();
        aalta_formula *E_afX = af_X == NULL ? not_cur_X : aalta_formula(aalta_formula::And, af_X, not_cur_X).unique();

        q.push({Cudd_T(node), T_afX, is_complement ^ Cudd_IsComplement(node)});
        q.push({Cudd_E(node), E_afX, is_complement ^ Cudd_IsComplement(node)});
    }
    for (const auto &it : YCons_related_succ)
        delete it.second;
    for (int i = 0; i < Y_cons_.size(); ++i)
        if (Y_cons_[i]->get_status() == Swin)
            swin_X_idx_.insert(i);
        else if (Y_cons_[i]->get_status() == Ewin)
        {
            status_ = Ewin;
            return;
        }
    if (swin_X_idx_.size() == X_parts_.size())
        status_ = Swin;
    resizeContainers();
}

edgeCons::~edgeCons()
{
    vector<ull> tmp;
    for (auto it : Y_cons_)
        tmp.push_back(ull(it));
    sort(tmp.begin(), tmp.end());
    auto uit = unique(tmp.begin(), tmp.end());
    for (auto it = tmp.begin(); it < uit; ++it)
        delete (YCons *)(*it);
}

YCons::YCons(DdNode *root, DdNode *state_bddp, aalta_formula *state_af, aalta_formula *af_X)
    : blocked_Y_(aalta_formula::TRUE()), current_Y_idx_(-1), status_(Dfs_incomplete),
        swin_Y_(aalta_formula::FALSE()), traved_Y_(aalta_formula::FALSE())
{
    queue<tuple<DdNode *, aalta_formula *, bool>> q;
    q.push({root, NULL, false});

    while (!q.empty()) /* do BFS!!! */
    {
        DdNode *node = std::get<0>(q.front());
        aalta_formula *af_Y = std::get<1>(q.front());
        bool is_complement = std::get<2>(q.front());
        q.pop();

        if (!FormulaInBdd::is_Y_var(node))
        {
            if (af_Y == NULL)
                af_Y = aalta_formula::TRUE();
            Y_parts_.push_back(af_Y);

            aalta_formula *edge_af = aalta_formula(aalta_formula::And, af_Y, af_X).unique();
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

            if (succ_state_bdd == FormulaInBdd::TRUE_bddP_)
            {
                status_ = Swin;
                insert_trav_all_afY_Y_idx(Y_parts_.size() - 1);
                continue; // NOTE: cannot insert to succ_bddP_to_idx_ as will ERROR when dtor (e, but adding a judge in dtor is OK)
            }
            else if (succ_state_bdd == state_bddp ||
                     succ_state_bdd == FormulaInBdd::FALSE_bddP_)
            {
                insert_ewin_Y_idx(Y_parts_.size() - 1);
                insert_trav_all_afY_Y_idx(Y_parts_.size() - 1);
            }

            succ_bddP_to_idx_.insert({ull(succ_state_bdd), successors_.size() - 1});
            continue;
        }

        aalta_formula *cur_Y = FormulaInBdd::get_af_var(Cudd_NodeReadIndex(node));
        aalta_formula *not_cur_Y = aalta_formula(aalta_formula::Not, NULL, cur_Y).unique();
        aalta_formula *T_afY = af_Y == NULL ? cur_Y : aalta_formula(aalta_formula::And, af_Y, cur_Y).unique();
        aalta_formula *E_afY = af_Y == NULL ? not_cur_Y : aalta_formula(aalta_formula::And, af_Y, not_cur_Y).unique();

        q.push({Cudd_T(node), T_afY, is_complement ^ Cudd_IsComplement(node)});
        q.push({Cudd_E(node), E_afY, is_complement ^ Cudd_IsComplement(node)});
    }
    if (ewin_Y_idx_.size() == Y_parts_.size())
        status_ = Ewin;
    resizeContainers();
}

void YCons::get_related_succ(vector<DdNode *> &related_succ)
{
    for (const auto &p : succ_bddP_to_idx_)
        related_succ.push_back((DdNode *)(p.first));
}

void edgeCons::processSignal(Signal sig, DdNode *succ)
{
    if (sig == To_swin)
    {
        auto range = succ_bddP_to_idx_.equal_range(ull(succ));
        for (auto it = range.first; it != range.second; ++it)
        {
            insert_swin_X_idx(it->second);
            Y_cons_[it->second]->processSignal(To_swin, succ);
            // NOTE: the following codes are useless, as we only need do in edgeCons::getEdge_wholeDFA
            // if (Y_cons_[it->second]->hasTravAllEdges())
            // {
            //     insert_trav_all_afX_X_idx(it->second);
            // }
        }
        if (swin_X_idx_.size() == X_parts_.size())
            status_ = Swin;
        else if ((swin_X_idx_.size() + dfs_complete_X_idx_.size()) ==
                 X_parts_.size())
            status_ = Dfs_complete;
        if (!WholeDFA_FLAG)
            current_X_idx_ = -1;
        else
        {
            if (current_X_idx_ != -1)
            {
                if (Y_cons_[current_X_idx_]->hasTravAllEdges())
                {
                    insert_trav_all_afX_X_idx(current_X_idx_);
                    current_X_idx_ = -1;
                }
            }
        }
    }
    else if (sig == To_ewin)
    {
        auto range = succ_bddP_to_idx_.equal_range(ull(succ));
        for (auto it = range.first; it != range.second; ++it)
        {
            Y_cons_[it->second]->processSignal(To_ewin, succ);
            if (Y_cons_[it->second]->get_status() == Ewin)
            {
                status_ = Ewin;
                current_X_idx_ = -1;
                return;
            }
            else if (Y_cons_[it->second]->get_status() == Dfs_complete)
            {
                insert_dfs_complete_X_idx(it->second);
            }
        }
        if ((swin_X_idx_.size() + dfs_complete_X_idx_.size()) ==
            X_parts_.size())
            status_ = Dfs_complete;
        if (Y_cons_[current_X_idx_]->get_status() != Dfs_incomplete)
            current_X_idx_ = -1;
    }
    else if (sig == Pending)
    {
        auto range = succ_bddP_to_idx_.equal_range(ull(succ));
        for (auto it = range.first; it != range.second; ++it)
        {
            Y_cons_[it->second]->processSignal(Pending, succ);
            if (Y_cons_[it->second]->get_status() == Dfs_complete)
                insert_dfs_complete_X_idx(it->second);
        }
        if ((swin_X_idx_.size() + dfs_complete_X_idx_.size()) ==
            X_parts_.size())
            status_ = Dfs_complete;
        if (Y_cons_[current_X_idx_]->get_status() != Dfs_incomplete)
            current_X_idx_ = -1;
    }
    else
    {
        if (current_X_idx_ == -1)
            status_ = Ewin;
        else
        {
            Y_cons_[current_X_idx_]->processSignal(Unsat, NULL);
            if (Y_cons_[current_X_idx_]->get_status() == Ewin)
                status_ = Ewin;
            else
            {
                for (int i = 0; i < Y_cons_.size(); ++i)
                    if (Y_cons_[i] == Y_cons_[current_X_idx_])
                        insert_dfs_complete_X_idx(i);
                if (dfs_complete_X_idx_.size() + swin_X_idx_.size() == X_parts_.size())
                    status_ = Dfs_complete;
            }
        }
        current_X_idx_ = -1;
    }
}

void YCons::processSignal(Signal sig, DdNode *succ)
{
    // assert(sig != To_swin);
    if (sig == To_ewin)
    {
        auto range = succ_bddP_to_idx_.equal_range(ull(succ));
        for (auto it = range.first; it != range.second; ++it)
            insert_ewin_Y_idx(it->second);
        if (ewin_Y_idx_.size() == Y_parts_.size())
            status_ = Ewin;
        else if (ewin_Y_idx_.size() + searched_Y_idx_.size() == Y_parts_.size())
            status_ = Dfs_complete;
    }
    else if (sig == To_swin)
    {
        status_ = Swin;
        if (WholeDFA_FLAG)
        {
            auto range = succ_bddP_to_idx_.equal_range(ull(succ));
            for (auto it = range.first; it != range.second; ++it)
            {
                insert_swin_Y_idx(it->second);
                insert_trav_all_afY_Y_idx(it->second);
            }
        }
    }
    else if (sig == Pending)
    {
        auto range = succ_bddP_to_idx_.equal_range(ull(succ));
        for (auto it = range.first; it != range.second; ++it)
            insert_searched_Y_idx(it->second);
        if (ewin_Y_idx_.size() + searched_Y_idx_.size() == Y_parts_.size())
            status_ = Dfs_complete;
    }
    else
    {
        if (searched_Y_idx_.empty())
            status_ = Ewin;
        else
            status_ = Dfs_complete;
    }
    current_Y_idx_ = -1;
}

bool edgeCons::getEdge(unordered_set<int> &edge,
                       queue<pair<aalta_formula *, aalta_formula *>> &model)
{
    aalta_formula *edge_af = NULL;
    if (SAT_TRACE_FLAG)
    {
        if (!model.empty())
        {
            if (checkConflict(model.front()))
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
                                     get_edge_cons_for_aaltaf())
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
                auto tmp = (evidence->end()) - 1; // accepting adges have been processed in construction of edgeCons
                for (auto it = evidence->begin(); it < tmp; ++it)
                    model.push(*it);
            }
            else
            {
                processSignal(Unsat, NULL);
                return false;
            }
        }
        assert(!model.empty());
        edge_af = set_search_direction(model.front());
        if (edge_af != NULL)
            model.pop();
        else
        {
            while (!model.empty())
                model.pop();
            return false;
        }
    }
    else
    {
        if (current_X_idx_ == -1)
            for (int i = 0; i < X_parts_.size(); ++i)
                if (swin_X_idx_.find(i) == swin_X_idx_.end() &&
                    dfs_complete_X_idx_.find(i) == dfs_complete_X_idx_.end())
                {
                    current_X_idx_ = i;
                    break;
                }
        if (current_X_idx_ == -1)
        {
            processSignal(Unsat, NULL);
            return false;
        }
        aalta_formula *af_X = X_parts_[current_X_idx_];
        aalta_formula *af_Y = Y_cons_[current_X_idx_]->getEdge();
        edge_af = aalta_formula(aalta_formula::And, af_X, af_Y).unique();
        edge_af = edge_af->simplify();
    }
    edge_af->to_set(edge);
    // cout<<edge_af->to_string()<<endl;
    fill_in_edgeset(edge);
    return true;
}

bool edgeCons::getEdge_wholeDFA(unordered_set<int> &edge, queue<pair<aalta_formula *, aalta_formula *>> &model)
{
    aalta_formula *edge_af = NULL;
    if (current_X_idx_ == -1)
        for (int i = 0; i < X_parts_.size(); ++i)
        {
            if (Y_cons_[i]->hasTravAllEdges())
                insert_trav_all_afX_X_idx(i);
            if (trav_all_afX_X_idx_.find(i) == trav_all_afX_X_idx_.end())
            {
                current_X_idx_ = i;
                break;
            }
        }
    if (current_X_idx_ == -1)
    {
        processSignal(Unsat, NULL);
        return false;
    }
    aalta_formula *af_X = X_parts_[current_X_idx_];
    aalta_formula *af_Y = Y_cons_[current_X_idx_]->getEdge_wholeDFA();
    edge_af = aalta_formula(aalta_formula::And, af_X, af_Y).unique();
    edge_af = edge_af->simplify();
    edge_af->to_set(edge);
    // cout<<edge_af->to_string()<<endl;
    fill_in_edgeset(edge);
    return true; 
}

aalta_formula *YCons::getEdge()
{
    assert(!SAT_TRACE_FLAG && current_Y_idx_ == -1);
    for (int i = 0; i < Y_parts_.size(); ++i)
        if (ewin_Y_idx_.find(i) == ewin_Y_idx_.end() &&
            searched_Y_idx_.find(i) == searched_Y_idx_.end())
        {
            current_Y_idx_ = i;
            break;
        }
    if (current_Y_idx_ == -1)
    {
        processSignal(Unsat, NULL);
        return NULL;
    }
    return Y_parts_[current_Y_idx_];
}

aalta_formula *YCons::getEdge_wholeDFA()
{
    assert(!SAT_TRACE_FLAG && current_Y_idx_ == -1);
    for (int i = 0; i < Y_parts_.size(); ++i)
        if (trav_all_afY_Y_idx_.find(i) == trav_all_afY_Y_idx_.end())
        {
            current_Y_idx_ = i;
            break;
        }
    if (current_Y_idx_ == -1)
    {
        processSignal(Unsat, NULL);
        return NULL;
    }
    return Y_parts_[current_Y_idx_];
}

void edgeCons::get_succ_edges(vector<Syn_Edge> &succ_Y_edges)
{
    assert(Y_cons_.size() == X_parts_.size());
    for (int i = 0; i < Y_cons_.size(); ++i)
    {
        if (Y_cons_[i]->get_status() == Ewin)
            break;
        aalta_formula *af_X = X_parts_[i];
        Y_cons_[i]->get_succ_Y_edges(af_X, succ_Y_edges);
    }
}

void YCons::get_succ_Y_edges(aalta_formula *af_X, vector<Syn_Edge> &succ_Y_edges)
{
    assert(Y_parts_.size() == successors_.size());
    for (int i = 0; i < Y_parts_.size(); ++i)
    {
        DdNode *succ_bdd = successors_[i];
        if (Syn_Frame::ewin_state_bdd_set.find(ull(succ_bdd)) !=
            Syn_Frame::ewin_state_bdd_set.end())
            continue;
        aalta_formula *af_Y = Y_parts_[i];
        aalta_formula *af_edge = aalta_formula(aalta_formula::And, af_X, af_Y).unique();
        succ_Y_edges.push_back({succ_bdd, af_edge});
    }
}

aalta_formula *edgeCons::set_search_direction(const pair<aalta_formula *, aalta_formula *> &XY)
{
    assert(SAT_TRACE_FLAG);
    if (current_X_idx_ == -1)
        current_X_idx_ = find_match_X_idx(XY.first);
    aalta_formula *Y = Y_cons_[current_X_idx_]->set_search_direction(XY.second);
    if (Y == NULL)
        return NULL;
    else
        return aalta_formula(aalta_formula::And, X_parts_[current_X_idx_], Y).unique();
}

bool edgeCons::checkSwinForBackwardSearch()
{
    bool is_swin = true;
    for (auto it : dfs_complete_X_idx_)
        if (!(Y_cons_[it]->checkSwinForBackwardSearch()))
        {
            is_swin = false;
            break;
        }
    return is_swin;
}

bool YCons::checkSwinForBackwardSearch()
{
    bool is_swin = false;
    for (auto it : searched_Y_idx_)
        if (Syn_Frame::swin_state_bdd_set.find(ull(successors_[it])) !=
            Syn_Frame::swin_state_bdd_set.end())
        {
            is_swin = true;
            break;
        }
    return is_swin;
}

int edgeCons::find_match_X_idx(aalta_formula *X)
{
    // get_edge_cons_for_aaltaf() guarantee that
    // Dfs_complete X will not appear again.
    unordered_set<int> target_x;
    X->to_set(target_x);
    for (int i = 0; i < X_parts_.size(); ++i)
        if (swin_X_idx_.find(i) == swin_X_idx_.end() &&
            dfs_complete_X_idx_.find(i) == dfs_complete_X_idx_.end())
        {
            unordered_set<int> tmp;
            X_parts_[i]->to_set(tmp);
            if (isCompatible(&target_x, &tmp))
                return i;
        }
    assert(false);
}

void edgeCons::insert_swin_X_idx(int x)
{
    if (swin_X_idx_.find(x) == swin_X_idx_.end())
    {
        swin_X_idx_.insert(x);
        aalta_formula *not_X = aalta_formula(aalta_formula::Not, NULL, X_parts_[x]).nnf();
        blocked_X_ = (aalta_formula(aalta_formula::And, blocked_X_, not_X).simplify())->unique();
    }
}

void edgeCons::insert_dfs_complete_X_idx(int x)
{
    if (dfs_complete_X_idx_.find(x) == dfs_complete_X_idx_.end())
    {
        dfs_complete_X_idx_.insert(x);
        aalta_formula *not_X = aalta_formula(aalta_formula::Not, NULL, X_parts_[x]).nnf();
        blocked_X_ = (aalta_formula(aalta_formula::And, blocked_X_, not_X).simplify())->unique();
    }
}

void edgeCons::insert_trav_all_afX_X_idx(int x)
{
    if (trav_all_afX_X_idx_.find(x) == trav_all_afX_X_idx_.end())
    {
        trav_all_afX_X_idx_.insert(x);
        traved_X_ = (aalta_formula(aalta_formula::Or, traved_X_, X_parts_[x]).simplify())->unique();
    }
}

void YCons::insert_ewin_Y_idx(int y)
{
    if (ewin_Y_idx_.find(y) == ewin_Y_idx_.end())
    {
        ewin_Y_idx_.insert(y);
        aalta_formula *not_Y = aalta_formula(aalta_formula::Not, NULL, Y_parts_[y]).nnf();
        blocked_Y_ = (aalta_formula(aalta_formula::And, blocked_Y_, not_Y).simplify())->unique();
    }
}
void YCons::insert_searched_Y_idx(int y)
{
    if (searched_Y_idx_.find(y) == searched_Y_idx_.end())
    {
        searched_Y_idx_.insert(y);
        aalta_formula *not_Y = aalta_formula(aalta_formula::Not, NULL, Y_parts_[y]).nnf();
        blocked_Y_ = (aalta_formula(aalta_formula::And, blocked_Y_, not_Y).simplify())->unique();
    }
}
void YCons::insert_trav_all_afY_Y_idx(int y)
{
    if (trav_all_afY_Y_idx_.find(y) == trav_all_afY_Y_idx_.end())
    {
        trav_all_afY_Y_idx_.insert(y);
        traved_Y_ = (aalta_formula(aalta_formula::Or, traved_Y_, Y_parts_[y]).simplify())->unique();
    }
}
void YCons::insert_swin_Y_idx(int y)
{
    if (swin_Y_idx_.find(y) == swin_Y_idx_.end())
    {
        swin_Y_idx_.insert(y);
        swin_Y_ = (aalta_formula(aalta_formula::Or, swin_Y_, Y_parts_[y]).simplify())->unique();
        aalta_formula *not_Y = aalta_formula(aalta_formula::Not, NULL, Y_parts_[y]).nnf();
        blocked_Y_ = (aalta_formula(aalta_formula::And, blocked_Y_, not_Y).simplify())->unique();
    }
}

bool isCompatible(unordered_set<int> *edge1, unordered_set<int> *edge2)
{
    bool compatible = true;
    unordered_set<int> *smaller_set = ((edge1->size()) < (edge2->size())) ? edge1 : edge2;
    unordered_set<int> *bigger_set = (smaller_set == edge1) ? edge2 : edge1;
    for (auto it : (*smaller_set))
    {
        if (bigger_set->find(-it) != bigger_set->end())
        {
            compatible = false;
            break;
        }
    }
    return compatible;
}

aalta_formula *edgeCons::get_edge_cons_for_aaltaf()
{
    if (current_X_idx_ == -1)
        return blocked_X_;
    return aalta_formula(aalta_formula::And,
                         X_parts_[current_X_idx_],
                         Y_cons_[current_X_idx_]->get_blocked_Y())
        .unique();
}

aalta_formula *YCons::set_search_direction(aalta_formula *Y)
{
    assert(SAT_TRACE_FLAG && current_Y_idx_ == -1);
    current_Y_idx_ = find_match_Y_idx(Y);
    if (current_Y_idx_ == -1)
        return NULL;
    return Y_parts_[current_Y_idx_];
}

int YCons::find_match_Y_idx(aalta_formula *Y)
{
    unordered_set<int> target_y;
    Y->to_set(target_y);
    for (int i = 0; i < Y_parts_.size(); ++i)
        if (ewin_Y_idx_.find(i) == ewin_Y_idx_.end() &&
            searched_Y_idx_.find(i) == searched_Y_idx_.end())
        {
            unordered_set<int> tmp;
            Y_parts_[i]->to_set(tmp);
            if (isCompatible(&target_y, &tmp))
                return i;
        }
    return -1; // fail to find
}
