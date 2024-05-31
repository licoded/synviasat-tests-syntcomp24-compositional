#include "synthesis.h"
#include <iostream>
#include <queue>
#include <algorithm>

#include "formula_in_bdd.h"
#include "preprocess.h"

using namespace std;
using namespace aalta;

bool SAT_TRACE_FLAG = false;

unsigned int Syn_Frame::num_varX;
unsigned int Syn_Frame::num_varY;
set<int> Syn_Frame::var_X;
set<int> Syn_Frame::var_Y;
unordered_set<ull> Syn_Frame::swin_state_bdd_set;
unordered_set<ull> Syn_Frame::Syn_Frame::ewin_state_bdd_set;
unordered_set<ull> Syn_Frame::dfs_complete_state_bdd_set;
vector<DdNode *> Syn_Frame::swin_state_bdd_vec;
vector<DdNode *> Syn_Frame::ewin_state_bdd_vec;

unordered_map<ull, set<DdNode *> *> Syn_Frame::predecessors;

unordered_map<ull, int> dfn;
unordered_map<ull, int> low;
int dfs_time;

bool is_realizable(aalta_formula *src_formula, unordered_set<string> &env_var, bool verbose = false)
{
    PartitionAtoms(src_formula, env_var);
    // number of variables
    Syn_Frame::num_varX = Syn_Frame::var_X.size();
    Syn_Frame::num_varY = Syn_Frame::var_Y.size();

    FormulaInBdd::InitBdd4LTLf(src_formula, Syn_Frame::var_X, Syn_Frame::var_Y);
    // FormulaInBdd::fixXYOrder(Syn_Frame::var_X, Syn_Frame::var_Y);
    Syn_Frame::swin_state_bdd_set.insert(ull(FormulaInBdd::TRUE_bddP_));
    Syn_Frame::ewin_state_bdd_set.insert(ull(FormulaInBdd::FALSE_bddP_));

    Syn_Frame *init = new Syn_Frame(src_formula);

    return forwardSearch(init);
}

bool forwardSearch(Syn_Frame *init_frame)
{
    if (init_frame->get_status() == Swin)
        return true;
    dfs_time = 0;
    dfn.clear(), low.clear();
    int dfs_cur = 0;

    // set dfn and low value for cur_frame (init_frame)
    initial_tarjan_frame(init_frame);

    vector<Syn_Frame *> tarjan_sta; // for tarjan algorithm
    vector<Syn_Frame *> dfs_sta;    // for DFS
    dfs_sta.push_back(init_frame);
    tarjan_sta.push_back(init_frame);

    unordered_map<ull, int> prefix_bdd2curIdx_map;
    unordered_map<ull, int> sta_bdd2curIdx_map;
    prefix_bdd2curIdx_map.insert({ull(init_frame->GetBddPointer()), dfs_cur});
    sta_bdd2curIdx_map.insert({ull(init_frame->GetBddPointer()), tarjan_sta.size() - 1});
    queue<pair<aalta_formula *, aalta_formula *>> model;
    while (dfs_cur >= 0)
    {
        Status cur_state_status = dfs_sta[dfs_cur]->checkStatus();
        DdNode *cur_bddP = dfs_sta[dfs_cur]->GetBddPointer();
        if (cur_state_status != Dfs_incomplete)
        {
            if (dfn.at((ull)cur_bddP) == low.at((ull)cur_bddP))
            {
                vector<Syn_Frame *> scc;
                getScc(dfs_cur, scc, tarjan_sta, sta_bdd2curIdx_map);
                backwardSearch(scc);
                for (auto it : scc)
                    delete it;
            }
            prefix_bdd2curIdx_map.erase((ull)cur_bddP);
            dfs_sta.pop_back();
            --dfs_cur;
            if (dfs_cur < 0)
            {
                Syn_Frame::releasePredecessors();
                return cur_state_status == Swin;
            }
            else
            {
                Syn_Frame *predecessor_fr = dfs_sta[dfs_cur];
                Signal signal = To_swin;
                if (cur_state_status == Ewin)
                    signal = To_ewin;
                else if (cur_state_status == Dfs_complete)
                    signal = Pending;
                predecessor_fr->processSignal(signal, cur_bddP);

                while (!model.empty())
                    model.pop();

                update_by_low(predecessor_fr, cur_bddP);
                continue;
            }
        }

        unordered_set<int> edge_var_set;
        bool exist_edge_to_explorer = dfs_sta[dfs_cur]->getEdge(edge_var_set, model);

        if (!exist_edge_to_explorer)
            continue;

        if (IsAcc(dfs_sta[dfs_cur]->GetFormulaPointer(), edge_var_set)) // i.e. next_frame is true/swin
        {
            dfs_sta[dfs_cur]->processSignal(To_swin, FormulaInBdd::TRUE_bddP_);
            while (!model.empty())
                model.pop();
        }
        else
        {
            aalta_formula *next_af = FormulaProgression(dfs_sta[dfs_cur]->GetFormulaPointer(), edge_var_set); //->simplify();
            // cout<<next_af->to_string()<<endl;
            Syn_Frame *next_frame = new Syn_Frame(next_af);
            if (next_frame->get_status() == Swin)
            {
                Syn_Frame::insert_swin_state(next_frame->GetBddPointer(), false);
                dfs_sta[dfs_cur]->processSignal(To_swin, next_frame->GetBddPointer());
                while (!model.empty())
                    model.pop();
                continue;
            }

            Syn_Frame::addToGraph(dfs_sta[dfs_cur]->GetBddPointer(), next_frame->GetBddPointer());

            if (dfn.find(ull(next_frame->GetBddPointer())) == dfn.end())
            {
                initial_tarjan_frame(next_frame);

                dfs_sta.push_back(next_frame);
                tarjan_sta.push_back(next_frame);
                dfs_cur++;
                prefix_bdd2curIdx_map.insert({(ull)next_frame->GetBddPointer(), dfs_cur});
                sta_bdd2curIdx_map.insert({(ull)next_frame->GetBddPointer(), tarjan_sta.size() - 1});
            }
            else
            {
                // update low
                if (sta_bdd2curIdx_map.find(ull(next_frame->GetBddPointer())) != sta_bdd2curIdx_map.end())
                    update_by_dfn(dfs_sta[dfs_cur], next_frame);

                // do synthesis feedback
                if (prefix_bdd2curIdx_map.find((ull)next_frame->GetBddPointer()) != prefix_bdd2curIdx_map.end())
                {
                    /**
                     * cur_Y has X -> prefix, cannot make cur_state undetermined
                     * only all Y has X -> prefix, can make cur_state undetermined
                     */
                    // self loop is processed in the constructiobn of edgeCons
                    assert(next_frame->GetBddPointer() != dfs_sta[dfs_cur]->GetBddPointer());
                    dfs_sta[dfs_cur]->processSignal(Pending, next_frame->GetBddPointer());
                    while (!model.empty())
                        model.pop();
                }
                else // else: has cur-- (moved backward)
                {
                    Status next_state_status;
                    auto Iter = sta_bdd2curIdx_map.find(ull(next_frame->GetBddPointer()));
                    if (Iter != sta_bdd2curIdx_map.end())
                        next_state_status = tarjan_sta[Iter->second]->get_status();
                    else
                    {
                        next_state_status = Syn_Frame::getBddStatus(next_frame->GetBddPointer());
                    }
                    assert(next_state_status != Dfs_incomplete);
                    Signal sig = To_swin;
                    if (next_state_status == Ewin)
                        sig = To_ewin;
                    else if (next_state_status == Dfs_complete)
                        sig = Pending;
                    dfs_sta[dfs_cur]->processSignal(sig, next_frame->GetBddPointer());
                    while (!model.empty())
                        model.pop();
                    /*
                     * TODO: whether modify ull(next_frame->GetBddPointer()) back to dfs_sta[dfs_cur]->current_next_stateid_?
                     *              need assign dfs_sta[dfs_cur]->current_next_stateid_ in getEdge!!!
                     */
                }
                delete next_frame;
            }
        }
    }
}

void backwardSearch(vector<Syn_Frame *> &scc)
{
    unordered_map<ull, Syn_Frame *> bddP_to_synFrP;
    set<DdNode *> cur_swin, new_swin, undecided;

    for (auto it : scc)
    {
        if (it->get_status() == Swin)
            cur_swin.insert(it->GetBddPointer());
        else if (it->get_status() == Dfs_complete)
        {
            undecided.insert(it->GetBddPointer());
            bddP_to_synFrP[ull(it->GetBddPointer())] = it;
        }
    }
    if (undecided.empty())
        return;

    set<DdNode *> candidate_new_swin;
    set<DdNode *> tmp_set;
    do
    {
        new_swin.clear();
        candidate_new_swin.clear();
        tmp_set.clear();
        for (auto it : cur_swin)
        {
            set<DdNode *> *pred = Syn_Frame::getPredecessors(it);
            set_union(candidate_new_swin.begin(), candidate_new_swin.end(),
                      pred->begin(), pred->end(),
                      inserter(tmp_set, tmp_set.begin()));
            candidate_new_swin.swap(tmp_set);
            tmp_set.clear();
        }
        set_intersection(candidate_new_swin.begin(), candidate_new_swin.end(),
                         undecided.begin(), undecided.end(),
                         inserter(tmp_set, tmp_set.begin()));
        candidate_new_swin.swap(tmp_set);
        tmp_set.clear();
        for (auto s : candidate_new_swin)
        {
            if (bddP_to_synFrP[ull(s)]->checkSwinForBackwardSearch())
            {
                Syn_Frame::insert_swin_state(s, false);
                Syn_Frame::remove_dfs_complete_state(s);
                new_swin.insert(s);
                undecided.erase(s);
            }
        }
        cur_swin = new_swin;
    } while (!new_swin.empty());
    for (auto s : undecided)
    {
        Syn_Frame::insert_ewin_state(s, false);
        Syn_Frame::remove_dfs_complete_state(s);
    }
    return;
}

void initial_tarjan_frame(Syn_Frame *cur_frame)
{
    dfn.insert({ull(cur_frame->GetBddPointer()), dfs_time});
    low.insert({ull(cur_frame->GetBddPointer()), dfs_time});
    ++dfs_time;
}

void update_by_low(Syn_Frame *cur_frame, DdNode *next_bddP)
{
    low[(ull)cur_frame->GetBddPointer()] =
        min(low.at((ull)cur_frame->GetBddPointer()), low.at((ull)next_bddP));
}

void update_by_dfn(Syn_Frame *cur_frame, Syn_Frame *next_frame)
{
    low[(ull)cur_frame->GetBddPointer()] =
        min(low.at((ull)cur_frame->GetBddPointer()), dfn.at((ull)next_frame->GetBddPointer()));
}

void getScc(int dfs_cur, std::vector<Syn_Frame *> &scc,
            vector<Syn_Frame *> &tarjan_sta,
            unordered_map<ull, int> &sta_bdd2curIdx_map)
{
    int lowTimeId = dfn.at((ull)tarjan_sta[dfs_cur]->GetBddPointer());

    while (!tarjan_sta.empty() && low[ull(tarjan_sta.back()->GetBddPointer())] == lowTimeId)
    {
        scc.push_back(tarjan_sta.back());
        /* TODO: assert exist before erase? And may bdd_prt repeat in sta, and when 2nd erase it will? */
        sta_bdd2curIdx_map.erase(ull(tarjan_sta.back()->GetBddPointer()));
        tarjan_sta.pop_back();
        if (dfn.at(ull(scc.back()->GetBddPointer())) == lowTimeId)
            break;
        if (tarjan_sta.size() == dfs_cur)
            break;
    }
}

Syn_Frame::Syn_Frame(aalta_formula *af)
    : status_(Dfs_incomplete), edgeCons_(NULL),
      swin_checked_idx_(0), ewin_checked_idx_(0)
{
    aalta_formula *acc_edge = preprocessAcc(af);
    if (acc_edge == NULL)
        status_ = Swin;
    state_in_bdd_ = new FormulaInBdd(af);
    if (status_ != Swin)
    {
        edgeCons_ = new edgeCons(state_in_bdd_->GetBddPointer(), af, acc_edge);
        status_ = edgeCons_->get_status();
    }
}

Syn_Frame::~Syn_Frame()
{
    delete edgeCons_;
    delete state_in_bdd_;
}

Status Syn_Frame::checkStatus()
{
    status_ = edgeCons_->get_status();
    DdNode *bddp = GetBddPointer();
    if (status_ == Dfs_incomplete)
        if (swin_state_bdd_set.find(ull(bddp)) != swin_state_bdd_set.end())
            status_ = Swin;
        else if (ewin_state_bdd_set.find(ull(bddp)) != ewin_state_bdd_set.end())
            status_ = Ewin;
        else if (dfs_complete_state_bdd_set.find(ull(bddp)) != dfs_complete_state_bdd_set.end())
            status_ = Dfs_complete;
    switch (status_)
    {
    case Swin:
        insert_swin_state(bddp, false);
        return Swin;
    case Ewin:
        insert_ewin_state(bddp, false);
        return Ewin;
    case Dfs_complete:
        insert_dfs_complete_state(bddp);
        return Dfs_complete;
    default:
        break;
    }

    int vec_size = Syn_Frame::swin_state_bdd_vec.size();
    for (; swin_checked_idx_ < vec_size; ++swin_checked_idx_)
        if (FormulaInBdd::Implies(Syn_Frame::swin_state_bdd_vec[swin_checked_idx_], GetBddPointer()))
        {
            insert_swin_state(bddp, true);
            return (status_ = Swin);
        }
    vec_size = Syn_Frame::ewin_state_bdd_vec.size();
    for (; ewin_checked_idx_ < vec_size; ++ewin_checked_idx_)
        if (FormulaInBdd::Implies(GetBddPointer(), Syn_Frame::ewin_state_bdd_vec[ewin_checked_idx_]))
        {
            insert_ewin_state(bddp, true);
            return (status_ = Ewin);
        }

    return status_;
}

// partition atoms and save index values respectively
void PartitionAtoms(aalta_formula *af, unordered_set<string> &env_val)
{
    if (af == NULL)
        return;
    int op = af->oper();
    if (op >= 11)
        if (env_val.find(af->to_string()) != env_val.end())
            Syn_Frame::var_X.insert(op);

        else
            Syn_Frame::var_Y.insert(op);

    else
    {
        PartitionAtoms(af->l_af(), env_val);
        PartitionAtoms(af->r_af(), env_val);
    }
}

void Syn_Frame::processSignal(Signal sig, DdNode *succ)
{
    edgeCons_->processSignal(sig, succ);
}

bool Syn_Frame::getEdge(unordered_set<int> &edge, queue<pair<aalta_formula *, aalta_formula *>> &model)
{
    return edgeCons_->getEdge(edge, model);
}

bool Syn_Frame::checkSwinForBackwardSearch()
{
    return edgeCons_->checkSwinForBackwardSearch();
}
