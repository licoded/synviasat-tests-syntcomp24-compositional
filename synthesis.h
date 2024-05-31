#ifndef __SYNTHESIS__
#define __SYNTHESIS__

#include <cassert>
#include <unordered_set>
#include <set>

#include "formula/aalta_formula.h"
#include "edge_cons.h"
#include "formula_in_bdd.h"
#include "syn_type.h"
#include "deps/CUDD-install/include/cudd.h"

using namespace std;
using namespace aalta;

extern bool SAT_TRACE_FLAG;

typedef unsigned long long ull;

// main entry
bool is_realizable(aalta_formula *src_formula, unordered_set<string> &env_var, bool verbose);

class edgeCons;

class Syn_Frame
{
private:
    FormulaInBdd *state_in_bdd_;
    edgeCons *edgeCons_;
    Status status_;

    int swin_checked_idx_;
    int ewin_checked_idx_;

    static unordered_map<ull, set<DdNode *> *> predecessors;

public:
    static set<int> var_X, var_Y;
    static unsigned int num_varX, num_varY;

    static unordered_set<ull> swin_state_bdd_set;
    static unordered_set<ull> ewin_state_bdd_set;
    static unordered_set<ull> dfs_complete_state_bdd_set;

    static vector<DdNode *> swin_state_bdd_vec;
    static vector<DdNode *> ewin_state_bdd_vec;

    static void insert_swin_state(DdNode *bddP, bool from_imply);
    static void insert_ewin_state(DdNode *bddP, bool from_imply);
    static void insert_dfs_complete_state(DdNode *bddP);
    static void remove_dfs_complete_state(DdNode *bddP);

    Syn_Frame(aalta_formula *af);
    ~Syn_Frame();

    DdNode *GetBddPointer() { return state_in_bdd_->GetBddPointer(); }
    aalta_formula *GetFormulaPointer() { return state_in_bdd_->GetFormulaPointer(); }

    Status checkStatus();
    void processSignal(Signal sig, DdNode *succ);

    bool getEdge(unordered_set<int> &edge, queue<pair<aalta_formula *, aalta_formula *>> &model);
    Status get_status() { return status_; }

    bool checkSwinForBackwardSearch();

    static void addToGraph(DdNode *src, DdNode *dst);
    static set<DdNode *> *getPredecessors(DdNode *);
    static void freePredecessorsSet(DdNode *);
    static void releasePredecessors()
    {
        for (auto it : Syn_Frame::predecessors)
            delete it.second;
    }
    static Status getBddStatus(DdNode *b)
    {
        if (swin_state_bdd_set.find(ull(b)) != swin_state_bdd_set.end())
            return Swin;
        else if (ewin_state_bdd_set.find(ull(b)) != ewin_state_bdd_set.end())
            return Ewin;
        else if (dfs_complete_state_bdd_set.find(ull(b)) != dfs_complete_state_bdd_set.end())
            return Dfs_complete;
        else
            return Dfs_incomplete;
    }
};

bool forwardSearch(Syn_Frame *);
void backwardSearch(std::vector<Syn_Frame *> &scc);

// for tarjan
void initial_tarjan_frame(Syn_Frame *cur_frame);
void update_by_low(Syn_Frame *cur_frame, DdNode *cur_bddP);
void update_by_dfn(Syn_Frame *cur_frame, Syn_Frame *next_frame);
void getScc(int cur, std::vector<Syn_Frame *> &scc,
            vector<Syn_Frame *> &sta, unordered_map<ull, int> &sta_bdd2curIdx_map);

void PartitionAtoms(aalta_formula *af, unordered_set<string> &env_val);

// implemantation of inline funtions
inline void Syn_Frame::insert_swin_state(DdNode *bddP, bool from_imply)
{
    if (Syn_Frame::swin_state_bdd_set.find(ull(bddP)) == Syn_Frame::swin_state_bdd_set.end())
    {
        Syn_Frame::swin_state_bdd_set.insert(ull(bddP));
        if (false) //(!from_imply)
            Syn_Frame::swin_state_bdd_vec.push_back(bddP);
    }
}

inline void Syn_Frame::insert_ewin_state(DdNode *bddP, bool from_imply)
{
    if (Syn_Frame::ewin_state_bdd_set.find(ull(bddP)) == Syn_Frame::ewin_state_bdd_set.end())
    {
        Syn_Frame::ewin_state_bdd_set.insert(ull(bddP));
        if (false) //(!from_imply)
            Syn_Frame::ewin_state_bdd_vec.push_back(bddP);
    }
}

inline void Syn_Frame::insert_dfs_complete_state(DdNode *bddP)
{
    Syn_Frame::dfs_complete_state_bdd_set.insert(ull(bddP));
}

inline void Syn_Frame::remove_dfs_complete_state(DdNode *bddP)
{
    Syn_Frame::dfs_complete_state_bdd_set.erase(ull(bddP));
}

inline void Syn_Frame::addToGraph(DdNode *src, DdNode *dst)
{
    if (predecessors.find(ull(dst)) == predecessors.end())
        predecessors[ull(dst)] = new set<DdNode *>();
    (predecessors[ull(dst)])->insert(src);
}

inline set<DdNode *> *Syn_Frame::getPredecessors(DdNode *s)
{
    assert(predecessors.find(ull(s)) != predecessors.end());
    return predecessors[ull(s)];
}

inline void Syn_Frame::freePredecessorsSet(DdNode *s)
{
    assert(predecessors.find(ull(s)) != predecessors.end());
    delete predecessors[ull(s)];
    predecessors.erase(ull(s));
}

#endif