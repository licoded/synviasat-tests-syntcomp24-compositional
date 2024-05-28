#include "synthesis.h"
#include <iostream>
#include <fstream>
#include <queue>
#include <algorithm>

extern "C" {
#include <mona/dfa.h>
#undef TRUE
#undef FALSE
}

#include "formula_in_bdd.h"
#include "preprocessAcc.h"

using namespace std;
using namespace aalta;

bool SAT_TRACE_FLAG = false;
bool WholeDFA_FLAG = false;

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

DFA *graph2DFA(Syn_Graph &graph, DdNode *init_bddP, int var_num, int *indicies);
void *printDFA(DFA *dfa, string &dot_filename, int var_num, unsigned int *var_index);
shared_ptr<char> string2char_ptr(const string &s)
{
    shared_ptr<char> ptr(new char[s.size() + 1]);
    strcpy(ptr.get(), s.c_str());
    ptr.get()[s.size()] = '\0';
    return ptr;
}
shared_ptr<char> af2binaryString(aalta_formula *af)
{
    // -11 -1(TAIL)
    unordered_set<int> edgeset;
    af->to_set(edgeset);
    int var_num = Syn_Frame::num_varX + Syn_Frame::num_varY;
    string bin_edge(var_num, 'X');
    for (auto it : edgeset)
    {
        int var_id = abs(it);
        assert(bin_edge[var_id-12] == 'X');
        bin_edge[var_id-12] = it > 0 ? '1' : '0';
    }
    return string2char_ptr(bin_edge);
}

bool is_realizable(aalta_formula *src_formula, unordered_set<string> &env_var, bool verbose = false)
{
    PartitionAtoms(src_formula, env_var);
    // number of variables
    Syn_Frame::num_varX = Syn_Frame::var_X.size();
    Syn_Frame::num_varY = Syn_Frame::var_Y.size();

    FormulaInBdd::InitBdd4LTLf(src_formula, Syn_Frame::var_X, Syn_Frame::var_Y);
    Syn_Frame::swin_state_bdd_set.insert(ull(FormulaInBdd::TRUE_bddP_));
    Syn_Frame::ewin_state_bdd_set.insert(ull(FormulaInBdd::FALSE_bddP_));

    hash_set<aalta_formula*> and_sub_afs = src_formula->and_to_set();
    WholeDFA_FLAG = false;
    for (auto it : and_sub_afs)
    {
        Syn_Frame *init = new Syn_Frame(it);
        if (!forwardSearch(init))
            return false;
        delete init;
    }

    if (and_sub_afs.size() == 1)
        return true;

    WholeDFA_FLAG = true;
    SAT_TRACE_FLAG = false;

    // prepare for export DFA
    int var_num = Syn_Frame::num_varX + Syn_Frame::num_varY;
    char **var_names = new char *[var_num];
    int var_cnt = 0;
    for (auto item : Syn_Frame::var_X)
    {
        auto var_str = aalta_formula(item, NULL, NULL).to_string();
        var_names[var_cnt] = new char[var_str.size() + 1];
        strcpy(var_names[var_cnt], var_str.c_str());
        var_names[var_cnt][var_str.size()] = '\0';
        var_cnt++;
    }
    for (auto item : Syn_Frame::var_Y)
    {
        auto var_str = aalta_formula(item, NULL, NULL).to_string();
        var_names[var_cnt] = new char[var_str.size() + 1];
        strcpy(var_names[var_cnt], var_str.c_str());
        var_names[var_cnt][var_str.size()] = '\0';
        var_cnt++;
    }
    auto orders = string2char_ptr(string('0', var_num));
    unsigned int *var_index = new unsigned int[var_num];
    int *indicies = new int[var_num];
    for (int i = 0; i < var_num; i++) {
        var_index[i] = i;
        indicies[i] = i;
    }

    // get whole DFA
    DFA *dfa = dfaTrue();
    for (auto it : and_sub_afs)
    {
        Syn_Graph graph;

        Syn_Frame *init = new Syn_Frame(it);
        DdNode *init_bddP = init->GetBddPointer();
        forwardSearch_wholeDFA(init, graph);
        cout << "sub_af:\t" << it->to_string() << endl;
        printGraph(graph); // for DEBUG

        DFA *dfa_cur = graph2DFA(graph, init_bddP, var_num, indicies);
        dfa_cur = dfaMinimize(dfa_cur);
        string af_s = it->to_string();
        // delete all spaces from af_s
        af_s.erase(remove(af_s.begin(), af_s.end(), ' '), af_s.end());
        string dfa_filename = "/home/lic/shengpingxiao/compositional-synthesis-codes/ltlfsyn_synthesis_envfirst_0501/examples/temp-drafts/" + af_s + ".dfa";
        string dot_filename = "/home/lic/shengpingxiao/compositional-synthesis-codes/ltlfsyn_synthesis_envfirst_0501/examples/temp-drafts/" + af_s + ".dot";

        printDFA(dfa_cur, dot_filename, var_num, var_index);
        // dfaExport(dfa_cur, string2char_ptr(dfa_filename).get(), var_num, var_names, orders.get());
        // system(("/home/lic/syntcomp2024/install_root/usr/local/bin/dfa2dot \""+dfa_filename+"\" \""+dot_filename+"\"").c_str());

        // TODO: dfa_cur = minize(dfa_cur);
        dfa = dfaProduct(dfa, dfa_cur, dfaAND);
        dfa = dfaMinimize(dfa);
        // delete init; // NOTE: WholeDFA --> init belongs to some scc --> has been deleted in forwardSearch_wholeDFA ???
    }

    string wholedfa_filename = "/home/lic/shengpingxiao/compositional-synthesis-codes/ltlfsyn_synthesis_envfirst_0501/examples/temp-drafts/whole.dfa";
    string wholedfa2dot_filename = "/home/lic/shengpingxiao/compositional-synthesis-codes/ltlfsyn_synthesis_envfirst_0501/examples/temp-drafts/whole_dfa2.dot";
    string wholedot_filename = "/home/lic/shengpingxiao/compositional-synthesis-codes/ltlfsyn_synthesis_envfirst_0501/examples/temp-drafts/whole.dot";
    printDFA(dfa, wholedot_filename, var_num, var_index);
    dfaExport(dfa, string2char_ptr(wholedfa_filename).get(), var_num, var_names, orders.get());
    system(("/home/lic/syntcomp2024/install_root/usr/local/bin/dfa2dot \""+wholedfa_filename+"\" \""+wholedfa2dot_filename+"\"").c_str());
    // TODO: delete char** and char*

    return true;
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
                Syn_Frame::insert_swin_state(next_frame->GetBddPointer(),false);
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

bool forwardSearch_wholeDFA(Syn_Frame *init_frame, Syn_Graph &graph)
{
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
        bool cur_state_hasTravAll_flag = dfs_sta[dfs_cur]->hasTravAllEdges();
        DdNode *cur_bddP = dfs_sta[dfs_cur]->GetBddPointer();
        if (cur_state_hasTravAll_flag)
        {
            if (dfn.at((ull)cur_bddP) == low.at((ull)cur_bddP))
            {
                vector<Syn_Frame *> scc;
                getScc(dfs_cur, scc, tarjan_sta, sta_bdd2curIdx_map);
                backwardSearch(scc);
                cout << "++ scc.size: " << scc.size() << endl;
                addSccToGraph(scc, graph);
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

        cout << "edge:\t";
        for (auto it : edge_var_set)
            cout << aalta_formula::get_name(it) << ", ";
        cout << endl;

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
                Syn_Frame::insert_swin_state(next_frame->GetBddPointer(),false);
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
    do
    {
        new_swin.clear();
        set<DdNode *> candidate_new_swin;
        for (auto it : cur_swin)
        {
            set<DdNode *> *pred = Syn_Frame::getPredecessors(it);
            set_union(candidate_new_swin.begin(), candidate_new_swin.end(),
                      pred->begin(), pred->end(),
                      inserter(candidate_new_swin, candidate_new_swin.begin()));
        }
        set_intersection(candidate_new_swin.begin(), candidate_new_swin.end(),
                         undecided.begin(), undecided.end(),
                         inserter(candidate_new_swin, candidate_new_swin.begin()));
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

void addSccToGraph(vector<Syn_Frame *> &scc, Syn_Graph &graph)
{
    for (auto syn_frame_ptr : scc)
    {
        graph.add_vertex(syn_frame_ptr->GetBddPointer());
        if (syn_frame_ptr->get_status() == Ewin ||
            Syn_Frame::ewin_state_bdd_set.find(ull(syn_frame_ptr->GetBddPointer())) != Syn_Frame::ewin_state_bdd_set.end())
        {
            continue;
        }
        vector<Syn_Edge> succ_edges;
        syn_frame_ptr->get_succ_edges(succ_edges);
        for (auto syn_edge : succ_edges)
        {
            cout << "||\t" << ull(syn_frame_ptr->GetBddPointer()) << " -> " << ull(syn_edge.first) << "\tby\t" << syn_edge.second->to_string() << endl;
            if (ull(syn_frame_ptr->GetBddPointer()) == ull(syn_edge.first))
                continue;
            graph.add_edge(syn_frame_ptr->GetBddPointer(), syn_edge.first, syn_edge.second);
        }
    }
}

void printGraph(Syn_Graph &graph)
{
    cout << "Graph vertices: ";
    for (auto v : graph.vertices)
        cout << ull(v) << ", ";
    cout << endl;
    cout << "Graph edges: " << endl;
    for (auto it : graph.edges)
    {
        cout << ull(it.first) << ": ";
        for (auto edge : it.second)
            cout << "(" << edge.label->to_string() << ", " << ull(edge.dest) << "), ";
        cout << endl;
    }
}

DFA *graph2DFA(Syn_Graph &graph, DdNode *init_bddP, int var_num, int *indicies)
{
    // assert(graph.vertices.size() > 2);  // NOTE: other cases: 1. sth. -> alway true/false 2. init is true/false !!!
    unordered_map<ull, int> bddP_to_stateid;
    int stateid_cnt = 0;
    // insert all vertex into bddP_to_stateid
    // INSERT-1. init_bddP
    auto init_vertex_Iter = graph.vertices.find(init_bddP);
    assert(init_vertex_Iter != graph.vertices.end());
    bddP_to_stateid.insert({ull(init_bddP), stateid_cnt++});
    graph.vertices.erase(init_bddP);
    // INSERT-2. false and true
    int true_stateid = 1, false_stateid = 2;
    bddP_to_stateid.insert({ull(FormulaInBdd::TRUE_bddP_), stateid_cnt++});
    bddP_to_stateid.insert({ull(FormulaInBdd::FALSE_bddP_), stateid_cnt++});
    graph.vertices.erase(FormulaInBdd::TRUE_bddP_);
    graph.vertices.erase(FormulaInBdd::FALSE_bddP_);
    // INSERT-2. others
    for (auto vertex : graph.vertices)
    {
        assert(bddP_to_stateid.find(ull(vertex)) == bddP_to_stateid.end());
        bddP_to_stateid.insert({ull(vertex), stateid_cnt++});
    }

    dfaSetup(bddP_to_stateid.size(), var_num, indicies);
    // EDGE-1. init_bddP
    auto init_edges_Iter = graph.edges.find(init_bddP);
    if (init_edges_Iter != graph.edges.end())
    {
        auto init_succ_edges = init_edges_Iter->second;
        dfaAllocExceptions(init_succ_edges.size());
        for (auto edge : init_succ_edges)
        {
            int dest_stateid = bddP_to_stateid[ull(edge.dest)];
            auto bin_edge_ptr = af2binaryString(edge.label);
            dfaStoreException(dest_stateid, bin_edge_ptr.get());
        }
        dfaStoreState(false_stateid);
        graph.edges.erase(init_bddP);
    }
    else
    {
        dfaAllocExceptions(0);
        dfaStoreState(false_stateid);
    }
    // EDGE-2. true and false
    dfaAllocExceptions(0);
    dfaStoreState(true_stateid);
    dfaAllocExceptions(0);
    dfaStoreState(false_stateid);
    // EDGE-3. others
    for (auto vertex_and_succ_edges_pair : graph.edges)
    {
        auto vertexBddP = vertex_and_succ_edges_pair.first;
        auto succ_edges = vertex_and_succ_edges_pair.second;
        dfaAllocExceptions(succ_edges.size());
        for (auto edge : succ_edges)
        {
            int dest_stateid = bddP_to_stateid[ull(edge.dest)];
            auto bin_edge_ptr = af2binaryString(edge.label);
            dfaStoreException(dest_stateid, bin_edge_ptr.get());
        }
        dfaStoreState(false_stateid);   // NOTE: I think there are no default transitions!!!
    }
    // get state_type_arr_s
    assert(bddP_to_stateid.size() > 2);
    string state_type_s = bddP_to_stateid.size() > 3 ? string(bddP_to_stateid.size()-3, '0') : "";
    state_type_s = "0+-" + state_type_s;
    cout << "build_str:\t" << string2char_ptr(state_type_s).get() << endl;
    return dfaBuild(string2char_ptr(state_type_s).get());
}

void *printDFA(DFA *dfa, string &dot_filename, int var_num, unsigned int *var_index)
{
    FILE* original_stdout = stdout;
    stdout = fopen(dot_filename.c_str(), "w");
    // === real code BEGIN
    dfaPrintGraphviz(dfa, var_num, var_index);
    // === real code END
    fclose(stdout);
    stdout = original_stdout;
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
    aalta_formula *neg_acc_X = preprocessAcc(af);
    if (neg_acc_X == NULL)
        status_ = Swin;
    state_in_bdd_ = new FormulaInBdd(af);
    if (WholeDFA_FLAG)
    {
        edgeCons_ = new edgeCons(state_in_bdd_->GetBddPointer(), af, aalta_formula::TRUE());
        status_ = edgeCons_->get_status();
    }
    else if (status_ != Swin)
    {
        edgeCons_ = new edgeCons(state_in_bdd_->GetBddPointer(), af, neg_acc_X);
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

bool Syn_Frame::hasTravAllEdges()
{
    return edgeCons_->hasTravAllEdges();
}

bool Syn_Frame::getEdge(unordered_set<int> &edge, queue<pair<aalta_formula *, aalta_formula *>> &model)
{
    if (WholeDFA_FLAG)
        return edgeCons_->getEdge_wholeDFA(edge, model);
    return edgeCons_->getEdge(edge, model);
}

void Syn_Frame::get_succ_edges(vector<Syn_Edge> &succ_edges)
{
    return edgeCons_->get_succ_edges(succ_edges);
}

bool Syn_Frame::checkSwinForBackwardSearch()
{
    return edgeCons_->checkSwinForBackwardSearch();
}
