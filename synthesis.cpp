#include "synthesis.h"
#include <iostream>
#include <fstream>
#include <queue>
#include <stack>
#include <algorithm>

extern "C" {
#include <mona/dfa.h>
#undef TRUE
#undef FALSE
}

#include "formula_in_bdd.h"
#include "preprocess.h"
#include "my_mona_dfa.h"

using namespace std;
using namespace aalta;

bool SAT_TRACE_FLAG = false;
bool WholeDFA_FLAG = false;
bool Minimize_FLAG = true;

unsigned int Syn_Frame::num_varX;
unsigned int Syn_Frame::num_varY;
set<int> Syn_Frame::var_X;
set<int> Syn_Frame::var_Y;
string Syn_Frame::partfile;
unordered_map<ull, bool> Syn_Frame::isAcc_byEmpty_bddP_map;
unordered_set<ull> Syn_Frame::swin_state_bdd_set;
unordered_set<ull> Syn_Frame::Syn_Frame::ewin_state_bdd_set;
unordered_set<ull> Syn_Frame::dfs_complete_state_bdd_set;
vector<DdNode *> Syn_Frame::swin_state_bdd_vec;
vector<DdNode *> Syn_Frame::ewin_state_bdd_vec;

unordered_map<ull, set<DdNode *> *> Syn_Frame::predecessors;

unordered_map<ull, int> dfn;
unordered_map<ull, int> low;
int dfs_time;

void monaDFA2graph(MonaDFA_Graph &graph, MyMonaDFA &dfa);
bool dfa_backward_check(string &dfa_filename);
DFA *graph2DFA(Syn_Graph &graph, DdNode *init_bddP, int var_num, int *indicies);
void printDFA(DFA *dfa, string &dot_filename, int var_num, unsigned int *var_index);
char *string2char_ptr(const string &s)
{
    char *ptr = new char[s.size() + 1];
    strcpy(ptr, s.c_str());
    ptr[s.size()] = '\0';
    return ptr;
}
char *af2binaryString(aalta_formula *af)
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
    }

    if (and_sub_afs.size() == 1)
        return true;

    WholeDFA_FLAG = true;
    SAT_TRACE_FLAG = false;
    Syn_Frame::isAcc_byEmpty_bddP_map.insert({ull(FormulaInBdd::TRUE_bddP_), true});
    Syn_Frame::isAcc_byEmpty_bddP_map.insert({ull(FormulaInBdd::FALSE_bddP_), false});

    // prepare for export DFA
    int var_num = Syn_Frame::num_varX + Syn_Frame::num_varY;
    char **var_names = new char *[var_num];
    for (auto item : Syn_Frame::var_X)
    {
        auto var_str = aalta_formula(item, NULL, NULL).to_string();
        int var_idx = item - 12;
        var_names[var_idx] = new char[var_str.size() + 1];
        strcpy(var_names[var_idx], var_str.c_str());
        var_names[var_idx][var_str.size()] = '\0';
    }
    for (auto item : Syn_Frame::var_Y)
    {
        auto var_str = aalta_formula(item, NULL, NULL).to_string();
        int var_idx = item - 12;
        var_names[var_idx] = new char[var_str.size() + 1];
        strcpy(var_names[var_idx], var_str.c_str());
        var_names[var_idx][var_str.size()] = '\0';
    }
    // reverse(var_names, var_names + var_num);
    char* orders = new char[var_num+1];
    memset(orders, 2, var_num);
    unsigned int *var_index = new unsigned int[var_num];
    int *indicies = new int[var_num];
    for (int i = 0; i < var_num; i++) {
        var_index[i] = i;
        indicies[i] = i;
    }

#ifdef DEBUG
    system("mkdir -p examples/temp-drafts");
#endif
    // get whole DFA
    DFA *dfa = dfaTrue(), *dfa_cur_min;
    for (auto it : and_sub_afs)
    {
        Syn_Graph graph;

        Syn_Frame *init = new Syn_Frame(it);
        DdNode *init_bddP = init->GetBddPointer();
        forwardSearch_wholeDFA(init, graph);
#ifdef DEBUG
        cout << "sub_af:\t" << it->to_string() << endl;
        printGraph(graph); // for DEBUG
#endif

        DFA *dfa_cur = graph2DFA(graph, init_bddP, var_num, indicies);
        if (Minimize_FLAG)
        {
            dfa_cur_min = dfaMinimize(dfa_cur);
            free(dfa_cur);
        }
        else
            dfa_cur_min = dfa_cur;
#ifdef DEBUG
        string af_s = it->to_string();
        // delete all spaces from af_s
        af_s.erase(remove(af_s.begin(), af_s.end(), ' '), af_s.end());
        string dfa_filename = "examples/temp-drafts/" + af_s + ".dfa";
        vector<char> dfa_filename_vec(dfa_filename.c_str(), dfa_filename.c_str() + dfa_filename.size() + 1);
        dfaExport(dfa_cur_min, dfa_filename_vec.data(), var_num, var_names, orders);
        string dot_filename = "examples/temp-drafts/" + af_s + ".dot";
        printDFA(dfa_cur_min, dot_filename, var_num, var_index);
#endif

        dfa = dfaProduct(dfa, dfa_cur_min, dfaAND);
        free(dfa_cur_min);
        if (Minimize_FLAG)
            dfa = dfaMinimize(dfa);
    }

    char* temp_filename = tmpnam(nullptr);
    string temp_filename_string = string(temp_filename);
    vector<char> filename_cstr(temp_filename_string.c_str(), temp_filename_string.c_str() + temp_filename_string.size() + 1);
    dfaExport(dfa, filename_cstr.data(), var_num, var_names, orders);

    Cudd* mgr = new Cudd();
    bool res = false;
    std::unordered_map<unsigned, BDD> strategy;
    Syft::syn test(mgr, temp_filename_string, Syn_Frame::partfile);
    bool syn_res = test.realizablity_env(strategy);

#ifdef DEBUG
    string wholedfa_filename = "examples/temp-drafts/whole.dfa";
    string wholedfa2dot_filename = "examples/temp-drafts/whole_dfa2.dot";
    string wholedot_filename = "examples/temp-drafts/whole.dot";
    printDFA(dfa, wholedot_filename, var_num, var_index);
    char *wholedfa_filename_char_ptr = string2char_ptr(wholedfa_filename);
    dfaExport(dfa, wholedfa_filename_char_ptr, var_num, var_names, orders);
    delete[] wholedfa_filename_char_ptr;
    system(("/home/lic/syntcomp2024/install_root/usr/local/bin/dfa2dot \""+wholedfa_filename+"\" \""+wholedfa2dot_filename+"\"").c_str());
#endif

    // TODO: delete char** and char*
    free(dfa);
    delete[] var_index;
    delete[] orders;
    delete[] indicies;
    for (int i = 0; i < var_num; i++)
        delete[] var_names[i];
    delete[] var_names;

    // return dfa_backward_check(wholedfa_filename);
    return syn_res;
}

bool forwardSearch(Syn_Frame *init_frame)
{
    if (init_frame->get_status() == Swin)
    {
        delete init_frame;
        return true;
    }
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
        bool cur_state_should_stopSearch_flag = dfs_sta[dfs_cur]->hasTravAllEdges() || (dfs_sta[dfs_cur]->get_status() == Ewin);
        DdNode *cur_bddP = dfs_sta[dfs_cur]->GetBddPointer();
        if (cur_state_should_stopSearch_flag)
        {
            if (dfn.at((ull)cur_bddP) == low.at((ull)cur_bddP))
            {
                vector<Syn_Frame *> scc;
                getScc(dfs_cur, scc, tarjan_sta, sta_bdd2curIdx_map);
                backwardSearch(scc);
                // cout << "++ scc.size: " << scc.size() << endl;
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

        // cout << "edge:\t";
        // for (auto it : edge_var_set)
        //     cout << aalta_formula::get_name(it) << ", ";
        // cout << endl;

        if (!exist_edge_to_explorer)
            continue;

        {
            aalta_formula *next_af = FormulaProgression_empty(dfs_sta[dfs_cur]->GetFormulaPointer(), edge_var_set); //->simplify();
            // cout<<next_af->to_string()<<endl;
            Syn_Frame *next_frame = new Syn_Frame(next_af);

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
            // cout << "||\t" << ull(syn_frame_ptr->GetBddPointer()) << " -> " << ull(syn_edge.first) << "\tby\t" << syn_edge.second->to_string() << endl;
            /* NOTE: self-loop in sub_af cannot be deleted, as they may not self-loop in whole_af */
            // if (ull(syn_frame_ptr->GetBddPointer()) == ull(syn_edge.first))
            //     continue;
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
    unordered_map<int, ull> stateid_to_bddP;
    int stateid_cnt = 0;
    // insert all vertex into bddP_to_stateid
    // INSERT-1. init_bddP
    int init_stateid = 0;
    auto init_vertex_Iter = graph.vertices.find(init_bddP);
    assert(init_vertex_Iter != graph.vertices.end());
    bddP_to_stateid.insert({ull(init_bddP), stateid_cnt++});
    stateid_to_bddP.insert({stateid_cnt-1, ull(init_bddP)});
    assert(init_stateid == stateid_cnt-1);
    graph.vertices.erase(init_bddP);
    // INSERT-2. false and true
    int true_stateid = 1, false_stateid = 2;
    bddP_to_stateid.insert({ull(FormulaInBdd::TRUE_bddP_), stateid_cnt++});
    stateid_to_bddP.insert({stateid_cnt-1, ull(FormulaInBdd::TRUE_bddP_)});
    assert(true_stateid == stateid_cnt-1);
    bddP_to_stateid.insert({ull(FormulaInBdd::FALSE_bddP_), stateid_cnt++});
    stateid_to_bddP.insert({stateid_cnt-1, ull(FormulaInBdd::FALSE_bddP_)});
    assert(false_stateid == stateid_cnt-1);
    graph.vertices.erase(FormulaInBdd::TRUE_bddP_);
    graph.vertices.erase(FormulaInBdd::FALSE_bddP_);
    // INSERT-2. others
    for (auto vertex : graph.vertices)
    {
        assert(bddP_to_stateid.find(ull(vertex)) == bddP_to_stateid.end());
        bddP_to_stateid.insert({ull(vertex), stateid_cnt++});
        stateid_to_bddP.insert({stateid_cnt-1, ull(vertex)});
    }

    dfaSetup(bddP_to_stateid.size(), var_num, indicies);
    vector<bool> state_visited(bddP_to_stateid.size(), 0);
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
            dfaStoreException(dest_stateid, bin_edge_ptr);
            delete[] bin_edge_ptr;
        }
        dfaStoreState(false_stateid);
        graph.edges.erase(init_bddP);
    }
    else
    {
        dfaAllocExceptions(0);
        dfaStoreState(false_stateid);
    }
    state_visited[init_stateid] = true;
    // EDGE-2. true and false
    dfaAllocExceptions(0);
    dfaStoreState(true_stateid);
    state_visited[true_stateid] = true;
    dfaAllocExceptions(0);
    dfaStoreState(false_stateid);
    state_visited[false_stateid] = true;
    // EDGE-3. others
    assert(stateid_cnt == bddP_to_stateid.size());
    for (int i = 0; i < stateid_cnt; i++)
    {
        if (state_visited[i])
            continue;
        auto vertex = (DdNode *)stateid_to_bddP[i];
        auto succ_edges_Iter = graph.edges.find(vertex);
        if (succ_edges_Iter == graph.edges.end())
        {
            dfaAllocExceptions(0);
            dfaStoreState(false_stateid);
            continue;
        }
        /* Else */
        auto succ_edges = succ_edges_Iter->second;
        dfaAllocExceptions(succ_edges.size());
        for (auto edge : succ_edges)
        {
            int dest_stateid = bddP_to_stateid[ull(edge.dest)];
            auto bin_edge_ptr = af2binaryString(edge.label);
            dfaStoreException(dest_stateid, bin_edge_ptr);
            delete[] bin_edge_ptr;
        }
        dfaStoreState(false_stateid);
    }
    // get state_type_arr_s
    assert(bddP_to_stateid.size() > 2);
    string state_type_s = string(bddP_to_stateid.size(), '0');
    for (auto bddP_and_stateid_pair : bddP_to_stateid)
    {
        auto bddP = bddP_and_stateid_pair.first;
        auto stateid = bddP_and_stateid_pair.second;
        if (Syn_Frame::isAcc_byEmpty_bddP_map[bddP])
            state_type_s[stateid] = '+';
        else if (Syn_Frame::ewin_state_bdd_set.find(ull(bddP)) != Syn_Frame::ewin_state_bdd_set.end())
            state_type_s[stateid] = '-';
        else
            state_type_s[stateid] = '0';
    }
    /**
     * DONE: change state_type of some state from 0 to +
     * NOTE: in following context, a is env var, b is sys var
     * 1. wnext state, e.g.
     *      - X(a)
     *      - X(a) & X(b)
     *      - X(a) & a
     *      - a & X(b)
     * 2. release state, e.g.
     *      - false R a     i.e.      G(a)
    */
    // cout << "build_str:\t" << string2char_ptr(state_type_s).get() << endl;
    auto state_type_char_ptr = string2char_ptr(state_type_s);
    DFA *dfa = dfaBuild(state_type_char_ptr);
    delete[] state_type_char_ptr;
    return dfa;
}

void printDFA(DFA *dfa, string &dot_filename, int var_num, unsigned int *var_index)
{
    FILE* original_stdout = stdout;
    stdout = fopen(dot_filename.c_str(), "w");
    // === real code BEGIN
    dfaPrintGraphviz(dfa, var_num, var_index);
    // === real code END
    fclose(stdout);
    stdout = original_stdout;
}

void monaDFA2graph(MonaDFA_Graph &graph, MyMonaDFA &dfa)
{
    for (int i = 0; i < dfa.states_num; i++)
    {
        vector<MonaDFA_Edge> cur_succ_edges;
        /* non-recursive DFS getEdge */
        stack<pair<int, aalta_formula *>> state_search_sta;
        state_search_sta.push({dfa.behaviour[i], aalta_formula::TRUE()});   // cur_bdd_id, pre_formula
        while(!state_search_sta.empty())
        {
            auto top_item = state_search_sta.top();
            state_search_sta.pop();
            vector<int> &cur_bdd = dfa.bdd[top_item.first];
            if (isEnd(cur_bdd))
            {
                int succ_state_id = cur_bdd[1];
                // graph.add_edge(i, cur_bdd[1], top_item.second);
                cur_succ_edges.push_back({succ_state_id, top_item.second});
            }
            else
            {
                int x = cur_bdd[0], l = cur_bdd[1], r = cur_bdd[2];
                aalta_formula *cur_var = aalta_formula(x+12, NULL, NULL).unique();   // TODO: ensure 12!!!
                aalta_formula *not_cur = aalta_formula(aalta_formula::Not, NULL, cur_var).unique();
                state_search_sta.push({l, aalta_formula(aalta_formula::And, top_item.second, not_cur).unique()});
                state_search_sta.push({r, aalta_formula(aalta_formula::And, top_item.second, cur_var).unique()});
            }
        }
        /* add to Graph */
        graph.add_vertex(i);
        for (auto edge : cur_succ_edges)
        {
            if (i == edge.first)
                continue;
            graph.add_edge(i, edge.first, edge.second);
        }
    }
}

void split_afXY(aalta_formula *edge, vector<aalta_formula *> &af_XY_pair)
{
    unordered_set<int> edge_set;
    edge->to_set(edge_set);
    aalta_formula *afX = aalta_formula::TRUE();
    aalta_formula *afY = aalta_formula::TRUE();
    for (auto var_id : edge_set)
    {
        aalta_formula *cur_var = aalta_formula(abs(var_id), NULL, NULL).unique();
        if (var_id < 0)
            cur_var = aalta_formula(aalta_formula::Not, NULL, cur_var).unique();
        if (Syn_Frame::var_X.find(var_id) != Syn_Frame::var_X.end())
        {
            if (afX == aalta_formula::TRUE())
                afX = cur_var;
            else
                afX = aalta_formula(aalta_formula::And, afX, cur_var).unique();
        }
        else
        {
            if (afY == aalta_formula::TRUE())
                afY = cur_var;
            else
                afY = aalta_formula(aalta_formula::And, afY, cur_var).unique();
        }
    }
    af_XY_pair.clear();
    af_XY_pair.push_back(afX);
    af_XY_pair.push_back(afY);
}

bool dfa_backward_check(string &dfa_filename)
{
    MyMonaDFA my_dfa;
    my_dfa.readMyMonaDFA(dfa_filename);
    MonaDFA_Graph mona_graph;
    monaDFA2graph(mona_graph, my_dfa);

    using MyYCons = pair<ull, int>;
    using MyXCons = unordered_map<ull, vector<MyYCons>*>;
    using MyEdgeCons = unordered_map<int, MyXCons *>;
    MyEdgeCons edge_cons_map;
    unordered_map<int, set<int>*> predecessors_map;

    for (auto vertex : mona_graph.vertices)
    {
        if (mona_graph.edges.find(vertex) == mona_graph.edges.end())
        {
            edge_cons_map.insert({vertex, NULL});
            continue;
        }
        auto vertex_edges = mona_graph.edges[vertex];
        MyXCons *vertex_XCons = new MyXCons();
        for (auto edge : vertex_edges)
        {
            auto edge_af = edge.label;
            auto successor = edge.dest;
            if (predecessors_map.find(successor) == predecessors_map.end())
            {
                predecessors_map.insert({successor, new set<int>()});
            }
            predecessors_map[successor]->insert(vertex);
            /* TODO: split afX and afY from edge_af */
            vector<aalta_formula *> af_XY_pair;
            split_afXY(edge_af, af_XY_pair);
            assert(af_XY_pair.size() == 2);
            aalta_formula *afX = af_XY_pair[0];
            aalta_formula *afY = af_XY_pair[1];
            /* TODO: collect ptrs and clean them in the end of func */
            FormulaInBdd *afX_in_bdd = new FormulaInBdd(afX);
            FormulaInBdd *afY_in_bdd = new FormulaInBdd(afY);
            ull afX_bddP = ull(afX_in_bdd->GetBddPointer());
            ull afY_bddP = ull(afY_in_bdd->GetBddPointer());
            delete afX_in_bdd;
            delete afY_in_bdd;
            if (vertex_XCons->find(afX_bddP) == vertex_XCons->end())
            {
                vertex_XCons->insert({afX_bddP, new vector<MyYCons>()});
            }
            vertex_XCons->at(afX_bddP)->push_back({afY_bddP, successor});
        }
        edge_cons_map.insert({vertex, vertex_XCons});
    }

    set<int> cur_swin, new_swin, swin;
    for (int i = 0; i < my_dfa.states_num; i++)
    {
        if (my_dfa.final[i] == 1)
        {
            cur_swin.insert(i);
            swin.insert(i);
        }
    }
    bool is_realizable = false;
    do {
        if (swin.find(my_dfa.initial_stateid) != swin.end())
        {
            is_realizable = true;
            break;
        }

        new_swin.clear();
        set<int> candidate_new_swin_pre;
        for (auto it : cur_swin)
        {
            set<int> *pred = predecessors_map[it];
            set_union(candidate_new_swin_pre.begin(), candidate_new_swin_pre.end(),
                      pred->begin(), pred->end(),
                      inserter(candidate_new_swin_pre, candidate_new_swin_pre.begin()));
        }
        set<int> candidate_new_swin;
        set_difference(candidate_new_swin_pre.begin(), candidate_new_swin_pre.end(),
                       swin.begin(), swin.end(),
                       inserter(candidate_new_swin, candidate_new_swin.begin()));
        for (auto s : candidate_new_swin)
        {
            if (edge_cons_map[s] == NULL)
                continue;
            bool cur_s_isSwin = true;
            for (auto afX_myYCons_vec_pair : *edge_cons_map[s])
            {
                bool cur_afX_toSwin = false;
                for (auto myYCons : *(afX_myYCons_vec_pair.second))
                {
                    if (swin.find(myYCons.second) != swin.end())
                    {
                        cur_afX_toSwin = true;
                        break;
                    }
                }
                if (!cur_afX_toSwin)
                {
                    cur_s_isSwin = false;
                    break;
                }
            }
            if (cur_s_isSwin)
            {
                new_swin.insert(s);
                swin.insert(s);
            }
        }
        cur_swin = new_swin;
    } while (!new_swin.empty());

    for (auto edge_cons_item : edge_cons_map)
    {
        if (edge_cons_item.second == NULL)
            continue;
        for (auto my_xcons_item : *(edge_cons_item.second))
        {
            delete my_xcons_item.second;
        }
        delete edge_cons_item.second;
    }
    // unordered_map<int, set<int>*> predecessors_map;
    for (auto prodecessors_item : predecessors_map)
        delete prodecessors_item.second;

    return is_realizable;
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
    state_in_bdd_ = WholeDFA_FLAG
        ? new FormulaInBdd(af, xnf_empty(af))
        : new FormulaInBdd(af);
    if (WholeDFA_FLAG)
    {
        if (isAcc_byEmpty_bddP_map.find(ull(state_in_bdd_->GetBddPointer())) == isAcc_byEmpty_bddP_map.end())
        {
            isAcc_byEmpty_bddP_map.insert({ull(state_in_bdd_->GetBddPointer()), IsEmptyAcc(af->nnf())});
        }
        edgeCons_ = new edgeCons(state_in_bdd_->GetBddPointer(), af, aalta_formula::TRUE());
        status_ = edgeCons_->get_status();
        if (isAcc_byEmpty_bddP_map[ull(state_in_bdd_->GetBddPointer())])
            status_ = Swin;
    }
    else if (status_ != Swin)
    {
        state_in_bdd_ = new FormulaInBdd(af);
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
    if (WholeDFA_FLAG && isAcc_byEmpty_bddP_map[ull(state_in_bdd_->GetBddPointer())])
        status_ = Swin;
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
    if (WholeDFA_FLAG)
    {
        /* NOTE: add isAcc_byEmpty_bddP_map to force those states processSignal with Swin to their predecessors */
        if (Syn_Frame::isAcc_byEmpty_bddP_map[ull(state_in_bdd_->GetBddPointer())])
            sig = To_swin;
        edgeCons_->processSignal_wholeDFA(sig, succ);
    }
    else
    {
        edgeCons_->processSignal(sig, succ);
    }
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
