#ifndef __FORMULA_IN_BDD__
#define __FORMULA_IN_BDD__

#include <unordered_map>
#include <iostream>
#include <set>

#include "formula/aalta_formula.h"
#include "formula/af_utils.h"
#include "deps/CUDD-install/include/cudd.h"

using namespace std;
using namespace aalta;

typedef unsigned long long ull;

class FormulaInBdd
{
private:
    static unordered_map<ull, ull> aaltaP_to_bddP_;
    static unordered_map<int, ull> bddIdx_to_aaltaP_;
    // static unordered_map<ull,DdNode*> temporal_afp_to_bddP_;
    static aalta_formula *src_formula_;

    static unordered_set<ull> aaltaP_map_created;

    static void CreatedMap4AaltaP2BddP(aalta_formula *af);
    // static DdNode *getXnfBdd(aalta_formula *af);
    static DdNode *buildXnfBdd(aalta_formula *af);

    aalta_formula *formula_;
    // aalta_formula *xnf_formula_;
    DdNode *bdd_;

public:
    static unsigned int X_var_nums, Y_var_nums, total_var_nums;
    static DdManager *global_bdd_manager_;
    static bool is_X_var(DdNode *node) { return Cudd_NodeReadIndex(node) >= Y_var_nums && Cudd_NodeReadIndex(node) < total_var_nums; }
    static bool is_Y_var(DdNode *node) { return Cudd_NodeReadIndex(node) < Y_var_nums; }
    static bool is_notXY_var(DdNode *node) { return Cudd_NodeReadIndex(node) >= total_var_nums; }
    static bool is_Next_var(DdNode *node) { return is_notXY_var(node) && !Cudd_IsConstant(node); }
    static aalta_formula *get_af_var(int node_idx) { return (aalta_formula *)bddIdx_to_aaltaP_[node_idx]; }

    static DdNode *TRUE_bddP_;
    static DdNode *FALSE_bddP_;

    // static unordered_map<ull, ull> bddP_to_afP;

    static void InitBdd4LTLf(aalta_formula *src_formula, std::set<int> &X_vars, std::set<int> &Y_vars);
    static void QuitBdd4LTLf() { Cudd_Quit(global_bdd_manager_); }
    static void fixXYOrder(set<int> &X_vars, set<int> &Y_vars);

    static DdNode *ConstructBdd(aalta_formula *af);

    FormulaInBdd(aalta_formula *af);

    inline DdNode *GetBddPointer() { return bdd_; }
    inline aalta_formula *GetFormulaPointer() { return formula_; }

    // if (af1 -> af2) in Boolean semantics, it returns true
    static bool Implies(aalta_formula *af1, aalta_formula *af2);
    static bool Implies(DdNode *af1, DdNode *af2);

    static void PrintMapInfo();

    static bool check_conflict(aalta_formula *af1, aalta_formula *af2);
};

#endif