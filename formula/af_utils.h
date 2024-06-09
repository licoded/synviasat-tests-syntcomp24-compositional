#ifndef __AF_UTILS__
#define __AF_UTILS__

#include <unordered_set>
#include <set>
#include "formula/aalta_formula.h"
using namespace aalta;
using namespace std;

aalta_formula * xnf(aalta_formula *af);
aalta_formula * xnf_empty(aalta_formula *af);
// xnf(aalta_formula *phi);
aalta_formula *FormulaProgression(aalta_formula *predecessor, unordered_set<int> &edge);
aalta_formula *FormulaProgression_empty(aalta_formula *predecessor, unordered_set<int> &edge);
bool IsEmptyAcc(aalta_formula *state_af);
// bool BaseWinningAtY(aalta_formula *end_state, unordered_set<int> &Y);
bool IsAcc(aalta_formula *predecessor, unordered_set<int> &tmp_edge);
void fill_in_edgeset(std::unordered_set<int> &partial_edgeset);

void to_conjunts(aalta_formula *af, vector<aalta_formula *>& conjuncts);

void to_conjunts(aalta_formula *af, set<aalta_formula *> &conjuncts);
void to_disjunts(aalta_formula *af, set<aalta_formula *> &disjunts);

// void fill_in_Y_edgeset(std::unordered_set<int> &partial_edgeset);
void fill_in_X_edgeset(std::unordered_set<int> &partial_edgeset);
aalta_formula *eliminateY(aalta_formula *af, const unordered_set<int> &Y);

#endif