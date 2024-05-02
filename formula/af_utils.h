#ifndef __AF_UTILS__
#define __AF_UTILS__

#include <unordered_set>
#include "formula/aalta_formula.h"
using namespace aalta;
using namespace std;

aalta_formula *xnf(aalta_formula *af);
aalta_formula *FormulaProgression(aalta_formula *predecessor, unordered_set<int> &edge);
// bool BaseWinningAtY(aalta_formula *end_state, unordered_set<int> &Y);
bool IsAcc(aalta_formula *predecessor, unordered_set<int> &tmp_edge);
void fill_in_edgeset(std::unordered_set<int> &partial_edgeset);

void fill_in_X_edgeset(std::unordered_set<int> &partial_edgeset);
aalta_formula *eliminateY(aalta_formula *af, const unordered_set<int> &Y);
#endif