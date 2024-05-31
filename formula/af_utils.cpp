#include "af_utils.h"
#include <map>
#include "synthesis.h"

std::map<aalta_formula *, aalta_formula *> f_to_xnf;

aalta_formula *xnf(aalta_formula *phi)
{
    if (phi == NULL)
        return NULL;
    if (f_to_xnf.find(phi) != f_to_xnf.end())
        return f_to_xnf[phi];
    int op = phi->oper();
    if (op >= 11)
        return phi;
    switch (op)
    {
    case aalta_formula::True:
    case aalta_formula::False:
    case aalta_formula::Not:
    case aalta_formula::Next:
    case aalta_formula::WNext:
    {
        return phi;
    }
    case aalta_formula::And:
    {
        aalta_formula *xnf_phi;
        aalta_formula *lf = xnf(phi->l_af());
        if ((lf->oper()) == aalta_formula::False)
            xnf_phi = aalta_formula::FALSE();
        else
        {
            aalta_formula *rf = xnf(phi->r_af());
            if ((rf->oper()) == aalta_formula::False)
                xnf_phi = aalta_formula::FALSE();
            else if ((lf->oper()) == aalta_formula::True)
                xnf_phi = rf;
            else if ((rf->oper()) == aalta_formula::True)
                xnf_phi = lf;
            else
                xnf_phi = aalta_formula(aalta_formula::And, lf, rf).unique();
        }
        f_to_xnf.insert({phi, xnf_phi});
        return xnf_phi;
    }
    case aalta_formula::Or:
    {
        aalta_formula *xnf_phi;
        aalta_formula *lf = xnf(phi->l_af());
        if ((lf->oper()) == aalta_formula::True)
            xnf_phi = aalta_formula::TRUE();
        else
        {
            aalta_formula *rf = xnf(phi->r_af());
            if ((rf->oper()) == aalta_formula::True)
                xnf_phi = aalta_formula::TRUE();
            else if ((lf->oper()) == aalta_formula::False)
                xnf_phi = rf;
            else if ((rf->oper()) == aalta_formula::False)
                xnf_phi = lf;
            else
                xnf_phi = aalta_formula(aalta_formula::Or, lf, rf).unique();
        }
        f_to_xnf.insert({phi, xnf_phi});
        return xnf_phi;
    }
    case aalta_formula::Until:
    { // l U r=xnf(r) | (xnf(l) & X(l U r))
        aalta_formula *next_phi = aalta_formula(aalta_formula::Next, NULL, phi).unique();
        aalta_formula *xnf_l_and_next_phi = (phi->l_af()->oper() == aalta_formula::True)
                                                ? next_phi // futrue
                                                : aalta_formula(aalta_formula::And, xnf(phi->l_af()), next_phi).unique();
        aalta_formula *xnf_phi = aalta_formula(aalta_formula::Or, xnf(phi->r_af()), xnf_l_and_next_phi).unique();
        f_to_xnf.insert({phi, xnf_phi});
        return xnf_phi;
    }
    case aalta_formula::Release:
    { // l R r=xnf(r) & (xnf(l) | WX(l R r))
        aalta_formula *wnext_phi = aalta_formula(aalta_formula::WNext, NULL, phi).unique();
        aalta_formula *xnf_l_or_wnext_phi = (phi->l_af()->oper() == aalta_formula::False)
                                                ? wnext_phi // global
                                                : aalta_formula(aalta_formula::Or, xnf(phi->l_af()), wnext_phi).unique();
        aalta_formula *xnf_phi = aalta_formula(aalta_formula::And, xnf(phi->r_af()), xnf_l_or_wnext_phi).unique();
        f_to_xnf.insert({phi, xnf_phi});
        return xnf_phi;
    }
    }
}

aalta_formula *FormulaProgression(aalta_formula *predecessor, unordered_set<int> &edge)
{
    if (predecessor == NULL)
        return NULL;
    int op = predecessor->oper();
    if (op == aalta_formula::Not || op >= 11)
    { // literal
        int lit = (op >= 11) ? op : (-((predecessor->r_af())->oper()));
        return ((edge.find(lit) != edge.end()) ? aalta_formula::TRUE()
                                               : aalta_formula::FALSE());
    }
    switch (op)
    {
    case aalta_formula::True:
    case aalta_formula::False:
    {
        return predecessor;
    }
    case aalta_formula::And:
    {
        aalta_formula *lf = FormulaProgression(predecessor->l_af(), edge);
        if ((lf->oper()) == aalta_formula::False)
            return aalta_formula::FALSE();
        aalta_formula *rf = FormulaProgression(predecessor->r_af(), edge);
        if ((rf->oper()) == aalta_formula::False)
            return aalta_formula::FALSE();
        else if ((lf->oper()) == aalta_formula::True)
            return rf;
        else if ((rf->oper()) == aalta_formula::True)
            return lf;
        else
            return aalta_formula(aalta_formula::And, lf, rf).unique();
    }
    case aalta_formula::Or:
    {
        aalta_formula *l_fp = FormulaProgression(predecessor->l_af(), edge);
        if ((l_fp->oper()) == aalta_formula::True)
            return aalta_formula::TRUE();
        aalta_formula *r_fp = FormulaProgression(predecessor->r_af(), edge);
        if ((r_fp->oper()) == aalta_formula::True)
            return aalta_formula::TRUE();
        else if ((l_fp->oper()) == aalta_formula::False)
            return r_fp;
        else if ((r_fp->oper()) == aalta_formula::False)
            return l_fp;
        else
            return aalta_formula(aalta_formula::Or, l_fp, r_fp).unique();
    }
    case aalta_formula::Next:
    case aalta_formula::WNext:
    {
        return (predecessor->r_af())->unique();
    }
    // if predecessor is in XNF,
    // the following two cases cannot appear
    case aalta_formula::Until:
    { // l U r = r | (l & X(l U r))
        aalta_formula *first_part = FormulaProgression(predecessor->r_af(), edge);
        if ((first_part->oper()) == aalta_formula::True)
            return aalta_formula::TRUE();
        aalta_formula *l_fp = FormulaProgression(predecessor->l_af(), edge);
        aalta_formula *second_part = NULL;
        if ((l_fp->oper()) == aalta_formula::True)
        {
            if (first_part == predecessor->r_af())
                return predecessor;
            second_part = predecessor;
        }
        else if ((l_fp->oper()) == aalta_formula::False)
            return first_part;
        else
            second_part = aalta_formula(aalta_formula::And, l_fp, predecessor).unique();
        if ((first_part->oper()) == aalta_formula::False)
            return second_part;
        else
            return aalta_formula(aalta_formula::Or, first_part, second_part).unique();
    }
    case aalta_formula::Release:
    { // l R r = r & (l | N(l R r))
        aalta_formula *first_part = FormulaProgression(predecessor->r_af(), edge);
        if ((first_part->oper()) == aalta_formula::False)
            return aalta_formula::FALSE();
        aalta_formula *l_fp = FormulaProgression(predecessor->l_af(), edge);
        aalta_formula *second_part = NULL;
        if ((l_fp->oper()) == aalta_formula::True)
            return first_part;
        else if ((l_fp->oper()) == aalta_formula::False)
            second_part = predecessor;
        else
            second_part = aalta_formula(aalta_formula::Or, l_fp, predecessor).unique();
        if ((first_part->oper()) == aalta_formula::True)
            return second_part;
        else
            return aalta_formula(aalta_formula::And, first_part, second_part).unique();
    }
    }
}

bool IsAcc(aalta_formula *predecessor, unordered_set<int> &tmp_edge)
{
    if (predecessor == NULL)
        return false;
    int op = predecessor->oper();
    if (op == aalta_formula::Not || op >= 11)
    { // literal
        int lit = (op >= 11) ? op : (-((predecessor->r_af())->oper()));
        return tmp_edge.find(lit) != tmp_edge.end();
    }
    switch (op)
    {
    case aalta_formula::True:
    case aalta_formula::WNext:
        return true;
    case aalta_formula::False:
    case aalta_formula::Next:
        return false;
    case aalta_formula::And:
        return IsAcc(predecessor->l_af(), tmp_edge) && IsAcc(predecessor->r_af(), tmp_edge);
    case aalta_formula::Or:
        return IsAcc(predecessor->l_af(), tmp_edge) || IsAcc(predecessor->r_af(), tmp_edge);
    case aalta_formula::Until:
    case aalta_formula::Release:
        return IsAcc(predecessor->r_af(), tmp_edge);
    }
}

void fill_in_edgeset(std::unordered_set<int> &partial_edgeset)
{
    if (partial_edgeset.size() == Syn_Frame::num_varX + Syn_Frame::num_varY)
        return;
    for (auto it : Syn_Frame::var_X)
    {
        if (partial_edgeset.find(it) == partial_edgeset.end() && partial_edgeset.find(-(it)) == partial_edgeset.end())
        {
            partial_edgeset.insert(it);
        }
    }
    for (auto it : Syn_Frame::var_Y)
    {
        if (partial_edgeset.find(it) == partial_edgeset.end() && partial_edgeset.find(-(it)) == partial_edgeset.end())
        {
            partial_edgeset.insert(it);
        }
    }
}

void to_conjunts(aalta_formula *af, vector<aalta_formula *> &conjuncts)
{
    if (af == NULL)
        return;
    // if (af->oper() == aalta_formula::Not)
    //   conjuncts.push_back(af->r_af());
    // else
    if (af->oper() == aalta_formula::And) // || af->oper() == aalta_formula::Or)
    {
        to_conjunts(af->l_af(), conjuncts);
        to_conjunts(af->r_af(), conjuncts);
    }
    else
        conjuncts.push_back(af);
}

void to_conjunts(aalta_formula *af, set<aalta_formula *> &conjuncts)
{
    if (af == NULL)
        return;
    if (af->oper() == aalta_formula::And)
    {
        to_conjunts(af->l_af(), conjuncts);
        to_conjunts(af->r_af(), conjuncts);
    }
    else
        conjuncts.insert(af);
}

void to_disjunts(aalta_formula *af, set<aalta_formula *> &disjunts)
{
    if (af == NULL)
        return;
    if (af->oper() == aalta_formula::Or)
    {
        to_disjunts(af->l_af(), disjunts);
        to_disjunts(af->r_af(), disjunts);
    }
    else
        disjunts.insert(af);
}

// void fill_in_Y_edgeset(std::unordered_set<int> &partial_edgeset)
// {
//     for (auto it : Syn_Frame::var_Y)
//     {
//         if (partial_edgeset.find(it) == partial_edgeset.end() && partial_edgeset.find(-(it)) == partial_edgeset.end())
//         {
//             partial_edgeset.insert(it);
//         }
//     }
// }

// aalta_formula *eliminateY(aalta_formula *af, const unordered_set<int> &Y)
// {
//     if (af == NULL)
//         return NULL;
//     auto op = af->oper();
//     if (op >= 11)
//     {
//         if (Syn_Frame::var_X.find(op) != Syn_Frame::var_X.end()) // x-variable
//             return af;
//         if (Y.find(-op) != Y.end())
//             return aalta_formula::FALSE();
//         else // two cases: op in Y, or op not in Y
//             return aalta_formula::TRUE();
//     }
//     else if (op == aalta_formula::Not)
//     {
//         auto rop = (af->r_af())->oper();
//         if (Syn_Frame::var_X.find(rop) != Syn_Frame::var_X.end()) // x-variable
//             return af;
//         if (Y.find(-rop) != Y.end())
//             return aalta_formula::TRUE();
//         else // two cases: rop in Y, or rop not in Y
//             return aalta_formula::FALSE();
//     }
//     switch (op)
//     {
//     case aalta_formula::True:
//     case aalta_formula::False:
//     case aalta_formula::Next:
//     case aalta_formula::WNext:
//     case aalta_formula::Until:
//     case aalta_formula::Release:
//         return af;
//     case aalta_formula::And:
//     {
//         aalta_formula *p_l = eliminateY(af->l_af(), Y);
//         if (p_l == aalta_formula::FALSE())
//             return aalta_formula::FALSE();
//         aalta_formula *p_r = eliminateY(af->r_af(), Y);
//         if (p_r == aalta_formula::FALSE())
//             return aalta_formula::FALSE();
//         if (p_l == aalta_formula::TRUE())
//             return p_r;
//         if (p_r == aalta_formula::TRUE())
//             return p_l;
//         return aalta_formula(aalta_formula::And, p_l, p_r).unique();
//     }
//     case aalta_formula::Or:
//     {
//         aalta_formula *p_l = eliminateY(af->l_af(), Y);
//         if (p_l == aalta_formula::TRUE())
//             return aalta_formula::TRUE();
//         aalta_formula *p_r = eliminateY(af->r_af(), Y);
//         if (p_r == aalta_formula::TRUE())
//             return aalta_formula::TRUE();
//         if (p_l == aalta_formula::FALSE())
//             return p_r;
//         if (p_r == aalta_formula::FALSE())
//             return p_l;
//         return aalta_formula(aalta_formula::Or, p_l, p_r).unique();
//     }
//     default:
//         assert(false);
//     }
// }