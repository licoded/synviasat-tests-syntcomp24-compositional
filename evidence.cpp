/*
 * File:   evidence.h
 * Author: Jianwen Li
 * Note: Evidence interface for LTLf satisfiability checking
 * Created on August 30, 2017
 */
#include "evidence.h"
#include <assert.h>
#include <iostream>
#include <vector>
#include <string>
#include <unordered_set>
#include "formula/olg_formula.h"
#include "formula/aalta_formula.h"
#include "util/hash_map.h"
#include "synthesis.h"
using namespace std;

namespace aalta
{
	std::vector<std::pair<aalta_formula *, aalta_formula *>> Evidence::sat_trace;
	void Evidence::push(bool tt)
	{
		assert(tt);
		// traces_.push_back("True");
		Evidence::sat_trace.push_back(make_pair(aalta_formula::TRUE(), aalta_formula::TRUE()));
	}

	void Evidence::push(olg_formula &olg)
	{
		hash_map<int, bool> &e = olg._evidence;
		vector<int> v;
		// string s = "(";
		aalta_formula *Y_af = aalta_formula::TRUE();
		aalta_formula *X_af = aalta_formula::TRUE();
		for (hash_map<int, bool>::iterator it = e.begin(); it != e.end(); it++)
		{
			string tmp = aalta_formula::get_name(it->first);
			if (tmp.find("!") != string::npos)
			{
				tmp = tmp.substr(3);				// remove first/open bracket and !/not char
				tmp = tmp.substr(0, tmp.size()-1);	// remove last/close bracket
				tmp = "!!!" + tmp;
			}
			if (tmp == "Tail")
				continue;
			aalta_formula *tmp_f = aalta_formula((it->first), NULL, NULL).unique();
			if (it->second)
			{
				// s += tmp + ", ";
			}
			else
			{
				// s += "-" + tmp + ", ";
				tmp_f = aalta_formula(aalta_formula::Not, NULL, tmp_f).unique();
			}
			if (Syn_Frame::var_Y.find(it->first) != Syn_Frame::var_Y.end())
				Y_af = ((Y_af == aalta_formula::TRUE()) ? tmp_f : aalta_formula(aalta_formula::And, Y_af, tmp_f).unique());
			else
				X_af = ((X_af == aalta_formula::TRUE()) ? tmp_f : aalta_formula(aalta_formula::And, X_af, tmp_f).unique());
		}
		// s += ")";
		// traces_.push_back(s);
		Evidence::sat_trace.push_back(make_pair(X_af, Y_af));
	}

	void Evidence::push(aalta_formula *f)
	{
		aalta_formula::af_prt_set p = f->to_set();
		// string s = "(";
		aalta_formula *Y_af = aalta_formula::TRUE();
		aalta_formula *X_af = aalta_formula::TRUE();
		for (aalta_formula::af_prt_set::iterator it = p.begin(); it != p.end(); it++)
		{
			string tmp = (((*it)->oper()) == aalta_formula::Not) ? ("!!!" + ((*it)->r_af())->to_string()) : ((*it)->to_string());
			if (tmp.find("Tail") != string::npos)
				continue;
			// s += tmp + ", ";
			int op = (((*it)->oper()) == aalta_formula::Not) ? (((*it)->r_af())->oper()) : ((*it)->oper());
			if (Syn_Frame::var_Y.find(op) != Syn_Frame::var_Y.end())
				Y_af = ((Y_af == aalta_formula::TRUE()) ? (*it) : aalta_formula(aalta_formula::And, Y_af, (*it)).unique());
			else
				X_af = ((X_af == aalta_formula::TRUE()) ? (*it) : aalta_formula(aalta_formula::And, X_af, (*it)).unique());
		}
		// s += ")";
		// traces_.push_back(s);
		Evidence::sat_trace.push_back(make_pair(X_af, Y_af));
	}

	void Evidence::pop_back()
	{
		// traces_.pop_back();
		Evidence::sat_trace.pop_back();
	}

	// void Evidence::print()
	// {
	// 	// cout << "Find satisfying model: \n";
	// 	cout << "\t\tLTLf SAT trace: " << endl;
	// 	for (auto it = sat_trace_->begin(); it != sat_trace_->end(); it++)
	// 	{
	// 		aalta_formula *trace_Y = it->first;
	// 		aalta_formula *trace_X = it->second;
	// 		cout
	// 			<< "\t\t\tY = " << trace_Y->to_literal_set_string() << endl
	// 			<< "\t\t\tX = " << trace_X->to_literal_set_string() << endl
	// 			<< "====" << endl;
	// 	}
	// }

	// for synthesis
	// assign undefined value of Y variables
	// aalta_formula *fill_in_Y(aalta_formula *partial_Y)
	// {
	// 	std::unordered_set<int> pa_set;
	// 	partial_Y->to_set(pa_set);
	// 	for (auto it = XY_Partition::var_Y.begin(); it != XY_Partition::var_Y.end(); ++it)
	// 	{
	// 		if (pa_set.find(*it) == pa_set.end() && pa_set.find(-(*it)) == pa_set.end())
	// 		{
	// 			aalta_formula *tmp_lit = aalta_formula(*it, NULL, NULL).unique();
	// 			partial_Y = aalta_formula(aalta_formula::And, partial_Y, tmp_lit).unique();
	// 		}
	// 	}
	// 	return partial_Y;
	// }
}