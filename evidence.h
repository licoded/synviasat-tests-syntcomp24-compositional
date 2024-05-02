/*
 * File:   evidence.h
 * Author: Jianwen Li
 * Note: Evidence interface for LTLf satisfiability checking
 * Created on August 30, 2017
 */

#ifndef EVIDENCE_H
#define EVIDENCE_H

#include "formula/aalta_formula.h"
#include "formula/olg_formula.h"
#include <vector>
#include <string>
#include <iostream>

namespace aalta
{
	class Evidence
	{
	public:
		// functions
		Evidence() { sat_trace.clear();}// = new std::vector<std::pair<aalta_formula *, aalta_formula *>>; };
		~Evidence() {}// delete sat_trace; }
		void print(){
			std::cout<<sat_trace.size()<<std::endl;
			std::cout<<((sat_trace.front()).first)->to_string()<<std::endl;
			std::cout<<((sat_trace.front()).second)->to_string()<<std::endl;}
		void push(bool);
		void push(olg_formula &);
		void push(aalta_formula *);
		void pop_back();

		inline const std::vector<std::pair<aalta_formula *, aalta_formula *>> *get_model_for_synthesis()
		{
			// std::cout<<sat_trace->size()<<std::endl;
			return &(Evidence::sat_trace);
		}

	private:
		// member
		// std::vector<std::string> traces_;

		// for ltlf synthesis
		// tr \in (<X,Y>)*
		static std::vector<std::pair<aalta_formula *, aalta_formula *>> sat_trace;
	};

	// for synthesis
	// assign undefined value of Y variables
	aalta_formula* fill_in_Y(aalta_formula* partial_Y);
}

#endif
