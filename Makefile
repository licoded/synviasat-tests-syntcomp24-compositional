
FORMULAFILES	=	formula/aalta_formula.cpp formula/af_utils.cpp formula/olg_formula.cpp formula/olg_item.cpp

PARSERFILES		=	ltlparser/ltl_formula.c ltlparser/ltllexer.c ltlparser/ltlparser.c ltlparser/trans.c 

UTILFILES		=	util/utility.cpp utility.cpp

SOLVER			=	minisat/core/Solver.cc aaltasolver.cpp solver.cpp carsolver.cpp 

CHECKING		=	ltlfchecker.cpp carchecker.cpp evidence.cpp

SYNTHESIS		=	formula_in_bdd.cpp synthesis.cpp edge_cons.cpp preprocessAcc.cpp

BDD_LIB			=	deps/CUDD-install/lib/libcudd.a


ALLFILES		=	main.cpp $(CHECKING) $(SOLVER) $(FORMULAFILES) $(PARSERFILES) $(UTILFILES) $(SYNTHESIS) $(BDD_LIB)


CC	    =   g++ -std=c++11
FLAG    = -I./  -I./minisat/ -isystem./minisat  -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS #-fpermissive 
DEBUGFLAG   =	-D DEBUG -Wall -g #-pg -fsanitize=undefined -fsanitize=address -fno-omit-frame-pointer
RELEASEFLAG = -O3 -static -flto -funroll-loops -fprofile-use #-pg 

ltlfsyn :	release

ltlparser/ltllexer.c :
	ltlparser/grammar/ltllexer.l
	flex ltlparser/grammar/ltllexer.l

ltlparser/ltlparser.c :
	ltlparser/grammar/ltlparser.y
	bison ltlparser/grammar/ltlparser.y
	
	

.PHONY :    release debug clean

release :   $(ALLFILES)
	    $(CC) $(FLAG) $(RELEASEFLAG) $(ALLFILES) -lm -lz -o ltlfsyn

debug :	$(ALLFILES)
	$(CC) $(FLAG) $(DEBUGFLAG) $(ALLFILES) -lm -lz -o ltlfsyn

clean :
	rm -f *.o *~ ltlfsyn
