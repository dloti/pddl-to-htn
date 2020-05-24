#include "create_htn.h"
#include "time.hxx"
#include <cassert>
#define UNORDERED false
#define LISP false
#define JSHOP2H false
//optimizations
#define REACHAB false
#define GORDER false

std::vector<int> direct_reachability;
std::vector<Condition> printed_locks;
std::map<int,Condition> reach_map;
std::map<Condition,int> reach_index;
std::vector<std::string> printedAchieves;
std::map<std::string, int> taskToInvariantMap;
std::map<int, std::map<std::string, std::string> > taskToFluentMap;
bool hasGoalConflicts = false;

void printCondition(std::ostream &out, bool b, Condition &c, const std::string &s, bool z, std::vector<std::string> &v,
		int invariant_number = -1) {

	out << " ( " << (b ? "NOT ( " : "");
	out << s << (z ? (c.neg ? "-" : "-") : "") << c.name;
	if (invariant_number > -1)
		out << invariant_number;
	for (unsigned i = 0; i < v.size(); ++i)
		out << " " << v[i];
	out << (b ? " )" : "") << " )";
}

void printCondition(std::ostream &out, bool b, Condition &c, std::vector<std::string> &v, std::set<int> &m) {
	out << " ( " << (b ? "NOT ( " : "");
	out << c.name;
	for (unsigned i = 0; i < c.params.size(); ++i) {
		m.erase(c.params[i]);
		out << " " << v[c.params[i]];
	}
	out << (b ? " )" : "") << " )";
}

void printTypes(std::ostream &out, Domain &d, std::vector<int> &typeIndexes, std::vector<std::string> &objects) {
	for (unsigned i = 0; i < typeIndexes.size(); ++i)
		out << " ( " << d.types[typeIndexes[i]].name << " " << objects[i] << " )";
}

bool isPosNegInvariant(int invariant_num) {
	return (invs[invariant_num].conds.size() == 2 && (invs[invariant_num].conds[0] == invs[invariant_num].conds[1])
			&& (invs[invariant_num].conds[0].neg || invs[invariant_num].conds[1].neg));
}

void printDOMethods(Domain &d, std::ostream &out) {
	for (TripMacroMap::iterator i = macros.begin(); i != macros.end(); ++i) {
//		std::cout << "\nMacros from " << invs[i->first.a].conds[i->first.b] << " to " << invs[i->first.a].conds[i->first.c] << "\n";

		for (unsigned j = 0; j < i->second.size(); ++j)
			if (i->second[j].variable.size() > 0) {
				macro m = i->second[j];
				Action a = d.actions[m.t.a];
				Condition c = a.getCondition(m.t.b);
				Condition t = a.getCondition(m.t.c);
//				std::cout << m.t << "\n";
//				std::cout << a << "\n" << c << "\n" << m << "\n";
//				std::cout<<i->first.a<<invs[i->first.a].conds.size()<<" "<< invs[i->first.a].conds<<"\n";
				out << "    ( :METHOD";
				std::ostringstream ts;
				ts << d.parametrizeCondition(a, "DO-" + c.name + "-", false, i->first.a);
				out <<ts.str()<< "\n";
				taskToInvariantMap[ts.str()] = i->first.a;
				taskToFluentMap[i->first.a][ts.str()] =  d.parametrizeCondition(a, t, "", false);
				ts.str("");
				ts.clear();

				ts<<d.parametrizeCondition(a, "!", false);
				taskToFluentMap[i->first.a][ts.str()] = d.parametrizeCondition(a, t, "", false);

				out << "              (";
				if (isPosNegInvariant(i->first.a))
					out << " ( NOT";
				out << d.parametrizeCondition(a, c, "", false);
				if (isPosNegInvariant(i->first.a))
					out << " )";

//				if (reach_idx != -1) {
//					Condition pc = invs[i->first.a].conds[0];
//					for (int k = m.rorder.size() - 1; k >= 0; --k) {
//						CondPairSet::iterator it = m.variable.begin();
//						for (int l = 0; l < m.rorder[k]; ++l, ++it)
//							;
//						Condition c2 = a.pre[it->second.first];
//						out << " (" << c2.name;
//						for (unsigned kp = 0; kp < c2.params.size(); ++kp) {
//							if(d.types[a.params[c2.params[kp]]] == reach_map[i->first.a])
//								out << " ?" << d.types[a.params[c2.params[kp]]].name << c2.params[kp]+1;
//							else
//								out << " ?" << d.types[a.params[c2.params[kp]]].name << c2.params[kp];
//						}
//						out << " )";
//					}
//
//					out<<" (REACHABLE"<<reach_idx<<"-"<<rc.name<<" ) ";
//				}
				out << " )\n";
				out	<< "              (";
				
				// if (!isPosNegInvariant(i->first.a) && GORDER){
				// 	out << d.parametrizeCondition(a, c, "!!LOCK-", false);
				// }
				
				out << std::string(
										(UNORDERED || (m.unordered_precs && m.rorder.size() > 0)) ?
												" ( :UNORDERED" : "");
			

				for (int k = m.rorder.size() - 1; k >= 0; --k) {
					CondPairSet::iterator it = m.variable.begin();
					for (int l = 0; l < m.rorder[k]; ++l, ++it)
						;
					Condition c2 = a.pre[it->second.first];
					//std::cout << k << "," << c2.name << "\n";
					std::string s(c2.neg ? "" : "ACHIEVE-");

					out << d.parametrizeCondition(a, c2, s, false);
				}
				out << std::string((UNORDERED || (m.unordered_precs && m.rorder.size() > 0)) ? ")" : "");
				for (CondPairSet::iterator it = m.variable.begin(); it != m.variable.end(); ++it) {
					Condition c2 = a.pre[it->second.first];
					std::string s(c2.neg ? "" : "IFUNLOCK-");
					out << d.parametrizeCondition(a, c2, s, false);
				}

				if (!isPosNegInvariant(i->first.a)){
					// if(!GORDER)
					// 	out << d.parametrizeCondition(a, c, "IFUNLOCK-", false);
					// else
					if(GORDER)
						out << d.parametrizeCondition(a, c, "!!UNLOCK-", false);
				}

				out << d.parametrizeCondition(a, "!", false);
			
				out << " )\n    )\n";
			}
	}
}

void printHDDLDOMethods(Domain &d, std::ostream &out) {
	for (TripMacroMap::iterator i = macros.begin(); i != macros.end(); ++i) {
//		std::cout << "\nMacros from " << invs[i->first.a].conds[i->first.b] << " to " << invs[i->first.a].conds[i->first.c] << "\n";

		for (unsigned j = 0; j < i->second.size(); ++j)
			if (i->second[j].variable.size() > 0) {
				macro m = i->second[j];
				Action a = d.actions[m.t.a];
				Condition c = a.getCondition(m.t.b);
				Condition t = a.getCondition(m.t.c);
				out<<"(:task "<< d.parametrizeHDDLCondition(a, "DO-" + c.name + "-", i->first.a)<<std::endl
				   <<")"<<std::endl;
				out<<"(:method ";
				std::ostringstream ts;
				ts << d.parametrizeHDDLCondition(a, "M-DO-" + c.name + "-", i->first.a);
				out <<ts.str()<< "\n";
				taskToInvariantMap[ts.str()] = i->first.a;
				taskToFluentMap[i->first.a][ts.str()] =  d.parametrizeCondition(a, t, "", false);
				ts.str("");
				ts.clear();

				out<<"\t:task"<<d.parametrizeCondition(a, "DO-" + c.name + "-",false, i->first.a)<<std::endl;

				out<<"\t:precondition (and ";
					if (isPosNegInvariant(i->first.a))
						out << " ( NOT";
					out << d.parametrizeCondition(a, c, "", false);
					if (isPosNegInvariant(i->first.a))
						out << " )";
				out<<")"<<std::endl;
				
				if(m.unordered_precs && m.rorder.size() > 1)
					out<<"\t:subtasks (and ";
				else 
					out<<"\t:ordered-subtasks (and ";
				for (int k = m.rorder.size() - 1; k >= 0; --k) {
					CondPairSet::iterator it = m.variable.begin();
					for (int l = 0; l < m.rorder[k]; ++l, ++it)
						;
					Condition c2 = a.pre[it->second.first];
					//std::cout << k << "," << c2.name << "\n";
					std::string s(c2.neg ? "" : "ACHIEVE-");

					out << d.parametrizeCondition(a, c2, s, false);
				}
				// for (CondPairSet::iterator it = m.variable.begin(); it != m.variable.end(); ++it) {
				// 	Condition c2 = a.pre[it->second.first];
				// 	std::string s(c2.neg ? "" : "IFUNLOCK-");
				// 	out << d.parametrizeCondition(a, c2, s, false);
				// }
				out << d.parametrizeCondition(a, "!", false);
			
				out << " )"<<std::endl;
				out<<")"<<std::endl;
			}
	}
}

void printInnerACHIEVE(Domain &d, std::ostream &out, int invariant_num, int condition_num, Condition& pred,
		std::vector<std::string>& params) {
	Condition c = invs[invariant_num].conds[condition_num];
	if (isPosNegInvariant(invariant_num) && c.neg)
		return;
	std::ostringstream ts;
	out << "    ( :METHOD";
	printCondition(ts, false, c, "ACHIEVE", true, params, invariant_num);
	out << ts.str();
	taskToInvariantMap[ts.str()] = invariant_num;
	taskToFluentMap[invariant_num][ts.str()] = d.parametrizeCondition(c, "", false);
	out << "\n";
	out << "              (";
	printCondition(out, pred.neg, pred, "", false, params);
	printTypes(out, d, pred.params, params);
	out << " )\n              ( )\n";
	out << "    )\n";
}

std::string printHDDLInnerACHIEVE(Domain &d, std::ostream &out, int invariant_num, int condition_num, Condition& pred,
		std::vector<std::string>& params) {
	Condition c = invs[invariant_num].conds[condition_num];
	if (isPosNegInvariant(invariant_num) && c.neg)
		return "";
	std::ostringstream ts;
	ts<<d.parametrizeHDDLCondition(c, "ACHIEVE-", invariant_num);
	out<<"( :task "<<ts.str()<<std::endl<<")"<<std::endl;
	out << "( :method "<<"M-"<<ts.str()<<std::endl;
	taskToInvariantMap[ts.str()] = invariant_num;
	taskToFluentMap[invariant_num][ts.str()] = d.parametrizeCondition(c, "", false);
	out<<"\t:precondition ";
		printCondition(out, pred.neg, pred, "", false, params);
	out<<std::endl;
	out<<"\t:task"<<d.parametrizeCondition(c, "ACHIEVE-",false, invariant_num)<<std::endl;
	out<<"\t:subtasks ( )"<<std::endl;
	out<<")"<<std::endl;

	return d.parametrizeCondition(c, "ACHIEVE-",false, invariant_num);
}

void printACHIEVEOps(Domain &d, std::ostream &out) {
	for (unsigned i = 0; i < invs.size(); ++i) {
		unsigned j = 0;
		out << "    ( :OPERATOR ( !!ACHIEVE" << i;
		std::multiset<int>::iterator it;
		for (it = invs[i].types.begin(); it != invs[i].types.end(); ++it, ++j)
			out << " ?" << d.types[*it].name << j;
		out << " )\n";
		out << "                ( ";
		out << ")\n";
		out << "                ( )\n";
		out << "                (";

		for (j = 0; j < invs[i].conds.size(); ++j) {
			if (invs[i].conds[j].neg)
				continue;
			unsigned l = 0;
			it = invs[i].types.begin();
			Condition c = invs[i].conds[j];
			std::vector<std::string> params(c.params.size());
			int x = d.pmap[c.name];
			//forall fix
			std::string forallstr = "";
			bool gotOne = false;
			if (c.params.size() > 0) {
				std::set<int> s = invs[i].preds[c.neg ? -1 - x : x];
				std::string fallparams = "";
				for (unsigned k = 0; k < c.params.size(); ++k) {
					std::ostringstream os;
					if (s.find(k) != s.end()) {
						os << "?" << d.types[*(it++)].name << l++;
						params[k] = os.str();
					}
				}
				for (unsigned k = 0; k < c.params.size(); ++k) {
					if (s.find(k) != s.end())
						continue;
					std::ostringstream os;
					os << "?" << d.types[c.params[k]].name << l++;
					params[k] = os.str();
					fallparams += " " + os.str();
				}
				if (fallparams.length() > 0) gotOne = true;
				if (gotOne) {
					forallstr += " (" + fallparams + " ) (";
					for (unsigned k = 0; k < c.params.size(); ++k)
						if (s.find(k) == s.end())
							forallstr += " " + d.types[c.params[k]].name + " " + params[k];
					forallstr += " )";
					forallstr = " ( FORALL " + forallstr + " (";
				}
			}
			out << forallstr;
            printCondition(out, false, c, "ACHIEVING", true, params);
			//printCondition(out, false, c, "ACHIEVING", true, params, i);
			if (gotOne)
				out << " ) )";
			//printCondition(out, false, c, "VISITED", true, params );
		}
		out << " )\n";
		out << "    )\n";
	}
}

void printSTOPALLOps(Domain &d, std::ostream &out) {
	for (unsigned i = 0; i < invs.size(); ++i) {
		unsigned j = 0;
		out << "    ( :OPERATOR ( !!STOPALL" << i;
		std::multiset<int>::iterator it;
		for (it = invs[i].types.begin(); it != invs[i].types.end(); ++it, ++j)
			out << " ?" << d.types[*it].name << j;
		out << " )\n";
		out << "                ( ";
		out << ")\n";
		out << "                (";

		for (j = 0; j < invs[i].conds.size(); ++j) {
			if (invs[i].conds[j].neg)
				continue;
			unsigned l = 0;
			it = invs[i].types.begin();
			Condition c = invs[i].conds[j];
			std::vector<std::string> params(c.params.size());
			int pred = d.pmap[c.name];
			std::set<int> s = invs[i].preds[c.neg ? -1 - pred : pred];
			//forall fix
			std::string forallstr = "";
			bool gotOne = false;
			if (c.params.size() > 0) {
				std::string fallparams = "";
				for (unsigned k = 0; k < c.params.size(); ++k) {
					std::ostringstream os;
					if (s.find(k) != s.end()) {
						os << "?" << d.types[*(it++)].name << l++;
						params[k]=os.str();
					}
				}
				for (unsigned k = 0; k < c.params.size(); ++k) {
					if (s.find(k) != s.end()) continue;
					std::ostringstream os;
					os << "?" << d.types[c.params[k]].name << l++;
					params[k]=os.str();
					fallparams += " " + os.str();
				}
				if (fallparams.length() > 0) gotOne = true;
				if (gotOne) {
					forallstr += " (" + fallparams + " ) (";
					for (unsigned k = 0; k < c.params.size(); ++k)
						if (s.find(k) == s.end())
							forallstr += " " + d.types[c.params[k]].name + " " + params[k];
					forallstr += " )";
					forallstr = " ( FORALL " + forallstr + " (";
				}
			}
			out << forallstr;
            printCondition(out, false, c, "ACHIEVING", true, params);
			printCondition(out, false, c, "VISITED", true, params);
			//printCondition(out, false, c, "ACHIEVING", true, params, i);
			//printCondition(out, false, c, "VISITED", true, params, i);
			if (gotOne)
				out << " ) )";
		}
		out << " )\n";
		out << "                ( )\n    )\n";
	}
}

//print entry point ACHIEVE methods
void printTopACHIEVE(Domain& d, std::ostream &out, std::vector<std::string>& param_types,
		std::vector<std::string>& params, int invariant_num, int condition_num, Condition& pred) {
	Condition c = invs[invariant_num].conds[condition_num];
	int x = d.pmap[c.name];
	std::set<int> s = invs[invariant_num].preds[c.neg ? -1 - x : x];
	if (isPosNegInvariant(invariant_num) && c.neg)
		return;
	if (std::find(printed_locks.begin(), printed_locks.end(), c) == printed_locks.end()) {
		printed_locks.push_back(c);
		//LOCKED-X -> FLAG-X
		out << "    ( :METHOD";
		printCondition(out, false, c, "ACHIEVE", true, params);
		out << "\n              (";
		printCondition(out, false, c, "LOCKED", true, params);
		for (int i = 0; i < params.size(); ++i)
			out << " ( " + param_types[i] + " " + params[i] + " ) ";
		out << " )\n";
		out << "              (";
		printCondition(out, false, c, "!!FLAG", true, params);
		out << " )\n   )\n";

		//NOT-LOCKED-X, X -> LOCK-X
		out << "    ( :METHOD";
		printCondition(out, false, c, "ACHIEVE", true, params);
		out << "\n              (";
		printCondition(out, false, c, "", false, params);
		for (int i = 0; i < params.size(); ++i)
			out << " ( " + param_types[i] + " " + params[i] + " ) ";
		out << " ( NOT";
		printCondition(out, false, c, "LOCKED", true, params);
		out << " ) )\n";
		out << "              (";
		printCondition(out, false, c, "!!LOCK", true, params);
		out << " )\n    )\n";
	}

	//NOT-LOCKED-X, NOT-X, NOT-ACHIEVING-X -> LIST-OF-TASKS
	out << "    ( :METHOD";
	printCondition(out, false, c, "ACHIEVE", true, params);
	out << "\n              (";
	CondPairMap v = predInvs[x];
	for (CondPairMap::iterator it = v.begin(); it != v.end(); ++it)
		for (PairSet::iterator it1 = it->second.begin(); it1 != it->second.end(); ++it1) {
			if (c.neg != it->first.neg)
				continue;
			out << " ( NOT";
            printCondition(out, false, c, "ACHIEVING", true, params);
			//printCondition(out, false, c, "ACHIEVING", true, params, it1->first);
			out << " )";
		}

	out << " ( NOT";
	printCondition(out, false, c, "", false, params);
	out << " )";

	for (int i = 0; i < params.size(); ++i)
		out << " ( " + param_types[i] + " " + params[i] + " ) ";

	out << " ( NOT";
	printCondition(out, false, c, "LOCKED", true, params);
	out << " ) )\n";
	out << "              (";
	out << " ( !!ACHIEVE" << invariant_num;
	for (unsigned l = 0; l < pred.params.size(); ++l)
		if (s.find(l) != s.end()) {
			out << " " << params[l];
		}
	out << " )";
	printCondition(out, false, c, "ACHIEVE", true, params, invariant_num);
	printCondition(out, false, c, "!!LOCK", true, params);
	out << " ( !!STOPALL" << invariant_num;
	for (unsigned l = 0; l < pred.params.size(); ++l)
		if (s.find(l) != s.end()) {
			out << " " << params[l];
		}
	out << " )";
	out << " )\n    )\n";
}

//print entry point ACHIEVE methods
void printHDDLTopACHIEVE(Domain& d, std::ostream &out, std::vector<std::string>& param_types,
		std::vector<std::string>& params, int invariant_num, int condition_num, Condition& pred) {
	Condition c = invs[invariant_num].conds[condition_num];
	int x = d.pmap[c.name];
	std::set<int> s = invs[invariant_num].preds[c.neg ? -1 - x : x];
	if (isPosNegInvariant(invariant_num) && c.neg)
		return;
	if (std::find(printed_locks.begin(), printed_locks.end(), c) == printed_locks.end()) {
		printed_locks.push_back(c);

		//NOT-LOCKED-X, X -> LOCK-X
		out << "( :task ";
		out<< d.parametrizeHDDLCondition(c, "ACHIEVE-")<<std::endl;
		out<<")"<<std::endl;
		out << "( :method ";
		out<< d.parametrizeHDDLCondition(c, "M-ACHIEVE-")<<std::endl;
		
		out<<"\t:precondition (and";
			printCondition(out, false, c, "", false, params);
		out<<")"<<std::endl;
		out << "\t:task ";
		out<< d.parametrizeCondition(c, "ACHIEVE-", false)<<std::endl;
		out <<"\t:ordered-subtasks ( )"<<std::endl;
		out<<")"<<std::endl;
	}

	//NOT-LOCKED-X, NOT-X, NOT-ACHIEVING-X -> LIST-OF-TASKS
	out << "( :method ";
		out<< d.parametrizeHDDLCondition(c, "M-ACHIEVE-")<<std::endl;
	out<<"\t:precondition";
	out << " ( NOT";
	printCondition(out, false, c, "", false, params);
	out<<")"<<std::endl;
	out << "\t:task ";
	out<< d.parametrizeCondition(c, "ACHIEVE-", false)<<std::endl;
	out <<"\t:subtasks ";
		printCondition(out, false, c, "ACHIEVE", true, params, invariant_num);
	out<<std::endl<<")"<<std::endl;
}

//print solve methods, test and finish operators
void printSOLVE(std::ostream &out, Domain &d, CondVec& gorder) {
	std::vector<std::string> emptyParams, params, argParams;
	for (int i = 0; i < gorder.size(); ++i) {
		argParams.clear();
		params.clear();

		//load parameters of current goal type
		for (unsigned k = 0; k < gorder[i].params.size(); ++k) {
			std::ostringstream os;
			os << d.types[gorder[i].params[k]].name;
			params.push_back(os.str());
			os << k;
			argParams.push_back("?" + os.str());
		}

		std::vector<std::string> cntArgParams = argParams;
		cntArgParams.insert(cntArgParams.begin(), "?CNT");

		//print test operators
		out << "    ( :OPERATOR ";
		printCondition(out, false, gorder[i], "!!TEST", true, emptyParams, i);
		out << "\n"
		//preconitions
				<< "                ( (FORALL (" + argParams[0] + ") ( ";
		printCondition(out, false, gorder[i], "GOAL", true, cntArgParams);
		for (unsigned k = 0; k < params.size(); ++k)
			out << " (" + params[k] + " " + argParams[k] + ")";
		out << " ) (";
		printCondition(out, false, gorder[i], "", false, argParams);
		out << " ) ) )\n"
		//delete
				<< "                ( )\n"
				//add
				<< "                ( )\n" << "    )\n";
		//print finish operators

		out << "    ( :OPERATOR ";
		printCondition(out, false, gorder[i], "!!FINISH", true, cntArgParams, i);
		out << "\n"
		//preconitions
				<< "                (";
		printCondition(out, false, gorder[i], "GOAL", true, cntArgParams);
		for (int k = 0; k < params.size(); ++k)
			out << " (" + params[k] + " " << argParams[k] + ")";
		out << " )\n"
		//delete
				<< "                ( )\n"
				//add
				<< "                (";
		printCondition(out, false, gorder[i], "DID", true, argParams);
		out << " )\n" << "    )\n";

		//print solve methods
		out << "    ( :METHOD (SOLVE ?CNT)\n";
		//preconditions
		out << "                (";
		printCondition(out, false, gorder[i], "GOAL", true, cntArgParams);
		//DID - removed
		printCondition(out, true, gorder[i], "", false, argParams);
		for (unsigned k = 0; k < params.size(); ++k)
			out << " (" << params[k] << " " << argParams[k] << ")";
		out << " )\n";
		//decomposition
		out << "                (";
		if (i > 0)
			printCondition(out, false, gorder[i - 1], "!!TEST", true, emptyParams, i - 1);
		printCondition(out, false, gorder[i], "ACHIEVE", true, argParams);
		printCondition(out, false, gorder[i], "!!FINISH", true, cntArgParams, i);
		out << " (SOLVE 0 ) ";
		out << ") \n";
		out << "    )\n";

		//Counter solve
		out << "    ( :METHOD (SOLVE ?CNT)\n";
		//preconditions
		out << "                (";
		printCondition(out, false, gorder[i], "GOAL", true, cntArgParams);
		//DID - removed
		printCondition(out, false, gorder[i], "", false, argParams);
		for (unsigned k = 0; k < params.size(); ++k)
			out << " (" << params[k] << " " << argParams[k] << ")";
		out << " )\n";
		//decomposition
		out << "                (";
		out << " (SOLVE (call + ?CNT 1) ) ";
		out << ") \n";
		out << "    )\n";
		
	}
		
	//Test solve
	out << "    ( :METHOD (SOLVE ?CNT)\n                ( ) \n                (";
	for (int i = 0; i < gorder.size(); ++i)
		printCondition(out, false, gorder[i], "!!TEST", true, emptyParams, i);
	out << " )\n    )\n";
}

void printAxioms(std::ostream &out, Domain &d){
	out<<"\n\t;AXIOMS\n";
	out<<"\t(:- (same ?x ?x) nil)\n";
	out<<"\t(:- (different ?x ?y) ((not (same ?x ?y))))\n";
	out<<"\t(:- (chksame ?x ?y ?d) ((same ?x ?y) (assign ?d 0)) ((different ?x ?y) (assign ?d 1) ))\n\n";
}

//print goal ordering methods, test and finish operators
void printORDER(std::ostream &out, Domain &d, CondVec& gorder) {
	std::vector<std::string> emptyParams, params, argParams, conf_params, arg_confParams;
	std::vector<int> arg_params_types;
	for (int i = 0; i < gorder.size(); ++i) {
		argParams.clear();
		params.clear();

		//load parameters of current goal type
		for (unsigned k = 0; k < gorder[i].params.size(); ++k) {
			std::ostringstream os;
			arg_params_types.push_back(gorder[i].params[k]);
			os << d.types[gorder[i].params[k]].name;
			params.push_back(os.str());
			os << k;
			argParams.push_back("?" + os.str());
		}

		std::vector<std::string> cntArgParams = argParams;
		cntArgParams.insert(cntArgParams.begin(), "?CNT");

		//print test operators
		out << "    ( :OPERATOR ";
		printCondition(out, false, gorder[i], "!!TEST-ORDER", true, emptyParams, i);
		out << "\n"
		//preconitions
				<< "                ( (FORALL (" + argParams[0] + ") ( ";
		printCondition(out, false, gorder[i], "TGOAL", true, argParams);
		for (unsigned k = 0; k < params.size(); ++k)
			out << " (" + params[k] + " " + argParams[k] + ")";
		out << " ) (";
		printCondition(out, false, gorder[i], "ORDERED", true, argParams);
		out << " ) ) )\n"
		//delete
				<< "                ( )\n"
		//add
				<< "                ( )\n" << "    )\n";
		//print finish operators

		out << "    ( :OPERATOR ";
		printCondition(out, false, gorder[i], "!!FINISH-ORDER", true, cntArgParams, i);
		out << "\n"
		//preconitions
				<< "                (";
		printCondition(out, false, gorder[i], "TGOAL", true, argParams);
		for (int k = 0; k < params.size(); ++k)
			out << " (" + params[k] + " " << argParams[k] + ")";
		//handle conflicts
		if (conflicts.find(gorder[i]) != conflicts.end()) {
			hasGoalConflicts = true;
			std::map<std::vector<int>, std::vector<int> > conf = conflicts[gorder[i]];
			//load parameters of other goal
			for (unsigned k = 0; k < gorder[i].params.size(); ++k) {
				std::ostringstream os;
				os << d.types[gorder[i].params[k]].name;
				conf_params.push_back(os.str());
				os << k + gorder[i].params.size();
				arg_confParams.push_back("?" + os.str());
			}
			for (std::map<std::vector<int>, std::vector<int> >::iterator confit = conf.begin(); confit != conf.end();
					++confit) {
				std::vector<std::string> mix_arg_params = arg_confParams;
				for (int ccnt = 0; ccnt < confit->first.size(); ++ccnt)
						mix_arg_params[confit->first[ccnt]] = argParams[confit->second[ccnt]];
				for (int ccnt = 0; ccnt < confit->first.size(); ++ccnt)
					mix_arg_params[confit->second[ccnt]] = arg_confParams[confit->first[ccnt]];

				//not odrered
				out << "  (FORALL (" + arg_confParams[confit->first[0]] + ") ( ";
				printCondition(out, false, gorder[i], "TGOAL", true, mix_arg_params);
				out << " (" + conf_params[confit->first[0]] + " " << arg_confParams[confit->first[0]] + ")";
				out << " ) (";
				printCondition(out, true, gorder[i], "ORDERED", true, mix_arg_params);
				out << " ) )";

				mix_arg_params = arg_confParams;
				for (int ccnt = 0; ccnt < confit->first.size(); ++ccnt){
						mix_arg_params[confit->second[ccnt]] = argParams[confit->first[ccnt]];
				}
				std::string fparam,ftype;
				for (int ccnt = 0; ccnt < confit->first.size(); ++ccnt) {
					if (d.isSupertype(arg_params_types[confit->second[ccnt]], arg_params_types[confit->first[ccnt]])) {
						std::ostringstream os;
						os << "?" << d.types[gorder[i].params[confit->first[ccnt]]].name
								<< (confit->second[ccnt] + 1 + gorder[i].params.size());
						mix_arg_params[confit->first[ccnt]] = os.str();
						ftype = d.types[gorder[i].params[confit->first[ccnt]]].name;
					} else {
						mix_arg_params[confit->first[ccnt]] = arg_confParams[confit->second[ccnt]];
						ftype = conf_params[confit->first[ccnt]];
					}
					fparam = mix_arg_params[confit->first[ccnt]];
				}
				//odrered
				out << "  (FORALL (" + fparam + ") ( ";
				printCondition(out, false, gorder[i], "TGOAL", true, mix_arg_params);
				out << " (" + ftype + " " << fparam + ")";
				out << " ) (";
				printCondition(out, false, gorder[i], "ORDERED", true, mix_arg_params);
				out << " ) )";
			}
		}
		out << " )\n"
		//delete
				<< "                ( )\n"
				//add
				<< "                (";
		printCondition(out, false, gorder[i], "GOAL", true, cntArgParams);
		printCondition(out, false, gorder[i], "ORDERED", true, argParams);
		out << " )\n" << "    )\n";

		//print solve methods
		out << "    ( :METHOD (ORDER ?CNT)\n";
		//preconditions
		out << "                (";
		printCondition(out, false, gorder[i], "TGOAL", true, argParams);
		printCondition(out, true, gorder[i], "ORDERED", true, argParams);
		for (unsigned k = 0; k < params.size(); ++k)
			out << "(" << params[k] << " " << argParams[k] << ") ";
		out << ") \n";
		//decomposition
		out << "                (";
		if (i > 0)
			printCondition(out, false, gorder[i - 1], "!!TEST-ORDER", true, emptyParams, i - 1);
		printCondition(out, false, gorder[i], "!!FINISH-ORDER", true, cntArgParams, i);
		out << " (ORDER (call + ?CNT 1) ) ";
		out << ") \n";
		out << "    )\n";
	}

	out << "    ( :METHOD (ORDER ?CNT)\n                ( ) \n                (";
	for (int i = 0; i < gorder.size(); ++i)
		printCondition(out, false, gorder[i], "!!TEST-ORDER", true, emptyParams, i);
	out << " )\n    )\n";
}

void printAuxOps(std::ostream &stream, Domain &d) {
	for (unsigned i = 0; i < d.preds.size(); ++i)
		if (d.predActions[i].size() > 0) {
			//check if goal conflict domain and in gorder mode
			d.printPredicate(d.preds[i], stream, true, false, "!!LOCK", "LOCKED");
			if(!hasGoalConflicts && GORDER)
				d.printPredicate(d.preds[i], stream, false, true, d.preds[i], "!!UNLOCK", "LOCKED");
			else
				d.printPredicate(d.preds[i], stream, false, false, "!!UNLOCK", "LOCKED");

			CondPairMap v = predInvs[d.pmap[d.preds[i].name]];
			std::vector<int> inv_nums;
			for (CondPairMap::iterator it = v.begin(); it != v.end(); ++it)
				for (PairSet::iterator it1 = it->second.begin(); it1 != it->second.end(); ++it1)
					if (std::find(inv_nums.begin(), inv_nums.end(), it1->first) == inv_nums.end())
						inv_nums.push_back(it1->first);
			for (unsigned j = 0; j < inv_nums.size(); ++j)
                d.printPredicate(d.preds[i], stream, true, false, "!!VISIT", "VISITED");
				//d.printPredicate(d.preds[i], stream, true, false, "!!VISIT", "VISITED", inv_nums[j]);
			d.printPredicate(d.preds[i], stream, true, false, "!!FLAG", "FLAGGED");
			d.printPredicate(d.preds[i], stream, false, false, "!!UNFLAG", "FLAGGED");
			d.printMethod(d.preds[i], stream, "IFUNLOCK", "FLAGGED");
		}
}

void printHDDLAuxOps(std::ostream &stream, Domain &d) {
	for (unsigned i = 0; i < d.preds.size(); ++i)
		if (d.predActions[i].size() > 0) {
			d.printHDDLAuxAction(d.preds[i], stream, false, false, "!!LOCK", "LOCKED");
			d.printHDDLAuxAction(d.preds[i], stream, true, false, "!!UNLOCK", "LOCKED");

			CondPairMap v = predInvs[d.pmap[d.preds[i].name]];
			std::vector<int> inv_nums;
			for (CondPairMap::iterator it = v.begin(); it != v.end(); ++it)
				for (PairSet::iterator it1 = it->second.begin(); it1 != it->second.end(); ++it1)
					if (std::find(inv_nums.begin(), inv_nums.end(), it1->first) == inv_nums.end())
						inv_nums.push_back(it1->first);
			
            d.printHDDLAuxAction(d.preds[i], stream, false, false, "!!VISIT", "VISITED");
			d.printHDDLAuxAction(d.preds[i], stream, false, false, "!!FLAG", "FLAGGED");
			d.printHDDLAuxAction(d.preds[i], stream, true, false, "!!UNFLAG", "FLAGGED");
			d.printMethod(d.preds[i], stream, "IFUNLOCK", "FLAGGED");
			
		}
}

//PREPROCESS singular invariants
void preprocessReach(std::ostream &out, Domain &d){
	for (int i = 0; i < invs.size(); ++i) {
		if (invs[i].conds.size() > 1 || invs[i].g.edges.size() == 0) continue;

		TripMap tm = invs[i].g.edges[0];
		Condition c = invs[i].conds[0];

		for (TripMap::iterator it = tm.begin(); it != tm.end(); ++it) {
			for (std::vector<trip>::iterator t = it->second.begin(); t != it->second.end(); ++t) {
				bool hasstatic = false;
				for (int j = 0; j < d.actions[t->a].pre.size(); ++j) {
					Condition pc = d.actions[t->a].pre[j];
					d.actions[t->a].typify(pc);
					if (d.actions[t->a].pre.size() == 1 && pc == c) {
						direct_reachability.push_back(i);
					}
					else if(d.actions[t->a].pre.size() > 1){
						 bool found = false;
						 for (int k = 0; k < invs.size(); ++k)
							if (std::find(invs[k].conds.begin(), invs[k].conds.end(), pc) != invs[k].conds.end())
								found = true;
						if(!found) {
							hasstatic = true;
							break;
						}
					}
				}
				if(!hasstatic){
					direct_reachability.push_back(i);
					break;
				}
			}
		}
	}
}


void printTaskToInv(std::ostream &out){
	out<<"\n;method to invariant map\n";
	out<<"(\n";
	for(std::map<std::string, int>::iterator it=taskToInvariantMap.begin();it!=taskToInvariantMap.end();++it){
		out<<"\t"<<it->first<<" = "<<it->second<<"\n";
	}
	out<<")\n";
}

void printTaskToFluent(std::ostream &out){
	out<<"\n;For each invariant mapping from method/operator to original fluent it has to achieve\n";
	for(std::map<int, std::map<std::string, std::string> >::iterator it=taskToFluentMap.begin();it!=taskToFluentMap.end();++it){
		out<<"(\n";
		for(std::map<std::string, std::string>::iterator it1=it->second.begin();it1!=it->second.end();++it1){
			out<<"\t"<<it1->first<<" - "<<it1->second<<"\n";
		}
		out<<")\n";
	}
}

//Wrapper method for printing HTN
void printHTN(Domain &d, Instance& ins, std::ostream &out, std::string domain_name) {
	out << "(define (domain " << domain_name <<std::endl;
	out << "(:requirements :typing)"<<std::endl;
	out << "(:types"<<std::endl;
	auto obj_type = std::find_if(d.types.begin(),d.types.end(),[](const Condition& type) {return "OBJECT" == type.name;});
	d.PDDLPrintTypes(out, std::distance(d.types.begin(), obj_type));
	out<<")"<<std::endl;

	out<<"(:predicates"<<std::endl;
	d.PDDLPrintPredicates(out);
	out<<")"<<std::endl;

	if(REACHAB) {
		preprocessReach(out,d);
		printAxioms(out, d);
	}
	if(GORDER){
		printORDER(out, d, trorder);
		printSOLVE(out, d, trorder);
	}
	d.printHDDLActions(out);
	//printHDDLAuxOps(out, d);
	//printACHIEVEOps(d, out);
	//printSTOPALLOps(d, out);
	printHDDLDOMethods(d, out);

	for (unsigned i = 0; i < invs.size(); ++i) {
		bool isDirReachable = false;
		if(std::find(direct_reachability.begin(),direct_reachability.end(),i)!= direct_reachability.end()){
			isDirReachable = true;
			out<<";DIR-REACH "<<std::endl;
		}
		//std::vector< int > params( invs[i].types.begin(), invs[i].types.end() );
		//std::cout << params << "\n";
		for (unsigned j = 0; j < invs[i].conds.size(); ++j) {
			Condition c = invs[i].conds[j];
			int x = d.pmap[c.name];
			std::set<int> s = invs[i].preds[c.neg ? -1 - x : x];
			//std::cout<<i<<" : s="<<s<<invs[i].types<<c.params<<c<<"\n";
			std::vector<std::string> params(c.params.size()), p1, sort_by, param_types(c.params.size());
			int sort_by_index = -1;
			std::multiset<int>::iterator it = invs[i].types.begin();
			for (unsigned k = 0; k < c.params.size(); ++k) {
				std::ostringstream os;
				os << d.types[c.params[k]].name;
				param_types[k] = os.str();
				os << k;
				params[k] = "?" + os.str();
				if (s.find(k) != s.end()) {
					p1.push_back(params[k]);
				}
				else{
					sort_by.push_back(params[k]);
					sort_by_index = k;
				}
			}
			for (unsigned k = 0; k < invs[i].conds.size(); ++k) {
				std::string hddlTaskParam;
				bool achieveWrap(false);
				Condition pred = invs[i].conds[k];
				if (j == k) {
					if (!achieveWrap) {
						printHDDLTopACHIEVE(d, out, param_types, params, i, j, pred);
						achieveWrap = true;
					}
					hddlTaskParam = printHDDLInnerACHIEVE(d, out, i, j, pred, params);
				}
				if (j != k || invs[i].types.size() < c.params.size()) {
					x = d.pmap[pred.name];
					s = invs[i].preds[pred.neg ? -1 - x : x];
					std::vector<std::string> p2;
					for (unsigned l = 0, m = 0; l < pred.params.size(); ++l) {
						if (s.find(l) == s.end()) {
							std::ostringstream os;
							os << "?" << d.types[pred.params[l]].name << l + c.params.size();
							p2.push_back(os.str());
						} else
							p2.push_back(p1[m++]);
					}

					TripDMap::iterator i2 = invs[i].g.edges.find(k);
					if (i2 != invs[i].g.edges.end())
						for (TripMap::iterator i3 = i2->second.begin(); i3 != i2->second.end(); ++i3) {
							trip t(i, k, i3->first);
							//std::cout << "Trippy " << t << "\n";
							std::vector<macro> v = macros[t];
							for (unsigned z = 0; z < v.size(); ++z) {
								std::set<int> mys;
								Action &a = d.actions[v[z].t.a];
								Condition del = a.getCondition(v[z].t.b);
								Condition add = a.getCondition(v[z].t.c);
								std::vector<std::string> pa,padd;
								//out<<"p2"<<p2<<std::endl;
								
								//out<<"del:"<<del<<" add:"<<add<<"aparam:"<<a.params<<"c:"<<c<<std::endl;
								for (unsigned l = 0; l < a.params.size(); ++l) {
									mys.insert(l);
									std::ostringstream os;
									os << "?" << d.types[a.params[l]].name << l + c.params.size() + pred.params.size();
									pa.push_back(os.str());									
								}
								
								for (unsigned l = 0; l < del.params.size(); ++l) {
									mys.erase(del.params[l]);
									pa[del.params[l]] = p2[l];
								}
								//out<<pa<<std::endl;
								for (unsigned l = 0; l < add.params.size(); ++l) {
									padd.push_back(pa[add.params[l]]);
								}
								
								if (isDirReachable){
									for(unsigned l=0;l<add.params.size();++l){
										mys.erase(add.params[l]);
										pa[add.params[l]] = params[l];
									}
								}

								if (isPosNegInvariant(i) && c.neg)
										continue;
								Condition cadd = add;
								a.typify(cadd);
								bool addsame =(cadd == c);
								bool sort = (c.params.size()>1) && addsame && sort_by_index>-1 && !isDirReachable && GORDER;
								if( sort )
									sort_by.push_back(padd[sort_by_index]);
								
								/*      ( :method ACHIEVE-AT1 
        								:parameters (?CRATE0 - CRATE ?PLACE1 - PLACE ?PLACE3 - PLACE ?SURFACE6 - SURFACE ?HOIST4 - HOIST)
										:task (ACHIEVE-AT1 ?CRATE0 ?PLACE1)
										:precondition (and ( NOT ( AT ?CRATE0 ?PLACE1 ) ) ( AT ?CRATE0 ?PLACE3 ) ( ON ?CRATE0 ?SURFACE6 ))
										:ordered-subtasks(and ( DO-AT-LIFT1 ?HOIST4 ?CRATE0 ?SURFACE6 ?PLACE3 ) ( ACHIEVE-AT1 ?CRATE0 ?PLACE1 ) )
									)
								*/
								std::string taskName = "ACHIEVE-"+c.name+std::to_string(i);
								if (i3->first != j || invs[i].types.size() < invs[i].conds[j].params.size()) {
									std::ostringstream head;
									std::set<std::string> typedParams;
									head << "( :method M-"<<taskName<<std::endl;
									head <<"\t:parameters (";
									for ( unsigned pk = 0; pk < params.size(); ++pk )
										typedParams.insert(" " + params[pk] + " - " + param_types[pk]);
									for (unsigned pk = 0; pk < a.params.size(); ++pk)
										typedParams.insert(" " + pa[pk] + " - " + d.types[a.params[pk]].name);

									for(auto& tp : typedParams)
										head<<tp;
									head<<")"<<std::endl;
									out<<head.str();
									out<<"\t:task "<<hddlTaskParam<<std::endl;
									out << "\t:precondition (and";
									out << " ( NOT";
									printCondition(out, false, c, "", false, params);
									out << " )";
									printCondition(out, pred.neg, pred, "", false, p2);

									for (CondPairSet::iterator i4 = v[0].fixed.begin(); i4 != v[0].fixed.end(); ++i4)
										if (i4->second.second.name != pred.name && i4->second.first < a.pre.size()) {
											Condition c3 = a.pre[i4->second.first];
											if(pred == c3) continue;
											printCondition(out, c3.neg, c3, pa, mys);
										}
									out<<" )"<<std::endl; //end precondtion
									//printTypes(out, d, a.params, pa);
									// if (!isDirReachable) {
									// 	out << " ( NOT";
                                    //     printCondition(out, false, pred, "VISITED", true, p2);
									// 	//printCondition(out, false, pred, "VISITED", true, p2, i);
									// 	out << " )";
									// 	if (!isPosNegInvariant(i) && !pred.neg) {
									// 		out << " ( NOT";
                                    //         printCondition(out, false, add, "VISITED", true, padd);
									// 		//printCondition(out, false, add, "VISITED", true, padd, i);
									// 		out << " )";
									// 	}
									// }
									out<<"\t:ordered-subtasks (and ";
									// if(!isDirReachable) {
									// 	if (!isPosNegInvariant(i) && !pred.neg)
                                    //         printCondition(out, false, pred, "!!VISIT", true, p2);
									// 		//printCondition(out, false, pred, "!!VISIT", true, p2, i);
									// }
									if (v[z].variable.size() > 0) {
										Condition cc(del.name + "-" + a.name, del.neg);
										printCondition(out, false, cc, "DO", true, pa, i);
									} else{
										std::ostringstream ts;
										printCondition(ts, false, a, "!", false, pa);
										out<<ts.str();
										taskToFluentMap[i][ts.str()] = d.parametrizeCondition(cadd,"",false);
									}

									printCondition(out, false, c, "ACHIEVE", true, params, i);
									out << " )\n)\n"; //end ordered-subtasks and end method

								} else if ( i3->first == j &&  invs[i].types.size() >= invs[i].conds[j].params.size()) {
								 	Condition add = a.getCondition( v[z].t.c );
								 	for ( unsigned l = 0; l < add.params.size(); ++l ) {
								 		mys.erase( add.params[l] );
								 		pa[add.params[l]] = params[l];
								 	}
									for (unsigned l = 0; l < add.params.size(); ++l) {
										padd.push_back(pa[add.params[l]]);
									}
								 	out << "    ( :DALO";
								 	printCondition(out, false, c, "ACHIEVE", true, params, i);
								 	out << "\n";
								 	out << "              (";
								 	if(sort)
										out << ":sort-by ?d (";
								 	out << " ( NOT";
								 	printCondition(out, false, c, "", false, params);
								 	out << " )";
								 	printCondition(out, pred.neg, pred, "", false, p2 );


								 	for ( CondPairSet::iterator i4 = v[0].fixed.begin(); i4 != v[0].fixed.end(); ++i4 )
								 		if ( i4->second.second.name != pred.name ) {
								 			Condition c3 = a.pre[i4->second.first];
								 			if(pred == c3) continue;
								 			printCondition(out, c3.neg, c3, pa, mys );
								 		}
								 	printTypes(out, d, a.params, pa );

								 	// out << " ( NOT";
                                    // printCondition(out, false, pred, "VISITED", true, p2);
								 	// //printCondition(out, false, pred, "VISITED", true, p2, i);
								 	// out << " )";
									// if (!isPosNegInvariant(i) && !pred.neg){
									// 	out << " ( NOT";
                                    //     printCondition(out, false, add, "VISITED", true, padd);
									// 	//printCondition(out, false, add, "VISITED", true, padd, i);
									// 	out << " )";
									// }

									//sort-by
									if(sort){
											out<<" (chksame";
											for(int chk=0;chk<sort_by.size();++chk){
												out<<" "<<sort_by[chk];
											}
											out<<" ?d )";
											out << " )";
									}

								 	out << " )\n              (";
								 	// if (!isPosNegInvariant(i) && !pred.neg)
                                    //     printCondition(out, false, pred, "!!VISIT", true, p2);
								 	// 	//printCondition(out, false, pred, "!!VISIT", true, p2, i);

								 	if ( v[z].variable.size() > 0 ) {
								 		//std::cout << del << "," << a << "\n";
								 		Condition cc( del.name + "-" + a.name, v[z].t.b >= 0 );
								 		printCondition(out, false, cc, "DO", true, pa, i);
								 	}
								 	else
								 		printCondition(out, false, a, "!", false, pa );

								 	printCondition(out, false, c, "ACHIEVE", true, params, i);
								 	out << " )\n    )\n";
								 }
								 if(sort_by.size() > 1 )
								 	sort_by.pop_back();
								  //isDirReachable = false;
							}
						}
				}
			}
		}
	}
	out << ")";
	if(JSHOP2H){
		out<<"\n(\n";
		printTaskToInv(out);
		printTaskToFluent(out);
		out<<"\n)\n";
	}
	out << ")\n";
}

int main(int argc, char *argv[]) {
	if (argc < 4) {
		std::cout << "Usage: ./create_htn <domain_name> <domain_file> <instance_file>\n";
		exit(1);
	}

	//float t0, tf;
	//t0 = time_used();
	Domain d(argv[2]);
	Instance ins(d, argv[3]);
	createHTN(argv[1], d, ins);
	printHTN(d, ins, std::cout, argv[1]);
	//tf = time_used();
	//std::cout << std::endl << "Total time: ";
	//report_interval(t0, tf, std::cout);
	//std::cout << std::endl;
	return 0;
}
