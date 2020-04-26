#include <fstream>
#include "macro.h"


#define HTN_DEBUG false
#define GOAL_DEBUG false
#define PRINT_GRAPHS false

typedef std::map< std::pair< int, int >, std::set< int > > PairSetMap;
typedef std::map< Condition, PairSetMap > CondPSMap;
typedef std::vector< macro > MacroVec;
typedef std::vector< std::pair< bool, macro > > IncMacroVec;
typedef std::set< std::vector< int > > VecSet;

macro gmacro;
std::map<Condition,CondVec> goalTypeMap;
CondVec grorder,trorder;
std::map<Condition, std::map<std::vector<int>, std::vector<int> > > conflicts;
CondPSMap goals;




void createHTN( const std::string &domName, Domain &d, Instance &ins ) {
	// read the invariant candidates from file
	InvSet s;
	std::ostringstream os;
	os << "domains/" << domName << "/inv.txt";
	Filereader f( os.str() );
	for ( std::getline( f.f, f.s ); !f.f.eof(); std::getline( f.f, f.s ) ) {
		SetMap m;
		for ( f.assert( "{" ); f.getChar() != '}'; f.next() ) {
			std::set< int > u;
			int x = f.tokenIndex( d.pmap );
			for ( unsigned j = 0; j < d.preds[x].params.size(); ++j ) {
				f.next();
				std::string t = f.getToken();
				if ( t[0] != '[' ) u.insert( t[0] - '0' ); // !!! SHOULD REALLY CONVERT STRING TO INT !!!
			}
			f.next();
			if ( f.getChar() == ',' ) ++f.c;
			// insert predicate with index x and bound parameters u
			m[x] = u;
		}

		// test candidate to see if it is an invariant
		bool b = true;
		std::set<std::vector<std::string> > u;
		for ( unsigned i = 0; i < ins.init.size(); ++i ) {
			SetMap::iterator j = m.find( d.pmap[ins.init[i].name] );
			if ( j != m.end() ) {
				Condition c = d.preds[d.pmap[ins.init[i].name]];
				std::vector< std::string > v;
				for ( std::set< int >::iterator k = j->second.begin(); k != j->second.end(); ++k ){
					v.push_back( ins.objects[c.params[*k]][ins.init[i].params[*k]] );
				}
				std::set<std::vector<std::string> >::iterator l = u.find( v );
				if ( b &= l == u.end() ) u.insert( v );
			}
		}
		// insert invariant corresponding to the map m
		if ( b ) {s.insert(inv(m));}
		f.c = 0;
	}

	// generate invariant meta-graphs
	actionInvs.resize( d.actions.size() );
	for (InvSet::iterator i = s.begin(); i != s.end(); ++i) {
		if (HTN_DEBUG)
			std::cout << "\nInvariant " << *i << "\n";
		// for each predicate "j" in the invariant
		for (SetMap::const_iterator j = i->preds.begin(); j != i->preds.end(); ++j) {
			// for each action "l" that adds or deletes the predicate
			for (PairSet::iterator l = d.predActions[j->first].begin(); l != d.predActions[j->first].end(); ++l)
				// for each other predicate "k" in the invariant (possibly same)
				for (SetMap::const_iterator k = j; k != i->preds.end(); ++k) {
					// p: first value is action index
					//    second value is (negated) number of parameters (if predicates are different)
					//    second value is index in add or del of action (if predicate is the same)

					//std::cout << " Consider action " << d.actions[l->first].name << " for " << d.preds[j->first] << ","
					//     << j->second << ";" << d.preds[k->first] << "," << k->second << "\n";
					//std::cout<<"action params"<<d.actions[l->first].params<<std::endl;

					std::pair<int, int> p(l->first, j != k ? -1 - d.actions[l->first].params.size() : l->second);
					PairSet::iterator m = d.predActions[k->first].upper_bound(p);
					// for each instance of the same action that changes "k"
					for (; m != d.predActions[k->first].end() && l->first == m->first; ++m) {
						//std::cout << " same action !!!\n";
						// if "j" is deleted and "k" added, or vice versa
						if (l->second < 0 ^ m->second < 0) {
							// insert an edge from "j" to "k" in invariant graph
							insertEdge(*j, *k, l->first, l->second, m->second, d, i->preds);
						}
					}
				}
		}
	}
	// Add invariants for unassigned predicates in action effects
	for ( unsigned i = 0; i < d.preds.size(); ++i )
		if ( d.predActions[i].size() > 0 && predInvs[i].size() == 0 ) {
			// add invariants for non-static predicates not already covered
			std::set< int > u;
			SetMap m;
			for ( unsigned j = 0; j < d.preds[i].params.size(); ++j )
				u.insert( j );
			m[i] = u;
			m[-1-i] = u;

			if ( HTN_DEBUG ) std::cout << "Additional invariant " << m << "\n";
			for ( PairSet::iterator j = d.predActions[i].begin(); j != d.predActions[i].end(); ++j ) {
				if ( HTN_DEBUG ) std::cout << "\ninserting...\n";

				trip t( j->first, j->second, j->second );
				Condition x = d.actions[j->first].typeCondition( j->second );
				std::multiset< int > h( x.params.begin(), x.params.end() );

				int a = invs.size(), e = insertInv( h, m );
				int n = j->second >= 0, o = j->second < 0;
				if ( a == e ) {
					invs[e].insertCond( x );
					insert( i, e, 0, x );
					x.neg = true;
					insert( i, e, 1, x );
					invs[e].conds.push_back( x );
				}

				invs[e].g.insertEdge( n, o, t );
				actionInvs[j->first].insert( trip( e, n, o ) );

				if ( HTN_DEBUG ) {
					TripVec v = invs[e].g.edges[n][o];
					std::cout << invs[e] << ", (" << n << "," << o << "):\n";
					for ( unsigned k = 0; k < v.size(); ++k )
						printTrip( v[k], d, std::cout );
				}
			}
		}



//	//additional connections for downcasted nodes
//	for (unsigned i = 0; i < d.preds.size(); ++i) {
//		PredMap::iterator l = predInvs.find(i);
//		if (l != predInvs.end()) {
//			if (l->second.size() > 1) {
//				for (CondPairMap::iterator m = l->second.begin(); m != l->second.end(); ++m) {
//					for (CondPairMap::iterator o = l->second.begin(); o != l->second.end(); ++o) {
//						if (o == m)
//							continue;
//
//						//check only the bound parameters for every inv where m and o appear
//						for (unsigned j = 0; j < m->first.params.size(); ++j) {
//							if (d.isSupertype(o->first.params[j], m->first.params[j])) {
//								for (PairSet::iterator km = m->second.begin(); km != m->second.end(); ++km) {
//									std::vector<int> mbound = getBoundParams(m->first, km->first,
//											d.pmap[m->first.name]);
//									for (PairSet::iterator ko = o->second.begin(); ko != o->second.end(); ++ko) {
//										if (invs[ko->first].preds != invs[km->first].preds)
//											continue;
//										std::vector<int> obound = getBoundParams(o->first, ko->first,
//												d.pmap[o->first.name]);
//										bool confirmed = false;
//										for (unsigned mi = 0; mi < mbound.size(); ++mi) {
//											for (unsigned oi = 0; oi < obound.size(); ++oi) {
//												if (d.isSupertype(obound[oi], mbound[mi])) {
//													if ( HTN_DEBUG ) std::cout << "Additional nodes should be inserted\n";
//													confirmed = true;
//												}
//											}
//										}
//										if (confirmed) {
//											copyEdges(m->first, o->first, km->first, ko->first, d);
//											break;
//										}
//									}
//								}
//								break;
//							}
//						}
//					}
//				}
//			}
//		}
//	}



	// print information about each predicate
	if ( HTN_DEBUG ) for ( unsigned i = 0; i < d.preds.size(); ++i ) {
		std::cout << "\nPredicate " << d.preds[i] << ":\n";
		for ( PairSet::iterator j = d.predActions[i].begin(); j != d.predActions[i].end(); ++j ) {
			std::cout << "  " << d.actions[j->first].name << ", " << *j << ": ";
			if (j->second < 0)
				std::cout << d.actions[j->first].del[-j->second - 1] << "\n";
			else std::cout << d.actions[j->first].add[j->second] << "\n";
		}
		PredMap::iterator l = predInvs.find(i);
		if ( l != predInvs.end() ){
			for ( CondPairMap::iterator m = l->second.begin(); m != l->second.end(); ++m ) {
				std::cout << "  Version " << m->first << "\n";
				for ( PairSet::iterator k = m->second.begin(); k != m->second.end(); ++k )
					std::cout << "    Invariant " << invs[k->first] << ";" << k->second << "\n";

			}
		}
	}

	// print information about each action
	if ( HTN_DEBUG ) for ( unsigned i = 0; i < d.actions.size(); ++i ) {
		std::cout << "\nAction " << d.actions[i] << "\n";
		for ( TripSet::iterator j = actionInvs[i].begin(); j != actionInvs[i].end(); ++j )
			std::cout << " Inv " << invs[j->a] << ";" << j->b << "->" << j->c << "\n";
	}

	// for each invariant, go through each edge and create macros
	for ( unsigned i = 0; i < invs.size(); ++i ) {
		if ( HTN_DEBUG ) std::cout << "\nInvariant " << invs[i] << "\n";
		// for each edge of the invariant graph from j->first to k->first
		for ( TripDMap::iterator j = invs[i].g.edges.begin(); j != invs[i].g.edges.end(); ++j )
			for ( TripMap::iterator k = j->second.begin(); k != j->second.end(); ++k ) {
				IncMacroVec z;
				trip t( i, j->first, k->first );
				if ( HTN_DEBUG ) std::cout << "\nMacros from " << invs[i].conds[t.b] << " to " << invs[i].conds[t.c] << "\n";

				for ( unsigned l = 0; l < k->second.size(); ++l ) {
					macro m( k->second[l], d );

					bool b = true;
					for ( unsigned n = 0; n < z.size(); ++n ) {
						b &= !( z[n].first && z[n].second.subsumes( m ) );
						if ( z[n].first && m.subsumes( z[n].second ) )
							z[n].first = 0;
					}
					z.push_back( std::make_pair( b, m ) );
				}

				MacroVec w;
				for ( unsigned l = 0; l < z.size(); ++l )
					if ( z[l].first ) {
						if ( HTN_DEBUG ) std::cout << " Non-pruned " << z[l].second;

						z[l].second.generateGraphs( d, true );

						if ( HTN_DEBUG ) std::cout << " Non-pruned " << z[l].second;

						if ( z[l].second.variable.size() == 1 )
							z[l].second.rorder = std::vector< int >( 1, 0 );
						z[l].second.unordered_precs = !(z[l].second.variable.size() < 2 || z[l].second.orderPrecons(d));
//						if ( z[l].sec	//std::cout<<gmacro.graphs<<std::endl;
						//std::reverse(grorder.begin(),grorder.end());
					//	std::cout<<ins.goal<<std::endl;
					//	std::cout<<ins.init<<std::endl;ond.variable.size() <= 2 ||
//						     z[l].second.orderPrecons(d) ) {
//							//if ( z[l].second.variable.size() > 0 ) std::cout << " Kept " << z[l].second;
//
//						}
						w.push_back( z[l].second );
					}
				macros[t] = w;
				//std::cout << "Trippy " << t << "\n";
				//if ( t.a == 1 && t.b == 1 && t.c == 0 ) exit( 0 );
			}
	}

	// get goals
	std::map<int,Condition> goalTypem;
	for ( unsigned i = 0; i < ins.goal.size(); ++i ) {
		if ( GOAL_DEBUG ) std::cout << "\nGoal " << ins.goal[i] << "\n";

		//get predicate index
		int x = d.pmap[ins.goal[i].name];
		//predInvs - Pred_index to (Condition,(inv_idx,cond_idx))
		for ( CondPairMap::iterator j = predInvs[x].begin(); j != predInvs[x].end(); ++j ) {
			//j->first - Condition j->second - (inv_idx, cond_idx)
			bool b = j->first.neg == ins.goal[i].neg;
			if ( GOAL_DEBUG ) std::cout << " try " << j->first << ";" << b << "\n";
			for ( unsigned l = 0; l < d.preds[x].params.size(); ++l ) {
				int val = ins.goal[i].params[l] < 0 ? -1-ins.goal[i].params[l] : ins.goal[i].params[l];
				std::string s = ins.objects[d.preds[x].params[l]][val];
				b &= ins.omap[j->first.params[l]].find( s ) != ins.omap[j->first.params[l]].end();
			}
			if ( b ) for ( PairSet::iterator k = j->second.begin(); k != j->second.end(); ++k ) {
				std::set< int > s;
				if ( GOAL_DEBUG ) std::cout << " match " << *k << "\n";
				//invs[k->first].preds[x] - inv abstract predicates with bound parameters
				for ( std::set< int >::iterator o = invs[k->first].preds[x].begin(); o != invs[k->first].preds[x].end(); ++o )
					s.insert( ins.goal[i].params[*o] );

				if ( GOAL_DEBUG ) std::cout << invs[k->first] << "," << s << "\n";
				if ( invs[k->first].conds.size() == 1 ) {
					CondPSMap::iterator q = insertMap( goals, j->first );
					insertMap( q->second, *k )->second.insert( 0 );
					goalTypem[i]=j->first;
					if(std::find(goalTypeMap[j->first].begin(),goalTypeMap[j->first].end(),ins.goal[i]) == goalTypeMap[j->first].end())
						goalTypeMap[j->first].push_back(ins.goal[i]);
				}
				else if ( invs[k->first].conds.size() == 2 && d.pmap[invs[k->first].conds[1 - k->second].name] == x ) {
					CondPSMap::iterator q = insertMap( goals, j->first );
					insertMap( q->second, *k )->second.insert( 1 - k->second );
					goalTypem[i]=j->first;
					if(std::find(goalTypeMap[j->first].begin(),goalTypeMap[j->first].end(),ins.goal[i]) == goalTypeMap[j->first].end())
						goalTypeMap[j->first].push_back(ins.goal[i]);
				}
				else for ( unsigned l = 0; l < ins.init.size(); ++l ) {
					if ( GOAL_DEBUG )
						std::cout << "check init " << ins.init[l] << "\n";
					int y = d.pmap[ins.init[l].name];
					SetMap::iterator n = invs[k->first].preds.find( y );
					if ( n != invs[k->first].preds.end() ) {
						std::set< int > t;
						for ( std::set< int >::iterator o = n->second.begin(); o != n->second.end(); ++o )
							t.insert( ins.init[l].params[*o] );
						if ( s == t ) {
							unsigned p;
							for ( p = 0; invs[k->first].conds[p].name != ins.init[l].name; ++p );
							if ( GOAL_DEBUG ) std::cout << "Found " << ins.init[l] << "," << s << "," << t << "\n";
							CondPSMap::iterator q = insertMap( goals, j->first );
							insertMap( q->second, *k )->second.insert( p );
							goalTypem[i]=j->first;
							if(std::find(goalTypeMap[j->first].begin(),goalTypeMap[j->first].end(),ins.goal[i]) == goalTypeMap[j->first].end())
								goalTypeMap[j->first].push_back(ins.goal[i]);
						}
					}
				}
			}
		}
	}
	if ( GOAL_DEBUG )
		std::cout << "\nGoals are " << goals << "\n";

	// generate goal macros
	//goals - Condition - [(inv_idx,cond_idx) - (set of parametrs that are the same in init and goal)]
//	gmacro.graphs.resize( 1 );
//	for ( CondPSMap::iterator i = goals.begin(); i != goals.end(); ++i ) {
//		CondGraphMap::iterator k = insertMap( gmacro.graphs[0], i->first );
//		for ( PairSetMap::iterator j = i->second.begin(); j != i->second.end(); ++j ) {
//			SetPairVec u;
//			std::map< int, int > h;
//			for ( unsigned l = 0; l < i->first.params.size(); ++l )
//					h[i->first.params[l]] = l;
//			mgraph g = gmacro.generateGraph( j->first, u, h, d );
//			if ( GOAL_DEBUG ) std::cout << "Goal " << i->first << "," << j->first << ": " << g << "\n";
//			insertMap( k->second, j->first, g );
//		}
//	}
//
//	for ( CondPSMap::iterator i = goals.begin(); i != goals.end(); ++i) {
//		std::cout<<"Cond:"<<i->first<<std::endl;
//		for(PairSetMap::iterator j = i->second.begin(); j!= i->second.end(); ++j){
//			std::cout<<"Pair:"<<j->first<<" Set:"<<j->second<<std::endl;
//		}
//	}

	CondVec gl;
	for(CondPSMap::iterator it = goals.begin();it!=goals.end();++it){
		gl.push_back(it->first);
	}

	std::map<int, int> posmap;
	for(unsigned i=0;i<gl.size();++i){
		for(std::map<int, Condition>::iterator it=goalTypem.begin();it!=goalTypem.end();++it){
			if(it->second==gl[i] && it->second.misc == gl[i].misc){
				posmap[it->first] = i;
			}
		}
	}
	gmacro.generateGoalGraphs(gl,d);
	trorder = gmacro.orderGoalTemplates(goals,d);
	gmacro.orderGoalsFull(goalTypeMap,conflicts, d, ins);

	//Print invariant graphs
	if (PRINT_GRAPHS) {
		std::ofstream fout;
		fout.open("types.txt", std::ofstream::out);
		fout << ins.objects << std::endl;

		for (int i = 0; i < d.types.size(); ++i) {
			fout << d.types[i] << " " << std::endl;
		}
		fout.flush();
		fout.close();
		fout.open((d.name + "graphs.dot").c_str(), std::ofstream::out);
		fout << "digraph invs" << " {\n label=Invs" << ";\n labelloc=top;\n labeljust=left;\n rank=same;\n";
		for (unsigned i = 0; i < invs.size(); ++i) {
			for (unsigned j = 0; j < invs[i].conds.size(); ++j) {
				int x = d.pmap[invs[i].conds[j].name];
				std::vector<int> bound_idx = getBoundIndexes(invs[i].conds[j], i, x);
				fout << j << i << "\t[label=<" << invs[i].conds[j].name;
				fout << "(";
				for (unsigned k = 0; k < invs[i].conds[j].params.size(); ++k) {
					bool underline = false;
					if (std::find(bound_idx.begin(), bound_idx.end(), k) != bound_idx.end())
						underline = true;
					fout << (!underline ? "" : "<u>") << d.types[invs[i].conds[j].params[k]].name.substr(0, 2)
							<< (!underline ? "" : "</u>");
					if (k < invs[i].conds[j].params.size() - 1)
						fout << ",";
				}
				fout << ")>]\n";
			}

			for (TripDMap::iterator it = invs[i].g.edges.begin(); it != invs[i].g.edges.end(); ++it) {
				for (TripMap::iterator it1 = it->second.begin(); it1 != it->second.end(); ++it1) {
					std::vector<trip> w = it1->second;
					for (unsigned j = 0; j < w.size(); ++j) {
						fout << it->first << i << " -> " << it1->first << i << "\t[label=\"" << d.actions[w[j].a].name
								<< "(";

						for (unsigned k = 0; k < d.actions[w[j].a].params.size(); ++k) {
							fout << d.types[d.actions[w[j].a].params[k]].name.substr(0, 2);
							if (k < d.actions[w[j].a].params.size() - 1)
								fout << ",";
						}
						fout << ")" << "\"]\n";
					}
				}
			}
		}
		fout << "}\n";
		fout.flush();
		fout.close();
	}
	//std::reverse(grorder.begin(),grorder.end());
	std::reverse(trorder.begin(),trorder.end());

}
