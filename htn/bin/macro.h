
#include "invariant.h"

#define MACRO_DEBUG false
typedef std::map< std::pair< int, int >, std::set< int > > PairSetMap;
typedef std::map< Condition, PairSetMap > CondPSMap;
//typedef pair<map<int,int>,Condition> mapcond;

// recConditions: recursively find conditions with subtypes
//   k: parameter index of condition
//   c: condition we are interested in
//   u: possible types
//   w: vector of resulting conditions
void recConditions( int k, Condition c, SetVec &u, CondVec &v ) {
	if ( k == c.params.size() ) v.push_back( c );
	else for ( std::set< int >::iterator i = u[k].begin(); i != u[k].end(); ) {
		c.params[k] = *( i++ );
		recConditions( k + 1, c, u, v );
	}
}

// findInvariants: find the conditions with subtypes AND supertypes
//   c: condition
//   d: domain
CondVec findConditions( const Condition &c, Domain &d ) {
	SetVec v;
	for ( unsigned i = 0; i < c.params.size(); ++i ) {
		std::set< int > s = d.getSubtypes( c.params[i] );
		std::set< int > t = d.getSupertypes( c.params[i] );
		s.insert( t.begin(), t.end() );
		if ( c.params[i] < 0 ) {
			t = d.getSubtypes( d.preds[d.pmap[c.name]].params[i] );
			s.insert( t.begin(), t.end() );
			t = d.getSupertypes( d.preds[d.pmap[c.name]].params[i] );
			s.insert( t.begin(), t.end() );
		}
		v.push_back(s);
	}
	CondVec w;
	recConditions( 0, c, v, w );
	return w;
}

// findInvariants: find the conditions with supertypes
//   c: condition
//   d: domain
CondVec findConditionsSuper( const Condition &c, Domain &d ) {
	SetVec v;
	for ( unsigned i = 0; i < c.params.size(); ++i ) {
		std::set< int > s;
		std::set< int > t = d.getSupertypes( c.params[i] );
		s.insert( t.begin(), t.end() );
		if ( c.params[i] < 0 ) {
			t = d.getSupertypes( d.preds[d.pmap[c.name]].params[i] );
			s.insert( t.begin(), t.end() );
		}
		v.push_back(s);
	}
	CondVec w;
	recConditions( 0, c, v, w );
	return w;
}

typedef std::list< PairSet > SetList;
typedef std::map< int, SetList > ListMap;
typedef std::map< int, ListMap > ListDMap;
typedef std::pair< std::pair< int, int >, std::set< int > > SetDPair;
typedef std::vector< SetDPair > SetPairVec;
typedef std::pair< int, SetPairVec > IntVecPair;

struct mgraph;

std::ostream &operator<<( std::ostream &stream, const mgraph &g );

struct mgraph {
	int inv;
	std::vector< int > next;
	ListDMap parents;

	mgraph() {}
	mgraph( int i ) : inv( i ), next( invs[i].conds.size() ) {
		for ( unsigned j = 0; j < next.size(); ++j ) next[j] = j;
	}

	bool subsumes( const mgraph &g ) {
		SetList::iterator n, o;
		ListMap::iterator k, l;
		for ( ListDMap::const_iterator i = g.parents.begin(); i != g.parents.end(); ++i ) {
			ListDMap::iterator j = parents.find( i->first );
			if ( j == parents.end() ) return false;
			for ( ListMap::const_iterator k = i->second.begin(); k != i->second.end(); ++k ) {
				ListMap::iterator l = j->second.find( k->first );
				if ( l == j->second.end() ) return false;
				for ( SetList::const_iterator n = k->second.begin(); n != k->second.end(); ++n ) {
					bool b = false;
					for ( SetList::iterator o = l->second.begin(); o != l->second.end(); ++o )
						b |= includes( n->begin(), n->end(), o->begin(), o->end() );
					if ( !b ) return false;
				}
			}
		}
		return true;
	}

	void insertEdge( int m, int n, const PairSet &s ) {
		// add the weak constraints s to the edge (m,n)
		if ( next[m] == m ) next[m] = n;
		ListDMap::iterator i = insertMap(parents, n);
		ListMap::iterator j = insertMap(i->second, m);
		bool b = true;
		for ( SetList::iterator k = j->second.begin(); k != j->second.end(); ) {
			b &= !includes( s.begin(), s.end(), k->begin(), k->end() );
			if ( b && includes( k->begin(), k->end(), s.begin(), s.end() ) )
				j->second.erase( k++ );
			else k++;
		}
		if ( b ) j->second.push_back( s );
	}

	bool admissible( CondVec &v, std::pair< int, int > &p,
	                 std::set< int > &s, int n, Domain &d, bool allowSingleInvs ) {
		for ( unsigned i = 0; i < v.size(); ++i ) {
			Condition c = invs[p.first].conds[p.second];
			if (invs[p.first].conds.size() == 1 ||
			     v[i].name != c.name ||
			     ( n < 3 && v[i].neg != c.neg || n > 2 && v[i].neg == c.neg ) ) {
				if ( MACRO_DEBUG ) std::cout << "  Is " << v[i] << " admissible for fixed " << p << "," << s << "?\n";
				if ( MACRO_DEBUG ) std::cout << "  Is " << v[i] << " admissible for fixed " << c << "," << s << "?\n";

				// QUICK AND DIRTY: CONSIDER "SINGULAR" INVARIANTS VIOLATED

				SetMap::iterator j = invs[p.first].preds.find( d.pmap[v[i].name] );
				if ( j != invs[p.first].preds.end() &&
				     !( n == 1  && invs[p.first].conds.size() > 1 &&
				        invs[p.first].conds[p.second].name == v[i].name &&
				        invs[p.first].conds[p.second].neg == v[i].neg ) ) {
					std::set< int > t = convert( j->second, v[i].params );
					if ( MACRO_DEBUG ) std::cout << "   Got " << v[i] << " in inv with set " << t << "\n";

					if(!allowSingleInvs && invs[p.first].conds.size() == 1) return false;

					if(s==t && invs[p.first].conds.size() > 1 ){
						if ( MACRO_DEBUG ) std::cout<<"S:"<<s<<"T:"<<t<<std::endl;
						if ( MACRO_DEBUG ) std::cout<<"Inv:"<<invs[p.first]<<std::endl;
						if ( MACRO_DEBUG ) std::cout<<"Condition size:"<<invs[p.first].conds.size()<<std::endl;
						if ( MACRO_DEBUG ) std::cout << "    VIOLATION\n";
						return false;
					}
				}
			}
		}
		return true;
	}

	void permute( int k, int n, std::set< int > &r, std::vector< int > &u,
	              std::multiset< int > &m, std::multiset< int >::iterator i,
	              std::set< int > &s, SetVec &v) {
		if ( i == m.end() ) v.push_back( s );
		else {
			unsigned j = n < *i ? 0 : k+1;
			for ( ; j < u.size(); ++j )
				if ( r.find( j ) == r.end() && u[j] == *i ) {
					s.insert( j );
					std::multiset< int >::iterator l = i;
					permute( j, *i, r, u, m, ++l, s, v );
					s.erase( j );
				}
		}
	}

	SetVec permute( std::set< int > &r, std::vector< int > &u,
	                std::multiset< int > &m ) {
		std::set< int > s;
		SetVec v;
		permute( 0, -1, r, u, m, m.begin(), s, v );
		//std::cout << "   " << u << "," << m << "," << v << "\n";
		return v;
	}

	PairSet weak( trip &t, Domain &d, PairVec &u, bool allowSingleInvs = false ) {
		std::set< int > r;
		PairSet s;
		Condition del = d.actions[t.a].getCondition( t.b );
		Condition add = d.actions[t.a].getCondition( t.c );
		r.insert( del.params.begin(), del.params.end() );
		r.insert( add.params.begin(), add.params.end() );
    
		for ( unsigned i = 0; i < u.size(); ++i ) {
			bool b = true;
			SetVec v = permute( r, d.actions[t.a].params, invs[u[i].first].types );
			for ( unsigned j = 0; j < v.size(); ++j ) {
				b &= admissible( d.actions[t.a].pre, u[i], v[j], 1, d, allowSingleInvs );
				b &= admissible( d.actions[t.a].add, u[i], v[j], 2, d, allowSingleInvs );
				b &= admissible( d.actions[t.a].del, u[i], v[j], 3, d, allowSingleInvs );
			}
			if ( !b ) s.insert( u[i] );
		}
		return s;
	}

	bool admissible( const trip &t, Domain &d, SetPairVec &v, bool allowSingleInvs = false) {
		if(MACRO_DEBUG) std::cout<<"Action"<<d.actions[t.a]<<std::endl;
		for ( unsigned i = 0; i < v.size(); ++i ) {
			std::set< int > s = convert( v[i].second, d.actions[t.a].getCondition( t.c ).params );
			//std::vector<Condition> precs = d.actions[t.a].pre;
			//Condition c = invs[v[i].first.first].conds[v[i].first.second];
			//for(unsigned j=0;j<precs.size();++j)
			//	if(c.name == precs[j].name)
			//		return true;

			if ( !admissible( d.actions[t.a].pre, v[i].first, s, 1, d, allowSingleInvs ) )
				return false;
			if ( !admissible( d.actions[t.a].add, v[i].first, s, 2, d, allowSingleInvs ) )
				return false;
			if ( !admissible( d.actions[t.a].del, v[i].first, s, 3, d, allowSingleInvs ) )
				return false;
		}
		return true;
	}

	SetPairVec funnel( const trip &t, Domain &d, SetPairVec &v ) {
		SetPairVec u;
		for ( unsigned i = 0; i < v.size(); ++i ) {
			Condition del = d.actions[t.a].getCondition( t.b );
			std::set< int > s = convert( v[i].second, d.actions[t.a].getCondition( t.c ).params ), t;
			for ( std::set< int >::iterator j = s.begin(); j != s.end(); ++j ) {
				unsigned k;
				for ( k = 0; k < del.params.size() && del.params[k] != *j; ++k );
				if ( k < del.params.size() ) t.insert( k );
			}
			if ( s.size() == t.size() )
				u.push_back( std::make_pair( v[i].first, t ) );
		}
		return u;
	}

	void BFS( const IntVecPair &p, PairVec &u, Domain &d, bool allowSingleInvs = false ) {
		std::set< IntVecPair > n;
		n.insert(p);

		std::set<int>::iterator k;
		std::vector< IntVecPair > v(1, p);
		for ( unsigned i = 0; i < v.size(); ++i ) {
			std::set<int>::iterator k = invs[inv].g.parents[v[i].first].begin();
			for ( ; k != invs[inv].g.parents[v[i].first].end(); ++k ) {
				TripVec w = invs[inv].g.edges[*k][v[i].first];
				if ( MACRO_DEBUG ) std::cout << "     Possible actions (" << *k << "," << v[i].first << ");" << w << "\n";
				for ( unsigned j = 0; j < w.size(); ++j )
					if ( admissible( w[j], d, v[i].second, allowSingleInvs ) ) {
						if ( MACRO_DEBUG ) std::cout << "    Admissible";
						if ( MACRO_DEBUG ) printTrip( w[j], d, std::cout );

						//std::cout << "Edge from " << *k << "," << invs[inv].conds[*k] << " to " << v[i].first << "," << invs[inv].conds[v[i].first] << "\n";

						insertEdge( *k, v[i].first, weak( w[j], d, u, allowSingleInvs ) );
        
						//std::cout << *this << "\n";

						IntVecPair q( *k, funnel( w[j], d, v[i].second ) );
						if ( n.find(q) == n.end() ) {
							if ( MACRO_DEBUG ) std::cout << "    New edge to " << q << "!!!\n";
							n.insert( q );
							v.push_back( q );
						}
					}
				if ( MACRO_DEBUG ) std::cout << "\n";
			}
		}
	}
};

// pass a macro graph to a stream
std::ostream &operator<<( std::ostream &stream, const mgraph &g ) {
	stream << g.next << "{";
	ListMap::const_iterator i;
	ListDMap::const_iterator j;
	for ( ListDMap::const_iterator i = g.parents.begin(); i != g.parents.end(); ++i )
		for ( ListMap::const_iterator j = i->second.begin(); j != i->second.end(); ++j )
			stream << std::make_pair( j->first, i->first ) << "+(" << j->second << ")";
	return stream << "}";
}

typedef std::pair< std::map< int, int >, std::pair< int, Condition > > CondPair;
typedef std::set< CondPair > CondPairSet;
typedef std::vector< mgraph > GraphVec;
typedef std::map< std::pair< int, int >, mgraph > GraphMap; // (inv_idx,cond_idx), mgraph
typedef std::map< Condition, GraphMap > CondGraphMap;
typedef std::vector< CondGraphMap > CondGraphVec;

struct macro {
	trip t;                            // corresponding action
	std::set< int > rel;               // relevant action params
	std::vector< int > rorder;         // reversed order of pre-cons
	CondPairSet fixed, variable;       // fixed and variable pre-conds
	CondGraphVec graphs;               // macro graphs
	bool unordered_precs;			   // unordered preconditions if true

    // ONE CONDITION MIGHT HAVE MULTIPLE INSTANCES !!! -> "CLEAR" IN DEPOTS

	macro() {}
	macro( const trip &x, Domain &d ) : t( x ) {
		Condition del = d.actions[t.a].getCondition( t.b );
		Condition add = d.actions[t.a].getCondition( t.c );
        //debug
		//std::cout<<std::endl<<"Macro:"<<del<<'-'<<add<<std::endl;

		rel.insert( del.params.begin(), del.params.end() );
		rel.insert( add.params.begin(), add.params.end() );

		del.neg = t.b >= 0;
		insertCond( t.b, del, d );
		//debug
		//std::cout<<"For "<<d.actions[t.a].name<<std::endl;
		for ( unsigned i = 0; i < d.actions[t.a].pre.size(); ++i )
			if ( del != d.actions[t.a].pre[i] )
				insertCond( i, d.actions[t.a].pre[i], d );
		//debug
		 //std::cout<<"Variable: "<<variable<<" - Fixed:"<<fixed<<std::endl;
		 //std::cout<<d.types<<std::endl;
	}

	// insert a condition
	void insertCond( int k, Condition c, Domain &d ) {
		std::map< int, int > m;
		int x = d.pmap[c.name];
		bool b = c != d.actions[t.a].getCondition( t.b ) && d.predActions[x].size() > 0, z = false;
		for ( unsigned i = 0; i < c.params.size(); ++i )
			if ( rel.find( c.params[i] ) != rel.end() ) m[c.params[i]] = i;

		d.actions[t.a].typify( c );

		//mod: find an action that adds c or one of it's supertypes
		// bool f = false;
		// CondVec supertypes = findConditionsSuper( c, d );
		// std::cout<<"Actions that add "<<c.dbgstr(d.types)<<":"<<std::endl;
		// for ( unsigned i = 0; i < supertypes.size(); ++i )
		// 	for (PairSet::iterator l = d.predActions[x].begin(); l != d.predActions[x].end(); ++l)
		// 		 if(l->second>=0) {Condition tmp = d.actions[l->first].add[l->second];
		// 		 	d.actions[l->first].typify(tmp);
		// 		 	if(tmp == supertypes[i]){
		// 		 		std::cout<<d.actions[l->first].name<<"-"<<tmp.dbgstr(d.types)<<std::endl;
		// 		 		f = true;
		// 		 		break;
		// 		 	}
		// 		 }

		// std::cout<<"For condition:"<<c.dbgstr(d.types)<<std::endl;
		CondVec v = findConditions( c, d );
		for ( unsigned i = 0; i < v.size(); ++i )
			z |= predInvs[x].find( v[i] ) != predInvs[x].end();

		// std::cout<<"v:";
		// for(int dbg=0;dbg<v.size();++dbg)
		// 	std::cout<<v[dbg].dbgstr(d.types)<<" ";
		// std::cout<<std::endl;
		// v = findConditionsSuper(c,d);
		// std::cout<<"sv:";
		// for(int dbg=0;dbg<v.size();++dbg)
		// 	std::cout<<v[dbg].dbgstr(d.types)<<" ";
		// std::cout<<std::endl;

		// std::cout<<"predInvs:";
		// for(PredMap::iterator it = predInvs.begin();it!=predInvs.end();++it)
		// 	for(CondPairMap::iterator it1 = it->second.begin();it1!=it->second.end();++it1)
		// 	std::cout<<((Condition)it1->first).dbgstr(d.types)<<" ";
		// std::cout<<std::endl;

		CondPair p( m, std::make_pair( k, c ) );
		if ( b && z ) variable.insert( p );
		else fixed.insert( p );
	}

	// whether a macro subsumed another
	bool subsumes( const macro &m ) {
		return includes( m.fixed.begin(), m.fixed.end(), fixed.begin(), fixed.end()) && includes( m.variable.begin(), m.variable.end(), variable.begin(), variable.end() );
	}
  
	// compute hard constraints on set of pre-conds
	SetPairVec hard( CondPairSet &s, Domain &d ) {
		SetPairVec h;
		for ( CondPairSet::iterator i = s.begin(); i != s.end(); ++i ) {
			int x = d.pmap[i->second.second.name];
			Condition c = d.actions[t.a].getCondition( t.b );
			//std::cout<<d.actions[t.a]<<std::endl;
			if ( i->second.first >= 0 ) c = d.actions[t.a].pre[i->second.first];

			// should this really be with subtypes AND supertypes???
			// (possibly just supertypes)
			CondVec v = findConditions( i->second.second, d );
			//std::cout << "  " << c << " hard? " << v << "\n";
			for ( unsigned j = 0; j < v.size(); ++j ) {
				CondPairMap::iterator l = predInvs[x].find( v[j] );
				if ( l != predInvs[x].end() )
					for ( PairSet::iterator k = l->second.begin(); k != l->second.end(); ++k ) {
						std::set< int > s = convert( invs[k->first].preds[x], c.params );
						h.push_back( std::make_pair( *k, s ) );
					}
			}
		}
		return h;
	}

	// compute hard constraints on set for goals - gets other condition from params
	SetPairVec hardGoal( CondPairSet &s,Condition &c, Domain &d, bool full=false ) {
		SetPairVec h;
		for ( CondPairSet::iterator i = s.begin(); i != s.end(); ++i ) {
			int x = d.pmap[i->second.second.name];
			//Condition c = d.actions[t.a].getCondition( t.b );
			//std::cout<<d.actions[t.a]<<std::endl;
			//if ( i->second.first >= 0 ) c = d.actions[t.a].pre[i->second.first];

			// should this really be with subtypes AND supertypes???
			// (possibly just supertypes)
			CondVec v = findConditions( i->second.second, d );
			//std::cout << "  " << c << " hard? " << v << "\n";
			for ( unsigned j = 0; j < v.size(); ++j ) {
				CondPairMap::iterator l = predInvs[x].find( v[j] );
				if ( l != predInvs[x].end() )
					for ( PairSet::iterator k = l->second.begin(); k != l->second.end(); ++k ) {
						std::set< int > s = convert( invs[k->first].preds[x], c.params );
						h.push_back( std::make_pair( *k, s ) );
					}
			}
		}
		return h;
	}

	// generate graph
	// h: hard constraints on pre-conditions
	// m: map from action parameter to condition parameter
	mgraph generateGraph( const std::pair< int, int > &p, SetPairVec &h,
	                      const std::map< int, int > &m, Domain &d, bool allowSingleInvs = false ) {
		//std::cout << "   M=" << m << "\n";
		mgraph g( p.first );
		std::set< int >::iterator i;
		PairVec u;
		SetPairVec v;
		if(MACRO_DEBUG) std::cout << "   H=" << h << "\n";
		for ( unsigned i = 0; i < h.size(); ++i ) {
			std::set< int > s;
			for ( std::set< int >::iterator j = h[i].second.begin(); j != h[i].second.end(); ++j ) {
				std::map< int, int >::const_iterator k = m.find( *j );
				if ( k != m.end() ) s.insert( k->second );
			}
			if(MACRO_DEBUG) std::cout << "   hard constraint " << h[i] << "," << s << "," << m << "\n";
			if ( s.size() == h[i].second.size() )
				v.push_back( std::make_pair( h[i].first, s ) );
			else u.push_back( h[i].first );
		}
		if(MACRO_DEBUG) std::cout << "   V=" << v << "\n";
		if(MACRO_DEBUG) std::cout << "   U=" << u << "\n";
		if ( MACRO_DEBUG ) std::cout << "   satisfy in " << p << " with restriction " << v << "," << u << "\n";
		if ( MACRO_DEBUG ) std::cout << "   satisfy in " << invs[p.first].conds[p.second] << " with restriction " << v << "," << u << "\n";
		g.BFS( std::make_pair( p.second, v ), u, d, allowSingleInvs );
		return g;
	}

	// generate graphs
	void generateGraphs( Domain &d, bool allowSingleInvs = false ) {
		SetPairVec h = hard( fixed, d );
		for ( CondPairSet::iterator i = variable.begin(); i != variable.end(); ) {
			GraphVec u;
			CondGraphMap m;
			int x = d.pmap[i->second.second.name];
			CondVec v = findConditions( i->second.second, d );
			for ( unsigned j = 0; j < v.size(); ++j ) {
				if ( MACRO_DEBUG )
					std::cout << " Test condition " << v[j] << "\n";
				CondPairMap::iterator l = predInvs[x].find( v[j] );
				if ( l != predInvs[x].end() )
					for ( PairSet::iterator k = l->second.begin(); k != l->second.end(); ++k ) {
						//if ( MACRO_DEBUG ) std::cout << " Candidate " << *k << "\n";
						//std::map< int, int >::const_iterator n;
						//std::set< int > s = invs[k->first].preds[x], t;
						//for ( n = i->first.begin(); n != i->first.end(); ++n )
						//	t.insert( n->second );

						//if ( includes( t.begin(), t.end(), s.begin(), s.end() ) ) {
							if ( MACRO_DEBUG ) std::cout << "   generate graph for " << v[j] << "\n";
							mgraph g = generateGraph( *k, h, i->first, d, allowSingleInvs );
							if ( g.parents.size() > 0 )
								insertMap( m, v[j] )->second[*k] = g;
						//}
					}
			}
			// CONSTANTS NOT HANDLED -> SCHEDULE
			if ( m.size() > 0 ) {
				graphs.push_back( m );
				++i;
			}
			else {
				fixed.insert( *i );
				variable.erase( i++ );
			}
		}
	}

	//generate graphs for goal macro
	void generateGoalGraphs(CondVec &gl, Domain &d ) {
			SetPairVec h = hard( fixed, d );

			int cndNum = 0;
			for ( CondVec::iterator i = gl.begin(); i != gl.end(); ) {
				std::map<int,int> paramMap;
				for(int cnt=0;cnt<i->params.size();++cnt)
					paramMap[i->params[cnt]] = cnt;
				GraphVec u;
				CondGraphMap m;
				int x = d.pmap[i->name];
                //mod
				CondVec v = findConditions( *i, d );
				for ( unsigned j = 0; j < v.size(); ++j ) {
					if ( MACRO_DEBUG )
						std::cout << " Test condition " << v[j] << "\n";
					CondPairMap::iterator l = predInvs[x].find( v[j] );
					if ( l != predInvs[x].end() )
						for ( PairSet::iterator k = l->second.begin(); k != l->second.end(); ++k ) {
							//if ( MACRO_DEBUG ) std::cout << " Candidate " << *k << "\n";
							//std::map< int, int >::const_iterator n;
							//std::set< int > s = invs[k->first].preds[x], t;
							//for ( n = i->first.begin(); n != i->first.end(); ++n )
							//	t.insert( n->second );

							//if ( includes( t.begin(), t.end(), s.begin(), s.end() ) ) {
								if ( MACRO_DEBUG ) std::cout << "   generate graph for " << v[j] << "\n";
								mgraph g = generateGraph( *k, h, paramMap, d );
								if ( g.parents.size() > 0 )
									insertMap( m, v[j] )->second[*k] = g;
							//}
						}
				}
				// CONSTANTS NOT HANDLED -> SCHEDULE
				if ( m.size() > 0 ) {
					graphs.push_back( m );
					++i;
				}
				else {
					fixed.insert( std::make_pair(paramMap, std::make_pair(-1,*i)) );
					gl.erase( i++ );
				}
				++cndNum;
			}
		}

	bool orderPrecons( Domain &d ) {
		CondPairSet s( variable );
        //debug
		//std::cout<<"OP: Variable:"<<s<<std::endl;
		//std::cout<<"Preconds:"<<d.actions[t.a].pre<<std::endl;
		for ( unsigned i = 1; i < variable.size(); ++i ) {
			unsigned k;
			for ( k = 0; find( rorder.begin(), rorder.end(), k ) != rorder.end(); ++k );
			for ( CondPairSet::iterator j = s.begin(); j != s.end(); ++j ) {
                //debug
				if ( MACRO_DEBUG ) std::cout << "   Test condition " << d.actions[t.a].pre[j->second.first]<<"\n";
				std::map< int, int > m;
				CondPairSet u;
				Condition c = d.actions[t.a].pre[j->second.first]; //same as j->second.second
				for ( unsigned l = 0; l < c.params.size(); ++l )
					m[c.params[l]] = l;
				std::set< int > r( c.params.begin(), c.params.end() );

				//for all other precons, find same parameters and make set of (map, (indice, condition))
				for ( CondPairSet::iterator o = s.begin(); o != s.end(); ++o )
					if (o->second.first != j->second.first) {
						std::map< int, int > h;
						c = d.actions[t.a].pre[o->second.first]; //same as o->second.second
						//int x = d.pmap[c.name]; not necessary

						//find all parameters of other condition that are the same
						for ( unsigned l = 0; l < c.params.size(); ++l )
							if ( r.find( c.params[l] ) != r.end() )
								h[c.params[l]] = l;
						u.insert( std::make_pair( h, o->second ) );
						//std::cout << "   Other condition " << c << "," << m << "\n";
					}

				bool b = true;
				SetPairVec h = hard(u, d);
				//std::cout << "   hard " << h << "\n";
				for ( CondGraphMap::iterator l = graphs[k].begin(); l != graphs[k].end(); ++l )
					for ( GraphMap::iterator n = l->second.begin(); n != l->second.end(); ++n ) {
						mgraph g = generateGraph( n->first, h, m, d, false );
						//std::cout << k << ": " << g << " - "<<n->second<<"\n";
						b &= g.subsumes( n->second );
					}
				if ( b ) {
					//std::cout<<"subsumes "<< k << std::endl;
					rorder.push_back( k );
					s.erase( *j );
					break;
				}

				for ( ++k; find( rorder.begin(), rorder.end(), k ) != rorder.end(); ++k );
			}
			if ( rorder.size() < i ) { return false; }
		}

		unsigned k;
		for ( k = 0; find( rorder.begin(), rorder.end(), k ) != rorder.end(); ++k );
			rorder.push_back( k );
		if ( MACRO_DEBUG ) std::cout <<"MDEBUG "<< rorder << "\n";
		return true;
	}

	CondVec orderGoalTemplates(CondPSMap &goals, Domain &d){
		CondVec s;
		CondVec gl;
		for(CondPSMap::iterator it = goals.begin();it!=goals.end();++it){
			s.push_back(it->first);
			gl.push_back(it->first);
		}
		//std::reverse(s.begin(),s.end());
		//std::reverse(gl.begin(),gl.end());
		//std::cout<<s<<std::endl;
		std::vector<Condition> grorder;
		int cndNum = 0;
		for ( unsigned cnt =0; cnt<gl.size();++cnt ) {
			//for ( k = 0; find( grorder.begin(), grorder.end(), k ) != grorder.end(); ++k );
			for ( CondVec::iterator j = s.begin(); j != s.end(); ++j ) {
				if ( MACRO_DEBUG ) std::cout << "   Test condition " << (*j) << "\n";
				std::map< int, int > m;
				CondPairSet u;
				Condition c = *j;
				for ( unsigned l = 0; l < c.params.size(); ++l )
					m[c.params[l]] = l;
				std::set< int > r( c.params.begin(), c.params.end() );

				for ( CondVec::iterator o = s.begin(); o != s.end(); ++o )
					if (o != j) {
						std::map< int, int > h;
						c = *o;
						int x = d.pmap[c.name];
						for ( unsigned l = 0; l < c.params.size(); ++l )
							if ( r.find( c.params[l] ) != r.end() )
								h[c.params[l]] = l;
						u.insert( std::make_pair( h, std::make_pair(cndNum, *o) ));
						//std::cout << "   Other condition " << c << "," << m << "\n";
					}

				bool b = true;
				//c is the other condition
				SetPairVec h = hardGoal(u,c,d);
				///std::cout << "   hard " << h << "\n";
				for ( CondGraphMap::iterator l = graphs[cndNum].begin(); l != graphs[cndNum].end(); ++l )
					for ( GraphMap::iterator n = l->second.begin(); n != l->second.end(); ++n ) {
						mgraph g = generateGraph( n->first, h, m, d, false );
						//std::cout << *j << ": " << g <<" - "<< n->second<<"\n";
						b &= g.subsumes( n->second );
					}
				if ( b ) {
					//std::cout<<"subsumes"<<std::endl;
					grorder.push_back( *j );
					//std::cout<<"Grorder:"<<grorder<<std::endl;
					s.erase( j );
					break;
				}
			}
			++cndNum;
		}
		return grorder;
	}

//TODO
	CondVec orderGoals(CondVec goals,CondVec goalTemp, std::map<int,int>& posmap, Domain &d){
		CondVec s;
		CondVec gl;
		for(unsigned i=0;i<goals.size();++i){
			goals[i].misc = goalTemp[posmap[i]].misc;
			s.push_back(goals[i]);
			gl.push_back(goals[i]);
		}
		std::vector<Condition> grorder;
		int cndNum = 0;
		for ( unsigned cnt =0; cnt<gl.size();++cnt ) {
			//for ( k = 0; find( grorder.begin(), grorder.end(), k ) != grorder.end(); ++k );
			for ( CondVec::iterator j = s.begin(); j != s.end(); ++j ) {
				if ( true ) std::cout << "   Test condition " << (*j) << "\n";
				std::map< int, int > m;
				CondPairSet u;
				Condition c = *j;
				for ( unsigned l = 0; l < c.params.size(); ++l )
					m[c.params[l]] = l;
				std::set< int > r( c.params.begin(), c.params.end() );

				for ( CondVec::iterator o = s.begin(); o != s.end(); ++o )
					if (o != j) {
						std::map< int, int > h;
						c = *o;
						int x = d.pmap[c.name];
						for ( unsigned l = 0; l < c.params.size(); ++l )
							if ( r.find( c.params[l] ) != r.end() )
								h[c.params[l]] = l;
						u.insert( std::make_pair( h, std::make_pair(cndNum, *o) ));
						//std::cout << "   Other condition " << c << "," << m << "\n";
					}

				bool b = true;
				//c is the other condition
				SetPairVec h;
				//SetPairVec h = hardGoal(u,c,d, true);
				///std::cout << "   hard " << h << "\n";
				if(posmap.find(cndNum) == posmap.end()){
					std::cout<<"DEBUG ERRROR"<<std::endl;
					break;
				}

				for ( CondGraphMap::iterator l = graphs[posmap[cndNum]].begin(); l != graphs[posmap[cndNum]].end(); ++l )
					for ( GraphMap::iterator n = l->second.begin(); n != l->second.end(); ++n ) {
						mgraph g = generateGraph( n->first, h, m, d, false );
						//std::cout << *j << ": " << g <<" - "<< n->second<<"\n";
						b &= g.subsumes( n->second );
					}
				if ( b ) {
					//std::cout<<"subsumes"<<std::endl;
					grorder.push_back( *j );
					//std::cout<<"Grorder:"<<grorder<<std::endl;
					s.erase( j );
					break;
				}
			}
			++cndNum;
		}
		return grorder;
	}

	void orderGoalsFull(std::map<Condition, CondVec>& typeMap,
			std::map<Condition, std::map<std::vector<int>, std::vector<int> > >& conflicts, Domain &d, Instance ins) {

		CondVec totalgrorder;
		for (std::map<Condition, CondVec>::iterator type_it = typeMap.begin(); type_it != typeMap.end(); ++type_it) {
			CondVec grorder;
			CondVec goals = type_it->second;
			//print grounded goal
//					for (unsigned i = 0; i < goals.size(); ++i) {
//						std::cout<<goals[i]<<" ";
//						Condition c = d.preds[d.pmap[goals[i].name]];
//						std::cout << goals[i].name << "( ";
//						for (unsigned j = 0; j < c.params.size(); ++j) {
//							std::cout << ins.objects[c.params[j]][goals[i].params[j]] << " ";
//						}
//						std::cout << ")" << " ";
//					}
//					std::cout << std::endl;
			grorder.push_back(goals[0]);

			for (int i = 1; i < goals.size(); ++i) {
				bool independent = true;
				int x = d.pmap[goals[i].name];
				Condition typeCond = type_it->first;

				for (unsigned ord_cnt = 0; ord_cnt < grorder.size(); ++ord_cnt) {
					unsigned invar_cnt = 0;

					bool nextrun = false;
					CondPairMap::iterator l = predInvs[x].find(typeCond);
					if (l != predInvs[x].end())
						for (PairSet::iterator k = l->second.begin(); k != l->second.end(); ++k) {
//							std::cout << "Invariant " << invs[k->first] << std::endl;
//							std::cout << "Test for:" << goals[i] << " for fixed:" << grorder[ord_cnt] << std::endl;

							++invar_cnt;
							//For each inward action
							std::set<int>::iterator it = invs[k->first].g.parents[k->second].begin();
							for (; it != invs[k->first].g.parents[k->second].end(); ++it) {
								TripVec w = invs[k->first].g.edges[*it][k->second];

								for (unsigned cnt = 0; cnt < w.size(); ++cnt) {
									//printTrip(w[cnt], d, std::cout);
									CondVec gprec = d.actions[w[cnt].a].pre;
									CondVec gprec_types = d.actions[w[cnt].a].pre;
									CondVec gprec_params = d.actions[w[cnt].a].pre;
									Condition c = d.preds[d.pmap[d.actions[w[cnt].a].getCondition(w[cnt].c).name]];

									//Ground preconditions for goal[i]
									for (unsigned p_cnt = 0; p_cnt < gprec.size(); ++p_cnt) {
										std::vector<int> goal_pred_params =
												d.actions[w[cnt].a].getCondition(w[cnt].c).params;
										std::map<int, int> goal_pred_map, goal_type_map, goal_param_map;
										for (unsigned pp_cnt = 0; pp_cnt < goal_pred_params.size(); ++pp_cnt) {
											goal_pred_map[goal_pred_params[pp_cnt]] = goals[i].params[pp_cnt];
											goal_type_map[goal_pred_params[pp_cnt]] = c.params[pp_cnt];
											goal_param_map[goal_pred_params[pp_cnt]] = pp_cnt;
										}

										for (unsigned pp_cnt = 0; pp_cnt < gprec[p_cnt].params.size(); ++pp_cnt) {
											if (goal_pred_map.find(gprec[p_cnt].params[pp_cnt])
													== goal_pred_map.end()) {
												gprec[p_cnt].params[pp_cnt] = -1;
												continue;
											}
											gprec_params[p_cnt].params[pp_cnt] =
													goal_param_map[gprec[p_cnt].params[pp_cnt]];
											gprec_types[p_cnt].params[pp_cnt] =
													goal_type_map[gprec[p_cnt].params[pp_cnt]];
											gprec[p_cnt].params[pp_cnt] = goal_pred_map[gprec[p_cnt].params[pp_cnt]];
										}
									}
									gprec.push_back(grorder[ord_cnt]);
									gprec_types.push_back(d.preds[d.pmap[grorder[ord_cnt].name]]);
//									std::cout<<"gprec:"<<gprec<<std::endl;
//									std::cout<<"grorder"<<grorder<<std::endl;
//									std::cout<<"gprec_types:"<<gprec_types<<std::endl;
//									std::cout<<"gprec_params:"<<gprec_params<<std::endl;
									bool b = true;
									std::vector<std::vector<std::string> > u;

									// mutex test
									std::vector<std::vector<int> > conflict_poss;
									std::vector<int> conf_pos_save;
									int conf_pos_save1;
									std::map<std::vector<int>, std::vector<int> > confmap;

									for (unsigned p_cnt = 0; p_cnt < gprec.size(); ++p_cnt) {
										SetMap::iterator j = invs[k->first].preds.find(d.pmap[gprec[p_cnt].name]);
										if (j != invs[k->first].preds.end()) {
//											std::cout << "Test:" << d.preds[j->first].name << " bound:" << j->second <<std::endl;
											Condition c = gprec_types[p_cnt];
//											std::cout<<d.preds<<std::endl;
											std::vector<std::string> v;
											std::vector<int> conflict_pos;
											for (std::set<int>::iterator z = j->second.begin(); z != j->second.end();
													++z) {
//												std::cout << "push back params of " << gprec[p_cnt] << std::endl;
												if (gprec[p_cnt].params[*z] > -1) {
													v.push_back(ins.objects[c.params[*z]][gprec[p_cnt].params[*z]]);
													if (p_cnt < gprec.size() - 1)
														conflict_pos.push_back(gprec_params[p_cnt].params[*z]);
													else
														conflict_pos.push_back(*z);
												}
											}
//											std::cout << "v:" << v << std::endl;
//											std::cout << "u:" << u << std::endl;
											std::vector<std::vector<std::string> >::iterator lt = std::find(u.begin(),
													u.end(), v);

											if (lt != u.end()) {
												conf_pos_save = conflict_pos;
												int pos = lt - u.begin();
												conf_pos_save1 = pos;
//												std::cout << "conflict" << u << std::endl;
											}
											if (independent &= b &= lt == u.end())
												if (v.size() > 0) {
													u.push_back(v);
													conflict_poss.push_back(conflict_pos);
												}

//											std::cout<<"conflict poss:"<<conflict_poss<<std::endl;
										}
									}
//									std::cout << "u:" << u << std::endl;
									if (b) {
//										std::cout << "true" << std::endl;
									} else {
//										std::cout << "false" << std::endl;
										confmap[conf_pos_save] = conflict_poss[conf_pos_save1];
										conflicts[typeCond] = confmap;
										// std::cout<<";GORDER DOMAIN"<<std::endl;
										grorder.insert(grorder.begin() + ord_cnt + 1, goals[i]);
										nextrun = true;
										break;
									}
									//end test
									gprec.pop_back();
								}
								if (nextrun)
									break;
								//std::cout << "Finished invariant" << invar_cnt << std::endl << std::endl;

							}
						}
					if (nextrun)
						break;

					//std::cout << "Reverse order:" << grorder << std::endl;
				}
				if (independent) {
					//std::cout<<"Independent"<<std::endl;
					grorder.insert(grorder.begin(), goals[i]);
				}
				//std::cout << std::endl;
			}
			std::reverse(grorder.begin(), grorder.end());
			type_it->second = grorder;
			//totalgrorder.insert(totalgrorder.end(),grorder.begin(), grorder.end());
		}
	}
};

// pass a macro to a stream
std::ostream &operator<<( std::ostream &stream, const macro &m ) {
	stream << "Macro" << m.t << "\n";
	stream << "  " << m.rel << "\n";
	stream << "  " << m.fixed << "\n";
	stream << "  " << m.variable << "\n";
	for ( unsigned i = 0; i < m.graphs.size(); ++i ) {
		for ( CondGraphMap::const_iterator j = m.graphs[i].begin(); j != m.graphs[i].end(); ++j ) {
			stream << "  " << j->first;
			for ( GraphMap::const_iterator k = j->second.begin(); k != j->second.end(); ++k )
				stream << ":" << k->first << ";" << k->second;
			stream << "\n";
		}
	}
	stream << "  " << m.rorder << "\n";
	return stream;
}


// global variables
typedef std::map< trip, std::vector< macro > > TripMacroMap;
TripMacroMap macros;            // invariant edges to macros

