
#include "domain.h"

#define INV_DEBUG false

template < typename T, typename U >
typename std::map< T, U >::iterator
insertMap( std::map< T, U > &m, const T &t, U u = U() ) {
	typename std::map< T, U >::iterator i = m.find( t );
	if ( i == m.end() ) i = m.insert( m.begin(), std::make_pair( t, u ) );
	return i;
}

// triple representing an action and a pair of conditions
struct trip {
	int a, b, c;
	trip() {}
	trip( int x, int y, int z ) : a( x ), b( y ), c( z ) {}
	bool operator<( const trip &t ) const {
		return a < t.a || a == t.a && ( b < t.b || b == t.b && c < t.c );
	}
};

// pass an triple to a stream
std::ostream &operator<<( std::ostream &stream, const trip &t ) {
	return stream << "(" << t.a << "," << t.b << "," << t.c << ")";
}

// print the action associated with a triplet
void printTrip( const trip &t, Domain &d, std::ostream &stream ) {
	stream << " " << d.actions[t.a].name
	       << "," << d.actions[t.a].getCondition( t.b )
	       << "," << d.actions[t.a].getCondition( t.c ) << "\n";
}

typedef std::map< int, std::set< int > > SetMap;
typedef std::map< int, std::vector< trip > > TripMap;
typedef std::map< int, TripMap > TripDMap;
typedef std::map< Condition, unsigned > CondMap;

// representation of a graph
// each node is an element of an invariant condition vector
struct graph {
	SetMap parents;
	TripDMap edges;
	void insertEdge( int m, int n, const trip &t ) {
		// add the (action,cond,cond) triplet t to the edge (m,n)
		TripDMap::iterator i = insertMap( edges, m );
		insertMap( i->second, n )->second.push_back( t );
		insertMap( parents, n )->second.insert( m );
	}
};

// representation of an invariant
struct inv {
	graph g;
	std::multiset< int > types;
	SetMap preds;               // abstract predicates with bound parameters (pred index, set of bound params)
	CondVec conds;              // concrete conditions
	CondMap condMap;

	inv() {}
	inv( const SetMap &p ) : preds( p ) {}
	inv( std::multiset< int > &t, const SetMap &p ) : types( t ), preds( p ) {}

	bool operator<( const inv &i ) const {
		return types < i.types || types == i.types && preds < i.preds;
	}

	int insertCond( Condition &c ) {
		CondMap::iterator i = insertMap( condMap, c, (unsigned)conds.size() );
		if ( i->second == conds.size() ) conds.push_back(c);
		return i->second;
	}
};

// pass an invariant to a stream
std::ostream &operator<<( std::ostream &stream, const inv &i ) {
	return stream << i.types << "," << i.preds << "," << i.conds;
}

typedef std::set< inv > InvSet;
typedef std::vector< inv > InvVec;
typedef std::set< trip > TripSet;
typedef std::vector< trip > TripVec;
typedef std::map< inv, unsigned > InvMap;
typedef std::vector< TripSet > TripSetVec;
typedef std::map< Condition, PairSet > CondPairMap;
typedef std::map< int, CondPairMap > PredMap;
typedef std::pair< int, std::set< int > > SetPair;

// global variables
InvVec invs;            // invariants
InvMap invMap;          // invariant map
TripSetVec actionInvs;  // actions to invariants and its edge
PredMap predInvs;       // preds to conditions and (inv,cond) pair


// insert an invariant for a predicate-condition pair
//   a: predicate index
//   b: invariant index
//   n: condition index
//   c: condition with parameter types (or constants)
void insert( int a, int b, int n, const Condition &c ) {
	PredMap::iterator i = insertMap( predInvs, a );
	insertMap( i->second, c )->second.insert( std::make_pair( b, n ) );
}

// insert a new invariant
int insertInv( std::multiset< int > &t, const SetMap &p ) {
	inv i( t, p );
	InvMap::iterator j = insertMap( invMap, i, (unsigned)invs.size() );
	if ( j->second == invs.size() ) invs.push_back( i );
	return j->second;
}

// convert a set into another
//   s: original set
//   v: conversion parameters
std::set< int > convert( const std::set< int > &s, const std::vector< int > &v) {
	std::set< int > t;
	for ( std::set< int >::iterator i = s.begin(); i != s.end(); ++i )
		t.insert( *i < 0 ? -1-*i : v[*i] );
	return t;
}
// convert a vector into another
//   u: original vector
//   v: conversion parameters
std::vector< int > convert( const std::vector< int > &u,
                            const std::vector< int > &v ) {
	std::vector< int > w;
	for ( unsigned i = 0; i < u.size(); ++i )
		w.push_back( u[i] < 0 ? -1-u[i] : v[u[i]] );
	return w;
}

// insert an edge into an invariant graph
//   p, q: the two predicates between which edge is inserted
//   a: action index
//   b, c: effects on p and q of action
//   m: complete set of predicates of the invariant
void insertEdge( SetPair p, SetPair q,
                 int a, int b, int c, Domain &d, const SetMap &m) {
	trip u( a, b, c );
	// if q is deleted and p added, swap
	if ( c < 0 ) { std::swap( u.b, u.c ); std::swap( p, q ); }

	// edge is from p to q
	// check that action parameters are equal for the bound parameters of p and q
	std::set< int > s, t;
	s = convert( p.second, d.actions[a].getCondition( u.b ).params );
	t = convert( q.second, d.actions[a].getCondition( u.c ).params );

	if ( s == t ) {
		// h contains the type of each action parameter associated with the edge
		// if the bound parameter corresponds to a constant, the constant is saved
		std::multiset< int > h;
		for ( std::set< int >::iterator i = s.begin(); i != s.end(); ++i )
			h.insert( *i < 0 ? *i : d.actions[a].params[*i] );

		if ( INV_DEBUG ) std::cout << "\ninserting...\n";

		// invariant is generated and inserted, index returned
		int e = insertInv( h, m );
		// condition parameters replaced with the corresponding type
		Condition x = d.actions[a].typeCondition( u.b );

		// insert the condition x into the invariant, index returned
		int n = invs[e].insertCond(x), o = n;

		// insert a reference from the predicate index and condition
		//   to its invariant and condition indices
		insert( p.first, e, n, x );

		if ( p != q ) {
			// if predicates are different, repeat for added predicate
			Condition y = d.actions[a].typeCondition( u.c );
			o = invs[e].insertCond( y );
			insert( q.first, e, o, y );
		}

		// edge is from n to o
		// triplet u indicates action and its corresponding conditions
		invs[e].g.insertEdge( n, o, u );

		// insert reference from action to invariant index and corresponding edge
		actionInvs[a].insert( trip( e, n, o ) );

		// print information about invariant and edge
		if ( INV_DEBUG ) {
			TripVec v = invs[e].g.edges[n][o];
			std::cout << invs[e] << ", (" << n << "," << o << "):\n";
			for ( unsigned i = 0; i < v.size(); ++i )
				printTrip( v[i], d, std::cout );
		}
	}
}

//get bound indexes
std::vector<int> getBoundIndexes(Condition c, int inv_num, int x){
	std::vector<int> ret;
	SetMap::iterator j = invs[inv_num].preds.find(x);
	if(j!= invs[inv_num].preds.end()){
		for (std::set<int>::iterator z = j->second.begin(); z != j->second.end();++z) {
			ret.push_back(*z);
		}
	}
	return ret;
}

//get bound params
std::vector<int> getBoundParams(Condition c, int inv_num, int x){
	std::vector<int> ret;
	SetMap::iterator j = invs[inv_num].preds.find(x);
	if(j!= invs[inv_num].preds.end()){
		for (std::set<int>::iterator z = j->second.begin(); z != j->second.end();++z) {
			ret.push_back(c.params[*z]);
		}
	}
	return ret;
}

//casts bound params of c to type t
void castCondBound(Condition& c, int inv_num, int t, Domain d){
	SetMap::iterator j = invs[inv_num].preds.find(d.pmap[c.name]);
		if(j!= invs[inv_num].preds.end()){
			for (std::set<int>::iterator z = j->second.begin(); z != j->second.end();++z) {
				c.params[*z] = t;
			}
		}
}

//copy the edges while downcasting the nodes
// m:supertype node, minv- supertype node's invariant index
// o:subtype node, oinv- subtype node's invariant index
void copyEdges(Condition m, Condition o, int minv, int oinv, Domain d) {
	//first get nodes connected to m
	std::vector<int> obound = getBoundParams(o, oinv, d.pmap[o.name]);
	CondVec::iterator cit = std::find(invs[minv].conds.begin(), invs[minv].conds.end(), m);
	int mcindex = cit - invs[minv].conds.begin();
	cit = std::find(invs[oinv].conds.begin(), invs[oinv].conds.end(), o);
	int ocindex = cit - invs[oinv].conds.begin();

	if ( INV_DEBUG ) std::cout << "    Additional nodes\n";
	std::set<int>::iterator it = invs[minv].g.parents[mcindex].begin();
	for (; it != invs[minv].g.parents[mcindex].end(); ++it) {
		TripVec w = invs[minv].g.edges[*it][mcindex];
		for (unsigned cnt = 0; cnt < w.size(); ++cnt) {
			Condition c = d.actions[w[cnt].a].typeCondition(w[cnt].b);
			//TODO only the first bound param...
			castCondBound(c, minv, obound[0], d);
			//insert the node and connection to oinv
			int nindex = invs[oinv].insertCond(c);
			invs[oinv].g.insertEdge(nindex, ocindex, w[cnt]);
		}

		w = invs[minv].g.edges[mcindex][*it];
		for (unsigned cnt = 0; cnt < w.size(); ++cnt) {
			Condition c = d.actions[w[cnt].a].typeCondition(w[cnt].c);
			//TODO only the first bound param...
			castCondBound(c, minv, obound[0], d);
			//insert the node and connection to oinv
			int nindex = invs[oinv].insertCond(c);
			invs[oinv].g.insertEdge(ocindex, nindex, w[cnt]);
		}
	}
}

