
#include "parse.h"

#define DOMAIN_DEBUG false

typedef std::vector< Action > ActionVec;
typedef std::vector< Condition > CondVec;
typedef std::vector< TokenMap > TokenVec;
typedef std::vector< std::string > StringVec;
typedef std::vector< StringVec > StringDVec;
typedef std::vector< std::set< int > > SetVec;
typedef std::set< std::pair< int, int > > PairSet;
typedef std::vector< std::pair< int, int > > PairVec;
typedef std::vector< PairSet > PairSetVec;

// insert element into vector and update map
template <typename T>
TokenMap::iterator insert(T t, TokenMap &m, std::vector<T> &v) {
	v.push_back(t);
	return m.insert(m.begin(), std::make_pair(t.c_str(), v.size() - 1));
}

// parse the name of a PDDL file
std::string parseName(Filereader &f, std::string u) {
	std::string s[5] = {"(", "DEFINE", "(", u, ")"}, t = "";
	for (unsigned i = 0; i < 5; ++i) {
		f.assert(s[i]);
		if (i == 3) {
			t = f.getToken();
			f.next();
		}
	}
	return t;
}

// add constants to type lists
void addConstants( int i, StringVec &a, CondVec &b, StringDVec &u, TokenVec &v ) {
	for ( unsigned j = 0; j < a.size(); ++j )
		insert( a[j], v[i], u[i] );
	for ( unsigned j = 0; j < b[i].params.size(); ++j )
		addConstants( b[i].params[j], a, b, u, v );
}

// parse a series of objects
void parseObjectList( Filereader &f, TokenMap &m, CondVec &b,
                      StringDVec &u, TokenVec &v ) {
	StringVec a;
	for ( f.next(); f.getChar() != ')'; f.next() ) {
		std::string s = f.getToken();
		if ( s == "-" ) {
			f.next();
			addConstants( f.tokenIndex( m ), a, b, u, v );
			a.clear();
		}
		else a.push_back( s );
	}
	for ( unsigned i = 0; i < a.size(); ++i )
		insert( a[i], v[0], u[0] );
	++f.c;
}

class Domain {
public:
	std::string name;          // name of domain
	bool typed, costs;         // whether domain is typed and has costs
	ActionVec actions;         // actions
	CondVec types, preds;      // types and predicates
	StringDVec constants;      // constants
	TokenMap amap, tmap, pmap; // map for actions, types, predicates
	TokenVec cmap;             // maps for constants

	PairSetVec predActions;     // actions with effect on predicate

	Domain( const std::string &s )
		: typed( false ), costs( false ), types( 1, Condition( "OBJECT" ) ),
		  constants( 1 ), cmap( 1 ) {
		parse(s);
	}

	void parse( const std::string &s ) {
		Filereader f( s );
		name = parseName( f, "DOMAIN" );

		if ( DOMAIN_DEBUG ) std::cout << name << "\n";

		while ( f.getChar() != ')' ) {
			f.assert( "(" );
			f.assert( ":" );
			std::string t = f.getToken();

			if ( DOMAIN_DEBUG ) std::cout << t << "\n";

			if ( t == "REQUIREMENTS" ) parseReq( f );
			else if ( t == "TYPES" ) parseTypes( f );
			else if ( t == "CONSTANTS" ) parseConstants( f );
			else if ( t == "PREDICATES" ) parsePredicates( f, false );
			else if ( t == "FUNCTIONS" ) parsePredicates( f, true );
			else if ( t == "ACTION" ) parseAction( f );
			else if ( t == "AXIOM" ) parseAxiom( f );
			else {
				f.c -= t.size();
				f.printLine();
				std::cout << "Unknown type " << t << "\n";
				exit( 1 );
			}
			f.next();
		}
	}

	void parseReq( Filereader &f ) {
		for ( f.next(); f.getChar() != ')'; f.next() ) {
		f.assert( ":" );
		std::string s = f.getToken();

		if ( DOMAIN_DEBUG ) std::cout << "  " << s << "\n";

		// ignore other requirements for now
		if ( s == "TYPING" ) typed = true;
		else if ( s == "ACTION-COSTS" ) costs = true;
		else if ( s == "EQUALITY" )
			if ( DOMAIN_DEBUG )
				std::cout << "Currently supports :EQUALITY only for functions\n";
		}
		++f.c;
	}

	void parseTypes( Filereader &f ) {
		if (!typed) {
			std::cout << "Requirement :TYPING needed to define types\n";
			exit( 1 );
		}

		types.clear();
		if ( costs ) insert( Condition( "NUMBER" ), tmap, types );
		std::vector< unsigned > v;
		for ( f.next(); f.getChar() != ')'; f.next() ) {
			std::string s = f.getToken();

			if ( s == "-" ) {
				f.next();
				s = f.getToken();

				TokenMap::iterator i = tmap.find( s );
				if ( i == tmap.end() )
					i = insert( Condition( s ), tmap, types );

				for ( unsigned j = 0; j < v.size(); ++j )
					types[v[j]].params.push_back( i->second );
	
				v.clear();
			}
			else {
				TokenMap::iterator i = tmap.find( s );
				if ( i == tmap.end() )
					i = insert( Condition( s ), tmap, types );
				v.push_back( i->second );
			}
		}
		constants.resize( types.size() );
		cmap.resize( types.size() );
		++f.c;

		for ( unsigned i = 0; DOMAIN_DEBUG && i < types.size(); ++i )
			std::cout << "  " << types[i] << "\n";
	}

	void parseConstants( Filereader &f ) {
		if ( typed && !types.size() ) {
			std::cout << "Types needed before defining constants\n";
			exit( 1 );
		}

		parseObjectList( f, tmap, types, constants, cmap );

		for ( unsigned i = 0; DOMAIN_DEBUG && i < constants.size(); ++i ) {
			std::cout << " ";
			if ( typed ) std::cout << " " << types[i] << ":";
			for ( unsigned j = 0; j < constants[i].size(); ++j )
				std::cout << " " << constants[i][j];
			std::cout << "\n";
		}
	}

	void parsePredicates( Filereader &f, bool areFunctions ) {
		if ( typed && !types.size() ) {
			std::cout << "Types needed before defining ";
			std::cout << (areFunctions ? "functions" : "predicates") << "\n";
			exit(1);
		}

		for ( f.next(); f.getChar() != ')'; f.next() ) {
			int k = 0;
			f.assert( "(" );
			Condition c( f.getToken() );
			for ( f.next(); f.getChar() != ')'; f.next() ) {
				std::string s = f.getToken();
				if ( s == "-" ) {
					f.next();
					if ( f.getChar() == '(' ) {
						f.assert( "(EITHER" );
						int i = f.tokenIndex( tmap );
						f.next();
						int j = f.tokenIndex( tmap );
						f.next();
						f.assert( ")" );

						std::ostringstream os;
						os << "EITHER_" << types[i].name << "_" << types[j].name;
						Condition d( os.str() );

						types[i].params.push_back( types.size() );
						types[j].params.push_back( types.size() );

						constants.push_back( constants[i] );
						cmap.push_back( cmap[i] );
						for ( unsigned x = 0; x < constants[j].size(); ++x )
							insert( constants[j][x], cmap[types.size()], constants[types.size()] );
						c.params.insert( c.params.end(), k, types.size() );
						insert( d, tmap, types );
					}
					else c.params.insert( c.params.end(), k, f.tokenIndex( tmap ) );
					k = 0;
				}
				else ++k;
			}
			++f.c;
			f.next();
			if ( k > 0 ) c.params.insert( c.params.end(), k, 0 );
			if ( areFunctions ) {
				if ( typed ) {
					f.assert( "-" );
					c.misc = f.tokenIndex(tmap);
					f.next();
				}
				else c.misc = 0;
			}
			if ( DOMAIN_DEBUG ) std::cout << "  " << c << "\n";
			insert( c, pmap, preds );
			predActions.push_back( PairSet() );
		}
		++f.c;
	}

	bool assertTypes( int i, int j ) {
		bool b = i == j;
		for ( unsigned k = 0; !b && k < types[i].params.size(); ++k )
			b = assertTypes( types[i].params[k], j );
		return b;
	}

	void assertTypes( Condition &c, Action &a, int i, int j ) {
		if ( !assertTypes( i, j ) ) {
			std::cout << "Incompatible type " << types[i].name << "for ";
			std::cout << "condition " << c << " of action " << a.name << "\n";
			exit( 1 );
		}
	}

	void parseAtom( Filereader &f, Condition &c, TokenMap &m, Action &a ) {
		unsigned k = 0;
		//std::cout << "Parse condition " << c << " of action " << a.name << "\n";
		for ( f.next(); k < c.params.size() && f.getChar() != ')'; f.next() ) {
			int i = f.tokenIndex( m, cmap[c.params[k]] );
			if ( i >= 0 ) assertTypes( c, a, a.params[i], c.params[k] );
			c.params[k++] = i;
		}
		if ( k < c.params.size() ) {
			std::cout << "Wrong number of parameters for condition " << c;
			std::cout << " of action " << a.name << "\n";
			exit( 1 );
		}
		++f.c;
	}

	void parseAtom( Filereader &f, TokenMap &m, Action &a, bool b ) {
		std::string s = f.getToken();
		if ( s == "=" || s == "ASSIGN" || s == "INCREASE" ) {
			f.next();
			f.assert( "(" );
			int i = f.tokenIndex( pmap );
			Condition c( preds[i] ), d( "" );
			parseAtom( f, c, m, a );
			f.next();
			if ( s == "INCREASE" ) {
				if ( f.getChar() == '(' ) {
					++f.c;
					f.next();
					int j = f.tokenIndex( pmap );
					d = Condition( preds[j] );
					parseAtom( f, d, m, a );
					c.misc = -j - 1;
				}
				else {
					std::istringstream is( f.getToken() );
					is >> c.misc;
				}
			}
			else {
				int j = f.tokenIndex( m, cmap[c.misc] );
				if ( j >= 0 ) assertTypes( c, a, a.params[j], c.misc );
				c.misc = j;
			}
			if ( b ) {
				predActions[i].insert( std::make_pair( actions.size(), a.add.size() ) );
				a.add.push_back( c );
			}
			else a.pre.push_back( c );

			if ( s == "INCREASE" && d.name != "" ) a.add.push_back( d );
			f.next();
			f.assert( ")" );
		}
		else if ( s == "NOT" ) {
			f.next();
			f.assert( "(" );
			int i = f.tokenIndex( pmap );
			Condition c( preds[i] );
			parseAtom( f, c, m, a );
			c.misc = a.params.size();
			if ( b ) {
				a.del.push_back( c );
				predActions[i].insert( std::make_pair( actions.size(), -a.del.size() ) );
			}
			else {
				c.neg = true;
				a.pre.push_back( c );
			}
			f.next();
			f.assert( ")" );
		}
		else {
			f.c -= s.size();
			int i = f.tokenIndex( pmap );
			Condition c( preds[i] );
			parseAtom( f, c, m, a );
			c.misc = a.params.size();
			if ( b ) {
				predActions[i].insert( std::make_pair( actions.size(), a.add.size() ) );
				a.add.push_back( c );
			}
			else a.pre.push_back( c );
		}
	}

	void parseCondition( Filereader &f, TokenMap &m, Action &a, bool b ) {
		f.next();
		f.assert( "(" );
		std::string s = f.getToken();
		if ( s == "AND" ) {
			for ( f.next(); f.getChar() != ')'; f.next() ) {
				f.assert( "(" );
				parseAtom( f, m, a, b );
			}
			++f.c;
		}
		else {
			f.c -= s.size();
			parseAtom( f, m, a, b );
		}
	}

	void parseAction( Filereader &f ) {
		if ( !preds.size() ) {
			std::cout << "Predicates needed before defining actions\n";
			exit(1);
		}

		f.next();
		Action a( f.getToken() );
		f.next();
		f.assert( ":PARAMETERS" );
		f.assert( "(" );
    
		int k = 0;
		StringVec v;
		TokenMap m;
		for ( f.next(); f.getChar() != ')'; f.next() ) {
			std::string s = f.getToken();
			if ( s == "-" ) {
				f.next();
				int i = f.tokenIndex( tmap );
				a.params.insert( a.params.end(), k, i );
				k = 0;
			}
			else {
				++k;
				insert( s, m, v );
			}
		}
		a.params.insert( a.params.end(), k, 0 );

		//std::cout << "  " << a.name << a.params << "\n";

		++f.c;
		f.next();
		f.assert( ":" );
		std::string s = f.getToken();
		if ( s == "PRECONDITION" ) {
			parseCondition( f, m, a, false );
			f.next();
			f.assert( ":" );
			s = f.getToken();
		}
		if ( s != "EFFECT" ) {
			f.c -= s.size();
			f.printLine();
			std::cout << "Unknown action command " << s << "\n";
			exit(1);
		}
		parseCondition( f, m, a, true );
		if ( DOMAIN_DEBUG ) std::cout << a << "\n\n";
		insert( a, amap, actions );
		f.next();
		f.assert( ")" );
	}

	void parseAxiom( Filereader &f ) {
		std::cout << "Axioms currently not supported\n";
		exit(1);
	}

	void recTypes( int type, std::set< int > &s ) {
		s.insert(type);
		for ( unsigned i = 0; i < types.size(); ++i )
			if ( s.find(i) == s.end() && std::find( types[i].params.begin(), types[i].params.end(), type ) != types[i].params.end() )
				recTypes( i, s );
	}

	std::set< int > getSubtypes( int type ) {
		std::set<int> s;
		recTypes(type, s);
		return s;
	}

	std::set< int > getSupertypes( int type ) {
		std::vector<int> v( 1, type );
		for ( unsigned i = 0; i < v.size(); ++i )
			if ( v[i] >= 0 ) v.insert( v.end(), types[v[i]].params.begin(), types[v[i]].params.end() );
		return std::set< int >( v.begin(), v.end() );
	}

	void PDDLPrintTypes(std::ostream &out, int init_type){
			auto subtypes = getSubtypes(init_type);
			std::set<int> fitered_subtypes;
			for(auto subtype : subtypes){
				if(subtype == init_type) continue;
				bool is_subsubtype = false;
				for(auto other_sub_type : subtypes){
					if(other_sub_type == subtype || other_sub_type == init_type) continue;
					if(isSupertype(subtype, other_sub_type)) {is_subsubtype=true; break;}
				}
				if(!is_subsubtype) fitered_subtypes.insert(subtype);
			}
			if(fitered_subtypes.size()<1) return;
			out<<"\t";
			for(auto subtype : fitered_subtypes){
				if(subtype == init_type) continue;
				out<<types[subtype].name<<" ";
			}
			out<<"- "<<types[init_type].name<<std::endl;
			for(auto subtype : fitered_subtypes){
				this->PDDLPrintTypes(out, subtype);
			}
		
	}

	void PDDLPrintPredicates(std::ostream &out){
		for(auto pred : preds){
			out<<"\t";
			out << "( " << pred.name;
			for ( unsigned i = 0; i < pred.params.size(); ++i ) {
			out << " ?" << types[pred.params[i]].name << i;
			if ( typed ) out << " - " << types[pred.params[i]].name;
			}
			out << " )"<<std::endl;
		}
	}

	//checks if type is subtype of supertype
	bool isSupertype(int type, int supertype){
		if(type == supertype) return false;
		std::set<int> supertypes = getSupertypes(type);
		return (supertypes.find(supertype)!=supertypes.end());
	}

	std::string parametrizeCondition( Condition &c, const std::string &s, bool b, int invariant_number=-1) {
		std::ostringstream os;
		os << " ( " << ( b ? "not ( " : "" ) << s << c.name;
		if(invariant_number>-1)
			os << invariant_number;
		for ( unsigned i = 0; i < c.params.size(); ++i )
			os << " ?" << types[c.params[i]].name << i;
		os << ( b ? " )" : "" ) << " )";
		return os.str();
	}

	std::string parametrizeHDDLCondition( Condition &c, const std::string &s, int invariant_number=-1) {
		std::ostringstream os;
		os << s << c.name;
		if(invariant_number>-1)
			os << invariant_number;
	 	os<<std::endl;
		os<<"\t:parameters (";
		for ( unsigned i = 0; i < c.params.size(); ++i )
			os << " ?" << types[c.params[i]].name << i << " - " << types[c.params[i]].name;
		os << " )";
		return os.str();
	}

	std::string parametrizeCondition( Action &a, Condition &c, const std::string &s, bool b ) {
		std::ostringstream os;
		os << " ( " << ( b ? "not ( " : "" ) << s << c.name;
		for ( unsigned i = 0; i < c.params.size(); ++i )
			os << " ?" << types[a.params[c.params[i]]].name << c.params[i];
		os << ( b ? " )" : "" ) << " )";
		return os.str();
	}

	void printConditionVector( Action &a, CondVec &v, std::ostream &stream,
	                           const std::string &s, bool b ) {
		for ( unsigned i = 0; i < v.size(); ++i )
			stream << parametrizeCondition( a, v[i], s, b );
	}

	void printSHOPOperators( std::ostream &stream ) {
		for ( unsigned i = 0; i < actions.size(); ++i ) {
			stream << "    ( :OPERATOR";
			stream << parametrizeCondition( actions[i], std::string( "!" ), false ) << "\n";

			stream << "                (";
			for ( unsigned j = 0; j < actions[i].params.size(); ++j ) {
				stream << " ( " << types[actions[i].params[j]].name << " ?";
				stream << types[actions[i].params[j]].name << j << " )";
			}
			printConditionVector( actions[i], actions[i].pre, stream, "", false );
			printConditionVector( actions[i], actions[i].del, stream, "LOCKED-", true );
			stream << " )\n                (";
			printConditionVector( actions[i], actions[i].del, stream, "", false );
			stream << " )\n                (";
			printConditionVector( actions[i], actions[i].add, stream, "", false );
			stream << " )\n    )\n";
		}
	}

	void printHDDLActions( std::ostream &os ) {
		for ( unsigned i = 0; i < actions.size(); ++i ) {
			os<<"( :action "<<actions[i].name<<std::endl;
			os<<"\t:parameters (";
				Condition& c = actions[i];
				for ( unsigned i = 0; i < c.params.size(); ++i )
					os << " ?" << types[c.params[i]].name << i <<" - "<<types[c.params[i]].name;
				os<<")"<<std::endl;

			os<<"\t:precondition (and"<<std::endl;
				os<<"\t\t";
				printConditionVector( actions[i], actions[i].pre, os, "", false );
				printConditionVector( actions[i], actions[i].del, os, "LOCKED-", true );
				os<<")"<<std::endl;
				
			os<<"\t:effect (and"<<std::endl;
				os<<"\t\t";
				printConditionVector( actions[i], actions[i].del, os, "", true );
				printConditionVector( actions[i], actions[i].add, os, "", false );
				os<<")"<<std::endl;
			os<<")"<<std::endl;
		
		}
	}

	void printMethod( Condition &c, std::ostream &stream, const std::string &s,  const std::string &t ) {
				std::string p("-");
				stream << "    ( :METHOD" << parametrizeCondition( c, s + p, false ) << "\n";
				stream << "               ("+parametrizeCondition( c, "FLAGGED" + p, false )+" )\n";
				stream << "               ("+parametrizeCondition( c, "!!UNFLAG" + p, false )+" )\n";
				stream << "               ( ( NOT"+parametrizeCondition( c, "FLAGGED" + p, false )+" ) )\n";
				stream << "               ("+parametrizeCondition( c, "!!UNLOCK" + p, false )+" )\n";
				stream << "    )\n";
	}

	void printHDDLMethod( Condition &c, std::ostream &os, const std::string &s,  const std::string &t ) {
				std::string p("-");
				os << "( :task " << parametrizeHDDLCondition( c, s + p) <<std::endl;
				os << ")"<<std::endl;
				os << "( :method " << parametrizeHDDLCondition( c, s + p) <<std::endl;
				os << "\t:task"<<parametrizeCondition( c, s + p, false)<<std::endl;
				os << "\t:precondition "+parametrizeCondition( c, "FLAGGED" + p, false )+"\n";
				os << "\t:ordered-subtasks (and"<<parametrizeCondition( c, "i-UNFLAG" + p, false )<<")"<<std::endl;
				os << ")"<<std::endl;

				os << "( :method " << parametrizeHDDLCondition( c, s + p) <<std::endl;
				os << "\t:task"<<parametrizeCondition( c, s + p, false)<<std::endl;
				os << "\t:precondition (not "+parametrizeCondition( c, "FLAGGED" + p, false )+")"<<std::endl;
				os << "\t:ordered-subtasks (and"<<parametrizeCondition( c, "i-UNLOCK" + p, false )<<")"<<std::endl;
				os << ")"<<std::endl;
	}


	void printPredicate( Condition &c, std::ostream &stream, bool b, bool n,
	                     const std::string &s, const std::string &t, int invariant_number=-1 ) {
		//std::string p( n ? "N-" : "-" );
		std::string p("-");
		std::string q = "               ( )\n";
		std::string r = "               (";
		std::string u = parametrizeCondition( c, t + p, false, invariant_number ) + " )\n";

		stream << "    ( :OPERATOR" << parametrizeCondition( c, s + p, false, invariant_number ) << "\n";
		if ( b ) stream << q << q << r << u;
		else stream << q << r << u << q;
		stream << "    )\n";
	}

	void printPredicate(Condition &c, std::ostream &stream, bool b, bool n, Condition &prec,
	                     const std::string &s, const std::string &t, int invariant_number=-1 ) {
		std::string p("-");
		std::string empty("               ( )\n");
		std::string q = "               (";
		q+=parametrizeCondition( prec, "DID-", n, invariant_number );
		q+=")\n";
		std::string r = "               (";
		std::string u = parametrizeCondition( c, t + p, false, invariant_number ) + " )\n";

		stream << "    ( :OPERATOR" << parametrizeCondition( c, s + p, false, invariant_number ) << "\n";
		if ( b ) stream << q << empty << r << u;
		else stream << q << r << u << empty;
		stream << "    )\n";
	}

	void printHDDLAuxAction( Condition &c, std::ostream &os, bool b, bool n,
	                     const std::string &s, const std::string &t, int invariant_number=-1 ) {
		std::string p("-");
		std::string u = parametrizeCondition( c, t + p, b, invariant_number );
		os<<"( :action "<<s+p<<c.name<<std::endl;
		os<<"\t:parameters (";
				for ( unsigned i = 0; i < c.params.size(); ++i )
					os << " ?" << types[c.params[i]].name << i <<" - "<<types[c.params[i]].name;
				os<<")"<<std::endl;
		os<<"\t:precondition ( )"<<std::endl;
		os<<"\t:effect (and"<<std::endl;
			os<<"\t\t";
			os<<u;
			os << ")"<<std::endl;
		os<<")"<<std::endl;
	}
};

class Instance {
public:
	Domain &d;
	std::string name;
	CondVec init, goal; // initial and goal states
	StringDVec objects; // objects
	TokenVec omap;      // maps for objects

//	Instance( Domain &dom, const std::string &s )
//		: d( dom ), objects( d.constants.size() ), omap( d.cmap.size() ) {
	Instance( Domain &dom, const std::string &s )
		: d( dom ), objects( d.constants ), omap( d.cmap ) {
		parse(s);
	}

	void parse( const std::string &s) {
		Filereader f( s );
		name = parseName( f, "PROBLEM" );

		if ( DOMAIN_DEBUG ) std::cout << name << "\n";
    
		for ( ; f.getChar() != ')'; f.next() ) {
			f.assert( "(" );
			f.assert( ":" );
			std::string t = f.getToken();

			if ( DOMAIN_DEBUG ) std::cout << t << "\n";

			if ( t == "DOMAIN" ) parseDomain( f );
			else if ( t == "OBJECTS" ) parseObjects( f );
			else if ( t == "INIT" ) parseInit( f );
			else if ( t == "GOAL" ) parseGoal( f );
			else {
				f.c -= t.size();
				f.printLine();
				std::cout << "Unknown type " << t << "\n";
				exit( 1 );
			}
		}
	}

	void parseDomain( Filereader &f ) {
		f.next();
		f.assert( d.name );
		f.assert( ")" );
	}

	void parseObjects( Filereader &f ) {
		parseObjectList( f, d.tmap, d.types, objects, omap );

		for ( unsigned i = 0; DOMAIN_DEBUG && i < objects.size(); ++i ) {
			std::cout << " ";
			if ( d.typed ) std::cout << " " << d.types[i] << ":";
			for ( unsigned j = 0; j < objects[i].size(); ++j )
				std::cout << " " << objects[i][j];
			std::cout << "\n";
		}
	}

	void parsePredicate( Filereader &f, CondVec &v ) {
		int x = f.tokenIndex( d.pmap );
		f.next();
    
		Condition c( d.preds[x] );
		for ( unsigned i = 0; i < d.preds[x].params.size(); ++i, f.next() )
			c.params[i] = f.tokenIndex( omap[d.preds[x].params[i]], d.cmap[d.preds[x].params[i]] );
		f.assert( ")" );
		v.push_back( c );
	}

	void parseInit( Filereader &f ) {
		for ( f.next(); f.getChar() != ')'; f.next() ) {
			f.assert( "(" );
			parsePredicate(f, init);
		}
		++f.c;

		for ( unsigned i = 0; DOMAIN_DEBUG && i < init.size(); ++i )
			std::cout << "  " << init[i] << "\n";
	}

	void parseGoal( Filereader &f ) {
		f.next();
		f.assert("(");
		std::string s = f.getToken();
		if ( s == "AND" ) {
			for ( f.next(); f.getChar() != ')'; f.next() ) {
				f.assert( "(" );
				parsePredicate( f, goal );
			}
			++f.c;
			f.next();
		}
		else {
			f.c -= s.size();
			parsePredicate( f, goal );
		}
		f.assert( ")" );

		for ( unsigned i = 0; DOMAIN_DEBUG && i < goal.size(); ++i )
			std::cout << "  " << goal[i] << "\n";
	}
};
