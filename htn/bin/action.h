
#include "cond.h"

class Action: public Condition {
public:
	std::vector< Condition > pre, add, del;
  
	Action( std::string s ) : Condition(s) {}

	// return delete effect (x < 0) or add effect (x >= 0)
	Condition getCondition( int x ) {
		return x < 0 ? del[-1 - x] : add[x];
	}

	// return typified delete effect (x < 0) or add effect (x >= 0)
	Condition typeCondition( int x ) {
		Condition c = getCondition( x );
		typify( c );
		return c;
	}

	// typify: replace a condition's types with those of the action
	void typify( Condition &c ) {
		for ( unsigned i = 0; i < c.params.size(); ++i )
			if ( c.params[i] >= 0 ) c.params[i] = params[c.params[i]];
	}

};

std::ostream &operator<<( std::ostream &stream, const Action &a ) {
	stream << "\n" << (Condition)a;
	for ( unsigned i = 0; i < a.pre.size(); ++i )
		stream << "\nPre: " << a.pre[i];
	for ( unsigned i = 0; i < a.add.size(); ++i )
		stream << "\nAdd: " << a.add[i];
	for ( unsigned i = 0; i < a.del.size(); ++i )
		stream << "\nDel: " << a.del[i];
	return stream;
}
