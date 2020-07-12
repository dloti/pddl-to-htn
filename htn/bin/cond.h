
#include "basic.h"

class Condition {
public:
	std::string name;
	bool neg;
	int misc;
	std::vector< int > params;

	Condition() {}

	Condition( std::string s, bool b = false, int m = -1 )
		: name( s ), neg( b ), misc( m ) {}

	Condition( const Condition &c )
		: name( c.name ), neg( c.neg ), misc( c.misc ), params( c.params ) {}

	std::string c_str() {
		return name;
	}

	bool operator!=( const Condition &c ) const {
		return !( *this == c );
	}

	bool operator==( const std::string &s ) const {
		return name == s;
	}

	bool operator==( const Condition &c ) const {
		return name == c.name && params == c.params;
	}

	bool operator<( const Condition &c ) const {
		return neg < c.neg || neg == c.neg &&
		       ( name < c.name || name == c.name && params < c.params );
	}

	std::string tag(){
		std::ostringstream str;
		for(int i=0;i<params.size();++i)
			str<<params[i];
		return str.str();
	}

	std::string dbgstr(std::vector<Condition>& types){
		std::string ret = name+"[";
		for(int i=0;i<params.size();++i)
			ret+=types[params[i]].name+((i==params.size()-1)?"":", ");
		ret+="]";
		return ret;
	}
};

std::ostream &operator<<( std::ostream &stream, const Condition &c ) {
	stream << ( c.neg ? "NOT " : "" ) << c.name << "<" << c.misc << ">";
	return stream << c.params;
}

