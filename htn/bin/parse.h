
#include "action.h"

typedef std::map< std::string, int > TokenMap;

class Filereader {
public:
	std::string s;      // current line of file
	std::ifstream f;    // file input stream
	unsigned r, c;      // current row and column of file
  
	Filereader( const std::string &file ) : f( file.c_str() ), r( 1 ), c( 0 ) {
		std::getline( f, s );
		if(!f) {
			std::cout<<"Error opening file "<<file<<std::endl;
			exit( 1 );
		}
		next();
	}

	~Filereader() {
		f.close();
	}

	// characters to be ignored
	bool ignore( char c ) {
		return c == ' ' || c == '\t' || c == '\r' || c == '\n' || c == '\f';
	}

	// parenthesis
	bool paren( char c ) {
		return c == '(' || c == ')' || c == '{' || c == '}';
	}

	// current character
	char getChar() {
		return s[c];
	}

	// print line and column
	void printLine() {
		std::cout << "Line " << r << ", column " << c+1 << ": ";
	}

	// get next non-ignored character
	void next() {
		for ( ; c < s.size() && ignore( s[c] ); ++c );
		while ( c == s.size() || s[c] == ';' ) {
			++r;
			if ( f.eof() ) {
				c = 0;
				printLine();
				std::cout << "Unexpected EOF\n";
				exit(1);
			}
			std::getline( f, s );
			for ( c = 0; c < s.size() && ignore( s[c] ); ++c );
		}
	}

	// get token converted to uppercase
	std::string getToken() {
		std::ostringstream os;
		while ( c < s.size() && !ignore( s[c] ) && !paren( s[c] ) && s[c] != ',' )
			os << ( 97 <= s[c] && s[c] <= 122 ? (char)( s[c++] - 32 ) : s[c++] );
		return os.str();
	}

	// assert syntax
	void assert( const std::string &t ) {
		unsigned b = 0;
		for ( unsigned k = 0; c + k < s.size() && k < t.size(); ++k )
			b += s[c + k] == t[k] || 
			     97 <= s[c + k] && s[c + k] <= 122 && s[c + k] == t[k] + 32;
		if ( b < t.size() ) {
			printLine();
			std::cout << t << " expected\n";
			exit( 1 );
		}
		c += t.size();
		next();
	}

	// get the index of a token
	int tokenIndex( TokenMap &m, TokenMap n = TokenMap() ) {
		std::string t = getToken();
		TokenMap::iterator i = m.find(t);
		if ( i == m.end() ) {
			i = n.find(t);
			if ( i == n.end() ) {
				c -= t.size();
				printLine();
				std::cout << t << " does not name a known token\n";
				exit( 1 );
			}
			return -i->second - 1;
		}
		return i->second;
	}
};
