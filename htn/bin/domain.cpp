
#include "domain.h"

int main( int argc, char *argv[] ) {
	if ( argc < 3 ) {
		std::cout << "Usage: ./domain <domain.pddl> <task.pddl>\n";
		exit( 1 );
	}
	Domain d( argv[1] );
	Instance i( d, argv[2] );
}
