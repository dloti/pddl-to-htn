
#include "create_htn.h"

#define UNORDERED false
#define LISP false
#define JSHOP2H false
//optimizations
#define GORDER false

int main( int argc, char *argv[] ) {
	if ( argc < 4 ) {
		std::cout << "Usage: ./initialize <domain_name> <domain_file> <instance_file>\n";
		exit( 1 );
	}
	
	Domain d( argv[2] );
	Instance ins( d, argv[3] );
	createHTN( argv[1], d, ins );

	std::ostream fout(std::cout.rdbuf());

	
	fout << "\n(DEFPROBLEM PROBLEM " << argv[1] << "\n    (\n";
	for ( unsigned i = 0; i < ins.objects.size(); ++i )
		for ( unsigned j = 0; j < ins.objects[i].size(); ++j )
			fout << "        (" << d.types[i].name << " " << ins.objects[i][j] << ")\n";
	for ( unsigned i = 0; i < ins.init.size(); ++i ) {
		fout << "        (" << ins.init[i].name;
		Condition c = d.preds[d.pmap[ins.init[i].name]];
		for ( unsigned j = 0; j < c.params.size(); ++j )
			fout << " " << ins.objects[c.params[j]][ins.init[i].params[j]];
		fout << ")\n";
	}
if(GORDER){
	//add goals to initial state
	for (unsigned j = 0; j < ins.goal.size(); ++j) {
		Condition c = d.preds[d.pmap[ins.goal[j].name]];
		fout << "        (TGOAL-" << c.name;
		for (unsigned k = 0; k < c.params.size(); ++k)
			fout << " " << ins.objects[c.params[k]][ins.goal[j].params[k]];
		fout << ")\n";
	}
}	fout << "    )\n    ";
	fout << "(" + std::string(UNORDERED ? " :UNORDERED" : "") + "\n";

//preordered for each instance
//	unsigned ordercnt = 0;
//	for (unsigned tc=0; tc < trorder.size(); ++tc) {
//		for (unsigned j = 0; j < goalTypeMap[trorder[tc]].size(); ++j) {
//			Condition c = d.preds[d.pmap[goalTypeMap[trorder[tc]][j].name]];
//			fout << "        (GOAL-" << c.name<<" "<<ordercnt;++ordercnt;
//			for (unsigned k = 0; k < c.params.size(); ++k)
//				fout << " " << ins.objects[c.params[k]][goalTypeMap[trorder[tc]][j].params[k]];
//			fout << ")\n";
//		}
//	}
//	fout << "    )\n    ";
//	fout << "("+std::string(UNORDERED?" :UNORDERED":"")+"\n";

//OLD code which ordered goals by types in goal state
//// for ( CondGraphMap::iterator i = gmacro.graphs[0].begin(); i != gmacro.graphs[0].end(); ++i ) {
//	for ( std::vector<Condition>::iterator i = grorder.begin(); i != grorder.end(); ++i ) {
//		for ( unsigned j = 0; j < ins.goal.size(); ++j ) {
//			Condition c = d.preds[d.pmap[ins.goal[j].name]];
////			if ( i->first.name == c.name ) {
//			if(i->name == c.name){
//				bool z = true;
//				for ( unsigned k = 0; k < c.params.size(); ++k ) {
//					std::string token = ins.objects[c.params[k]][ins.goal[j].params[k]];
////					TokenMap::iterator it = ins.omap[i->first.params[k]].find( token );
////					z &= it != ins.omap[i->first.params[k]].end();
//					TokenMap::iterator it = ins.omap[i->params[k]].find( token );
//					z &= it != ins.omap[i->params[k]].end();
//				}
//				if ( z ) {
//					fout << "        (achieve-" << c.name;
//					for ( unsigned k = 0; k < c.params.size(); ++k )
//						fout << " " << ins.objects[c.params[k]][ins.goal[j].params[k]];
//					fout << ")\n";
//				}
//			}
//		}
//
//	}

if(GORDER)	{
			 fout<<"        (ORDER 0)\n"; 
			 fout<<"        (SOLVE 0)";
			}
else{
	for ( unsigned j = 0; j < ins.goal.size(); ++j ) {
		Condition c = d.preds[d.pmap[ins.goal[j].name]];
		std::cout << "        (ACHIEVE-" << c.name;
			for (unsigned k = 0; k < c.params.size(); ++k)
				std::cout << " " << ins.objects[c.params[k]][ins.goal[j].params[k]];
			std::cout << ")\n";
	}
}
fout<<"\t)\n";
	if(JSHOP2H)
		fout << ";heuristic\n";
	fout<< ")\n\n";
	
	if(LISP)
		fout << "(find-plans 'PROBLEM :verbose :plans)\n";
}
