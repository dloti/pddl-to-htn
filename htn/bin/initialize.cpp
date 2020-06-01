
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

	
	fout << "(define (problem p)"<<std::endl;
	fout << "(:domain "<<argv[1]<<")"<<std::endl;
	fout<<"(:objects"<<std::endl;
	for ( unsigned i = 0; i < ins.objects.size(); ++i )
		for ( unsigned j = 0; j < ins.objects[i].size(); ++j )
			fout << "\t" << ins.objects[i][j] << " - " << d.types[i].name << std::endl;
	fout<<")"<<std::endl;//end objects

	if(GORDER){
	//add goals to initial state
	for (unsigned j = 0; j < ins.goal.size(); ++j) {
		Condition c = d.preds[d.pmap[ins.goal[j].name]];
		fout << "        (TGOAL-" << c.name;
		for (unsigned k = 0; k < c.params.size(); ++k)
			fout << " " << ins.objects[c.params[k]][ins.goal[j].params[k]];
		fout << ")\n";
	}
}	//fout << "    )\n    ";
	//fout << "(" + std::string(UNORDERED ? " :UNORDERED" : "") + "\n";

// if(GORDER)	{
// 			 fout<<"        (ORDER 0)\n"; 
// 			 fout<<"        (SOLVE 0)";
// 			}
// else{
	fout<<"(:htn"<<std::endl;
	fout<<"\t:tasks (and"<<std::endl;
	for ( unsigned j = 0; j < ins.goal.size(); ++j ) {
		Condition c = d.preds[d.pmap[ins.goal[j].name]];
		std::cout << "\t(ACHIEVE-" << c.name;
			for (unsigned k = 0; k < c.params.size(); ++k)
				std::cout << " " << ins.objects[c.params[k]][ins.goal[j].params[k]];
			std::cout << ")"<<std::endl;
	}
	fout<<"\t)"<<std::endl; //end :tasks
	fout<<":ordering ( )"<<std::endl;
	fout<<":constraints ( )"<<std::endl;
	fout<<")"<<std::endl;
// }
	fout<<"(:init"<<std::endl;
	for ( unsigned i = 0; i < ins.init.size(); ++i ) {
		fout << "        (" << ins.init[i].name;
		Condition c = d.preds[d.pmap[ins.init[i].name]];
		for ( unsigned j = 0; j < c.params.size(); ++j )
			fout << " " << ins.objects[c.params[j]][ins.init[i].params[j]];
		fout << ")\n";
	}

fout<<")"<<std::endl;
	if(JSHOP2H)
		fout << ";heuristic\n";
	fout<< ")\n\n";
	
	if(LISP)
		fout << "(find-plans 'PROBLEM :verbose :plans)\n";
}
