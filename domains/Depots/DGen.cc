#include <iostream>
#include <fstream>
#include <stdlib.h>
#include <string>
#include <vector>

enum typeStatus {ON,OFF};
typeStatus typing;

int rnd(int limit) {
	return 1+(int) ((((double)((long int)limit)*random()))/(RAND_MAX+1.0));
};

int rnd2(int limit) {
	return limit/2 + rnd(limit/2);
};

int rnd3(int locs,int limit)
{
	return (int) (locs*(1.0+(double)(((long int)(limit-1)) * random())/(RAND_MAX+1.0)));
};


struct locatable {
	int location;
	locatable(int locs) : location(rnd(locs)) {};
	locatable() : location(0) {};
};


struct Truck : public locatable {
	int capacity;
	int speed;
	Truck(int locs,int maxc) : locatable(locs), capacity(rnd2(maxc)),
			speed(rnd(10))
 	{};
};

struct Pallet : public locatable {
	int topcrate;
	int dtopcrate;
	Pallet(int locs) : locatable(locs), topcrate(0), dtopcrate(0) {};
};

struct Crate : public locatable {
	static int maxWeight;
	int weight;
	int pallet;
	int surface;

	int dpallet;
	int dsurface;

	Crate(int ps,int maxw) : locatable(), pallet(rnd(ps)), 
							weight(rnd(maxw)), dpallet(0), dsurface(0)
	 {
		maxWeight = weight>maxWeight?weight:maxWeight;
	 };		
};

int Crate::maxWeight = 0;

struct Hoist : public locatable {
	int powr;

	Hoist(int locs) : locatable(locs), powr(rnd(10))
	{};
};

struct Map {
	vector< vector<int> > distances;

	Map(int locs)
	{
		for(int i = 0;i < locs;++i)
		{
			distances.push_back(vector<int>());
			for(int j = 0;j < locs;++j)
				distances[i].push_back(rnd(10));
		};
	};
};

struct DepotDescriptor {
	enum ProblemType {STRIPS,NUMERIC,SIMPLETIMED,TIMED};
	int numDepots;
	int numDistributors;
	int numTrucks;
	int numPallets;
	int numHoists;
	int numCrates;

	ProblemType probtype;

	int maxCapacity;
	int maxWeight;

	DepotDescriptor(int dps,int dsts,int trks,int plts,int hsts,int crts,ProblemType tp = DepotDescriptor::STRIPS,int mxwt = 0,int mxcp = 0) :
		numDepots(dps), numDistributors(dsts), numTrucks(trks), numPallets(plts),
		numHoists(hsts), numCrates(crts), probtype(tp), maxCapacity(mxcp), 
		maxWeight(mxwt) {};
};



class Depot {
private:
	int seed;
	DepotDescriptor::ProblemType probtype;

	int numDepots;
	int numDistributors;

	vector<Truck> trucks;
	vector<Pallet> pallets;
	vector<Hoist> hoists;
	vector<Crate> crates;

	Map * m;

	void location(ostream & o,int i) const
	{
		if(i < numDepots) 
		{
			o << "depot" << i;
		}
		else
		{
			o << "distributor" << i - numDepots;
		};
	};

 	void location(ostream & o,const locatable & l) const
	{
		location(o,l.location-1);
	};




public:
	Depot(unsigned int s,const DepotDescriptor & d) : 
		seed(s), probtype(d.probtype)
	{
		srandom(s);
		numDepots = d.numDepots;
		numDistributors = d.numDistributors;
		int numTrucks = d.numTrucks;
		int locs = numDepots+numDistributors;
		m = new Map(locs);
		int numPallets = max(d.numPallets,locs);
		int numHoists = max(d.numHoists,locs);
		
		for(int i = 0;i < numTrucks;++i)
		{
			Truck t(locs,d.maxCapacity);
			trucks.push_back(t);
		};

		for(int i = 0;i < numHoists;++i)
		{
			Hoist h(locs);
			if(i < locs) h.location = i+1;
			hoists.push_back(h);
		};

		for(int i = 0;i < numPallets;++i)
		{
			Pallet p(locs);
			if(i < locs) p.location = i+1;
			pallets.push_back(p);
		};

		for(int i = 0;i < d.numCrates;++i)
		{
			Crate c(numPallets,d.maxWeight);
			c.location = pallets[c.pallet-1].location;
			c.surface = pallets[c.pallet-1].topcrate;
			pallets[c.pallet-1].topcrate = i+1;
			crates.push_back(c);
		};

		for(int i = 0;i < 2*d.numCrates; ++i)
		{
			int c = rnd(d.numCrates)-1;
			if(crates[c].dpallet) continue;
			crates[c].dpallet = rnd(numPallets);
			crates[c].dsurface = pallets[crates[c].dpallet-1].dtopcrate;
			pallets[crates[c].dpallet-1].dtopcrate = c+1;
		};


	};

	~Depot() {delete m;};

	void write(ostream & o) const
	{
		o << "(define (problem depotprob" << seed << ") (:domain Depot)\n(:objects\n\t";
		for(int i = 0;i < numDepots;++i)
		{
			o << "depot" << i << " ";
		};
		if(typing==ON) o << "- Depot\n\t";
		for(int i = 0;i < numDistributors;++i)
		{
			o << "distributor" << i << " ";
		};
		if(typing==ON) o << "- Distributor\n\t";
		for(int i = 0;i < trucks.size();++i)
		{
			o << "truck" << i << " ";
		};
		if(typing==ON) o << "- Truck\n\t";
		for(int i = 0;i < pallets.size();++i)
		{
			o << "pallet" << i << " ";
		};
		if(typing==ON) o << "- Pallet\n\t";
		for(int i = 0;i < crates.size();++i)
		{
			o << "crate" << i << " ";
		};
		if(typing==ON) o << "- Crate\n\t";
		for(int i = 0;i < hoists.size();++i)
		{
			o << "hoist" << i << " ";
		};
		if(typing==ON) o << "- Hoist";
		o << ")\n(:init\n";
		for(int i = 0;i < pallets.size();++i)
		{
			if(typing==OFF) 
			{
				o << "\t(pallet pallet" << i << ")\n";
				o << "\t(surface pallet" << i << ")\n";
			};
			o << "\t(at pallet" << i << " ";	
			location(o,pallets[i]);
			o << ")\n\t(clear ";
			if(pallets[i].topcrate)
			{
				o << "crate" << pallets[i].topcrate-1 << ")\n";
			}
			else
			{
				o << "pallet" << i << ")\n";
			};
		};
		for(int i = 0;i < trucks.size();++i)
		{
			if(typing==OFF) 
			{
				o << "\t(truck truck" << i << ")\n";
			};
			o << "\t(at truck" << i << " ";	
			location(o,trucks[i]);
			o << ")\n";
			if(probtype==DepotDescriptor::TIMED)
			{
				o << "\t(= (speed truck" << i << ") " << 
				  trucks[i].speed << ")\n";

			};
			if(probtype==DepotDescriptor::NUMERIC)
			{
				o << "\t(= (current_load truck" << i << ") 0)\n"
				 << "\t(= (load_limit truck" << i << ") ";
				if(2*trucks[i].capacity < Crate::maxWeight || i==0)
				{
 					o << trucks[i].capacity + Crate::maxWeight << ")\n";
				}
				else
				{
					o << trucks[i].capacity << ")\n";
				};

			};
		};
		for(int i = 0;i < hoists.size();++i)
		{
			if(typing==OFF) 
			{
				o << "\t(hoist hoist" << i << ")\n";
			};
			o << "\t(at hoist" << i << " ";	
			location(o,hoists[i]);
			o << ")\n\t(available hoist" << i << ")\n";
			if(probtype==DepotDescriptor::TIMED)
			{
				o << "\t(= (power hoist" << i << ") " 
						<< hoists[i].powr << ")\n";
			};
		};
		for(int i = 0;i < crates.size();++i)
		{
			if(typing==OFF) 
			{
				o << "\t(crate crate" << i << ")\n";
				o << "\t(surface crate" << i << ")\n";
			};
			o << "\t(at crate" << i << " ";	
			location(o,crates[i]);
			o << ")\n\t(on crate" << i << " ";
			if(crates[i].surface)
			{
				o << "crate" << crates[i].surface-1 << ")\n";
			}
			else
			{
				o << "pallet" << crates[i].pallet-1 << ")\n";
			};
			if(probtype==DepotDescriptor::NUMERIC || 
				probtype==DepotDescriptor::TIMED)
			{
				o << "\t(= (weight crate" << i << ") " << crates[i].weight << ")\n";
			};
		};
		if(typing==OFF)
		{
			for(int i = 0; i < numDepots+numDistributors;++i)
			{
				o << "\t(place ";
				location(o,i);
				o << ")\n";
			};
		};
		if(probtype==DepotDescriptor::TIMED)
		{
			for(int i = 0; i < m->distances.size(); ++i)
			{
				for(int j = 0; j < m->distances[i].size(); ++j)
				{
					o << "\t(= (distance ";
					location(o,i);
					o << " ";
					location(o,j);
					o << ") ";
					if(j != i)
					{
						o << m->distances[i][j] << ")\n";
					}
					else
					{
						o << "0)\n";
					};
				};
			};
		};

		if(probtype==DepotDescriptor::NUMERIC) o << "\t(= (fuel-cost) 0)\n";

		o << ")\n\n(:goal (and\n";
		for(int i = 0;i < crates.size();++i)
		{
			if(crates[i].dpallet)
			{
				if(crates[i].dsurface)
				{
					o << "\t\t(on crate" << i << " crate" << 
							crates[i].dsurface-1 << ")\n";
				}
				else
				{
					o << "\t\t(on crate" << i << " pallet" <<
							crates[i].dpallet-1 << ")\n";
				};
			};
		};
		o << "\t)\n)";
		if(probtype != DepotDescriptor::STRIPS && probtype != DepotDescriptor::NUMERIC)
			o << "\n\n(:metric minimize (total-time))";
		if(probtype == DepotDescriptor::NUMERIC)
		{
		  if(rnd(10) < 4) o << "\n\n(:metric minimize (fuel-cost))";
		  else o << "\n\n(:metric minimize (total-time))";
		};
		o << ")\n";
		
	};

};

ostream & operator<<(ostream& o,const Depot & d)
{
	d.write(o);
	return o;
};

void usage()
{
	cout << "Useage: gdep <seed> [-s|-t|-n|-w <weight>|-c <capacity>|-f <filename>]\n\t\t<#depots> <#distributors> <#trucks> <#pallets> <#hoists> <#crates>\n\n\tOptions:\n\tu: untyped\n\ts: simple-time\n\tt: time\n\tn: numeric\n\tw: provide maximum weight for crates\n\tc: maximum capacity for trucks\n\tf: optional file for output\n\n\tAll numbers are integers.\n\n";

	exit(0);
};



DepotDescriptor commandLine(int & seed,string & filename,int argc, char * argv[])
{
	DepotDescriptor::ProblemType probtype = DepotDescriptor::STRIPS;
	int wgt = 1;
	int cap = 1;
	int nxt = 0;
	int val[6];

	if(argc <= 0) usage();

	seed = atoi(argv[0]);
	--argc;
	++argv;

	while(argc>0)
	{
		if(*argv[0]=='-')
		{
			switch(char o = *++argv[0])
			{
				case 't':
					probtype = DepotDescriptor::TIMED;
					break;
				case 's':
					probtype = DepotDescriptor::SIMPLETIMED;
					break;
				case 'n':
					probtype = DepotDescriptor::NUMERIC;
					break;
				case 'u':
				        typing = OFF;
					break;
				default:
					--argc;
					++argv;
					if(argc < 0) usage();
					switch(o)
					{
						case 'w':
							wgt = atoi(argv[0]);
							break;
						case 'c':
							cap = atoi(argv[0]);
							break;
						case 'f':
							filename = string(argv[0]);
							break;
						default:
							usage();
					};
			};
			--argc;
			++argv;
		}
		else 
		{
			if(nxt == 6) usage();
			val[nxt++] = atoi(argv[0]);
			++argv;
			--argc;
		};
	};

	if(nxt < 6) usage();

	return DepotDescriptor(val[0],val[1],val[2],val[3],val[4],val[5],probtype,wgt,cap);
};
							


int main(int argc,char * argv[])
{
        typing = ON;
	int seed;
	string filename("");

	DepotDescriptor d = commandLine(seed,filename,--argc,++argv);

	Depot dp(seed,d);

	ostream o;
	if(filename != "") 
	{
		ofstream o(filename.c_str());
		o << dp;
	}
	else
	{
		cout << dp;
	};

	return 0;
};


