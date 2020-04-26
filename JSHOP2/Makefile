c: src/JSHOP2/JSHOP2.g src/JSHOP2/*.java
	cd src/JSHOP2; java -cp ~/ownCloud/research/hierarchy/htn/JSHOP2/bin/antlr.jar:~/ownCloud/research/hierarchy/htn/JSHOP2/bin/JSHOP2.jar antlr.Tool JSHOP2.g; javac -cp ~/ownCloud/research/hierarchy/htn/JSHOP2/bin/antlr.jar:~/ownCloud/research/hierarchy/htn/JSHOP2/bin/JSHOP2.jar *.java
	cd src; jar cvf JSHOP2.jar JSHOP2/*.class;
	rm src/JSHOP2/*.class
	rm src/JSHOP2/JSHOP2Lexer.*
	rm src/JSHOP2/JSHOP2Parser.*
	rm src/JSHOP2/JSHOP2TokenTypes.java
	rm src/JSHOP2/JSHOP2TokenTypes.txt
	mv src/JSHOP2.jar bin

d: src/JSHOP2/*.java
	rm -rf doc
	cd src; javadoc -d ../doc -author -version -private JSHOP2

1: bin/JSHOP2.jar
	cd examples/blocks; java JSHOP2.InternalDomain blocks
	cd examples/blocks; java JSHOP2.InternalDomain -r problem
	cd examples/blocks; javac problem.java
	cd examples/blocks; java -Xss2048K problem
	cd examples/blocks; rm blocks.java; rm blocks.txt; rm problem.java; rm *.class

2: bin/JSHOP2.jar
	cd examples/basic; java JSHOP2.InternalDomain basic
	cd examples/basic; java JSHOP2.InternalDomain -r problem
	cd examples/basic; javac problem.java
	cd examples/basic; java problem
	cd examples/basic; rm basic.java; rm basic.txt; rm problem.java; rm *.class

3: bin/JSHOP2.jar
	cd examples/oldblocks; java JSHOP2.InternalDomain oldblocks
	cd examples/oldblocks; java JSHOP2.InternalDomain -r problem
	cd examples/oldblocks; javac problem.java
	cd examples/oldblocks; java problem
	cd examples/oldblocks; rm oldblocks.java; rm oldblocks.txt; rm problem.java; rm *.class

4: bin/JSHOP2.jar
	cd examples/test; java JSHOP2.InternalDomain test
	cd examples/test; java JSHOP2.InternalDomain -r12 problem
	cd examples/test; javac problem.java
	cd examples/test; java problem
	cd examples/test; rm test.java; rm test.txt; rm problem.java; rm *.class

5: bin/JSHOP2.jar
	cd examples/logistics; java JSHOP2.InternalDomain logistics
	cd examples/logistics; java JSHOP2.InternalDomain -r problem
	cd examples/logistics; javac problem.java
	cd examples/logistics; java problem
	cd examples/logistics; rm logistics.java; rm logistics.txt; rm problem.java; rm *.class

6: bin/JSHOP2.jar
	cd examples/freecell; java JSHOP2.InternalDomain freecell
	cd examples/freecell; java JSHOP2.InternalDomain -r problem
	cd examples/freecell; javac problem.java
	cd examples/freecell; java problem
	cd examples/freecell; rm freecell.java; rm freecell.txt; rm problem.java; rm *.class

7: bin/JSHOP2.jar
	cd examples/propagation; java JSHOP2.InternalDomain propagation
	cd examples/propagation; java JSHOP2.InternalDomain -r problem
	cd examples/propagation; javac problem.java
	cd examples/propagation; java problem
	cd examples/propagation; rm propagation.java; rm propagation.txt; rm problem.java; rm *.class

8: bin/JSHOP2.jar
	cd examples/forall; java JSHOP2.InternalDomain forall
	cd examples/forall; java JSHOP2.InternalDomain -ra problem
	cd examples/forall; javac problem.java
	cd examples/forall; java problem
	cd examples/forall; rm forallexample.java; rm forallexample.txt; rm problem.java; rm *.class

9: bin/JSHOP2.jar
	cd examples/rover; java JSHOP2.InternalDomain rover
	cd examples/rover; java JSHOP2.InternalDomain -r problem
	cd examples/rover; javac problem.java
	cd examples/rover; java problem
	cd examples/rover; rm rover.java; rm rover.txt; rm problem.java; rm *.class

10: bin/JSHOP2.jar
	cd examples/blocks; java JSHOP2.InternalDomain blocks
	cd examples/blocks; java JSHOP2.InternalDomain -ra smallproblem
	cd examples/blocks; javac smallproblem.java
	cd examples/blocks; java smallproblem
	cd examples/blocks; rm blocks.java; rm blocks.txt; rm smallproblem.java; rm *.class
