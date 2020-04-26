@echo off

if (%1) == (c) goto :Compile
if (%1) == (d) goto :Doc
if (%1) == (1) goto :Run1
if (%1) == (2) goto :Run2
if (%1) == (3) goto :Run3
if (%1) == (4) goto :Run4
if (%1) == (5) goto :Run5
if (%1) == (6) goto :Run6
if (%1) == (7) goto :Run7
if (%1) == (8) goto :Run8
if (%1) == (9) goto :Run9
if (%1) == (10) goto :Run10

goto :Compile

:Compile
  cd src\JSHOP2
  java antlr.Tool JSHOP2.g
  javac *.java
  cd ..
  jar cvf JSHOP2.jar JSHOP2\*.class
  del JSHOP2\*.class
  del JSHOP2\JSHOP2Lexer.*
  del JSHOP2\JSHOP2Parser.*
  del JSHOP2\JSHOP2TokenTypes.java
  del JSHOP2\JSHOP2TokenTypes.txt
  move JSHOP2.jar ..\bin
  cd ..
  goto :End

:Doc
  del doc/s/q > NUL
  cd src
  javadoc -d ..\doc -author -version -private JSHOP2
  cd ..
  goto :End

:Run1
  cd examples\blocks
  java JSHOP2.InternalDomain blocks
  java JSHOP2.InternalDomain -r problem
  javac problem.java
  java -Xss2048K problem
  del blocks.java
  del blocks.txt
  del problem.java
  del *.class
  cd ..\..
  goto :End

:Run2
  cd examples\basic
  java JSHOP2.InternalDomain basic
  java JSHOP2.InternalDomain -r problem
  javac problem.java
  java problem
  del basic.java
  del basic.txt
  del problem.java
  del *.class
  cd ..\..
  goto :End

:Run3
  cd examples\oldblocks
  java JSHOP2.InternalDomain oldblocks
  java JSHOP2.InternalDomain -r problem
  javac problem.java
  java problem
  del oldblocks.java
  del oldblocks.txt
  del problem.java
  del *.class
  cd ..\..
  goto :End

:Run4
  cd examples\test
  java JSHOP2.InternalDomain test
  java JSHOP2.InternalDomain -r12 problem
  javac problem.java
  java problem
  del test.java
  del test.txt
  del problem.java
  del *.class
  cd ..\..
  goto :End

:Run5
  cd examples\logistics
  java JSHOP2.InternalDomain logistics
  java JSHOP2.InternalDomain -r problem
  javac problem.java
  java problem
  del logistics.java
  del logistics.txt
  del problem.java
  del *.class
  cd ..\..
  goto :End

:Run6
  cd examples\freecell
  java JSHOP2.InternalDomain freecell
  java JSHOP2.InternalDomain -r problem
  javac problem.java
  java problem
  del freecell.java
  del freecell.txt
  del problem.java
  del *.class
  cd ..\..
  goto :End

:Run7
  cd examples\propagation
  java JSHOP2.InternalDomain propagation
  java JSHOP2.InternalDomain -r problem
  javac problem.java
  java problem
  del propagation.java
  del propagation.txt
  del problem.java
  del *.class
  cd ..\..
  goto :End

:Run8
  cd examples\forall
  java JSHOP2.InternalDomain forall
  java JSHOP2.InternalDomain -ra problem
  javac problem.java
  java problem
  del forallexample.java
  del forallexample.txt
  del problem.java
  del *.class
  cd ..\..
  goto :End

:Run9
  cd examples\rover
  java JSHOP2.InternalDomain rover
  java JSHOP2.InternalDomain -r problem
  javac problem.java
  java problem
  del rover.java
  del rover.txt
  del problem.java
  del *.class
  cd ..\..
  goto :End

:Run10
  cd examples\blocks
  java JSHOP2.InternalDomain blocks
  java JSHOP2.InternalDomain -ra smallproblem
  javac smallproblem.java
  java smallproblem
  del blocks.java
  del blocks.txt
  del smallproblem.java
  del *.class
  cd ..\..
  goto :End

:End
