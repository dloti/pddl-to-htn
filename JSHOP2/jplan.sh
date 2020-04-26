#!/bin/bash
# $1 - path, $2 - domain, $3 - problem name
export CLASSPATH=$CLASSPATH:~/ownCloud/research/hierarchy/htn/JSHOP2/bin/antlr.jar:~/ownCloud/research/hierarchy/htn/JSHOP2/bin/JSHOP2.jar:.
cwd=$(pwd)
cd $1;
mkdir -p "prob"$3
cp $3 "prob"$3"/problem"
cp $2 "prob"$3"/"$2
cd "prob"$3
java JSHOP2.InternalDomain $2;
java JSHOP2.InternalDomain -r problem;
cd $cwd;
python ~/ownCloud/research/hierarchy/htn/JSHOP2/shortener.py -p $1"prob"$3"/";
cd $1"prob"$3;
javac problem.java
#mkdir -p ../../../solutions/$2
#java -Xss4m problem > ../../../solutions/$2/$3".sol"
java problem
cd ..
#rm -rf "prob"$3
#rm $2".java"; rm  $2".txt"; rm problem.java; rm *.class
