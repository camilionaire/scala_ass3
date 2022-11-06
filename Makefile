# Makefsle for ScopeLang
#

.SUFFIXES: .scala .class

.PRECIOUS: %.scala

.scala.class:
	scalac $*.scala

all: testsli

SLInterp.class: ScopeLang.class
TestSLI.class: SLInterp.class 

sl:	ScopeLang.class
sli: SLInterp.class
testsli: TestSLI.class

clean:	
	rm *.class
