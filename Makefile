SCALAFILES= rational.scala  arithmetic.scala \
	DLprover.scala  parse.scala  printing.scala 


LIBRARIES= .:./commons-cli-1.2/commons-cli-1.2.jar:$(JLINK)/JLink.jar

ifndef SCALAC
SCALAC = fsc
endif


all : $(SCALAFILES)
	$(SCALAC)  -classpath $(LIBRARIES) $(SCALAFILES) -deprecation -unchecked



prover : $(PROVERFILES)
	$(SCALAC) -classpath .:./commons-cli-1.2/commons-cli-1.2.jar $(PROVERFILES) -deprecation -unchecked

clean :
	rm -rf DLProver/