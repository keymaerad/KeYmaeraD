SCALAFILES= banyan.scala  worker.scala coordinator.scala \
	rational.scala  arithmetic.scala \
	DLprover.scala DLclient.scala parse.scala  printing.scala \
	DLrunner.scala

SCALAFLYLES= $(SCALAFILES) banyan-fly.scala

BANYANFILES = banyan.scala worker.scala coordinator.scala printing.scala

PROVERFILES = rational.scala arithmetic.scala \
		DLprover.scala DLclient.scala parse.scala

LIBRARIES= .:./commons-cli-1.2/commons-cli-1.2.jar:$(JLINK)/JLink.jar

ifndef SCALAC
SCALAC = fsc
endif


all : $(SCALAFILES)
	$(SCALAC)  -classpath $(LIBRARIES) $(SCALAFILES) -deprecation -unchecked


banyan : $(BANYANFILES)
	$(SCALAC) -classpath $(LIBRARIES) $(BANYANFILES) -deprecation -unchecked

prover : $(PROVERFILES)
	$(SCALAC) -classpath .:./commons-cli-1.2/commons-cli-1.2.jar $(PROVERFILES) -deprecation -unchecked

withfly : $(SCALAFLYLES)
	$(SCALAC) -classpath .:./commons-cli-1.2/commons-cli-1.2.jar:../FlyScala-1.3.7.jar $(SCALAFLYLES) -deprecation -unchecked

clean :
	rm -rf banyan/ DLProver/