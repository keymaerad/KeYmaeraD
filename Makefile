SCALAFILES= types.scala rational.scala logicutil.scala arithmetic.scala \
	parse.scala printing.scala \
	nodes.scala mathematicautil.scala \
	rules.scala procedures.scala jobs.scala \
	frontend.scala frontactor.scala \
	DLprover.scala tactics.scala GUI/guifrontend.scala


LIBRARIES= .:$(JLINK)/JLink.jar:./commons-cli-1.2/commons-cli-1.2.jar

ifndef SCALAC
SCALAC= fsc
endif


OPTIONS=
ALLOPTIONS=${OPTIONS} -deprecation -unchecked


all : prover

.PHONY : prover

prover : specialoptions $(SCALAFILES)
	$(SCALAC)  -classpath $(LIBRARIES) $(SCALAFILES) $(ALLOPTIONS)

specialoptions : 	
	$(SCALAC) -version 2>&1 | python specialoptions.py > specialoptions

clean :
	rm -f specialoptions
	rm -rf KeYmaeraD/
	$(SCALAC) -shutdown -verbose

# We should allow the tactics library to be compiled separately. 
#.PHONY : tacticlib
#tacticlib : KeYmaeraD/TacticLib/*.class
#KeYmaeraD/TacticLib/*.class : TacticLib/*.scala
#	$(SCALAC)  -classpath $(LIBRARIES) TacticLib/*.scala $(ALLOPTIONS)
