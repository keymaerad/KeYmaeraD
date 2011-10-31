BACKENDSOURCES= types.scala rational.scala logicutil.scala arithmetic.scala \
	parse.scala keyparse.scala printing.scala \
	nodes.scala mathematicautil.scala \
	rules.scala procedures.scala jobs.scala \
	DLprover.scala 

FRONTENDSOURCES= frontend.scala frontactor.scala GUI/guifrontend.scala \
	tactics.scala 	


LIBRARIES= .:$(JLINK)/JLink.jar:./commons-cli-1.2/commons-cli-1.2.jar


ifndef SCALAC
SCALAC= fsc
endif


OPTIONS=
ALLOPTIONS=${OPTIONS} -deprecation -unchecked


all : backend frontend

.PHONY : prover
.PHONY : backend

backend : KeYmaeraD/rules.class
frontend : KeYmaeraD/frontend.class 

KeYmaeraD/rules.class : specialoptions $(BACKENDSOURCES)
	$(SCALAC)  -classpath $(LIBRARIES) $(BACKENDSOURCES) $(ALLOPTIONS)

KeYmaeraD/frontend.class  : specialoptions $(FRONTENDSOURCES)
	$(SCALAC)  -classpath $(LIBRARIES) $(FRONTENDSOURCES) $(ALLOPTIONS)

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
