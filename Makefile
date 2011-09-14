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
ALLOPTIONS=$(OPTIONS) -deprecation -unchecked


all : version $(SCALAFILES)
	$(SCALAC)  -classpath $(LIBRARIES) $(SCALAFILES) $(ALLOPTIONS)

version : 	
	$(SCALAC) -version 2>&1 | python specialoptions.py > specialoptions

clean :
	rm -f specialoptions
	rm -rf DLBanyan/
	fsc -shutdown -verbose
