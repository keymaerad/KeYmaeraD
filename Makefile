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

OPTIONS = -deprecation 

all : $(SCALAFILES)
	$(SCALAC)  -classpath $(LIBRARIES) $(SCALAFILES) $(OPTIONS)

clean :
	rm -rf DLBanyan/
	fsc -shutdown -verbose
