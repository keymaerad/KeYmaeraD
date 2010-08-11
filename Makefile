SCALAFILES= types.scala rational.scala  arithmetic.scala \
	parse.scala  printing.scala \ 
	nodes.scala \
	mathematicautil.scala \
	rules.scala procedures.scala jobs.scala \
        frontend.scala frontactor.scala \
	DLprover.scala  tactics.scala \
	GUI/guifrontend.scala


LIBRARIES= .:$(JLINK)/JLink.jar:$(JGRAPH)/lib/jgraphx.jar

ifndef SCALAC
SCALAC= fsc
endif


all : $(SCALAFILES)
	$(SCALAC)  -classpath $(LIBRARIES) $(SCALAFILES) -deprecation -unchecked

clean :
	rm -rf DLBanyan/
	fsc -shutdown -verbose
