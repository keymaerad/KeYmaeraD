SCALAFILES= types.scala rational.scala  arithmetic.scala \
	parse.scala  printing.scala nodes.scala \
        frontend.scala frontactor.scala \
	DLprover.scala  


LIBRARIES= .:./commons-cli-1.2/commons-cli-1.2.jar:$(JLINK)/JLink.jar

ifndef SCALAC
SCALAC = fsc
endif

all : $(SCALAFILES)
	$(SCALAC)  -classpath $(LIBRARIES) $(SCALAFILES) -deprecation -unchecked

clean :
	rm -rf DLBanyan/