LIBRARIES= ./commons-cli-1.2/commons-cli-1.2.jar

all:
	rm -r -f DLBanyan
	#fsc *.scala -unchecked -deprecation
	fsc *.scala -unchecked -deprecation -cp $(LIBRARIES) 
	make run

run:
	#scala DLBanyan.Test --input examples/simpler.dl
	scala DLBanyan.Test examples/simpler.dl

spaceex:
	${SPACEEX} -m DLBanyan/_.xml --config DLBanyan/_.cfg

graph:
	dot DLBanyan/_.dot -Tps | gv -
