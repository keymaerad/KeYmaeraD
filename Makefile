#LIBRARIES= ./commons-cli-1.2/commons-cli-1.2.jar

all:
	#make run FILE=examples/water_tank.dl
	#make run FILE=examples/bouncingball.dl
	make run FILE=tests/test2_false.dl

test:
	make run

compile:
	rm -r -f DLBanyan
	fsc *.scala -unchecked -deprecation
	#fsc *.scala -unchecked -deprecation -cp $(LIBRARIES) 
	make test

run:
	scala DLBanyan.Test $(FILE)

input:
	vi DLBanyan/_.xml DLBanyan/_.cfg

spaceex:
	${SPACEEX} -m DLBanyan/_.xml --config DLBanyan/_.cfg

graph:
	#dot DLBanyan/_.dot -Tps | gv -
	dot DLBanyan/_.dot -Tps > /tmp/ddl_graph.ps
	evince /tmp/ddl_graph.ps
