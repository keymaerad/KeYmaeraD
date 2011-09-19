LIBRARIES= ./commons-cli-1.2/commons-cli-1.2.jar
TEST=examples/

all:
	#make run FILE=examples/simpler.dl
	#make run FILE=examples/simple.dl
	#make run FILE=examples/bouncingball.dl
	make run FILE=examples/water_tank.dl
	#make run FILE=examples/TRM-essentials.dl

compile:
	#rm -r -f DLBanyan
	#fsc *.scala -unchecked -deprecation
	fsc *.scala -unchecked -deprecation -cp $(LIBRARIES) 
	make

run:
	scala DLBanyan.Test $(FILE)

input:
	vi DLBanyan/_.xml DLBanyan/_.cfg

spaceex:
	${SPACEEX} -m DLBanyan/_.xml --config DLBanyan/_.cfg

graph:
	dot DLBanyan/_.dot -Tps | gv -
