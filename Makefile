all:
	./build.sh

test:	all
	./tests/tests/codegen/test.sh
	./tests/tests/codegen-hidden/test.sh

#FILE=./tests/tests/codegen/input/02-expr.dcf
#FILE=./tests/tests/codegen-hidden/input/hidden-17-divide.dcf
#FILE=./tests/tests/codegen/input/06-control-flow.dcf
FILE=./tests/tests/codegen/input/04-math2.dcf
#FILE=./fail.dcf
FILE=./tests/tests/codegen/input/05-calls.dcf
FILE=./tests/tests/codegen/input/09-global.dcf
FILE=./tests/tests/codegen/input/16-qsort.dcf
rtest:	all
	cat $(FILE)
	./run.sh -t opt $(FILE)
	./run.sh -t assembly $(FILE) | tee out.s
	gcc -o a.out out.s
	./a.out
