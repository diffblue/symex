
default: tests.log

test:
	@if ! ../../lib/cbmc/regression/test.pl -c ../chain.sh ; then \
		../../lib/cbmc/regression/failed-tests-printer.pl ; \
		exit 1; \
	fi

tests.log:
	pwd
	@if ! ../../lib/cbmc/regression/test.pl -c ../chain.sh ; then \
		../../lib/cbmc/regression/failed-tests-printer.pl ; \
		exit 1; \
	fi

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	@for dir in *; do \
		rm -f tests.log; \
		if [ -d "$$dir" ]; then \
			cd "$$dir"; \
			rm -f *.out *.gb; \
			cd ..; \
		fi \
	done
