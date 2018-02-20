default: tests.log

test:
	@if ! ../../lib/cbmc/regression/test.pl -c "../../../src/symex/symex --shortest-path" ; then \
		../../lib/cbmc/regression/failed-tests-printer.pl ; \
		exit 1 ; \
	fi

		@if ! ../../lib/cbmc/regression/test.pl -c "../../../src/symex/symex --shortest-path --randomize" ; then \
		../../lib/cbmc/regression/failed-tests-printer.pl ; \
		exit 1 ; \
	fi

tests.log: ../test.pl
	@if ! ../../lib/cbmc/regression/test.pl -c "../../../src/symex/symex --shortest-path" ; then \
		../../lib/cbmc/regression/failed-tests-printer.pl ; \
		exit 1 ; \
	fi

	@if ! ../../lib/cbmc/regression/test.pl -c ../../../src/symex/symex "--shortest-path --randomize" ; then \
		../../lib/cbmc/regression/failed-tests-printer.pl ; \
		exit 1 ; \
	fi

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) '{}' \;
	$(RM) tests.log
