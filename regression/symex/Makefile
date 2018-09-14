default: tests.log

test:
	@../../lib/cbmc/regression/test.pl -p -c ../../../src/symex/symex

tests.log: ../test.pl
	@../../lib/cbmc/regression/test.pl -p -c ../../../src/symex/symex

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
