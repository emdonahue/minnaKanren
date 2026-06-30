SHELL := /bin/bash
.PHONY: default clean profile bench repl rebench doc test debug

#TODO figure out how to compile a whole program that may have its own libraries that have name conflicts with internal libraries
#https://www.reddit.com/r/scheme/comments/lw8e4t/looking_for_a_chez_scheme_example_using_a/
#echo '(generate-wpo-files #t) (compile-library "src/mk/mk.ss") (compile-whole-library "src/mk/mk.wpo" "lib/mk.so")' | scheme -q --compile-imported-libraries --libdirs src/mk --optimize-level 3
#scheme --libdirs .:../lib --script main.ss
#echo '(generate-wpo-files #t) (compile-program "main.ss") (compile-whole-program "main.wpo" "main.so")' | scheme -q --libdirs ../lib:. --import-notify --optimize-level 3

default: lib/mk.so

lib/mk.so:
	make clean
	mkdir -p lib	
	echo '(generate-wpo-files #t) (compile-library "src/mk/mk.ss")' | scheme -q --compile-imported-libraries --libdirs src/mk --optimize-level 3
	echo '(compile-whole-library "src/mk/mk.wpo" "lib/mk.so")' | scheme -q --libdirs src/mk --optimize-level 3

clean:
	@rm -rf profile lib
	@find src -name '*.wpo' -delete -o -name '*.so' -delete

profile:
# Builds an html heatmap of function calls for optimization purposes.
	make clean
	mkdir -p profile
	echo "(compile-profile 'source) "'(import (chezscheme) (mk)) (load "src/profile/profile.ss") (profile-dump-html "profile/")' | scheme -q --libdirs 'src/mk:src/tests:src/benchmarks:src/examples' --optimize-level 1 # The non-zero optimize level turns off debug code like (cert)

bench:
# Builds a set of benchmarks to test performance improvements.
	make clean
	@mkdir -p benchmarks
	@echo '(generate-wpo-files #t) (compile-program "src/benchmarks/benchmarks.ss") (compile-whole-program "src/benchmarks/benchmarks.wpo" "src/benchmarks/benchmarks.so")' | scheme -q --compile-imported-libraries --libdirs src/mk:src/benchmarks --optimize-level 3
	@scheme --compile-imported-libraries --optimize-level 3 --program src/benchmarks/benchmarks.so | sed -E 's/#<time-duration ([[:digit:].]+)>/\1/g' | LC_COLLATE=C sort > benchmarks/bench
	@if [[ 1 < $$(ls -1 benchmarks | wc -l) ]]; then BENCHMARK=$$(ls -1v benchmarks | tail -n1); LC_COLLATE=C join -e0 -oauto -a1 -a2 -t$$'\t' benchmarks/$$BENCHMARK benchmarks/bench | awk -vOFS='\t' -F'\t' -vBENCHMARK=$$BENCHMARK 'BEGIN {print "benchmark",BENCHMARK,"current","% improvement","% > prev","slower?"} {if ($$2==0||$$3==0) {$$4="-"; $$5="-"} else {$$4=-100*($$3-$$2)/$$2" %"; $$5=$$2/$$3; $$5=($$2/$$3-1)*100; if($$5<0) $$6="x"} print}' | column -ts$$'\t'; else cat benchmarks/bench | column -ts$$'\t'; fi
	@cp benchmarks/bench benchmarks/bench-$$(ls -1v benchmarks | wc -l)

rebench:
# If you don't believe the numbers bench gave you, re-roll until your optimization wins!
	rm -f benchmarks/$$(ls -1v benchmarks | tail -n1)
	make bench

repl:
# Boot up a REPL preloaded with miniKanren
	scheme --libdirs src/mk src/repl/repl.ss

todo:
# Extract TODOs from source and build doc file
	echo '# Not Yet Implemented' > TODO.md
	grep -nr --exclude=utils.ss -e '(nyi' src | sed -E 's|^([^:]+):([^:]+):.*\(nyi([^)]*)\).*|- \3 ([\1:\2](https://github.com/emdonahue/aiKanren/blob/main/\1#L\2))|g' >> TODO.md
	echo '# TODO' >> TODO.md
	grep -nr -e 'TODO' src | sed -E 's|^([^:]+):([^:]+):.*TODO (.*)|- \3 ([\1:\2](https://github.com/emdonahue/aiKanren/blob/main/\1#L\2))|' >> TODO.md

test:
# Run unit tests
	make clean
	scheme --libdirs src/mk:src/tests:src/benchmarks:src/examples --script src/tests/all-tests.ss

debug:
# Run unit tests with debugging enabled
	scheme --debug-on-exception --compile-imported-libraries --libdirs src/mk:src/tests:src/benchmarks:src/examples --script src/tests/all-tests.ss # --import-notify
