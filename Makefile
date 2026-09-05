all:
	lake build

test:
	lake test

# The slow examples, one process each so the kernel reports the peak
# memory of each; a file's imports are checked again as part of it.
SLOW = Bench BenchDeep BenchBrunerie BenchHope Hope Pi4S3

bench: all
	for f in $(SLOW); do \
	  /usr/bin/time -f "$$f: %e s wall, %U s user, %M KB peak" \
	    .lake/build/bin/kleenextt check examples/$$f.ktt || exit 1; \
	done

.PHONY: all test bench
