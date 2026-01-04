LEAN_NUM_THREADS ?= 12

.PHONY: build verify clean report

build:
	LEAN_NUM_THREADS=$(LEAN_NUM_THREADS) lake build TzimtzumV2 --old 2>&1 | tee build.log

verify:
	LEAN_NUM_THREADS=$(LEAN_NUM_THREADS) lake build TzimtzumV2 2>&1 | tee build.log

report: build
	@python3 verify_report.py < build.log | tee verification-report.md

clean:
	lake clean
