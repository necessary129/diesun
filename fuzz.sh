#!/usr/bin/env bash

set -eu

mkdir -p tests2
mv tests/* tests2/ || true

cleanup () {
	rm tests/*
	mv tests2/* tests/
}
trap cleanup EXIT
trap "exit 0" SIGHUP
fuzz() {
	pid=$$
	testname="tests/var_test_zfuzz${pid}"
	while true; do
		echo '#lang racket' >"${testname}.rkt"
		racket fuzz-smith.rkt --max-depth 25 >>"${testname}.rkt"
		reads=$(grep -o '(read)' "${testname}.rkt" | wc -l)
		touch "${testname}.in"
		for _ in $(seq 1 "$reads"); do
			echo $RANDOM >>"${testname}.in"
		done
		res="$(racket ${testname}.rkt <${testname}.in)"
		echo "$(( ((res % 256) + 256) % 256 ))" >"${testname}.res"
		tail -n +2 "${testname}.rkt" >"${testname}1.rkt"
		rm "${testname}.rkt" && mv "${testname}1.rkt" "${testname}.rkt"
		racket fuzz-test.rkt 2>&1 | grep 'FAILURE' && break
		rm "${testname}.in"
	done
	echo "=== PROGRAM ==="
	cat "${testname}.rkt"
	echo "=== END PROGRAM ==="
	echo "=== INPUT ==="
	cat "${testname}.in"
	echo "=== END INPUT ==="
	echo "=== RES ==="
	cat "${testname}.res"
	echo "=== END RES ==="
	racket fuzz-test.rkt
	racket run-tests.rkt
	exit 1

}
fuzz
