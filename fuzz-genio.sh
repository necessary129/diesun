#!/usr/bin/env bash
testname=$1
reads=$(grep -o '(read)' "${testname}.rkt" | wc -l)
touch "${testname}.in"
for _ in $(seq 1 "$reads"); do
	echo $RANDOM >>"${testname}.in"
done
echo "#lang racket" > "${testname}1.rkt"
cat "${testname}.rkt" >> "${testname}1.rkt"
res="$(racket ${testname}1.rkt <${testname}.in)"
case $res in
"#f") reso="#f" ;;
"#t") reso="#t" ;;
*) reso="$((((res % 256) + 256) % 256))" ;;
esac
echo "$reso" >"${testname}.res"
rm "${testname}1.rkt"
