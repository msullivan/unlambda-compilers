#!/bin/bash

N=${1:-200}

measure() {
    compiler=$1
    mode=$2
    shift 2

    start_time=$EPOCHREALTIME
    $* ../unlambda-2.0.0/CUAN/prime_numbers.unl | head -n$N > /dev/null
    end_time=$EPOCHREALTIME

    elapsed=$(python3 -c "print($end_time - $start_time)")
    if [ -z "$baseline" ]; then
        baseline=$elapsed
    fi
    if [ "$last_compiler"x != "$compiler"x ]; then
        compiler_baseline=$elapsed
        last_compiler=$compiler
    fi
    ratio=$(python3 -c "print($elapsed / $baseline)")
    compiler_ratio=$(python3 -c "print($elapsed / $compiler_baseline)")
    printf "%s,%s,%d,%0.3f,%0.3f,%0.3f\n" $mode $compiler $N $elapsed $ratio $compiler_ratio

}

for COMPILER in smlnj mlton; do
    for MODE in interp-unlambda sml-delay sml-cps sml-case; do
        measure $COMPILER $MODE ./unlambda-$COMPILER --$MODE
    done
done

measure rustc relambda ../relambda/target/release/main 2>/dev/null
measure gcc irori-unlambda ../irori-unlambda/unlambda
measure gcc c-refcnt ../unlambda-2.0.0/c-refcnt/unlambda.linux
