! Copyright (C) 2013 Doug Coleman.
! See http://factorcode.org/license.txt for BSD license.
USING: kernel locals sequences sets ;
IN: sets.extras

: setwise-xor ( seq1 seq2 -- set )
    [ append members ] [ intersect ] 2bi diff ;

: symmetric-diff ( set1 set2 -- set )
    [ union ] [ intersect ] 2bi diff ;

: proper-subset? ( set1 set2 -- ? )
    2dup subset? [ swap subset? not ] [ 2drop f ] if ;

: superset? ( set1 set2 -- ? )
    swap subset? ;

: disjoint? ( set1 set2 -- ? )
    intersects? not ;

:: non-repeating ( seq -- seq' )
    HS{ } clone :> visited
    0 seq new-resizable :> accum
    seq [
        accum over visited ?adjoin
        [ push ] [ remove! drop ] if
    ] each accum seq like ;
