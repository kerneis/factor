! Copyright (C) 2003, 2009 Slava Pestov.
! See http://factorcode.org/license.txt for BSD license.
USING: system kernel math io prettyprint tools.memory
tools.dispatch ;
IN: tools.time

: benchmark ( quot -- runtime )
    nano-count [ call nano-count ] dip - ; inline

: time. ( time -- )
    "Running time: " write 1000000000 /f pprint " seconds" print ;

: time-banner. ( -- )
    "Additional information was collected." print
    "dispatch-stats.  - Print method dispatch statistics" print
    "gc-events.       - Print all garbage collection events" print
    "gc-stats.        - Print breakdown of different garbage collection events" print
    "gc-summary.      - Print aggregate garbage collection statistics" print ;

: time ( quot -- )
    [ [ benchmark ] collect-dispatch-stats ] collect-gc-events
    time. nl time-banner. ; inline
