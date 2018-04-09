

(DEFTHM STMT-IS-CONS
        (IMPLIES (STMTP S) (CONSP S))
        :INSTRUCTIONS (:PROMOTE :INDUCT :S))

(DEFTHM CAR-STMT-OK
        (IMPLIES (AND (STMTP S9)
                      (NOT (EQUAL (CAR S9) 'SKIP))
                      (NOT (EQUAL (CAR S9) 'BEGIN))
                      (NOT (EQUAL (CAR S9) 'MALLOC))
                      (NOT (EQUAL (CAR S9) 'FOR)))
                 (EQUAL (CAR S9) '[]=))
        :INSTRUCTIONS (:PROMOTE :INDUCT :S :S :S))

(defthm stmt-measure-pos
  (implies (stmtp s)
           (and (integerp (stmt-measure s))
                (> (stmt-measure s) 0))))
