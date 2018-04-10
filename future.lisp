

(DEFTHM
 BUF-DECLARED-AFTER-SIM-1D-UPDATE-HELPER1
 (IMPLIES
   (AND (CONSP E)
        (CONSP (CAR E))
        (SYMBOLP (CAR (CAR E)))
        (SYMBOLP (CADR (CAR E)))
        (NOT (CDDR (CAR E)))
        (CONSP (CDR (CAR E)))
        (EXPRP (CDR E))
        (NOT-USE-SYMBOL (CDR E) (CAR (CAR E)))
        (CONTEXTP CTX)
        (CONSP (ASSOC-EQUAL (CAR (CAR E)) CTX))
        (CONSP (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX)))
        (INTEGER-LISTP (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX)))
        (CONSP (ASSOC-EQUAL (CADR (CAR E)) CTX))
        (INTEGERP (CDR (ASSOC-EQUAL (CADR (CAR E)) CTX)))
        (< (CDR (ASSOC-EQUAL (CADR (CAR E)) CTX))
           0))
   (CONSP (ASSOC-EQUAL (CAR (CAR E))
                       (PUT-ASSOC-EQUAL (CAR (CAR E))
                                        (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX))
                                        CTX))))
 :INSTRUCTIONS (:PROVE))

(DEFTHM
 BUF-DECLARED-AFTER-SIM-1D-UPDATE-HELPER2
 (IMPLIES
  (AND (CONSP E)
       (CONSP (CAR E))
       (SYMBOLP (CAR (CAR E)))
       (SYMBOLP (CADR (CAR E)))
       (NOT (CDDR (CAR E)))
       (CONSP (CDR (CAR E)))
       (EXPRP (CDR E))
       (NOT-USE-SYMBOL (CDR E) (CAR (CAR E)))
       (CONTEXTP CTX)
       (CONSP (ASSOC-EQUAL (CAR (CAR E)) CTX))
       (CONSP (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX)))
       (INTEGER-LISTP (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX)))
       (CONSP (ASSOC-EQUAL (CADR (CAR E)) CTX))
       (INTEGERP (CDR (ASSOC-EQUAL (CADR (CAR E)) CTX)))
       (< (CDR (ASSOC-EQUAL (CADR (CAR E)) CTX))
          0))
  (CONSP
     (CDR (ASSOC-EQUAL (CAR (CAR E))
                       (PUT-ASSOC-EQUAL (CAR (CAR E))
                                        (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX))
                                        CTX)))))
 
(DEFTHM
 BUF-DECLARED-AFTER-SIM-1D-UPDATE-HELPER3
 (IMPLIES
  (AND (CONSP E)
       (CONSP (CAR E))
       (SYMBOLP (CAR (CAR E)))
       (SYMBOLP (CADR (CAR E)))
       (NOT (CDDR (CAR E)))
       (CONSP (CDR (CAR E)))
       (EXPRP (CDR E))
       (NOT-USE-SYMBOL (CDR E) (CAR (CAR E)))
       (CONTEXTP CTX)
       (CONSP (ASSOC-EQUAL (CAR (CAR E)) CTX))
       (CONSP (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX)))
       (INTEGER-LISTP (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX)))
       (CONSP (ASSOC-EQUAL (CADR (CAR E)) CTX))
       (INTEGERP (CDR (ASSOC-EQUAL (CADR (CAR E)) CTX)))
       (< (CDR (ASSOC-EQUAL (CADR (CAR E)) CTX))
          0))
  (INTEGER-LISTP
     (CDR (ASSOC-EQUAL (CAR (CAR E))
                       (PUT-ASSOC-EQUAL (CAR (CAR E))
                                        (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX))
                                        CTX)))))
 :INSTRUCTIONS (:PROVE))

(DEFTHM
 BUF-DECLARED-AFTER-SIM-1D-UPDATE-HELPER1
 (IMPLIES
   (AND (CONSP E)
        (CONSP (CAR E))
        (SYMBOLP (CAR (CAR E)))
        (SYMBOL-LISTP (CDR (CAR E)))
        (EQUAL (LEN (CDR (CAR E))) 1)
        (NOT (EQUAL (CAR (CAR E)) (CADR (CAR E))))
        (EXPRP (CDR E))
        (CONTEXTP CTX)
        (CONSP (ASSOC-EQUAL (CAR (CAR E)) CTX))
        (INTEGER-LISTP (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX)))
        (< 0
           (LEN (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX))))
        (CONSP (ASSOC-EQUAL (CADR (CAR E)) CTX))
        (INTEGERP (CDR (ASSOC-EQUAL (CADR (CAR E)) CTX)))
        (< (CDR (ASSOC-EQUAL (CADR (CAR E)) CTX))
           0))
   (CONSP (ASSOC-EQUAL (CAR (CAR E))
                       (PUT-ASSOC-EQUAL (CAR (CAR E))
                                        (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX))
                                        CTX))))
 :INSTRUCTIONS (:PROVE))

(DEFTHM
 BUF-DECLARED-AFTER-SIM-1D-UPDATE-HELPER2
 (IMPLIES
  (AND (CONSP E)
       (CONSP (CAR E))
       (SYMBOLP (CAR (CAR E)))
       (SYMBOL-LISTP (CDR (CAR E)))
       (EQUAL (LEN (CDR (CAR E))) 1)
       (NOT (EQUAL (CAR (CAR E)) (CADR (CAR E))))
       (EXPRP (CDR E))
       (CONTEXTP CTX)
       (CONSP (ASSOC-EQUAL (CAR (CAR E)) CTX))
       (INTEGER-LISTP (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX)))
       (< 0
          (LEN (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX))))
       (CONSP (ASSOC-EQUAL (CADR (CAR E)) CTX))
       (INTEGERP (CDR (ASSOC-EQUAL (CADR (CAR E)) CTX)))
       (< (CDR (ASSOC-EQUAL (CADR (CAR E)) CTX))
          0))
  (INTEGER-LISTP
     (CDR (ASSOC-EQUAL (CAR (CAR E))
                       (PUT-ASSOC-EQUAL (CAR (CAR E))
                                        (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX))
                                        CTX)))))
 :INSTRUCTIONS (:PROVE))

(defthm buf-declared-after-sim-1d-update
  (implies (and (halide-1dp e)
                (contextp ctx)
                (declared-buf (halide-funcname e) ctx)
                (declared-int (car (halide-dims e)) ctx))
           (declared-buf (halide-funcname e)
                         (simulate-1d-update e ctx)))
  :hints (("Goal"
           :do-not-induct t)))

(defthm buf-declared-after-sim-1d-update-put-int
  (implies (and (halide-1dp e)
                (contextp ctx)
                (integerp n)
                (declared-buf (halide-funcname e) ctx)
                (equal ctx2
                       (put-assoc (halide-dim0 e) n ctx))
                )
           (declared-buf (halide-funcname e)
                         (simulate-1d-update e ctx2)))
  :hints (("Goal" :do-not-induct t)))



(defthm simulate-1d-for-helper1
  (implies (and (halide-1dp e)
                (contextp ctx)
                (integerp n)
                (declared-buf (halide-funcname e) ctx))
           (declared-buf (halide-funcname e)
                         (delete-assoc (car (halide-dims e))
                                       (simulate-1d-update
                                        e (put-assoc (car (halide-dims e))
                                                     n ctx)))))
  :hints (("Goal" :do-not-induct t)))

(defthm simulate-1d-for-type-ok
  (implies (and (natp base)
                (natp extent)
                (contextp ctx)
                (declared-buf (halide-funcname e) ctx)
                (halide-1dp e))
           (contextp (simulate-1d-for e base extent ctx))))
