

(DEFTHM
 MAIN-HELPER1
 (IMPLIES
   (AND (CONTEXTP CTX)
        (INTEGERP B)
        (HALIDE-1DP E))
   (CONTEXTP
        (DELETE-CTX (HALIDE-DIM0 E)
                    (SIMULATE-1D-UPDATE E (PUT-CTX (HALIDE-DIM0 E) B CTX)))))
 :INSTRUCTIONS (:PROVE))

(defthm test
 (IMPLIES
  (AND (DECLARED-BUF (HALIDE-FUNCNAME E) CTX)
       (CONTEXTP CTX)
       (NATP EXTENT)
       (INTEGERP BASE)
       (HALIDE-1DP E)
       (NOT (ZP EXTENT)))
  (LET
   ((DIM0 (CAR (HALIDE-DIMS E))))
   (AND
    (LET ((NAME DIM0) (VAL BASE) (ALIST CTX))
         (AND (OR (NOT (EQLABLEP NAME))
                  (ALISTP ALIST))
              (OR (EQLABLEP NAME)
                  (EQLABLE-ALISTP ALIST))
              (EQUAL (PUT-ASSOC-EQUAL NAME VAL ALIST)
                     (PUT-ASSOC-EQL-EXEC NAME VAL ALIST))))
    (LET
     ((CTX-I (PUT-ASSOC-EQUAL DIM0 BASE CTX)))
     (AND
      (ACL2-NUMBERP BASE)
      (LET
       ((BASE-1I (+ BASE 1)))
       (AND
        (ACL2-NUMBERP EXTENT)
        (LET
         ((EXTENT-1I (+ -1 EXTENT)))
         (AND
          (HALIDE-1DP E)
          (DECLARED-BUF (HALIDE-FUNCNAME E) CTX-I)
          (CONTEXTP CTX-I)
          (DECLARED-INT (HALIDE-DIM0 E) CTX-I)
          (LET ((KEY DIM0)
                (ALIST (SIMULATE-1D-UPDATE E CTX-I)))
               (AND (OR (NOT (EQLABLEP KEY)) (ALISTP ALIST))
                    (OR (EQLABLEP KEY)
                        (EQLABLE-ALISTP ALIST))
                    (EQUAL (DELETE-ASSOC-EQUAL KEY ALIST)
                           (DELETE-ASSOC-EQL-EXEC KEY ALIST))))
          (LET
            ((CTX-1I (DELETE-ASSOC-EQUAL DIM0 (SIMULATE-1D-UPDATE E CTX-I))))
            (AND (HALIDE-1DP E)
                 (DECLARED-BUF (HALIDE-FUNCNAME E)
                               CTX-1I)
                 (NATP EXTENT-1I)
                 (INTEGERP BASE-1I)
                 (CONTEXTP CTX-1I))))))))))))
  )

(verify-guards simulate-1d-for
              :hints (("Goal" :do-not-induct t)))

(DEFTHM
 CONTEXTP-SIMULATE-1D-FOR
 (IMPLIES (AND (INTEGERP BASE)
               (INTEGERP EXTENT)
               (CONTEXTP CTX)
               (DECLARED-BUF (HALIDE-FUNCNAME E) CTX)
               (HALIDE-1DP E))
          (CONTEXTP (SIMULATE-1D-FOR E BASE EXTENT CTX)))
 :INSTRUCTIONS
 (:INDUCT
  :PROMOTE (:DEMOTE 2)
  (:DIVE 2 1)
  :EXPAND :S-PROP :TOP
  (:CLAIM
    (CONTEXTP (DELETE-ASSOC-EQUAL
                   (CAR (HALIDE-DIMS E))
                   (SIMULATE-1D-UPDATE E
                                       (PUT-ASSOC-EQUAL (CAR (HALIDE-DIMS E))
                                                        BASE CTX)))))
  (:USE (:INSTANCE BUF-DECLARED-AFTER-PUT-SIM-DEL (E E)
                   (CTX CTX)
                   (BASE BASE)))
  :PROMOTE (:DEMOTE 1)
  (:DIVE 1)
  (:DIVE 2)
  :S-PROP :TOP
  :BASH :BASH))

(defthm contextp-after-put-sim-del
  (implies (and (contextp ctx)
                (halide-1dp e)
                (integerp base)
                (declared-buf (halide-funcname e) ctx)
                )
           (contextp (delete-ctx
                      (halide-dim0 e)
                      (simulate-1d-update
                       e
                       (put-ctx (halide-dim0 e)
                                  base
                                  ctx))))))

(defthm contextp-after-sim-1d-update
  (implies (and (halide-1dp e)
                (contextp ctx)
                )
           (contextp (simulate-1d-update e ctx)))
  :hints (("Goal"
           :do-not-induct t)))

(defthm buf-declared-after-sim-1d-update
  (implies (and (halide-1dp e)
                (contextp ctx)
                (declared-buf (halide-funcname e) ctx)
                )
           (declared-buf (halide-funcname e)
                         (simulate-1d-update e ctx)))
  :hints (("Goal"
           :do-not-induct t)))

(DEFTHM
 BUF-DECLARED-AFTER-PUT-SIM-DEL
 (IMPLIES
  (AND (HALIDE-1DP E)
       (CONTEXTP CTX)
       (DECLARED-BUF (HALIDE-FUNCNAME E) CTX)
       (INTEGERP BASE))
  (DECLARED-BUF
   (HALIDE-FUNCNAME E)
   (DELETE-ASSOC (HALIDE-DIM0 E)
                 (SIMULATE-1D-UPDATE E
                                     (PUT-ASSOC (HALIDE-DIM0 E) BASE CTX))))))

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
