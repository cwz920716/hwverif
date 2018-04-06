

(defthm simulate-1d-for-helper--3
(IMPLIES
   (AND (CONSP E)
        (CONSP (CAR E))
        (SYMBOLP (CAR (CAR E)))
        (SYMBOL-LISTP (CDR (CAR E)))
        (EQUAL (LEN (CDR (CAR E))) 1)
        (NOT (EQUAL (CAR (CAR E)) (CADR (CAR E))))
        (EXPRP (CDR E))
        (CONTEXTP CTX)
        (INTEGERP N)
        (CONSP (ASSOC-EQUAL (CAR (CAR E)) CTX))
        (INTEGER-LISTP (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX)))
        (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX))
        (NOT (INTEGER-LISTP (CDR (ASSOC-EQUAL (CAR (CAR E))
                                              (PUT-ASSOC-EQUAL (CADR (CAR E))
                                                               N CTX))))))
   (INTEGER-LISTP
        (CDR (ASSOC-EQUAL (CAR (CAR E))
                          (DELETE-ASSOC-EQUAL (CADR (CAR E))
                                              (PUT-ASSOC-EQUAL (CADR (CAR E))
                                                               N CTX)))))))

(defthm simulate-1d-for-helper--2
(IMPLIES
   (AND (CONSP E)
        (CONSP (CAR E))
        (SYMBOLP (CAR (CAR E)))
        (SYMBOL-LISTP (CDR (CAR E)))
        (EQUAL (LEN (CDR (CAR E))) 1)
        (NOT (EQUAL (CAR (CAR E)) (CADR (CAR E))))
        (EXPRP (CDR E))
        (CONTEXTP CTX)
        (INTEGERP N)
        (CONSP (ASSOC-EQUAL (CAR (CAR E)) CTX))
        (INTEGER-LISTP (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX)))
        (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX))
        (NOT (INTEGER-LISTP (CDR (ASSOC-EQUAL (CAR (CAR E))
                                              (PUT-ASSOC-EQUAL (CADR (CAR E))
                                                               N CTX))))))
   (CONSP (ASSOC-EQUAL (CAR (CAR E))
                       (DELETE-ASSOC-EQUAL (CADR (CAR E))
                                           (PUT-ASSOC-EQUAL (CADR (CAR E))
                                                            N CTX))))))


(defthm simulate-1d-for-helper--1
(IMPLIES (AND (CONSP E)
              (CONSP (CAR E))
              (SYMBOLP (CAR (CAR E)))
              (SYMBOL-LISTP (CDR (CAR E)))
              (EQUAL (LEN (CDR (CAR E))) 1)
              (NOT (EQUAL (CAR (CAR E)) (CADR (CAR E))))
              (EXPRP (CDR E))
              (CONTEXTP CTX)
              (INTEGERP N)
              (CONSP (ASSOC-EQUAL (CAR (CAR E)) CTX))
              (INTEGER-LISTP (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX)))
              (CDR (ASSOC-EQUAL (CAR (CAR E)) CTX)))
         (CONSP (ASSOC-EQUAL (CADR (CAR E))
                             (PUT-ASSOC-EQUAL (CADR (CAR E))
                                              N CTX)))))


(defun realize-1d-inner (e size id ctx)
  (declare (xargs :guard (and (halide-1dp e)
                              (natp size)
                              (natp id)
                              (contextp ctx))))
  (if (zp size)
      nil
    (cons (realize-at-1d e id ctx)
          (realize-1d-inner e (1- size) (1+ id) ctx))))

(defun realize-1d (e size ctx)
  (declare (xargs :guard (and (halide-1dp e)
                              (natp size)
                              (contextp ctx))))
  (realize-1d-inner e size 0 ctx))


(include-book "arithmetic/top-with-meta" :dir :system)

(include-book "std/basic/arith-equivs" :dir :system)

(local (in-theory (enable* arith-equiv-forwarding)))


;; (defthm non-stmt-measure-zp
;;   (implies (not (stmtp s))
;;            (zp (stmt-m s))))

(defthm plus-le-comm
  (implies (and (natp a)
                (natp b)
                (natp x)
                (natp y)
                (<= a x)
                (<= b y))
           (<= (+ a b)
               (+ x y))))

(defthm lt-le-comm
  (implies (and (natp x)
                (natp y)
                (natp z)
                (< x y)
                (<= y z))
           (< x
              z)))

(defthm le-implies-lt-1
  (implies (and (natp x)
                (natp y)
                (<= x y))
           (< x (+ 1 y))))

(defthm a-le-ca
  (implies (and (natp a)
                (natp c)
                (< 0 c))
           (<= a
               (* c a))))

(defthm stmt-measure-helper-1
 (implies (and (natp a)
               (natp b)
               (natp c)
               (< 0 c))
          (< (+ a b)
             (+ 1
                (* c a)
                (* c b)))))

(defthm le-lt-comm
  (implies (and (natp x)
                (natp y)
                (natp z)
                (<= x y)
                (< y z))
           (< x
              z)))

(defthm stmt-measure-helper-2
 (implies (and (natp a)
               (natp b)
               (natp c)
               (< 0 c))
          (<= (+ 1
                 (* c a)
                 (* c b))
              (+ c
                 (* c a)
                 (* c b)))))

(defthm stmt-measure-helper-3
 (implies (and (natp a)
               (natp b)
               (natp c)
               (< 0 c))
          (<= (* a b)
              (* c a b))))

(defthm stmt-measure-helper-4
 (implies (and (natp a)
               (natp b)
               (natp c)
               (< 0 c))
          (< (* a b c)
              (+ c
                 (* c a b)))))

(DEFTHM STMT-MEASURE-HELPER-5
        (IMPLIES (AND (NATP A) (NATP B) (NATP C) (< 0 C))
                 (< (* A B) (+ C (* C A B))))
        :INSTRUCTIONS ((:USE (:INSTANCE LE-LT-COMM (X (* A B))
                                        (Y (* C A B))
                                        (Z (+ C (* C A B)))))
                       :PROVE))


