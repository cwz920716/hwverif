
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


