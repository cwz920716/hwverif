

;(include-book "std/lists/top" :dir :system)

;(include-book "std/strings/top" :dir :system)

;(include-book "arithmetic/top-with-meta" :dir :system)

;(defun id-from-nat (s idx)
;  (declare (xargs :guard (and
;                          (symbolp s)
;                          (integerp idx))))
;  (intern$ (STRING-APPEND
;            (STRING-APPEND
;             (SYMBOL-NAME S)
;             "_")
;            (STR::NATSTR (NFIX IDX)))
;           "ACL2"))

;; bound will make any input integer p to be within interval [0, N)
(defun bound (p N)
  (declare (xargs :guard (and (integerp p)
                              (integerp N))))
  (if (< N 0)
      -1
    (if (< p 0)
        0
      (if (< p N)
          p
        (- N 1)))))

(defthm bound-type-ok (implies (and (integer-listp l)
                                    (consp l)
                                    (integerp x))
                               (integerp (nth (bound x (length l)) l))))

(defthm bound-ok (implies (and (< 0 N)
                               (integerp N)
                               (integerp x))
                          (and (integerp (bound x N))
                               (< (bound x N) N))))

(DEFTHM MEMBER-IF-BOUNDED
        (IMPLIES (AND (INTEGER-LISTP L)
                      (CONSP L)
                      (INTEGERP X)
                      (< X (LENGTH L)))
                 (MEMBER (NTH X L) L)))

(defthm bound-mem-ok (implies (and (integer-listp l)
                                   (consp l)
                                   (integerp x))
                              (member (nth (bound x (length l)) l) l)))

(defthm bound-mem-int (implies (and (integer-listp l)
                                    (consp l)
                                    (integerp x))
                               (integerp (nth (bound x (length l)) l))))

(defthm update-nth-buf-ok
    (implies (and (bufferp buf)
                  (integerp n1)
                  (integerp n2)
                  (<= 0 n1)
                  (< n1 (length buf)))
             (bufferp (update-nth n1 n2 buf))))
