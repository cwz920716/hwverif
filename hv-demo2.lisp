

; Class examples Feb 19, 2018
; Mertcan Temel

;; Problem 1 (proved)



(Defun nu-vec-gen (j N)
  (declare (xargs :measure (nfix (- N j))))
  (if (zp (- N j))
      nil
    (cons j
          (nu-vec-gen (1+ j) N))))


(defun ind2 (a j N)
  (if (zp a)
      nil
    (if (zp (- N j))
        nil
      (cons (+ N j a)
            (ind2 (1- a)
                  (1+ j)
                  N)))))


(defthm lemma-2
  (IMPLIES (AND (INTEGERP N)
              (<= 0 N)
              (INTEGERP J)
              (<= 0 J)
              (< 0 (+ (- J) N))
              (< J N)
              (CONSP (NU-VEC-GEN J N)))
           (EQUAL (CAR (NU-VEC-GEN J N)) J)))


(defthm nth-of-nu-vec-gen
 (implies (and (natp a)
               (natp N)
               (natp j)
               (< a (- N j))
               (< j N))
          (equal (nth a (nu-vec-gen j N))
                 (+ a j)))
 :hints (("Goal"
          :induct (ind2 a j N))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Problem 2 (proved)

; this is the first problem we tried but then switched to the one above.

; I defined the theorem
; nu-vec-gen2vs1, which basically replaces nu-vec-gen2 with nu-vec-gen and so
; the main theorem uses the theorem in Problem 1 to prove this one
; no induction needed as it does rewriting only.

(defun nu-vec-gen2 (N)
  (if (zp N)
      nil
    (app (nu-vec-gen2 (1- N))
         (list (1- N)))))




;disabled because we don't want (nu-vec-gen j N) to be rewritten everywhere.
(defthmd nu-vec-gen2vs1-lemma
  (implies (and (natp N)
                (natp j)
                (< j N))
           (equal  (nu-vec-gen j N)
                   (app (nu-vec-gen j (1- N))
                        (list (1- N))))))

(defthm nu-vec-gen2vs1
  (equal (nu-vec-gen2 N)
         (nu-vec-gen 0 N))
  :hints (("Goal"
           :in-theory (enable nu-vec-gen2vs1-lemma))))


;now proved:

(defthm nth-of-vec-gen2
 (implies (and (< a N)
               (natp N)
               (natp a))
          (equal (nth a (nu-vec-gen2 N))
                 a)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;Problem 3

;given the function:

(defun getevens (x)
  (declare (xargs :guard (true-listp x)))
  (if (atom x)
      nil
    (cons (car x)
          (getevens (cdr (cdr x))))))


;prove (no need to add new hypothesis):

(defthm nth-of-evens
  (implies (natp i)
           (equal (nth (* 2 i) x)
                  (nth i (getevens x)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;Problem 4

(defun vect+ (x y)
  (if (atom x)
      nil
    (if (atom y)
        nil
      (cons (+ (car x) (car y))
            (vect+ (cdr x) (cdr y))))))


; prove this theorem:

(defthm nth-of-vect+
  (IMPLIES (EQUAL (LEN X) (LEN Y))
           (EQUAL (FIX (NTH A (VECT+ X Y)))
                  (+ (FIX (NTH A X))
                     (FIX (NTH A Y))))))



;you can check the definition of "fix" by typing ":pe fix" in ACL2

;if you put this theorem into proof builder and then hit induct, you will see
;that ACL2 is smart enough this time to detect that it needs a modified
;induction scheme so no need to define a new function for the induction scheme


