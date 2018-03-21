;; Simplified Halide Lang
;; Author: Wenzhi Cui

;; A Halide Function has 3 components: a function name, a list of dimentional identifier
;; and a expression definition, e.g.,
;; blur_x(x, y) = (input(x-1, y) + input(x, y) + input(x+1, y)) / 3
;;
;; In the above example, the function name is blur_x, , dimentional identifer
;; list is '(x y), and the expression is what appeared on right hand side (RHS)
;; of the '=' sign. The exprssion is like a basic C expression which supports
;; arithmetics and "array indexing" operation. In theory, "array" can only be
;; applied to an acl2-array or list, or another well defined Halide function.
;; For the ease of explanation, we call a array or list of numbers as 'Buffer'
;; and a Halide Function as 'Func' 

;; A legal expression can have following syntax in ACL2:
;; Expr = (<op> Expr Expr ...)  <op> can be anything like +/*/-/...
;; Expr = ([] <Buffer-or-Func> Expr)  1-d index
;; Expr = ([2] <Buffer-or-Func> Expr Expr)  2-d index (not-for-now)
;; Expr = <dimentional_identifier>
;; Expr = <const_number>

;; For milestone 0.1, we build an evaluator for halide expression.

(defun bufferp (buf)
  (declare (xargs :guard t))
  (and (integer-listp buf)
       (< 0 (length buf))))

;; bound will make any input integer p to be within interval [0, N)
(defun bound (p N)
  (declare (xargs :guard (and (integerp p)
                              (natp N))))
  (if (< N 0)
      -1
    (if (< p 0)
        0
      (if (< p N)
          p
        (- N 1)))))

(defthm bound-type-ok (implies (and (integer-listp l)
                                    (> (length l) 0)
                                    (integerp x))
                               (integerp (nth (bound x (length l)) l))))

(defthm bound-ok (implies (and (< 0 N)
                               (natp N)
                               (integerp x))
                          (and (natp (bound x N))
                               (< (bound x N) N))))

(DEFTHM MEMBER-IF-BOUNDED
        (IMPLIES (AND (INTEGER-LISTP L)
                      (< 0 (LENGTH L))
                      (NATP X)
                      (< X (LENGTH L)))
                 (MEMBER (NTH X L) L)))

(defthm bound-mem-ok (implies (and (integer-listp l)
                                   (> (length l) 0)
                                   (integerp x))
                              (member (nth (bound x (length l)) l) l)))

(defun [] (buf x)
  (declare (xargs :guard (and (bufferp buf)
                              (integerp x))))
  (nth (bound x (length buf)) buf))
  
(defun contextp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (let ((pair (car x)))
      (and (consp pair)
           (symbolp (car pair))
           (or (integerp (cdr pair))
               (bufferp (cdr pair)))
           (contextp (cdr x))))))

(defun exprp (e)
  (declare (xargs :guard t))
  (if (atom e)
      (or (integerp e)
          (symbolp e))
    (and (true-listp e)
         (let* ((fn (car e))
                (args (cdr e))
                (arg1 (car args))
                (arg2 (cadr args)))
           (case fn
             (- (and (consp args)
                     (atom (cdr args))
                     (exprp arg1)))
             (+ (and (consp args)
                     (consp (cdr args))
                     (atom (cddr args))
                     (exprp arg1)
                     (exprp arg2)))
             (* (and (consp args)
                     (consp (cdr args))
                     (atom (cddr args))
                     (exprp arg1)
                     (exprp arg2)))
             ([] (and (consp args)
                      (consp (cdr args))
                      (atom (cddr args))
                      (symbolp arg1)
                      (exprp arg2)))
             (otherwise nil))
           ))
    ))

(defun expr-eval (e c)
  (declare (xargs :guard
                  (and (exprp e)
                       (contextp c))))
  (if (atom e)
      (if (symbolp e)
          (let ((r (cdr (assoc e c))))
            (if (bufferp r)
                r
              (ifix r)))
        (ifix e))
    (let ((fn (car e))
          (args (cdr e)))
      (case fn
        (- (- (ifix (expr-eval (car args) c))))
        (+ (+ (ifix (expr-eval (car args) c))
              (ifix (expr-eval (cadr args) c))))
        (* (* (ifix (expr-eval (car args) c))
              (ifix (expr-eval (cadr args) c))))
        ([] (let ((buf (expr-eval (car args) c)))
              (if (bufferp buf)
                  ([] buf (ifix (expr-eval (cadr args) c)))
                (ifix buf))))
        (otherwise 0)))))
                  

(defun constant-fold (e)
  (declare (xargs
            :guard (exprp e))
            ;; :measure (...)
           )
  (if (atom e)
      e
    (let* ((fn (car e))
           (args (cdr e))
           (arg1 (car args))
           (arg1* (cdr args))
           (arg2 (cadr args))
           (arg2* (cddr args))
           (v1 (constant-fold arg1))
           (v2 (constant-fold arg2)))
      (case fn
        (- (if (integerp v1) (- v1) (cons fn (cons v1 arg1*))))
        (+ (if (and (integerp v1)
                    (integerp v2))
               (+ v1 v2)
             (cons fn (cons v1 (cons v2 arg2*)))))
        (* (if (and (integerp v1)
                    (integerp v2))
               (* v1 v2)
             (cons fn (cons v1 (cons v2 arg2*)))))
        ([] (cons fn (cons v1 (cons v2 arg2*))))
        (otherwise e)))))

(defthm constant-fold-expr (implies (exprp e)
                                    (exprp (constant-fold e))))

(defthm constant-fold-is-correct
  (implies (and (exprp e)
                (contextp a))
           (equal (expr-eval (constant-fold e) a)
                  (expr-eval e a))))

;; A halide program has three components: A symbolic name, a symblic list for
;; dimentional vars, and a expression for pure definition
(defun halidep (e)
  (declare (xargs :guard t))
  (and (consp e)
       (consp (car e))
       (symbolp (caar e))
       (symbol-listp (cdar e))
       (> (len (cdar e)) 0)
       (exprp (cdr e))))

(defun halide-1dp (e)
  (declare (xargs :guard t))
  (and (consp e)
       (consp (car e))
       (symbolp (caar e))
       (symbol-listp (cdar e))
       (= (len (cdar e)) 1)
       (exprp (cdr e))))

(defun halide-funcname (e)
  (declare (xargs :guard (halidep e)))
  (caar e))

(defun halide-dims (e)
  (declare (xargs :guard (halidep e)))
  (cdar e))

(defun halide-expr (e)
  (declare (xargs :guard (halidep e)))
  (cdr e))

;; Above looks good

(defun realize-at-1d (e id ctx)
  (declare (xargs :guard (and (natp id)
                              (halide-1dp e)
                              (contextp ctx))))
  (let* ((dim0 (car (halide-dims e)))
         (rhs (halide-expr e))
         (idp (cons dim0 id)))
    (ifix (expr-eval rhs (cons idp ctx)))))

(assert-event (equal 3
                     (realize-at-1d (cons '(f x)
                                          '(+ x (* x 2)))
                                    1 nil)))

(assert-event (equal 63
                     (realize-at-1d (cons '(f x)
                                          '(* x (+ x 2)))
                                    7 nil)))

(assert-event (equal 5
                     (realize-at-1d (cons '(f x)
                                          '([] input x))
                                    4
                                    (cons '(input 1 1 2 3 5 8 13)
                                          nil)
                                    )))

(defthm realize-type-correct
  (implies (and (halidep e)
                (natp i)
                (contextp ctx))
           (integerp (realize-at-1d e i ctx))))

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

(defun induct-risz (n)
  (if (zp n)
      0
    (1+ (induct-risz (1- n)))))

(defthm realize-inner-size-good
  (implies (and (halide-1dp e)
                (natp N)
                (natp i)
                (contextp ctx))
           (equal (len (realize-1d-inner e N i ctx))
                  N))
  :hints (("Goal"
           :induct (induct-risz N)))
  )

(defthm realize-size-good
  (implies (and (halide-1dp e)
                (natp N)
                (contextp ctx))
           (equal (len (realize-1d e N ctx))
                  N)))
