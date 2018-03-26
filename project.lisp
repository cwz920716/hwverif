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

;; For now, we only support array indexing, excluding Func indexing

;; A legal expression can have following syntax in ACL2:
;; Expr = (<op> Expr Expr ...)  <op> can be anything like +/*/-/...
;; Expr = ([] <Buffer-or-Func> Expr)  1-d index
;; Expr = ([2] <Buffer-or-Func> Expr Expr)  2-d index (not-for-now)
;; Expr = <dimentional_identifier>
;; Expr = <const_number>

;; For milestone 0.1, we build an evaluator for halide expression.

(include-book "std/lists/top" :dir :system)

;; a buffer is an integer list which is non-empty
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

(defun []= (buf x val)
  (declare (xargs :guard (and (bufferp buf)
                              (integerp x)
                              (integerp val))))
  (update-nth (bound x (length buf)) val buf))

;; A context is a list which only supports (symbol.integer) or (symbol.buffer)
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

(defthm context-is-alist
  (implies (contextp ctx)
           (alistp ctx)))

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
             (alloca (and (consp args)
                          (atom (cdr args))
                          (natp arg1)))
             
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
        (alloca (repeat (ifix (expr-eval (car args) c)) 0))
        (otherwise 0)))))

(defun induct-rib (n)
  (if (or (<= n 1)
          (not (natp n)))
      t
    (induct-rib (- n 1))))

(DEFTHM REPEAT-IS-BUF
        (IMPLIES (AND (NATP N) (>= N 1))
                 (BUFFERP (REPEAT N 0)))
        :INSTRUCTIONS ((:INDUCT (INDUCT-RIB N))
                       :BASH (:DV 1)
                       (:DIVE 1)
                       :UP
                       :EXPAND :S
                       :TOP :EXPAND
                       :S :BASH))
                
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
        (alloca (cons fn (cons v1 arg1*)))
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

;; A halide IR is a C-like internal format:
;;   stmt = skip
;;          (skip)
;;        = stmt ;; stmt
;;          (begin stmt stmt)
;;        = malloc symbol size
;;          (malloc symbol nat)
;;        = for symbol form nat to nat stmt
;;          (for symbol nat nat stmt)
;;        = assign symbol index val
;;          ([]= symbol expr expr)

(defun stmtp (s)
  (declare (xargs :guard t))
  (if (atom s)
      nil
    (and (true-listp s)
         (let* ((com (car s))
                (args (cdr s))
                (s1 (car args))
                (s2 (cadr args))
                (s2* (cddr args))
                (s3 (car s2*))
                (s3* (cdr s2*))
                (s4 (car s3*))
                (s4* (cdr s3*)))
           (case com
             (skip (atom args))
             (begin (and (stmtp s1)
                         (stmtp s2)
                         (atom s2*)))
             (malloc (and (symbolp s1)
                          (natp s2)
                          (> s2 0)
                          (atom s2*)))
             (for (and (symbolp s1)
                       (natp s2)
                       (natp s3)
                       (stmtp s4)
                       (atom s4*)))
             ([]= (and (symbolp s1)
                       (exprp s2)
                       (exprp s3)
                       (atom s3*)))
             (otherwise nil))))))

(defthm context-put-ok
  (implies (and (symbolp name)
                (bufferp buf)
                (contextp ctx))
           (contextp (put-assoc name buf ctx))))
                
(defun exec-stmt (s ctx)
  (declare (xargs :guard (and (stmtp s)
                              (contextp ctx))))
  (if (atom s)
      ctx
    (let* ((com (car s))
                (args (cdr s))
                (s1 (car args))
                (s2 (cadr args))
                (s2* (cddr args))
                (s3 (car s2*))
                (s3* (cdr s2*))
                (s4 (car s3*))
                (s4* (cdr s3*)))
      (declare (ignore s3 s4 s4*))
      (case com
        (skip ctx)
        (begin (exec-stmt s2
                          (exec-stmt s1 ctx)))
        (malloc (put-assoc s1
                           (repeat s2 0)
                           ctx))
        ;; ignore []= for a bit
        ;; how to handle for?
        (otherwise ctx)))))
           
