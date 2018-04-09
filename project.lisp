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

;; a buffer is an integer list which is non-empty
(defun bufferp (buf)
  (declare (xargs :guard t))
  (and (consp buf)
       (integer-listp buf)))

(local (include-book "std/lists/repeat" :dir :system))

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

#||
(defun bufferp (buf)
  (declare (xargs :guard t))
  (and (integer-listp buf)
       (< 0 (length buf))))

(defthm buf-not-nil
  (implies (bufferp buf)
           (not (atom buf))))
||#


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
  (if (and (<= 0 x)
           (< x (length buf)))
      (update-nth x val buf)
    buf))

(defthm update-buf-ok
    (implies (and (bufferp buf)
                  (integerp n1)
                  (integerp n2))
             (bufferp ([]= buf n1 n2))))

(defthm update-buf-ok-2
    (implies (and (bufferp buf)
                  (integerp n1)
                  (integerp n2)
                  (<= 0 n1)
                  (< n1 (length buf)))
             (bufferp (update-nth n1 n2 buf))))
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

(defthm context-put-buf-ok
  (implies (and (symbolp name)
                (bufferp buf)
                (contextp ctx))
           (contextp (put-assoc name buf ctx))))

(defthm context-put-nat-ok
  (implies (and (symbolp name)
                (natp n)
                (contextp ctx))
           (contextp (put-assoc name n ctx))))

(defthm context-del-ok
  (implies (and (symbolp name)
                (contextp ctx))
           (contextp (delete-assoc name ctx))))

(defun declared-buf (sym ctx)
  (declare (xargs :guard (and (symbolp sym)
                              (contextp ctx))))
  (let ((sa (assoc sym ctx)))
    (and (consp sa)
         (bufferp (cdr sa)))))

(defun declared-int (sym ctx)
  (declare (xargs :guard (and (symbolp sym)
                              (contextp ctx))))
  (let ((sa (assoc sym ctx)))
    (and (consp sa)
         (integerp (cdr sa)))))

(defthm buf-declared-after-update-idx
  (implies (and (contextp ctx)
                (symbolp dim0)
                (symbolp fname)
                (not (equal fname dim0))
                (declared-int dim0 ctx)
                (integerp dim0)
                (declared-buf fname ctx))
           (declared-buf fname (put-assoc dim0 idx ctx))))

(defthm buf-declared-after-delete-idx
  (implies (and (contextp ctx)
                (symbolp dim0)
                (symbolp fname)
                (not (equal fname dim0))
                (declared-int dim0 ctx)
                (integerp dim0)
                (declared-buf fname ctx))
           (declared-buf fname (delete-assoc dim0 ctx))))

(defthm buf-declared-after-put-buf
  (implies (and (contextp ctx)
                (symbolp fname)
                (bufferp buf))
           (declared-buf fname (put-assoc fname buf ctx))))

(defthm int-declared-after-put-int
  (implies (and (contextp ctx)
                (symbolp dim0)
                (integerp n))
           (declared-int dim0 (put-assoc dim0 n ctx))))

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
                          (natp arg1)
                          (< 0 arg1)))             
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
       (not (equal (caar e)
                   (car (cdar e))))
       (exprp (cdr e))))

(defun halide-funcname (e)
  (declare (xargs :guard (halidep e)))
  (caar e))

(defun halide-dims (e)
  (declare (xargs :guard (halidep e)))
  (cdar e))

(defun halide-dim0 (e)
  (declare (xargs :guard (halidep e)))
  (car (halide-dims e)))

(defun halide-expr (e)
  (declare (xargs :guard (halidep e)))
  (cdr e))

(defun simulate-1d-update (e ctx)
  (declare (xargs :guard (and (halide-1dp e)
                              (contextp ctx)
                              (declared-buf (halide-funcname e) ctx)
                              (declared-int (car (halide-dims e)) ctx)
                              )))
  (let* ((fname (halide-funcname e))
         (dim0 (car (halide-dims e)))
         (buf (cdr (assoc fname ctx)))
         (idx (cdr (assoc dim0 ctx))))
    (if (and (bufferp buf)
             (integerp idx))
        (put-assoc fname
                   ([]= buf
                        (ifix idx)
                        (ifix (expr-eval (halide-expr e) ctx)))
                   ctx)
      ctx)))

(defun simulate-1d-for (e base extent ctx)
  (declare (xargs :guard (and (integerp base)
                              (natp extent)
                              (contextp ctx)
                              (declared-buf (halide-funcname e) ctx)
                              (halide-1dp e))
                  :verify-guards nil
                  ))
  (if (zp extent)
      ctx
    (let* ((dim0 (car (halide-dims e)))
           (ctx-i (put-assoc dim0 base ctx))
           (base-1i (+ base 1))
           (extent-1i (1- extent))
           (ctx-1i (delete-assoc dim0
                                 (simulate-1d-update e ctx-i))))
      (simulate-1d-for e base-1i extent-1i ctx-1i))))

(defun simulate-1d (e base size ctx)
  (declare (xargs :guard (and (halide-1dp e)
                              (natp size)
                              (natp base)
                              (< 0 size)
                              (contextp ctx))
                  :verify-guards nil))
  (let* ((ctx-init (put-assoc (halide-funcname e)
                              (repeat size 0)
                              ctx)))
    (simulate-1d-for e base size ctx-init)))

;; A halide IR is a C-like internal format:
;;   stmt = skip
;;          (skip)
;;        = stmt ;; stmt
;;          (begin stmt stmt)
;;        = symbol = malloc(size)
;;          (malloc symbol nat)
;;        = for (int symbol = nat1; symbol = nat1 + nat2; symbol++) {
;;              stmt
;;          }
;;          (for symbol nat1 nat2 stmt)
;;        = symbol[index] = val
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

(defun stmt-measure (s)
  (if (atom s)
      0
    (let* ((com (car s))
                (args (cdr s))
                (s1 (car args))
                (s2 (cadr args))
                (s2* (cddr args))
                (s3 (car s2*))
                (s3* (cdr s2*))
                (s4 (car s3*))
                (s4* (cdr s3*)))
      (declare (ignore s4*))
      (case com
        (skip 1)
        (begin (+ 1
                  (stmt-measure s1)
                  (stmt-measure s2)))
        (malloc 1)
        (for (+ 1
                (nfix s3)
                (stmt-measure s4)
                (* (nfix s3) (stmt-measure s4))))
        ([]= (+ 1
                (stmt-measure (car s))
                (stmt-measure (cdr s))))
        (otherwise  (+ 1
                       (stmt-measure (car s))
                       (stmt-measure (cdr s))))
        ))))

(defthm stmt-measure-pos
  (implies (stmtp s)
           (and (integerp (stmt-measure s))
                (> (stmt-measure s) 0))))

(defun exec-stmt (s ctx)
  (declare (xargs :guard (and (stmtp s) (contextp ctx))
                  :verify-guards nil
            :measure (stmt-measure s)))
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
      (case com
        (skip ctx)
        (begin (exec-stmt s2
                          (exec-stmt s1 ctx)))
        (malloc (put-assoc s1
                           (repeat s2 0)
                           ctx))
        ;; ignore []= for a bit
        ;; how to handle for?
        (for (if (zp s3)
                 ctx
               (let* ((ctx-i (put-assoc s1 s2 ctx))
                      (base-1i (+ s2 1))
                      (extent-1i (nfix (1- s3)))
                      (loop-i1 (cons com
                                     (cons s1
                                           (cons base-1i
                                                 (cons extent-1i
                                                       (cons s4 s4*))))))
                      ;; TODO: Should I delete s1 from ctx-1i?
                      (ctx-1i (delete-assoc s1
                                            (exec-stmt s4 ctx-i))))
                 (exec-stmt loop-i1 ctx-1i))))
        ([]= (let* ((buf-assoc (assoc s1 ctx))
                    (buf (cdr buf-assoc)))
               (if (and (consp buf-assoc)
                        (bufferp buf))
                   (put-assoc s1
                              ([]= buf
                                   (ifix (expr-eval s2 ctx))
                                   (ifix (expr-eval s3 ctx)))
                              ctx)
                 ctx)))
        (otherwise ctx)))))

(DEFTHM EXEC-STMT-TYPE-OK
        (IMPLIES (AND (STMTP S) (CONTEXTP CTX))
                 (CONTEXTP (EXEC-STMT S CTX)))
        :INSTRUCTIONS (:INDUCT :PROVE :PROVE :PROMOTE (:DIVE 1)
                               :X
                               :TOP :PROVE
                               :PROVE :PROVE
                               :PROVE :PROVE
                               :PROVE :PROVE))

(defthm exec-stmt-guards-helper1
(IMPLIES (AND (CONTEXTP CTX)
              S (TRUE-LISTP S)
              (SYMBOLP (CADR S))
              (EXPRP (CADDR S))
              (EXPRP (CADDDR S))
              (NOT (CDDDDR S))
              (EQUAL (CAR S) '[]=)
              (NOT (CONSP (ASSOC-EQUAL (CADR S) CTX))))
         (NOT (ASSOC-EQUAL (CADR S) CTX))))

(verify-guards exec-stmt
  :hints (("Goal"
           :do-not-induct t)))

(assert-event (equal (cons '(f 0 0 1 0 0)
                           (cons (cons 'i 2) nil))
                     (exec-stmt (list '[]= 'f 'i 1)
                                (cons '(f 0 0 0 0 0)
                                      (cons (cons 'i 2) nil)))))

(assert-event (equal (exec-stmt (list 'begin
                                      (list 'malloc 'f 10)
                                      (list 'for 'i 0 10
                                            (list '[]= 'f 'i 'i)))
                                nil)
                     (simulate-1d (cons '(f x)
                                        'x)
                                  0 10 nil)))

(verify (implies
         (and (exprp expr)
              (natp n)
              (natp b)
              (< 0 n)
              (contextp ctx)
              ;;(no-free-vars expr ctx)
              ;;(not-use-symbol expr 'f)
              )
         (equal (exec-stmt (list 'begin
                                 (list 'malloc 'f n)
                                 (list 'for 'i b n
                                       (list '[]= 'f 'i expr)))
                           ctx)
                (simulate-1d (cons '(f i)
                                   expr)
                             b n ctx))))
