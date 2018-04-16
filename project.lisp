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

(local (include-book "std/lists/repeat" :dir :system))

(defun induct-rib (n)
  (if (zp n)
      t
    (induct-rib (- n 1))))

(DEFTHM REPEAT-IS-BUF
        (IMPLIES (NATP N)
                 (INTEGER-LISTP (REPEAT N 0)))
        :INSTRUCTIONS ((:INDUCT (INDUCT-RIB N))
                       :PROMOTE (:DIVE 1)
                       :X
                       :TOP (:CLAIM (NATP (1- N)))
                       :BASH :BASH))

(DEFTHM REPEAT-POSINT-BUF
        (IMPLIES (AND (INTEGERP N) (< 0 N))
                 (INTEGER-LISTP (REPEAT N 0))))

(defun [] (buf x)
  (declare (xargs :guard (and (integer-listp buf)
                              (integerp x))))
  (ifix (nth (nfix x) buf)))

(DEFTHM BUFFER-ACCESS-OK
        (IMPLIES (AND (INTEGER-LISTP BUF) (INTEGERP N))
                 (INTEGERP ([] BUF N)))
        :INSTRUCTIONS ((:DIVE 1 1)
                       :EXPAND :TOP (:DIVE 2 1)
                       :EXPAND
                       :TOP :PROVE))

(defun assign2 (buf x val)
  (declare (xargs :guard (and (integer-listp buf)
                              (natp x)
                              (integerp val))))
  (if (endp buf)
      nil
    (if (zp x)
        (cons val (cdr buf))
      (cons (car buf) (assign2 (cdr buf) (nfix (1- x)) val))
    )))

(defthm assign-buf-ok
    (implies (and (integer-listp buf)
                  (natp n1)
                  (integerp i2))
             (integer-listp (assign2 buf n1 i2))))

(defun []= (buf x val)
  (declare (xargs :guard (and (integer-listp buf)
                              (integerp x)
                              (integerp val))))
  (if (natp x)
      (assign2 buf x val)
    buf))

(defthm update-buf-ok
    (implies (and (integer-listp buf)
                  (integerp i1)
                  (integerp i2))
             (integer-listp ([]= buf i1 i2))))

;; A context is a list which only supports (symbol.integer) or (symbol.buffer)
(defun contextp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (let ((pair (car x)))
      (and (consp pair)
           (symbolp (car pair))
           (or (integerp (cdr pair))
               (integer-listp (cdr pair)))
           (contextp (cdr x))))))

(defthm context-is-alist
  (implies (contextp ctx)
           (alistp ctx)))

(defun put-ctx (k v ctx)
  (declare (xargs :guard (and (symbolp k)
                              (or (integerp v)
                                  (integer-listp v))
                              (contextp ctx))))
  (if (endp ctx)
      (list (cons k v))
    (if (equal k (caar ctx))
        (cons (cons k v) (cdr ctx))
      (cons (car ctx)
            (put-ctx k v (cdr ctx))))))

(defthm put-assoc-ctx-ok
  (implies (and (symbolp k)
                (or (integerp v)
                    (integer-listp v))
                (contextp ctx))
           (equal (put-assoc k v ctx)
                  (put-ctx k v ctx))))

(defun delete-ctx (k ctx)
  (declare (xargs :guard (and (symbolp k)
                              (contextp ctx))))
  (if (endp ctx)
      nil
    (if (equal k (caar ctx))
        (cdr ctx)
      (cons (car ctx) (delete-ctx k (cdr ctx))))))

(defthm delete-ctx-ctx-ok
  (implies (and (symbolp k)
                (contextp ctx))
           (equal (delete-assoc k ctx)
                  (delete-ctx k ctx))))

(defthm context-put-buf-ok
  (implies (and (symbolp name)
                (integer-listp buf)
                (contextp ctx))
           (contextp (put-ctx name buf ctx))))

(defthm context-put-int-ok
  (implies (and (symbolp name)
                (integerp n)
                (contextp ctx))
           (contextp (put-ctx name n ctx))))

(defthm context-del-ok
  (implies (and (symbolp name)
                (contextp ctx))
           (contextp (delete-ctx name ctx))))

(defun declared-buf (sym ctx)
  (declare (xargs :guard (and (symbolp sym)
                              (contextp ctx))))
  (let ((sa (assoc sym ctx)))
    (and (consp sa)
         (integer-listp (cdr sa)))))

(defthm declared-buf-ok
  (implies (and (symbolp s)
                (contextp ctx)
                (declared-buf s ctx))
           (and (consp (assoc s ctx))
                (integer-listp (cdr (assoc s ctx))))
           ))

(defun declared-int (sym ctx)
  (declare (xargs :guard (and (symbolp sym)
                              (contextp ctx))))
  (let ((sa (assoc sym ctx)))
    (and (consp sa)
         (integerp (cdr sa)))))

(defthm declared-int-ok
  (implies (and (symbolp s)
                (contextp ctx)
                (declared-int s ctx))
           (and (consp (assoc s ctx))
                (integerp (cdr (assoc s ctx))))
           ))

(defthm exist-after-put-ctx
  (implies (and (contextp ctx)
                (symbolp k)
                (or (integerp v)
                    (integer-listp v))
                )
           (consp (assoc k
                         (put-ctx k v ctx))))
  )

(defthm equal-after-put-ctx
  (implies (and (contextp ctx)
                (symbolp k)
                (or (integerp v)
                    (integer-listp v))
                )
           (equal (cdr (assoc k (put-ctx k v ctx)))
                  v)))

(defthm exist-after-del-k2
  (implies (and (contextp ctx)
                (symbolp k1)
                (symbolp k2)
                (not (equal k1 k2))
                (consp (assoc k1 ctx))
                )
           (consp (assoc k1
                         (delete-ctx k2 ctx)))))

(defthm unchanged-after-del-k2
  (implies (and (contextp ctx)
                (symbolp k1)
                (symbolp k2)
                (not (equal k1 k2))
                (consp (assoc k1 ctx))
                (equal (cdr (assoc k1 ctx))
                       v)
                )
           (equal (cdr (assoc k1
                              (delete-ctx k2 ctx)))
                  v)))

(defthm exist-after-put-k2
  (implies (and (contextp ctx)
                (symbolp k1)
                (symbolp k2)
                (not (equal k1 k2))
                (consp (assoc k1 ctx))
                (or (integerp v2)
                    (integer-listp v2))
                )
           (consp (assoc k1
                         (put-ctx k2 v2 ctx)))))

(defthm unchanged-after-put-k2
  (implies (and (contextp ctx)
                (symbolp k1)
                (symbolp k2)
                (not (equal k1 k2))
                (consp (assoc k1 ctx))
                (equal (cdr (assoc k1 ctx))
                       v)
                (or (integerp v2)
                    (integer-listp v2))
                )
           (equal (cdr (assoc k1
                              (put-ctx k2 v2 ctx)))
                  v)))

(defthm buf-declared-after-put-buf
  (implies (and (contextp ctx)
                (symbolp fname)
                (integer-listp buf))
           (declared-buf fname (put-ctx fname buf ctx))))

(defthm int-declared-after-put-int
  (implies (and (contextp ctx)
                (symbolp dim0)
                (integerp n))
           (declared-int dim0 (put-ctx dim0 n ctx))))

(defthm buf-declared-after-update-idx
  (implies (and (contextp ctx)
                (symbolp dim0)
                (symbolp fname)
                (not (equal fname dim0))
                (integerp idx)
                (declared-buf fname ctx))
           (declared-buf fname (put-ctx dim0 idx ctx))))

(defthm buf-declared-after-delete-idx
  (implies (and (contextp ctx)
                (symbolp dim0)
                (symbolp fname)
                (not (equal fname dim0))
                (declared-buf fname ctx))
           (declared-buf fname (delete-ctx dim0 ctx))))

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
                          (integerp arg1)
                          (< 0 arg1)))             
             (otherwise nil))
           ))
    ))

(defun not-use-symbol (e s)
  (declare (xargs :guard (and (exprp e)
                              (symbolp s))))
  (if (atom e)
      (if (symbolp e)
          (not (equal e s)) 
        t)
    (let ((fn (car e))
          (args (cdr e)))
      (case fn
        (- (not-use-symbol (car args) s))
        (+ (and (not-use-symbol (car args) s)
                (not-use-symbol (cadr args) s)))
        (* (and (not-use-symbol (car args) s)
                (not-use-symbol (cadr args) s)))
        ([] (and (not-use-symbol (car args) s)
                 (not-use-symbol (cadr args) s)))
        (alloca t)
        (otherwise nil)))))

(defun expr-eval (e c)
  (declare (xargs :guard
                  (and (exprp e)
                       (contextp c))))
  (if (atom e)
      (if (symbolp e)
          (let ((r (cdr (assoc e c))))
            (if (integer-listp r)
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
              (if (integer-listp buf)
                  ([] buf (ifix (expr-eval (cadr args) c)))
                (ifix buf))))
        (alloca (repeat (ifix (expr-eval (car args) c)) 0))
        (otherwise 0)))))

(defthm expr-type-ok
  (implies (and (exprp e)
                (contextp ctx))
           (or (integer-listp (expr-eval e ctx))
               (integerp (expr-eval e ctx)))))

;; A halide program has three components: A symbolic name, a symblic list for
;; dimentional vars, and a expression for pure definition
(defun halidep (e)
  (declare (xargs :guard t))
  (and (consp e)
       (consp (car e))
       (symbol-listp (car e))
       (no-duplicatesp (car e))
       (consp (cdar e))
       (exprp (cdr e))
       (not-use-symbol (cdr e) (caar e))
       ))

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

(defun halide-1dp (e)
  (declare (xargs :guard t))
  (and (halidep e)
       (atom (cddar e))
       ))

(defthm halide-1d-is-halide
    (implies (halide-1dp e)
             (halidep e)))

(defthm halide-name-ok
  (implies (halide-1dp e)
           (not (equal (halide-funcname e)
                       (halide-dim0 e)))))

(defthm halide-expr-ok
  (implies (halide-1dp e)
           (not-use-symbol (halide-expr e)
                           (halide-funcname e))))

(defun simulate-1d-update (e ctx)
  (declare (xargs :guard (and (halide-1dp e)
                              (contextp ctx)
                              ;(declared-buf (halide-funcname e) ctx)
                              ;(declared-int (halide-dim0 e) ctx)
                              )
                  ;:verify-guards nil
                  ))
  (let* ((fname (halide-funcname e))
         (dim0 (halide-dim0 e))
         (buf-pair (assoc fname ctx))
         (idx-pair (assoc dim0 ctx))
         (buf (cdr buf-pair))
         (idx (cdr idx-pair)))
    (if (and (consp buf-pair)
             (consp idx-pair)
             (integer-listp buf)
             (integerp idx))
        (put-ctx fname
                   ([]= buf
                        (ifix idx)
                        (ifix (expr-eval (halide-expr e) ctx)))
                   ctx)
      ctx)))

(defun simulate-1d-for (e base extent ctx)
  (declare (xargs :guard (and (halide-1dp e)
                              (integerp base)
                              (natp extent)
                              (contextp ctx)
                              (declared-buf (halide-funcname e) ctx))
                  :verify-guards t
                  ))
  (if (zp extent)
      ctx
    (let* ((dim0 (car (halide-dims e)))
           (ctx-i (put-ctx dim0 base ctx))
           (base-1i (+ base 1))
           (extent-1i (nfix (- extent 1)))
           (ctx-1i (delete-ctx dim0
                                 (simulate-1d-update e ctx-i))))
      (simulate-1d-for e base-1i extent-1i ctx-1i))))

(defun simulate-1d (e base size ctx)
  (declare (xargs :guard (and (halide-1dp e)
                              (natp size)
                              (natp base)
                              (< 0 size)
                              (contextp ctx))
                  :verify-guards t))
  (let* ((ctx-init (put-ctx (halide-funcname e)
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
        (malloc (put-ctx s1
                           (repeat s2 0)
                           ctx))
        ;; ignore []= for a bit
        ;; how to handle for?
        (for (if (zp s3)
                 ctx
               (let* ((ctx-i (put-ctx s1 s2 ctx))
                      (base-1i (+ s2 1))
                      (extent-1i (1- s3))
                      (loop-i1 (cons com
                                     (cons s1
                                           (cons base-1i
                                                 (cons extent-1i
                                                       (cons s4 s4*))))))
                      ;; TODO: Should I delete s1 from ctx-1i?
                      (ctx-1i (delete-ctx s1
                                            (exec-stmt s4 ctx-i))))
                 (exec-stmt loop-i1 ctx-1i))))
        ([]= (let* ((buf-assoc (assoc s1 ctx))
                    (buf (cdr buf-assoc)))
               (if (and (consp buf-assoc)
                        (integer-listp buf))
                   (put-ctx s1
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

(DEFTHM
 EXEC-FOR-EQUAL-SIM-FOR
 (IMPLIES (AND (NATP N)
               (NATP B)
               (SYMBOLP F)
               (SYMBOLP I)
               (CONTEXTP CTX)
               (DECLARED-BUF F CTX)
               (NOT (EQUAL F I))
               (EXPRP EXPR)
               (NOT-USE-SYMBOL EXPR F))
          (EQUAL (EXEC-STMT (LIST 'FOR I B N (LIST '[]= F I EXPR))
                            CTX)
                 (SIMULATE-1D-FOR (CONS (LIST F I) EXPR)
                                  B N CTX)))
 :INSTRUCTIONS
 (:INDUCT
  (:DEMOTE 2)
  (:DIVE 1)
  (:DIVE 2)
  (:DIVE 1)
  (:DIVE 1)
  :S :UP :UP :UP (:DIVE 2 2)
  (:DIVE 3)
  :S :UP (:DIVE 4 1)
  :S :UP :UP :UP (:DIVE 1 2)
  :S :UP :UP (:DIVE 2 4)
  :S :TOP :PROMOTE :PROMOTE (:DIVE 1)
  :X :TOP (:DIVE 2)
  :EXPAND :S-PROP :TOP
  (:CLAIM (HALIDE-1DP (CONS (LIST F I) EXPR)))
  (:CLAIM
   (CONTEXTP
    (DELETE-CTX
      (CAR (HALIDE-DIMS (CONS (LIST F I) EXPR)))
      (SIMULATE-1D-UPDATE (CONS (LIST F I) EXPR)
                          (PUT-CTX (CAR (HALIDE-DIMS (CONS (LIST F I) EXPR)))
                                   B CTX)))))
  (:CLAIM
   (DECLARED-BUF
    F
    (DELETE-CTX
      (CAR (HALIDE-DIMS (CONS (LIST F I) EXPR)))
      (SIMULATE-1D-UPDATE (CONS (LIST F I) EXPR)
                          (PUT-CTX (CAR (HALIDE-DIMS (CONS (LIST F I) EXPR)))
                                   B CTX)))))
  :BASH :BASH))

(defthm exec-stmt-equal-sim
  (implies
   (and (exprp expr)
        (natp n)
        (natp b)
        (contextp ctx)
        (symbolp f)
        (symbolp i)
        (not (equal f i))
        (not-use-symbol expr f)
        )
   (equal (exec-stmt (list 'begin
                           (list 'malloc f n)
                           (list 'for i b n
                                 (list '[]= f i expr)))
                     ctx)
          (simulate-1d (cons (list f i)
                             expr)
                       b n ctx))))

;;Now write and verify the compiler
(defun compile-halide (e n)
  (declare (xargs :guard (and (halide-1dp e)
                              (natp n)
                              (< 0 n))))
  (let* ((f (halide-funcname e))
         (id (halide-dim0 e))
         (expr (halide-expr e)))
    (list 'begin
          (list 'malloc f n)
          (list 'for id 0 n
                (list '[]= f id expr)))
    ))

(defthm compiler-type-ok
  (implies (and (halide-1dp e)
                (natp n)
                (< 0 n))
           (stmtp (compile-halide e n))))

(defthm compiler-ok
  (implies (and (halide-1dp e)
                (natp n)
                (< 0 n)
                (contextp ctx))
           (equal (exec-stmt (compile-halide e n)
                             ctx)
                  (simulate-1d e 0 n ctx))))

;; Now add constant folding

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
