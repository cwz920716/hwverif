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
          (not (integerp n)))
      t
    (induct-rib (- n 1))))

(DEFTHM REPEAT-IS-BUF
        (IMPLIES (AND (INTEGERP N) (>= N 1))
                 (BUFFERP (REPEAT N 0)))
        :INSTRUCTIONS ((:INDUCT (INDUCT-RIB N))
                       :BASH (:DV 1)
                       (:DIVE 1)
                       :UP
                       :EXPAND :S
                       :TOP :EXPAND
                       :S :BASH))

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
                                    (> (length l) 0)
                                    (integerp x))
                               (integerp (nth (bound x (length l)) l))))

(defthm bound-ok (implies (and (< 0 N)
                               (integerp N)
                               (integerp x))
                          (and (integerp (bound x N))
                               (< (bound x N) N))))

(DEFTHM MEMBER-IF-BOUNDED
        (IMPLIES (AND (INTEGER-LISTP L)
                      (< 0 (LENGTH L))
                      (INTEGERP X)
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

(defthm update-nth-buf-ok
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

(defun put-ctx (k v ctx)
  (declare (xargs :guard (and (symbolp k)
                              (or (integerp v)
                                  (bufferp v))
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
                    (bufferp v))
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
                (bufferp buf)
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
         (bufferp (cdr sa)))))

(defthm declared-buf-ok
  (implies (and (symbolp s)
                (contextp ctx)
                (declared-buf s ctx))
           (and (consp (assoc s ctx))
                (bufferp (cdr (assoc s ctx))))
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
                    (bufferp v))
                )
           (consp (assoc k
                         (put-ctx k v ctx))))
  )

(defthm equal-after-put-ctx
  (implies (and (contextp ctx)
                (symbolp k)
                (or (integerp v)
                    (bufferp v))
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
                    (bufferp v2))
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
                    (bufferp v2))
                )
           (equal (cdr (assoc k1
                              (put-ctx k2 v2 ctx)))
                  v)))

(defthm buf-declared-after-put-buf
  (implies (and (contextp ctx)
                (symbolp fname)
                (bufferp buf))
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

(defthm halide-name-ok
  (implies (halide-1dp e)
           (not (equal (halide-funcname e)
                       (halide-dim0 e)))))

(defun simulate-1d-update (e ctx)
  (declare (xargs :guard (and (halide-1dp e)
                              (contextp ctx)
                              (declared-buf (halide-funcname e) ctx)
                              (declared-int (halide-dim0 e) ctx)
                              )
                  :verify-guards nil))
  (let* ((fname (halide-funcname e))
         (dim0 (halide-dim0 e))
         (buf (cdr (assoc fname ctx)))
         (idx (cdr (assoc dim0 ctx))))
    (if (and (bufferp buf)
             (integerp idx))
        (put-ctx fname
                   ([]= buf
                        (ifix idx)
                        (ifix (expr-eval (halide-expr e) ctx)))
                   ctx)
      ctx)))

;; get stuck
(verify-guards simulate-1d-update
              :hints (("Goal" :do-not-induct t)))

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

(DEFTHM BDAPSD-HELPER1
        (IMPLIES (AND (HALIDE-1DP E)
                      (CONTEXTP CTX)
                      (DECLARED-BUF (HALIDE-FUNCNAME E) CTX)
                      (INTEGERP BASE))
                 (DECLARED-BUF (HALIDE-FUNCNAME E)
                               (PUT-CTX (HALIDE-DIM0 E) BASE CTX)))
        :INSTRUCTIONS
        (:PROMOTE :S-PROP
                  (:USE (:INSTANCE BUF-DECLARED-AFTER-UPDATE-IDX (CTX CTX)
                                   (DIM0 (HALIDE-DIM0 E))
                                   (FNAME (HALIDE-FUNCNAME E))
                                   (IDX BASE)))
                  (:DEMOTE 1)
                  (:DIVE 1 2)
                  :TOP :PROMOTE :PROMOTE (:DEMOTE 1)
                  (:DIVE 1 2)
                  :S :TOP :PROMOTE (:DEMOTE 5)
                  :BASH))

(DEFTHM
 BDAPSD-HELPER2
 (IMPLIES
    (AND (HALIDE-1DP E)
         (CONTEXTP CTX)
         (DECLARED-BUF (HALIDE-FUNCNAME E) CTX)
         (INTEGERP BASE))
    (DECLARED-BUF (HALIDE-FUNCNAME E)
                  (SIMULATE-1D-UPDATE E
                                      (PUT-ASSOC (HALIDE-DIM0 E) BASE CTX))))
 :INSTRUCTIONS
 (:PROMOTE :S-PROP
           (:CLAIM (DECLARED-BUF (HALIDE-FUNCNAME E)
                                 (PUT-ASSOC-EQUAL (HALIDE-DIM0 E)
                                                  BASE CTX)))
           :PROVE))

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
                                     (PUT-ASSOC (HALIDE-DIM0 E) BASE CTX)))))
 :INSTRUCTIONS
 (:PROMOTE
   :S-PROP
   (:CLAIM (DECLARED-BUF (HALIDE-FUNCNAME E)
                         (PUT-ASSOC-EQUAL (HALIDE-DIM0 E)
                                          BASE CTX)))
   (:CLAIM (DECLARED-BUF (HALIDE-FUNCNAME E)
                         (SIMULATE-1D-UPDATE E
                                             (PUT-ASSOC-EQUAL (HALIDE-DIM0 E)
                                                              BASE CTX))))
   (:CLAIM (NOT (EQUAL (HALIDE-FUNCNAME E)
                       (HALIDE-DIM0 E))))
   (:USE (:INSTANCE BUF-DECLARED-AFTER-DELETE-IDX
                    (DIM0 (HALIDE-DIM0 E))
                    (FNAME (HALIDE-FUNCNAME E))
                    (CTX (SIMULATE-1D-UPDATE E
                                             (PUT-ASSOC-EQUAL (HALIDE-DIM0 E)
                                                              BASE CTX)))))
   :PROMOTE (:DEMOTE 1)
   :BASH))

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

;; get stuck
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

(defun simulate-1d (e base size ctx)
  (declare (xargs :guard (and (halide-1dp e)
                              (natp size)
                              (natp base)
                              (< 0 size)
                              (contextp ctx))
                  :verify-guards nil))
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
                      (extent-1i (nfix (1- s3)))
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
                        (bufferp buf))
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

(verify (implies
         (and (exprp expr)
              (natp n)
              (natp b)
              (< 0 n)
              (contextp ctx)
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
