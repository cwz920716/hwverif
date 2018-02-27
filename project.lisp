;; Simplified Halide Lang
;; Author: Wenzhi Cui

;; A Halide Function has 3 components: a function name, a list of dimentional identifier
;; and a expression definition, e.g.,
;; blur_x(x, y) = (input(x-1, y) + input(x, y) + input(x+1, y)) / 3
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
;; Expr = ([][] <Buffer-or-Func> Expr Expr)  2-d index
;; Expr = <dimentional_identifier>
;; Expr = <const_number>

;; For milestone 0, we do not support buffer/func indexing yet.

; do I need to define []?
(defun [] (func args)
  (declare (xargs :guard (true-listp args)))
  (cons func args))

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
             (otherwise nil))
           ))
    ))
  
(defun integerp-al (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (let ((pair (car x)))
      (and (consp pair)
           (symbolp (car pair))
           (integerp (cdr pair))
           (integerp-al (cdr x))))))

(defun all-integers (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (integerp (car x))
         (all-integers (cdr x)))))

(defun halide-eval (e a)
  (declare (xargs :guard
                  (and (exprp e)
                       (integerp-al a))))
  (if (atom e)
      (if (symbolp e)
          (ifix (cdr (assoc e a)))
        (ifix e))
    (let ((fn (car e))
          (args (cdr e)))
      (case fn
        (- (- (halide-eval (car args) a)))
        (+ (+ (halide-eval (car args) a)
              (halide-eval (cadr args) a)))
        (* (* (halide-eval (car args) a)
              (halide-eval (cadr args) a)))
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
        (otherwise e)))))

(defthm constant-fold-expr (implies (exprp e)
                                    (exprp (constant-fold e))))

(defthm constant-fold-is-correct
  (implies (and (exprp e)
                (integerp-al a))
           (equal (halide-eval (constant-fold t e) a)
                  (halide-eval e a))))
