

(defun no-free-vars (e c)
  (declare (xargs :guard (and (exprp e)
                              (contextp c))))
  (if (atom e)
      (if (symbolp e)
          (let ((has_key (assoc e c)))
            (consp has_key))
        t)
    (let ((fn (car e))
          (args (cdr e)))
      (case fn
        (- (no-free-vars (car args) c))
        (+ (and (no-free-vars (car args) c)
                (no-free-vars (cadr args) c)))
        (* (and (no-free-vars (car args) c)
                (no-free-vars (cadr args) c)))
        ([] (and (no-free-vars (car args) c)
                 (no-free-vars (cadr args) c)))
        (alloca t)
        (otherwise nil)))))

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
