

(defun realize-at-1d (e id ctx)
  (declare (xargs :guard (and (natp id)
                              (halide-1dp e)
                              (contextp ctx))))
  (let* ((dim0 (car (halide-dims e)))
         (rhs (halide-expr e))
         (new-ctx (put-assoc dim0 id ctx)))
    (ifix (expr-eval rhs new-ctx))))

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
