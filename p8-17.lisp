(defun listize (x)
  (cons x nil))

(defun app (a b)
  (if (consp a)
      (cons (car a) (app (cdr a) b))
    b))

(defun rev (x)
  (if (atom x)
      nil
    (app (rev (cdr x)) (listize (car x)))))

(defun mapnil (x)
  (if (consp x)
      (cons nil (mapnil (cdr x)))
    nil))

(defun swap-tree (x)
  (if (consp x)
      (cons (swap-tree (cdr x))
            (swap-tree (car x)))
    x))

(defun mem (a b)
  (if (consp b)
      (or (equal a (car b)) (mem a (cdr b)))
    (equal a b)))

(defun sub (x y)
  (if (consp x)
      (and (mem (car x) y)
           (sub (cdr x) y))
    (mem x y)))

(defun int (a b)
  (if (consp a)
      (if (mem (car a) b)
          (cons (car a) (int (cdr a) b))
        (int (cdr a) b))
    (if (mem a b) a nil)))

(defun tip (e x)
  (if (consp x)
      (or (tip e (car x))
          (tip e (cdr x)))
    (equal e x)))

(defun flatten (x)
  (if (consp x)
      (app (flatten (car x))
           (flatten (cdr x)))
    (cons x nil)))

(defun length0 (x)
  (if (consp x)
      (+ 1 (length0 (cdr x)))
    0))

(defun evenlen (x)
  (if (consp x)
      (not (evenlen (cdr x)))
    t))
