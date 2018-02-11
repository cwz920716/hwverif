(defun app (x y)
  (cond ((endp x) y)
        (t (cons (car x)
                 (app (cdr x) y))))) 

(defthm associativity-of-app 
        (equal (app (app a b) c) 
               (app a (app b c)))) 

(defthm Mod01 (implies (natp x) (or (equal (mod x 2) 0) (equal (mod x 2) 1))))

(defthm xxx (implies (natp x) (equal (mod (* x 2) 2) 0)))
