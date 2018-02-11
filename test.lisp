(defun tree-copy (x)
  (if (consp x)
      (cons (tree-copy (car x))
            (tree-copy (cdr x)))
    x))

(defun app (x y)
  (if (consp x)
      (cons (car x) (app (cdr x) y))
    y))

(defun rev (x)
  (if (consp x)
      (app (rev (cdr x)) (cons (car x) nil))
    nil))

(defun mapnil (x)
  (if (consp x)
      (cons nil (mapnil (cdr x)))
    nil))

(defun swap-tree (x)
  (if (consp x)
      (cons (swap-tree (cdr x))
            (swap-tree (car x)))
    x))

(defun mem (e x)
  (if (consp x)
      (if (equal e (car x))
          t
        (mem e (cdr x)))
    nil))

(defun sub (x y)
  (if (consp x)
      (if (mem (car x) y)
          (sub (cdr x) y)
        nil)
    t))

(defun int (x y)
  (if (consp x)
      (if (mem (car x) y)
          (cons (car x) (int (cdr x) y))
        (int (cdr x) y))
    nil))

(defun mapnil1 (x a)
  (if (consp x)
      (mapnil1 (cdr x) (cons nil a))
    a))

(defun rev1 (x a)
  (if (consp x)
      (rev1 (cdr x) (cons (car x) a))
    a))

(DEFTHM COPY-OK (EQUAL (TREE-COPY X) X)
        :INSTRUCTIONS (:INDUCT (:DIVE 1)
                               :EXPAND
                               :S :TOP
                               :S (:DIVE 1)
                               :EXPAND :S
                               :TOP :S))

(DEFTHM APP-NIL-OK
        (IMPLIES (TRUE-LISTP A)
                 (EQUAL (APP A NIL) A))
        :INSTRUCTIONS (:PROMOTE :INDUCT :PROMOTE (:DIVE 1)
                                :EXPAND :S :TOP :S :PROMOTE (:DIVE 1)
                                :EXPAND
                                :S :TOP (:CLAIM (TRUE-LISTP (CDR A)))
                                (:CLAIM (EQUAL (APP (CDR A) NIL) (CDR A)))
                                :S))

(DEFTHM APP-ASSOC
        (EQUAL (APP A (APP B C))
               (APP (APP A B) C))
        :INSTRUCTIONS (:INDUCT (:DIVE 1)
                               :EXPAND :S :TOP (:DIVE 2)
                               (:DIVE 1)
                               :EXPAND :S :TOP :S (:DIVE 1)
                               :EXPAND :S :TOP (:DIVE 2)
                               (:DIVE 1)
                               :EXPAND :S
                               :TOP (:DIVE 2)
                               :EXPAND :S
                               :TOP :S))

(DEFTHM LIST-CDR-LIST
        (IMPLIES (TRUE-LISTP X)
                 (TRUE-LISTP (CDR X)))
        :INSTRUCTIONS (:INDUCT :PROMOTE :S :PROMOTE :S))

(DEFTHM LIST-APP-LIST
        (IMPLIES (AND (TRUE-LISTP X) (TRUE-LISTP Y))
                 (TRUE-LISTP (APP X Y)))
        :INSTRUCTIONS (:INDUCT :PROMOTE :S
                               :PROMOTE (:DIVE 1)
                               :EXPAND :S
                               :TOP :S))
(DEFTHM LIST-REV-LIST
        (IMPLIES (TRUE-LISTP X)
                 (TRUE-LISTP (REV X)))
        :INSTRUCTIONS (:INDUCT :PROMOTE :S :PROMOTE (:DIVE 1)
                               :X :TOP (:USE LIST-APP-LIST)
                               :PROMOTE (:REWRITE LIST-APP-LIST)
                               (:DROP 1)
                               (:USE LIST-CDR-LIST)))

(DEFTHM IMPLIES-TRANS
        (IMPLIES (AND (IMPLIES A B) (IMPLIES B C))
                 (IMPLIES A C))
        :INSTRUCTIONS (:S))

(DEFTHM REV-APP-OK
        (IMPLIES (AND (TRUE-LISTP X) (TRUE-LISTP Y))
                 (EQUAL (REV (APP X Y))
                        (APP (REV Y) (REV X))))
        :INSTRUCTIONS (:INDUCT :PROMOTE :S (:USE APP-NIL-OK)
                               :PROMOTE (:DIVE 2)
                               :TOP (:USE LIST-REV-LIST)
                               :PROMOTE (:DIVE 2)
                               (:REWRITE APP-NIL-OK)
                               :TOP :S :S :PROMOTE (:DIVE 1)
                               (:DIVE 1)
                               :X :TOP (:DIVE 1)
                               :X :TOP (:DIVE 1 1)
                               :TOP (:DIVE 2 2)
                               :X :TOP :S (:USE LIST-CDR-LIST)
                               :PROMOTE (:DIVE 1 2)
                               :TOP (:DIVE 1 1)
                               (:DROP 1)
                               :TOP (:USE LIST-CDR-LIST)
                               :PROMOTE (:DIVE 2 1)
                               :TOP (:DEMOTE 1 3)
                               :S))

(DEFTHM REV-REV-OK
        (IMPLIES (TRUE-LISTP X)
                 (EQUAL (REV (REV X)) X))
        :INSTRUCTIONS (:INDUCT :PROMOTE :S :PROMOTE (:DIVE 1)
                               (:DIVE 1)
                               :X :TOP (:USE REV-APP-OK)
                               :PROMOTE (:DIVE 1)
                               (:REWRITE REV-APP-OK)
                               :TOP (:DIVE 1 1)
                               :S
                               :TOP (:DIVE 1 2)
                               :TOP (:USE LIST-CDR-LIST)
                               :PROMOTE (:DIVE 1 2)
                               :TOP (:DEMOTE 4)
                               :S (:USE LIST-REV-LIST)
                               :PROMOTE :S))

(DEFTHM SWAP-SWAP-OK
        (EQUAL (SWAP-TREE (SWAP-TREE X)) X)
        :INSTRUCTIONS (:INDUCT :S (:DIVE 1 1)
                               :X :TOP (:DIVE 1)
                               :X
                               :TOP :S))

(DEFTHM SUB-CDR-OK
        (IMPLIES (SUB X Y) (SUB (CDR X) Y))
        :INSTRUCTIONS (:INDUCT :S
                               :PROMOTE (:DEMOTE 2 3)
                               :S (:DIVE 1)
                               :EXPAND :S
                               :TOP :S))

(DEFTHM SUB-CONS-OK
        (IMPLIES (SUB X Y) (SUB X (CONS (CAR A) Y)))
        :INSTRUCTIONS (:INDUCT :S :X (:DEMOTE 2)
                               :S :PROMOTE :X (:DIVE 1)
                               (:DIVE 2)
                               :TOP (:DIVE 1 1)
                               :TOP (:DIVE 1 2)
                               :TOP (:USE SUB-CDR-OK)
                               :PROMOTE (:DEMOTE 4)
                               :S (:DIVE 2)
                               :TOP :SPLIT (:DEMOTE 3 6)
                               :S))

(defun count-in (x l)
  (if (consp l)
      (if (equal x (car l))
          (+ 1 (count x (cdr l)))
        (count x (cdr l)))
    0))

(defun consist (a x y)
  (if (consp a)
      (if (equal (count-in (car a) x)
                 (count-in (car a) y))
          (consist (cdr a) x y)
        nil)
    t))

(DEFTHM CONSIST-SELF (CONSIST A X X)
  :INSTRUCTIONS (:INDUCT :S (:DEMOTE 2) :S :S))

(DEFTHM CONSIST-COMM
        (EQUAL (CONSIST A X Y) (CONSIST A Y X))
        :INSTRUCTIONS (:INDUCT :S (:DIVE 1)
                               :EXPAND :S :TOP (:DIVE 2)
                               :EXPAND
                               :S (:DIVE 1)
                               :EXPAND :S
                               :TOP (:DIVE 2)
                               :EXPAND :S
                               :TOP :S))

(defun perm (x y)
  (and (consist x x y)
       (consist y x y)))


(DEFTHM PERM-SELF (PERM X X)
        :INSTRUCTIONS (:X))

(DEFTHM PERM-COMM (EQUAL (PERM X Y) (PERM Y X))
  :INSTRUCTIONS (:S :S))

(defun ordered (x)
  (if (atom x)
      t
    (if (atom (cdr x))
        t
      (if (lexorder (car x) (cadr x))
          (ordered (cdr x))
        nil))))

(defun ins-sort (x l)
  (if (atom l)
      (cons x nil)
    (if (lexorder x (car l))
        (cons x l)
      (cons (car l) (ins-sort x (cdr l)))
      )))

(defun isort (x)
  (if (consp x)
      (ins-sort (car x) (isort (cdr x)))
    nil))

(DEFTHM ORDERED-CDR-OK
        (IMPLIES (ORDERED L) (ORDERED (CDR L)))
        :INSTRUCTIONS (:INDUCT (:DIVE 1)
                               :EXPAND
                               :S :TOP
                               :S (:DIVE 1)
                               :EXPAND :S
                               :TOP :S
                               :PROMOTE :S
                               :PROMOTE :S))

(DEFTHM ORDERED-INS-HELPER
        (IMPLIES (AND (ORDERED L)
                      (CONSP L)
                      (LEXORDER (CAR L) X))
                 (LEXORDER (CAR L)
                           (CAR (INS-SORT X (CDR L)))))
        :INSTRUCTIONS (:INDUCT :PROMOTE (:DIVE 2 1)
                               :EXPAND :S :TOP :SPLIT :S :S (:DEMOTE 3)
                               :S (:DEMOTE 3)
                               (:DIVE 1)
                               :EXPAND :S
                               :TOP :S
                               :PROMOTE (:DIVE 2 1)
                               :EXPAND :S
                               :TOP :SPLIT
                               :S :S
                               :S :S
                               :S :S
                               :PROMOTE :S))

(DEFTHM ORDERED-INS-ORDERED
        (IMPLIES (ORDERED L)
                 (ORDERED (INS-SORT X L)))
        :INSTRUCTIONS (:INDUCT :PROMOTE (:DIVE 1)
                               :EXPAND
                               :S :TOP :EXPAND :S (:USE ORDERED-CDR-OK)
                               :PROMOTE
                               :S :S))

(verify (ordered (isort x)))
