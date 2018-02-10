P41. Not a theorem. If x = t, the (app x nil) = nil which is not equal to x.

P44. Not a theorem. If x = t, then (rev x) = nil and (rev (rev x)) = nil, which
is not equal to x.

P45. Use Induction. The base case is (not (consp x)), and (swap-tree x) = x and
(swap-tree (swap-tree x)) = x.

The induction hypothesis is (and (consp x)
                                 (equal (swap-tree (swap-tree (car x))) (car x))
                                 (equal (swap-tree (swap-tree (car x))) (cdr x)))
Since (car x) = (cons (car x) (cdr x)), 
(swap-tree x) =
(cons (swap-tree (cdr x)) (swap-tree (car x)))
and (swap-tree (swap-tree x)) =
(cons (swap-tree (swap-tree (car x))) (swap-tree (swap-tree (cdr x)))).
Based on induction hypothesis,
(swap-tree (swap-tree x)) = (cons (car x) (cdr x)) = x. QED.

P48.

Lemma 48.1. Prove (implies (sub x y) (sub x (cons a y))).
Proof. Induct on x. The base case is (not (consp x)), (sub x (cons a y)) = t.

The induction hypothesis is (and (consp x)
                                 (implies (sub (cdr x) y)
                                          (sub (cdr x) (cons a y)))).
Because x = (cons (car x) (cdr x)), and (sub x y), we have (mem (car x) y) = t and (sub (cdr x) y).
It is easy to show (mem (car x) (cons a y)) = t because (mem (car x) y), and also
(sub (cdr x) (cons a y)). hence (sub x y) = t. QED.

Back to Prove (sub a a).
Use induction on a. The base case we have (not (consp a)), hence (sub a a) = t.
The induction hypothesis is (and (consp a)
                                 (sub (cdr a) (cdr a)).
Because (sub (cdr a) (cdr a)) and use lemma 48.1 replace 'a' = (car a),
hence we have (sub (cdr a) (cons (car a) (cdr a))) = (sub (cdr a) a). 
Also, it is easy to show (mem (car a) a) = t given a = (cons (car a) (cdr a)). Hence
We have (sub a a) = (if (mem (car a) a) (sub (cdr a) a) nil) = t. QED.

P49.
Lemma 49.1 Prove (implies (and (mem x a) (sub a b))
                          (mem x b)).
Proof.
Induct on a.
The base case is (not (consp a)), (mem x a) = nil hence
(and (mem x a) (sub a b)) = nil. Nil can imply anything. Base case done.

The induction hypothesis is (and (consp a)
                                 (implies (and (mem x (cdr a)) (sub (cdr a) b))
                                          (mem x b))).
Becuase (mem x a) = t and a = (cons (car a) (cdr a)),
So (mem x a) = (if (equal x (car a)) t (mem x (cdr a))) = t,
we have either (equal x (car a)) = t or
(mem x (cdr a)) = t. 

Case 1. (equal x (car a)) = t so x = (car a).
Because (sub a b) = t, we have (mem x b) = (mem (car a) b) = t. (Case 1 done).

Case 2. (mem x (cdr a)) = t.
Because (sub a b) = (if (mem (car a) b) (sub (cdr a) b) nil) = t,
we konw (mem (car a) b) = t and (sub (cdr a) b) = t.
Based on induction hypothesis, we have (mem x b). (Case 2 done).
QED.

Back to Prove (implies (and (sub a b) (sub b c)) (sub a c)).
Proof.
Induct on a.
The base case is (not (consp a)). We have (sub a c) = t. Base case done.
The induction hypothesis is (and (consp a)
                                 (implies (and (sub (cdr a) b) (sub b c))
                                          (sub (cdr a) c))).
Because a = (cons (car a) (cdr a)),
(sub a c) = (if (mem (car a) c) (sub (cdr a) c) nil) and
(sub a b) = (if (mem (car a) b) (sub (cdr a) b) nil).
Because (sub a b) = t, we have (mem (car a) b) = t and (sub (cdr a) b) = t.
Based on lemma 49.1, becase (mem (car a) b) and (sub b c) we have (mem (car a) c) = t.
ALso, use the induction hypothesis, we have (sub (cdr a) c) = t.
Hence (sub a c) = (if (mem (car a) c) (sub (cdr a) c) nil) t.
Induction case done.
QED.

P50. 
Lemma 50.1. Prove (implies (and (sub a c) (sub b c))
                                (sub (app a b) c)).
Proof.
Induct on a. The base case is (not (consp a)), (app a b) = b and
(sub (app a b) c) = (sub b c) = t. (Base case done).

The induction hypothesis is (and (consp a)
                                 (implies (and (sub (cdr a) c) (sub b c))
                                          (sub (app (cdr a) b) c))).

Because (sub a c) = (if (mem (car a) c) (sub (cdr a) c) nil) = t,
we have (mem (car a) c) = t and (sub (cdr a) c) = t.
Use the induction hypothesis we have (sub (app (cdr a) b) c).
We also know (app a b) = (cons (car a) (app (cdr a) b)) in the induction case.
So (sub (app a b) c)) = (sub (cons (car a) (app (cdr a) b)) c)
                      = (if (mem (car a) c)
                            (sub (app (cdr a) b) c)
                            nil)
                      = t.
QED.

Too prove P50, use lemma 50.1 and we know (sub a a), hence,
(sub (app a a) a). QED.
