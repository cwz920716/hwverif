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
Also, it is easy to show (mem (car a) a) given a = (cons (car a) (cdr a)). Hence
We have (sub a a) also is true in induction case. QED.

P49.
Lemma 49.1 Prove (implies (and (mem x a) (sub a b))
                          (mem x b)).
Proof.
Induct on a.
The base case is (not (consp a)), (mem x a) = nil hence
(and (mem x a) (sub a b)) = nil. Nil can imply anything. Base case done.
The induction hypothesis is (and (consp a)
                                 (implies (and (mem x a2) (sub a2 b))
                                          (mem x b))).
Becuase (mem x a) and a = (cons a1 a2), we have either (equal x a1) or
(mem x a2). 
Case 1. x = a1. Because (sub a b) = t, we have (mem a1 b) = t. (Case 1 done).
Case 2. (mem x a2). Because (sub a b), we have (mem a1 b) and (sub a2 b).
Based on induction hypothesis, we have (mem x b). (Case 2 done).
QED.

Back to Prove (implies (and (sub a b) (sub b c)) (sub a c)).
Proof.
Induct on a.
The base case is (not (consp a)). We have (sub a c) = t. Base case done.
The induction hypothesis is (and (consp a)
                                 (implies (and (sub a2 b) (sub b c))
                                          (sub a2 c))).
Because a = (cons a1 a2),
(sub a c) = (if (mem a1 c) (sub a2 c) nil).
Because (sub a b) = t, we have (mem a1 b) = t and (sub a2 b) = t.
Based on lemma 49.1, becase (mem a1 b) and (sub b c) we have (mem a1 c) = t.
ALso, use the induction hypothesis, we have (sub a2 c) = t. Hence (sub a c) = t.
Induction case done.
QED.

P50. 
Lemma 50.1. Prove (implies (sub b a) (sub (app a b) a)).
Proof. 
