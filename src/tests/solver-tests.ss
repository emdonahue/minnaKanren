(import (test-runner) (mk core) (mk core goals) (mk constraints) (mk tracing))

(define x1 (var 1))
(define x2 (var 2))
(define x3 (var 3))
(define x4 (var 4))

(test-suite
 solver

 ;; === CON/DISJUNCTION ===
 (tassert "conj fail first" (conj fail succeed) fail)
 (tassert "conj fail rest" (conj succeed fail) fail)
 (tassert "conj compress succeed" (conj succeed succeed) succeed)
 (tassert "conj single goals" (conj* (== 1 1)) (== 1 1))
 (tassert "conj keep normal goals" (conj* (== 1 1) succeed (== 2 2)) (conj* (== 1 1) (== 2 2)))

 (tassert "disj succeed first" (disj succeed fail) succeed)
 (tassert "disj succeed rest" (disj fail succeed) succeed)
 (tassert "disj compress fail" (disj fail fail) fail)
 (tassert "disj single goals" (disj* (== 1 1)) (== 1 1))
 (tassert "disj keep normal goals" (disj* (== 1 1) fail (== 1 1)) (disj (== 1 1) (== 1 1)))

 ;; === SUBSTITUTION ===
 (tassert "substitution constraint-ground fail" (run1 x1 (=/= x1 1) (== x1 1)) (void))
 (tassert "substitution constraint-ground succeed" (run1 x1 (=/= x1 1) (== x1 2)) 2)
 (tassert "substitution ground-constraint fail" (run1 x1 (=/= x1 1) (== 1 x1)) (void))
 (tassert "substitution ground-constraint succeed" (run1 x1 (=/= x1 1) (== 2 x1)) 2)
 (tassert "substitution constraint-bound fail" (run1 x1 (== x1 1) (=/= x1 1)) (void))
 (tassert "substitution constraint-bound succeed" (run1 x1 (== x1 2) (=/= x1 1)) 2)
 (tassert "substitution bound-constraint fail" (run1 x1 (== 1 x1) (=/= x1 1)) (void))
 (tassert "substitution bound-constraint succeed" (run1 x1 (== 2 x1) (=/= x1 1)) 2)
 (tassert "substitution constraint-free" (run1 (x1 x2) (=/= x1 1) (== x1 x2)) (list (=/= x2 1) (=/= x2 1)))
 (tassert "substitution constraint-free high var" (run1 (x1 x2) (=/= x2 1) (== x1 x2)) (list (=/= x2 1) (=/= x2 1)))
 (tassert "substitution free-constraint" (run1 (x1 x2) (=/= x1 1) (== x2 x1)) (list (=/= x2 1) (=/= x2 1)))
 (tassert "substitution free-constraint high var" (run1 (x1 x2) (=/= x2 1) (== x2 x1)) (list (=/= x2 1) (=/= x2 1)))

 (tassert "substitution constraint-constraint" (run1 x1 (=/= x1 1) (=/= x1 2)) (conj (=/= x1 2) (=/= x1 1)))
 (tassert "substitution constraint-constraint-free" (run1 (x1 x2) (=/= x1 1) (=/= x2 2) (== x1 x2)) (list (conj (=/= x2 1) (=/= x2 2)) (conj (=/= x2 1) (=/= x2 2))))
 (tassert "substitution constraint-constraint-free2" (run1 (x1 x2) (=/= x1 1) (=/= x2 2) (== x2 x1)) (list (conj (=/= x2 1) (=/= x2 2)) (conj (=/= x2 1) (=/= x2 2))))
 (tassert "substitution constraint disunify free" (run1 (x1 x2) (=/= x1 1) (=/= x1 x2)) (list (conj (=/= x1 x2) (=/= x1 1)) (proxy x1)))
 (tassert "substitution constraint disunify free2" (run1 (x1 x2) (=/= x2 1) (=/= x1 x2)) (list (=/= x1 x2) (conj (=/= x2 1) (proxy x1))))

 (tassert "substitution pconstraint-ground fail" (run1 x1 (symbolo x1) (== x1 1)) (void))
 (tassert "substitution ground-pconstraint fail" (run1 x1 (== x1 1) (symbolo x1)) (void))
 (tassert "substitution pconstraint-ground succeed" (run1 x1 (symbolo x1) (== x1 'symbol)) 'symbol)
 (tassert "substitution ground-pconstraint succeed" (run1 x1 (== x1 'symbol) (symbolo x1)) 'symbol)
 (tassert "substitution pconstraint-constraint" (run1 x1 (symbolo x1) (=/= x1 1)) (symbolo x1))
 (tassert "substitution constraint-pconstraint" (run1 x1 (=/= x1 1) (symbolo x1)) (symbolo x1))

 (tassert "eq? variables must not unify when constrained" (run1 x1 (=/= x1 1) (== x1 x1)) (=/= x1 1))
 (tassert "eq? variables must not disunify when constrained" (run1 x1 (=/= x1 1) (=/= x1 x1)) (void))
 
 ;; === ATTRIBUTED VARIABLES ===

 (tassert "disequalities attribute only to first var" (run1 (x1 x2) (=/= (cons x1 x2) '(1 . 2))) (list (disj (=/= x1 1) (=/= x2 2)) x2))

 (tassert "disj of disequalities attribute only to first var" (run1 (x1 x2) (disj (=/= x1 1) (=/= x2 2))) `(,(disj (=/= x1 1) (=/= x2 2)) ,x2))


 ;; Single variable
 (tassert "attribute x1=1=>x1=/=x1=>fail" (run1 x1 (disj (=/= x1 1) (== x1 2))) (disj (=/= x1 1) (== x1 2))) ; TODO can we simplify disjunctions of == and =/= of the same var? technically should be simplified to x1 =/= 1
 (tassert "attribute to negation if second and promote" (run1 x1 (disj (== x1 1) (=/= x1 1))) (disj (== x1 1) (=/= x1 1)))
 (tassert "attribute ~1=>2,~2=>1" (run1 x1 (disj (== x1 1) (== x1 2))) (disj (== x1 1) (== x1 2)))

 ;; Multi variable
 (tassert "attribute ~x1=>x2, ~x2=>x1" (run1 (x1 x2) (disj (== x1 1) (== x2 2)))
          (list (disj (== x1 1) (== x2 2)) x2)) 
 (tassert "attribute x1=>x2, ~x2=>x1" (run1 (x1 x2) (disj (== x1 1) (conj (== x1 1) (== x2 2)))) (list (disj (== x1 1) (conj (== x1 1) (== x2 2))) x2))
 (tassert "attribute x1=>x2, x2=>x1" (run1 (x1 x2 x3) (disj (conj (== x1 1) (== x2 2)) (== x3 3)))
          (list (disj (conj (== x1 1) (== x2 2)) (== x3 3))
                (proxy x1)
                x3))
 (tassert "attribute == =/=" (run1 (x1 x2) (disj (== x1 1) (=/= x2 2)))
          (list (disj (== x1 1) (=/= x2 2)) x2))
 (tassert "attribute =/= ==" (run1 (x1 x2) (disj (=/= x2 2) (== x1 1)))
          (list x1 (disj (=/= x2 2) (== x1 1))))
 

 ;; Multi variable with negation
 (tassert "attribute x1:x1=1=>x2=2" (run1 (x1 x2) (disj (=/= x1 1) (== x2 2)))
          (list (disj (=/= x1 1) (== x2 2)) x2))
 
 (tassert "attribute x1:x1=1=>x2=2, x3:x3~3=>x2=2, x2:x2~2=>x3=3" (run1 (x1 x2 x3) (disj (conj (=/= x1 1) (== x3 3)) (== x2 2)))
          (list (disj (conj (=/= x1 1) (== x3 3)) (== x2 2))
                x2
                (proxy x1)))

 ;; Multi variable with fresh
 (tassert "attribute x1:~x1=>x2=2" (run1 (x1 x2) (disj (matcho ([(a . d) x1])) (== x2 2)))
          (lambda (a) (and (disj? (car a)) (matcho? (disj-lhs (car a))) (equal? (disj-rhs (car a)) (== x2 2)) (equal? x2 (cadr a)))))
 
 ;; === SOLVER ===
 (tassert "constraint ==" (run1 x1 (constraint (== x1 1))) 1)
 (tassert "constraint =/=" (run1 x1 (constraint (=/= x1 1))) (=/= x1 1))
 (tassert "constraint fail|succeed" (run1 x1 (constraint (conde [(== x1 1) (== x1 2)] [(== 3 3)]))) x1)
 (tassert "constraint fail|==" (run1 x1 (constraint (conde [(== x1 1) (== x1 2)] [(== x1 3)]))) 3)
 (tassert "constraint ==|== ==" (run1 x1 (constraint (conde [(== x1 1)] [(== x1 2)])) (constraint (== x1 1))) 1)
 (tassert "constraint =/= ==|==" (run1 x1 (constraint (=/= x1 1)) (constraint (conde [(== x1 1)] [(== x1 2)]))) 2)
 (tassert "constraint ==|== =/=" (run1 x1 (constraint (conde [(== x1 1)] [(== x1 2)])) (constraint (=/= x1 1))) 2)
 (tassert "constraint &" (run1 (x1 x2) (== x1 1) (=/= x2 2)) (list 1 (=/= x2 2)))
 (tassert "constraint |" (run1 x1 (constraint (conde ((== x1 1)) ((== x1 2))))) (disj* (== x1 1) (== x1 2)))
 (tassert "constraint == fail|==" (run1 (x1 x2) (constraint (== x1 1)) (constraint (conde ((== x1 2)) ((== x2 2))))) '(1 2))
 (tassert "constraint == succeed|==" (run1 (x1 x2) (constraint (== x1 1)) (constraint (conde ((== x1 1)) ((== x2 2))))) (list 1 x2))


 (tassert "constraint == ==|fail" (run1 (x1 x2) (constraint (== x1 1)) (constraint (conde ((== x2 2)) ((== x1 2))))) (list 1 (disj (== x2 2) (== x1 2))))
 (tassert "constraint == ==|succeed" (run1 (x1 x2) (constraint (== x1 1)) (constraint (conde ((== x2 2)) ((== x1 1))))) (list 1 (disj (== x2 2) (== x1 1))))
 (tassert "constraint == ==|succeed(out)" (run1 (x1 x2 x3) (constraint (== x1 1)) (constraint (== x3 3) (conde ((== x2 2)) ((== x1 1))))) (list 1 (disj (== x2 2) (== x1 1)) 3))
 (tassert "constraint == ==|==|=="
          (run1 (x1 x2 x3) (constraint (== x3 1))
                (constraint (conde ((== x1 x3)) ((== x2 x3)) ((== x1 x3)))))
          (list (disj (disj (== x1 1) (== x2 x3)) (== x1 x3)) x2 1))
 #;
 (parameterize ([lazy-solver #t])
 (tassert "constraint == ==|==|=="
 (run1 (x1 x2 x3) (constraint (== x3 1))
 (constraint (conde ((== x1 x3)) ((== x2 x3)) ((== x1 x3)))))
 (list (disj (disj (== x1 1) (== x2 1)) (== x1 x3)) (proxy x1) 1)))
 (tassert "constraint ==|== ==" (run1 x1 (constraint (conde ((== x1 1)) ((== x1 2)))) (constraint (== x1 1))) 1)
 (tassert "constraint =/=|=/= ==" (run1 x1 (constraint (disj* (=/= x1 1) (=/= x1 2))) (constraint (== x1 1))) 1)
 (tassert "constraint =/=|=/= ==2" (run1 (x1 x2) ; =/= dont need to simplify, so just apply the == and move on
                                         (constraint (disj* (=/= x1 1) (=/= x2 1)))
                                         (constraint (== x2 1)))
          (list (disj* (=/= x1 1) (=/= x2 1)) 1))

 (tassert "constraint simplification lvl 2" (run1 (x1 x2 x3 x4) (constraint (== x4 1)) (constraint (conde ((== x1 x4)) ((== x2 x4)) ((== x3 x4)))))
          (list (disj (disj (== x1 1) (== x2 x4)) (== x3 x4)) x2 x3 1))
 #;
 (parameterize ([lazy-solver #t])
 (tassert "constraint simplification lvl 2" (run1 (x1 x2 x3 x4) (constraint (== x4 1)) (constraint (conde ((== x1 x4)) ((== x2 x4)) ((== x3 x4)))))
 (list (disj (disj (== x1 1) (== x2 1)) (== x3 x4)) (proxy x1) x3 1)))
 (tassert "constraint =/=* fails &== failing all =/=" (run1 (x1 x2) (== x1 1) (== x2 2) (constraint (=/= (cons x1 x2) '(1 . 2)))) (void))
 (tassert "disj head disj preserves ctn" (run1 (x1 x2) (constraint (disj* (constraint (disj* (=/= x1 1) (=/= x1 1))) (== x1 1)) (== x2 2)) (== x1 1)) '(1 2))
 (tassert "disj preserves ctn" (run1 (x1 x2) (constraint (disj* (=/= x1 1) (=/= x1 1) (== x1 1)) (== x2 2)) (== x1 1)) '(1 2))
 
 (tassert "disj only walks 1st disjunct if no ==" (run1 (x1 x2) (== x2 2) (constraint (conde [(=/= x1 1)] [(=/= x2 2)]))) (list (disj (=/= x1 1) (=/= x2 2)) 2))
 #;
 (parameterize ([lazy-solver #t])
 (tassert "disj only walks 1st disjunct if no ==" (run1 (x1 x2) (== x2 2) (constraint (conde [(=/= x1 1)] [(=/= x2 2)]))) (list (disj (=/= x1 1) (=/= x2 2)) 2)))

 ;; === STORE ===
 #;
 (tassert "normalized constraints removed when further solved" (run1 (x1 x2 x3) (disj (conj (make-matcho4 (list x1 x2) '() #f) (== x1 x3)) (=/= x1 1))) (list (disj (=/= x1 1) (conj (== x1 x2) matcho-x3-x2) ) x2 x3))

 
 ;; === DISEQUALITY ===

 (tassert "disunify ground-self" (run* (q) (=/= 2 2)) '())
 (tassert "disunify ground-different" (run* () (=/= 1 2)) '(()))
 (tassert "disunify free-self" (run* (x1) (=/= x1 x1)) '())
 (tassert "disunify free-ground" (run1 x1 (=/= x1 1)) (=/= x1 1))
 (tassert "disunify ground-free" (run1 x1 (=/= 1 x1)) (=/= x1 1))
 (tassert "disunify free-free" (run1 (x1 x2) (=/= x1 x2)) (list (=/= x1 x2) (proxy x1)))
 (tassert "disunify bound" (run* (x1) (== x1 1) (=/= x1 1)) '())
 (tassert "disunify check" (run* (x1) (=/= x1 1) (== x1 1)) '())
 (tassert "disunify free-ground x2" (run1 x1 (=/= x1 1) (=/= x1 2)) (conj (=/= x1 2) (=/= x1 1)))
 (tassert "disunify transfer to free then check" (run* (x1 x2) (=/= x1 2) (== x1 x2) (== x2 2)) '())
 (tassert "disunify lists" (car (run1 (x1 x2) (=/= (cons x1 x2) (cons 1 2)))) (disj* (=/= x1 1) (=/= x2 2)))
 (tassert "disunify fire lists" (run1 (x1 x2) (=/= (cons x1 x2) (cons 1 2)) (== x1 1)) (list 1 (=/= x2 2)))
 (tassert "disunify fire lists and fail" (run* (x1 x2) (=/= (cons x1 x2) (cons 1 2)) (== x1 1) (== x2 2)) '())
 (tassert "disunify simultaneous list diseq" (run* (x1 x2) (=/= (cons x1 x2) (cons 1 2)) (== (cons x1 x2) (cons 1 2))) '())
 (tassert "disunify simultaneous list diseq, fail on first" (run* (x1 x2) (=/= x1 1) (== (cons x1 x2) (cons 1 2))) '())
 (tassert "disunify simultaneous list diseq, fail on second" (run* (x1 x2) (=/= x2 2) (== (cons x1 x2) (cons 1 2))) '())
 (tassert "disunify transfer on free-free up varid" (run1 (x1 x2) (=/= x1 1) (== x1 x2)) (list (=/= x2 1) (=/= x2 1)))
 (tassert "disunify transfer on free-free down varid" (run1 (x1 x2) (=/= x2 1) (== x2 x1)) (list (=/= x2 1) (=/= x2 1)))
 (tassert "disunify fire low varid" (run1 (x1 x2) (=/= x1 x2) (== x2 x1)) (void))
 (tassert "disunify conj" (run1 (x1 x2) (=/= x1 1) (=/= x2 2) (== x1 x2))
          (list (conj (=/= x2 1) (=/= x2 2)) (conj (=/= x2 1) (=/= x2 2))))
 (tassert "disunify fire low varid" (run1 (x1 x2) (== x2 1) (=/= x1 1) (== x1 x2)) (void))
 (tassert "disunify fire high varid" (run1 (x1 x2) (== x1 1) (=/= x2 1) (== x1 x2)) (void))
 (tassert "disunify fired constraints restored on failure" (run1 x1 (disj (== x1 1) (== x1 1)) (=/= (list x1 x1) '(1 1))) (void))
 (tassert "disunify disjunction builds continuation" (run1 x1 (disj (== x1 1) (== x1 2)) (=/= (list x1 x1) '(3 3)))
          (disj (== x1 1) (== x1 2)))
 (tassert "disunify disjunction runs ctn" (run1 x1 (constraint (=/= (list x1 x1) '(1 1)) (== x1 1))) (void))
 (tassert "disunify disjunction runs ctn" (run1 x1 (constraint (=/= (list x1 x1) '(1 1)) (== x1 1))) (void))

 (tassert "disunify simplify simple abort" (run1 x1 (=/= x1 1) (=/= x1 1)) (=/= x1 1))
 (tassert "disunify simplify ignores conj" (run1 x1 (=/= x1 1) (=/= x1 2) (=/= x1 3)) (conj (=/= x1 3) (conj (=/= x1 2) (=/= x1 1))))
 (tassert "disunify simplify conj early succeed" (run1 x1 (conj (=/= x1 1) (=/= x1 2)) (=/= x1 1)) (conj (=/= x1 2) (=/= x1 1)))
 (tassert "disunify simplify abort pconstraint" (run1 x1 (symbolo x1) (=/= x1 1)) (symbolo x1))    
 (tassert "disunify simplify ignore pconstraint" (run1 x1 (numbero x1) (=/= x1 1)) (conj (=/= x1 1) (numbero x1)))
 (tassert "disunify simplify abort negative pconstraint" (run1 x1 (noto (numbero x1)) (=/= x1 1)) (noto (numbero x1)))
 (tassert "disunify simplify match succeed" (run1 x1 (constraint (matcho ([(a . d) x1]))) (=/= x1 1)) (lambda (c) (matcho? c)))
 (tassert "disunify simplify match" (run1 x1 (constraint (matcho ([(a . d) x1]))) (=/= x1 '(1 . 2))) (lambda (c) (and (conj? c) (equal? (conj-lhs c) (=/= x1 '(1 . 2))) (matcho? (conj-rhs c)))))
 (tassert "disunify simplify negative matcho" (run1 x1 (constraint (noto (matcho ([(a . d) x1])))) (=/= x1 1)) (lambda (c) (and (conj? c) (matcho? (noto-goal (conj-rhs c))) (equal? (conj-lhs c) (=/= x1 1)))))
 (tassert "disunify simplify disjunction fails first" (run1 (x1 x2) (disj (== x2 2) (== x1 1)) (=/= x1 1)) (list (=/= x1 1) (disj (== x2 2) (== x1 1))))
 (tassert "disunify simplifies secondary constraint if primary is val" (run1 (x1 x2) (== x1 1) (disj (== x2 1) (== x2 2)) (=/= x1 x2)) '(1 2))
 (tassert "disunify suspends and preserves whole ctn" (run1 (x1 x2 x3) (constraint (=/= (cons x1 x2) '(())) (== x3 1))) (list (disj (=/= x1 '()) (=/= x2 '())) x2 1))
 (tassert "disunify preserves pending goals in ctn" (run1 (x1 x2) (constraint (=/= x1 1) (disj (=/= x2 1) (=/= x2 2)))) (list (=/= x1 1) (disj (=/= x2 1) (=/= x2 2))))
 (tassert "disunify simplify drops when =/= in a conj" (run1 x1 (disj (conj (=/= x1 1) (conj (numbero x1) (=/= x1 1))) (=/= x1 2))) (disj (conj (=/= x1 1) (numbero x1)) (=/= x1 2)))
 (tassert "disunify occurs check" (run1 x1 (=/= x1 (list x1))) x1)
 (tassert "=/= quiescent even with unnormalized vars" (run1 (x1 x2 x3) (=/= x1 x2) (=/= x1 x3)) (list (conj (=/= x1 x3) (=/= x1 x2)) (proxy x1) (proxy x1)))
 (tassert "=/= stored constraints recheck disj =/=" (run1 (x1 x2) (disj (== x1 1) (== x1 1)) (disj (=/= x1 1) (=/= x2 2))) (list (disj (== x1 1) (== x1 1)) (=/= x2 2)))
 ;(tassert "disunify disjunctions from lists simplify" (run1 (x1 x2) (=/= (list x1 x1) '(1 1)) (=/= (list x1 x2) '(1 2))) (list (disj (=/= x1 1) (=/= (list x1) '(1))) x2))
 (tassert "=/= stored constraints simplify disj =/=" (run1 (x1 x2) (disj (== x1 1) (== x1 1)) (=/= (list x1 x2) '(1 2))) (list (disj (== x1 1) (== x1 1)) (=/= x2 2)))

 ;; === EQUALITY ===
 
 (tassert "==-c ground-self" (run1 x1 (constraint (== 1 1))) x1)
 (tassert "==-c ground-different" (run1 x1 (constraint (== 1 2))) (void))
 (tassert "==-c free-ground" (run1 x1 (constraint (== x1 1))) 1)
 (tassert "==-c bound-ground-same" (run1 x1 (== x1 1) (constraint (== x1 1))) 1)
 (tassert "==-c bound-ground-different" (run1 x1 (== x1 2) (constraint (== x1 1))) (void))
 (tassert "==-c ground-bound-same" (run1 x1 (constraint (== x1 1)) (== x1 1)) 1)
 (tassert "==-c ground-bound-different" (run1 x1 (constraint (== x1 1)) (== x1 2)) (void))
 (tassert "==-c x ==-c conflict" (run1 x1 (constraint (== x1 1)) (constraint (== x1 2))) (void))
 (tassert "==-c x ==-c no conflict" (run1 x1 (constraint (== x1 1)) (constraint (== x1 1))) 1)
 (tassert "==-c & ==-c conflict" (run1 x1 (constraint (conj* (== x1 2) (== x1 1)))) (void))
 (tassert "==-c & ==-c no conflict" (run1 x1 (constraint (conj* (== x1 1) (== x1 1)))) 1)
 (tassert "==-c x =/=-c conflict" (run1 x1 (=/= x1 1) (constraint (== x1 1))) (void))
 (tassert "==-c x =/=-c no conflict" (run1 x1 (=/= x1 2) (constraint (== x1 1))) 1)
 (tassert "==-c | ==-c" (run1 x1 (constraint (disj* (== x1 1) (== x1 2)))) (disj (== x1 1) (== x1 2)))
 (tassert "==-c | ==-c attributes" (run1 (x1 x2) (constraint (disj* (== x1 1) (== x2 2)))) (list (disj (== x1 1) (== x2 2)) x2))
 (tassert "==-c | ==-c simplifies bound"
          (run1 (x1 x2) (== x1 1) (constraint (disj* (== x1 1) (== x2 2)))) (list 1 x2))
 (tassert "==-c | ==-c transfers bound"
          (run1 (x1 x2) (== x1 3) (constraint (disj* (== x1 1) (== x2 2)))) (list 3 2))
 

 ;; === DISJUNCTION ===

 (tassert "== factored out of disj" (run1 x1 (disj (== x1 1) (== x1 1))) (disj (== x1 1) (== x1 1)))
 (tassert "== factored out of nested disj" (run1 (x1 x2) (== x2 2) (disj (conj (== x2 2) (disj (== x1 1) (== x1 1))) (== x2 3))) (list (disj (disj (== x1 1) (== x1 1)) (== x2 3)) 2))
 (tassert "== factored out of nested disj tail" (run1 (x1 x2) (== x2 2) (disj (== x1 1) (conj (== x2 2) (disj (== x1 1) (== x1 1))))) (list (disj (== x1 1) (conj (== x2 2) (disj (== x1 1) (== x1 1)))) 2))
 (tassert "nested disj terminates disj solving" (run1 (x1 x2) (== x2 2) (disj (== x1 1) (conj (== x2 2) (disj (== x1 2) (== x1 1))))) (list (disj (== x1 1) (conj (== x2 2) (disj (== x1 2) (== x1 1)))) 2))
 (tassert "=/= & (=/=|succeed)" (run1 x1 (disj (numbero x1) (symbolo x1)) (=/= x1 1)) (conj (=/= x1 1) (disj (numbero x1) (symbolo x1))))
 (tassert "disj common non == are extracted" (run1 x1 (disj (=/= x1 1) (=/= x1 1))) (disj (=/= x1 1) (=/= x1 1)))
 (tassert "stale constraints on multiple vars are ignored when stored" (run1 (x1 x2) (disj (== x1 1) (conj (== x1 2) (== x2 3))) (== x1 1) (== x2 3)) '(1 3))
 (tassert "disj factors ==s already in store" (run1 (x1 x2) (disj (== x1 1) (== x2 2)) (disj (== x1 1) (=/= x2 2))) (list (conj (disj (== x1 1) (== x2 2)) (disj (== x1 1) (=/= x2 2))) x2))

 ;; === NOTO ===
 (tassert "noto continues to solve pending constraints" (run1 (x1 x2 x3) (== x1 1) (== x2 (cons x3 x3)) (noto (matcho ([(a . d) x2]) (disj (=/= x3 3) (== x1 2))))) '(1 (3 . 3) 3))
 (tassert "noto does not negate rechecked constraints" (run1 (x1 x2) (disj (== x1 1) (== x2 2)) (noto (symbolo x1))) (list (conj (disj (== x1 1) (== x2 2)) (noto (symbolo x1))) x2))
 (tassert "absento failed because match wasn't eager" (run1 (x1 x2) (noto (absento x2 (list x1 '()))) (== x1 1) (== x2 3)) (void))
 (tassert "repeatedly solved constraints deduplicate" (run1 (x1 x2) (disj (conj (=/= x1 1) (== x1 x2)) (== x1 1))) (list (disj (conj (=/= x1 1) (== x1 x2)) (== x1 1)) x2))

 ;; === PCONSTRAINT ===
 (tassert "pconstraint rechecks if not normalized" (run1 (x1 x2) (disj (conj (numbero x1) (numbero x2)) (symbolo x1)) (== x2 2) (== x1 1)) '(1 2))
 (tassert "proxy constraints eq? value even when vars not unified"
          (run1 (x1 x2 x3) (pconstraint (list x1 x2 x3) (lambda (x y x-c y-c p) p) #f) (== x2 x3))
          (lambda (s) (and (pconstraint? (car s)) (conj? (cadr s)) (eq? (cadr s) (caddr s)))))
 (tassert "pconstraint stale var" (run1 (x1 x2)  (== x1 x2) (== x1 'symbol) (symbolo x1)) '(symbol symbol))

 
 ;; === MATCH ===
 ;;(tassert "match doesnt blend" (caddr (run1 (x1 x2 x3) (== x1 (cons x2 x3)) (absento 'closure x1))) 1)
 (tassert "match doesn't overwrite =/=" (run1 x1 (=/= x1 '(())) (matcho ([(a . d) x1]) (== a 1) (== d 2))) '(1 . 2))

 ;; === REDUCTIONS ===
 (tassert "reduce == simplifies =/=" (run1 (x1 x2) (=/= x2 1) (== x1 x2)) (list (=/= x2 1) (=/= x2 1)))
 (tassert "reduce == simplifies =/= ctn" (run1 (x1 x2) (constraint (== x1 x2) (=/= x2 1))) (list (=/= x2 1) (=/= x2 1)))
 (tassert "reduce == simplifies =/= inverse" (run1 (x1 x2) (constraint (== x1 x2) (=/= 1 x2))) (list (=/= x2 1) (=/= x2 1)))
 (tassert "reduce == =/= fail" (run1 (x1 x2) (constraint (== x1 x2) (=/= x1 x2))) (void))
 (tassert "reduce == rechecks =/=" (run1 (x1 x2) (=/= x2 2) (== x1 1)) (list 1 (=/= x2 2)))
 (tassert "reduce == rechecks =/= ctn" (run1 (x1 x2) (constraint (== x1 1) (=/= x2 2))) (list 1 (=/= x2 2)))
 (tassert "reduce == partitions ctn and recheck" (run1 (x1 x2 x3 x4) (== x1 (cons x2 3)) (=/= x2 x4) (constraint (noto (matcho ([(a . b) x1]) (== a x3))))) (list (cons (conj (=/= x2 x3) (=/= x2 x4)) 3) (conj (=/= x2 x3) (=/= x2 x4)) (proxy x2) (proxy x2)))
 (tassert "reduce == stores pending rechecks in state" (run1 (x1 x2) (disj (disj (== x1 1) (== x2 2)) (== x2 3)) (== x1 4)) (list 4 (disj (== x2 2) (== x2 3))))
 
 ;;(tassert "reduce == simplifies proxy" (run1 (x1 x2) (disj (== x1 1) (== x2 2)) (== x1 x2)) (list (disj (== x2 1) (== x2 2)) (disj (== x2 1) (== x2 2)))) ;TODO remove proxies from secondary vars in ==

 ;; === RECHECK ===

                                        ;(trace-run* (x1 x2 x3) (disj (== x2 3) (== x3 3)) (disj (== x1 2) (== x2 2)) (== x1 1))
 
 )
