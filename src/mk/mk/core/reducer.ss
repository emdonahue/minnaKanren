;; Constraint normalizer that simplifies constraints using only information contained mutually among the collection of constraints--no walking or references to variable bindings in the substitution. Used as an optimization in the solver to extract what information can be extracted from constraints before continuing with full solving using the substitution.
(library (mk core reducer)
  (export reduce-constraint)
  (import (chezscheme) (mk core goals) (mk core mini-substitution) (mk core utils) (mk core variables) (mk core streams) (mk core matcho))
  ;; TODO test whether we need 2 var eq with: x == y | ... AND y == z (or z == y) | ... AND x=/=z

  (define (==->substitution g)
    (cert (==? g) (var? (==-lhs g)))
    (list (cons (==-lhs g) (==-rhs g))))

  (define (=/=->substitution g) ; To fully reduce =/=, we must unroll possibly list disequalities the disunifier lazily ignored.
    (cert (=/=? g)) 
    (mini-unify '() (=/=-lhs g) (=/=-rhs g)))

  (define (maybe-fail e r)
    (if (or (fail? e) (fail? r)) (values fail fail) (values e r)))
  
  (define (vouch e e-normalized r-normalized r)
    (if (fail? e) (values fail fail)
        (if (or e-normalized (and r-normalized (vouches? r e))) (values e succeed) (values succeed e))))
  
  (define (vouches? r e)
    (cert (or (goal? r) (mini-substitution? r)) (goal? e))
    (or (succeed? r)
     (if (mini-substitution? r)
         (for-all (lambda (v) (mini-normalized? r v)) (normalized-vars e))
         (let ([n-vars (normalized-vars r)])
           (for-all (lambda (v) (member v n-vars)) (normalized-vars e))))))
  
  
  ;; === REDUCEE ===
  (define reduce-constraint ; Reduce constraint e (reduceE) using the information contained in constraint r (reduceR).
    (case-lambda
      [(e r) (reduce-constraint e r #t)]
      [(e r e-free) (reduce-constraint e r e-free #f e-free (not e-free))]
      [(e r e-free r-disjunction e-normalized r-normalized)
       (cert (goal? e) (or (fail? e) (not (fail? r))) (or (goal? r) (mini-substitution? r))) ; -> simplified recheck
       (exclusive-cond
        [(succeed? r) (values e succeed)] ; Succeed can only come from an empty store default so we know e is normalized.
        [(disj? r) (disj-reducer r e)]
        [(conj? r) (conj-reducer e r e-free r-disjunction e-normalized r-normalized)]
        [else
         (exclusive-cond
          [(or (fail? e) (succeed? e)) (values e e)]
          [(conj? e) (reduce-conj e r e-free r-disjunction e-normalized r-normalized)]
          [(disj? e) (disj-reducee e r e-free r-disjunction e-normalized r-normalized)]
          [(and (noto? e) (not (=/=? e))) (reduce-noto e r e-free r-disjunction e-normalized r-normalized)]
          [(constraint? e) (reduce-constraint (constraint-goal e) r e-free r-disjunction e-normalized r-normalized)]
          [(and (=/=? e) (pair? (=/=-lhs e)))
           (reduce-constraint (mini-disunify '() (=/=-lhs e) (=/=-rhs e)) r e-free r-disjunction e-normalized r-normalized)]
          [(proxy? e) (constraint-reduce e r #f r-disjunction #f r-normalized)] ; Proxies are never normalized bc they can't be stored. They can only be rechecked. They are also never free.
          [else (constraint-reduce e r e-free r-disjunction e-normalized r-normalized)])])]))

  (define (disj-reducer r e)
    (cert (disj? r))
    (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint e (disj-lhs r) #t)]
                 [(simplified-rhs recheck-rhs) (reduce-constraint e (disj-rhs r) #t)])
      (if (and (equal? simplified-lhs simplified-rhs) (equal? recheck-lhs recheck-rhs)) (values simplified-lhs recheck-lhs) ; We can only reduce if all disjuncts reduce the same way so it won't matter which ends up being true.
          (values e succeed))))

  (define (conj-reducer e r e-free r-disjunction e-normalized r-normalized)
    (cert (conj? r))
    (let-values ([(simplified recheck) (reduce-constraint e (conj-lhs r) e-free r-disjunction e-normalized r-normalized)])
      (if (and (trivial? simplified) (trivial? recheck))
          (maybe-fail simplified recheck)
          (let-values ([(simplified/simplified simplified/recheck) (reduce-constraint simplified (conj-rhs r) e-free r-disjunction e-normalized r-normalized)])
            (if (fail? simplified/simplified) (values fail fail)
                (let-values ([(recheck/simplified recheck/recheck) (reduce-constraint recheck (conj-rhs r) e-free r-disjunction e-normalized r-normalized)])
                  (maybe-fail simplified/simplified
                              (conj simplified/recheck (conj recheck/simplified recheck/recheck)))))))))
  
  #;
  (define (conj-reducer e r e-free r-disjunction e-normalized r-normalized) ; ; ;
  (cert (conj? r))                      ; ; ;
  (let*-values ([(simplified recheck) (reduce-constraint e (conj-lhs r) e-free r-disjunction e-normalized r-normalized)] ; ; ;
  [(simplified/simplified simplified/recheck) (reduce-constraint simplified (conj-rhs r) e-free r-disjunction e-normalized r-normalized)] ; ; ;
  [(recheck/simplified recheck/recheck) (reduce-constraint recheck (conj-rhs r) e-free r-disjunction e-normalized r-normalized)]) ; ; ;
  (maybe-fail (conj simplified/simplified (conj simplified/recheck recheck/simplified)) recheck/recheck)))
  
  (org-define (=/=-reduce2 r e)
              ;; =/=,=/= -> succeed | =/=,=/=
              ;; =/=,==|... -> =/=,fail|...
              ;; =/=,=/=|... -> =/=,fail|...
              ;; what should we do where =/= & =/=|=/=... could extract the =/= from each branch of the | and simplify it, but it would mean overwriting things? probably we shouldnt try to check that something satisfies all branches and just nuke the branches one by one, which is also a cleaner final expression. 
              ;; =/= can only simplify ==->fail and =/=->succeed
              (exclusive-cond
               [(==? e) ; -> fail?. Simple equality check ok because 1) we ignore list unifications for performance reasons, constants will already succeed or fail, and == orders vars by id
                succeed
                                        ;(vouch (if (equal? e (noto-goal r)) fail e) e-normalized r-normalized (noto-goal r))
                ]
               [else (assertion-violation '=/=-reduce "Unrecognized constraint type" e)]))

  (define (reduce-conj e r e-free r-disjunction e-normalized r-normalized)
    (cert (conj? e))
    (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (conj-lhs e) r e-free r-disjunction e-normalized r-normalized)])
      (if (fail? simplified-lhs) (values fail fail)
          (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (conj-rhs e) r e-free r-disjunction e-normalized r-normalized)])
            (values (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs))))))

  (define (disj-reducee e r e-free r-disjunction e-normalized r-normalized)
    (cert (disj? e))
    (let-values ([(simplified-lhs recheck-lhs) (reduce-constraint (disj-lhs e) r e-free r-disjunction e-normalized r-normalized)])
      (exclusive-cond
       [(and (succeed? simplified-lhs) (succeed? recheck-lhs)) (values succeed succeed)] ; Succeed if all disjuncts succeed.
       [(fail? simplified-lhs) ; If the first disjunct fails, the remainder may be unnormalized and must be rechecked.
        (let-values ([(simplified-rhs recheck-rhs)
                      (reduce-constraint (disj-rhs e) r e-free r-disjunction #f r-normalized)])
          (maybe-fail succeed (conj simplified-rhs recheck-rhs)))]
       [else ; Recheck if lhs needs recheck (since attr vars are based on lhs) or if the disj collapses (may need to redistribute conjuncts). 
        (let-values ([(simplified-rhs recheck-rhs) (reduce-constraint (disj-rhs e) r e-free r-disjunction #f r-normalized)]) 
          (let ([d (disj (conj simplified-lhs recheck-lhs) (conj simplified-rhs recheck-rhs))]) 
            (if (and (trivial? recheck-lhs) (disj? d)) (maybe-fail d succeed) (maybe-fail succeed d))))])))
  
  (define (reduce-noto e r e-free r-disjunction e-normalized r-normalized)
    (let-values ([(simplified recheck) (reduce-constraint (noto-goal e) r e-free r-disjunction e-normalized r-normalized)])
      (vouch (disj (noto simplified) (noto recheck)) e-normalized (and r-normalized (succeed? recheck)) succeed)))

  ;; === REDUCER ===
  (define (constraint-reduce e r e-free r-disjunction e-normalized r-normalized)
    (exclusive-cond
     [(list? r) (==-reducer e r e-free r-disjunction e-normalized r-normalized)]
     [(==? r) (==-reducer e (==->substitution r) e-free r-disjunction e-normalized r-normalized)]
     [(=/=? r) (=/=-reduce e r e-free r-disjunction e-normalized r-normalized)]
     [(pconstraint? r) (pconstraint-reduce e r e-free r-disjunction e-normalized r-normalized)]
     [(noto? r) (noto-reduce e (noto-goal r) e-free r-disjunction e-normalized r-normalized)]
     [(matcho? r) (matcho-reduce e r e-free r-disjunction e-normalized r-normalized)]
     [(proxy? r) (vouch e e-normalized #f succeed)] ; Proxies are never normalized and so can vouch for nothing
     [else (assertion-violation 'reduce-constraint "Unrecognized constraint type" (cons e r))]))

  (org-define (==-reducer e s e-free r-disjunction e-normalized r-normalized)
              (cert (goal? e) (mini-substitution? s)) ;TODO just be polymorphic with == and dont keep converting to minisub
              (exclusive-cond
               [(==? e) (let ([t (mini-unify s (==-lhs e) (==-rhs e))]) ; TODO does == x == ever come up in the reducer?
                          (cond
                           [(failure? t) (values fail fail)]
                           [(eq? s t) (values succeed succeed)] 
                           [else (values e succeed)]))

                #;
                (let-values ([(lhs-normalized? lhs) (mini-walk-normalized s (==-lhs e))] ; ; ; ;
                [(rhs-normalized? rhs) (mini-walk-normalized s (==-rhs e))]) ; ; ; ;
                (vouch (== lhs rhs) e-normalized (and r-normalized (var? lhs) lhs-normalized? rhs-normalized?) succeed))]
               [(=/=? e) (maybe-fail (mini-disunify s (=/=-lhs e) (=/=-rhs e)) succeed)

                #;
                (let-values ([(e r-vouches) (mini-disunify/normalized s (=/=-lhs e) (=/=-rhs e))]) ;
                (vouch e e-normalized (and r-normalized r-vouches) succeed))]
               [(matcho? e) (let-values ([(expanded? e ==s) (matcho/expand e s)])
                              (if expanded?
                                  (reduce-constraint (conj ==s e) s e-free r-disjunction #f r-normalized)
                                  (let-values ([(==s ==s/recheck) (reduce-constraint ==s s e-free r-disjunction #f r-normalized)]
                                               [(e e/recheck) (vouch e e-normalized r-normalized s)])
                                    (values (conj ==s e) (conj ==s/recheck e/recheck)))))]
               [(pconstraint? e) (==/pconstraint-reduce e s e-free r-disjunction e-normalized r-normalized)]
               [(proxy? e) ; If we can vouch that they have already been walked, discard. Otherwise we have to walk them (cant be stored). 
                (if (and r-normalized (mini-normalized? s (proxy-var e))) (values succeed succeed) (values succeed e))] 
               [else (assertion-violation '==-reducer "Unrecognized constraint type" e)]))

  (org-define (=/=-reduce e r e-free r-disjunction e-normalized r-normalized)
              ;; =/= can only simplify ==->fail and =/=->succeed
              (cert (=/=? r))
              (exclusive-cond
               [(==? e) ; -> fail?. Simple equality check ok because 1) we ignore list unifications for performance reasons, constants will already succeed or fail, and == orders vars by id
                (vouch (if (equal? e (noto-goal r)) fail e) e-normalized r-normalized (noto-goal r))]
               [(=/=? e)                        ; -> succeed, =/=
                (if (equal? e r) (values succeed succeed) ; Identical =/= can cancel
                    (values e succeed))]
               #;
               [(=/=? e)                          ; -> succeed, =/= ; ; ;
               (cert (not (pair? (=/=-lhs e))))  ; ; ; ;
               (if (and (not (and e-free r-disjunction)) (equal? e r)) ; If reducee is free and reducer is in a disjunction, we must negate our usual symmetric equality check and preserve the reducee so it can later simplify the reducer. ; ; ;
               (values succeed succeed)      ; Identical =/= can cancel ; ; ;
               (vouch e e-normalized (and r-normalized (not (and e-free r-disjunction))) (noto-goal r)))]
               [(matcho? e) (vouch e e-normalized r-normalized r)]
               [(pconstraint? e) (vouch e e-normalized r-normalized r)]
               [(proxy? e) (if (vouches? r e) (values succeed succeed) (values succeed e))]
               [else (assertion-violation '=/=-reduce "Unrecognized constraint type" e)]))
  
  (define (pconstraint-reduce e r e-free r-disjunction e-normalized r-normalized)
    (cert (pconstraint? r))
    (exclusive-cond
     [(==? e) (let-values ([(simplified recheck) (==/pconstraint-reduce r (==->substitution e) e-free r-disjunction e-normalized r-normalized)])
                (if (fail? simplified) (values fail fail) (vouch e e-normalized r-normalized r)))]
     [(=/=? e)                          ; -> succeed, =/=
      (let-values ([(simplified recheck) (==/pconstraint-reduce r (=/=->substitution e) e-free r-disjunction e-normalized r-normalized)])
        (if (fail? simplified) (values succeed succeed) (vouch e e-normalized r-normalized r)))]
     [else (assertion-violation 'pconstraint-reduce "Unrecognized constraint type" e)]))

  (define ==/pconstraint-reduce ;TODO extract an expander for pconstraints analagous to matcho/expand
    ;; Walk all variables of the pconstraint and ensure they are normalized.
    (case-lambda 
      [(e s e-free r-disjunction e-normalized r-normalized) (==/pconstraint-reduce e s e-free r-disjunction e-normalized r-normalized (pconstraint-vars e))]
      [(e s e-free r-disjunction e-normalized r-normalized vars)
       (if (null? vars) (vouch e e-normalized r-normalized succeed)
           (let ([v (mini-reify s (car vars))])
             (if (eq? (car vars) v) ; If any have been updated, run the pconstraint.
                 (==/pconstraint-reduce e s e-free r-disjunction e-normalized r-normalized (cdr vars))
                 (reduce-constraint ((pconstraint-procedure e) (car vars) v e succeed e) s e-free r-disjunction e-normalized r-normalized))))]))

  (org-define (matcho-reduce e r e-free r-disjunction e-normalized r-normalized)
              (exclusive-cond
               [(==? e) (if (failure? (mini-unify (matcho-substitution r) (==-lhs e) (==-rhs e)))
                            (values fail fail)
                            (vouch e e-normalized r-normalized r))]
               [(=/=? e)                ; -> succeed, =/=
                (let-values ([(d n?) (mini-disunify/normalized (matcho-substitution r) (=/=-lhs e) (=/=-rhs e))])
                  (org-display d n? (matcho-substitution r) e)
                  (if (succeed? d) (values succeed succeed) (vouch e e-normalized r-normalized r)))]
               ;;TODO matchos with eq? lambda can cancel
               [else (assertion-violation 'matcho-reduce "Unrecognized constraint type" e)]))

  (define (noto-reduce e r e-free r-disjunction e-normalized r-normalized)
    (let-values ([(simplified recheck) (reduce-constraint r (if (noto? e) (noto-goal e) e) e-free r-disjunction e-normalized r-normalized)])
      (if (and (succeed? simplified) (succeed? recheck))
          (if (noto? e) (values succeed succeed) (values fail fail))
          (vouch e e-normalized r-normalized r)))))
