(library (mk core solver) ; Central logic of the constraint solver
  (export run-constraint simplify-pconstraint)
  (import (chezscheme) (mk core unifier) (mk core goals) (mk core streams) (mk core variables) (mk core utils) (mk core mini-substitution) (mk core reducer) (mk core matcho) (mk core walk))

  ;; TODO define a (goal) form, dual to (consraint) that pushes constraints back up into the search. especially good inside matcho. similar functionality to original delayed goals paper

  (define (run-constraint g s)
    ;; Simplifies g as much as possible, and stores it in s. Primary interface for evaluating a constraint.
              (cert (goal? g) (maybe-state? s)) ; -> maybe-state?
    (let-values ([(delta s) (solve-constraint g s succeed succeed succeed)]) s))

  (org-define (solve-constraint g s ctn resolve delta)
    ;; Reduces a constraint as much as needed to determine failure and returns constraint that is a conjunction of primitive goals and disjunctions, and state already containing all top level conjuncts in the constraint but none of the disjuncts. Because we cannot be sure about adding disjuncts to the state while simplifying them, no disjuncts in the returned goal will have been added, but all of the top level primitive conjuncts will have, so we can throw those away and only add the disjuncts to the store.
    ;; resolve: constraints retrieved from the store that we need to recheck, but which should not be negated by noto on the return (so we cant just solve them immediately. we must delay rechecking until we are done with g).
    ;; delta: conjunction of all the simplified goals we have added to the store. reflects the change (delta) of the returned state's constraint store.
    (cert (goal? g) (maybe-state? s) (goal? ctn)) ; -> delta maybe-state?
    (if (failure? s) (values fail failure)
        (exclusive-cond
         [(fail? g) (values fail failure)]
         [(succeed? g) (solve-succeed s ctn resolve delta)]
         [(==? g) (solve-== g s ctn resolve delta)]
         [(and (=/=? g) (not (noto? g))) (nyi =/= solver)]
         [(noto? g) (solve-noto (noto-goal g) s ctn resolve delta)]
         [(disj? g) (solve-disj g s ctn resolve delta)]
         [(conde? g) (solve-constraint (conde->disj g) s ctn resolve delta)]
         [(conj? g) (solve-constraint (conj-lhs g) s (conj (conj-rhs g) ctn) resolve delta)]
         [(constraint? g) (solve-constraint (constraint-goal g) s ctn resolve delta)]
         [(suspend? g) (solve-constraint (suspend-goal g) s ctn resolve delta)]
         [(matcho? g) (solve-matcho g s ctn resolve delta)]
         [(pconstraint? g) (solve-pconstraint g s ctn resolve delta)]
         [(proxy? g) (solve-proxy g s ctn resolve delta)]
         [else (assertion-violation 'solve-constraint "Unrecognized constraint type" g)])))


  (define (solve-succeed s ctn resolve delta)
    (if (succeed? ctn) ; Solve until continuation is trivial.
        (if (succeed? resolve) ; If we have no ctn and nothing left to recheck, we're done.
            (values delta s)
            (let-values ([(resolved s) (solve-constraint resolve s succeed succeed delta)])
              (values (if (fail? resolved) fail delta) s))) ; If our recheck constraints fail, fail. Otherwise return the delta of the original simplified constraint (not the rechecks, since we don't want noto to negate the rechecked values that were removed from the constraint store but that were not children of noto). We want to make sure all constraints succeed, but we only want to save the simplified form of our original constraint. Not others that must be rechecked as a result of checking it (eg because it is a unification that fires subsequent constraints).
        (solve-constraint ctn s succeed resolve delta)))

  (define (solve-disj g s ctn resolve delta) ; TODO use ==s in delta to simplify rhs disjuncts
    (let-values ([(d-lhs s-lhs) (solve-constraint (disj-lhs g) s succeed succeed succeed)]) ; Solve the lhs in a new hypothetical environment with no continuation. Just simplify the current disj goals in the context of the current state. Passing the continuation through creates many copies of the same constraints, which destroys performance.
      (exclusive-cond ; Solve the lhs disjunct.
       [(fail? d-lhs) (solve-constraint (disj-rhs g) s ctn resolve delta)] ; If it fails, continue solving disjuncts.
       [(succeed? d-lhs) (solve-constraint ctn s succeed resolve delta)] ; If it succeeds, discard the entire disj constraint.
       [else ; If it only simplifies, store the simplified disj with a new lhs.
        (let ([simplified-lhs (disj d-lhs (disj-rhs g))])
          (solve-constraint ctn (store-constraint s simplified-lhs)
                            succeed resolve (conj delta simplified-lhs)))])))

  (define (solve-matcho g s ctn resolve delta)
    (let-values ([(expanded? g ==s) (matcho/expand g s)])
      (if expanded?
          (solve-constraint ==s s (conj g ctn) resolve delta)
          (solve-constraint ==s (store-constraint s g) ctn resolve (conj delta g)))))



  (define (solve-proxy g s ctn resolve delta) ; Solves the constraint on the proxied varid.
    (let-values ([(v c) (walk-var-val s (proxy-var g))]) ; TODO have proxies identify which constraints to keep and re-store the rest. can we use object id or will constraints get reconstructed as they move vars? if not, use attributed variables maybe (tho then we have to keep proxy var up to date, but reducer can handle that on var-var switch)
      (if (goal? c) (solve-constraint c (extend s v succeed) ctn resolve delta)
          (solve-constraint ctn s succeed resolve delta))))

  (define (solve-noto g s ctn resolve delta)
    (cert (not (noto? g))) ; g is the already unwrapped inner goal of the noto.
    (exclusive-cond
     [(==? g) (solve-=/= g s ctn resolve delta)]
     [(matcho? g) ; Because matcho may return a negatable complex constraint (like disj), we must expand it and see if we can perform the negation before we know how to solve the resulting constraint. Otherwise eg we might solve only 1 branch of a disj, but then attempt to store all branches of the negated conj into the state, which will mean some branches may contain stale variables.
      (let-values ([(expanded? g ==s) (matcho/expand g s)])
        (let ([g (disj (noto ==s) (noto g))])
         (if expanded?
             (solve-constraint g s ctn resolve delta)
             (solve-constraint ctn (store-constraint s g) succeed resolve (conj delta g)))))]
     [else
      (let-values ([(g s^) ; Evaluate the positive constraint hypothetically and invert the result (success <=> failure). Discard the state, which may have changed under the hypothetical positive constraint, and keep only the simplified constraint g, which we negate and return to the store. This is the same logic as for classical implementations of disequality (inverting the substitution of unification), but generalized to arbitrary constraints.
                    (solve-constraint g s succeed succeed succeed)])
        (solve-constraint ctn (store-constraint s (noto g)) succeed resolve (conj delta (noto g))))]))



  (define (solve-== g s ctn resolve delta)
    ;; Runs a unification, collects constraints that need to be rechecked as a result of unification, and solves those constraints.
    ;;TODO consider making occurs check a goal that we can append in between constraints we find and the rest of the ctn, so it only walks if constraints dont fail
    ;; TODO if we only get 1 binding in solve-==, it has already been simplified inside unify and we can skip it
    ;; TODO can we simplify delta/pending as well and simplify already delta constraints from lower in the computation?
    ;; TODO when we store simplified constraints, we should remove all proxies to bound variables using the mini sub as we store the simplified constraints
    (let-values ([(bindings simplified committed pending delta s) (unify s delta (==-lhs g) (==-rhs g))]) ; bindings is a mini-substitution of normalized ==s added to s. simplified is a constraint that does not need further solving, recheck is a constraint that does need further solving, s is the state
      ;;TODO do we need all these returns?
      ;;TODO merge constraints together so they simplify each other not just conjoin
      (if (fail? bindings) (values fail failure)
          (solve-constraint ctn (store-constraint s simplified) succeed (conj pending (conj resolve committed)) delta))))

  
  (define (solve-=/= g s ctn resolve delta) ; TODO simplify ctn
    (cert (==? g))                          ; -> delta state?
    (let-values ([(g c) (disunify s (==-lhs g) (==-rhs g))]) ; If non-trivial, g is normalized x=/=y or, in the case of list =/=, a disjunction headed by one normalized =/= and a number of lazy =/=. c is conjoined constraints on x&y that may need to be rechecked.
      (cert (or (trivial? g) (=/=? g) (and (disj? g) (=/=? (disj-car g)))))
      (let-values ([(g g/recheck) (reduce-constraint g c #t)])
        (if (trivial? g) (solve-constraint g/recheck s ctn resolve delta) ; If g is entailed, skip it and keep solving. We may have g/recheck when c is a disjunction where all disjuncts need to recheck part of g. If g is fail, so is g/recheck.
            (let-values ([(c c/recheck) (reduce-constraint c g #t)]) ; Determine which stored constraints need to be rechecked. c returned from disunifier only contains constraints on x (those on y that would be relevant to x=/y are already proxied to x), so we don't need to touch y's constraints.
              (cert (not (conj-memp c ==?))) ; TODO c/recheck may contain constraints attributable to this variable that can just be moved over to c
              (let ([attr-vars (attributed-vars g)]) ; Get the variables on which to store the new g.
                (solve-constraint ; Run the constraints that need to be rerun,
                 c/recheck (extend ; and replace the store constraints in the store along with the new g.
                            (if (not (null? (cdr attr-vars))) ; TODO can we check if c already has attr vars to y, and so already should have proxy?
                                (add-proxy s (cadr attr-vars) (car attr-vars)) s) ; Add a proxy to g's second var if needed.
                            (car attr-vars) (conj g c)) ctn resolve (conj delta g))))))))

  (define solve-pconstraint
    (case-lambda
      [(g s ctn resolve delta) (solve-pconstraint g s ctn resolve delta '())]
      [(g s ctn resolve delta vs)       ; -> delta pending state?
       (cert (goal? g) (state? s) (goal? ctn) (goal? resolve) (goal? delta) (list? vs))
       (if (not (pconstraint? g)) (solve-constraint g s ctn resolve delta)
           (let ([var (find (lambda (v) (not (memq v vs))) (pconstraint-vars g))])
             (if (not var) (solve-constraint ctn (store-constraint s g) succeed resolve (conj delta g)) ; All vars walked. Store constraint.
                 (let-values ([(var^ val) (walk-var-val s var)])
                   #;
                   (when (and (equal? var^ (make-var 17)) (equal? val 'list))
                     ;(pretty-print (walk-substitution s))
                   )
                   (let ([vs (cons var^ vs)])
                     (cond
                      [(var? val) (solve-pconstraint (pconstraint-rebind-var g var val) s ctn resolve delta vs)] ; Assume for the moment that pconstraints only operate on ground values, so we can simply replace var-var bindings. Identical free vars can always be skipped.
                      [(goal? val) (let-values ([(g simplified recheck p)
                                                 (simplify-pconstraint val (pconstraint-rebind-var g var var^))])
                                     (if (succeed? g) (solve-constraint ctn s succeed resolve delta)
                                         (if (or (fail? simplified) (fail? recheck)) (values fail failure)
                                             (solve-pconstraint g (extend s var^ simplified) ;TODO can we just stash the pconstraint with the simplified under certain conditions if we know it wont need further solving?
                                                                ctn (conj recheck resolve) delta vs))))]
                      [else (solve-pconstraint (pconstraint-check g var val) s ctn resolve delta vs)]))))))]))

  (define simplify-pconstraint ; TODO is simplify pconstraint used? probably should be removed
    (case-lambda
      [(g p) (simplify-pconstraint g p p)]
      [(g p c)
       (cert (or (pconstraint? p) (succeed? p)) (goal? g) (or (succeed? c) (pconstraint? c)))
       (cond
        [(succeed? p) (values succeed succeed succeed c)]
        [(conj? g) (let-values ([(p-lhs simplified-lhs recheck-lhs c) (simplify-pconstraint (conj-lhs g) p c)])
                     (if (or (fail? p-lhs) (fail? simplified-lhs) (fail? recheck-lhs)) (values fail fail succeed c)
                         (let-values ([(p-rhs simplified-rhs recheck-rhs c) (simplify-pconstraint (conj-rhs g) p c)])
                           (values (if (or (succeed? p-lhs) (succeed? p-rhs)) succeed p) (conj simplified-lhs simplified-rhs) (conj recheck-lhs recheck-rhs) c))))]
        [(disj? g) (simplify-pconstraint-disj g p c)]
        [(pconstraint? g) (if (equal? p g) (values succeed succeed succeed c)
                              (let ([v (memp (lambda (v) (memq v (pconstraint-vars g))) (pconstraint-vars p))])
                                (if (not v) (values p g succeed c)
                                    (let-values ([(g simplified recheck) ((pconstraint-procedure g) v v p g p)])
                                      (values g simplified recheck c)))))]
        [(==? g) (if (memq (==-lhs g) (pconstraint-vars p))
                     (let ([entailed ((pconstraint-procedure p) (==-lhs g) (==-rhs g) p succeed p)])
                       (values entailed (if (fail? entailed) fail g) succeed c))
                     (values p g succeed c))
         #;
         (let-values ([(simplified recheck) (simplify-unification p (->mini-substitution g))]) ;
         (values simplified g recheck c))]
        ;; numbero & not numbero -> succeed succeed -> fail fail
        ;; numbero & not symbolo  -> fail fail -> numbero succeed
        ;; numbero & =/=1 -> succeed ==1 -> numbero =/=1
        ;; numbero & =/='symbol -> fail fail -> numbero succeed
        ;; numbero & not symbolo x2 -> numbero symbolo x2 -> numbero not symbolo x2
        [(noto? g) (let-values ([(entailed simplified recheck c) (simplify-pconstraint (noto-goal g) p c)])
                     ;(display entailed simplified recheck)
                     (when (not (succeed? recheck)) (display p))
                     (cert (succeed? recheck))
                     (let ([p (if (and (succeed? entailed) (succeed? simplified)) fail p)])
                       (values p (noto simplified) succeed c)))]
        [else (values p g succeed c)])]))

  (define (simplify-pconstraint-disj g p d)
    (cert (or (succeed? d) (pconstraint? d)))
    (let*-values ([(unified-lhs simplified-lhs recheck-lhs d)
                   (simplify-pconstraint (disj-lhs g) p d)]
                  [(disunified-lhs) (conj simplified-lhs recheck-lhs)])
      (if (succeed? disunified-lhs) (values unified-lhs succeed succeed d)
          (let*-values ([(unified-rhs simplified-rhs recheck-rhs d)
                         (simplify-pconstraint (disj-rhs g) p d)]
                        [(disunified-rhs) (conj simplified-rhs recheck-rhs)])
            (if (succeed? disunified-rhs) (values unified-rhs succeed succeed d)
                (let ([unified (if (and (succeed? unified-lhs) (succeed? unified-rhs)) succeed p)])
                  (let-values ([(conjs disjs lhs rhs) (disj-factorize disunified-lhs disunified-rhs)])
                    (let ([disunified
                           (conj conjs (conj
                                        (if (not (or (succeed? unified-lhs) (succeed? unified-rhs)))
                                            (conj d (disj lhs rhs))
                                            (disj (if (succeed? unified-lhs) lhs (conj d lhs))
                                                  (if (succeed? unified-rhs) rhs (conj d rhs)))) disjs))])
                      (if (or (fail? simplified-lhs) (not (succeed? recheck-lhs))
                              (and (or (fail? simplified-rhs) (not (succeed? recheck-rhs)))
                                   (conj-memp simplified-lhs ==?))) ; Only need to check simplified since any non succeed recheck will force a recheck
                          (values unified succeed disunified succeed)
                          (values unified disunified succeed succeed))))))))))



  (org-define (store-constraint s g)
    ;; Store simplified constraints into the constraint store.
    (cert (maybe-state? s) (goal? g) (not (conde? g))) ; -> state?
    (exclusive-cond
     [(fail? g) failure]
     [(succeed? g) s]
     [(conj? g) (store-constraint (store-constraint s (conj-lhs g)) (conj-rhs g))] ;TODO storing conj whole if lhs and rhs have same attributed vars. check attr vars of lhs and rhs. if same, pass to parent. when differ, store children independently
     [(==? g) (extend s (==-lhs g) (==-rhs g))]
     [else ; All other constraints get assigned to their attributed variables.
      (add-constraint s g (list-sort (lambda (v1 v2) (fx< (var-id v1) (var-id v2))) (attributed-vars g)))])))
