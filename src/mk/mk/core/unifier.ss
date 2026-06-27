(library (mk core unifier) ; Main state object that holds substitution & constraints
  (export state-substitution state-varid empty-state set-state-substitution increment-varid set-state-varid
          instantiate-var add-constraint add-proxy unify disunify extend remove-constraint) 
  (import (chezscheme) (mk core sbral) (mk core variables) (mk core streams) (mk core goals) (mk core utils) (mk core mini-substitution) (mk core reducer) (mk core walk))
  
  ;; === UNIFICATION ===

  
  (define unify ;TODO is there a good opportunity to further simplify constraints rechecked by unify using the other unifications we are performing during a complex unification? currently we only simplify constraints with the unification on the variable to which they are bound, but they might contain other variables that we could simplify now and then not have to walk to look up later. maybe we combine the list of unifications and the list of constraints after return from unify
    ;;Unlike traditional unification, unify builds the new substitution in parallel with a goal representing the normalized extensions made to the unification that can be used by the constraint system. The substitution also contains constraints on the variable, which must be dealt with by the unifier.
    (case-lambda
      [(s d x y) (unify s d x y '())] ; Create an empty list of simplified extension bindings made to the substitution.
      [(s d x y bindings)
       (cert (state? s)) ; -> bindings simplified recheck state
       (let-values ([(x-var x) (walk-var-val s x)]
                    [(y-var y) (walk-var-val s y)])
         (if (and (var? y-var) (var? x-var) (fx< (var-id y-var) (var-id x-var))) ; Swap x and y if both are vars and y has a lower index. We will be storing y in the x location and the x constraints in the y location, so swapping lets us disambiguate which is which.
             (unify-binding s d y-var y x-var x bindings)
             (unify-binding s d x-var x y-var y bindings)))]))

  (define (unify-binding s d x-var x y-var y bindings) 
    (cert (not (or (goal? x-var) (goal? y-var)))
          (or (not (var? x-var)) (not (var? y-var)) (fx<= (var-id x-var) (var-id y-var)))) ; If both vars, x-var guaranteed to have lower id
    (cond
     
     [(goal? x) 
      (if (goal? y)
          (if (eq? x-var y-var)
              (values bindings succeed succeed succeed d s)
              (extend-constraint s d x-var y-var x y bindings)) ; x->y, y->y, ^cx(y)&cy
          (extend-constraint s d x-var y x succeed bindings))] ; x->y, ^cx(y). y always replaces x if x var, no matter whether y var or const     
     [(eq? x y) (values bindings succeed succeed succeed d s)]
     [(goal? y) (if (var? x)
                    (extend-constraint s d x y-var succeed y bindings) ; x->y, y->y, ^cy. y always replaces x due to id, 
                    (extend-constraint s d y-var x y succeed bindings))] ; y->x, ^cy(x). unless x is a constant.
     [(var? x) (extend-var s d x y bindings)]
     [(var? y) (extend-var s d y x bindings)]
     [(and (pair? x) (pair? y)) 
      (let-values
          ([(bindings simplified committed pending d s) (unify s d (car x) (car y) bindings)])
        (if (fail? bindings)
            (values fail fail fail fail fail failure)
            (let-values ([(bindings simplified^ committed^ pending^ d s) (unify s d (cdr x) (cdr y) bindings)])
              (values bindings (conj simplified simplified^) (conj committed committed^) (conj pending pending^) d s))))]
     [else (values fail fail fail fail fail failure)]))
  
  (define (extend-var s d x y bindings)
    ;; Insert a new binding x->y into the substitution.
    (if (occurs-check/binding s x y) (values fail fail fail fail fail failure)
     (values (cons (cons x y) bindings) succeed succeed succeed (conj d (== x y)) (extend s x y))))

  (define (extend-constraint s d x y x-c y-c bindings)
    ;; Opportunistically simplifies the retrieved constraints using the available vars and vals and then extends the substitution. Since x->y now, we can replace x with y everywhere it appears, and y with y's new value. If there was a constraint on y (and y was a var), we must explicitly remove it since it won't have been overwritten.
    (cert (var? x) (or (not (var? y)) (fx< (var-id x) (var-id y))))
    (if (occurs-check/binding s x y)
        (values fail fail fail fail fail failure)
        (let ([bindings (cons (cons x y) bindings)])
          (let-values ([(x-c/simplified x-c/recheck) (reduce-constraint x-c bindings #f)]) ;TODO handle simplified during ==
           (values bindings succeed (conj x-c/simplified x-c/recheck) y-c (conj d (== x y)) (extend s x y))))
        #;
     (let-values ([(pending committed)
                  
                   (conj-partition (lambda (g) (conj-member g d)) x-c)])
       (let-values ([(committed/simplified committed/recheck) (simplify-unification committed (list (cons x y)))]) ;TODO return y constraint to simplify it with potentially other bindings and also unbind its var?
         (if (or (fail? committed/simplified) (fail? committed/recheck)) (values fail fail fail fail fail failure) ; (if (succeed? val-c) s (remove-constraint s val))
             (let-values ([(pending/simplified pending/recheck) (simplify-unification pending (list (cons x y)))])
               (if (or (fail? pending/simplified) (fail? pending/recheck)) (values fail fail fail fail fail failure) ; (if (succeed? val-c) s (remove-constraint s val))

                   ;; remove var-c constraints from delta
                   ;; add simplified constraints back to delta
                   ;; return separate 
                   (if (occurs-check/binding s x y)
                       (values fail fail fail fail fail failure)
                       (values (cons (cons x y) bindings) (conj committed/simplified pending/simplified) committed/recheck pending/recheck (conj (conj (conj-diff d pending) pending/simplified) (== x y)) (extend s x y))))))))))

  (define (extend s x y)
    ;; Insert a new binding between x and y into the substitution.
    (cert (state? s) (not (eq? x y)))
    (set-state-substitution
     s (sbral-set-ref
        (state-substitution s)
        (fx- (sbral-length (state-substitution s)) (var-id x)) y succeed)))

  (define (occurs-check/binding s v term) ;TODO see if the normalized ==s can help speed up occurs-check/binding, eg by only checking rhs terms in case of a trail of unified terms. maybe use the fact that normalized vars have directional unification?
    ;; TODO try implementing occurs check in the constraint system and eliminating checks in the wrong id direction (eg only check lower->higher)
    ;; TODO add a non occurs check =!= or ==!
    ;; Returns #t if it detects a cyclic unification.
    ;;TODO remove double occurs check
    (cert (state? s) (var? v))
    (exclusive-cond
     [(eq? v term) #t]            ; term is already walked by normalized ==s
     [(pair? term)
      (or (eq? v (car term)) (eq? v (cdr term)) ; can't just walk a term bc it is already in the substitution
          (occurs-check/binding s v (walk-var s (car term))) (occurs-check/binding s v (walk-var s (cdr term))))]
     [else #f]))

  ;; === DISUNIFICATION ===
  
  (define (disunify s x y)
    ;; Specialized unification for =/= constraints. Only solves enough to confirm non failure and simplifies using special routines for =/=. Returns disunification along with constraints on the vars that may need to be rechecked.
    (cert (state? s)) ; -> substitution? goal?
    (let-values ([(x-var x) (walk-var-val s x)]
                 [(y-var y) (walk-var-val s y)]) ;TODO how does disunify play with constraints in substitution?
      (if (eq? x-var y-var) (values fail fail) ; The same variable is never =/= itself regardless of value or constraint.
          (if (and (var? y-var) (var? x-var) (fx< (var-id y-var) (var-id x-var))) ; Swap x and y if both are vars and y has a lower index
              (disunify-binding s y-var y x-var x)
              (disunify-binding s x-var x y-var y)))))

  (define (disunify-binding s x-var x y-var y) 
    (cert (state? s) ; -> goal?(disequality) goal?(constraint)
          (or (not (var? x-var)) (not (var? y-var)) (fx< (var-id x-var) (var-id y-var)))) ; if x-var and y-var are both vars, x-var has a lower index
    (cond
     [(goal? x) (extend/disunify s x-var (if (goal? y) y-var y) fail x)] ; Return the constraint on x to recheck for possible == to commit.
     [(goal? y) (if (var? x)
                    (extend/disunify s x y-var fail succeed) ; x is older so it controls the constraints that may pertain to x=/=y. This is a function of the disunifier assigning x=/=y goals to x. If a constraint that might unify could be solved by x=/=y, it would already be attributed to x. Therefore, we only need to add the x=/=y constraint. There is nothing to recheck.
                    (extend/disunify s y-var x fail y))] ; Since x is a value here, treat y like the dominant constraint and simplify it.
     [(eq? x y) (values fail fail)]
     [(var? x) (extend/disunify s x y fail succeed)]
     [(var? y) (extend/disunify s y x fail succeed)]
     [(and (pair? x) (pair? y))
      (let-values ([(lhs c) (disunify s (car x) (car y))])
        (exclusive-cond
         [(succeed? lhs) (values succeed succeed)] ; TODO test whether all the manual checks for fail/succeed could be replaced by conj/disj macros
         [(fail? lhs) (disunify s (cdr x) (cdr y))]
         [else (values (disj lhs (=/= (cdr x) (cdr y))) c)]))]
     [else (values succeed succeed)]))

  (define (extend/disunify s x y d c)
    (if (occurs-check/binding s x y) (values succeed succeed)
     (values (disj (=/= x y) d) c)))
  

  ;; === CONSTRAINTS ===

  
  (define (add-constraint s c vs) ;TODO consider sorting ids of variables before adding constraints to optimize adding to sbral. or possibly writing an sbral multi-add that does one pass and adds everything. would work well with sorted lists of attr vars to compare which constraints we can combine while adding
    (cert (state? s) (goal? c) (list? vs) (not (conj-memp c ==?)))
    ;; Proxy constraints with multiple attributed variables so that they only need to be solved once by whichever variable is checked first and can be removed from the global store so subsequent checks will simply succeed.
    (let ([stored-constraint (substitution-ref (state-substitution s) (car vs))])
      (cert (goal? stored-constraint))
      (fold-left (lambda (s v) (add-proxy s v (car vs))) (extend s (car vs) (conj stored-constraint c)) (cdr vs))))

  (define (add-proxy s v c) ; TODO add-proxy should only add at most one proxy per variable
    (cert (state? s) (var? v) (var? c))
    (let ([stored-constraint (substitution-ref (state-substitution s) v)])
      (cert (goal? stored-constraint))
      (extend s v (conj stored-constraint (proxy c)))))

  (define (remove-constraint s v)
    (extend s v succeed)))
