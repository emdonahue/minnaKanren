(library (mk core goals) ; Definitions for core mk goals
  (export goal?
          make-== ==? ==-lhs ==-rhs == ==-member?
          succeed fail succeed? fail? trivial?
          make-noto noto? noto-goal
          make-conj conj? conj-lhs conj-rhs
          make-disj disj? disj-lhs disj-rhs disj->list
          suspend suspend? suspend-goal
          make-matcho matcho? matcho-ctn matcho-substitution
          proxy proxy? proxy-var proxy proxy-id
          conde conde? conde-lhs conde-rhs conde-car conde-cdr conde-disj conde->disj
          pconstraint pconstraint? pconstraint-vars pconstraint-data pconstraint-procedure pconstraint-rebind-var pconstraint-check pconstraint-attributed?
          constraint constraint? constraint-goal
          dfs-goal dfs-goal? dfs-goal-procedure
          make-conj conj conj? conj-lhs conj-rhs conj* conj-memp conj-fold conj-filter conj-diff conj-member conj-memq conj-intersect conj-partition
          noto =/= =/=-lhs =/=-rhs =/=? =/=-member?
          make-disj disj disj? disj-car disj-cdr disj* disj-lhs disj-rhs disj-succeeds? disj-factorize disj-factorized
          fresh-vars fresh exist
          attributed-vars matcho-attributed-vars pattern-binding? pattern-vars? normalized-vars)
  (import (chezscheme) (mk core variables) (mk core streams) (mk core utils))

  
  ;; === SUCCEED & FAIL ===
  (define succeed ; A goal that trivially succeeds. Used as a constant rather than a function call.
    (vector 'succeed))
  (define fail ; A goal that trivially fails. Used as a constant rather than a function call.
    (vector 'fail))
  (define (succeed? g) (eq? g succeed))
  (define (fail? g) (eq? g fail))
  (define (trivial? g) (or (succeed? g) (fail? g)))

  ;; === == ===
  (define-structure (== lhs rhs)) ;TODO ensure that if two vars are unified, there is a definite order even in the goal so that we can read the rhs as always the 'value' when running constraints. also break two pairs into a conj of ==. then we can simplify the order checking inside the unifier
  (define (== x y) ; Implements unification between terms.
    (cond
     [(or (eq? x __) (eq? y __)) succeed]
     [(equal? x y) succeed]
     [(var? x) (if (var? y) (if (var< x y) (make-== x y) (make-== y x)) (make-== x y))]
     [(var? y) (make-== y x)]
     [(and (pair? x) (pair? y)) (make-== x y)]
     [else fail]))

  (define (==-member? e g)
    (cert (==? g))
    (or (equal? (==-lhs g) e) (equal? (==-rhs g) e)))
  
  ;; === DFS ===
  (define-structure (dfs-goal procedure))
  (define (dfs-goal p) ; Wraps a procedure that has the same signature as run-goal-dfs. Called internally by run-goal-dfs, which transparently passes its arguments to the procedure and returns the resulting values. Used to dynamically extend the behavior of the dfs interpreter.
    (cert (procedure? p))
    (make-dfs-goal p))

  
  ;; === PROXY ===
  (define-structure (proxy var)) ;TODO make proxies remove only their specific constraint and return other conjoined constraints to the store, not rerun all conjuncts.
  (define (proxy v) ; If a constraint is bound to multiple variables, we only keep one true copy of the constraint. The other variables receive proxy constraints that remember the one variable with the true constraint. When solving, proxy constraints fetch the true constraint and run that to avoid running multiple copies of the same constraint. In addition to being generally inefficient, multiple copies can lead to various kinds of blow up conditions depending on how solving is implemented (eg multiple copies of a fresh will yield constraints with different object identities, which may make it hard to do any simplification, especially if we simplify them locally first).
    (cert (var? v))
    (make-proxy v))

  (define (proxy-id p) (var-id (proxy-var p)))

  ;; === CONDE ===
  (define-structure (conde lhs rhs))

  (define-syntax conde ; Nondeterministic branching.
    (syntax-rules () 
      [(_ (g ...))
       (conj* g ...)]
      [(_ c0 c ...)
       (conde-disj (conde c0) (conde c ...))]))
  
  (define (conde-car g)
    (if (conde? g)
        (conde-car (conde-lhs g))
        g))
  
  (define (conde-cdr g)
    (if (conde? g)
        (let ([lhs (conde-cdr (conde-lhs g))])
          (if (fail? lhs) (conde-rhs g) (make-conde lhs (conde-rhs g))))
        fail))
  
  (define (conde-disj x y)
    ;; Conde can simplify on failure, but unlike disj constraints, cannot simply remove itself on success.
    (cond
     [(fail? x) y]
     [(fail? y) x]
     [else (make-conde x y)]))


  ;; === PCONSTRAINT ===
  (define-structure (pconstraint vars procedure data))
  
  (define (pconstraint vars procedure data)
    (cert (list? vars) (procedure? procedure))
    (make-pconstraint vars procedure data))

  (define pconstraint-rebind-var
    ;; Moves a pconstraint from one var to another
    (case-lambda
      [(g v) (pconstraint (cons v (cdr (pconstraint-vars g)))
                          (pconstraint-procedure g)
                          (pconstraint-data g))]
      [(g v v^) (if (eq? v v^) g
                    (pconstraint (cons v^ (remq v (pconstraint-vars g)))
                                 (pconstraint-procedure g)
                                 (pconstraint-data g)))]))

  (define (pconstraint-check p var val)
    (when (not (memq var (pconstraint-vars p))) ;TODO remove debug
      (printf "var ~s val ~s~%" var val)
      (pretty-print p))
    (cert (memq var (pconstraint-vars p)))
    ((pconstraint-procedure p) var val succeed succeed p))

  (define (pconstraint-attributed? p var)
    (memq var (pconstraint-vars p)))
  

  ;; === CONSTRAINT ===
  (define-structure (constraint goal))

  (define-syntax constraint ; Wrapped goals are conjoined and interpreted as a constraint.
    (syntax-rules ()
      [(_ g ...)
       (let ([c (conj* g ...)])
         (if (or (fail? c) (succeed? c)) c (make-constraint c)))]))

  
  ;; === CONJ ===
  (define-structure (conj lhs rhs))
  
  (define (conj lhs rhs) ; Logical conjunction between goals or constraints.
    ;; Can be used between any goals or constraints. Unlike disj, conj is not specific to constraint goals.
    ;(when (or (not (goal? lhs)) (not (goal? rhs))) (pretty-print lhs) (pretty-print rhs))
    (cert (goal? lhs) (goal? rhs))
    ;TODO replace conj with make-conj or short circuiting conj* where possible, especially test in matcho for walking large ground lists
    (cond
     [(or (fail? lhs) (fail? rhs)) fail]
     [(succeed? rhs) lhs]
     [(succeed? lhs) rhs]
     [else (make-conj lhs rhs)]))

  (define-syntax conj* ;TODO experiment with short circuiting conj and disj macros
    (syntax-rules () ;TODO make conj a macro but when it is just an identifier macro make it return a function of itself for use with higher order fns
      [(_) succeed]
      [(_ g) g]
      [(_ lhs rhs ...)
       (conj lhs (conj* rhs ...))
       #;
       (let ([l lhs])
         (if (fail? l) fail
             (let ([r (conj* rhs ...)])
               (cond
                [(fail? r) r]
                [(succeed? l) r]
                [(succeed? r) l]
                [else (make-conj l r)]))))]))

  (define (conj-filter p c)
    (if (conj? c)
        (conj
         (conj-filter p (conj-lhs c))
         (conj-filter p (conj-rhs c)))
        (if (p c) c succeed)))

  (define (conj-diff c d)
    (if (conj? c) (conj (conj-diff (conj-lhs c) d) (conj-diff (conj-rhs c) d))
        (if (conj-member c d) succeed c)))

  (define (conj-intersect c d)
    (if (conj? c) (conj (conj-intersect (conj-lhs c) d) (conj-intersect (conj-rhs c) d))
        (if (conj-member c d) c succeed)))

  (define (conj-member e c)
    (if (conj? c) (or (conj-member e (conj-lhs c)) (conj-member e (conj-rhs c)))
        (equal? c e)))

  (define (conj-memq e c)
    (if (conj? c) (or (conj-memq e (conj-lhs c)) (conj-memq e (conj-rhs c)))
        (eq? c e)))

  (define (conj-memp c p)
    (if (conj? c)
        (or (conj-memp (conj-lhs c) p) (conj-memp (conj-rhs c) p))
        (if (p c) c #f)))
  
  (define (conj-fold p s cs)
    (cert (procedure? p))
    (if (not (conj? cs))
        (p s cs)
        (conj-fold p (conj-fold p s (conj-lhs cs)) (conj-rhs cs))))

  (define (conj-partition p cs)
    (if (conj? cs) (let-values ([(lhs-t lhs-f) (conj-partition p (conj-lhs cs))]
                                [(rhs-t rhs-f) (conj-partition p (conj-rhs cs))])
                     (values (conj lhs-t rhs-t) (conj lhs-f rhs-f)))
        (if (p cs) (values cs succeed) (values succeed cs))))

  
  ;; === DISJ ===
  (define-structure (disj lhs rhs))
  
  (define (disj lhs rhs) ; Logical disjunction between constraints.
    ; Unlike conj, disj is specific to constraints and any goals joined with disj will be interpreted as constraints rather than as nondeterministic goals.
    (cert (goal? lhs) (goal? rhs))
    ;TODO convert constructor fns to constructed params of structure  
    (cond
     [(or (succeed? lhs) (succeed? rhs)) succeed]
     [(fail? rhs) lhs]
     [(fail? lhs) rhs]
     [else (make-disj lhs rhs)]))

  (define (disj* . disjs)
    (fold-right (lambda (lhs rhs) (disj lhs rhs)) fail disjs))

  (define (disj-car g)
    (if (disj? g)
        (disj-car (disj-lhs g))
        g))

  (define (disj-cdr g) ;TODO microbenchmark disj cdr that looks ahead instead of using base case to check for non disj
    (if (disj? g)
        (disj (disj-cdr (disj-lhs g)) (disj-rhs g))
        fail))

  (define conde->disj
    ;; Inverts conde from right-branching to left-branching to allow for optimizations in solve-disj
    (case-lambda
      [(c) (conde->disj c fail)]
      [(c d) (if (conde? c) (conde->disj (conde-rhs c) (conde->disj (conde-lhs c) d)) (disj d c))]))
  
  (define (disj-succeeds? d)
    ;; True if d contains a literal succeed goal.
    (cond
     [(succeed? d) #t]
     [(disj? d) (or (disj-succeeds? (disj-lhs d)) (disj-succeeds? (disj-rhs d)))]
     [else #f]))

  (define (disj-factorize lhs rhs)
    (let ([intersection (conj-intersect lhs rhs)])
      (values (conj-filter (lambda (c) (not (disj? c))) intersection)
              (conj-filter disj? intersection)
              (conj-diff lhs intersection)
              (conj-diff rhs intersection))))

  (define (disj-factorized lhs rhs)
    ;; Factorizes out goals common to all branches of a disj so they can be applied once. 
    (let-values ([(cs ds lhs rhs) (disj-factorize lhs rhs)])
      (conj cs (conj (if (or (not (conj-memp lhs ==?)) (conj-memp rhs ==?)) (disj lhs rhs) (disj rhs lhs)) ds))))

  (define disj->list
    (case-lambda
      [(d) (disj->list d '())]
      [(d ds)
       (if (disj? d)
           (disj->list (disj-lhs d) (disj->list (disj-rhs d) ds))
           (cons d ds))]))
  
  ;; === SUSPEND ===
  (define-structure (suspend goal))

  (define (suspend g) ; A suspend goal tells the interleaving interpreter to suspend this branch and continue with the search later. This is the fundamental primitive on which fresh is built, but it can be used directly by end-users.
    (cert (goal? g))
    (if (or (succeed? g) (fail? g)) g (make-suspend g)))

  
  ;; === FRESH/EXIST ===
  (define-syntax fresh-vars ; Accepts a state and syntactic list of variables. Binds a new state with appropriately incremented variable id counter and runs the body forms in the scope of variables bound to the new logic variables. This is the basic primitive for all logic variable instantiation.
    (syntax-rules ()
      [(_ [(end-state end-goal) (start-state (start-goal ...) ())] body ...) ; Empty variable lists => just run the goals without incrementing the state.
       (let ([end-state start-state]
             [end-goal (conj* start-goal ...)])
         body ...)]
      [(_ [(end-state end-goal) (start-state (start-goal ...) (q ...))] body ...)
       (let* ([vid (state-varid start-state)] ; Get the current state var id.
              [q (begin (set! vid (fx1+ vid)) (make-var vid))] ... ; For each fresh variable, set its var id and increment the var id.
              [end-goal (conj* start-goal ...)] ; Conjoin the goals into a single goal.
              [end-state (if (succeed? end-goal) start-state (set-state-varid start-state vid))]) ; If the state is a trivial success, we won't need those variables, so throw out the state and the new fresh variables to conserve var id index.
         body ...)]
      [(_ [(end-state end-goal) (start-state (start-goal ...) q)] body ...) ; Single variables are treated as 1-length lists.
       (fresh-vars [(end-state end-goal) (start-state (start-goal ...) (q))] body ...)]))

  (define-syntax exist 
    (syntax-rules ()
      [(_ q g ...)
       (lambda (start-state p c)
         (fresh-vars [(end-state end-goal) (start-state (g ...) q)] ;TODO make fresh insert fail checks between conjuncts to short circuit even building subsequent goals
                     (values end-goal end-state p c)))]))

  (define-syntax fresh ; Introduce fresh variables.
    ;; (fresh (x y z) ...)
    ;; Can be run with an empty variable list to simply suspend the search at that point.
    (syntax-rules ()
      [(_ q g ...)
       (exist q (suspend (conj* g ...)))]))

  ;; === NEGATION ===
  (define-structure (noto goal)) ; Negated goal
  (define (=/= lhs rhs) (noto (== lhs rhs))) ; Defining =/= as a function of == lets us reuse =='s variable ordering machinery.
  (define (=/=-lhs g) (==-lhs (noto-goal g)))
  (define (=/=-rhs g) (==-rhs (noto-goal g)))
  (define (=/=? g) (and (noto? g) (==? (noto-goal g))))
  (define (=/=-member? v g)
    (cert (=/=? g))
    (==-member? v (noto-goal g)))
  ;;(define-structure (=/= lhs rhs))
  #;
  (define (=/= x y) ; Implements disunification between terms.
    (cond
     [(or (eq? x __) (eq? y __)) succeed]
     [(equal? x y) fail]
     [(var? x) (if (var? y) (if (var< x y) (make-=/= x y) (make-=/= y x)) (make-=/= x y))]
     [(var? y) (make-=/= y x)]
     [(and (pair? x) (pair? y)) (make-=/= x y)]
     [else succeed]))


  (define (noto g) ; Logical negation of constraints.
    ;; Goals wrapped with noto will be interpreted as negated constraints. Negation in this context should be understood in terms of a few simple operations:
    ;; == and =/= become the other when negated
    ;; conj and disj become the other when negated and their children are negated in accordance with De Morgan's laws
    ;; primitive constraints (such as symbolo) become negated versions of themselves (e.g. not-symbolo)
    ;; matcho lazily waits until it can expand and then negates its expansion
    ;; fresh cannot currently be negated
    
    (cert (goal? g))
    (exclusive-cond
     [(succeed? g) fail]
     [(fail? g) succeed]
     [(==? g) (make-noto g)]
     ;[(==? g) (=/= (==-lhs g) (==-rhs g))]
     ;[(=/=? g) (== (=/=-lhs g) (=/=-rhs g))]
     [(or (matcho? g) (pconstraint? g)) (make-noto g)]
     [(disj? g) (conj (noto (disj-car g)) (noto (disj-cdr g)))]
     [(conde? g) (conj (noto (conde-lhs g)) (noto (conde-rhs g)))]
     [(conj? g) (disj (noto (conj-lhs g)) (noto (conj-rhs g)))]
     [(noto? g) (noto-goal g)]
     [(constraint? g) (noto (constraint-goal g))]
     [else (assertion-violation 'noto "Unrecognized constraint type" g)]))

  ;; === MATCHO ===
  
  (define-structure (matcho substitution ctn))

  (define (pattern-binding? b)
    (cert (pair? b) (var? (car b)))
    (pattern-var? (car b)))

  (define (pattern-vars? x)
    (if (pair? x)
        (or (pattern-vars? (car x)) (pattern-vars? (cdr x)))
        (and (var? x) (zero? (var-id x)))))
  
  (define (matcho-attributed-vars g)
    ;; The matcho attributed vars are the non pattern vars still in the substitution because they have not been fully grounded.
    (cert (matcho? g))
    (map car (remp pattern-binding? (matcho-substitution g))))
  
  ;; === ATTR VARS ===

  (define attributed-vars
    ;; Extracts the free variables in the constraint to which it should be attributed.
    (case-lambda
      [(g) (attributed-vars g '())]
      [(g vs)
       (cert (goal? g) (not (proxy? g)))
       (exclusive-cond
        [(succeed? g) vs]
        [(disj? g) (attributed-vars (disj-car g) vs)]
        [(conj? g) (attributed-vars (conj-lhs g) (attributed-vars (conj-rhs g) vs))]
        [(noto? g)
         (if (==? (noto-goal g))
             (attributed-vars
              (noto-goal g)
              (if (and (var? (==-rhs (noto-goal g))) (not (memq (==-rhs (noto-goal g)) vs)))
                  (cons (==-rhs (noto-goal g)) vs) vs))
             (attributed-vars (noto-goal g) vs))]
        [(==? g) ;TODO test whether == must attribute to both vars like =/=
         (cert (var? (==-lhs g)))
         (if (memq (==-lhs g) vs) vs (cons (==-lhs g) vs))]
        [(matcho? g) (matcho-attributed-vars g)]
        [(pconstraint? g) (fold-left (lambda (vs v) (if (memq v vs) vs (cons v vs))) vs (pconstraint-vars g))]
        [(constraint? g) (attributed-vars (constraint-goal g) vs)]
        [else (assertion-violation 'attributed-vars "Unrecognized constraint type" g)])]))

  (define (normalized-vars g)
    (cert (not (conj? g)) (not (disj? g)))
    (exclusive-cond
     [(==? g) (let ([rhs (if (var? (==-rhs g)) (list (==-rhs g)) '())])
                (if (var? (==-lhs g)) (cons (==-lhs g) rhs) rhs))]
     [(proxy? g) (list (proxy-var g))]
     [else (attributed-vars g)]))
  
  ;; === CONTRACTS ===  
  (define (goal? g)
    (or (procedure? g) (==? g) (conj? g) (disj? g) (succeed? g) (fail? g) (=/=? g) (noto? g) (constraint? g) (pconstraint? g) (conde? g) (suspend? g) (proxy? g) (dfs-goal? g) (matcho? g))))
