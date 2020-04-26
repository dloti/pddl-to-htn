(define (domain depot)
(:requirements :durative-actions)
(:predicates
	 (at ?x ?y) (on ?x ?y) (in ?x ?y) (lifting ?x ?y) (available ?x) (clear ?x)(place ?x) (locatable ?x) (depot ?x) (distributor ?x) (truck ?x) (hoist ?x) (surface ?x) (pallet ?x) (crate ?x) )
(:durative-action drive
 :parameters ( ?x ?y ?z)
 :duration (= ?duration 10)
 :condition
	(and (at start (truck ?x)) (at start (place ?y)) (at start (place ?z))  (at start (at ?x ?y)))
 :effect
	(and (at end  (at ?x ?z)) (at start  (not (at ?x ?y)))))

(:durative-action lift
 :parameters ( ?x ?y ?z ?p)
 :duration (= ?duration 1)
 :condition
	(and (at start (hoist ?x)) (at start (crate ?y)) (at start (surface ?z)) (at start (place ?p))  (over all (at ?x ?p)) (at start (available ?x)) (at start (at ?y ?p)) (at start (on ?y ?z)) (at start (clear ?y)))
 :effect
	(and (at start  (not (on ?y ?z))) (at start  (clear ?z)) (at start  (not (available ?x))) (at start  (not (clear ?y))) (at start  (lifting ?x ?y)) (at start  (not (at ?y ?p)))))

(:durative-action drop
 :parameters ( ?x ?y ?z ?p)
 :duration (= ?duration 1)
 :condition
	(and (at start (hoist ?x)) (at start (crate ?y)) (at start (surface ?z)) (at start (place ?p))  (over all (at ?x ?p)) (over all (at ?z ?p)) (over all (clear ?z)) (over all (lifting ?x ?y)))
 :effect
	(and (at end  (on ?y ?z)) (at end  (clear ?y)) (at end  (not (clear ?z))) (at end  (at ?y ?p)) (at end  (not (lifting ?x ?y))) (at end  (available ?x))))

(:durative-action load
 :parameters ( ?x ?y ?z ?p)
 :duration (= ?duration 3)
 :condition
	(and (at start (hoist ?x)) (at start (crate ?y)) (at start (truck ?z)) (at start (place ?p))  (over all (at ?x ?p)) (over all (at ?z ?p)) (over all (lifting ?x ?y)))
 :effect
	(and (at end  (available ?x)) (at end  (in ?y ?z)) (at end  (not (lifting ?x ?y)))))

(:durative-action unload
 :parameters ( ?x ?y ?z ?p)
 :duration (= ?duration 4)
 :condition
	(and (at start (hoist ?x)) (at start (crate ?y)) (at start (truck ?z)) (at start (place ?p))  (over all (at ?x ?p)) (over all (at ?z ?p)) (at start (available ?x)) (at start (in ?y ?z)))
 :effect
	(and (at start  (lifting ?x ?y)) (at start  (not (available ?x))) (at start  (not (in ?y ?z)))))

)
