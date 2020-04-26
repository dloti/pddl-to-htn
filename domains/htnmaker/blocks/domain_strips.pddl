(define (domain blocksworld)
  (:requirements :strips)
(:predicates (clear ?x)
             (on-table ?x)
             (arm-empty)
             (on ?x ?y))

(:action !MOVE-B-TO-B
  :parameters (?bm ?bf ?bt)
  :precondition (and (clear ?bm) (clear ?bt) (on ?bm ?bf))
  :effect (and (on ?bm ?bt) (clear ?bf) (not (clear ?bt)) 
               (not (on ?bm ?bf))))

(:action !MOVE-B-TO-T
  :parameters  (?bm ?bf)
  :precondition (and (clear ?bm) (on ?bm ?bf))
  :effect (and (on-table ?bm) (clear ?bf) 
               (not (on ?bm ?bf))))

(:action !MOVE-T-TO-B
  :parameters  (?bm ?bt)
  :precondition (and (clear ?bm) (clear ?bt) (on-table ?bm))
  :effect (and (on ?bm ?bt)
               (not (clear ?bt)) (not (on-table ?bm)))))

