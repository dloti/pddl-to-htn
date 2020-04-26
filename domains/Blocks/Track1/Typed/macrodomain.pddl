;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 4 Op-blocks world
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (domain BLOCKS)
  (:requirements :strips :typing)
  (:types block)
  (:predicates (on ?x - block ?y - block)
	       (ontable ?x - block)
	       (clear ?x - block)
	       (handempty)
	       (holding ?x - block)
	       )

   (:action pick-up-stack
	     :parameters (?x - block ?y - block)
	     :precondition (and (clear ?x) (ontable ?x) (clear ?y))
	     :effect
	     (and (not (ontable ?x))
		   (clear ?x)
		   (not (clear ?y))
		   (on ?x ?y) )
	     )

    (:action unstack-put-down
	     :parameters (?x - block ?y - block)
	     :precondition (and (on ?x ?y) (clear ?x))
	     :effect
	     (and 
		   (ontable ?x)
	       (clear ?y)
		   (not (on ?x ?y))
	     )
	     )

    (:action unstack-stack
	     :parameters (?x - block ?y - block ?z - block)
	     :precondition (and (on ?x ?y) (clear ?x) (clear ?z) )
	     :effect
	     (and 
		   (clear ?y)
		   (not (on ?x ?y))
		   (on ?x ?z) 
		   (not (clear ?z)))
	     )
    )
