(define (domain satellite)
(:requirements :fluents :equality :negative-preconditions :conditional-effects)
(:predicates
	 (on_board ?i ?s) (supports ?i ?m) (pointing ?s ?d) (power_avail ?s) (power_on ?i) (calibrated ?i) (have_image ?d ?m) (calibration_target ?i ?d)(satellite ?x) (direction ?x) (instrument ?x) (mode ?x) )
(:functions
	 (data_capacity ?s) (data ?d ?m) (slew_time ?a ?b) (data-stored) (fuel ?s) (fuel-used))
(:action turn_to
 :parameters ( ?s ?d_new ?d_prev)
 :precondition
	(and (satellite ?s) (direction ?d_new) (direction ?d_prev)  (pointing ?s ?d_prev) (not (= ?d_new ?d_prev)) (>= (fuel ?s) (slew_time ?d_new ?d_prev)))
 :effect
	(and (pointing ?s ?d_new) (not (pointing ?s ?d_prev)) (decrease (fuel ?s) (slew_time ?d_new ?d_prev)) (increase (fuel-used) (slew_time ?d_new ?d_prev))))

(:action switch_on
 :parameters ( ?i ?s)
 :precondition
	(and (instrument ?i) (satellite ?s)  (on_board ?i ?s) (power_avail ?s))
 :effect
	(and (power_on ?i) 
	(when (calibrated ?i) (not (calibrated ?i))) 
	(not (power_avail ?s))))

(:action switch_off
 :parameters ( ?i ?s)
 :precondition
	(and (instrument ?i) (satellite ?s)  (on_board ?i ?s) (power_on ?i))
 :effect
	(and (power_avail ?s) (not (power_on ?i))))

(:action calibrate
 :parameters ( ?s ?i ?d)
 :precondition
	(and (satellite ?s) (instrument ?i) (direction ?d)  (on_board ?i ?s) (calibration_target ?i ?d) (pointing ?s ?d) (power_on ?i))
 :effect
	 (calibrated ?i))

(:action take_image
 :parameters ( ?s ?d ?i ?m)
 :precondition
	(and (satellite ?s) (direction ?d) (instrument ?i) (mode ?m)  (calibrated ?i) (on_board ?i ?s) (supports ?i ?m) (power_on ?i) (pointing ?s ?d) (power_on ?i) (>= (data_capacity ?s) (data ?d ?m)))
 :effect
	(when (not (have_image ?d ?m))
		(and (have_image ?d ?m) (decrease (data_capacity ?s) (data ?d ?m)) (increase (data-stored) (data ?d ?m)))))

)
