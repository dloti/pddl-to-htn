(define (domain satellite)
(:requirements :equality :fluents :durative-actions :negative-preconditions :conditional-effects)
(:predicates
	 (on_board ?i ?s) (supports ?i ?m) (pointing ?s ?d) (power_avail ?s) (power_on ?i) (calibrated ?i) (have_image ?d ?m) (calibration_target ?i ?d)(satellite ?x) (direction ?x) (instrument ?x) (mode ?x) )
(:functions
	 (slew_time ?a ?b) (calibration_time ?a ?d))
(:durative-action turn_to
 :parameters ( ?s ?d_new ?d_prev)
 :duration (= ?duration (slew_time ?d_prev ?d_new))
 :condition
	(and (at start (satellite ?s)) (at start (direction ?d_new)) (at start (direction ?d_prev))  (at start (pointing ?s ?d_prev)) (over all (not (= ?d_new ?d_prev))))
 :effect
	(and (at start  (not (pointing ?s ?d_prev))) (at end  (pointing ?s ?d_new))))

(:durative-action switch_on
 :parameters ( ?i ?s)
 :duration (= ?duration 2)
 :condition
	(and (at start (instrument ?i)) (at start (satellite ?s))  (over all (on_board ?i ?s)) (at start (power_avail ?s)))
 :effect
	(and (at start  (not (power_avail ?s))) 
	(when (at start (calibrated ?i)) (at start  (not (calibrated ?i))))
	 (at end  (power_on ?i))))

(:durative-action switch_off
 :parameters ( ?i ?s)
 :duration (= ?duration 1)
 :condition
	(and (at start (instrument ?i)) (at start (satellite ?s))  (over all (on_board ?i ?s)) (at start (power_on ?i)))
 :effect
	(and (at end  (power_avail ?s)) (at start  (not (power_on ?i)))))

(:durative-action calibrate
 :parameters ( ?s ?i ?d)
 :duration (= ?duration (calibration_time ?i ?d))
 :condition
	(and (at start (satellite ?s)) (at start (instrument ?i)) (at start (direction ?d))  (over all (on_board ?i ?s)) (over all (calibration_target ?i ?d)) (at start (pointing ?s ?d)) (over all (power_on ?i)) (at end (power_on ?i)))
 :effect
	 (at end  (calibrated ?i)))

(:durative-action take_image
 :parameters ( ?s ?d ?i ?m)
 :duration (= ?duration 7)
 :condition
	(and (at start (satellite ?s)) (at start (direction ?d)) (at start (instrument ?i)) (at start (mode ?m))  (over all (calibrated ?i)) (over all (on_board ?i ?s)) (over all (supports ?i ?m)) (over all (power_on ?i)) (over all (pointing ?s ?d)) (at end (power_on ?i)))
 :effect
	 (when (at end (not (have_image ?d ?m))) (at end  (have_image ?d ?m))))

)
