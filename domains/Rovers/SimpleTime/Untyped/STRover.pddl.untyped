(define (domain rover)
(:requirements :durative-actions)
(:predicates
	 (at ?x ?y) (at_lander ?x ?y) (can_traverse ?r ?x ?y) (equipped_for_soil_analysis ?r) (equipped_for_rock_analysis ?r) (equipped_for_imaging ?r) (empty ?s) (have_rock_analysis ?r ?w) (have_soil_analysis ?r ?w) (full ?s) (calibrated ?c ?r) (supports ?c ?m) (available ?r) (visible ?w ?p) (have_image ?r ?o ?m) (communicated_soil_data ?w) (communicated_rock_data ?w) (communicated_image_data ?o ?m) (at_soil_sample ?w) (at_rock_sample ?w) (visible_from ?o ?w) (store_of ?s ?r) (calibration_target ?i ?o) (on_board ?i ?r) (channel_free ?l)(rover ?x) (waypoint ?x) (store ?x) (camera ?x) (mode ?x) (lander ?x) (objective ?x) )
(:durative-action navigate
 :parameters ( ?x ?y ?z)
:duration (= ?duration 5)
 :condition
	(and (at start (rover ?x)) (at start (waypoint ?y)) (at start (waypoint ?z))  (over all (can_traverse ?x ?y ?z)) (at start (available ?x)) (at start (at ?x ?y)) (over all (visible ?y ?z)))
 :effect
	(and (at end  (at ?x ?z)) (at start  (not (at ?x ?y)))))

(:durative-action sample_soil
 :parameters ( ?x ?s ?p)
 :duration (= ?duration 10)
 :condition
	(and (at start (rover ?x)) (at start (store ?s)) (at start (waypoint ?p))  (over all (at ?x ?p)) (at start (at ?x ?p)) (at start (at_soil_sample ?p)) (at start (equipped_for_soil_analysis ?x)) (at start (store_of ?s ?x)) (at start (empty ?s)))
 :effect
	(and (at end  (not (at_soil_sample ?p))) (at end  (have_soil_analysis ?x ?p)) (at end  (full ?s)) (at start  (not (empty ?s)))))

(:durative-action sample_rock
 :parameters ( ?x ?s ?p)
:duration (= ?duration 8)
 :condition
	(and (at start (rover ?x)) (at start (store ?s)) (at start (waypoint ?p))  (over all (at ?x ?p)) (at start (at ?x ?p)) (at start (at_rock_sample ?p)) (at start (equipped_for_rock_analysis ?x)) (at start (store_of ?s ?x)) (at start (empty ?s)))
 :effect
	(and (at end  (not (at_rock_sample ?p))) (at end  (have_rock_analysis ?x ?p)) (at end  (full ?s)) (at start  (not (empty ?s)))))

(:durative-action drop
 :parameters ( ?x ?y)
:duration (= ?duration 1)
 :condition
	(and (at start (rover ?x)) (at start (store ?y))  (at start (store_of ?y ?x)) (at start (full ?y)))
 :effect
	(and (at end  (empty ?y)) (at end  (not (full ?y)))))

(:durative-action calibrate
 :parameters ( ?r ?i ?t ?w)
 :duration (= ?duration 5)
 :condition
	(and (at start (rover ?r)) (at start (camera ?i)) (at start (objective ?t)) (at start (waypoint ?w))  (at start (equipped_for_imaging ?r)) (at start (calibration_target ?i ?t)) (over all (at ?r ?w)) (at start (visible_from ?t ?w)) (at start (on_board ?i ?r)))
 :effect
	 (at end  (calibrated ?i ?r)))

(:durative-action take_image
 :parameters ( ?r ?p ?o ?i ?m)
 :duration (= ?duration 7)
 :condition
	(and (at start (rover ?r)) (at start (waypoint ?p)) (at start (objective ?o)) (at start (camera ?i)) (at start (mode ?m))  (over all (calibrated ?i ?r)) (at start (on_board ?i ?r)) (over all (equipped_for_imaging ?r)) (over all (supports ?i ?m)) (over all (visible_from ?o ?p)) (over all (at ?r ?p)))
 :effect
	(and (at end  (not (calibrated ?i ?r))) (at end  (have_image ?r ?o ?m))))

(:durative-action communicate_soil_data
 :parameters ( ?r ?l ?p ?x ?y)
:duration (= ?duration 10)
 :condition
	(and (at start (rover ?r)) (at start (lander ?l)) (at start (waypoint ?p)) (at start (waypoint ?x)) (at start (waypoint ?y))  (over all (at ?r ?x)) (over all (at_lander ?l ?y)) (at start (have_soil_analysis ?r ?p)) (at start (visible ?x ?y)) (at start (available ?r)) (at start (channel_free ?l)))
 :effect
	(and (at end  (available ?r)) (at end  (communicated_soil_data ?p)) (at end  (channel_free ?l)) (at start  (not (channel_free ?l))) (at start  (not (available ?r)))))

(:durative-action communicate_rock_data
 :parameters ( ?r ?l ?p ?x ?y)
 :duration (= ?duration 10)
 :condition
	(and (at start (rover ?r)) (at start (lander ?l)) (at start (waypoint ?p)) (at start (waypoint ?x)) (at start (waypoint ?y))  (over all (at ?r ?x)) (over all (at_lander ?l ?y)) (at start (have_rock_analysis ?r ?p)) (at start (visible ?x ?y)) (at start (available ?r)) (at start (channel_free ?l)))
 :effect
	(and (at end  (available ?r)) (at end  (communicated_rock_data ?p)) (at end  (channel_free ?l)) (at start  (not (channel_free ?l))) (at start  (not (available ?r)))))

(:durative-action communicate_image_data
 :parameters ( ?r ?l ?o ?m ?x ?y)
 :duration (= ?duration 15)
 :condition
	(and (at start (rover ?r)) (at start (lander ?l)) (at start (objective ?o)) (at start (mode ?m)) (at start (waypoint ?x)) (at start (waypoint ?y))  (over all (at ?r ?x)) (over all (at_lander ?l ?y)) (at start (have_image ?r ?o ?m)) (at start (visible ?x ?y)) (at start (available ?r)) (at start (channel_free ?l)))
 :effect
	(and (at end  (available ?r)) (at end  (communicated_image_data ?o ?m)) (at end  (channel_free ?l)) (at start  (not (channel_free ?l))) (at start  (not (available ?r)))))

)
