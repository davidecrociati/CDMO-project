(set-logic QF_LIA)
(declare-fun num_couriers () Int)
(assert (= num_couriers 2))
(declare-fun num_items () Int)
(assert (= num_items 6))
(declare-fun lower_bound () Int)
(assert (= lower_bound 8))
(declare-fun upper_bound () Int)
(assert (= upper_bound 40))
(declare-fun courier_1_capa () Int)
(assert (= courier_1_capa 15))
(declare-fun courier_2_capa () Int)
(assert (= courier_2_capa 10))
(declare-fun item_1_size () Int)
(assert (= item_1_size 3))
(declare-fun item_2_size () Int)
(assert (= item_2_size 2))
(declare-fun item_3_size () Int)
(assert (= item_3_size 6))
(declare-fun item_4_size () Int)
(assert (= item_4_size 5))
(declare-fun item_5_size () Int)
(assert (= item_5_size 4))
(declare-fun item_6_size () Int)
(assert (= item_6_size 4))
(declare-fun distance_1_1 () Int)
(assert (= distance_1_1 0))
(declare-fun distance_1_2 () Int)
(assert (= distance_1_2 3))
(declare-fun distance_1_3 () Int)
(assert (= distance_1_3 4))
(declare-fun distance_1_4 () Int)
(assert (= distance_1_4 5))
(declare-fun distance_1_5 () Int)
(assert (= distance_1_5 6))
(declare-fun distance_1_6 () Int)
(assert (= distance_1_6 6))
(declare-fun distance_1_7 () Int)
(assert (= distance_1_7 2))
(declare-fun distance_2_1 () Int)
(assert (= distance_2_1 3))
(declare-fun distance_2_2 () Int)
(assert (= distance_2_2 0))
(declare-fun distance_2_3 () Int)
(assert (= distance_2_3 1))
(declare-fun distance_2_4 () Int)
(assert (= distance_2_4 4))
(declare-fun distance_2_5 () Int)
(assert (= distance_2_5 5))
(declare-fun distance_2_6 () Int)
(assert (= distance_2_6 7))
(declare-fun distance_2_7 () Int)
(assert (= distance_2_7 3))
(declare-fun distance_3_1 () Int)
(assert (= distance_3_1 4))
(declare-fun distance_3_2 () Int)
(assert (= distance_3_2 1))
(declare-fun distance_3_3 () Int)
(assert (= distance_3_3 0))
(declare-fun distance_3_4 () Int)
(assert (= distance_3_4 5))
(declare-fun distance_3_5 () Int)
(assert (= distance_3_5 6))
(declare-fun distance_3_6 () Int)
(assert (= distance_3_6 6))
(declare-fun distance_3_7 () Int)
(assert (= distance_3_7 4))
(declare-fun distance_4_1 () Int)
(assert (= distance_4_1 4))
(declare-fun distance_4_2 () Int)
(assert (= distance_4_2 4))
(declare-fun distance_4_3 () Int)
(assert (= distance_4_3 5))
(declare-fun distance_4_4 () Int)
(assert (= distance_4_4 0))
(declare-fun distance_4_5 () Int)
(assert (= distance_4_5 3))
(declare-fun distance_4_6 () Int)
(assert (= distance_4_6 3))
(declare-fun distance_4_7 () Int)
(assert (= distance_4_7 2))
(declare-fun distance_5_1 () Int)
(assert (= distance_5_1 6))
(declare-fun distance_5_2 () Int)
(assert (= distance_5_2 7))
(declare-fun distance_5_3 () Int)
(assert (= distance_5_3 8))
(declare-fun distance_5_4 () Int)
(assert (= distance_5_4 3))
(declare-fun distance_5_5 () Int)
(assert (= distance_5_5 0))
(declare-fun distance_5_6 () Int)
(assert (= distance_5_6 2))
(declare-fun distance_5_7 () Int)
(assert (= distance_5_7 4))
(declare-fun distance_6_1 () Int)
(assert (= distance_6_1 6))
(declare-fun distance_6_2 () Int)
(assert (= distance_6_2 7))
(declare-fun distance_6_3 () Int)
(assert (= distance_6_3 8))
(declare-fun distance_6_4 () Int)
(assert (= distance_6_4 3))
(declare-fun distance_6_5 () Int)
(assert (= distance_6_5 2))
(declare-fun distance_6_6 () Int)
(assert (= distance_6_6 0))
(declare-fun distance_6_7 () Int)
(assert (= distance_6_7 4))
(declare-fun distance_7_1 () Int)
(assert (= distance_7_1 2))
(declare-fun distance_7_2 () Int)
(assert (= distance_7_2 3))
(declare-fun distance_7_3 () Int)
(assert (= distance_7_3 4))
(declare-fun distance_7_4 () Int)
(assert (= distance_7_4 3))
(declare-fun distance_7_5 () Int)
(assert (= distance_7_5 4))
(declare-fun distance_7_6 () Int)
(assert (= distance_7_6 4))
(declare-fun distance_7_7 () Int)
(assert (= distance_7_7 0))
(declare-fun stop_1_3 () Int)
(assert (>= stop_1_3 1))
(assert (<= stop_1_3 7))
(declare-fun stop_1_4 () Int)
(assert (>= stop_1_4 1))
(assert (<= stop_1_4 7))
(declare-fun stop_1_5 () Int)
(assert (>= stop_1_5 1))
(assert (<= stop_1_5 7))
(declare-fun stop_1_6 () Int)
(assert (>= stop_1_6 1))
(assert (<= stop_1_6 7))
(declare-fun stop_1_7 () Int)
(assert (>= stop_1_7 1))
(assert (<= stop_1_7 7))
(declare-fun stop_2_3 () Int)
(assert (>= stop_2_3 1))
(assert (<= stop_2_3 7))
(declare-fun stop_2_4 () Int)
(assert (>= stop_2_4 1))
(assert (<= stop_2_4 7))
(declare-fun stop_2_5 () Int)
(assert (>= stop_2_5 1))
(assert (<= stop_2_5 7))
(declare-fun stop_2_6 () Int)
(assert (>= stop_2_6 1))
(assert (<= stop_2_6 7))
(declare-fun stop_2_7 () Int)
(assert (>= stop_2_7 1))
(assert (<= stop_2_7 7))
(declare-fun item_1_resp () Int)
(assert (>= item_1_resp 1))
(assert (<= item_1_resp 2))
(declare-fun item_2_resp () Int)
(assert (>= item_2_resp 1))
(assert (<= item_2_resp 2))
(declare-fun item_3_resp () Int)
(assert (>= item_3_resp 1))
(assert (<= item_3_resp 2))
(declare-fun item_4_resp () Int)
(assert (>= item_4_resp 1))
(assert (<= item_4_resp 2))
(declare-fun item_5_resp () Int)
(assert (>= item_5_resp 1))
(assert (<= item_5_resp 2))
(declare-fun item_6_resp () Int)
(assert (>= item_6_resp 1))
(assert (<= item_6_resp 2))
(declare-fun distance_1_traveled () Int)
(assert (>= distance_1_traveled 0))
(assert (<= distance_1_traveled 40))
(declare-fun distance_2_traveled () Int)
(assert (>= distance_2_traveled 0))
(assert (<= distance_2_traveled 40))
(declare-fun load_1 () Int)
(assert (= load_1 (+(ite (= item_1_resp 1) item_1_size 0)(ite (= item_2_resp 1) item_2_size 0)(ite (= item_3_resp 1) item_3_size 0)(ite (= item_4_resp 1) item_4_size 0)(ite (= item_5_resp 1) item_5_size 0)(ite (= item_6_resp 1) item_6_size 0))))
(assert (>= courier_1_capa load_1))
(declare-fun load_2 () Int)
(assert (= load_2 (+(ite (= item_1_resp 2) item_1_size 0)(ite (= item_2_resp 2) item_2_size 0)(ite (= item_3_resp 2) item_3_size 0)(ite (= item_4_resp 2) item_4_size 0)(ite (= item_5_resp 2) item_5_size 0)(ite (= item_6_resp 2) item_6_size 0))))
(assert (>= courier_2_capa load_2))
(declare-fun stop_1_1 () Int)
(declare-fun stop_1_8 () Int)
(assert (= stop_1_1 7))
(assert (= stop_1_8 7))
(declare-fun stop_2_1 () Int)
(declare-fun stop_2_8 () Int)
(assert (= stop_2_1 7))
(assert (= stop_2_8 7))
(assert (or (= item_1_resp 1)(= item_2_resp 1)(= item_3_resp 1)(= item_4_resp 1)(= item_5_resp 1)(= item_6_resp 1)))
(assert (or (= item_1_resp 2)(= item_2_resp 2)(= item_3_resp 2)(= item_4_resp 2)(= item_5_resp 2)(= item_6_resp 2)))
(declare-fun stop_1_2 () Int)
(assert (>= stop_1_2 1))
(assert (<= stop_1_2 6))
(declare-fun stop_2_2 () Int)
(assert (>= stop_2_2 1))
(assert (<= stop_2_2 6))
(assert (=> (> courier_1_capa courier_2_capa) (> load_1 load_2)))
(assert (=> (> courier_2_capa courier_1_capa) (> load_2 load_1)))
(assert (= (+(ite (= stop_1_2 1) 1 0) (ite (= stop_1_3 1) 1 0) (ite (= stop_1_4 1) 1 0) (ite (= stop_1_5 1) 1 0) (ite (= stop_1_6 1) 1 0) (ite (= stop_1_7 1) 1 0) (ite (= stop_2_2 1) 1 0) (ite (= stop_2_3 1) 1 0) (ite (= stop_2_4 1) 1 0) (ite (= stop_2_5 1) 1 0) (ite (= stop_2_6 1) 1 0) (ite (= stop_2_7 1) 1 0) ) 1))(assert (= (+(ite (= stop_1_2 2) 1 0) (ite (= stop_1_3 2) 1 0) (ite (= stop_1_4 2) 1 0) (ite (= stop_1_5 2) 1 0) (ite (= stop_1_6 2) 1 0) (ite (= stop_1_7 2) 1 0) (ite (= stop_2_2 2) 1 0) (ite (= stop_2_3 2) 1 0) (ite (= stop_2_4 2) 1 0) (ite (= stop_2_5 2) 1 0) (ite (= stop_2_6 2) 1 0) (ite (= stop_2_7 2) 1 0) ) 1))(assert (= (+(ite (= stop_1_2 3) 1 0) (ite (= stop_1_3 3) 1 0) (ite (= stop_1_4 3) 1 0) (ite (= stop_1_5 3) 1 0) (ite (= stop_1_6 3) 1 0) (ite (= stop_1_7 3) 1 0) (ite (= stop_2_2 3) 1 0) (ite (= stop_2_3 3) 1 0) (ite (= stop_2_4 3) 1 0) (ite (= stop_2_5 3) 1 0) (ite (= stop_2_6 3) 1 0) (ite (= stop_2_7 3) 1 0) ) 1))(assert (= (+(ite (= stop_1_2 4) 1 0) (ite (= stop_1_3 4) 1 0) (ite (= stop_1_4 4) 1 0) (ite (= stop_1_5 4) 1 0) (ite (= stop_1_6 4) 1 0) (ite (= stop_1_7 4) 1 0) (ite (= stop_2_2 4) 1 0) (ite (= stop_2_3 4) 1 0) (ite (= stop_2_4 4) 1 0) (ite (= stop_2_5 4) 1 0) (ite (= stop_2_6 4) 1 0) (ite (= stop_2_7 4) 1 0) ) 1))(assert (= (+(ite (= stop_1_2 5) 1 0) (ite (= stop_1_3 5) 1 0) (ite (= stop_1_4 5) 1 0) (ite (= stop_1_5 5) 1 0) (ite (= stop_1_6 5) 1 0) (ite (= stop_1_7 5) 1 0) (ite (= stop_2_2 5) 1 0) (ite (= stop_2_3 5) 1 0) (ite (= stop_2_4 5) 1 0) (ite (= stop_2_5 5) 1 0) (ite (= stop_2_6 5) 1 0) (ite (= stop_2_7 5) 1 0) ) 1))(assert (= (+(ite (= stop_1_2 6) 1 0) (ite (= stop_1_3 6) 1 0) (ite (= stop_1_4 6) 1 0) (ite (= stop_1_5 6) 1 0) (ite (= stop_1_6 6) 1 0) (ite (= stop_1_7 6) 1 0) (ite (= stop_2_2 6) 1 0) (ite (= stop_2_3 6) 1 0) (ite (= stop_2_4 6) 1 0) (ite (= stop_2_5 6) 1 0) (ite (= stop_2_6 6) 1 0) (ite (= stop_2_7 6) 1 0) ) 1))(assert (=> (<= 1 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) (ite (= item_4_resp 1) 1 0) (ite (= item_5_resp 1) 1 0) (ite (= item_6_resp 1) 1 0) )) (< stop_1_2 7)))
(assert (=> (< stop_1_2 7) (<= 1 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) (ite (= item_4_resp 1) 1 0) (ite (= item_5_resp 1) 1 0) (ite (= item_6_resp 1) 1 0) ))))
(assert (=> (<= 2 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) (ite (= item_4_resp 1) 1 0) (ite (= item_5_resp 1) 1 0) (ite (= item_6_resp 1) 1 0) )) (< stop_1_3 7)))
(assert (=> (< stop_1_3 7) (<= 2 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) (ite (= item_4_resp 1) 1 0) (ite (= item_5_resp 1) 1 0) (ite (= item_6_resp 1) 1 0) ))))
(assert (=> (<= 3 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) (ite (= item_4_resp 1) 1 0) (ite (= item_5_resp 1) 1 0) (ite (= item_6_resp 1) 1 0) )) (< stop_1_4 7)))
(assert (=> (< stop_1_4 7) (<= 3 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) (ite (= item_4_resp 1) 1 0) (ite (= item_5_resp 1) 1 0) (ite (= item_6_resp 1) 1 0) ))))
(assert (=> (<= 4 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) (ite (= item_4_resp 1) 1 0) (ite (= item_5_resp 1) 1 0) (ite (= item_6_resp 1) 1 0) )) (< stop_1_5 7)))
(assert (=> (< stop_1_5 7) (<= 4 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) (ite (= item_4_resp 1) 1 0) (ite (= item_5_resp 1) 1 0) (ite (= item_6_resp 1) 1 0) ))))
(assert (=> (<= 5 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) (ite (= item_4_resp 1) 1 0) (ite (= item_5_resp 1) 1 0) (ite (= item_6_resp 1) 1 0) )) (< stop_1_6 7)))
(assert (=> (< stop_1_6 7) (<= 5 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) (ite (= item_4_resp 1) 1 0) (ite (= item_5_resp 1) 1 0) (ite (= item_6_resp 1) 1 0) ))))
(assert (=> (<= 6 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) (ite (= item_4_resp 1) 1 0) (ite (= item_5_resp 1) 1 0) (ite (= item_6_resp 1) 1 0) )) (< stop_1_7 7)))
(assert (=> (< stop_1_7 7) (<= 6 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) (ite (= item_4_resp 1) 1 0) (ite (= item_5_resp 1) 1 0) (ite (= item_6_resp 1) 1 0) ))))
(assert (=> (<= 1 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) (ite (= item_4_resp 2) 1 0) (ite (= item_5_resp 2) 1 0) (ite (= item_6_resp 2) 1 0) )) (< stop_2_2 7)))
(assert (=> (< stop_2_2 7) (<= 1 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) (ite (= item_4_resp 2) 1 0) (ite (= item_5_resp 2) 1 0) (ite (= item_6_resp 2) 1 0) ))))
(assert (=> (<= 2 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) (ite (= item_4_resp 2) 1 0) (ite (= item_5_resp 2) 1 0) (ite (= item_6_resp 2) 1 0) )) (< stop_2_3 7)))
(assert (=> (< stop_2_3 7) (<= 2 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) (ite (= item_4_resp 2) 1 0) (ite (= item_5_resp 2) 1 0) (ite (= item_6_resp 2) 1 0) ))))
(assert (=> (<= 3 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) (ite (= item_4_resp 2) 1 0) (ite (= item_5_resp 2) 1 0) (ite (= item_6_resp 2) 1 0) )) (< stop_2_4 7)))
(assert (=> (< stop_2_4 7) (<= 3 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) (ite (= item_4_resp 2) 1 0) (ite (= item_5_resp 2) 1 0) (ite (= item_6_resp 2) 1 0) ))))
(assert (=> (<= 4 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) (ite (= item_4_resp 2) 1 0) (ite (= item_5_resp 2) 1 0) (ite (= item_6_resp 2) 1 0) )) (< stop_2_5 7)))
(assert (=> (< stop_2_5 7) (<= 4 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) (ite (= item_4_resp 2) 1 0) (ite (= item_5_resp 2) 1 0) (ite (= item_6_resp 2) 1 0) ))))
(assert (=> (<= 5 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) (ite (= item_4_resp 2) 1 0) (ite (= item_5_resp 2) 1 0) (ite (= item_6_resp 2) 1 0) )) (< stop_2_6 7)))
(assert (=> (< stop_2_6 7) (<= 5 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) (ite (= item_4_resp 2) 1 0) (ite (= item_5_resp 2) 1 0) (ite (= item_6_resp 2) 1 0) ))))
(assert (=> (<= 6 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) (ite (= item_4_resp 2) 1 0) (ite (= item_5_resp 2) 1 0) (ite (= item_6_resp 2) 1 0) )) (< stop_2_7 7)))
(assert (=> (< stop_2_7 7) (<= 6 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) (ite (= item_4_resp 2) 1 0) (ite (= item_5_resp 2) 1 0) (ite (= item_6_resp 2) 1 0) ))))
(assert (=> (= item_1_resp 1) (or (= stop_1_2 1)(= stop_1_3 1)(= stop_1_4 1)(= stop_1_5 1)(= stop_1_6 1)(= stop_1_7 1))))
(assert (=> (= item_2_resp 1) (or (= stop_1_2 2)(= stop_1_3 2)(= stop_1_4 2)(= stop_1_5 2)(= stop_1_6 2)(= stop_1_7 2))))
(assert (=> (= item_3_resp 1) (or (= stop_1_2 3)(= stop_1_3 3)(= stop_1_4 3)(= stop_1_5 3)(= stop_1_6 3)(= stop_1_7 3))))
(assert (=> (= item_4_resp 1) (or (= stop_1_2 4)(= stop_1_3 4)(= stop_1_4 4)(= stop_1_5 4)(= stop_1_6 4)(= stop_1_7 4))))
(assert (=> (= item_5_resp 1) (or (= stop_1_2 5)(= stop_1_3 5)(= stop_1_4 5)(= stop_1_5 5)(= stop_1_6 5)(= stop_1_7 5))))
(assert (=> (= item_6_resp 1) (or (= stop_1_2 6)(= stop_1_3 6)(= stop_1_4 6)(= stop_1_5 6)(= stop_1_6 6)(= stop_1_7 6))))
(assert (=> (= item_1_resp 2) (or (= stop_2_2 1)(= stop_2_3 1)(= stop_2_4 1)(= stop_2_5 1)(= stop_2_6 1)(= stop_2_7 1))))
(assert (=> (= item_2_resp 2) (or (= stop_2_2 2)(= stop_2_3 2)(= stop_2_4 2)(= stop_2_5 2)(= stop_2_6 2)(= stop_2_7 2))))
(assert (=> (= item_3_resp 2) (or (= stop_2_2 3)(= stop_2_3 3)(= stop_2_4 3)(= stop_2_5 3)(= stop_2_6 3)(= stop_2_7 3))))
(assert (=> (= item_4_resp 2) (or (= stop_2_2 4)(= stop_2_3 4)(= stop_2_4 4)(= stop_2_5 4)(= stop_2_6 4)(= stop_2_7 4))))
(assert (=> (= item_5_resp 2) (or (= stop_2_2 5)(= stop_2_3 5)(= stop_2_4 5)(= stop_2_5 5)(= stop_2_6 5)(= stop_2_7 5))))
(assert (=> (= item_6_resp 2) (or (= stop_2_2 6)(= stop_2_3 6)(= stop_2_4 6)(= stop_2_5 6)(= stop_2_6 6)(= stop_2_7 6))))
(declare-const successors (Array Int Int))
(assert (=> (not (= stop_1_2 7)) (= (select successors stop_1_2) stop_1_3)))
(assert (=> (not (= stop_1_3 7)) (= (select successors stop_1_3) stop_1_4)))
(assert (=> (not (= stop_1_4 7)) (= (select successors stop_1_4) stop_1_5)))
(assert (=> (not (= stop_1_5 7)) (= (select successors stop_1_5) stop_1_6)))
(assert (=> (not (= stop_1_6 7)) (= (select successors stop_1_6) stop_1_7)))
(assert (=> (not (= stop_1_7 7)) (= (select successors stop_1_7) stop_1_8)))
(assert (=> (not (= stop_1_8 7)) (= (select successors stop_1_8) stop_1_9)))
(assert (=> (not (= stop_2_2 7)) (= (select successors stop_2_2) stop_2_3)))
(assert (=> (not (= stop_2_3 7)) (= (select successors stop_2_3) stop_2_4)))
(assert (=> (not (= stop_2_4 7)) (= (select successors stop_2_4) stop_2_5)))
(assert (=> (not (= stop_2_5 7)) (= (select successors stop_2_5) stop_2_6)))
(assert (=> (not (= stop_2_6 7)) (= (select successors stop_2_6) stop_2_7)))
(assert (=> (not (= stop_2_7 7)) (= (select successors stop_2_7) stop_2_8)))
(assert (=> (not (= stop_2_8 7)) (= (select successors stop_2_8) stop_2_9)))
(assert (> distance_1_traveled 0))
(assert (<= distance_1_traveled 40))
(assert (> distance_2_traveled 0))
(assert (<= distance_2_traveled 40))
(check-sat)
(get-model)
