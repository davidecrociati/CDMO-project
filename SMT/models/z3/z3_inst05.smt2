(set-logic ALL)
(declare-fun num_couriers () Int)
(assert (= num_couriers 2))
(declare-fun num_items () Int)
(assert (= num_items 3))
(declare-fun lower_bound () Int)
(assert (= lower_bound 160))
(declare-fun upper_bound () Int)
(assert (= upper_bound 271))
(declare-fun courier_1_capa () Int)
(assert (= courier_1_capa 18))
(declare-fun courier_2_capa () Int)
(assert (= courier_2_capa 30))
(declare-fun item_1_size () Int)
(assert (= item_1_size 20))
(declare-fun item_2_size () Int)
(assert (= item_2_size 17))
(declare-fun item_3_size () Int)
(assert (= item_3_size 6))
(declare-fun distance_1_1 () Int)
(assert (= distance_1_1 0))
(declare-fun distance_1_2 () Int)
(assert (= distance_1_2 21))
(declare-fun distance_1_3 () Int)
(assert (= distance_1_3 86))
(declare-fun distance_1_4 () Int)
(assert (= distance_1_4 99))
(declare-fun distance_2_1 () Int)
(assert (= distance_2_1 21))
(declare-fun distance_2_2 () Int)
(assert (= distance_2_2 0))
(declare-fun distance_2_3 () Int)
(assert (= distance_2_3 71))
(declare-fun distance_2_4 () Int)
(assert (= distance_2_4 80))
(declare-fun distance_3_1 () Int)
(assert (= distance_3_1 92))
(declare-fun distance_3_2 () Int)
(assert (= distance_3_2 71))
(declare-fun distance_3_3 () Int)
(assert (= distance_3_3 0))
(declare-fun distance_3_4 () Int)
(assert (= distance_3_4 61))
(declare-fun distance_4_1 () Int)
(assert (= distance_4_1 59))
(declare-fun distance_4_2 () Int)
(assert (= distance_4_2 80))
(declare-fun distance_4_3 () Int)
(assert (= distance_4_3 61))
(declare-fun distance_4_4 () Int)
(assert (= distance_4_4 0))
(declare-fun stop_1_3 () Int)
(assert (>= stop_1_3 1))
(assert (<= stop_1_3 4))
(declare-fun stop_1_4 () Int)
(assert (>= stop_1_4 1))
(assert (<= stop_1_4 4))
(declare-fun stop_2_3 () Int)
(assert (>= stop_2_3 1))
(assert (<= stop_2_3 4))
(declare-fun stop_2_4 () Int)
(assert (>= stop_2_4 1))
(assert (<= stop_2_4 4))
(declare-fun item_1_resp () Int)
(assert (>= item_1_resp 1))
(assert (<= item_1_resp 2))
(declare-fun item_2_resp () Int)
(assert (>= item_2_resp 1))
(assert (<= item_2_resp 2))
(declare-fun item_3_resp () Int)
(assert (>= item_3_resp 1))
(assert (<= item_3_resp 2))
(declare-fun distance_1_traveled () Int)
(assert (>= distance_1_traveled 0))
(assert (<= distance_1_traveled 271))
(declare-fun distance_2_traveled () Int)
(assert (>= distance_2_traveled 0))
(assert (<= distance_2_traveled 271))
(declare-fun load_1 () Int)
(assert (= load_1 (+(ite (= item_1_resp 1) item_1_size 0)(ite (= item_2_resp 1) item_2_size 0)(ite (= item_3_resp 1) item_3_size 0))))
(assert (<= load_1 courier_1_capa))
(declare-fun load_2 () Int)
(assert (= load_2 (+(ite (= item_1_resp 2) item_1_size 0)(ite (= item_2_resp 2) item_2_size 0)(ite (= item_3_resp 2) item_3_size 0))))
(assert (<= load_2 courier_2_capa))
(declare-fun stop_1_1 () Int)
(declare-fun stop_1_5 () Int)
(assert (= stop_1_1 4))
(assert (= stop_1_5 4))
(declare-fun stop_2_1 () Int)
(declare-fun stop_2_5 () Int)
(assert (= stop_2_1 4))
(assert (= stop_2_5 4))
(assert (or (= item_1_resp 1)(= item_2_resp 1)(= item_3_resp 1)))
(assert (or (= item_1_resp 2)(= item_2_resp 2)(= item_3_resp 2)))
(declare-fun stop_1_2 () Int)
(assert (>= stop_1_2 1))
(assert (<= stop_1_2 3))
(declare-fun stop_2_2 () Int)
(assert (>= stop_2_2 1))
(assert (<= stop_2_2 3))
(assert (=> (> courier_1_capa courier_2_capa) (> load_1 load_2)))(assert (=> (<= 1 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) )) (< stop_1_2 4)))
(assert (=> (< stop_1_2 4) (<= 1 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) ))))
(assert (=> (<= 2 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) )) (< stop_1_3 4)))
(assert (=> (< stop_1_3 4) (<= 2 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) ))))
(assert (=> (<= 3 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) )) (< stop_1_4 4)))
(assert (=> (< stop_1_4 4) (<= 3 (+ (ite (= item_1_resp 1) 1 0) (ite (= item_2_resp 1) 1 0) (ite (= item_3_resp 1) 1 0) ))))
(assert (=> (<= 1 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) )) (< stop_2_2 4)))
(assert (=> (< stop_2_2 4) (<= 1 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) ))))
(assert (=> (<= 2 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) )) (< stop_2_3 4)))
(assert (=> (< stop_2_3 4) (<= 2 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) ))))
(assert (=> (<= 3 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) )) (< stop_2_4 4)))
(assert (=> (< stop_2_4 4) (<= 3 (+ (ite (= item_1_resp 2) 1 0) (ite (= item_2_resp 2) 1 0) (ite (= item_3_resp 2) 1 0) ))))
(assert (=> (= item_1_resp 1) (or (= stop_1_2 1)(= stop_1_3 1)(= stop_1_4 1))))
(assert (=> (= item_2_resp 1) (or (= stop_1_2 2)(= stop_1_3 2)(= stop_1_4 2))))
(assert (=> (= item_3_resp 1) (or (= stop_1_2 3)(= stop_1_3 3)(= stop_1_4 3))))
(assert (=> (= item_1_resp 2) (or (= stop_2_2 1)(= stop_2_3 1)(= stop_2_4 1))))
(assert (=> (= item_2_resp 2) (or (= stop_2_2 2)(= stop_2_3 2)(= stop_2_4 2))))
(assert (=> (= item_3_resp 2) (or (= stop_2_2 3)(= stop_2_3 3)(= stop_2_4 3))))
(declare-fun successor_of_1 () Int)
(assert (> successor_of_1 0))
(assert (<= successor_of_1 4))
(declare-fun successor_of_2 () Int)
(assert (> successor_of_2 0))
(assert (<= successor_of_2 4))
(declare-fun successor_of_3 () Int)
(assert (> successor_of_3 0))
(assert (<= successor_of_3 4))
(assert (=> (not (= stop_1_2 4)) (= stop_1_2 1) (= successor_of_1 stop_1_3)))
(assert (=> (not (= stop_1_2 4)) (= stop_1_2 2) (= successor_of_2 stop_1_3)))
(assert (=> (not (= stop_1_2 4)) (= stop_1_2 3) (= successor_of_3 stop_1_3)))
(assert (=> (not (= stop_1_3 4)) (= stop_1_3 1) (= successor_of_1 stop_1_4)))
(assert (=> (not (= stop_1_3 4)) (= stop_1_3 2) (= successor_of_2 stop_1_4)))
(assert (=> (not (= stop_1_3 4)) (= stop_1_3 3) (= successor_of_3 stop_1_4)))
(assert (=> (not (= stop_1_4 4)) (= stop_1_4 1) (= successor_of_1 stop_1_5)))
(assert (=> (not (= stop_1_4 4)) (= stop_1_4 2) (= successor_of_2 stop_1_5)))
(assert (=> (not (= stop_1_4 4)) (= stop_1_4 3) (= successor_of_3 stop_1_5)))
(assert (=> (not (= stop_2_2 4)) (= stop_2_2 1) (= successor_of_1 stop_2_3)))
(assert (=> (not (= stop_2_2 4)) (= stop_2_2 2) (= successor_of_2 stop_2_3)))
(assert (=> (not (= stop_2_2 4)) (= stop_2_2 3) (= successor_of_3 stop_2_3)))
(assert (=> (not (= stop_2_3 4)) (= stop_2_3 1) (= successor_of_1 stop_2_4)))
(assert (=> (not (= stop_2_3 4)) (= stop_2_3 2) (= successor_of_2 stop_2_4)))
(assert (=> (not (= stop_2_3 4)) (= stop_2_3 3) (= successor_of_3 stop_2_4)))
(assert (=> (not (= stop_2_4 4)) (= stop_2_4 1) (= successor_of_1 stop_2_5)))
(assert (=> (not (= stop_2_4 4)) (= stop_2_4 2) (= successor_of_2 stop_2_5)))
(assert (=> (not (= stop_2_4 4)) (= stop_2_4 3) (= successor_of_3 stop_2_5)))
(assert (= distance_1_traveled (+ (ite (and (= item_1_resp 1) (= successor_of_1 1) ) distance_1_1 0)(ite (and (= item_1_resp 1) (= successor_of_1 2) ) distance_1_2 0)(ite (and (= item_1_resp 1) (= successor_of_1 3) ) distance_1_3 0)(ite (and (= item_1_resp 1) (= successor_of_1 4) ) distance_1_4 0)(ite (and (= item_2_resp 1) (= successor_of_2 1) ) distance_2_1 0)(ite (and (= item_2_resp 1) (= successor_of_2 2) ) distance_2_2 0)(ite (and (= item_2_resp 1) (= successor_of_2 3) ) distance_2_3 0)(ite (and (= item_2_resp 1) (= successor_of_2 4) ) distance_2_4 0)(ite (and (= item_3_resp 1) (= successor_of_3 1) ) distance_3_1 0)(ite (and (= item_3_resp 1) (= successor_of_3 2) ) distance_3_2 0)(ite (and (= item_3_resp 1) (= successor_of_3 3) ) distance_3_3 0)(ite (and (= item_3_resp 1) (= successor_of_3 4) ) distance_3_4 0)(ite (= 1 stop_1_2) distance_4_1 0)(ite (= 2 stop_1_2) distance_4_2 0)(ite (= 3 stop_1_2) distance_4_3 0)(ite (= 4 stop_1_2) distance_4_4 0))))
(assert (= distance_2_traveled (+ (ite (and (= item_1_resp 2) (= successor_of_1 1) ) distance_1_1 0)(ite (and (= item_1_resp 2) (= successor_of_1 2) ) distance_1_2 0)(ite (and (= item_1_resp 2) (= successor_of_1 3) ) distance_1_3 0)(ite (and (= item_1_resp 2) (= successor_of_1 4) ) distance_1_4 0)(ite (and (= item_2_resp 2) (= successor_of_2 1) ) distance_2_1 0)(ite (and (= item_2_resp 2) (= successor_of_2 2) ) distance_2_2 0)(ite (and (= item_2_resp 2) (= successor_of_2 3) ) distance_2_3 0)(ite (and (= item_2_resp 2) (= successor_of_2 4) ) distance_2_4 0)(ite (and (= item_3_resp 2) (= successor_of_3 1) ) distance_3_1 0)(ite (and (= item_3_resp 2) (= successor_of_3 2) ) distance_3_2 0)(ite (and (= item_3_resp 2) (= successor_of_3 3) ) distance_3_3 0)(ite (and (= item_3_resp 2) (= successor_of_3 4) ) distance_3_4 0)(ite (= 1 stop_2_2) distance_4_1 0)(ite (= 2 stop_2_2) distance_4_2 0)(ite (= 3 stop_2_2) distance_4_3 0)(ite (= 4 stop_2_2) distance_4_4 0))))
(assert (<= distance_1_traveled 206))
(assert (<= distance_2_traveled 206))
(check-sat)
(get-model)