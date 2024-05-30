
(set-logic ALL)
(declare-fun num_couriers () Int)
(assert (= num_couriers 2))
(declare-fun num_items () Int)
(assert (= num_items 3))
(declare-fun lower_bound () Int)
(assert (= lower_bound 160))
(declare-fun upper_bound () Int)
(assert (= upper_bound 271))

(declare-fun couriers_capa () (Array Int Int))
(assert (= (select couriers_capa 1) 18))
(assert (= (select couriers_capa 2) 30))
(declare-fun items_size () (Array Int Int))
(assert (= (select items_size 1) 20))
(assert (= (select items_size 2) 17))
(assert (= (select items_size 3) 6))
(declare-fun distances_1 () (Array Int Int))
(assert (= (select distances_1 1) 0))
(assert (= (select distances_1 2) 21))
(assert (= (select distances_1 3) 86))
(assert (= (select distances_1 4) 99))
(declare-fun distances_2 () (Array Int Int))
(assert (= (select distances_2 1) 21))
(assert (= (select distances_2 2) 0))
(assert (= (select distances_2 3) 71))
(assert (= (select distances_2 4) 80))
(declare-fun distances_3 () (Array Int Int))
(assert (= (select distances_3 1) 92))
(assert (= (select distances_3 2) 71))
(assert (= (select distances_3 3) 0))
(assert (= (select distances_3 4) 61))
(declare-fun distances_4 () (Array Int Int))
(assert (= (select distances_4 1) 59))
(assert (= (select distances_4 2) 80))
(assert (= (select distances_4 3) 61))
(assert (= (select distances_4 4) 0))
(declare-fun stops_1 () (Array Int Int))
(assert (>= (select stops_1 1) 1))
(assert (<= (select stops_1 1) 3))
(assert (>= (select stops_1 2) 1))
(assert (<= (select stops_1 2) 4))
(assert (>= (select stops_1 3) 1))
(assert (<= (select stops_1 3) 4))
(declare-fun stops_2 () (Array Int Int))
(assert (>= (select stops_2 1) 1))
(assert (<= (select stops_2 1) 3))
(assert (>= (select stops_2 2) 1))
(assert (<= (select stops_2 2) 4))
(assert (>= (select stops_2 3) 1))
(assert (<= (select stops_2 3) 4))
(declare-fun items_resp () (Array Int Int))
(assert (>= (select items_resp 1) 1))
(assert (<= (select items_resp 1) 2))
(assert (>= (select items_resp 2) 1))
(assert (<= (select items_resp 2) 2))
(assert (>= (select items_resp 3) 1))
(assert (<= (select items_resp 3) 2))
(declare-fun distances_traveled () (Array Int Int))
(assert (>= (select distances_traveled 1) 0))
(assert (<= (select distances_traveled 1) 271))
(assert (>= (select distances_traveled 2) 0))
(assert (<= (select distances_traveled 2) 271))

(declare-fun loads () (Array Int Int))
(assert (= (select loads 1) (+ (ite (= (select items_resp 1) 1) (select items_size 1) 0)(ite (= (select items_resp 2) 1) (select items_size 2) 0)(ite (= (select items_resp 3) 1) (select items_size 3) 0))))
(assert (>= (select couriers_capa 1) (select loads 1)))
(assert (= (select loads 2) (+ (ite (= (select items_resp 1) 2) (select items_size 1) 0)(ite (= (select items_resp 2) 2) (select items_size 2) 0)(ite (= (select items_resp 3) 2) (select items_size 3) 0))))
(assert (>= (select couriers_capa 2) (select loads 2)))

(assert (or (= (select items_resp 1) 1)(= (select items_resp 2) 1)(= (select items_resp 3) 1)))
(assert (or (= (select items_resp 1) 2)(= (select items_resp 2) 2)(= (select items_resp 3) 2)))

(assert (=> (>= (select couriers_capa 1) (select couriers_capa 2)) (>= (select loads 1) (select loads 2))))
(assert (=> (>= (select couriers_capa 2) (select couriers_capa 1)) (>= (select loads 2) (select loads 1))))

(assert (= (+(ite (= (select stops_1 1) 1) 1 0) (ite (= (select stops_1 2) 1) 1 0) (ite (= (select stops_1 3) 1) 1 0) (ite (= (select stops_2 1) 1) 1 0) (ite (= (select stops_2 2) 1) 1 0) (ite (= (select stops_2 3) 1) 1 0) ) 1))(assert (= (+(ite (= (select stops_1 1) 2) 1 0) (ite (= (select stops_1 2) 2) 1 0) (ite (= (select stops_1 3) 2) 1 0) (ite (= (select stops_2 1) 2) 1 0) (ite (= (select stops_2 2) 2) 1 0) (ite (= (select stops_2 3) 2) 1 0) ) 1))(assert (= (+(ite (= (select stops_1 1) 3) 1 0) (ite (= (select stops_1 2) 3) 1 0) (ite (= (select stops_1 3) 3) 1 0) (ite (= (select stops_2 1) 3) 1 0) (ite (= (select stops_2 2) 3) 1 0) (ite (= (select stops_2 3) 3) 1 0) ) 1))
(assert (=> (<= 1 (+ (ite (= (select items_resp 1) 1) 1 0) (ite (= (select items_resp 2) 1) 1 0) (ite (= (select items_resp 3) 1) 1 0) )) (< (select stops_1 1) 4)))
(assert (=> (< (select stops_1 1) 4) (<= 1 (+ (ite (= (select items_resp 1) 1) 1 0) (ite (= (select items_resp 2) 1) 1 0) (ite (= (select items_resp 3) 1) 1 0) ))))
(assert (=> (<= 2 (+ (ite (= (select items_resp 1) 1) 1 0) (ite (= (select items_resp 2) 1) 1 0) (ite (= (select items_resp 3) 1) 1 0) )) (< (select stops_1 2) 4)))
(assert (=> (< (select stops_1 2) 4) (<= 2 (+ (ite (= (select items_resp 1) 1) 1 0) (ite (= (select items_resp 2) 1) 1 0) (ite (= (select items_resp 3) 1) 1 0) ))))
(assert (=> (<= 3 (+ (ite (= (select items_resp 1) 1) 1 0) (ite (= (select items_resp 2) 1) 1 0) (ite (= (select items_resp 3) 1) 1 0) )) (< (select stops_1 3) 4)))
(assert (=> (< (select stops_1 3) 4) (<= 3 (+ (ite (= (select items_resp 1) 1) 1 0) (ite (= (select items_resp 2) 1) 1 0) (ite (= (select items_resp 3) 1) 1 0) ))))
(assert (=> (<= 1 (+ (ite (= (select items_resp 1) 2) 1 0) (ite (= (select items_resp 2) 2) 1 0) (ite (= (select items_resp 3) 2) 1 0) )) (< (select stops_2 1) 4)))
(assert (=> (< (select stops_2 1) 4) (<= 1 (+ (ite (= (select items_resp 1) 2) 1 0) (ite (= (select items_resp 2) 2) 1 0) (ite (= (select items_resp 3) 2) 1 0) ))))
(assert (=> (<= 2 (+ (ite (= (select items_resp 1) 2) 1 0) (ite (= (select items_resp 2) 2) 1 0) (ite (= (select items_resp 3) 2) 1 0) )) (< (select stops_2 2) 4)))
(assert (=> (< (select stops_2 2) 4) (<= 2 (+ (ite (= (select items_resp 1) 2) 1 0) (ite (= (select items_resp 2) 2) 1 0) (ite (= (select items_resp 3) 2) 1 0) ))))
(assert (=> (<= 3 (+ (ite (= (select items_resp 1) 2) 1 0) (ite (= (select items_resp 2) 2) 1 0) (ite (= (select items_resp 3) 2) 1 0) )) (< (select stops_2 3) 4)))
(assert (=> (< (select stops_2 3) 4) (<= 3 (+ (ite (= (select items_resp 1) 2) 1 0) (ite (= (select items_resp 2) 2) 1 0) (ite (= (select items_resp 3) 2) 1 0) ))))

(assert (=> (= (select items_resp 1) 1) (or (= (select stops_1 1) 1)(= (select stops_1 2) 1)(= (select stops_1 3) 1))))
(assert (=> (= (select items_resp 2) 1) (or (= (select stops_1 1) 2)(= (select stops_1 2) 2)(= (select stops_1 3) 2))))
(assert (=> (= (select items_resp 3) 1) (or (= (select stops_1 1) 3)(= (select stops_1 2) 3)(= (select stops_1 3) 3))))
(assert (=> (= (select items_resp 1) 2) (or (= (select stops_2 1) 1)(= (select stops_2 2) 1)(= (select stops_2 3) 1))))
(assert (=> (= (select items_resp 2) 2) (or (= (select stops_2 1) 2)(= (select stops_2 2) 2)(= (select stops_2 3) 2))))
(assert (=> (= (select items_resp 3) 2) (or (= (select stops_2 1) 3)(= (select stops_2 2) 3)(= (select stops_2 3) 3))))

(declare-const successors (Array Int Int))
(assert (<= (select successors 1) 4))
(assert (<= (select successors 2) 4))
(assert (<= (select successors 3) 4))
(assert (=> (not (= (select stops_1 1) 4)) (= (select successors (select stops_1 1)) (select stops_1 2))))
(assert (=> (not (= (select stops_1 2) 4)) (= (select successors (select stops_1 2)) (select stops_1 3))))
(assert (=> (not (= (select stops_2 1) 4)) (= (select successors (select stops_2 1)) (select stops_2 2))))
(assert (=> (not (= (select stops_2 2) 4)) (= (select successors (select stops_2 2)) (select stops_2 3))))

(assert (= (select distances_traveled 1) (+ (ite (and (= (select items_resp 1) 1) (= (select successors 1) 1) ) (select distances_1 1) 0)(ite (and (= (select items_resp 1) 1) (= (select successors 1) 2) ) (select distances_1 2) 0)(ite (and (= (select items_resp 1) 1) (= (select successors 1) 3) ) (select distances_1 3) 0)(ite (and (= (select items_resp 1) 1) (= (select successors 1) 4) ) (select distances_1 4) 0)(ite (and (= (select items_resp 2) 1) (= (select successors 2) 1) ) (select distances_2 1) 0)(ite (and (= (select items_resp 2) 1) (= (select successors 2) 2) ) (select distances_2 2) 0)(ite (and (= (select items_resp 2) 1) (= (select successors 2) 3) ) (select distances_2 3) 0)(ite (and (= (select items_resp 2) 1) (= (select successors 2) 4) ) (select distances_2 4) 0)(ite (and (= (select items_resp 3) 1) (= (select successors 3) 1) ) (select distances_3 1) 0)(ite (and (= (select items_resp 3) 1) (= (select successors 3) 2) ) (select distances_3 2) 0)(ite (and (= (select items_resp 3) 1) (= (select successors 3) 3) ) (select distances_3 3) 0)(ite (and (= (select items_resp 3) 1) (= (select successors 3) 4) ) (select distances_3 4) 0)(select distances_4 (select stops_1 1)))))
(assert (= (select distances_traveled 2) (+ (ite (and (= (select items_resp 1) 2) (= (select successors 1) 1) ) (select distances_1 1) 0)(ite (and (= (select items_resp 1) 2) (= (select successors 1) 2) ) (select distances_1 2) 0)(ite (and (= (select items_resp 1) 2) (= (select successors 1) 3) ) (select distances_1 3) 0)(ite (and (= (select items_resp 1) 2) (= (select successors 1) 4) ) (select distances_1 4) 0)(ite (and (= (select items_resp 2) 2) (= (select successors 2) 1) ) (select distances_2 1) 0)(ite (and (= (select items_resp 2) 2) (= (select successors 2) 2) ) (select distances_2 2) 0)(ite (and (= (select items_resp 2) 2) (= (select successors 2) 3) ) (select distances_2 3) 0)(ite (and (= (select items_resp 2) 2) (= (select successors 2) 4) ) (select distances_2 4) 0)(ite (and (= (select items_resp 3) 2) (= (select successors 3) 1) ) (select distances_3 1) 0)(ite (and (= (select items_resp 3) 2) (= (select successors 3) 2) ) (select distances_3 2) 0)(ite (and (= (select items_resp 3) 2) (= (select successors 3) 3) ) (select distances_3 3) 0)(ite (and (= (select items_resp 3) 2) (= (select successors 3) 4) ) (select distances_3 4) 0)(select distances_4 (select stops_2 1)))))

(assert (<= (select distances_traveled 1) 271))
(assert (<= (select distances_traveled 2) 271))
(check-sat)
(get-model)
