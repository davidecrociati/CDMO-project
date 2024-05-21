
(set-logic QF_FD)
(declare-const num_couriers Int)
(assert (= num_couriers 2))
(declare-const num_items Int)
(assert (= num_items 6))
(declare-const courier_1_size Int)
(assert (= courier_1_size 15))
(declare-const courier_2_size Int)
(assert (= courier_2_size 10))
(declare-const item_1_size Int)
(assert (= item_1_size 3))
(declare-const item_2_size Int)
(assert (= item_2_size 2))
(declare-const item_3_size Int)
(assert (= item_3_size 6))
(declare-const item_4_size Int)
(assert (= item_4_size 5))
(declare-const item_5_size Int)
(assert (= item_5_size 4))
(declare-const item_6_size Int)
(assert (= item_6_size 4))
(check-sat)
(get-model)