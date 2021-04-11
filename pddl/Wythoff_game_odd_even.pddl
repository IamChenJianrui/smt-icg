(define (domain Wythoff_game)
    (:constants ?max 1)
    (:objects ?m ?n)
    (:type normal)
    (:tercondition (and (= ?m 0) (= ?n 0)))
    (:constraint (and (>= ?m 0) (>= ?n 0) (or (> ?m 0) (> ?n 0))))
    (:action take1
        :parameters (?k)
        :precondition (and (>= ?m ?k) (> ?k 0) (<= ?k ?max) (= (% (- ?m ?k) 2) 1))
        :effect (assign ?m (- ?m ?k)))
    (:action take2
        :parameters (?k)
        :precondition (and (>= ?n ?k) (> ?k 0) (<= ?k ?max))
        :effect (assign ?n (- ?n ?k)))
    (:action take3
        :parameters (?k)
        :precondition (and (>= ?m ?k) (>= ?n ?k) (> ?k 0) (<= ?k ?max))
        :effect (and (assign ?m (- ?m ?k)) (assign ?n (- ?n ?k))))
)