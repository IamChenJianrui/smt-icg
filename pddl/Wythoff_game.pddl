(define (domain Wythoff_game)
    (:objects ?m ?n)
    (:type normal)
    (:tercondition (and (= ?m 0) (= ?n 0)))
    (:constraint (or (and (> ?m 0) (>= ?n 0)) (and (> ?n 0) (>= ?m 0))))
    (:action take1
        :parameters (?k)
        :precondition (and (>= ?m ?k) (> ?k 0) (<= ?k 3))
        :effect (assign ?m (- ?m ?k)))
    (:action take2
        :parameters (?k)
        :precondition (and (>= ?n ?k) (> ?k 0) (<= ?k 3))
        :effect (assign ?n (- ?n ?k)))
    (:action take3
        :parameters (?k)
        :precondition (and (>= ?m ?k) (>= ?n ?k) (> ?k 0) (<= ?k 3))
        :effect (and (assign ?m (- ?m ?k)) (assign ?n (- ?n ?k))))

)