(define (domain Max_min_two_piled_nim)
    (:objects ?v1 ?v2)
    (:type normal)
    (:tercondition (and (= ?v1 0) (= ?v2 0)))
    (:constraint (and (>= ?v1 0) (>= ?v2 0)))
    (:action take1
        :parameters (?k)
        :precondition (and (>= ?v1 ?k) (>= ?k 1))
        :effect (and (when (>= (- ?v1 ?k) ?v2) (assign ?v1 (- ?v1 ?k))) (when (< (- ?v1 ?k) ?v2) (assign ?v2 (- ?v1 ?k))) (when (< (- ?v1 ?k) ?v2) (assign ?v1 ?v2)) ))
    (:action take2
        :parameters (?k)
        :precondition (and (>= ?v2 ?k) (>= ?k 1))
        :effect (assign ?v2 (- ?v2 ?k)))
)