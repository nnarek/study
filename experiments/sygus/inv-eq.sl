(set-logic LIA)

(synth-inv inv-f ((x Int) (y Int)))

(declare-var x Int)
(declare-var y Int)

;; preconditions 
(define-fun pre-f ((x Int) (y Int)) Bool
    (and (= x 1) (= y 1)))

;; predicate which describes each iteration(describes all possible valid transitions from one state to another). variables with names x! and y! are values of x and y after each iteration
(define-fun trans-f ((x Int) (y Int) (x! Int) (y! Int)) Bool
    (and (= x! (+ x y)) (= y! (+ x y))))

;; postconditions
(define-fun post-f ((x Int) (y Int)) Bool
    (>= y 1))

;; it is obvious that x will always be equal to y
(inv-constraint inv-f pre-f trans-f post-f)

(check-synth)