;;(set-logic LIA)
;;(set-logic QF_NIA)
(set-logic NIA)

(synth-inv inv-f ((x Int) (y Int))

    ;; Declare the non-terminals that would be used in the grammar
    ((B Bool) (I Int) )

    (
        (B Bool ((and B B) (or B B) (not B)
            (= I I) (< I I) (> I I) (>= I I) (<= I I)))
        (I Int (x y 0 1 2
             (+ I I) (- I I) (* I I)
             (ite B I I)))
                            
    )

)

(declare-var x Int)
(declare-var y Int)

(define-fun pre-f ((x Int) (y Int)) Bool
    (and (= x 0) (= y 0)     (= (* 2 y) (* x (+ x 1)))))
    ;;(and (= x 0) (= y 0)))

(define-fun trans-f ((x Int) (y Int) (x! Int) (y! Int)) Bool
    (and (= x! (+ x 1)) (= y! (+ x y 1))        (= (* 2 y) (* x (+ x 1))))) 
    ;;(and (= x! (+ x 1)) (= y! (+ x y 1))))

(define-fun post-f ((x Int) (y Int)) Bool
    (and (>= y 0) (>= x 0)        (= (* 2 y) (* x (+ x 1)))))
    ;;(and (>= y 0) (>= x 0)))

(inv-constraint inv-f pre-f trans-f post-f)
;;cvc5 not able to find invariant even if I include it in all statements

(check-synth)