(define-sort Word () (_ BitVec 256))
(define-fun zero () Word  (_ bv0 256))

;; Signed addition can wrap if the signs of x and y are the same.
;; If both are positive and x + y < x, then overflow happened.
;; If both are negative and x + y > x, then underflow happened.
(define-fun
    add-overflow-basic
    ((x Word) (y Word)) Bool
    (or (and (bvslt x zero)
             (bvslt y zero)
             (bvsgt (bvadd x y) x))
        (and (bvsgt x zero)
             (bvsgt y zero)
             (bvslt (bvadd x y) x))))

;; Here is a clever way to calculate the same truth value,
;; from _Hacker's Delight_, section 2.13.
(define-fun
    add-overflow-clever
    ((x Word) (y Word)) Bool
    (bvslt zero
           (bvand (bvxor (bvadd x y) x)
                  (bvxor (bvadd x y) y))))

(set-option :pp.bv-literals false)

(declare-const x Word)
(declare-const y Word)

(assert (not (= (add-overflow-basic x y) (add-overflow-basic x y))))

(check-sat)
(display "Unsat is good; no exception was found.")
