#lang racket

(require redex/reduction-semantics)

(define-language Λ
  (e x 
     (λ x e)
     (e e))
  (x variable-not-otherwise-mentioned)
  (A hole
     ((in-hole A (λ x A)) e))
  (O hole
     ((in-hole A O) e))
  (I hole
     (in-hole A (λ x I)))
  (E hole
     (E e)
     (in-hole A E)
     (side-condition 
      (in-hole O_0 ((in-hole A (λ x_0 (in-hole I_0 (in-hole E_0 x_0))))
                    E_1))
      (A? (term (in-hole O_0 I_0)))))
  (v (λ x e)))

(define A? (redex-match Λ A))

(define-term A_0 ((λ x hole) e_x))
(define-term A_1 ((λ x ((λ y hole) e_y)) e_x))
(define-term A_2 ((λ x ((λ y ((λ z hole) e_z)) e_y)) e_x))
(define-term A_3 ((((λ x (λ y (λ z hole))) e_x) e_y) e_z))
(define-term A_4 (((λ x ((λ y (λ z hole)) e_y)) e_x) e_z))

(test-predicate A? (term A_0))
(test-predicate A? (term A_1))
(test-predicate A? (term A_2))
(test-predicate A? (term A_3))
(test-predicate A? (term A_4))

(redex-let Λ ([((in-hole A_5 (λ z (in-hole A_6 hole))) e_z)
               (term A_4)])
           (test-predicate (redex-match Λ hole) (term A_6))
           (redex-let Λ ([((in-hole A_7 (λ x (in-hole A_8 hole))) e_x)
                          (term A_5)])
                      (test-predicate (redex-match Λ hole) (term A_7))
                      (redex-let Λ ([((in-hole A_9 (λ y (in-hole A_10 hole))) e_y)
                                     (term A_8)])
                                 (test-predicate (redex-match Λ hole) (term A_9))
                                 (test-predicate (redex-match Λ hole) (term A_10)))))

;; match-sets: (or/c #f (listof match)) -> (set/c (set/c bind))
(define (match-sets matches)
  (if matches
      (for/fold ([s (set)]) ([m matches])
                (set-add s (apply set (match-bindings m))))
      (set)))

(test-equal
 (match-sets (redex-match Λ (in-hole O ((in-hole A (λ x (in-hole I hole))) e)) (term A_4)))
 (set (set (make-bind 'A (term hole))
           (make-bind 'O (term (hole e_z)))
           (make-bind 'I (term ((λ y (λ z hole)) e_y)))
           (make-bind 'x (term x))
           (make-bind 'e (term e_x)))
      (set (make-bind 'A (term hole))
           (make-bind 'O (term (((λ x hole) e_x) e_z)))
           (make-bind 'I (term (λ z hole)))
           (make-bind 'x (term y))
           (make-bind 'e (term e_y)))
      (set (make-bind 'A (term ((λ x ((λ y hole) e_y)) e_x)))
           (make-bind 'O (term hole))
           (make-bind 'I (term hole))
           (make-bind 'x (term z))
           (make-bind 'e (term e_z)))))

(define std-red
  ;; warning: assumes a convenient choice of names for bound variables
  (context-closure
   (reduction-relation
    Λ
    (--> (in-hole O ((in-hole A_1 (λ x (in-hole I (in-hole E x))))
                     (in-hole A_2 v)))
         (in-hole O (in-hole A_1 (subst (in-hole A_2 (in-hole I (in-hole E x))) x v)))))
   Λ E))

(define-metafunction Λ
  subst : e x v -> e
  [(subst x x v) v]
  [(subst x_1 x_2 v) x_1]
  [(subst (λ x e) x v) (λ x e)]
  [(subst (λ x_1 e) x_2 v) (λ x_1 (subst e x_2 v))]
  [(subst (e_1 e_2) x v) ((subst e_1 x v) (subst e_2 x v))])

(test--> std-red
         (term ((λ x x) (λ y y)))
         (term (λ y y)))
(test--> std-red
         (term (((λ x x) (λ y y)) (λ z z)))
         (term ((λ y y) (λ z z))))
(test--> std-red
         (term ((λ z (λ x z)) ((λ x x) (λ y y)))))
(test--> std-red
         (term ((λ x ((λ a a) (λ b b))) (λ y y)))
         (term ((λ x (λ b b)) (λ y y))))
(test--> std-red
         (term ((λ z (z z)) ((λ x x) (λ y y))))
         (term ((λ z (z z)) (λ y y))))
(test--> std-red
         (term ((λ z z) 
                ((λ a ((λ x (x a)) (λ y y)))
                 ((λ b b) (λ c c)))))
         (term ((λ z z) 
                ((λ a ((λ y y) a))
                 ((λ b b) (λ c c))))))


(test-results)