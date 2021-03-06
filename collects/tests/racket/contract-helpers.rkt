#lang racket
(require rackunit
         racket/contract/private/arrow)
(check-equal? (matches-arity-exactly? (λ () 1) 0 0 '() '()) #t)
(check-equal? (matches-arity-exactly? (λ () 1) 1 1 '() '()) #f)
(check-equal? (matches-arity-exactly? (λ () 1) 0 1 '() '()) #f)
(check-equal? (matches-arity-exactly? (λ () 1) 0 #f '() '()) #f)
(check-equal? (matches-arity-exactly? (λ (x y) x) 2 2 '() '()) #t)
(check-equal? (matches-arity-exactly? (λ (x y) x) 1 1 '() '()) #f)
(check-equal? (matches-arity-exactly? (λ (x y) x) 2 3 '() '()) #f)
(check-equal? (matches-arity-exactly? (λ (x y) x) 3 #f '() '()) #f)

(check-equal? (matches-arity-exactly? (case-lambda
                                  [() 1]
                                  [(x) 2])
                                0 1 '() '()) #t)
(check-equal? (matches-arity-exactly? (case-lambda
                                  [() 1]
                                  [(x) 2])
                                0 2 '() '()) #f)
(check-equal? (matches-arity-exactly? (case-lambda
                                  [() 1]
                                  [(x y) 2])
                                0 2 '() '()) #f)
(check-equal? (matches-arity-exactly? (case-lambda
                                  [() 1]
                                  [(x y) 2])
                                0 1 '() '()) #f)
(check-equal? (matches-arity-exactly? (case-lambda
                                  [() 1]
                                  [(x y) 2])
                                0 #f '() '()) #f)

(check-equal? (matches-arity-exactly? (lambda (x . y) x)
                                1 #f '() '()) #t)
(check-equal? (matches-arity-exactly? (lambda (x . y) x)
                                0 #f '() '()) #f)
(check-equal? (matches-arity-exactly? (lambda (x #:y y) y)
	                              1 1 '(#:y) '())
              #t)
(check-equal? (matches-arity-exactly? (lambda (x #:y y #:z z) y)
	                              1 1 '(#:y #:z) '())
              #t)
(check-equal? (matches-arity-exactly? (lambda (x #:y y #:z z) y)
	                              1 1 '(#:y) '())
              #f)
(check-equal? (matches-arity-exactly? (lambda (x #:y y #:z z) y)
	                              1 1 '(#:z) '())
              #f)
(check-equal? (matches-arity-exactly? (lambda (x #:y y #:z z) y)
	                              1 1 '() '())
              #f)
(check-equal? (matches-arity-exactly? (lambda (x #:y y #:z z) y)
	                              1 1 '() '(#:x))
              #f)
(check-equal? (matches-arity-exactly? (lambda (x #:y y #:z [z 1]) y)
	                              1 1 '(#:y) '(#:z))
              #t)
(check-equal? (matches-arity-exactly? (lambda (x #:y y #:z [z 1]) y)
	                              1 1 '(#:y) '())
              #f)
(check-equal? (matches-arity-exactly? (lambda (x #:y y #:z [z 1]) y)
	                              1 1 '() '(#:z))
              #f)
(check-equal? (matches-arity-exactly? (lambda (x #:y y #:z [z 1]) y)
	                              1 1 '(#:y #:z) '())
              #f)
(check-equal? (matches-arity-exactly? (lambda (x #:y y #:z [z 1]) y)
	                              1 1 '() '(#:y #:z))
              #f)

