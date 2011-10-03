(module term-test scheme
  (require "../private/term.rkt"
           "../private/matcher.rkt"
           "../private/error.rkt"
           "test-util.rkt")
  
  (reset-count)
  (test (term 1) 1)
  (test (term (1 2)) (list 1 2))
  (test (term (1 ,(+ 1 1))) (list 1 2))
  (test (term-let ([x 1]) (term (x x))) (list 1 1))
  (test (term-let ([(x ...) (list 1 2 3)]) (term ((y x) ...))) '((y 1) (y 2) (y 3)))
  
  (test (term (in-hole (1 hole) 2)) (term (1 2)))
  
  (test (equal? (term hole) (term hole)) #t)
  (test (hole? (term hole)) #t)
  (test (hole? (term (hole #f))) #f)
  (test (hole? (term (hole the-name))) #f)
  
  (test (term-let-fn ((f (lambda (q) q)))
                     (term (f 1 2 3)))
        (term (1 2 3)))
  
  (test (term-let-fn ((f (lambda (q) `(y ,(car q)))))
                     (term (f (zzzz))))
        (term (y (zzzz))))
  
  (test (term-let-fn ((f (λ (x) (add1 (car x)))))
                     (term (f 2)))
        (term 3))
  
  (test (term-let ([((x ...) ...) (list (list 1 1) (list 2 2) (list 3 3))])
          (term-let-fn ((f (λ (x) (car x))))
                       (term ((qq (f x) ...) ...))))
        (term ((qq 1 1) (qq 2 2) (qq 3 3))))
  
  (test (term-let-fn ((f (lambda (x) (car x))))
                     (term (f hole)))
        (term hole))
  
  (test (term-let-fn ((f (lambda (q) `(y ,(car q)))))
                     (term-let-fn ((g (lambda (x) `(ff ,(car x)))))
                                  (term (g (f (zzzz))))))
        (term (ff (y (zzzz)))))
  
  (test (term-let-fn ((f (lambda (q) `(y ,(car q)))))
                     (term-let-fn ((g (lambda (x) `(ff ,(car x)))))
                                  (term (f (g (f (zzzz)))))))
        (term (y (ff (y (zzzz))))))
  
  (test (term-let ([x 1])
          (term (x . y)))
        (term (1 . y)))
  
  (test (term-let ([(x ...) (list 3 2 1)])
          (term (x ... . y)))
        (term (3 2 1 . y)))
  
  (test (term-let ([(x . y) (cons 1 2)])
          (term (x y)))
        (term (1 2)))
  
  ;; test that the implicit `plug' inserted by `in-hole' 
  ;; deals with ellipses properly
  (test (term-let ([(E ...) (list (term (1 hole)) (term (2 hole)) (term (3 hole)))])
          (term ((in-hole E x) ...)))
        (term ((1 x) (2 x) (3 x))))
  
  (test (term-let-fn ((metafun car))
                     (term-let ((x 'whatever)
                                ((y ...) '(4 5 6)))
                       (term (((metafun x) y) ...))))
        '((whatever 4) (whatever 5) (whatever 6)))
  
  (test (term-let-fn ((metafun (λ (x) (car x))))
                     (term-let (((y ...) '(4 5 6)))
                       (term ((y (metafun 1)) ...))))
        '((4 1) (5 1) (6 1)))
  
  (test (term-let-fn ((f (compose add1 car)))
                     (term-let (((x ...) '(1 2 3))
                                ((y ...) '(a b c)))
                               (term (((f x) y) ...))))
        '((2 a) (3 b) (4 c)))
  
  (test (term-let-fn ((f (curry foldl + 0)))
                     (term-let (((x ...) '(1 2 3)))
                               (term (f x ...))))
        6)
  
  (test (term-let-fn ((f (compose add1 car)))
                     (term-let (((x ...) '(1 2 3))
                                (((y ...) ...) '((a b c) (d e f) (g h i))))
                               (term ((((f x) y) ...) ...))))
        '(((2 a) (3 b) (4 c)) ((2 d) (3 e) (4 f)) ((2 g) (3 h) (4 i))))
  
  (test (term-let-fn ((f (curry foldl + 0)))
                     (term-let ((((x ...) ...) '((1 2) (3 4 5) (6))))
                               (term ((f x ...) ...))))
        '(3 12 6))
  
  (test (term (hole 2)) (layer '() the-hole '(2)))
  (test (term (1 hole)) (layer '(1) the-hole '()))
  (test (term (hole hole)) (list the-hole the-hole))
  (test (term (hole (hide-hole hole))) (layer '() the-hole `(,the-hole)))
  (test (term (hide-hole 1)) 1)
  (test (term (in-hole (a hole d) (b hole c)))
        (layer '(a) (layer '(b) the-hole '(c)) '(d)))
  (test (term (in-hole (a hole d) (hide-hole (b hole c))))
        `(a ,(layer '(b) the-hole '(c)) d))
  (test (term (in-hole (a hole d) (b (hide-hole hole) c)))
        `(a (b ,the-hole c) d))
  (test (term (in-hole (hide-hole (a hole)) b))
        '(a b))
  
  (test (term-let-fn ((f (λ (cs) (apply plug cs))))
                     (term (0 (f (1 hole) (2 hole)))))
        (layer '(0) (layer '(1) (layer '(2) the-hole '()) '()) '()))
  (test (term-let-fn ((f (λ (cs) (apply plug cs))))
                     (term (in-hole (0 (f (1 hole) (2 hole))) 3)))
        '(0 (1 (2 3))))
  
  (test (plug the-hole 'a) 'a)
  (test (plug (layer '() the-hole '(b)) 'a) '(a b))
  (test (plug (layer '() the-hole '(b)) (layer '(a) the-hole '())) 
        (layer '() (layer '(a) the-hole '()) '(b)))
  (test (plug (layer '(a) the-hole '()) 'b) '(a b))
  (test (plug (layer '(a) the-hole '()) (layer '() the-hole '(b)))
        (layer '(a) (layer '() the-hole '(b)) '()))
  (test (with-handlers ([exn:fail:redex? exn-message])
          (plug '(a b c) 'd)
          "")
        #rx"term has no pluggable hole")
  
  (define-namespace-anchor here)
  (define ns (namespace-anchor->namespace here))
  
  (parameterize ([current-namespace ns])
    (exec-runtime-error-tests "run-err-tests/term.rktd"))
  
  (exec-syntax-error-tests "syn-err-tests/term.rktd")
  
  (print-tests-passed 'term-test.rkt))
