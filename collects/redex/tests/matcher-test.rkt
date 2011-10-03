(module matcher-test mzscheme
  (require "../private/matcher.rkt"
           "../private/error.rkt"
           (only "test-util.rkt" equal/bindings?)
           mzlib/list)
  
  (error-print-width 500)
  
  (define (make-test-mtch b) (make-mtch b (non-decomp)))
  
  (define (test)
    (print-struct #t)
    (test-empty 'any 1 (list (make-test-mtch (make-bindings (list (make-bind 'any 1))))))
    (test-empty 'any 'true (list (make-test-mtch (make-bindings (list (make-bind 'any 'true))))))
    (test-empty 'any "a" (list (make-test-mtch (make-bindings (list (make-bind 'any "a"))))))
    (test-empty 'any '(a b) (list (make-test-mtch (make-bindings (list (make-bind 'any '(a b)))))))
    (test-empty 'any #t (list (make-test-mtch (make-bindings (list (make-bind 'any #t))))))
    (test-empty 1 1 (list (make-test-mtch (make-bindings null))))
    (test-empty 1 '() #f)
    (test-empty 99999999999999999999999999999999999999999999999
                99999999999999999999999999999999999999999999999
                (list (make-test-mtch (make-bindings null))))
    (test-empty 99999999999999999999999999999999999999999999999
                '()
                #f)
    (test-empty 'x 'x (list (make-test-mtch (make-bindings null))))
    (test-empty 'x '() #f)
    (test-empty 1 2 #f)
    (test-empty "a" "b" #f)
    (test-empty "a" '(x) #f)
    (test-empty "a" '() #f)
    (test-empty "a" "a" (list (make-test-mtch (make-bindings null))))
    (test-empty #s(x 1) #s(x 1) (list (make-test-mtch (make-bindings null))))
    (test-empty #s(x 1) #s(x 2) #f)
    (test-empty 'number 1 (list (make-test-mtch (make-bindings (list (make-bind 'number 1))))))
    (test-empty 'number 'x #f)
    (test-empty 'number '() #f)
    (test-empty 'natural 1 (list (make-test-mtch (make-bindings (list (make-bind 'natural 1))))))
    (test-empty 'natural 'x #f)
    (test-empty 'natural '() #f)
    (test-empty 'natural -1 #f)
    (test-empty 'natural 1.0 #f)
    (test-empty 'integer -1 (list (make-test-mtch (make-bindings (list (make-bind 'integer -1))))))
    (test-empty 'integer 'x #f)
    (test-empty 'integer '() #f)
    (test-empty 'integer 1.0 #f)
    (test-empty 'real 1.1 (list (make-test-mtch (make-bindings (list (make-bind 'real 1.1))))))
    (test-empty 'real 'x #f)
    (test-empty 'real '() #f)
    (test-empty 'real 2+3i #f)
    (test-empty 'string "a" (list (make-test-mtch (make-bindings (list (make-bind 'string "a"))))))
    (test-empty 'string 1 #f)
    (test-empty 'string '() #f)
    (test-empty 'variable 'x (list (make-test-mtch (make-bindings (list (make-bind 'variable 'x))))))
    (test-empty 'variable 1 #f)
    (test-empty '(variable-except x) 1 #f)
    (test-empty '(variable-except x) 'x #f)
    (test-empty '(variable-except x) 'y (list (make-test-mtch (make-bindings null))))
    (test-lang 'x 'y (list (make-test-mtch (make-bindings (list (make-bind 'x 'y)))))
               (list (make-nt 'x (list (make-rhs '(variable-except x))))))
    (test-empty '(variable-prefix x:) 'x: (list (make-test-mtch (make-bindings null))))
    (test-empty '(variable-prefix x:) 'x:x (list (make-test-mtch (make-bindings null))))
    (test-empty '(variable-prefix x:) ': #f)
    (test-empty '(variable-prefix x:) '() #f)
    
    (test-empty 'hole 1 #f)
    (test-empty `hole
                the-hole
                (list (make-test-mtch (make-bindings (list)))))
    (test-empty '(in-hole (hole 2) 1)
                '(1 2)
                (list (make-test-mtch (make-bindings (list)))))
    
    (test-empty '(in-hole (name E_1 ((hide-hole hole) hole)) x)
                `(,the-hole x)
                (list (make-test-mtch (make-bindings (list (make-bind 'E_1 (layer (list the-hole) the-hole null)))))))
    (test-empty '(in-hole (name E_1 ((hide-hole hole) hole)) x)
                `(x ,the-hole)
                #f)

    
    (test-empty '(name x number) 1 (list (make-test-mtch (make-bindings (list (make-bind 'x 1) (make-bind 'number 1))))))
    (test-empty 'number_x 1 (list (make-test-mtch (make-bindings (list (make-bind 'number_x 1))))))
    (test-empty 'string_y "b" (list (make-test-mtch (make-bindings (list (make-bind 'string_y "b"))))))
    (test-empty 'any_z '(a b) (list (make-test-mtch (make-bindings (list (make-bind 'any_z '(a b)))))))
    
    (test-empty '(name x_!_1 number) 1 (list (make-test-mtch (make-bindings (list (make-bind 'number 1))))))
    (test-empty '((name x_!_1 number) (name x_!_1 number)) '(1 1) #f)
    (test-empty '((name x_!_1 number_a) (name x_!_1 number_b)) '(1 2) 
                (list (make-test-mtch (make-bindings (list (make-bind 'number_a 1)
                                                           (make-bind 'number_b 2))))))
    (test-empty '(number_!_1 number_!_1) '(1 1) #f)
    (test-empty '(number_!_1 number_!_1) '(1 2) (list (make-test-mtch (make-bindings (list)))))
    (test-empty '(number_!_1 ...) '(1 2) (list (make-test-mtch (make-bindings (list)))))
    (test-empty '(number_!_1 ...) '(1 2 3 4 5) (list (make-test-mtch (make-bindings (list)))))
    (test-empty '(number_!_1 ...) '(1 2 3 1 5) (list (make-test-mtch (make-bindings (list)))))
    (test-empty '((number_!_1 ...) (number_!_1 ...)) 
                '((1 2 3 1 5) (1 2 3 1 5))
                #f)
    (test-empty '((number_!_1 ...) (number_!_1 ...)) 
                '((17 2 3 1 5) (1 2 3 1 5))
                (list (make-test-mtch (make-bindings (list)))))
    (test-empty '((number_!_1 number_!_1) ... number_!_1 ...) '((1 1) (2 2) 1 3) #f)
    (test-empty '((number_!_1 number_!_1) ... number_!_1 ...) '((1 1) (2 3) 1 2) #f)
    (test-empty '((number_!_1 number_!_1) ... number_!_1 ...)
                '((1 1) (2 3) 1 4)
                (list (make-test-mtch (make-bindings (list)))))
    
    (test-ellipses '(a) '(a))
    (test-ellipses '(a ...) `(,(make-repeat 'a '() #f #f)))
    (test-ellipses '((a ...) ...) `(,(make-repeat '(a ...) '() #f #f)))
    (test-ellipses '(a ... b c ...) `(,(make-repeat 'a '() #f #f) b ,(make-repeat 'c '() #f #f)))
    (test-ellipses '((name x a) ...) `(,(make-repeat '(name x a) (list (make-bind 'x '())) #f #f))) 
    (test-ellipses '((name x (a ...)) ...)
                   `(,(make-repeat '(name x (a ...)) (list (make-bind 'x '())) #f #f)))
    (test-ellipses '(((name x a) ...) ...)
                   `(,(make-repeat '((name x a) ...) (list (make-bind 'x '())) #f #f)))
    (test-ellipses '((1 (name x a)) ...)
                   `(,(make-repeat '(1 (name x a)) (list (make-bind 'x '())) #f #f)))
    (test-ellipses '((any (name x a)) ...)
                   `(,(make-repeat '(any (name x a)) (list (make-bind 'any '())
                                                           (make-bind 'x '())) 
                                   #f #f)))
    (test-ellipses '((number (name x a)) ...)
                   `(,(make-repeat '(number (name x a)) (list (make-bind 'number '())
                                                              (make-bind 'x '())) 
                                   #f #f)))
    (test-ellipses '((variable (name x a)) ...)
                   `(,(make-repeat '(variable (name x a)) (list (make-bind 'variable '())
                                                                (make-bind 'x '()))
                                   #f #f)))
    (test-ellipses '(((name x a) (name y b)) ...)
                   `(,(make-repeat '((name x a) (name y b)) (list (make-bind 'x '()) (make-bind 'y '())) #f #f)))
    (test-ellipses '((name x (name y b)) ...)
                   `(,(make-repeat '(name x (name y b)) (list (make-bind 'x '()) (make-bind 'y '())) #f #f)))
    (test-ellipses '((in-hole (name x a) (name y b)) ...)
                   `(,(make-repeat '(in-hole (name x a) (name y b)) 
                                   (list (make-bind 'y '()) (make-bind 'x '())) #f #f)))
    
    (test-ellipses '(a ..._1)
                   `(,(make-repeat 'a (list) '..._1 #f)))
    (test-ellipses '(a ..._!_1)
                   `(,(make-repeat 'a (list) '..._!_1 #t)))
    
    (test-empty '() '() (list (make-test-mtch (make-bindings null))))
    (test-empty '(a) '(a) (list (make-test-mtch (make-bindings null))))
    (test-empty '(a) '(b) #f)
    (test-empty '(a b) '(a b) (list (make-test-mtch (make-bindings null))))
    (test-empty '(a b) '(a c) #f)
    (test-empty '() 1 #f)
    (test-empty '(#f x) '(#f x) (list (make-test-mtch (make-bindings null))))
    (test-empty '(#f (name y any)) '(#f) #f)
    (test-empty '(in-hole (z hole) a) '(z a) (list (make-test-mtch (make-bindings (list)))))
    (test-empty '(in-hole (z hole) (in-hole (x hole) a)) 
                '(z (x a))
                (list (make-test-mtch (make-bindings (list)))))
    (test-empty '(in-hole (name z (z hole)) (name xa (in-hole (name x (x hole)) a))) 
                '(z (x a))
                (list (make-test-mtch 
                       (make-bindings 
                        (list (make-bind 'z (layer '(z) the-hole '()))
                              (make-bind 'x (layer '(x) the-hole '()))
                              (make-bind 'xa '(x a)))))))
    
    (test-empty '(in-hole (1 2) 2) '(1 2) #f)
    
    (test-empty '(in-hole (name no-y ((name no-z (in-hole (x hole) hole)) z)) y)
                '((x y) z)
                (list (make-test-mtch
                       (make-bindings
                        (list (make-bind 'no-y (layer '() (layer '(x) the-hole '()) '(z)))
                              (make-bind 'no-z (layer '(x) the-hole '())))))))
    
    (test-empty '(in-hole
                  (cons (name C (hole b))
                        (name C (hole b)))
                  a)
                `((,the-hole b)
                  (a b))
                #f)
    
    (let ([t `((,the-hole b) (,the-hole b))])
      (test-empty '(in-hole (name C ((hole b) (hole b)))
                            hole)
                  t
                  (list (make-test-mtch
                         (make-bindings
                          (list (make-bind 'C (layer '() (layer '() the-hole '(b)) `((,the-hole b)))))))
                        (make-test-mtch
                         (make-bindings
                          (list (make-bind 'C (layer `((,the-hole b))
                                                     (layer '() the-hole '(b))
                                                     '()))))))))
    
    (test-empty '(number number) '(1 1) (list (make-test-mtch (make-bindings (list (make-bind 'number 1))))))
    (test-empty '((name x number) (name x number)) '(1 1) (list (make-test-mtch (make-bindings (list (make-bind 'x 1) (make-bind 'number 1))))))
    (test-empty '((name x number_q) (name x number_r)) '(1 1) (list (make-test-mtch (make-bindings (list (make-bind 'x 1) 
                                                                                                         (make-bind 'number_q 1)
                                                                                                         (make-bind 'number_r 1))))))
    (test-empty '(number number) '(1 2) #f)
    (test-empty '((name x number) (name x number)) '(1 2) #f)
    (test-empty '((name x number_q) (name x number_r)) '(1 2) #f)
    
    (test-empty '(a ...) '() (list (make-test-mtch (make-bindings empty))))
    (test-empty '(a ...) '(a) (list (make-test-mtch (make-bindings empty))))
    (test-empty '(a ...) '(a a) (list (make-test-mtch (make-bindings empty))))
    (test-empty '((name x a) ...) '() (list (make-test-mtch (make-bindings (list (make-bind 'x '()))))))
    (test-empty '((name x a) ...) '(a) (list (make-test-mtch (make-bindings (list (make-bind 'x '(a)))))))
    (test-empty '((name x a) ...) '(a a) (list (make-test-mtch (make-bindings (list (make-bind 'x '(a a)))))))
    (test-empty '(hole ...) '() (list (make-test-mtch (make-bindings empty))))
    
    (test-empty '(b ... a ...) '() (list (make-test-mtch (make-bindings empty))))
    (test-empty '(b ... a ...) '(a) (list (make-test-mtch (make-bindings empty))))
    (test-empty '(b ... a ...) '(b) (list (make-test-mtch (make-bindings empty))))
    (test-empty '(b ... a ...) '(b a) (list (make-test-mtch (make-bindings empty))))
    (test-empty '(b ... a ...) '(b b a a) (list (make-test-mtch (make-bindings empty))))
    (test-empty '(b ... a ...) '(a a) (list (make-test-mtch (make-bindings empty))))
    (test-empty '(b ... a ...) '(b b) (list (make-test-mtch (make-bindings empty))))
    
    (test-empty '(a ..._1 a ..._2) 
                '(a) 
                (list (make-test-mtch (make-bindings (list (make-bind '..._1 1) (make-bind '..._2 0))))
                      (make-test-mtch (make-bindings (list (make-bind '..._1 0) (make-bind '..._2 1))))))
    (test-empty '(a ..._1 a ..._1) '(a) #f)
    (test-empty '(a ..._1 a ..._1)
                '(a a) 
                (list (make-test-mtch (make-bindings (list (make-bind '..._1 1))))))
    
    (test-empty '((a ..._1 a ..._1) ...)
                '((a a a a)) 
                (list (make-test-mtch (make-bindings (list (make-bind '..._1 '(2)))))))
    (test-empty '((a ..._!_1 a ..._!_1) ...)
                '((a a a a)) 
                (list (make-test-mtch (make-bindings '()))
                      (make-test-mtch (make-bindings '()))
                      (make-test-mtch (make-bindings '()))
                      (make-test-mtch (make-bindings '()))))

    (test-empty '((name x a) ..._!_1 (name y a) ..._!_1) 
                '(a a) 
                (list (make-test-mtch (make-bindings (list (make-bind 'x '()) (make-bind 'y '(a a)))))
                      (make-test-mtch (make-bindings (list (make-bind 'x '(a a)) (make-bind 'y '()))))))
    
    (test-empty '((name y b) ... (name x a) ...) '() 
                (list (make-test-mtch (make-bindings (list (make-bind 'x '())
                                                           (make-bind 'y '()))))))
    (test-empty '((name y b) ... (name x a) ...) '(a)
                (list (make-test-mtch (make-bindings (list (make-bind 'x '(a))
                                                           (make-bind 'y '()))))))
    (test-empty '((name y b) ... (name x a) ...) '(b) 
                (list (make-test-mtch (make-bindings (list (make-bind 'x '())
                                                           (make-bind 'y '(b)))))))
    (test-empty '((name y b) ... (name x a) ...) '(b b a a) 
                (list (make-test-mtch (make-bindings (list (make-bind 'x '(a a))
                                                           (make-bind 'y '(b b)))))))
    (test-empty '((name y a) ... (name x a) ...) '(a) 
                (list (make-test-mtch (make-bindings (list (make-bind 'x '())
                                                           (make-bind 'y '(a)))))
                      (make-test-mtch (make-bindings (list (make-bind 'x '(a))
                                                           (make-bind 'y '()))))))
    (test-empty '((name y a) ... (name x a) ...) '(a a) 
                (list (make-test-mtch (make-bindings (list (make-bind 'x '())
                                                           (make-bind 'y '(a a)))))
                      (make-test-mtch (make-bindings (list (make-bind 'x '(a))
                                                           (make-bind 'y '(a)))))
                      (make-test-mtch (make-bindings (list (make-bind 'x '(a a))
                                                           (make-bind 'y '()))))))
    
    (test-ab '(bb_y ... aa_x ...) '() 
             (list (make-test-mtch (make-bindings (list (make-bind 'aa_x '())
                                                        (make-bind 'bb_y '()))))))
    (test-ab '(bb_y ... aa_x ...) '(a)
             (list (make-test-mtch (make-bindings (list (make-bind 'aa_x '(a))
                                                   (make-bind 'bb_y '()))))))
    (test-ab '(bb_y ... aa_x ...) '(b) 
             (list (make-test-mtch (make-bindings (list (make-bind 'aa_x '())
                                                   (make-bind 'bb_y '(b)))))))
    (test-ab '(bb_y ... aa_x ...) '(b b a a) 
             (list (make-test-mtch (make-bindings (list (make-bind 'aa_x '(a a))
                                                        (make-bind 'bb_y '(b b)))))))
    (test-ab '(aa_y ... aa_x ...) '(a) 
             (list (make-test-mtch (make-bindings (list (make-bind 'aa_x '())
                                                        (make-bind 'aa_y '(a)))))
                   (make-test-mtch (make-bindings (list (make-bind 'aa_x '(a))
                                                        (make-bind 'aa_y '()))))))
    (test-ab '(aa_y ... aa_x ...) '(a a) 
             (list (make-test-mtch (make-bindings (list (make-bind 'aa_x '())
                                                        (make-bind 'aa_y '(a a)))))
                   (make-test-mtch (make-bindings (list (make-bind 'aa_x '(a))
                                                        (make-bind 'aa_y '(a)))))
                   (make-test-mtch (make-bindings (list (make-bind 'aa_x '(a a))
                                                        (make-bind 'aa_y '()))))))
    
    (test-empty '((name x number) ...) '(1 2) (list (make-test-mtch (make-bindings (list (make-bind 'x '(1 2)) (make-bind 'number '(1 2)))))))
    
    (test-empty '(a ...) '(b) #f)
    (test-empty '(a ... b ...) '(c) #f)
    (test-empty '(a ... b) '(b c) #f)
    (test-empty '(a ... b) '(a b c) #f)
    
    (test-lang '(n n ...) '((1 1) 1 1) (list (make-test-mtch (make-bindings (list (make-bind 'n '(1 1))))))
               (list (make-nt 'n (list (make-rhs 'any) (make-rhs 'number)))))
    (test-lang '(n (n ...)) '((1 1) (1 1)) (list (make-test-mtch (make-bindings (list (make-bind 'n '(1 1))))))
               (list (make-nt 'n (list (make-rhs 'any) (make-rhs 'number)))))
    (test-empty '((name x any) 
                  ((name x number) ...))
                '((1 1) (1 1))
                (list (make-test-mtch (make-bindings (list (make-bind 'x '(1 1))
                                                           (make-bind 'any '(1 1))
                                                           (make-bind 'number '(1 1)))))))
    
    (test-empty '((variable_1 variable_1) ...)
                '((x y))
                #f)
    
    
    (test-empty '(number ...) '()
                (list (make-test-mtch (make-bindings (list (make-bind 'number '()))))))
    (test-ab '(aa ...) '()
             (list (make-test-mtch (make-bindings (list (make-bind 'aa '()))))))
    
    
    ;; testing block-in-hole
    (test-empty '(hide-hole a) 'b #f)
    (test-empty '(hide-hole a) 'a (list (make-test-mtch (make-bindings '()))))
    (test-empty '(hide-hole a) '(block-in-hole a) #f)
    (test-empty '(in-hole (x (hide-hole hole)) 1) '(x 1) #f)
    (test-empty '(in-hole (x hole) 1) '(x 1) (list (make-test-mtch (make-bindings '()))))
    (test-empty '(in-hole ((hole #f) (hide-hole hole)) junk)
                '(junk junk2)
                #f)
    
    (test-xab 'lsts '() (list (make-bindings (list (make-bind 'lsts '())))))
    (test-xab 'lsts '(x) (list (make-bindings (list (make-bind 'lsts '(x))))))
    (test-xab 'lsts 'x (list (make-bindings (list (make-bind 'lsts 'x)))))
    (test-xab 'lsts #f (list (make-bindings (list (make-bind 'lsts #f)))))
    (test-xab 'split-out '1 (list (make-bindings (list (make-bind 'split-out 1)))))

    (test-xab 'exp 1 (list (make-bindings (list (make-bind 'exp 1)))))
    (test-xab 'exp '(+ 1 2) (list (make-bindings (list (make-bind 'exp '(+ 1 2))))))
    (test-xab '(in-hole ctxt any)
              '1
              (list (make-bindings (list (make-bind 'ctxt the-hole) (make-bind 'any 1)))))
    (test-xab '(in-hole ctxt (name x any))
              '1
              (list (make-bindings (list (make-bind 'ctxt the-hole) (make-bind 'x 1) (make-bind 'any 1)))))
    (test-xab '(in-hole (name c ctxt) (name x any))
              '(+ 1 2)
              (list (make-bindings (list (make-bind 'ctxt the-hole)
                                         (make-bind 'c the-hole)
                                         (make-bind 'x '(+ 1 2))
                                         (make-bind 'any '(+ 1 2))))
                    (make-bindings (list (make-bind 'ctxt (layer '(+) the-hole '(2)))
                                         (make-bind 'c (layer '(+) the-hole '(2)))
                                         (make-bind 'x 1)
                                         (make-bind 'any 1)))
                    (make-bindings (list (make-bind 'ctxt (layer '(+ 1) the-hole '()))
                                         (make-bind 'c (layer '(+ 1) the-hole '()))
                                         (make-bind 'x 2)
                                         (make-bind 'any 2)))))
    (test-xab '(in-hole (name c ctxt) (name i (+ number_1 number_2)))
              '(+ (+ 1 2) (+ 3 4))
              (list (make-bindings (list (make-bind 'i '(+ 1 2))
                                         (make-bind 'number_1 1)
                                         (make-bind 'number_2 2)
                                         (make-bind 'ctxt (layer '(+) the-hole '((+ 3 4))))
                                         (make-bind 'c (layer '(+) the-hole '((+ 3 4))))))
                    (make-bindings (list (make-bind 'i '(+ 3 4)) 
                                         (make-bind 'number_1 3)
                                         (make-bind 'number_2 4)
                                         (make-bind 'ctxt (layer '(+ (+ 1 2)) the-hole '()))
                                         (make-bind 'c (layer '(+ (+ 1 2)) the-hole '()))))))
    
    (test-empty '(in-hole ((z hole)) (name x any))
                '((z a))
                (list (make-test-mtch (make-bindings (list (make-bind 'x 'a) (make-bind 'any 'a))))))
    (test-empty '(in-hole (name c (z ... hole z ...)) any)
                '(z z)
                (list 
                 (make-test-mtch (make-bindings (list (make-bind 'c (layer '(z) the-hole '())) 
                                                      (make-bind 'any 'z))))
                 (make-test-mtch (make-bindings (list (make-bind 'c (layer '() the-hole '(z)))
                                                      (make-bind 'any 'z))))))
    (test-empty '(in-hole (name c (z ... hole z ...)) any)
                '(z z z)
                (list 
                 (make-test-mtch (make-bindings (list (make-bind 'c (layer '(z z) the-hole '()))
                                                      (make-bind 'any 'z))))
                 (make-test-mtch (make-bindings (list (make-bind 'c (layer '(z) the-hole '(z)))
                                                      (make-bind 'any 'z))))
                 (make-test-mtch (make-bindings (list (make-bind 'c (layer '() the-hole '(z z)))
                                                      (make-bind 'any 'z))))))
    
    (test-empty '(z (in-hole (name c (z hole)) a))
                '(z (z a))
                (list 
                 (make-test-mtch (make-bindings (list (make-bind 'c (layer '(z) the-hole '())))))))
    
    (test-empty '(a (in-hole (name c1 (b (in-hole (name c2 (c hole)) d) hole)) e))
                '(a (b (c d) e))
                (list 
                 (make-test-mtch (make-bindings (list (make-bind 'c2 (layer '(c) the-hole '()))
                                                      (make-bind 'c1 (layer '(b (c d)) the-hole '())))))))

    (test-empty '(in-hole (in-hole hole hole) a)
                'a
                (list (make-test-mtch (make-bindings (list)))))
    
    (test-empty '(a (b (in-hole (name c1 (in-hole (name c2 (c hole)) (d hole))) e)))
                '(a (b (c (d e))))
                (list 
                 (make-test-mtch (make-bindings (list (make-bind 'c1 (layer '(c)
                                                                            (layer '(d) the-hole '())
                                                                            '()))
                                                      (make-bind 'c2 (layer '(c) the-hole '())))))))
    
    (test-empty '((in-hole (name x (hole b)) a)
                  (in-hole (name x (hole b)) a))
                '((a b) (a b))
                (list (make-test-mtch (make-bindings (list (make-bind 'x (layer '() the-hole '(b))))))))
    (test-empty '((in-hole (name x (hole b)) a)
                  (name x (hole b)))
                `((a b) (,the-hole b))
                #f)
    
    (test-xab '(in-hole (a-or-hole ...) a) 
              `(,the-hole a)
              (list (make-bindings (list (make-bind 'a-or-hole (list the-hole the-hole))))))
    (test-xab '(in-hole ((name q (a a-or-hole)) ...) b) 
              `((a ,the-hole) (a b) (a ,the-hole))
              (list (make-bindings 
                     (list (make-bind 'a-or-hole (list the-hole the-hole the-hole))
                           (make-bind 'q (list `(a ,the-hole)
                                               (layer '(a) the-hole '())
                                               `(a ,the-hole)))))))
    (test-xab '(in-hole (name C (a-or-hole ...)) b)
              '(a b a)
              (list (make-bindings (list (make-bind 'C (layer '(a) the-hole '(a)))
                                         (make-bind 'a-or-hole (list 'a the-hole 'a))))))
    
    (test-xab '(in-hole num-tree-ctxt 9) 
              '(1 2 ((7 8 9) 5 6) 3 4)
              (list (make-bindings 
                     (list (make-bind 'num-tree-ctxt
                                      (layer '(1 2) (layer '() (layer '(7 8) the-hole '()) '(5 6))'(3 4)))))))
    
    (let ([matches (match-pattern 
                    (compile-pattern xab-lang '(in-hole num-tree-ctxt 2) #t)
                    '(1 2 3))])
      (run-test 'context-as-list-setup #t (and matches #t))
      (run-test 'context-as-list 
                #t
                (and
                 (andmap (λ (mtch)
                           (define ctxt (lookup-binding (mtch-bindings mtch) 'num-tree-ctxt))
                           (and (layer? ctxt)
                                (match-pattern (compile-pattern xab-lang '(1 hole 3) #t) ctxt)
                                (match-pattern (compile-pattern xab-lang 'num-tree-ctxt #t) ctxt)))
                         matches)
                 #t)))
    
    (test-empty `(+ 1 (side-condition any ,(lambda (bindings) #t) #t))
                '(+ 1 b)
                (list (make-test-mtch (make-bindings (list (make-bind 'any 'b))))))
    (test-empty `(+ 1 (side-condition any ,(lambda (bindings) #f) #f))
                '(+ 1 b)
                #f)
    
    (test-empty `(+ 1 (side-condition b ,(lambda (bindings) #t) #t))
                '(+ 1 b)
                (list (make-test-mtch (make-bindings '()))))
    (test-empty `(+ 1 (side-condition a ,(lambda (bindings) #t)) #t)
                '(+ 1 b)
                #f)

    (test-empty `(side-condition (name x any) ,(lambda (bindings) (eq? (lookup-binding bindings 'x) 'a)) (eq? (term x) 'a))
                'a
                (list 
                 (make-test-mtch (make-bindings (list (make-bind 'x 'a)
                                                      (make-bind 'any 'a))))))

    (test-empty `(+ 1 (side-condition (name x any) ,(lambda (bindings) (eq? (lookup-binding bindings 'x) 'a)) (eq? (term x) 'a)))
                '(+ 1 a)
                (list 
                 (make-test-mtch (make-bindings (list (make-bind 'x 'a)
                                                      (make-bind 'any 'a))))))

    (test-empty `(side-condition (name x any) ,(lambda (bindings) (eq? (lookup-binding bindings 'x) 'a)) (eq? (term x) 'a))
                'b
                #f)
    
    (test-empty `(+ 1 (side-condition (name x any) ,(lambda (bindings) (eq? (lookup-binding bindings 'x) 'a)) (eq? (term x) 'a)))
                '(+ 1 b)
                #f)
    
    (test-empty `(side-condition ((any_1 ..._a) (any_2 ..._a))
                                 ,(lambda (bindings) (error 'should-not-be-called))
                                 (error 'should-not-be-called))
                '((1 2 3) (4 5))
                #f)
    
    (test-xab 'exp_1
              '(+ 1 2)
              (list (make-bindings (list (make-bind 'exp_1 '(+ 1 2))))))
    (test-xab '(exp_1 exp_2)
              '((+ 1 2) (+ 3 4))
              (list (make-bindings (list (make-bind 'exp_1 '(+ 1 2)) (make-bind 'exp_2 '(+ 3 4))))))
    (test-xab '(exp_1 exp_1)
              '((+ 1 2) (+ 3 4))
              #f)
    (test-xab 'nesting-names
              'b
              (list (make-bindings (list (make-bind 'nesting-names 'b)))))
    (test-xab 'nesting-names
              '(a b)
              (list (make-bindings (list (make-bind 'nesting-names '(a b))))))
    (test-xab 'nesting-names
              '(a (a b))
              (list (make-bindings (list (make-bind 'nesting-names '(a (a b)))))))
    (test-xab '((name x a) nesting-names)
              '(a (a (a b)))
              (list (make-bindings (list (make-bind 'x 'a)
                                         (make-bind 'nesting-names '(a (a b)))))))
    (test-xab 'nesting-names
              '(a (a (a (a b))))
              (list (make-bindings (list (make-bind 'nesting-names '(a (a (a (a b)))))))))
    
    (test-xab 'same-in-nt
              '(x x)
              (list (make-bindings (list (make-bind 'same-in-nt '(x x))))))
    (test-xab 'same-in-nt
              '(x y)
              #f)
    
    (test-xab '(in-hole (cross forever-list) 1)
              '(a b c)
              #f)
    
    (test-xab '(in-hole (cross forever-list) 1)
              '(1 x x)
              (list (make-bindings '())))
    
    (test-xab '(in-hole (cross forever-list) 1)
              '(x 1 x)
              (list (make-bindings '())))
    
    
    (test-xab '(in-hole (cross simple) g)
              'g
              (list (make-bindings (list))))
    
    (test-xab 'var '+ #f)
    (test-xab 'var 'anunusedvariable (list (make-bindings (list (make-bind 'var 'anunusedvariable)))))
    (test-xab 'var 'exp (list (make-bindings (list (make-bind 'var 'exp)))))
    (test-xab 'var 'exp_x (list (make-bindings (list (make-bind 'var 'exp_x)))))
    
    (test-xab 'underscore '(+ 1 2) (list (make-bindings (list (make-bind 'underscore '(+ 1 2))))))
    (test-xab 'underscore '2 (list (make-bindings (list (make-bind 'underscore 2)))))
    
    (run-test
     'compatible-context-language1
     (build-compatible-context-language
      (mk-hasheq '((exp . ()) (ctxt . ())))
      (list (make-nt 'exp
                     (list (make-rhs '(+ exp exp))
                           (make-rhs 'number)))
            (make-nt 'ctxt
                     (list (make-rhs '(+ ctxt exp))
                           (make-rhs '(+ exp ctxt))
                           (make-rhs 'hole)))))
     (list
      (make-nt 'ctxt-ctxt
               (list (make-rhs 'hole)
                     (make-rhs `((hide-hole +) (cross ctxt-ctxt) (hide-hole exp)))
                     (make-rhs `((hide-hole +) (hide-hole ctxt) (cross ctxt-exp)))
                     (make-rhs `((hide-hole +) (cross ctxt-exp) (hide-hole ctxt)))
                     (make-rhs `((hide-hole +) (hide-hole exp) (cross ctxt-ctxt)))))
      (make-nt 'ctxt-exp
               (list (make-rhs `((hide-hole +) (cross ctxt-exp) (hide-hole exp)))
                     (make-rhs `((hide-hole +) (hide-hole exp) (cross ctxt-exp)))))
      (make-nt 'exp-ctxt
               (list (make-rhs `((hide-hole +) (cross exp-ctxt) (hide-hole exp)))
                     (make-rhs `((hide-hole +) (hide-hole ctxt) (cross exp-exp)))
                     (make-rhs `((hide-hole +) (cross exp-exp) (hide-hole ctxt)))
                     (make-rhs `((hide-hole +) (hide-hole exp) (cross exp-ctxt)))))
      (make-nt 'exp-exp 
               (list (make-rhs 'hole) 
                     (make-rhs `((hide-hole +) (cross exp-exp) (hide-hole exp))) 
                     (make-rhs `((hide-hole +) (hide-hole exp) (cross exp-exp)))))))
    
    (run-test
     'compatible-context-language2
     (build-compatible-context-language
      (mk-hasheq '((m . ()) (v . ())))
      (list (make-nt 'm (list (make-rhs '(m m)) (make-rhs '(+ m m)) (make-rhs 'v)))
            (make-nt 'v (list (make-rhs 'number) (make-rhs '(lambda (x) m))))))
     (list
      (make-nt 'v-v (list (make-rhs 'hole) (make-rhs '((hide-hole lambda) (hide-hole (x)) (cross v-m)))))
      (make-nt 'v-m
               (list
                (make-rhs '((cross v-m) (hide-hole m)))
                (make-rhs '((hide-hole m) (cross v-m)))
                (make-rhs '((hide-hole +) (cross v-m) (hide-hole m)))
                (make-rhs '((hide-hole +) (hide-hole m) (cross v-m)))
                (make-rhs '(cross v-v))))
      (make-nt 'm-v (list (make-rhs '((hide-hole lambda) (hide-hole (x)) (cross m-m)))))
      (make-nt 'm-m
               (list
                (make-rhs 'hole)
                (make-rhs '((cross m-m) (hide-hole m)))
                (make-rhs '((hide-hole m) (cross m-m)))
                (make-rhs '((hide-hole +) (cross m-m) (hide-hole m)))
                (make-rhs '((hide-hole +) (hide-hole m) (cross m-m)))
                (make-rhs '(cross m-v))))))
    
    (run-test
     'compatible-context-language3
     (build-compatible-context-language
      (mk-hasheq '((m . ()) (seven . ())))
      (list (make-nt 'm (list (make-rhs '(m seven m)) (make-rhs 'number)))
            (make-nt 'seven (list (make-rhs 7)))))
     `(,(make-nt
         'm-m
         `(,(make-rhs 'hole) 
           ,(make-rhs `((cross m-m) (hide-hole seven) (hide-hole m)))
           ,(make-rhs `((hide-hole m) (hide-hole seven) (cross m-m)))))
       ,(make-nt
         'seven-m
         `(,(make-rhs `((cross seven-m) (hide-hole seven) (hide-hole m)))
           ,(make-rhs `((hide-hole m) (cross seven-seven) (hide-hole m)))
           ,(make-rhs `((hide-hole m) (hide-hole seven) (cross seven-m)))))
       ,(make-nt 'seven-seven `(,(make-rhs 'hole)))))
    
    (run-test
     'compatible-context-language4
     (build-compatible-context-language
      (mk-hasheq '((a . ()) (b . ()) (c . ())))
      (list (make-nt 'a (list (make-rhs 'b)))
            (make-nt 'b (list (make-rhs 'c)))
            (make-nt 'c (list (make-rhs 3)))))
     (list (make-nt 'c-c (list (make-rhs 'hole)))
           (make-nt 'c-b (list (make-rhs '(cross c-c))))
           (make-nt 'c-a (list (make-rhs '(cross c-b))))
           (make-nt 'b-b (list (make-rhs 'hole)))
           (make-nt 'b-a (list (make-rhs '(cross b-b))))
           (make-nt 'a-a (list (make-rhs 'hole)))))
    
    (let ([t `((1 ,the-hole) ,the-hole)])
      (test-xab
       'W 
       t
       (list (make-bindings (list (make-bind 'W t))))))

    (let ([t `(((1 (2 ,the-hole)) ,the-hole)
               ,(layer '() (layer '(1) the-hole '()) `(,the-hole)))])
      (test-xab 'W t (list (make-bindings (list (make-bind 'W t))))))

    (let ([t `(((1 (2 hole)) hole)
               ((1 hole) hole))])
      (test-xab 'W t #f))

    (let ([t `(((1 ,the-hole) (2 ,the-hole))
               ,(layer `((1 ,the-hole)) the-hole '()))])
      (test-xab 'W t (list (make-bindings (list (make-bind 'W t))))))

    (let ([id '(λ (x) x)])
      (test-unwrapped-cont-vals
       'e
       id
       (list (make-test-mtch 
              (make-bindings (list (make-bind 'e id)))))))
    
    (let* ([f '(λ (x) x)]
           [a '(λ (y) y)]
           [t `(,f ,a)])
      (test-unwrapped-cont-vals
       '(in-hole E e)
       t
       (list (make-test-mtch 
              (make-bindings 
               (list (make-bind 'e t)
                     (make-bind 'E the-hole))))
             (make-test-mtch 
              (make-bindings 
               (list (make-bind 'e f)
                     (make-bind 'E (layer '() the-hole `(,a))))))
             (make-test-mtch 
              (make-bindings 
               (list (make-bind 'e a)
                     (make-bind 'E (layer `(,f) the-hole '()))))))))
    
    (let* ([v '(λ (y) y)]
           [r `((λ (x) x) ,v)]
           [t `(,the-hole ,r)])
      (test-unwrapped-cont-vals
       '(in-hole E (name r ((λ (x) e) v)))
       t
       (list (make-test-mtch
              (make-bindings
               (list (make-bind 'E (layer `(,the-hole) the-hole '()))
                     (make-bind 'r r)
                     (make-bind 'x 'x)
                     (make-bind 'e 'x)
                     (make-bind 'v v)))))))
    
    (let ([t `(,the-hole ,the-hole)])
      (test-unwrapped-cont-vals
       'v
       t
       (list (make-test-mtch
              (make-bindings (list (make-bind 'v t))))))
      (test-unwrapped-cont-vals
       '(in-hole E e)
       t
       (list (make-test-mtch
              (make-bindings (list (make-bind 'E the-hole)
                                   (make-bind 'e t))))
             (make-test-mtch
              (make-bindings (list (make-bind 'E (layer '() the-hole `(,the-hole)))
                                   (make-bind 'e the-hole))))
             (make-test-mtch
              (make-bindings (list (make-bind 'E (layer `(,the-hole) the-hole '()))
                                   (make-bind 'e the-hole)))))))
    
    (let* ([x 'y]
           [e 'y]
           [v `(,the-hole ,the-hole)]
           [t `((λ (,x) ,e) ,v)])
      (test-unwrapped-cont-vals
       '((λ (x) e) v)
       t
       (list (make-test-mtch
              (make-bindings (list (make-bind 'x x)
                                   (make-bind 'e e)
                                   (make-bind 'v v)))))))
    
    (run-test/cmp 'split-underscore1 (split-underscore 'a_1) 'a eq?)
    (run-test/cmp 'split-underscore2 (split-underscore 'a_!_1) 'a eq?)
    (run-test/cmp 'split-underscore3 
                  (with-handlers ([exn:fail? (λ (e) (cadr (regexp-match #rx"^([^:]+):" (exn-message e))))]) 
                    (split-underscore 'a_b_1))
                  "compile-pattern"
                  equal?)
    
    (test-ellipsis-binding '((number_1 number_2) ...) '() '((1 2)))
    (test-ellipsis-binding '((name x number_1) ...) '() '(1 2))
    (test-ellipsis-binding '(((number_1 ...) (number_2 ...)) ...) '() '(((1) (2))))
    (test-ellipsis-binding '(number ... variable) '() '(1 x))
    (test-ellipsis-binding '((in-hole H_1 number_1) ...) '((H hole)) '(1 2))
    
    (cond
      [(= failures 0)
       (printf "matcher-test.rkt: all ~a tests passed.\n" test-count)]
      [else
       (printf "matcher-test.rkt: ~a test~a failed.\n" 
               failures
               (if (= failures 1)
                   ""
                   "s"))]))

  ;; mk-hasheq : (listof (cons sym any)) -> hash-table
  ;; builds a hash table that has the bindings in assoc-list
  (define (mk-hasheq assoc-list)
    (let ([ht (make-hash-table)])
      (for-each
       (lambda (a)
         (hash-table-put! ht (car a) (cdr a)))
       assoc-list)
      ht))
  
  ;; test-empty : sexp[pattern] sexp[term] answer -> void
  ;; returns #t if pat matching exp with the empty language produces ans.
  (define (test-empty pat exp ans)
    (run-match-test
     `(match-pattern (compile-pattern (compile-language 'pict-stuff-not-used '() '()) ',pat #t) ',exp)
     (match-pattern 
      (compile-pattern (compile-language 'pict-stuff-not-used '() '()) pat #t)
      exp)
     ans))
  
  ;; make-nt-map : (listof nt) -> (listof (listof symbol))
  (define (make-nt-map nts)
    (map (λ (x) (list (nt-name x))) nts))
  
  ;; test-lang : sexp[pattern] sexp[term] answer (list/c nt) -> void
  ;; returns #t if pat matching exp with the language defined by the given nts
  (define (test-lang pat exp ans nts)
    (let ([nt-map (make-nt-map nts)])
      (run-match-test
       `(match-pattern (compile-pattern (compile-language 'pict-stuff-not-used ',nts ',nt-map) ',pat #t) ',exp)
       (match-pattern 
        (compile-pattern (compile-language 'pict-stuff-not-used nts nt-map) pat #t)
        exp)
       ans)))
  
  (define xab-lang #f)
  ;; test-xab : sexp[pattern] sexp[term] (or/c false/c (listof binding)) -> void
  ;; returns #t if pat matching exp with a simple language produces ans.
  (define (test-xab pat exp ans)
    (unless xab-lang
      (let ([nts
             (list (make-nt 'exp
                            (list (make-rhs '(+ exp exp))
                                  (make-rhs 'number)))
                   (make-nt 'ctxt
                            (list (make-rhs '(+ ctxt exp))
                                  (make-rhs '(+ exp ctxt))
                                  (make-rhs 'hole)))
                   
                   (make-nt 'ec-one
                            (list (make-rhs '(+ (hole xx) exp))
                                  (make-rhs '(+ exp (hole xx)))))
                   
                   (make-nt 'same-in-nt (list (make-rhs '((name x any) (name x any)))))
                   
                   (make-nt 'forever-list (list (make-rhs '(forever-list forever-list ...))
                                                (make-rhs 'x)))
                   
                   (make-nt 'lsts
                            (list (make-rhs '())
                                  (make-rhs '(x))
                                  (make-rhs 'x)
                                  (make-rhs '#f)))
                   (make-nt 'split-out
                            (list (make-rhs 'split-out2)))
                   (make-nt 'split-out2
                            (list (make-rhs 'number)))
                   
                   (make-nt 'simple (list (make-rhs 'simple-rhs)))
                   
                   (make-nt 'nesting-names
                            (list (make-rhs '(a (name x nesting-names)))
                                  (make-rhs 'b)))
                   (make-nt 'var (list (make-rhs `variable-not-otherwise-mentioned)))
                   
                   (make-nt 'underscore (list (make-rhs 'exp_1)))
                   
                   (make-nt 'a-or-hole (list (make-rhs 'hole) (make-rhs 'a)))
                   
                   (make-nt 'num-tree (list (make-rhs 'number)
                                            (make-rhs '(num-tree ...))))
                   (make-nt 'num-tree-ctxt (list (make-rhs 'hole)
                                                 (make-rhs '(num-tree ... num-tree-ctxt num-tree ...))))
                   
                   (make-nt 'W (list (make-rhs 'hole)
                                     (make-rhs '((in-hole W_1 (number hole))
                                                 W_1)))))])
      (set! xab-lang
            (compile-language 'pict-stuff-not-used
                              nts
                              (map (λ (x) (list (nt-name x))) nts)))))
    (run-match-test
     `(match-pattern (compile-pattern xab-lang ',pat #t) ',exp)
     (match-pattern (compile-pattern xab-lang pat #t) exp)
     (and ans
          (map (λ (b) (make-test-mtch b))
               ans))))
  
  (define ab-lang #f)
  ;; test-xab : sexp[pattern] sexp[term] answer -> void
  ;; returns #t if pat matching exp with a simple language produces ans.
  (define (test-ab pat exp ans)
    (unless ab-lang
      (set! ab-lang
            (compile-language 
             'pict-stuff-not-used
             (list (make-nt 'aa
                            (list (make-rhs 'a)))
                   (make-nt 'bb
                            (list (make-rhs 'b))))
             '((aa) (bb)))))
    (run-match-test
     `(match-pattern (compile-pattern ab-lang ',pat #t) ',exp)
     (match-pattern (compile-pattern ab-lang pat #t) exp)
     ans))
  
  (define unwrapped-cont-vals #f)
  (define (test-unwrapped-cont-vals pat term ans)
    (unless unwrapped-cont-vals
      (define nts
        (list (make-nt 'e (list (make-rhs '(e e))
                                (make-rhs 'v)
                                (make-rhs 'x)))
              (make-nt 'x (list (make-rhs 'variable-not-otherwise-mentioned)))
              (make-nt 'v (list (make-rhs '(λ (x) e))
                                (make-rhs 'E)))
              (make-nt 'E (list (make-rhs 'hole)
                                (make-rhs '(E e))
                                (make-rhs '(v E))))))
      (set! unwrapped-cont-vals
            (compile-language
             'pict-stuff-not-used
             nts
             (map (λ (x) (list (nt-name x))) nts))))
    (run-match-test
     `(match-pattern (compile-pattern unwraped-cont-vals ',pat #t) ',term)
     (match-pattern (compile-pattern unwrapped-cont-vals pat #t) term)
     ans))
  
  ;; test-ellipses : sexp sexp -> void
  (define (test-ellipses pat expected)
    (run-test
     `(rewrite-ellipses test-suite:non-underscore-binder? ',pat (lambda (x) x))
     (rewrite-ellipses test-suite:non-underscore-binder? pat (lambda (x) x))
     expected))
  
  (define (test-suite:non-underscore-binder? x)
    (memq x '(number any variable string)))
  
  ;; test-ellipsis-binding: sexp sexp sexp -> boolean
  ;; Checks that `extract-empty-bindings' produces bindings in the same order
  ;; as the matcher, as required by `collapse-single-multiples'
  (define (test-ellipsis-binding pat nts/sexp exp)
    (define (binding-names bindings)
      (map (λ (b)
             (cond [(bind? b) (bind-name b)]
                   [(mismatch-bind? b) (mismatch-bind-name b)]))
           bindings))
    (run-test
     `(test-ellipsis-binding ,pat)
     (binding-names
      (bindings-table-unchecked
       (mtch-bindings
        (car 
         ((compiled-pattern-cp
           (let ([nts (map (λ (nt-def) (nt (car nt-def) (map rhs (cdr nt-def)))) nts/sexp)])
             (compile-pattern (compile-language 'pict-stuff-not-used nts (make-nt-map nts)) pat #t)))
          exp)))))
     (binding-names (extract-empty-bindings test-suite:non-underscore-binder? pat))))
  
  ;; run-test/cmp : sexp any any (any any -> boolean)
  ;; compares ans with expected. If failure,
  ;; prints info about the test and increments failures
  (define failures 0)
  (define test-count 0)
  (define (run-test/cmp symbolic ans expected cmp?)
    (set! test-count (+ test-count 1))
    (cond
      [(cmp? ans expected)
       '(printf "passed: ~s\n" symbolic)]
      [else 
       (set! failures (+ failures 1))
       (fprintf (current-error-port)
                "    test: ~s\nexpected: ~e\n     got: ~e\n"
                symbolic expected ans)]))
  
  (define (run-test symbolic ans expected) (run-test/cmp symbolic ans expected equal/bindings?))
  
  ;; run-match-test : sexp got expected
  ;;   expects both ans and expected to be lists or both to be #f and
  ;;   compares them using a set-like equality if they are lists
  (define (run-match-test symbolic ans expected)
    (run-test/cmp
     symbolic ans expected
     (λ (xs ys)
       (cond
         [(and (not xs) (not ys)) #t]
         [(and (list? xs)
               (list? ys))
          (and (andmap (λ (x) (memf (λ (y) (equal/bindings? x y)) ys)) xs)
               (andmap (λ (y) (memf (λ (x) (equal/bindings? x y)) xs)) ys)
               (= (length xs) (length ys)))]
         [else #f]))))
  
  (test))
