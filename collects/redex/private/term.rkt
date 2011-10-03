#lang scheme/base

(require (for-syntax scheme/base 
                     "term-fn.rkt"
                     syntax/boundmap
                     syntax/parse
                     racket/syntax)
         racket/match
         "error.rkt"
         "matcher.rkt")

(provide term term-let define-term
         hole in-hole hide-hole plug
         term-let/error-name term-let-fn term-define-fn)

(define-syntax (hole stx) (raise-syntax-error 'hole "used outside of term"))
(define-syntax (in-hole stx) (raise-syntax-error 'in-hole "used outside of term"))
(define-syntax (hide-hole stx) (raise-syntax-error 'hide-hole "used outside of term"))

(define-struct hidden-hole (term))
(define-struct plugged (term hole?))

(define (with-syntax* stx)
  (syntax-case stx ()
    [(_ () e) (syntax e)]
    [(_ (a b ...) e) (syntax (with-syntax (a) (with-syntax* (b ...) e)))]))

(define-syntax-rule (term t)
  (#%expression (term/private t)))

(define-syntax (term/private orig-stx)
  (define outer-bindings '())
  (define applied-metafunctions
    (make-free-identifier-mapping))
  
  (define (rewrite stx)
    (let-values ([(rewritten _) (rewrite/max-depth stx 0)])
      rewritten))
  
  (define (metafunction-application f)
    #`(λ (x) (#,f (map make-term (syntax->list x)))))
  
  (define (rewrite-application fn args depth)
    (let-values ([(rewritten max-depth) (rewrite/max-depth args depth)])
      (let ([result-id (car (generate-temporaries '(f-results)))])
        (let loop ([func fn]
                   [args-stx rewritten]
                   [res result-id]
                   [args-depth (min depth max-depth)])
          (with-syntax ([func func]
                        [args args-stx]
                        [res res])
            (if (zero? args-depth)
                (begin
                  (set! outer-bindings 
                        (cons (syntax [res (func (quasisyntax args))])
                              outer-bindings))
                  (values result-id (min depth max-depth)))
                (loop (syntax (λ (l) (map func (syntax->list l))))
                      (syntax/loc args-stx (args (... ...)))
                      (syntax (res (... ...)))
                      (sub1 args-depth))))))))
  
  (define (rewrite/max-depth stx depth)
    (syntax-case stx (unquote unquote-splicing in-hole hole hide-hole)
      [(metafunc-name arg ...)
       (and (identifier? (syntax metafunc-name))
            (term-fn? (syntax-local-value (syntax metafunc-name) (λ () #f))))
       (let ([f (term-fn-get-id (syntax-local-value/record (syntax metafunc-name) (λ (x) #t)))])
         (free-identifier-mapping-put! applied-metafunctions f #t)
         (rewrite-application (metafunction-application f) (syntax/loc stx (arg ...)) depth))]
      [f
       (and (identifier? (syntax f))
            (term-fn? (syntax-local-value (syntax f) (λ () #f))))
       (raise-syntax-error 'term "metafunction must be in an application" orig-stx stx)]
      [x
       (and (identifier? (syntax x))
            (term-id? (syntax-local-value (syntax x) (λ () #f))))
       (let ([id (syntax-local-value/record (syntax x) (λ (x) #t))])
         (values (datum->syntax (term-id-id id) (syntax-e (term-id-id id)) (syntax x))
                 (term-id-depth id)))]
      [x
       (defined-term-id? #'x)
       (let ([ref (syntax-property
                   (defined-term-value (syntax-local-value #'x))
                   'disappeared-use #'x)])
         (with-syntax ([v #`(begin
                              #,(defined-check ref "term" #:external #'x)
                              #,ref)])
           (values #'#,v 0)))]
      [(unquote x)
       (values (syntax (unsyntax x)) 0)]
      [(unquote . x)
       (raise-syntax-error 'term "malformed unquote" orig-stx stx)]
      [(unquote-splicing x)
       (values (syntax (unsyntax-splicing x)) 0)]
      [(unquote-splicing . x)
       (raise-syntax-error 'term "malformed unquote splicing" orig-stx stx)]
      [(in-hole id body)
       (rewrite-application #'plug-instantiated (syntax/loc stx (id body)) depth)]
      [(in-hole . x)
       (raise-syntax-error 'term "malformed in-hole" orig-stx stx)]
      [(hide-hole t)
       (rewrite-application (metafunction-application #'hidden-hole) (syntax/loc stx (t)) depth)]
      [(hide-hole . _)
       (raise-syntax-error 'term "malformed hide-hole" orig-stx stx)]
      [hole (values (syntax (unsyntax the-hole)) 0)]
      
      
      [() (values stx 0)]
      [(x ... . y)
       (not (null? (syntax->list #'(x ...))))
       (let-values ([(x-rewrite max-depth)
                     (let i-loop ([xs (syntax->list (syntax (x ...)))])
                       (cond
                         [(null? xs) (rewrite/max-depth #'y depth)]
                         [else
                          (let ([new-depth (if (and (not (null? (cdr xs)))
                                                    (identifier? (cadr xs))
                                                    (free-identifier=? (quote-syntax ...)
                                                                       (cadr xs)))
                                               (+ depth 1)
                                               depth)])
                            (let-values ([(fst fst-max-depth)
                                          (rewrite/max-depth (car xs) new-depth)]
                                         [(rst rst-max-depth)
                                          (i-loop (cdr xs))])
                              (values (cons fst rst)
                                      (max fst-max-depth rst-max-depth))))]))])
         (values (datum->syntax stx x-rewrite stx) max-depth))]
      
      [_ (values stx 0)]))
  
  (syntax-case orig-stx ()
    [(_ template)
     (with-disappeared-uses
      (with-syntax ([rewritten (rewrite (syntax template))])
        #`(begin
            #,@(free-identifier-mapping-map
                applied-metafunctions
                (λ (f _) (defined-check f "metafunction")))
            #,(let loop ([bs (reverse outer-bindings)])
                (cond
                  [(null? bs) (syntax (make-term (quasisyntax rewritten)))]
                  [else (with-syntax ([rec (loop (cdr bs))]
                                      [fst (car bs)])
                          (syntax (with-syntax (fst)
                                    rec)))])))))]))

(define (plug-instantiated args)
  (syntax-case args ()
    [(c t)
     (let*-values ([(c* _) (make-term* #'c)]
                   [(t* t?) (make-term* #'t)]
                   [(p p?) (plug* c* t* t?)])
       (plugged p p?))]))

(define (make-term s)
  (let-values ([(t _) (make-term* s)])
    t))

(define make-term*
  (match-lambda
    [(? syntax? s)
     (make-term* (syntax-e s))]
    [(hidden-hole (list t))
     (values t #f)]
    [(plugged t t?)
     (values t t?)]
    [(? hole?)
     (values the-hole #t)]
    [(? layer? l)
     (values l #t)]
    [(cons h t)
     (define-values (ht h?) (make-term* h))
     (define-values (tt t?) (make-term* t))
     (join ht h? tt t?)]
    [t (values t #f)]))

(define join
  (match-lambda**
   [((? context? t) #t ts #f)
    (values (layer null t ts) #t)]
   [(t #f (layer l c r) #t)
    (values (layer (cons t l) c r) #t)]
   [(t t? (layer l c r) ts?)
    (values (cons t (append l (cons c r)))
            (or t? ts?))]
   [(t t? ts ts?)
    (values (cons t ts) (or t? ts?))]))

(define (plug* C t t?)
  (match C
    [(? hole?) 
     (values t t?)]
    [(layer l C* r)
     (let-values ([(p p?) (plug* C* t t?)])
       (if p?
           (values (layer l p r) #t)
           (values (append l (cons p r)) #f)))]
    [_ (redex-error 'plug "term has no pluggable hole:\n~s" C)]))

(define (plug C t)
  (let-values ([(p _) (plug* C t (has-context? t))])
    p))

(define has-context?
  (match-lambda
    [(? hole?) #t]
    [(? layer?) #t]
    [(cons l r) 
     (or (has-context? l)
         (has-context? r))]
    [_ #f]))

(define-syntax (term-let-fn stx)
  (syntax-case stx ()
    [(_ ([f rhs] ...) body1 body2 ...)
     (with-syntax ([(g ...) (generate-temporaries (syntax (f ...)))])
       (syntax 
        (let ([g rhs] ...)
          (let-syntax ([f (make-term-fn #'g)] ...)
            body1
            body2 ...))))]))

(define-syntax (term-define-fn stx)
  (syntax-case stx ()
    [(_ id exp)
     (with-syntax ([id2 (datum->syntax #'here (syntax-e #'id))])
       (syntax
        (begin
          (define id2 exp)
          (define-syntax id
            (make-term-fn ((syntax-local-certifier) #'id2))))))]))

(define-syntax (term-let/error-name stx)
  (syntax-case stx ()
    [(_ error-name ([x1 rhs1] [x rhs] ...) body1 body2 ...)
     (let-values ([(orig-names new-names depths new-x1)
                   (let loop ([stx #'x1] [depth 0])
                     (define ((combine orig-names new-names depths new-pat)
                              orig-names* new-names* depths* new-pat*)
                       (values (append orig-names orig-names*)
                               (append new-names new-names*)
                               (append depths depths*)
                               (cons new-pat new-pat*)))
                     (syntax-case stx (...)
                       [x 
                        (and (identifier? #'x)
                             (not (free-identifier=? (quote-syntax ...) #'x)))
                        (let ([new-name (datum->syntax #'here (syntax-e #'x))])
                          (values (list #'x)
                                  (list new-name)
                                  (list depth)
                                  new-name))]
                       [(x (... ...) . xs)
                        (let-values ([(orig-names new-names depths new-pat)
                                      (call-with-values
                                       (λ () (loop #'xs depth))
                                       (call-with-values
                                        (λ () (loop #'x (add1 depth)))
                                        combine))])
                          (values orig-names new-names depths 
                                  (list* (car new-pat) #'(... ...) (cdr new-pat))))]
                       [(x . xs)
                        (call-with-values
                         (λ () (loop #'xs depth))
                         (call-with-values
                          (λ () (loop #'x depth))
                          combine))]
                       [_
                        (values '() '() '() stx)]))])
       (with-syntax ([(orig-names ...) orig-names]
                     [(new-names ...) new-names]
                     [(depths ...) depths]
                     [new-x1 new-x1]
                     [no-match (syntax/loc (syntax rhs1)
                                 (error 'error-name "term ~s does not match pattern ~s" rhs1 'x1))])
         (syntax
          (syntax-case rhs1 ()
            [new-x1 
             (let-syntax ([orig-names (make-term-id #'new-names (syntax-e #'depths))] ...)
               (term-let/error-name error-name ((x rhs) ...) body1 body2 ...))]
            [_ no-match]))))]
    [(_ error-name () body1 body2 ...)
     (syntax
      (begin body1 body2 ...))]
    [(_ x)
     (raise-syntax-error 'term-let "expected at least one body" stx)]))

(define-syntax (term-let stx)
  (syntax-case stx ()
    [(_ () body1)
     #'body1]
    [(_ ([x rhs] ...) body1 body2 ...)
     (syntax
      (term-let/error-name term-let ((x rhs) ...) body1 body2 ...))]
    [(_ x)
     (raise-syntax-error 'term-let "expected at least one body" stx)]))

(define-syntax (define-term stx)
  (syntax-parse stx
    [(_ x:id t:expr)
     (not-expression-context stx)
     #'(begin
         (define term-val (term t))
         (define-syntax x (defined-term #'term-val)))]))