#lang racket

(require "SL-syntax.rkt" "SL-semantics.rkt"
         "TL-syntax.rkt" "TL-semantics.rkt"
         redex)

(define-syntax-rule (make-eval red-rel-expr lang-id)
  (let ([red-rel red-rel-expr])
    (define extract-answer
      (term-match/single 
       lang-id
       [(Σ / v) (term (answer v))]
       [any #f]))
    (λ (program)
      (define state (unique-normal-form program red-rel))
      (define answer (extract-answer state))
      (or answer
          (raise (eval-undefined "stuck" (current-continuation-marks) program state))))))
(define-struct (eval-undefined exn:fail) (input stuck-state))
(provide make-eval
         (struct-out eval-undefined))

(define-metafunction SL
  [(answer (λ (x ...) e))
   procedure]
  [(answer (K v ...))
   (K (answer v) ...)]
  [(answer σ)
   reference]
  [(answer (κ E))
   procedure])

(define (unique-normal-form t R)
  (match (let ([nfs '()]
               [seen (set)])
           (let recur ([u t] [s (max-normalization-steps)])
             (when (negative? s)
               (raise (normalization-timeout "too many steps" (current-continuation-marks))))
             (unless (set-member? seen u)
               (set! seen (set-add seen u))
               (match (apply-reduction-relation R u)
                 [(list) (set! nfs (cons u nfs))]
                 [vs (for ([v vs]) (recur v (sub1 s)))])))
           nfs)
    [(list u) u]
    [(list) (raise (normalization-timeout "no normal forms" (current-continuation-marks)))]
    [_ (error 'unique-normal-form "distinct normal forms")]))
(define max-normalization-steps (make-parameter +inf.0))
(define-struct (normalization-timeout exn:fail) ())
(provide max-normalization-steps
         (struct-out normalization-timeout))

(define-syntax (test-result stx)
  (syntax-case stx ()
    [(_ L R Σ0 e0 v)
     #`(redex-let L ([(Σ / e) (unique-normal-form (term (Σ0 / e0)) R)])
                  #,(syntax/loc stx (test-equal (term e) (term v))))]))

(define-syntax (test-stuck stx)
  (syntax-case stx ()
    [(_ L R v? Σ0 e0)
     #`(redex-let L ([(Σ / e) (unique-normal-form (term (Σ0 / e0)) R)])
                  #,(syntax/loc stx (test-predicate (negate v?) (term e))))]))

(define-syntax-rule (define-test-forms language relation test-result-id test-stuck-id)
  (begin
    (define value? (redex-match language v))
    (define-syntax-rule (test-result-id . args)
      (test-result language relation . args))
    (define-syntax-rule (test-stuck-id . args)
      (test-stuck language relation value? . args))
    (provide test-result-id test-stuck-id)))

(define-test-forms SL -->SL test-SL-result test-SL-stuck)
(define-test-forms TL -->TL test-TL-result test-TL-stuck)

(define-metafunction SL
  [(make-store) ∅]
  [(make-store [any_1 any_2] any_3 ...)
   ((make-store any_3 ...)
    [(ref any_1) ↦ any_2])])
(provide make-store)
