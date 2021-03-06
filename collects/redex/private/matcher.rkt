#lang scheme/base

#|

Note: the patterns described in the doc.txt file are
slightly different than the patterns processed here.
The difference is in the form of the side-condition
expressions. Here they are procedures that accept
binding structures, instead of expressions. The
reduction (And other) macros do this transformation
before the pattern compiler is invoked.

|#
(require scheme/list
         scheme/match
         scheme/contract
         racket/set
         "underscore-allowed.rkt")

(define-struct compiled-pattern (cp))

(define caching-enabled? (make-parameter #t))

;; lang = (listof nt)
;; nt = (make-nt sym (listof rhs))
;; rhs = (make-rhs single-pattern)
;; single-pattern = sexp
(define-struct nt (name rhs) #:inspector (make-inspector))
(define-struct rhs (pattern) #:inspector  (make-inspector))

;; var = (make-var sym sexp)
;; patterns are sexps with `var's embedded
;; in them. It means to match the
;; embedded sexp and return that binding

;; bindings = (make-bindings (listof rib))
;; rib = (make-bind sym sexp)
;; if a rib has a pair, the first element of the pair should be treated as a prefix on the identifer
;; NOTE: the bindings may contain mismatch-ribs temporarily, but they are all removed
;;       by merge-multiples/remove, a helper function called from match-pattern
(define-values (make-bindings bindings-table bindings?)
  (let () 
    (define-struct bindings (table) #:inspector (make-inspector)) ;; for testing, add inspector
    (define mt-bindings (make-bindings null))
    (values (lambda (table) (if (null? table) mt-bindings (make-bindings table)))
            bindings-table
            bindings?)))

(define-struct bind (name exp) #:inspector (make-inspector)) ;; for testing, add inspector
(define-struct mismatch-bind (name exp) #:inspector (make-inspector)) ;; for testing, add inspector

;; repeat = (make-repeat compiled-pattern (listof rib) (union #f symbol) boolean)
(define-struct repeat (pat empty-bindings suffix mismatch?) #:inspector (make-inspector)) ;; inspector for tests below

;; compiled-pattern : exp -> (union #f (listof mtch))

(define-struct mtch (bindings matched) #:transparent)
(define (literal-match x)
  (mtch (make-bindings '())
        (non-decomp)))

(define-struct decomp (context term) #:transparent)
(define-struct non-decomp () #:transparent)

(define (non-decomps matches)
  (filter (match-lambda
            [(mtch _ (decomp _ _)) #f]
            [(mtch _ (non-decomp)) #t])
          matches))

(define-struct layer (left focus right) #:transparent)
(define (context? t)
  (or (hole? t)
      (layer? t)))

(define none
  (let ()
    (define-struct none ())
    (make-none)))
(define (none? x) (eq? x none))

;; compiled-lang : (make-compiled-lang (listof nt) (listof nt)
;;                                     hash[sym -o> compiled-pattern]
;;                                     hash[sym -o> compiled-pattern]
;;                                     (set/c sym)
;;                                     hash[sym -o> compiled-pattern]
;;                                     hash[sym -o> compiled-pattern]
;;                                     (set/c sym)
;;                                     hash[sexp[pattern] -o> (cons compiled-pattern boolean)]
;;                                     hash[sexp[pattern] -o> (cons compiled-pattern boolean)]
;;                                     pict-builder
;;                                     (listof symbol)
;;                                     (listof (listof symbol))) -- keeps track of `primary' non-terminals

(define-struct compiled-lang (lang cclang 
                                   ht list-ht left-rec-nts
                                   across-ht across-list-ht across-left-rec-nts
                                   cache bind-names-cache pict-builder
                                   literals nt-map))

;; lookup-binding : bindings (union sym (cons sym sym)) [(-> any)] -> any
(define (lookup-binding bindings
                        sym
                        [fail (lambda () 
                                (error 'lookup-binding "didn't find ~e in ~e" sym bindings))])
  (let loop ([ribs (bindings-table bindings)])
    (cond
      [(null? ribs) (fail)]
      [else
       (let ([rib (car ribs)])
         (if (and (bind? rib) (equal? (bind-name rib) sym))
             (bind-exp rib)
             (loop (cdr ribs))))])))

;; compile-language : language-pict-info[see pict.rkt] (listof nt) (listof (listof sym)) -> compiled-lang
(define (compile-language pict-info lang nt-map)
  (define (init-ht)
    (define ht (make-hasheq))
    (for-each (lambda (nt) (hash-set! ht (nt-name nt) null))
              lang)
    ht)
  (define clang-ht (init-ht))
  (hash-for-each
   clang-ht
   (lambda (nt rhs)
     (when (has-underscore? nt)
       (error 'compile-language "cannot use underscore in nonterminal name, ~s" nt))))
  (define clang-list-ht (init-ht))
  (define across-ht (make-hasheq))
  (define across-list-ht (make-hasheq))
  (define compatible-context-language
    (build-compatible-context-language clang-ht lang))
  (for-each (lambda (nt)
              (hash-set! across-ht (nt-name nt) null)
              (hash-set! across-list-ht (nt-name nt) null))
            compatible-context-language)
  (define cache (make-hash))
  (define bind-names-cache (make-hash))
  (define literals (extract-literals lang))
  (define-values (left-rec-nts across-left-rec-nts)
    (left-recursive-non-terminals lang compatible-context-language))
  (define clang 
    (make-compiled-lang lang compatible-context-language 
                        clang-ht clang-list-ht left-rec-nts
                        across-ht across-list-ht across-left-rec-nts
                        cache bind-names-cache
                        pict-info
                        literals
                        nt-map))
  (define non-list-nt-table (build-non-list-nt-label lang))
  (define list-nt-table (build-list-nt-label lang))
  (define (do-compilation ht list-ht lang prefix-cross?)
    (for-each
     (lambda (nt)
       (for-each
        (lambda (rhs)
          (let ([compiled-pattern 
                 (compile-pattern/cross? clang (rhs-pattern rhs) prefix-cross? #f)])
            (let ([add-to-ht
                   (lambda (ht)
                     (hash-set!
                      ht
                      (nt-name nt)
                      (cons compiled-pattern (hash-ref ht (nt-name nt)))))]
                  [may-be-non-list? (may-be-non-list-pattern? (rhs-pattern rhs) non-list-nt-table)]
                  [may-be-list? (may-be-list-pattern? (rhs-pattern rhs) list-nt-table)])
              (when may-be-non-list? (add-to-ht ht))
              (when may-be-list? (add-to-ht list-ht))
              (unless (or may-be-non-list? may-be-list?)
                (error 'compile-language 
                       "internal error: unable to determine whether pattern matches lists, non-lists, or both: ~s"
                       (rhs-pattern rhs))))))
        (nt-rhs nt)))
     lang))
  
  (do-compilation clang-ht clang-list-ht lang #t)
  (do-compilation across-ht across-list-ht compatible-context-language #f)
  clang)

;; left-recursive-non-terminals: 
;; (listof nt) (listof nt) -> (values (hash/c symbol boolean) (hash/c symbol boolean))
(define (left-recursive-non-terminals nts cross-nts)
  (define nt-names (map nt-name nts))
  
  (define generates-hole (make-hash))
  (define directly-reachable (make-hash))
  (define changed? #f)
  
  (define (process-nt nt cross?)
    (define key (list (nt-name nt) cross?))
    (define gen-hole?
      (for/fold ([any? #f]) ([r (nt-rhs nt)])
                (define this? (process-pat (rhs-pattern r) key))
                (or any? this?)))
    (hash-update! generates-hole key
                  (λ (already?)
                    (when (and gen-hole? (not already?))
                      (set! changed? #t))
                    gen-hole?)
                  #f))
  
  (define (process-pat pat within-key)
    (match pat
      [`hole #t]
      [(? symbol? (app symbol->string s))
       (match (regexp-match #rx"^([^_]*)" s)
         [(list _ (app string->symbol before-underscore))
          (if (member before-underscore nt-names)
              (reach-nt within-key (list before-underscore #f))
              #f)])]
      [`(name ,_ ,p)
       (process-pat p within-key)]
      [`(in-hole ,p ,q)
       (if (process-pat p within-key)
           (process-pat q within-key)
           #f)]
      [`(hide-hole ,p)
       (process-pat p within-key)
       #f]
      [`(side-condition ,p ,_ ,_)
       (process-pat p within-key)]
      [`(cross ,(? symbol? s))
       (reach-nt within-key (list (cross-name s (not (second within-key))) #t))]
      [_ #f]))
  
  (define (reach-nt src dst)
    (hash-update! directly-reachable src
                  (λ (prev-reachable)
                    (define dst-reachable
                      (hash-ref directly-reachable dst (set)))
                    (define now-reachable 
                      (set-add (set-union prev-reachable dst-reachable) dst))
                    (unless (equal? prev-reachable now-reachable)
                      (set! changed? #t))
                    now-reachable)
                  (set))
    (hash-ref generates-hole dst #f))
  
  (let loop ()
    (for ([n nts]) (process-nt n #f))
    (for ([n cross-nts]) (process-nt n #t))
    (when changed?
      (set! changed? #f)
      (loop)))
  
  (for/fold ([lr (set)] [lrc (set)])
            ([(nt reachable) directly-reachable])
            (if (set-member? reachable nt)
                (match-let ([(list name cross?) nt])
                  (if cross?
                      (values lr (set-add lrc name))
                      (values (set-add lr name) lrc)))
                (values lr lrc))))

;; cross-name: symbol boolean -> symbol
(define (cross-name name prefix?)
  (if prefix?
      (symbol-append name '- name)
      name))

;; extract-literals : (listof nt) -> (listof symbol)
(define (extract-literals nts)
  (let ([literals-ht (make-hasheq)]
        [nt-names (map nt-name nts)])
    (for-each (λ (nt) 
                (for-each (λ (rhs) (extract-literals/pat nt-names (rhs-pattern rhs) literals-ht))
                          (nt-rhs nt)))
              nts)
    (hash-map literals-ht (λ (x y) x))))

;; extract-literals/pat : (listof sym) pattern ht -> void
;; inserts the literals mentioned in pat into ht
(define (extract-literals/pat nts pat ht)
  (let loop ([pat pat])
    (match pat
      [`any (void)]
      [`number (void)]
      [`string (void)]
      [`natural (void)]
      [`integer (void)]
      [`real (void)]
      [`variable (void)]
      [`(variable-except ,s ...) (void)]
      [`(variable-prefix ,s) (void)]
      [`variable-not-otherwise-mentioned (void)]
      [`hole (void)]
      [(? symbol? s) 
       (unless (regexp-match #rx"_" (symbol->string s))
         (unless (regexp-match #rx"^\\.\\.\\." (symbol->string s))
           (unless (memq s nts)
             (hash-set! ht s #t))))]
      [`(name ,name ,pat) (loop pat)]
      [`(in-hole ,p1 ,p2) 
       (loop p1)
       (loop p2)]
      [`(hide-hole ,p) (loop p)]
      [`(side-condition ,p ,g ,e)
       (loop p)]
      [`(cross ,s) (void)]
      [_
       (let l-loop ([l-pat pat])
         (when (pair? l-pat) 
           (loop (car l-pat))
           (l-loop (cdr l-pat))))])))

;; build-nt-property : lang (pattern[not-non-terminal] (pattern -> boolean) -> boolean) boolean
;;                  -> hash[symbol[nt] -> boolean]
(define (build-nt-property lang test-rhs conservative-answer combine-rhss)
  (let ([ht (make-hasheq)]
        [rhs-ht (make-hasheq)])
    (for-each
     (lambda (nt)
       (hash-set! rhs-ht (nt-name nt) (nt-rhs nt))
       (hash-set! ht (nt-name nt) 'unknown))
     lang)
    (let ()
      (define (check-nt nt-sym)
        (let ([current (hash-ref ht nt-sym)])
          (case current
            [(unknown)
             (hash-set! ht nt-sym 'computing)
             (let ([answer (combine-rhss 
                            (map (lambda (x) (check-rhs (rhs-pattern x)))
                                 (hash-ref rhs-ht nt-sym)))])
               (hash-set! ht nt-sym answer)
               answer)]
            [(computing) conservative-answer]
            [else current])))
      (define (check-rhs rhs)
        (cond
          [(hash-maps? ht rhs)
           (check-nt rhs)]
          [else (test-rhs rhs check-rhs)]))
      (for-each (lambda (nt) (check-nt (nt-name nt)))
                lang)
      ht)))

;; build-compatible-context-language : lang -> lang
(define (build-compatible-context-language clang-ht lang)
  (remove-empty-compatible-contexts
   (apply
    append
    (map 
     (lambda (nt1)
       (map
        (lambda (nt2)
          (let ([compat-nt (build-compatible-contexts/nt clang-ht (nt-name nt1) nt2)])
            (if (eq? (nt-name nt1) (nt-name nt2))
                (make-nt (nt-name compat-nt)
                         (cons
                          (make-rhs 'hole)
                          (nt-rhs compat-nt)))
                compat-nt)))
        lang))
     lang))))

;; remove-empty-compatible-contexts : lang -> lang
;; Removes the empty compatible context non-terminals and the 
;; rhss that reference them.
(define (remove-empty-compatible-contexts lang)
  (define (has-cross? pattern crosses)
    (match pattern
      [`(cross ,(? symbol? nt)) (memq nt crosses)]
      [(list-rest p '... rest) (has-cross? rest crosses)]
      [(cons first rest) (or (has-cross? first crosses)
                             (has-cross? rest crosses))]
      [_ #f]))
  (define (delete-empty nts)
    (for/fold ([deleted null] [kept null]) ([nt nts])
      (if (null? (nt-rhs nt))
          (values (cons nt deleted) kept)
          (values deleted (cons nt kept)))))
  (define (delete-references deleted-names remaining-nts)
    (map (λ (nt) 
           (make-nt (nt-name nt)
                    (filter (λ (rhs) (not (has-cross? (rhs-pattern rhs) deleted-names))) 
                            (nt-rhs nt))))
         remaining-nts))
  
  (let loop ([nts lang])
    (let-values ([(deleted kept) (delete-empty nts)])
      (if (null? deleted)
          kept
          (loop (delete-references (map nt-name deleted) kept))))))

;; build-compatible-contexts : clang-ht prefix nt -> nt
;; constructs the compatible closure evaluation context from nt.
(define (build-compatible-contexts/nt clang-ht prefix nt)
  (make-nt
   (symbol-append prefix '- (nt-name nt))
   (apply append
          (map
           (lambda (rhs)
             (let-values ([(maker count) (build-compatible-context-maker clang-ht
                                                                         (rhs-pattern rhs)
                                                                         prefix)])
               (let loop ([i count])
                 (cond
                   [(zero? i) null]
                   [else (let ([nts (build-across-nts (nt-name nt) count (- i 1))])
                           (cons (make-rhs (maker (box nts)))
                                 (loop (- i 1))))]))))
           (nt-rhs nt)))))

(define (symbol-append . args)
  (string->symbol (apply string-append (map symbol->string args))))

;; build-across-nts : symbol number number -> (listof pattern)
(define (build-across-nts nt count i)
  (let loop ([j count])
    (cond
      [(zero? j) null]
      [else
       (cons (= i (- j 1)) 
             (loop (- j 1)))])))

;; build-compatible-context-maker : symbol pattern -> (values ((box (listof pattern)) -> pattern) number)
;; when the result function is applied, it takes each element
;; of the of the boxed list and plugs them into the places where
;; the nt corresponding from this rhs appeared in the original pattern. 
;; The number result is the number of times that the nt appeared in the pattern.
(define (build-compatible-context-maker clang-ht pattern prefix)
  (let ([count 0])
    (define maker
     (let loop ([pattern pattern])
       (define (untouched-pattern _) 
         (values pattern #f))
       (match pattern
         [`any untouched-pattern]
         [`number untouched-pattern]
         [`string untouched-pattern]
         [`natural untouched-pattern]
         [`integer untouched-pattern]
         [`real untouched-pattern]
         [`variable untouched-pattern] 
         [`(variable-except ,vars ...) untouched-pattern]
         [`(variable-prefix ,var) untouched-pattern]
         [`variable-not-otherwise-mentioned untouched-pattern]
         [`hole untouched-pattern]
         [(? string?) untouched-pattern]
         [(? symbol?) 
          (cond
            [(hash-ref clang-ht pattern #f)
             (set! count (+ count 1))
             (lambda (l)
               (let ([fst (car (unbox l))])
                 (set-box! l (cdr (unbox l)))
                 (if fst
                     (values `(cross ,(symbol-append prefix '- pattern)) #t)
                     (values pattern #f))))]
            [else untouched-pattern])]
         [`(name ,name ,pat)
          (let ([patf (loop pat)])
            (lambda (l)
              (let-values ([(p h?) (patf l)])
                (values `(name ,name ,p) h?))))]
         [`(in-hole ,context ,contractum)
          (let ([match-context (loop context)]
                [match-contractum (loop contractum)])
            (lambda (l)
              (let-values ([(ctxt _) (match-context l)]
                           [(ctct h?) (match-contractum l)])
                (values `(in-hole ,ctxt ,ctct) h?))))]
         [`(hide-hole ,p)
          (let ([m (loop p)])
            (lambda (l)
              (let-values ([(p h?) (m l)])
                (if h?
                    (values p #t)
                    (values `(hide-hole ,p) #f)))))]
         [`(side-condition ,pat ,condition ,expr)
          (let ([patf (loop pat)])
            (lambda (l)
              (let-values ([(p h?) (patf l)])
                (values `(side-condition ,p ,condition ,expr) h?))))]
         [(? list?)
          (define pre-cross
            (let l-loop ([ps pattern])
              (match ps
                ['() '()]
                [(list-rest p '... ps*)
                 (cons (list (loop p) p) (l-loop ps*))]
                [(cons p ps*)
                 (cons (list (loop p) #f) (l-loop ps*))])))
          (λ (l)
            (define any-cross? #f)
            (define post-cross
              (map (match-lambda 
                     [(list f r?)
                      (let-values ([(p h?) (f l)])
                        (set! any-cross? (or any-cross? h?))
                        (list p h? r?))])
                   pre-cross))
            (define (hide p)
              (if any-cross? `(hide-hole ,p) p))
            (values
             (foldr (λ (post tail)
                      (match post
                        [(list p* #t (and (not #f) p))
                         `(,(hide p) ... ,p* ,(hide p) ... . ,tail)]
                        [(list p #f (not #f))
                         `(,(hide p) ... . ,tail)]
                        [(list p* #t #f)
                         `(,p* . ,tail)]
                        [(list p #f #f)
                         `(,(hide p) . ,tail)]))
                    '()
                    post-cross)
             any-cross?))]
         [else untouched-pattern])))
    (values (λ (l) (let-values ([(p _) (maker l)]) p))
            count)))

;; build-list-nt-label : lang -> hash[symbol -o> boolean]
(define (build-list-nt-label lang)
  (build-nt-property 
   lang
   (lambda (pattern recur)
     (may-be-list-pattern?/internal pattern
                                    (lambda (sym) #f)
                                    recur))
   #t
   (lambda (lst) (ormap values lst))))

(define (may-be-list-pattern? pattern list-nt-table)
  (let loop ([pattern pattern])
    (may-be-list-pattern?/internal
     pattern
     (lambda (sym) 
       (hash-ref list-nt-table (symbol->nt sym) #t))
     loop)))

(define (may-be-list-pattern?/internal pattern handle-symbol recur)
  (match pattern
    [`any #t]
    [`number #f]
    [`string #f]
    [`variable #f] 
    [`natural #f]
    [`integer #f]
    [`real #f]
    [`(variable-except ,vars ...) #f]
    [`variable-not-otherwise-mentioned #f]
    [`(variable-prefix ,var) #f]
    [`hole  #t]
    [(? string?) #f]
    [(? symbol?)
     (handle-symbol pattern)]
    [`(name ,name ,pat)
     (recur pat)]
    [`(in-hole ,context ,contractum)
     (recur context)]
    [`(hide-hole ,p)
     (recur p)]
    [`(side-condition ,pat ,condition ,expr)
     (recur pat)]
    [(? list?)
     #t]
    [else 
     ;; is this right?!
     (or (null? pattern) (pair? pattern))]))


;; build-non-list-nt-label : lang -> hash[symbol -o> boolean]
(define (build-non-list-nt-label lang)
  (build-nt-property 
   lang
   (lambda (pattern recur)
     (may-be-non-list-pattern?/internal pattern
                                        (lambda (sym) #t)
                                        recur))
   #t
   (lambda (lst) (ormap values lst))))

(define (may-be-non-list-pattern? pattern non-list-nt-table)
  (let loop ([pattern pattern])
    (may-be-non-list-pattern?/internal
     pattern
     (lambda (sym)
       (hash-ref non-list-nt-table (symbol->nt sym) #t))
     loop)))

(define (may-be-non-list-pattern?/internal pattern handle-sym recur)
  (match pattern
    [`any #t]
    [`number #t]
    [`string #t]
    [`variable #t]
    [`natural #t]
    [`integer #t]
    [`real #t]
    [`(variable-except ,vars ...) #t]
    [`variable-not-otherwise-mentioned #t]
    [`(variable-prefix ,prefix) #t]
    [`hole #t]
    [(? string?) #t]
    [(? symbol?) (handle-sym pattern)]
    [`(name ,name ,pat)
     (recur pat)]
    [`(in-hole ,context ,contractum)
     (recur context)]
    [`(hide-hole ,p)
     (recur p)]
    [`(side-condition ,pat ,condition ,expr)
     (recur pat)]
    [(? list?)
     #f]
    [else 
     ;; is this right?!
     (not (or (null? pattern) (pair? pattern)))]))

;; match-pattern : compiled-pattern exp -> (union #f (listof bindings))
(define (match-pattern compiled-pattern exp)
  (let ([results ((compiled-pattern-cp compiled-pattern) exp #f '())])
    (and results
         (let ([filtered (filter-multiples (non-decomps results))])
           (and (not (null? filtered))
                filtered)))))

;; filter-multiples : (listof mtch) -> (listof mtch)
(define (filter-multiples matches)
  (let loop ([matches matches]
             [acc null])
    (cond
      [(null? matches) acc]
      [else
       (let ([merged (merge-multiples/remove (car matches))])
         (if merged
             (loop (cdr matches) (cons merged acc))
             (loop (cdr matches) acc)))])))

;; merge-multiples/remove : bindings -> (union #f bindings)
;; returns #f if all duplicate bindings don't bind the same thing
;; returns a new bindings 
(define (merge-multiples/remove match)
  (let/ec fail
    (let (
          ;; match-ht : sym -o> sexp
          [match-ht (make-hash)]
          
          ;; mismatch-ht : sym -o> hash[sexp -o> #t]
          [mismatch-ht (make-hash)]
          
          [ribs (bindings-table (mtch-bindings match))])
      (for-each
       (lambda (rib)
         (cond
           [(bind? rib)
            (let ([name (bind-name rib)]
                  [exp (bind-exp rib)])
              (let ([previous-exp (hash-ref match-ht name uniq)])
                (cond
                  [(eq? previous-exp uniq)
                   (hash-set! match-ht name exp)]
                  [else
                   (unless (equal? exp previous-exp)
                     (fail #f))])))]
           [(mismatch-bind? rib)
            (let* ([name (mismatch-bind-name rib)]
                   [exp (mismatch-bind-exp rib)]
                   [priors (hash-ref mismatch-ht name uniq)])
              (when (eq? priors uniq)
                (let ([table (make-hash)])
                  (hash-set! mismatch-ht name table)
                  (set! priors table)))
              (when (hash-ref priors exp #f)
                (fail #f))
              (hash-set! priors exp #t))]))
       ribs)
      (mtch (make-bindings (hash-map match-ht make-bind))
            (mtch-matched match)))))

(require racket/pretty)

;; compile-pattern : compiled-lang pattern boolean -> compiled-pattern
(define (compile-pattern clang pattern bind-names?)
  (make-compiled-pattern (compile-pattern/cross? clang pattern #t bind-names?)))

;; name-to-key/binding : hash[symbol -o> key-wrap]
(define name-to-key/binding (make-hasheq))
(define-struct key-wrap (sym) #:inspector (make-inspector))

;; compile-pattern/cross? : compiled-lang pattern boolean boolean -> compiled-pattern
(define (compile-pattern/cross? clang pattern prefix-cross? bind-names?)
  (define clang-ht (compiled-lang-ht clang))
  (define clang-list-ht (compiled-lang-list-ht clang))
  (define across-ht (compiled-lang-across-ht clang))
  (define across-list-ht (compiled-lang-across-list-ht clang))
  
  (define (compile-pattern/default-cache pattern)
    (compile-pattern/cache pattern 
                           (if bind-names?
                               (compiled-lang-bind-names-cache clang)
                               (compiled-lang-cache clang))))
  
  (define (compile-pattern/cache pattern compiled-pattern-cache)
    (let ([compiled-cache (hash-ref compiled-pattern-cache pattern uniq)])
      (cond 
        [(eq? compiled-cache uniq)
         (let ([compiled-pattern
                (true-compile-pattern pattern)])
           (let ([memoized (memoize compiled-pattern)])
             (hash-set! compiled-pattern-cache pattern memoized)
             memoized))]
        [else
         compiled-cache])))
  
  (define (true-compile-pattern pattern)
    (match pattern
      [(? (lambda (x) (eq? x '....)))
       (error 'compile-language "the pattern .... can only be used in extend-language")]
      [`(variable-except ,vars ...)
       (lambda (exp memo active)
         (and (symbol? exp)
              (not (memq exp vars))
              (list (literal-match exp))))]
      [`(variable-prefix ,var)
       (let* ([prefix-str (symbol->string var)]
              [prefix-len (string-length prefix-str)])
         (lambda (exp memo active)
           (and (symbol? exp)
                (let ([str (symbol->string exp)])
                  (and ((string-length str) . >= . prefix-len)
                       (string=? (substring str 0 prefix-len) prefix-str)
                       (list (literal-match exp)))))))]
      [`hole match-hole]
      [(? string?)
       (lambda (exp memo active)
         (and (string? exp)
              (string=? exp pattern)
              (list (literal-match exp))))]
      [(? symbol?)
       (cond
         [(has-underscore? pattern)
          (let*-values ([(binder before-underscore)
                         (let ([before (split-underscore pattern)])
                           (values pattern before))]
                        [(match-raw-name)
                         (compile-id-pattern before-underscore)])
            (match-named-pat binder match-raw-name))]
         [else 
          (let ([match-raw-name (compile-id-pattern pattern)])
            (if (non-underscore-binder? pattern)
                (match-named-pat pattern match-raw-name)
                match-raw-name))])]
      [`(cross ,(? symbol? pre-id))
       (let ([id (cross-name pre-id prefix-cross?)])
         (cond
           [(hash-maps? across-ht id)
            (define (unwrapped exp memo active)
              (match-nt (hash-ref across-list-ht id) (hash-ref across-ht id) exp memo active))
            (if (set-member? (compiled-lang-across-left-rec-nts clang) id)
                (iterated-match unwrapped (list id #f))
                unwrapped)]
           [else
            (error 'compile-pattern "unknown cross reference ~a" id)]))]
      
      [`(name ,name ,pat)
       (let ([match-pat (compile-pattern/default-cache pat)])
         (match-named-pat name match-pat))]
      [`(in-hole ,context ,contractum) 
       (let ([match-context (compile-pattern/default-cache context)]
             [match-contractum (compile-pattern/default-cache contractum)])
         (match-in-hole match-context match-contractum))]
      [`(hide-hole ,p)
       (let ([match-pat (compile-pattern/default-cache p)])
         (lambda (exp memo active)
           (let ([matches (match-pat exp memo active)])
             (and matches
                  (non-decomps matches)))))]
      
      [`(side-condition ,pat ,condition ,expr)
       (let ([match-pat (compile-pattern/default-cache pat)])
         (lambda (exp memo active)
           (let ([matches (match-pat exp memo active)])
             (and matches
                  (let ([filtered (filter (λ (m) (condition (mtch-bindings m))) 
                                          (filter-multiples matches))])
                    (if (null? filtered)
                        #f
                        filtered))))))]
      [(? list?)
       (let ([rewritten (rewrite-ellipses non-underscore-binder? pattern compile-pattern/default-cache)])
         (let ([count (and (not (ormap repeat? rewritten))
                           (length rewritten))])
           (lambda (exp memo active)
             (define term
               (match exp
                 [(layer l c r) (append l (cons c r))]
                 [_ exp]))
             (cond
               [(list? term)
                ;; shortcircuit: if the list isn't the right length, give up immediately.
                (if (and count
                         (not (= (length term) count)))
                    #f
                    (match-list rewritten term))]
               [else #f]))))]
      
      ;; an already comiled pattern
      [(? compiled-pattern?)
       (compiled-pattern-cp pattern)]
      
      [else 
       (lambda (exp memo active)
         (and (equal? pattern exp)
              (list (literal-match exp))))]))
  
  (define (non-underscore-binder? pattern)
    (and bind-names?
         (or (hash-maps? clang-ht pattern)
             (memq pattern underscore-allowed))))
  
  ;; compile-id-pattern : symbol[with-out-underscore] -> compiled-pattern-proc
  (define (compile-id-pattern pat)
    (match pat
      [`any (simple-match (λ (x) #t))]
      [`number (simple-match number?)]
      [`string (simple-match string?)]
      [`variable (simple-match symbol?)]
      [`variable-not-otherwise-mentioned
       (let ([literals (compiled-lang-literals clang)])
         (simple-match
          (λ (exp)
            (and (symbol? exp) 
                 (not (memq exp literals))))))]
      [`natural (simple-match (λ (x) (and (integer? x) (exact? x) (not (negative? x)))))]
      [`integer (simple-match (λ (x) (and (integer? x) (exact? x))))]
      [`real (simple-match real?)]
      [(? is-non-terminal?)
       (define unwrapped
         (lambda (exp memo active)
           (match-nt (hash-ref clang-list-ht pat) (hash-ref clang-ht pat) exp memo active)))
       (if (set-member? (compiled-lang-left-rec-nts clang) pat)
           (iterated-match unwrapped (list pat #f))
           unwrapped)]
      [else
       (lambda (exp memo active) 
         (and (eq? exp pat)
              (list (literal-match exp))))]))
  
  (define (is-non-terminal? sym) (hash-maps? clang-ht sym))
  
  ;; simple-match : (any -> bool) -> compiled-pattern
  ;; does a match based on a built-in Scheme predicate
  (define (simple-match pred)
    (lambda (exp memo active) 
      (and (pred exp) 
           (list (literal-match exp)))))
  
  (compile-pattern/default-cache pattern))

;; match-named-pat : symbol <compiled-pattern> -> <compiled-pattern>
(define (match-named-pat name match-pat)
  (let ([mismatch-bind? (regexp-match #rx"_!_" (symbol->string name))])
    (lambda (exp memo active)
      (let ([matches (match-pat exp memo active)])
        (and matches 
             (map (λ (m)
                    (define named
                      (match (mtch-matched m)
                        [(decomp c t) c]
                        [(non-decomp) exp]))
                    (mtch (make-bindings 
                           (cons (if mismatch-bind?
                                     (make-mismatch-bind name named)
                                     (make-bind name named))
                                 (bindings-table (mtch-bindings m))))
                          (mtch-matched m)))
                  matches))))))

;; split-underscore : symbol -> symbol
;; returns the text before the underscore in a symbol (as a symbol)
;; raise an error if there is more than one underscore in the input
(define (split-underscore sym)
  (let ([str (symbol->string sym)])
    (cond
      [(regexp-match #rx"^([^_]*)_[^_]*$" str)
       =>
       (λ (m) (string->symbol (cadr m)))]
      [(regexp-match #rx"^([^_]*)_!_[^_]*$" str)
       =>
       (λ (m) (string->symbol (cadr m)))]
      [else
       (error 'compile-pattern "found a symbol with multiple underscores: ~s" sym)])))

;; has-underscore? : symbol -> boolean
(define (has-underscore? sym)
  (memq #\_ (string->list (symbol->string sym))))

;; symbol->nt : symbol -> symbol
;; strips the trailing underscore from a symbol, if one is there.
(define (symbol->nt sym)
  (cond
    [(has-underscore? sym)
     (split-underscore sym)]
    [else sym]))

(define cache-size 350)
(define (set-cache-size! cs) (set! cache-size cs))

(define (memoize match-term)
  (let ([ht (make-hash)]
        [entries 0])
    (lambda (term memo active)
      (cond
        [(or (not (caching-enabled?)) memo)
         (match-term term memo active)]
        [else
         (unless (< entries cache-size)
           (set! entries 0)
           (set! ht (make-hash)))
         (let ([ans (hash-ref ht term uniq)])
           (cond
             [(eq? ans uniq)
              (set! entries (+ entries 1))
              (let ([res (match-term term memo active)])
                (hash-set! ht term res)
                res)]
             [else
              ans]))]))))

;; match-hole : compiled-pattern
(define (match-hole exp memo active)
  (define decomp-match
    (mtch (make-bindings '())
          (decomp the-hole exp)))
  (if (hole? exp)
      (list decomp-match
            (mtch (make-bindings '()) (non-decomp)))
      (list decomp-match)))

;; match-in-hole : compiled-pattern compiled-pattern -> compiled-pattern
(define (match-in-hole match-context match-contractum)
  (lambda (exp memo active)
    (let ([context-matches (match-context exp memo active)])
      (and context-matches
           (for/fold ([matches '()]) ([context-match context-matches])
                     (match context-match
                       [(mtch _ (non-decomp))
                        matches]
                       [(mtch context-bindings (decomp context contractum-term))
                        (define-values (new-memo new-active)
                          (if (eq? contractum-term exp)
                              (values memo active)
                              (values #f '())))
                        (let ([contractum-matches (match-contractum contractum-term new-memo new-active)])
                          (if contractum-matches
                              (for/fold ([matches matches]) 
                                        ([contractum-match contractum-matches])
                                        (match contractum-match
                                          [(mtch contractum-bindings (non-decomp))
                                           (cons (mtch (append-bindings contractum-bindings context-bindings)
                                                       (non-decomp))
                                                 matches)]
                                          [(mtch contractum-bindings (decomp inner-context inner-term))
                                           (cons (mtch (append-bindings contractum-bindings context-bindings)
                                                       (decomp (append-contexts context inner-context)
                                                               inner-term))
                                                 matches)]))
                              matches))]))))))

(define append-contexts
  (match-lambda**
   [((? hole?) c) c]
   [((layer l c1 r) c2)
    (layer l (append-contexts c1 c2) r)]))

(define-struct (indexed-decomp decomp) (index))

;; match-list : (listof (union repeat compiled-pattern)) sexp -> (union #f (listof bindings))
(define (match-list patterns exp)
  (let (;; raw-match : (listof (listof (listof mtch)))
        [raw-match (match-list/raw patterns exp)])
    (and (not (null? raw-match))
         (let loop ([raw-match raw-match])
           (cond
             [(null? raw-match) '()]
             [else (append (combine-matches exp (car raw-match))
                           (loop (cdr raw-match)))])))))

;; match-list/raw : (listof (union repeat compiled-pattern)) 
;;                  sexp
;;               -> (listof (listof (listof mtch)))
;; the result is the raw accumulation of the matches for each subpattern, as follows:
;;  (listof (listof (listof mtch)))
;;  \       \       \-------------/  matches for one position in the list (failures don't show up)
;;   \       \-------------------/   one element for each position in the pattern list
;;    \-------------------------/    one element for different expansions of the ellipses
;; the failures to match are just removed from the outer list before this function finishes
;; via the `fail' argument to `loop'.
(define (match-list/raw patterns orig-term)
  (let/ec k
    (let loop ([patterns patterns]
               [exp orig-term]
               [list-pos 1]
               ;; fail : -> alpha
               ;; causes one possible expansion of ellipses to fail
               ;; initially there is only one possible expansion, so
               ;; everything fails.
               [fail (lambda () (k null))])
      (cond
        [(pair? patterns)
         (let ([fst-pat (car patterns)])
           (cond
             [(repeat? fst-pat)
              (if (or (null? exp) (pair? exp))
                  (let ([r-pat (repeat-pat fst-pat)]
                        [r-mt (mtch (make-bindings (repeat-empty-bindings fst-pat))
                                    (non-decomp))])
                    (apply 
                     append
                     (cons (let/ec k
                             (let ([mt-fail (lambda () (k null))])
                               (map (lambda (pat-ele) 
                                      (cons (add-ellipses-index (list r-mt) (repeat-suffix fst-pat) (repeat-mismatch? fst-pat) 0)
                                            pat-ele))
                                    (loop (cdr patterns) exp list-pos mt-fail))))
                           (let r-loop ([rest-exp exp]
                                        [past-matches (list r-mt)]
                                        [repeat-length 1]
                                        [list-pos list-pos])
                             (cond
                               [(pair? rest-exp)
                                (let ([m (r-pat (car rest-exp) #f '())])
                                  (if m
                                      (let* ([combined-matches (collapse-single-multiples list-pos m past-matches)]
                                             [reversed 
                                              (add-ellipses-index 
                                               (reverse-multiples combined-matches)
                                               (repeat-suffix fst-pat)
                                               (repeat-mismatch? fst-pat)
                                               repeat-length)])
                                        (cons 
                                         (let/ec fail-k
                                           (map (lambda (x) (cons reversed x))
                                                (loop (cdr patterns) 
                                                      (cdr rest-exp)
                                                      (+ list-pos 1)
                                                      (lambda () (fail-k null)))))
                                         (r-loop (cdr rest-exp)
                                                 combined-matches
                                                 (+ repeat-length 1)
                                                 (+ list-pos 1))))
                                      (list null)))]
                               ;; what about dotted pairs?
                               [else (list null)])))))
                  (fail))]
             [else
              (cond
                [(pair? exp)
                 (let* ([fst-exp (car exp)]
                        [matches (fst-pat fst-exp #f '())])
                   (if matches
                       (let ([indexed 
                              (for/list ([m matches])
                                (match m
                                  [(mtch _ (non-decomp)) m]
                                  [(mtch b (decomp c t))
                                   (mtch b (indexed-decomp c t list-pos))]))])
                         (map (lambda (x) (cons indexed x))
                              (loop (cdr patterns) (cdr exp) (+ list-pos 1) fail)))
                       (fail)))]
                [else
                 (fail)])]))]
        [else
         (if (null? exp)
             (list null)
             (fail))]))))

;; add-ellipses-index : (listof mtch) sym boolean number -> (listof mtch)
(define (add-ellipses-index mtchs key mismatch-bind? i)
  (if key
      (let ([rib (if mismatch-bind? 
                     (make-mismatch-bind key i)
                     (make-bind key i))])
        (map (λ (m)
               (mtch (make-bindings (cons rib (bindings-table (mtch-bindings m))))
                     (mtch-matched m)))
             mtchs))
      mtchs))

;; collapse-single-multiples : nat (listof mtch) (listof mtch[to-lists]) -> (listof mtch[to-lists])
(define (collapse-single-multiples single-index bindingss multiple-bindingss)
  (for*/fold ([matches null])
             ([single-match bindingss]
              [multiple-match multiple-bindingss])
             (match* (single-match multiple-match)
                     [((mtch _ (? decomp?)) (mtch _ (? decomp?)))
                      matches]
                     [((mtch b1 (decomp c t)) (mtch b2 (? non-decomp?)))
                      (cons (mtch (cons-bindings b1 b2)
                                  (indexed-decomp c t single-index))
                            matches)]
                     [((mtch b1 (? non-decomp?)) (mtch b2 (? indexed-decomp? d)))
                      (cons (mtch (cons-bindings b1 b2) d)
                            matches)]
                     [((mtch b1 (? non-decomp?)) (mtch b2 (? non-decomp?)))
                      (cons (mtch (cons-bindings b1 b2) (non-decomp))
                            matches)])))

(define (cons-bindings head-bindings tail-bindings)
  (make-bindings
   (map (match-lambda* 
          [`(,(struct bind (name sing-exp)) ,(struct bind (name mult-exp)))
           (make-bind name (cons sing-exp mult-exp))]
          [`(,(struct mismatch-bind (name sing-exp)) ,(struct mismatch-bind (name mult-exp)))
           (make-mismatch-bind name (cons sing-exp mult-exp))]
          [else 
           (error 'collapse-single-multiples
                  "internal error: expected matches' bindings in same order; got ~e ~e"
                  head-bindings
                  tail-bindings)])
        (bindings-table head-bindings)
        (bindings-table tail-bindings))))

;; reverse-multiples : (listof mtch[to-lists]) -> (listof mtch[to-lists])
;; reverses the rhs of each rib in the bindings
(define (reverse-multiples matches)
  (map (lambda (match)
         (let ([bindings (mtch-bindings match)])
           (make-mtch
            (make-bindings
             (map (lambda (rib)
                    (cond
                      [(bind? rib)
                       (make-bind (bind-name rib)
                                  (reverse (bind-exp rib)))]
                      [(mismatch-bind? rib)
                       (make-mismatch-bind (mismatch-bind-name rib)
                                           (reverse (mismatch-bind-exp rib)))]))
                  (bindings-table bindings)))
            (mtch-matched match))))
       matches))

(define ((iterated-match match-term nt-key) term memo active)
  (if memo
      (if (member nt-key active)
          (set-map (hash-ref (match-memo-table memo) nt-key (set)) values)
          (let ([matches (match-term term memo (cons nt-key active))])
            (hash-update! (match-memo-table memo)
                          nt-key
                          (λ (prev)
                            (define matches-set
                              (if matches (apply set matches) (set)))
                            (unless (equal? matches-set prev)
                              (set-box! (match-memo-changed memo) #t))
                            matches-set)
                          (set))
            matches))
      (let ([memo (match-memo (make-hash) (box #f))])
        (let loop ()
          (define matches (match-term term memo '()))
          (if (unbox (match-memo-changed memo))
              (begin
                (set-box! (match-memo-changed memo) #f)
                (loop))
              matches)))))

(define-struct match-memo (table changed) #:transparent)

;; match-nt : (listof compiled-rhs) 
;;            (listof compiled-rhs) 
;;            term 
;;            match-memo 
;;            (listof (list/c symbol boolean))
;;        -> (union #f (listof bindings))
(define (match-nt list-rhs non-list-rhs term memo active)
  (let loop ([rhss (if (or (null? term) (pair? term) (layer? term))
                       list-rhs
                       non-list-rhs)]
             [ht #f])
    (cond
      [(null? rhss) 
       (if ht
           (hash-map ht (λ (k v) k))
           #f)]
      [else
       (let ([mth (remove-bindings/filter ((car rhss) term memo active))])
         (cond
           [mth
            (let ([ht (or ht (make-hash))])
              (for-each (λ (x) (hash-set! ht x #t)) mth)
              (loop (cdr rhss) ht))]
           [else 
            (loop (cdr rhss) ht)]))])))

;; remove-bindings/filter : (union #f (listof mtch)) -> (union #f (listof mtch))
(define (remove-bindings/filter matches)
  (and matches
       (let ([filtered (filter-multiples matches)])
         (and (not (null? filtered))
              (map (λ (match) (mtch (make-bindings '()) (mtch-matched match)))
                   filtered)))))

;; rewrite-ellipses : (symbol -> boolean)
;;                    (listof pattern) 
;;                    (pattern -> compiled-pattern)
;;                 -> (listof (union repeat compiled-pattern))
;; moves the ellipses out of the list and produces repeat structures
(define (rewrite-ellipses non-underscore-binder? pattern compile)
  (let loop ([exp-eles pattern]
             [fst dummy])
    (cond
      [(null? exp-eles)
       (if (eq? fst dummy)
           empty
           (list (compile fst)))]
      [else
       (let ([exp-ele (car exp-eles)])
         (cond
           [(or (eq? '... exp-ele)
                (prefixed-with? "..._" exp-ele))
            (when (eq? fst dummy)
              (error 'match-pattern "bad ellipses placement: ~s" pattern))
            (let ([compiled (compile fst)]
                  [rest (loop (cdr exp-eles) dummy)])
              (let ([underscore-key (if (eq? exp-ele '...) #f exp-ele)]
                    [mismatch? (and (regexp-match #rx"_!_" (symbol->string exp-ele)) #t)])
                (cons (make-repeat compiled (extract-empty-bindings non-underscore-binder? fst) underscore-key mismatch?) 
                      rest)))]
           [(eq? fst dummy)
            (loop (cdr exp-eles) exp-ele)]
           [else
            (let ([compiled (compile fst)]
                  [rest (loop (cdr exp-eles) exp-ele)])
              (cons compiled rest))]))])))

(define (prefixed-with? prefix exp)
  (and (symbol? exp)
       (let* ([str (symbol->string exp)]
              [len (string-length str)])
         (and (len . >= . (string-length prefix))
              (string=? (substring str 0 (string-length prefix))
                        prefix)))))

(define dummy (box 0))

;; extract-empty-bindings : (symbol -> boolean) pattern -> (listof rib)
(define (extract-empty-bindings non-underscore-binder? pattern)
  (let loop ([pattern pattern]
             [ribs null])
    (match pattern
      [`(variable-except ,vars ...) ribs]
      [`(variable-prefix ,vars) ribs]
      [`variable-not-otherwise-mentioned ribs]
      
      [`hole ribs]
      [(? symbol?) 
       (cond
         [(regexp-match #rx"_!_" (symbol->string pattern))
          (cons (make-mismatch-bind pattern '()) ribs)]
         [(or (has-underscore? pattern)
              (non-underscore-binder? pattern))
          (cons (make-bind pattern '()) ribs)]
         [else ribs])]
      [`(name ,name ,pat) 
       (cons (if (regexp-match #rx"_!_" (symbol->string name))
                 (make-mismatch-bind name '())
                 (make-bind name '()))
             (loop pat ribs))]
      [`(in-hole ,context ,contractum) (loop contractum (loop context ribs))]
      [`(hide-hole ,p) (loop p ribs)]
      [`(side-condition ,pat ,test ,expr) (loop pat ribs)]
      [(? list?)
       (let ([rewritten (rewrite-ellipses non-underscore-binder? pattern (lambda (x) x))])
         (let i-loop ([r-exps rewritten]
                      [ribs ribs])
           (cond
             [(null? r-exps) ribs]
             [else (let ([r-exp (car r-exps)])
                     (cond
                       [(repeat? r-exp)
                        (append (if (repeat-suffix r-exp)
                                    (list ((if (repeat-mismatch? r-exp)
                                               make-mismatch-bind
                                               make-bind)
                                           (repeat-suffix r-exp)
                                           '()))
                                    null)
                                (repeat-empty-bindings r-exp)
                                (i-loop (cdr r-exps) ribs))]
                       [else
                        (loop (car r-exps) (i-loop (cdr r-exps) ribs))]))])))]
      [else ribs])))

;; combine-matches : term (listof (listof mtch)) -> (listof mtch)
;; input is the list of bindings corresonding to a piecewise match
;; of a list. produces all of the combinations of complete matches
(define (combine-matches matched-term matchess)
  (define ms
    (let loop ([matchess matchess])
      (cond
        [(null? matchess) combine-matches-base-case]
        [else (combine-pair (car matchess) (loop (cdr matchess)))])))
  (for/list ([m ms])
    (match m
      [(mtch _ (non-decomp)) m]
      [(mtch b (indexed-decomp c t i))
       (define-values (l r)
         (layer-sides
          (match matched-term
            [(layer l c r) (append l (cons c r))]
            [_ matched-term])
          i))
       (mtch b (decomp (layer l c r) t))])))

(define combine-matches-base-case 
  (list (mtch (make-bindings null)
              (non-decomp))))

(define (layer-sides ts i)
  (if (= i 1)
      (values null (cdr ts))
      (let-values ([(l r) (layer-sides (cdr ts) (- i 1))])
        (values (cons (car ts) l) r))))

;; combine-pair : (listof mtch) (listof mtch) -> (listof mtch)
(define (combine-pair fst snd)
  (for*/fold ([mtchs null]) ([mtch1 fst] [mtch2 snd])
             (match* (mtch1 mtch2) ; both match lists
                     [((mtch _ (? decomp?)) (mtch _ (? decomp?)))
                      mtchs]
                     [((mtch b1 (? decomp? d)) (mtch b2 (non-decomp)))
                      (cons (mtch (append-bindings b1 b2) d)
                            mtchs)]
                     [((mtch b1 (non-decomp)) (mtch b2 (? decomp? d)))
                      (cons (mtch (append-bindings b1 b2) d)
                            mtchs)]
                     [((mtch b1 (non-decomp)) (mtch b2 (non-decomp)))
                      (cons (mtch (append-bindings b1 b2) (non-decomp))
                            mtchs)])))

(define (append-bindings bs cs)
  (make-bindings (append (bindings-table bs) (bindings-table cs))))

(define (hash-maps? ht key)
  (not (eq? (hash-ref ht key uniq) uniq)))

(define-values (the-hole the-not-hole hole?)
  (let ()
    (define-struct hole () #:inspector #f)
    (define the-hole (make-hole))
    (define the-not-hole (make-hole))
    (values the-hole the-not-hole hole?)))

;; used in hash lookups to tell when something isn't in the table
(define uniq (gensym))

(provide/contract
 (match-pattern (compiled-pattern? any/c . -> . (or/c false/c (listof mtch?))))
 (compile-pattern (-> compiled-lang? any/c boolean?
                      compiled-pattern?))
 
 (set-cache-size! (-> (and/c integer? positive?) void?))
 (cache-size (and/c integer? positive?))
 
 (make-bindings ((listof bind?) . -> . bindings?))
 (bindings-table (bindings? . -> . (listof bind?)))
 (bindings? (any/c . -> . boolean?))
 
 (mtch? (any/c . -> . boolean?))
 (make-mtch (bindings? non-decomp? . -> . mtch?))
 (mtch-bindings (mtch? . -> . bindings?))
 (mtch-matched (mtch? . -> . non-decomp?))
 (non-decomp (-> non-decomp?))
 
 (make-bind (symbol? any/c . -> . bind?))
 (bind? (any/c . -> . boolean?))
 (bind-name (bind? . -> . symbol?))
 (bind-exp (bind? . -> . any/c))
 (compile-language (-> any/c (listof nt?) (listof (listof symbol?)) compiled-lang?))
 (symbol->nt (symbol? . -> . symbol?))
 (has-underscore? (symbol? . -> . boolean?))
 (split-underscore (symbol? . -> . symbol?)))
(provide compiled-pattern?)

;; for test suite
(provide extract-empty-bindings
         (rename-out [bindings-table bindings-table-unchecked])
         (struct-out mismatch-bind)
         (struct-out compiled-pattern))

(provide (struct-out nt)
         (struct-out rhs)
         (struct-out compiled-lang)
         (struct-out layer)
         context?
         
         lookup-binding
         
         compiled-pattern
         
         none? none
         
         make-repeat
         the-not-hole the-hole hole?
         rewrite-ellipses
         build-compatible-context-language
         caching-enabled?)
