#lang at-exp racket/base
(require racket/function
         racket/match
         racket/list)

(struct bibdb (raw bibs))

(define (bibtex-parse ip)
  (define STRING-DB (make-hash))
  (define ENTRY-DB (make-hash))
  
  (define (read-while pred ip)
    (list->string
     (let loop ()
       (match (peek-char ip)
         [(? pred)
          (cons (read-char ip)
                (loop))]
         [_
          empty]))))
  
  (define (read-until pred ip)
    (read-while (negate pred) ip))
  
  (define (slurp-whitespace ip)
    (read-while (λ (c) (and (char? c) (char-whitespace? c))) ip))
  
  (define (read-entries ip)
    (slurp-whitespace ip)
    (match (read-char ip)
      [#\%
       (read-line ip)
       (read-entries ip)]
      [#\@
       (read-entry ip)
       (read-entries ip)]
      [(? eof-object?)
       (void)]
      [c
       (error 'read-entries "Expected % or @, got ~v" c)]))
  
  (define (read-entry ip)
    (match (read-until (λ (c) (char=? c #\{)) ip)
      [(app string-downcase "string")
       (slurp-whitespace ip)
       (read-char ip)
       (define tag (read-tag ip))
       (slurp-whitespace ip)
       (match (read-char ip)
         [#\=
          (slurp-whitespace ip)
          (define string (read-value ip))
          (slurp-whitespace ip)
          (match (read-char ip)
            [#\}
             (hash-set! STRING-DB tag string)]
            [c
             (error 'read-entry "Parsing string, expected }, got ~v" c)])]
         [c
          (error 'read-entry "Parsing string, expected =, got ~v" c)])]
      [(app string-downcase "comment")
       (read-char ip)
       (let loop ()
         (read-until (λ (c) (or (char=? c #\{) (char=? c #\}))) ip)
         (match (read-char ip)
           [#\{
            (loop) (loop)]
           [#\}
            (void)]))]
      [typ
       (read-char ip)
       (slurp-whitespace ip)
       (define label (read-until (λ (c) (char=? c #\,)) ip))
       (read-char ip)
       (define alist
         (let loop ()
           (slurp-whitespace ip)
           (define atag (read-tag ip))
           (slurp-whitespace ip)
           (match (read-char ip)
             [#\=
              (slurp-whitespace ip)
              (define aval (read-value ip))
              (match (read-char ip)
                [#\,
                 (hash-set (loop) atag aval)]
                [#\}
                 (hash atag aval)]
                [c
                 (error 'read-entry "Parsing entry, expected , or }, got ~v" c)])]
             [c
              (error 'read-entry "Parsing entry, expected =, got ~v" c)])))
       (hash-set! ENTRY-DB label
                  (hash-set alist 'type typ))]))
  
  (define (read-tag ip)
    (slurp-whitespace ip)
    (string-downcase (read-until char-whitespace? ip)))
  
  (define (read-value ip)
    (slurp-whitespace ip)
    (match (peek-char ip)
      [#\{
       (read-char ip)
       (let loop ()
         (define first-part (read-until (λ (c) (or (char=? c #\{) (char=? c #\})))
                                        ip))
         (match (peek-char ip)
           [#\{
            (string-append first-part (read-value ip) (loop))]
           [#\}
            (read-char ip)
            first-part]))]
      [(? char-numeric?)
       (read-while char-numeric? ip)]
      [(? char-alphabetic?)
       (define string-tag (read-until (λ (c) (char=? c #\,)) ip))
       (hash-ref STRING-DB string-tag
                 (λ () string-tag))]
      [c
       (error 'read-value "Parsing value, expected {, got ~v" c)]))
  
  (read-entries ip)
  
  (bibdb ENTRY-DB (make-hash)))

(define (path->bibdb pth)
  (define bibdb
    (with-input-from-file
        pth
      (λ ()
        (bibtex-parse (current-input-port)))))
  bibdb)

(require scriblib/autobib
         scribble/manual)

(define-syntax-rule
  (define-bibtex-cite bib-pth
    ~cite-id citet-id generate-bibliography-id)
  (begin
    (define bibtex-db (path->bibdb bib-pth))
    (define-cite autobib-cite autobib-citet generate-bibliography-id)
    (define ((make-citer citer) f . r)
      (apply citer (map (curry generate-bib bibtex-db) 
                        (append-map (curry regexp-split #rx" +")
                                    (cons f r)))))
    (define ~cite-id (make-citer autobib-cite))
    (define citet-id (make-citer autobib-citet))))

(define (parse-author as)
  (apply authors
         (for/list ([a (in-list (regexp-split #rx" *and *" as))])
           (match (regexp-split #rx" +" a)
             [(list one) (org-author-name one)]
             [(list one two) (author-name one two)]
             [(list-rest first rest) (author-name first (apply string-append (add-between rest " ")))]))))
(define (parse-pages ps)
  (match ps
    [(regexp #rx"^([0-9]+)\\-+([0-9]+)$" (list _ f l))
     (list f l)]
    [#f
     #f]
    [_
     (error 'parse-pages "Invalid page format ~e" ps)]))

(define (generate-bib db key)
  (match-define (bibdb raw bibs) db)
  (hash-ref! bibs key
             (λ ()
               (define the-raw (hash-ref raw key (λ () (error 'bibtex "Unknown citation ~e" key))))
               (define (raw-attr a [def #f])
                 (hash-ref the-raw a def))
               (match (raw-attr 'type)
                 ["misc"
                  (make-bib #:title (raw-attr "title")
                            #:author (parse-author (raw-attr "author"))
                            #:date (raw-attr "year")
                            #:url (raw-attr "url"))]
                 ["book"
                  (make-bib #:title (raw-attr "title")
                            #:author (parse-author (raw-attr "author"))
                            #:date (raw-attr "year")
                            #:is-book? #t
                            #:url (raw-attr "url"))]
                 ["article"
                  (make-bib #:title (raw-attr "title")
                            #:author (parse-author (raw-attr "author"))
                            #:date (raw-attr "year")
                            #:location (journal-location (raw-attr "journal")
                                                         #:pages (parse-pages (raw-attr "pages"))
                                                         #:number (raw-attr "number")
                                                         #:volume (raw-attr "volume"))
                            #:url (raw-attr "url"))]
                 ["inproceedings"
                  (make-bib #:title (raw-attr "title")
                            #:author (parse-author (raw-attr "author"))
                            #:date (raw-attr "year")
                            #:location (proceedings-location (raw-attr "booktitle"))
                            #:url (raw-attr "url"))]
                 ["webpage"
                  (make-bib #:title (raw-attr "title")
                            #:author (parse-author (raw-attr "author"))
                            #:date (raw-attr "year")
                            #:url (raw-attr "url"))]
                 ["techreport"
                  (make-bib #:title (raw-attr "title")
                            #:author (parse-author (raw-attr "author"))
                            #:date (raw-attr "year")
                            #:location 
                            (match* ((raw-attr "institution") (raw-attr "number"))
                                    [(#f #f) @elem{}]
                                    [(l #f) @elem{@|l|}]
                                    [(#f n) @elem{@|n|}]
                                    [(l n) @elem{@|l|, @|n|}])
                            #:url (raw-attr "url"))]
                 [_
                  (make-bib #:title (format "~v" the-raw))]))))

(provide define-bibtex-cite)
