#;
(
vector-ref.rkt line 10 col 1 - vector-ref - vector
1
)

#lang typed/scheme
#:optimize
(require racket/unsafe/ops)
(vector-ref (ann (vector 1 2) (Vector Integer Integer)) 0)