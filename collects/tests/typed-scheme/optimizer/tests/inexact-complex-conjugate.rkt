#;
(
inexact-complex-conjugate.rkt line 15 col 14 - 1.0+2.0i - unboxed literal
inexact-complex-conjugate.rkt line 15 col 4 - conjugate - unboxed unary inexact complex
inexact-complex-conjugate.rkt line 15 col 35 - 2.0+4.0i - unboxed literal
inexact-complex-conjugate.rkt line 15 col 25 - conjugate - unboxed unary inexact complex
inexact-complex-conjugate.rkt line 15 col 1 - + - unboxed binary inexact complex
inexact-complex-conjugate.rkt line 15 col 0 - (#%app + (#%app conjugate (quote 1.0+2.0i)) (#%app conjugate (quote 2.0+4.0i))) - unboxed inexact complex
3.0-6.0i
)

#lang typed/scheme
#:optimize
(require racket/unsafe/ops)
(+ (conjugate 1.0+2.0i) (conjugate 2.0+4.0i))