#lang scribble/manual

@(require "common.rkt")

@declare-exporting[plot]

@title[#:tag "renderer3d"]{3D Renderers}

@defproc[(renderer3d? [value any/c]) boolean?]{
Returns @racket[#t] if @racket[value] is a 3D @tech{renderer}; that is, if @racket[plot3d] can plot @racket[value].
The following functions create such renderers.
}

@section{3D Renderer Function Arguments}

As with functions that return 2D renderers, functions that return 3D renderers always have these kinds of arguments:
@itemlist[
          @item{Required (and possibly optional) arguments representing the graph to plot.}
          @item{Optional keyword arguments for overriding calculated bounds, with the default value @(racket #f).}
          @item{Optional keyword arguments that determine the appearance of the plot.}
          @item{The optional keyword argument @(racket #:label), which specifies the name of the renderer in the legend.}]

See @secref["renderer2d-function-arguments"] for a detailed example.

@section{3D Point Renderers}

@doc-apply[points3d]{
Returns a renderer that draws points in 3D space.

For example, a scatter plot of points sampled uniformly from the surface of a sphere:
@interaction[#:eval plot-eval
                    (let ()
                      (define (runif) (- (* 2 (random)) 1))
                      (define (rnormish) (+ (runif) (runif) (runif) (runif)))
                      
                      (define xs0 (build-list 1000 (λ _ (rnormish))))
                      (define ys0 (build-list 1000 (λ _ (rnormish))))
                      (define zs0 (build-list 1000 (λ _ (rnormish))))
                      (define mags (map (λ (x y z) (sqrt (+ (sqr x) (sqr y) (sqr z))))
                                        xs0 ys0 zs0))
                      (define xs (map / xs0 mags))
                      (define ys (map / ys0 mags))
                      (define zs (map / zs0 mags))
                      
                      (plot3d (points3d (map vector xs ys zs) #:sym 'dot)
                              #:altitude 25))]
}

@section{3D Line Renderers}

@doc-apply[lines3d]{
Returns a renderer that draws connected lines, with points in 3D space.
}

@doc-apply[parametric3d]{
Returns a renderer that plots a vector-valued function of time. For example,
@interaction[#:eval plot-eval
                    (plot3d (parametric3d (λ (t)
                                            (vector (* (cos (* 80 t)) (cos t))
                                                    (* (sin (* 80 t)) (cos t))
                                                    (sin t)))
                                          (- pi) pi
                                          #:samples 3000 #:alpha 0.5)
                            #:altitude 25)]
}

@section{3D Surface Renderers}

@doc-apply[surface3d]{
Returns a renderer that plots a two-input, one-output function. For example,
@interaction[#:eval plot-eval (plot3d (list (surface3d (λ (x y) (+ (sqr x) (sqr y))) -1 1 -1 1
                                                       #:label "z = x^2 + y^2")
                                            (surface3d (λ (x y) (- (+ (sqr x) (sqr y)))) -1 1 -1 1
                                                       #:color 4 #:line-color 4
                                                       #:label "z = -x^2 - y^2")))]
}

@doc-apply[polar3d]{
Returns a renderer that plots a function from latitude and longitude to radius.

Currently, latitudes range from @(racket 0) to @(racket (* 2 pi)), and longitudes from @(racket (* -1/2 pi)) to @(racket (* 1/2 pi)).

A sphere is the graph of a polar function of constant radius:
@interaction[#:eval plot-eval (plot3d (polar3d (λ (θ ρ) 1)) #:altitude 25)]

Combining polar function renderers allows faking latitudes or longitudes in larger ranges, to get, for example, a seashell plot:
@interaction[#:eval plot-eval
                    (let ()
                      (define (f1 θ ρ) (+ 1 (/ θ 2 pi) (* 1/8 (sin (* 8 ρ)))))
                      (define (f2 θ ρ) (+ 0 (/ θ 2 pi) (* 1/8 (sin (* 8 ρ)))))
                      
                      (plot3d (list (polar3d f1 #:color "navajowhite"
                                             #:line-style 'transparent #:alpha 2/3)
                                    (polar3d f2 #:color "navajowhite"
                                             #:line-style 'transparent #:alpha 2/3))
                              #:title "A Seashell" #:x-label #f #:y-label #f))]
}

@section{3D Contour Renderers}

@doc-apply[contours3d]{
Returns a renderer that plots contour lines on the surface of a function.

The appearance keyword arguments are interpreted identically to the appearance keyword arguments to @(racket contours).
In particular, when @(racket levels) is @(racket 'auto), contour values correspond precisely to @italic{z} axis ticks.

For example,
@interaction[#:eval plot-eval (plot3d (contours3d (λ (x y) (+ (sqr x) (sqr y))) -1.1 1.1 -1.1 1.1
                                                  #:label "z = x^2 + y^2")
                                      #:legend-anchor 'top-left)]
}

@doc-apply[contour-intervals3d]{
Returns a renderer that plots contour intervals and contour lines on the surface of a function.
The appearance keyword arguments are interpreted identically to the appearance keyword arguments to @(racket contour-intervals).

For example,
@interaction[#:eval plot-eval (plot3d (contour-intervals3d (λ (x y) (+ (sqr x) (sqr y)))
                                                           -1.1 1.1 -1.1 1.1
                                                           #:label "z = x^2 + y^2")
                                      #:legend-anchor 'top-left)]
}

@section{3D Isosurface Renderers}

@doc-apply[isosurface3d]{
Returns a renderer that plots the surface of constant output value of the function @(racket f). The argument @(racket d) is the constant value.

For example, a sphere is all the points in which the Euclidean distance function returns the sphere's radius:                                                           
@interaction[#:eval plot-eval (plot3d (isosurface3d
                                       (λ (x y z) (sqrt (+ (sqr x) (sqr y) (sqr z)))) 1
                                       -1 1 -1 1 -1 1)
                                      #:altitude 25)]
}

@doc-apply[isosurfaces3d]{
Returns a renderer that plots multiple isosurfaces. The appearance keyword arguments are interpreted similarly to those of @(racket contours).

Use this to visualize functions from three inputs to one output; for example:
@interaction[#:eval plot-eval (let ()
                                (define (saddle x y z) (- (sqr x) (* 1/2 (+ (sqr y) (sqr z)))))
                                (plot3d (isosurfaces3d saddle #:d-min -1 #:d-max 1 #:label "")
                                        #:x-min -2 #:x-max 2
                                        #:y-min -2 #:y-max 2
                                        #:z-min -2 #:z-max 2
                                        #:legend-anchor 'top-left))]

If it helps, think of the output of @(racket f) as a density or charge.
}

@section{3D Rectangle Renderers}

@doc-apply[rectangles3d]{
Returns a renderer that draws rectangles.

This can be used to draw histograms; for example,
@interaction[#:eval plot-eval
                    (let ()
                      (define (norm2 x y) (exp (* -1/2 (+ (sqr (- x 5)) (sqr y)))))
                      (define x-ivls (bounds->intervals (linear-seq 2 8 10)))
                      (define y-ivls (bounds->intervals (linear-seq -5 5 10)))
                      (define x-mids (linear-seq 2 8 9 #:start? #f #:end? #f))
                      (define y-mids (linear-seq -5 5 9 #:start? #f #:end? #f))
                      (plot3d (rectangles3d (append*
                                             (for/list ([y-ivl  (in-list y-ivls)]
                                                        [y  (in-list y-mids)])
                                               (for/list ([x-ivl  (in-list x-ivls)]
                                                          [x  (in-list x-mids)])
                                                 (define z (norm2 x y))
                                                 (vector x-ivl y-ivl (ivl 0 z)))))
                                            #:alpha 3/4
                                            #:label "Appx. 2D Normal")))]
}

@doc-apply[discrete-histogram3d]{
Returns a renderer that draws discrete histograms on a two-valued domain.

Missing pairs are not drawn; for example,
@interaction[#:eval plot-eval
                    (plot3d (discrete-histogram3d '(#(a a 1) #(a b 2) #(b b 3))
                                                  #:label "Missing (b,a)"
                                                  #:color 4 #:line-color 4))]
}
