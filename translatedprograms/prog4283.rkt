;;#lang racket

(module prog-4283 racket
  ;;(require (submod ".." lib))
  (provide
   (contract-out
    [buildAverage (expr/c expr/c . -> . Average)]
    [buildCosine (expr/c . -> . Cosine)]
    [buildSine (expr/c . -> . Sine)]
    [buildThresh (expr/c expr/c expr/c expr/c . -> . Thresh)]
    [buildTimes (expr/c expr/c . -> . Times)]
    [buildX (void . -> . VarX)]
    [buildY (void . -> . VarY)]
    [build ((parametric->/c (a b) (a b . -> . (or/c a b))) integer? . -> . (or/c VarX VarY))]))

  

   ;; Translate each ocaml variant into a struct. Field names are arbitary
  (struct VarX ())
  (struct VarY ())
  (struct Sine (e1))
  (struct Cosine (e1))
  (struct Average (e1 e2))
  (struct Times (e1 e2))
  (struct Thresh (e1 e2 e3 e4))
    
  ;; Define contract corresponding to ocaml type
  (define expr/c
    (flat-murec-contract ([varx/c (struct/c VarX)]
                         [vary/c (struct/c VarY)]
                         [sine/c (struct/c Sine expr/c)]
                         [cosine/c (struct/c Cosine expr/c)]
                         [average/c (struct/c Average expr/c expr/c)]
                         [times/c (struct/c Times expr/c expr/c)]
                         [thresh/c (struct/c Thresh expr/c expr/c expr/c expr/c)]
                         [expr/c (or/c varx/c vary/c sine/c cosine/c average/c times/c thresh/c)])
                         expr/c))

  (define (buildAverage e1 e2) (Average e1 e2))

  (define (buildCosine e) (Cosine e))

  (define (buildSine e) (Sine e))

  (define (buildThresh e1 e2 e3 e4) (Thresh e1 e2 e3 e4))

  (define (buildTimes e1 e2) (Times e1 e2))

  (define (buildX void) (VarX))

  (define (buildY void) (VarY))

  (define (build rand depth)
    (let ([temp (rand 0 4)])
    (letrec ([buildhelper (lambda (num depth expr)
                            (cond
                              [(= num 0)
                               (cond
                                 [(= (rand 0 1) 0) (buildX void)]
                                 [else (buildY void)])]
                              [(= num 1)
                               (cond
                                 [(= (rand 0 1) 0) (buildSine (buildhelper 0 (- depth 1) expr))]
                                 [else (buildCosine (buildhelper 0 (- depth 1) expr))])]
                              [(= num 2)
                               (cond
                                 [(= (rand 0 1) 0) (buildAverage (buildhelper (- num 1) (- depth 1) expr) (buildhelper (- num 1) (- depth 1) expr))]
                                 [else (buildTimes (buildhelper (- num 1) (- depth 1) expr) (buildhelper (- num 1) (- depth 1) expr))])]
                              [(= num 3) (buildhelper (- num 1) depth expr)]
                              [(= num 4) (buildThresh (buildhelper (- num 2) (- depth 1) expr) (buildhelper (- num 1) (- depth 1) expr) (buildhelper (- num 1) (- depth 1) expr) (buildhelper (- num 1) (- depth 1) expr))]))])
      (buildhelper temp depth ""))))
                               

  
)