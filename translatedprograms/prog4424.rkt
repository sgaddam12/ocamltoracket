;;#lang soft-contract

;; Opaque library providing function signatures (w/o implementation)

(module prog-4424 racket
  ;;(require (submod ".." lib))

  (provide
   (contract-out
    [eval (expr/c number? number? . -> . number?)]
    [ffor (number? number? (number? . -> . number?) . -> . void?)]
    [toIntensity (integer? . -> . real?)]
    [toReal (integer? integer? . -> . real?)]
    [build ((parametric->/c (a b) (a b . -> . (or/c a b))) integer? . -> . string?)]
    [eval_fn (expr/c number? number? . -> . (or/c number? exn?))]))
  
  ;; Translate each ocaml variant into a struct. Field names are arbitary
  
  (struct VarX () #:transparent)
  (struct VarY () #:transparent)
  (struct Sine (e1) #:transparent)
  (struct Cosine (e1) #:transparent)
  (struct Average (e1 e2) #:transparent)
  (struct Times (e1 e2) #:transparent)
  (struct Thresh (e1 e2 e3 e4) #:transparent)
    
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


    (define (eval e x y)
      (match e
        [(VarX) x]
        [(VarY) y]
        [(Sine e1)
         (sin (* pi (eval e1 x y)))]
        [(Cosine e1)
         (cos (* pi (eval e1 x y)))]
        [(Average e1 e2)
         (/ (+ (eval e1 x y) (eval e2 x y)) 2.0)]
        [(Times e1 e2)
         (* (eval e1 x y) (eval e2 x y))]
        [(Thresh e1 e2 e3 e4)
         (cond
           [(< (eval e1 x y) (eval e2 x y)) (eval e3 x y)]
           [else (eval e4 x y)])]
        [_ raise-contract-error]
        )
      )

  (define (ffor low high f)
    (cond
      [(> low high) void]
      [else (let ([temp (f low)]) (ffor (+ low 1) high f))]))

  (define (toIntensity z)
    (+ 127.5 (* 127.5 z)))

  (define (toReal i n)
    (/ i n))

  (define ^ string-append)
  
  (define (build rand depth)
    (let ([temp (rand 0 4)])
  (letrec ([buildhelper (lambda (num depth expr)
              (cond
                [(= num 0)
                 (cond
                   [(= (rand 0 1) 0) (^ expr "VarX")]
                   [else (^ expr "VarY")])]
                [(= num 1)
                 (cond
                   [(= (rand 0 1) 0) (^ "Sine(" (^ (buildhelper 0 (- depth 1) expr) ")"))]
                   [else (^ "Cosine(" (^ (buildhelper 0 (- depth 1) expr) ")"))])]
                 [(= num 2)
                  (cond
                    [(= (rand 0 1) 0) (^ expr (^ "(("
                                                                         (^ (buildhelper (rand 0 (- depth 1)) (- depth 1) expr) (^ "+" (^ (buildhelper (rand 0 (- depth 1)) (- depth 1) expr) ")/2)")))))]  
                    [else (^ expr (^ (buildhelper (rand 0 (- depth 1)) (- depth 1) expr) (^ "*" (buildhelper (rand 0 (- depth 1)) (- depth 1) expr))))])]
                 [(= num 4) (^ expr (^ "(" (^ (buildhelper (rand 0 (- depth 1)) (- depth 1) expr) (^ "<" (^ (buildhelper (rand 0 (- depth 1)) (- depth 1) expr) (^ "?" (^ (buildhelper (rand 0 (- depth 1)) (- depth 1) expr) (^ ":" (^ (buildhelper (rand 0 (- depth 1)) (- depth 1) expr) ")")))))))))]))])
      (buildhelper temp depth ""))))

  (define (ignore a) (void))

  (define (emitColor f1 f2 f3 n name)
    (let* ([fname (^ "art_c_" name)]
           [chan (open-output-file (^ fname ".ppm"))]
           [n2p1 (+ 1 (* n 2))]
           [temp1 (fprintf chan "P6 ~a ~a 255~n" n2p1 n2p1)]
           [temp2 (ffor (- 0 n) n (lambda (ix)
                                    (ffor (- 0 n) n (lambda (iy)
                                                      (let* ([x (toReal ix n)]
                                                             [y (toReal iy n)]
                                                             [z1 (f1 (list x y))]
                                                             [z2 (f2 (list x y))]
                                                             [z3 (f3 (list x y))]
                                                             [iz1 (toIntensity z1)]
                                                             [iz2 (toIntensity z2)]
                                                             [iz3 (toIntensity z3)])
                                                        (begin
                                                          (write chan (integer->char iz1))
                                                          (write chan (integer->char iz2))
                                                          (write chan (integer->char iz3))))))))])
      (begin
        (close-output-port chan)
        (ignore (system (^ "convert " (^ fname (^ ".ppm" (^ fname ".jpg"))))))
        (ignore (system (^ "rm " (^ fname ".ppm")))))))

  (define (assert bool)
    (cond
      [(not bool) raise 'AssertionError]))

  (define (eval_fn e x y)
    (let ([rv (eval e x y)])
      (cond
        [(not (and (<= -1.0 rv) (<= rv 1.0))) raise `AssertionError]
        [else rv])))
           
  )