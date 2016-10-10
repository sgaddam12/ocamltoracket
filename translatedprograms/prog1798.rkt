;;#lang soft-contract

(module prog-1798 racket
  ;;(require (submod ".." lib))
  
  (provide
   (contract-out
    [clone ((listof any/c) number? . -> . (listof any/c))]
    [padZero ((listof any/c) (listof any/c) . -> . (listof any/c))]
    [removeZero ((listof number?) . -> . (listof number?))]
    ))

  (define (clone x n)
    (cond
      [(<= n 0) '()]
      [else (cons x (clone x (- n 1)))]))

  (define (padZero l1 l2)
    (let ([diff (- (length l1) (length l2))])
      (cond
        [(>= diff 0) (cons l1 (list (append (clone 0 diff) l2)))]
        [else (cons (append (clone 0 (abs diff)) l1) (list l2))])))

  (define (removeZero l)
    (match l
      ['() '()]
      [(cons h t)
       (cond
         [(= h 0) (removeZero t)]
         [else (cons h (removeZero t))])]))

  (define (combine l1 l2)
    (cond
      [(and (= (length l1) 0) (= (length l2) 0)) '()]
      [(= (length l1) (length l2)) (cons (list (car l1) (car l2)) (combine (rest l1) (rest l2)))]
      [else (raise-arguments-error 'lengths
                                   "l1 is not the same size as l2"
                                   "l1" (length l1)
                                   "l2" (length l2))]))
  
  (define (bigAdd l1 l2)
    (letrec ([add (lambda (l1 l2)
                    (letrec ([f (lambda (a x)
                                  (cond
                                    [(= (length x) 2)
                                     (cond
                                       [(and (= (length a) 2) (= (car a) 0))
                                        (cond
                                          [(> (+ (car x) (cadr x)) 9) (list 1 (list (remainder (+ (car x) (cadr x)) 10)))]
                                          [else (list 0 (list (+ (car x) (cadr x))))])]
                                       [(= (length a) 2)
                                        (cond
                                          [(> (+ (+ (car x) (cadr x)) 1) 9) (list 1 (append (list (remainder (+ (+ (car x) (cadr x)) 1) 10)) a))]
                                          [else (list 0 (cons (+ (+ (car x) (cadr x)) 1) a))])])]))])
                      (let ([base '(0 '())])
                        (let ([args (reverse (combine l1 l2))])
                          (let ([res (cadr (foldl f base args))]) res)))))])
      (removeZero (add (car (padZero l1 l2)) (cadr (padZero l1 l2))))))

  )
