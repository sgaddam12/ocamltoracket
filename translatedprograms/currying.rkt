#lang racket
(require soft-contract/fake-contract)

(define (ycomb x y) (x y))

(provide/contract [ycomb (((any/c . -> . any/c) . -> . (any/c . -> . any/c)) (any/c . -> . any/c) . -> . (any/c . -> . any/c))])