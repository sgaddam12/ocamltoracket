#lang racket
(require soft-contract/fake-contract)

(define (plus a b) (string-length (b a)))

(provide/contract [plus (number? (number? . -> . string) . -> . number?)])

