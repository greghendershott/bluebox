#lang racket

(define-syntax-rule (define-define id)
  (define (id) 0))

(define-define dd)

(define-syntax-rule (d/p/c (id arg ...) contract e ...)
  (begin
    (define (id arg ...)
      e ...)
    (provide (contract-out [id contract]))))

(d/p/c (dpc x)
       (-> any/c any)
       #t)

(define (f x)
  "Here's an optional doc string.

It can be multiple lines, of course."
  0)

(define (fd x [d0 0])
  0)
(provide fd)

(define (kw a b c [d0 0] [d1 1] #:kw kw)
  (+ 1 0))
(provide kw)

(define (-r x)
  0)
(provide (rename-out [-r r]))

(define/contract (dc x #:kw kw)
  (-> integer? #:kw integer? any)
  0)
(provide dc)

(define (pc)
  0)
(provide (contract-out [pc (-> any)]))

(define (-pcr)
  0)
(provide (contract-out [rename -pcr pcr (-> any)]))

(define/contract (rest x . xs)
  (->* (integer?) () #:rest integer? integer?)
  0)

(define/contract (foo r0
                      r1
                      #:kw kw
                      [opt0 (list 0)]
                      #:kwopt [kwopt (list 1)])
  (->* (integer? string? #:kw boolean?)
       (list? #:kwopt list?)
       integer?)
  0)
  
