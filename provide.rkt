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
;; ;;;

;; #|

;; (require "provide.rkt")
;; (pretty-print
;;  (for/list ([sym '(f r dc pc pcr)])
;;    (match (identifier-binding (namespace-symbol->identifier sym))
;;      [(list source-mpi source-id
;;             nominal-source-mpi nominal-source-id
;;             source-phase import-phase nominal-export-phase)
;;       (list sym "source" source-id "nominal" nominal-source-id)])))

;; ;; ==>
;; ;; '((f "source" f "nominal" f)
;; ;;   (r "source" -r "nominal" r)
;; ;;   (dc "source" dc "nominal" dc)
;; ;;   (pc "source" provide/contract-id-pc.9 "nominal" pc)
;; ;;   (pcr "source" provide/contract-id-pcr.13 "nominal" pcr))

;; |#
