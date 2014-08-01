#lang at-exp racket/base

(require syntax/modread
         syntax/parse
         racket/match
         racket/function
         racket/pretty
         racket/contract
         racket/list)

;; Return a syntax object (or #f) for the contents of `file`.
(define (file->syntax file #:expand? expand?)
  (define-values (base _ __) (split-path file))
  (parameterize ([current-load-relative-directory base]
                 [current-namespace (make-base-namespace)])
    (define stx (with-handlers ([exn:fail? (const #f)])
                  (with-module-reading-parameterization
                   (thunk
                    (with-input-from-file file read-syntax/count-lines)))))
    (if expand?
        (expand stx) ;; do this while current-load-relative-directory is set
        stx)))

(define (read-syntax/count-lines)
  (port-count-lines! (current-input-port))
  (read-syntax))

;;; db

(struct db [sigs
            contracts
            deflocs
            old-names
            new-names] #:transparent)
(define (make-db)
  (db (make-hasheq)
      (make-hasheq)
      (make-hasheq)
      (make-hasheq)
      (make-hasheq)))

(define (add-sig! db sym sig)
  (hash-set! (db-sigs db) (syntax-e sym) (syntax->datum sig)))
(define (add-contract! db sym contract)
  (hash-set! (db-contracts db) (syntax-e sym) (syntax->datum contract)))
(define (add-defloc! db sym stx)
  (hash-set! (db-deflocs db) (syntax-e sym) stx))
(define (add-rename! db old new)
  (hash-set! (db-old-names db) (syntax-e new) (syntax-e old))
  (hash-set! (db-new-names db) (syntax-e old) (syntax-e new)))

(define (get-sig db sym [else #f])
  (hash-ref (db-sigs db) sym else))
(define (get-contract db sym [else #f])
  (hash-ref (db-contracts db) sym else))
(define (get-defloc db sym [else #f])
  (hash-ref (db-deflocs db) sym else))
(define (get-old-name db sym [else #f])
  (hash-ref (db-old-names db) sym else))
(define (get-new-name db sym [else #f])
  (hash-ref (db-new-names db) sym else))

;; If `nom` has been renamed (from one or more (transitively) other
;; names), return those names in order from "more nominal" to "more
;; real". This will be the empty list if no renaming.
(define (realer-names db nom)
  (match (get-old-name db nom #f)
    [#f (list)]
    [s (cons s (realer-names db s))]))

(define (get-contract/effective db nom)
  (define names (reverse (cons nom (realer-names db nom))))
  (for/or ([name names]) ;use "outermost" contract
    (get-contract db name)))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; walk : syntax [db] -> hash
;;
;; Walk the syntax looking for define and provide forms, adding
;; information to db.
(define (walk stx [db (make-db)])
  (syntax-parse stx
    [((~datum module) _ _ . stxs)
     (for-each (λ (stx) (walk stx db))
               (syntax->list #'stxs))]
    [((~datum #%module-begin) . stxs)
     (for-each (λ (stx) (walk stx db))
               (syntax->list #'stxs))]
    [((~datum define) (s . as) . _)
     (add-defloc! db #'s #'s)
     (add-sig! db #'s #'as)]
    [((~datum define/contract) (s . as) c . _)
     (add-defloc! db #'s #'s)
     (add-sig! db #'s #'as)
     (add-contract! db #'s #'c)]
    [((~datum provide/contract) . stxs)
     (for ([stx (syntax->list #'stxs)])
       (syntax-parse stx
         [(s c) (add-contract! db #'s #'c)]
         [_     #f]))]
    [((~datum provide) . stxs)
     (for ([stx (syntax->list #'stxs)])
       (syntax-parse stx
         [((~datum rename-out) . stxs)
          (for ([stx (syntax->list #'stxs)])
            (syntax-parse stx
              [(from to) (add-rename! db #'from #'to)]
              [_ #f]))]
         [((~datum contract-out) . stxs)
          (for ([stx (syntax->list #'stxs)])
            (syntax-parse stx
              [((~datum rename) from to c)
               (add-rename! db #'from #'to)
               (add-contract! db #'to #'c)
               (add-contract! db #'from #'c)]
              [(s c) (add-contract! db #'s #'c)]
              [_ #f]))]
         [_ #f]))]
    ;;
    ;; patterns for fully-expanded syntax
    ;;
    ;; Ultimately this is the only approach that will work with all
    ;; files, including those with their own define and provide macros
    ;; and definer macros -- those will expand to primitives we _can_
    ;; walk. However walking them is harder, especially keyword
    ;; procedures and contracts.

    ;; Plain procedure w/o any optional or keyword parameters
    [((~datum define-values) (id:id) ((~datum lambda) sig:sig-class . stxs))
     (add-defloc! db #'id #'id)
     (add-sig! db #'id #'sig)]
    
    ;; Procedure with optional and/or keyword parameters
    [((~datum define-values)
      (id:id)
      ((~datum let-values) (((_:id)
                             ((~datum lambda) (_:id ...)
                              nlv:nested-lv)))
       ((~datum let-values) (_ ...)
        ((~datum #%app)
         _ ;lifted.N
         _ ;λ
         _ ;case-λ
         _ ;'(some-keywords)
         (quote kw ...)))))
     (define (helper args kws*)
       (define symbol->keyword (compose string->keyword symbol->string))
       (define kws (car (syntax->datum kws*)))
       (define xs
         (append*
          (for/list ([arg (syntax->datum args)])
            (match arg
              [(and xs (or `(,id (quote ,def))
                           `(,id ,def)))
               (if (member (symbol->keyword id) kws)
                   `(,(symbol->keyword id) (,id ,def))
                   `((,id ,def)))]
              [id
               (if (member (symbol->keyword id) kws)
                   `(,(symbol->keyword id) ,id)
                   `(,id))]))))
       (datum->syntax args xs))
     (add-defloc! db #'id #'id)
     (add-sig! db #'id (helper #'nlv.ids #'(kw ...)))]

    ;; Contract (provide)
    [((~datum define-values)
      (_)
      ((~datum let-values) (((id:id)
                             ((~datum #%app)
                              (~datum coerce-contract)
                              'provide/contract
                              ((~datum #%app)
                               (~datum flat-named-contract)
                               ctr:expr
                               _))))
       _))
     (add-contract! db #'id #'ctr)]
    
    ;; Contract (define/contract)
    ;;
    ;; I don't see how to recover the contract expression from
    ;; fully-expanded syntax -- it is not preserved as the expression
    ;; from the original source.
    ;;
    ;; I'm going to punt on this. Hopefully that's acceptable because
    ;; define/contract is not the preferred form.

    ;; Rename
    [((~datum #%provide) . stxs)
     (for ([stx (syntax->list #'stxs)])
       (syntax-parse stx
         [((~datum rename) from to) (add-rename! db #'from #'to)]
         [_ #f]))]

    
    [_ #f])
  db)

(define (file->db path) ;path? -> db?
  ;; Walk the unexpanded syntax -- then walk the fully-expanded, too.
  (walk (file->syntax path #:expand? #t)
        (walk (file->syntax path #:expand? #f))))

(define-syntax-class nested-lv
  (pattern ((~datum let-values) () ((~datum #%app) _ ...))
           #:with ids '())
  (pattern ((~datum let-values)
            (((id:id) ((~datum if) _ _ default:expr))) lv:nested-lv)
           #:with ids (cons (list #'id #'default) #'lv.ids))
  (pattern ((~datum let-values) (((id:id) _ ...))
            lv:nested-lv)
           #:with ids (cons #'id #'lv.ids)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Signatures

(define-splicing-syntax-class sig-arg
  #:attributes (val)
  (pattern (~seq kw:keyword [id:id def:expr])
           #:attr val #`[(kw [id def])
                         #f
                         #,(keyword->string (syntax-e #'kw))])
  (pattern (~seq kw:keyword id:id)
           #:attr val #`[(kw id)
                         #t
                         #,(keyword->string (syntax-e #'kw))])
  (pattern [id:id def:expr]
           #:attr val #`[(id def)
                         #f
                         ""])
  (pattern id:id
           #:attr val #`[(id)
                         #t
                         ""]))

;; (syntax-parse #'(x #:kw0 kw0)
;;   [(x:sig-arg ...)
;;    #'((x.id
;;        x.pos?
;;        x.req?
;;        x.sort-val) ...)])

(define-syntax-class sig-class
  #:attributes (reqs opts rest)
  (pattern (a:sig-arg ...)
           #:attr reqs (sort-sig-args #'(a.val ...) #t)
           #:attr opts (sort-sig-args #'(a.val ...) #f)
           #:attr rest #f)
  (pattern (a:sig-arg ... . r:id)
           #:attr reqs (sort-sig-args #'(a.val ...) #t)
           #:attr opts (sort-sig-args #'(a.val ...) #f)
           #:attr rest #'r))

(define (sort-sig-args stx req?)
  ;; Expects stx to be a list of lists, where `first` is the contract,
  ;; `second` is a required? boolean, and `third` is the value to use
  ;; when sorting. Sorts and returns a list of just the first items
  ;; (i.e. discards the sort-by values).
  (map first
       (sort (filter (λ (v)
                       (equal? (second v) req?))
                     (syntax->datum stx))
             string<?
             #:key third)))

;; (syntax-parse #'(a . rest) ;;#'(x #:kw kw [y 0] #:kw-opt [kw-opt 0])
;;   [sig:sig-class
;;    (displayln (syntax->datum #'sig))
;;    (displayln (attribute sig.reqs))
;;    #t])

;;; Contracts

(define-splicing-syntax-class ctr-arg
  #:attributes (val)
  (pattern (~seq kw:keyword ctr:expr)
           #:attr val #`[ctr #,(keyword->string (syntax-e #'kw))])
  (pattern (~seq ctr:expr)
           #:attr val #`[ctr ""]))

;; (syntax-parse #'(-> #:kw0 any/c)
;;   [((~literal ->) x:ctr-arg)
;;    #'(x.sort-val)])

(define (sort-ctr-args stx)
  ;; Expects stx to be a list of lists, where `first` is the contract
  ;; and `second` is the value to use when sorting. Sorts and returns
  ;; a list of just the first items (i.e. discards the sort-by
  ;; values).
  (map first
       (sort (syntax->datum stx)
             string<?
             #:key second)))

;; Syntax class for matching contracts. Returns 3 plain (non-syntax)
;; Required argument contracts (sorted), Optional argument contracts
;; (sorted), and return contract. The arguments are sorted to
;; positional arguments in their original order, first, then keyword
;; arguments sorted by #:keyword name.
(define-syntax-class ctr-class
  #:attributes (reqs opts rtn rest)
  (pattern ((~datum ->*)
            (req:ctr-arg ...)
            (opt:ctr-arg ...)
            (~optional (~seq #:rest rest:expr))
            _rtn:expr)
           #:attr reqs (sort-ctr-args #'(req.val ...))
           #:attr opts (sort-ctr-args #'(opt.val ...))
           #:attr rtn (syntax->datum #'rtn))
  (pattern ((~datum ->) req:ctr-arg ... r:expr)
           #:attr reqs (sort-ctr-args #'(req.val ...))
           #:attr opts '()
           #:attr rest #f
           #:attr rtn (syntax->datum #'r)))

;; (syntax-parse '(-> any/c #:kw1 int? #:kw0 char? any)
;;   [ctr:ctr-class
;;    (list (attribute ctr.reqs)
;;          (attribute ctr.opts)
;;          (attribute ctr.rtn))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; blue-box : symbol stx stx -> string
;;
;; Combine a signature and a contract into a classic Racket
;; documentation "blue box" summary.
;;
;; Note: `sig` is expected NOT to include the function name, which is
;; in `sym` instead.
(define/contract (blue-box sym sig con)
  (-> symbol? (or/c list? pair? syntax?) (or/c #f list? pair? syntax?) any)
  (define-values (sig-reqs sig-opts sig-rest)
    (syntax-parse sig
      [sig:sig-class (values (attribute sig.reqs)
                             (attribute sig.opts)
                             (and (attribute sig.rest)
                                  (syntax->datum (attribute sig.rest))))]))
  (define-values (con-reqs con-opts con-rest con-rtn)
    (syntax-parse con
      [con:ctr-class (values (attribute con.reqs)
                             (attribute con.opts)
                             (and (attribute con.rest)
                                  (syntax->datum (attribute con.rest)))
                             (attribute con.rtn))]
      [_ (values '() '() #f #f)]))
  ;; (pretty-print (list sig-reqs sig-opts
  ;;                     con-reqs con-opts con-rtn))
  ;; [1] Display the signature
  (define sig-opt-ids
    (append* (map (compose reverse cdr reverse flatten) sig-opts)))
  ;; FIXME: pretty-print doesn't really wrap correctly, we should do
  ;; it ourselves: 1. keep `#:kw kw` on same line. 2. Take into
  ;; account the `-> return?` for wrapping.
  (pretty-display/no-newline
   `(,sym
     ,@(append* sig-reqs)
     ,@(if (empty? sig-opt-ids) '() '(#\[))
     ,@sig-opt-ids
     ,@(if (empty? sig-opt-ids) '() '(#\]))
     ,@(if sig-rest `(#\. ,sig-rest) '())
     ))
  ;; [1a] Including the return type if any
  (when con-rtn (display " -> ") (display con-rtn))
  (newline)
  ;; [2] Display the parameter types, if any, each on own line.
  ;; [2a] Required
  (for ([s sig-reqs]
        [c con-reqs])
    (display "  ")
    (display (car (reverse s)))
    (display " : ")
    (pretty-display c))
  ;; [2b] Optional
  (for ([s sig-opts]
        [c con-opts])
    (display "  ")
    (define-values (id def) (match s
                              [(list kw (list id def)) (values id def)]
                              [(list id def) (values id def)]))
    (display id)
    (display " : ")
    (pretty-display/no-newline c)
    (display " = ")
    (print def)
    (newline))
  ;; [2c] Rest
  (when (and sig-rest con-rest)
    (display "  ")
    (display sig-rest)
    (display " : ")
    (pretty-display con-rest)))

;; (blue-box 'name
;;           #'(req [opt 0] #:kw-req kw-req #:kw-opt [kw-opt 0])
;;           #'(->*
;;             (req? #:kw kw-req? #:kw-very-long kw-very-long?)
;;             (opt? #:kw-opt kw-opt?)
;;             rtn?))

(define (db->blue-boxes db)
  (for ([(sym sig) (in-hash (db-sigs db))])
    (blue-box sym sig (get-contract/effective db sym))))

(define (file->blue-boxes path)
  (db->blue-boxes (file->db path)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; blue-line (one-liner format)

(define/contract (blue-line sym sig con)
  (-> symbol? (or/c list? pair? syntax?) (or/c #f list? pair? syntax?) any)
    (define-values (sig-reqs sig-opts sig-rest)
    (syntax-parse sig
      [sig:sig-class (values (attribute sig.reqs)
                             (attribute sig.opts)
                             (and (attribute sig.rest)
                                  (syntax->datum (attribute sig.rest))))]))
  (define-values (con-reqs con-opts con-rest con-rtn)
    (syntax-parse con
      [con:ctr-class (values (attribute con.reqs)
                             (attribute con.opts)
                             (and (attribute con.rest)
                                  (syntax->datum (attribute con.rest)))
                             (attribute con.rtn))]
      [_ (values '() '() #f #f)]))
  ;; (define sig-opt-ids
  ;;   (append* (map (compose reverse cdr reverse flatten) sig-opts)))
  (display "(")
  (display sym)
  (for ([s sig-reqs]
        [c (or con-reqs (make-list (length sig-reqs) #f))])
    (display " {")
    (for ([v s]) (display v))
    (display " : ")
    (pretty-display/no-newline c)
    (display "}"))
  (unless (empty? sig-opts)
    (display " [")
    (for ([s sig-opts]
          [c (or con-opts (make-list (length sig-opts) #f))])
      (display " {")
      (for ([v s]) (display v))
      (display " : ")
      (pretty-display/no-newline c)
      (display "}"))
    (display "]"))
  (when (and sig-rest con-rest)
    (display " {")
    (display sig-rest)
    (display " : ")
    (pretty-display/no-newline con-rest)
    (display "}"))
  (display ")")
  (when con-rtn (display " -> ") (display con-rtn))
  (newline))

(define (db->blue-lines db)
  (for ([(sym sig) (in-hash (db-sigs db))])
    (blue-line sym sig (get-contract/effective db sym))))

(define (file->blue-lines path)
  (db->blue-lines (file->db path)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (pretty-display/no-newline v)
  (define oos (open-output-string))
  (pretty-display v oos)
  (define s (get-output-string oos))
  (display (substring s 0 (sub1 (string-length s))))) ;; not trailing \n

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; usage examples

(require racket/runtime-path)
(define-runtime-path provide.rkt "provide.rkt")
;; (file->blue-boxes provide.rkt)
;; (file->blue-lines provide.rkt)

(require syntax/modresolve)
;; (file->blue-boxes (resolve-module-path 'net/url (current-load-relative-directory)))
;; (file->blue-lines (resolve-module-path 'net/url (current-load-relative-directory)))

;; (define _db (walk (file->syntax provide.rkt #:expand? #t)))
;; (db-sigs _db)
;; (db-contracts _db)
;; (db-old-names _db)
;; (db-deflocs _db)
