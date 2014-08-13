#lang at-exp racket/base

(require racket/syntax
         syntax/modread
         syntax/parse
         racket/match
         racket/pretty
         racket/contract
         racket/list)

;; Get the contents of a file as a syntax object, and return the
;; result of applying the supplied function.
(define/contract (file->syntax file proc)
  (-> path? (-> syntax? any/c) any/c)
  (define-values (base _ __) (split-path file))
  (parameterize ([current-load-relative-directory base])
    (define stx (with-handlers ([exn:fail? (λ () #f)])
                  (with-module-reading-parameterization
                   (λ ()
                    (with-input-from-file file read-syntax/count-lines)))))
    ;; Call `proc` while current-load-relative-directory is set, so
    ;; that relative `require`s work.
    (and stx (proc stx))))

(define (read-syntax/count-lines)
  (port-count-lines! (current-input-port))
  (read-syntax))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (expand-finding-definitions-and-contracts stx)
  (define db (make-db))
  (void (expand (munge-module stx db)))
  db)

;; Wrap every module-level expression in a macro `partial-expand` that
;; does a `local-expand` to certain forms where it is convenient to
;; discover definitions and contracts, using `walk`, then return the
;; original form for further expansion.
;;
;; Note: The expand/hide function from macro-debugger/expand does what
;; I want -- but very slowly, since under the hood it's deriving and
;; storing all the expansion steps. Very slowly means 90 seconds vs. 1
;; second for the approach I'm using here. I'd *love* to simply use
;; expand/hide, but can't.
;;
;; QUESTION: Is there a better way to do this? More or less, I want to
;; override #%module-begin. The only way I can figure out how to do so
;; for any arbitrary module that uses any arbitrary lang, is to munge
;; the syntax object here. Although this works for the examples I've
;; tried so far, is it actually correct and reliable in general?
(define (munge-module stx db)
  (syntax-parse stx
    [(module id lang
       (#%module-begin mod-exps ...))
     (define/with-syntax partial-expand (gensym)) ;avoid name collision
     (define/with-syntax (new-mod-exps ...)
       (for/list ([mod-exp (syntax->list #'(mod-exps ...))])
         (syntax-parse mod-exp
           ;; FIXME: Why doesn't #:literals work here?
           #:datum-literals (module+) ;module+ can't be wrapped...
           [(module+ . _) mod-exp]    ;...so leave it as-is
           [_ #`(partial-expand #,mod-exp)])))
     #`(module id lang
         (#%module-begin
          (require (for-syntax racket/base))
          (define-syntax (partial-expand stx)
            (syntax-case stx ()
              [(_ e)
               (begin
                 (#,walk (local-expand #'e
                                       'top-level ;QUESTION: Why
                                                  ;doesn't 'module
                                                  ;work here?
                                       (list #'define
                                             #'provide
                                             #'define/contract
                                             #'provide/contract))
                         #,db)
                 #'e)]))
          new-mod-exps ...))]))

(define (file->db path) ;path? -> db?
  (parameterize ([current-namespace (make-base-namespace)])
    (file->syntax path expand-finding-definitions-and-contracts)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; db

(struct db [sigs
            contracts
            deflocs
            docstrs
            old-names
            new-names] #:transparent)
(define (make-db)
  (db (make-hasheq)
      (make-hasheq)
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
(define (add-docstr! db sym stx)
  (hash-set! (db-docstrs db) (syntax-e sym) (syntax->datum stx)))
(define (add-rename! db old new)
  (hash-set! (db-old-names db) (syntax-e new) (syntax-e old))
  (hash-set! (db-new-names db) (syntax-e old) (syntax-e new)))

(define (get-sig db sym [else #f])
  (hash-ref (db-sigs db) sym else))
(define (get-contract db sym [else #f])
  (hash-ref (db-contracts db) sym else))
(define (get-defloc db sym [else #f])
  (hash-ref (db-deflocs db) sym else))
(define (get-docstr db sym [else #f])
  (hash-ref (db-docstrs db) sym else))
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

;; If `nom` has been renamed one or more times, then it may have one
;; or more contracts. Return the "effective" one. Here we use the
;; "outermost" one, because it is closest to what the user perceives
;; the function to be. (This isn't necessarily the "most restrictive"
;; contract, which might also be interesting, but I think is N/A for
;; this purpose.)
(define (get-contract/effective db nom)
  (define names (reverse (cons nom (realer-names db nom))))
  (for/or ([name names]) ;use "outermost" contract
    (get-contract db name)))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; walk : syntax [db] -> hash
;;
;; Walk the syntax looking for define and provide forms, adding
;; information to db.
;;
;; Note: Although `db` is returned for convenience, it is mutated (not
;; functionally updated).
(define (walk stx [db (make-db)])
  (syntax-parse stx
    #:literals
    (begin module #%module-begin define define/contract
           provide provide/contract)
    ;;
    ;; Just walk recursively
    ;;
    [(begin . stxs) (for ([stx (syntax->list #'stxs)])
                      (walk stx db))]
    [(module _id _lang . stxs) (for ([stx (syntax->list #'stxs)])
                                 (walk stx db))]
    [(#%module-begin . stxs) (for ([stx (syntax->list #'stxs)])
                               (walk stx db))]
    ;;
    ;; Definitions (and maybe contracts)
    ;;
    [(define (id . args) (~optional doc:str) . _)
     (add-defloc! db #'id #'id)
     (add-sig! db #'id #'args)
     (when (attribute doc) (add-docstr! db #'id #'doc))]
    [(define/contract (id . args) con (~optional doc:str) . _)
     (add-defloc! db #'id #'id)
     (add-sig! db #'id #'args)
     (add-contract! db #'id #'con)
     (when (attribute doc) (add-docstr! db #'id #'doc))]
    ;;
    ;; Provides (and maybe contracts and renames)
    ;;
    [(provide/contract . stxs)
     (for ([stx (syntax->list #'stxs)])
       (syntax-parse stx
         [(id con) (add-contract! db #'id #'con)]
         [_        #f]))]
    [(provide . stxs)
     (for ([stx (syntax->list #'stxs)])
       (syntax-parse stx
         #:literals (rename-out contract-out)
         [(rename-out . stxs)
          (for ([stx (syntax->list #'stxs)])
            (syntax-parse stx
              [(from to) (add-rename! db #'from #'to)]
              [_ #f]))]
         [(contract-out . stxs)
          (for ([stx (syntax->list #'stxs)])
            (syntax-parse stx
              ;; QUESTION: Why doesn't #:literals work here?
              #:datum-literals (rename)
              [(rename from to con)
               (add-rename! db #'from #'to)
               (add-contract! db #'to #'con)
               (add-contract! db #'from #'con)]
              [(id con) (add-contract! db #'id #'con)]
              [_ #f]))]
         [_ #f]))]
    [_ #f])
  db)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct blue
  (sym        ;symbol? : The function name
   sig        ;list? : The full arguments list, NOT including `sym`
   sig-reqs   ;list? : The required args
   sig-opts   ;list? : The optional args
   sig-rest   ;list? : The rest arg
   con        ;(or/c #f (listof sexpr?)) : The contract (if any)
   con-reqs   ;(or/c #f (listof sexpr?)) : Required args' contracts
   con-opts   ;(or/c #f (listof sexpr?)) : Optional args' contracts
   con-rest   ;(or/c #f (listof sexpr?)) : Rest arg's contract
   con-rtn    ;(or/c #f sexpr?)          : Return value contract
   doc)       ;(or/c #f string?) : The doc string
  #:transparent)

(define/contract (sym->blue db sym)
  (-> db? symbol? blue?)
  (define sig (get-sig db sym))
  (define-values (sig-reqs sig-opts sig-rest)
    (syntax-parse sig
      [sig:sig-class (values (attribute sig.reqs)
                             (attribute sig.opts)
                             (and (attribute sig.rest)
                                  (syntax->datum (attribute sig.rest))))]))
  (define con (get-contract/effective db sym))
  (define-values (con-reqs con-opts con-rest con-rtn)
    (syntax-parse con
      [con:ctr-class (values (attribute con.reqs)
                             (attribute con.opts)
                             (and (attribute con.rest)
                                  (syntax->datum (attribute con.rest)))
                             (attribute con.rtn))]
      [_ (values '() '() #f #f)]))
  (define doc (get-docstr db sym))
  (blue sym
        sig sig-reqs sig-opts sig-rest
        con con-reqs con-opts con-rest con-rtn
        doc))

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

(define-syntax-class sig-class
  #:attributes (reqs opts rest)
  (pattern (a:sig-arg ...)
           #:attr reqs (filter&sort-sig-args #'(a.val ...) #t)
           #:attr opts (filter&sort-sig-args #'(a.val ...) #f)
           #:attr rest #f)
  (pattern (a:sig-arg ... . r:id)
           #:attr reqs (filter&sort-sig-args #'(a.val ...) #t)
           #:attr opts (filter&sort-sig-args #'(a.val ...) #f)
           #:attr rest #'r))

(define (filter&sort-sig-args stx req?)
  ;; Helper function for sig-class. Expects stx to be a list of lists,
  ;; where for each inner list `first` is the contract, `second` is a
  ;; `required?` boolean, and `third` is the value to use when
  ;; sorting. Sorts and returns a list of just the first items (i.e.
  ;; discards the sort-by values).
  (map first
       (sort (filter (λ (v)
                       (equal? (second v) req?))
                     (syntax->datum stx))
             string<?
             #:key third)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Contracts

(define-splicing-syntax-class ctr-arg
  #:attributes (val)
  (pattern (~seq kw:keyword ctr:expr)
           #:attr val #`[ctr #,(keyword->string (syntax-e #'kw))])
  (pattern (~seq ctr:expr)
           #:attr val #`[ctr ""]))

;; Syntax class for matching contracts. Returns 3 plain (non-syntax)
;; attributes: Required argument contracts (sorted), Optional argument
;; contracts (sorted), and return contract. The arguments are sorted
;; to positional arguments in their original order, first, then
;; keyword arguments sorted by #:keyword name.
(define-syntax-class ctr-class
  ;; FIXME: Why doesn't #:literals work here?
  #:datum-literals (->* ->)
  #:attributes (reqs opts rtn rest)
  (pattern (->* (req:ctr-arg ...)
                (opt:ctr-arg ...)
                (~optional (~seq #:rest rest:expr))
                _rtn:expr)
           #:attr reqs (sort-ctr-args #'(req.val ...))
           #:attr opts (sort-ctr-args #'(opt.val ...))
           #:attr rtn (syntax->datum #'_rtn))
  (pattern (-> req:ctr-arg ... r:expr)
           #:attr reqs (sort-ctr-args #'(req.val ...))
           #:attr opts '()
           #:attr rest #f
           #:attr rtn (syntax->datum #'r)))

(define (sort-ctr-args stx)
  ;; Helper function for ctr-class. Expects stx to be a list of lists,
  ;; where `first` is the contract and `second` is the value to use
  ;; when sorting. Sorts and returns a list of just the first items
  ;; (i.e. discards the sort-by values).
  (map first
       (sort (syntax->datum stx)
             string<?
             #:key second)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; print-blue-box : blue? -> any
;;
;; A classic Racket documentation "blue box" summary.
(define/contract (print-blue-box b)
  (-> blue? any)
  (match-define (blue sym sig sig-reqs sig-opts sig-rest
                      con con-reqs con-opts con-rest con-rtn doc) b)
  ;; [1] Display the signature
  (define sig-opt-kws/ids
    (append* (for/list ([sig sig-opts])
               (match sig
                 [(list (? keyword? kw) (list id def)) (list kw id)]
                 [(list id def) (list id)]))))
  ;; FIXME: pretty-print doesn't really wrap correctly, we should do
  ;; it ourselves: 1. keep `#:kw kw` on same line. 2. Take into
  ;; account the `-> return?` for wrapping.
  (pretty-display/no-newline
   `(,sym
     ,@(append* sig-reqs)
     ,@(if (empty? sig-opt-kws/ids) '() '(#\[))
     ,@sig-opt-kws/ids
     ,@(if (empty? sig-opt-kws/ids) '() '(#\]))
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
    (define-values (id def)
      (match s
        [(list (? keyword? kw) (list id def)) (values id def)]
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
    (pretty-display con-rest))
  (when doc
    (displayln doc)))

(define (db->blue-boxes db)
  (for ([sym (in-hash-keys (db-sigs db))])
    (print-blue-box (sym->blue db sym))))

(define (file->blue-boxes path)
  (db->blue-boxes (file->db path)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; print-blue-line : blue? -> any
;;
;; A one-line format, more suitable for e.g. eldoc status bar.
(define/contract (print-blue-line b)
  (-> blue? any)
  (match-define (blue sym sig sig-reqs sig-opts sig-rest
                      con con-reqs con-opts con-rest con-rtn doc) b)
  (display "(")
  (display sym)
  (for ([s sig-reqs]
        [c (or con-reqs (make-list (length sig-reqs) #f))])
    (match s
      [(list (? keyword? kw) id) (printf " ~a ~a:~a" kw id c)]
      [(list id)                 (printf    " ~a:~a"    id c)]))
  (unless (empty? sig-opts)
    (for ([s sig-opts]
          [c (if (empty? con-opts) (make-list (length sig-opts) #f) con-opts)])
      (match s
        [(list (? keyword? kw) (list id def))
         (if c
             (printf " ~a ~a:~a=~a" kw id c def)
             (printf " ~a ~a=~a" kw id def))]
        [(list id def)
         (if c
             (printf " ~a:~a=~a" id c def)
             (printf " ~a=~a" id def))])))
  (when (and sig-rest con-rest)
    (display " ")
    (display sig-rest)
    (display ":")
    (pretty-display/no-newline con-rest))
  (display ")")
  (when con-rtn (display " -> ") (display con-rtn))
  (newline))

(define (db->blue-lines db)
  (for ([sym (in-hash-keys (db-sigs db))])
    (print-blue-line (sym->blue db sym))))

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
;; (file->blue-boxes (resolve-module-path 'net/url current-load-relative-directory))
;; (file->blue-lines (resolve-module-path 'net/url current-load-relative-directory))
;; (file->blue-boxes (resolve-module-path 'aws/s3 current-load-relative-directory))

;; (define _db (file->db provide.rkt expand))
;; (db-sigs _db)
;; (db-contracts _db)
;; (db-old-names _db)
;; (db-deflocs _db)
