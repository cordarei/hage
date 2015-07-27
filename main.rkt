#lang racket/base

(require racket/match)
(require db)

(require hage/parser)
(require racket-trx/trx)

;; ---------------------------------------------------------------------------------------------------
;; labels
(define (car-or-false lst) (if (null? lst) #f (car lst)))

;; (string? (list string?) (or/c number? #f) (or/c number? #f))
(struct ptb-label (category functions coindex coordindex) #:transparent)

;; (-> string? constituent-label?)
(define (string->ptb-label lbl)
  (define parts (regexp-split #rx"(?=[-=])" lbl))
  (define category (car parts))
  ;
  (define (collect-parts p)
    (map (λ (x) (substring x 1))
         (filter (λ (x) (regexp-match p x))
                 (cdr parts))))
  (define (collect-index p)
    (car-or-false (map string->number
                       (collect-parts p))))
  ;
  (define functions (collect-parts #rx"-[A-Z]"))
  (define coindex (collect-index #rx"-[0-9]"))
  (define coordindex (collect-index #rx"=[0-9]"))
  ;
  (ptb-label category functions coindex coordindex))


;; tests
(define lbl-complex "PP-LOC-PRD-TPC-3")
(define lbl-complex2 "NP=2")

;; (string->ptb-label lbl-complex)
;; (string->ptb-label lbl-complex2)


;; ---------------------------------------------------------------------------------------------------
;; trees

;; Tree = tree constituent | constituent ptb/label attr (listof Tree) | tagged-ord String String attr
(struct tree (root-constituent) #:transparent)
(struct constituent (label attr children) #:transparent)
(struct tagged-word (word pos attr) #:transparent)

(define (attr-get k attr) (define a (assoc k attr)) (and a (cdr a)))
(define (attr-set k v attr) (cons (cons k v) (filter (λ (x) (not (equal? k (car x)))) attr)))

(define (tree-attr k t)
  (match t
    [(tagged-word w p a)
     (attr-get k a)]
    [(constituent l a c)
     (attr-get k a)]))

(define (update-attr k v t)
  (match t
    [(tagged-word w p a)
     (tagged-word w p (attr-set k v a))]
    [(constituent l a c)
     (constituent l (attr-set k v a) c)]))

(define (sexp->tree sxp)
  (define (helper s)
    (match s
      [(list (? string? pos) (? string? word))
       (tagged-word word pos '())]
      [(list "ROOT" (? list? child))
       (helper child)]
      [(list (? string? label) (? list? children) ...)
       (constituent (string->ptb-label label) '() (map helper children))]))
  (tree (helper sxp)))


(define (yield sth)
  (match sth
    [(tagged-word word pos attr)
     (list word)]
    [(constituent label attr children)
     (apply append (map yield children))]
    [(tree root)
     (yield root)]))

;; Tree (listof Natural) -> Tree
(define (tree-ref t idx)
  (if (null? idx)
      t
      (match t
        [(constituent l a cs)
         (tree-ref (list-ref cs (car idx)) (cdr idx))]
        [(tree r) (if (= 0 (car idx))
                      (tree-ref r (cdr idx))
                      (error "oops"))])))

; Tree -> Tree
(define (add-spans t)
  (define (helper c start)
    (match c
      [(constituent label attr children)
       (define-values (new-children end)
         (for/fold ([new-children '()]
                    [new-start start])
                   ([c children])
           (define-values (new-child new-end)
             (helper c new-start))
           (values (cons new-child new-children)
                   new-end)))
       (values (constituent label
                            (attr-set 'span (cons start end) attr)
                            (reverse new-children))
               end)]
      [(tagged-word word pos attr)
       (values (tagged-word word pos (attr-set 'span (cons start (+ start 1)) attr))
               (+ start 1))]))
  (let-values ([(root end) (helper (tree-root-constituent t) 0)])
    (tree root)))

(define (annotate-empty t)
 (define (annotate-empty x)
  (match x
    [(tagged-word w p a)
     (tagged-word w p (attr-set 'empty (equal? p "-NONE-") a))]
    [(constituent l a cs)
     (define new-cs (map annotate-empty cs))
     (constituent l
                  (attr-set 'empty (ormap (λ (x) (tree-attr 'empty x)) new-cs) a)
                  new-cs)]
    ))
  (tree (annotate-empty (tree-root-constituent t))))



;;;
;;; or try a zipper-based processing model?
;;;  pass multiple processor functions which work on zipper positions to the main annotate function
;;; annotations could be stored in separate list
;;; tree position as index
;;; lexicographic order of tree positions == pre-order

;; ---------------------------------------------------------------------------------------------------
;; experiments

;; (define (np? x) (equal? "NP" (substring x 0 2)))
;; (define (! pred?) (lambda (x) (not (pred? x))))

;; (define pat (trx (^ ,np? (+ (any)))))
;; (define non-recursive (trx (^ ,np? (+ (rec notnp (or (^ ,string? ,string?) (^ ,(! np?) (+ notnp))))))))

(define ex-tree (car (ptb-read (open-input-file "/home/joseph/Data/PTB/combined/wsj/00/wsj_0003.mrg"))))
(define ex-tree-tree (sexp->tree ex-tree))

;; (define npsbj (cadr
;;                (cadr
;;                 (cadr ex-tree))))
;; (define basenp (cadr (cadr npsbj)))

;; (define npsbjconst (tree-root-constituent ex-tree-tree))

;; (trx-match pat npsbj)
;; (trx-match non-recursive npsbj)
;; (trx-match non-recursive basenp)

(define conn (sqlite3-connect #:database "/home/joseph/Work/test.db" #:mode 'create))
(query-exec conn "create table words(word)")
(define insert-st (prepare conn "insert into words values($1)" ))
(for ((w (yield ex-tree-tree)))
  #;(query-exec conn (format "insert into words values (\"~a\")" w))
  (query-exec conn insert-st w)
  )
(query-list conn "select * from words")
(disconnect conn)
