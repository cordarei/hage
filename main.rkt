#lang racket/base

(require racket/match)

(require hage/parser)
(require racket-trx/trx)

;; ---------------------------------------------------------------------------------------------------
;; labels
(define (car-or-false lst) (if (null? lst) #f (car lst)))

;; (string? (list string?) (or/c number? #f) (or/c number? #f))
(struct ptb/label (category functions coindex coordindex) #:transparent)

;; (-> string? constituent-label?)
(define (parse-label lbl)
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
  (ptb/label category functions coindex coordindex))


;; tests
(define lbl-complex "PP-LOC-PRD-TPC-3")
(define lbl-complex2 "NP=2")

(parse-label lbl-complex)
(parse-label lbl-complex2)


;; ---------------------------------------------------------------------------------------------------
;; trees

(struct tree (root-constituent) #:transparent)
(struct constituent (label attr children) #:transparent)
(struct tagged-word (word pos attr) #:transparent)

(define (sexp->tree sxp)
  (define (helper s)
    (match s
      [(list (? string? pos) (? string? word))
       (tagged-word word pos '())]
      [(list (? string? label) (? list? children) ...)
       (constituent (parse-label label) '() (map helper children))]))
  (tree (helper sxp)))

;; ---------------------------------------------------------------------------------------------------
;; experiments

(define (np? x) (equal? "NP" (substring x 0 2)))
(define (! pred?) (lambda (x) (not (pred? x))))

(define pat (trx (^ ,np? (+ (any)))))
(define non-recursive (trx (^ ,np? (+ (rec notnp (or (^ ,string? ,string?) (^ ,(! np?) (+ notnp))))))))

(define ex-tree (car (ptb-read (open-input-file "/home/joseph/Data/PTB/combined/wsj/00/wsj_0003.mrg"))))

(define npsbj (cadr
               (cadr
                (cadr ex-tree))))
(define basenp (cadr (cadr npsbj)))

(trx-match pat npsbj)
(trx-match non-recursive npsbj)
(trx-match non-recursive basenp)
