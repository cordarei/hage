#lang racket/base

(require hage/parser)
(require hage/trx)


(define (np? x) (equal? "NP" (substring x 0 2)))
(define (! pred?) (lambda (x) (not (pred? x))))

(define pat (trx (^ ,np? (+ (any)))))
(define non-recursive (trx (^ ,np? (+ (rec notnp (or (^ ,string? ,string?) (^ ,(! np?) (+ notnp))))))))

(define tree (car (ptb-read (open-input-file "/home/joseph/Data/PTB/combined/wsj/00/wsj_0003.mrg"))))

(define npsbj (cadr 
               (cadr
                (caadr tree))))
(define basenp (cadr (cadr npsbj)))

(trx-match pat npsbj)
(trx-match non-recursive npsbj)
(trx-match non-recursive basenp)