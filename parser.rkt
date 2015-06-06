#lang racket/base

(require parser-tools/lex
         (prefix-in : parser-tools/lex-sre)
         parser-tools/yacc)

(provide ptb-read)


(define default-root-label "ROOT")

;;----
;; lexer
(define-tokens label (LABEL))
(define-empty-tokens delim (OP CP EOF))

(define ptb-lexer
  (lexer-src-pos
   [(:+ whitespace) (return-without-pos (ptb-lexer input-port))]
   [(:+ (:~ (:or whitespace #\( #\)))) (token-LABEL lexeme)]
   [#\( 'OP]
   [#\) 'CP]
   [(eof) 'EOF]
   ))

;;----
;; parser
(define (format-parse-error tok-ok name val start-pos end-pos)
  (format "parse error with token-ok?:~a name:~a val:~a from ~a to ~a~n" tok-ok name val start-pos end-pos))
(define (display-parse-error tok-ok name val start-pos end-pos)
  (display (format-parse-error tok-ok name val start-pos end-pos)))

(define ptb-parser
  (parser
   (start sents)
   (end EOF)
   (src-pos)
   (tokens label delim)
   (error display-parse-error)
   (grammar
    (sents [(s sents) (cons $1 $2)]
           [() null])
    (s [(sexp) $1]
       [(empty-root) $1])
    (empty-root [(OP sexp CP) (list default-root-label $2)])
    (sexp [(leaf) $1]
          [(OP LABEL sexp-list CP) (cons $2 (reverse $3))])
    (leaf [(OP LABEL LABEL CP) (list $2 $3)])
    (sexp-list [() null]
               [(sexp-list sexp) (cons $2 $1)])
    )))

(define (ptb-read port)
  (ptb-parser (lambda () (ptb-lexer port))))
