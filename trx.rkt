;; ===================================================================================================
;; Implements a matcher for regular tree expressions
;;   based on Ilya Bagrak and Olin Shivers (2004) 'trx: Regular-tree expressions, now in Scheme'.

#lang racket

(require racket/control)

(module+ test
  (require rackunit))

;; ---------------------------------------------------------------------------------------------------
; abstract syntax

(struct ast-lit-node
  (literal
  private))

(struct ast-sym-node
  (symbol
  children
  private))

(struct ast-seq-node
  (quantifier
  child
  private))

;; ---------------------------------------------------------------------------------------------------
;; automata

;; the record type that holds a compiled tree automaton
(struct fta
  (states
   ;; list of labels used in rules -- unused?
   alphabet
   labeled-rules
   empty-rules
   final-states
   special-states
   submatch-states))

;; a non-empty rule: f(q_in)q_out -> q
(struct label-rule
  (sym-name
  in-state
  out-state
  final-state))

;; an empty rule: () -> q
(struct empty-rule
  (final-state))

;; special symbol for matching unlabeled trees
(define unlabeled-tree (gensym))

(module+ test
  ;; example fta that matches (a b c d) and no other tree
  (define ex-fta
    (fta '(q0 q1 q2 q3 q4 q6)
         '(a b c d)
         (list (label-rule 'a 'q1 'q2 'q0)
               (label-rule 'b 'q2 'q4 'q1)
               (label-rule 'c 'q2 'q6 'q4)
               (label-rule 'd 'q2 'q2 'q6))
         (list (empty-rule 'q2))
         '(q0)
         '()
         '())))
#;
(define (match-empty aut state)
  (for/or ([r (fta-empty-rules aut)])
    (eq? state (empty-rule-final-state r))))
#;
(module+ test
  (check-not-false (match-empty ex-fta 'q2))
  (check-false (match-empty ex-fta 'q1)))

;; does the given rule match the given node in the given state
(define (rule-match? fta rule node state)
  (let* ([q (label-rule-final-state rule)]
        [f (label-rule-sym-name rule)]
        [n.label (cond
                   [(eq? f unlabeled-tree) f]
                   [(list? node) (car node)]
                   [else node])])
    (and (eq? q state)
         (equal? f n.label))))

(module+ test
  (check-true (rule-match? ex-fta (list-ref (fta-labeled-rules ex-fta) 0) '(a b c d) 'q0))
  (check-false (rule-match? ex-fta (list-ref (fta-labeled-rules ex-fta) 1) '(a b c d) 'q0))
  (check-false (rule-match? ex-fta (list-ref (fta-labeled-rules ex-fta) 1) '(a b c d) 'q1))
  (check-false (rule-match? ex-fta (list-ref (fta-labeled-rules ex-fta) 0) '(b c d) 'q0))
  (check-true (rule-match? ex-fta (list-ref (fta-labeled-rules ex-fta) 1) 'b 'q1))
  (check-true (rule-match? ex-fta (list-ref (fta-labeled-rules ex-fta) 1) '(b c d) 'q1))
  (check-true (rule-match? ex-fta (list-ref (fta-labeled-rules ex-fta) 3) 'd 'q6)))

(define (select-rule fta node state)
  (filter (λ (r) (rule-match? fta r node state))
          (fta-labeled-rules fta)))

(module+ test
  (check-equal? (select-rule ex-fta '(a b c d) 'q0) (list (list-ref (fta-labeled-rules ex-fta) 0)))
  (check-equal? (select-rule ex-fta 'b 'q1) (list (list-ref (fta-labeled-rules ex-fta) 1)))
  (check-equal? (select-rule ex-fta 'd 'q6) (list (list-ref (fta-labeled-rules ex-fta) 3)))
  (check-equal? (select-rule ex-fta '(a b c d) 'q1) '()))


(define (leaf? node) (or (not (list? node)) (empty? (cdr node))))
(define (leftchild node) (cadr node))
(define (child-siblings node) (cddr node))
(define (error) (shift k #f))
(define (or/error x) (or x (error)))
#;(define (select-or-error f xs) (let ([xs (filter f xs)]) (if (empty? xs) (error) xs)))
(define (match-empty fta state)
  #;(select-or-error (λ (r) (eq? state (empty-rule-final-state r))) (fta-empty-rules fta))
  (or/error (for/or ([r (fta-empty-rules fta)]) (eq? state (empty-rule-final-state r)))))
(define-syntax-rule (combine-result child-result sibling-result) (and child-result sibling-result))
(define (match-with-rule fta rule node siblings state)
  (let ([qin (label-rule-in-state rule)]
        [qout (label-rule-out-state rule)])
    (begin
     (if (leaf? node)
         (match-empty fta qin)
         (match-node fta (leftchild node) (child-siblings node) qin))
     (if (empty? siblings)
         (match-empty fta qout)
         (match-node fta (car siblings) (cdr siblings) qout)))))

(define (match-node fta node siblings state)
  #;(for/or ([r (select-or-error (λ (r) (rule-match? fta r node state)) (fta-labeled-rules fta))])
    (reset (match-with-rule fta r node siblings state)))
  (or/error
   (for/or ([r (filter (λ (r) (rule-match? fta r node state)) (fta-labeled-rules fta))])
    (reset (match-with-rule fta r node siblings state)))))

(module+ test
  (check-not-false (match-node ex-fta '(a b c d) '() 'q0))
  (check-not-false (match-node ex-fta 'b '(c d) 'q1))
  (check-not-false (match-node ex-fta 'd '() 'q6))
  
  (check-false (match-node ex-fta '(a b) '() 'q0))
  (check-false (match-node ex-fta '(a c) '() 'q0))
  )

;---
; interface

(define (trx-match aut tree) #f)
(define-syntax-rule (trx rte)
  #f)

(module+ test
  #;(check-not-false (trx-match (trx 'a) 'a)))
