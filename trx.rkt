;; ===================================================================================================
;; Implements a matcher for regular tree expressions
;;   based on Ilya Bagrak and Olin Shivers (2004) 'trx: Regular-tree expressions, now in Scheme'.

#lang racket

(require racket/control)
(require racket/generator)

(module+ test
  (require rackunit))


;; ---------------------------------------------------------------------------------------------------
;; automata

;; the record type that holds a compiled tree automaton
(struct fta
  (states
   alphabet
   labeled-rules
   empty-rules
   final-states
   special-states
   submatch-states) #:transparent)

;; a non-empty rule: f(q_in)q_out -> q
(struct labeled-rule
  (sym-name
  in-state
  out-state
  final-state) #:transparent)

;; an empty rule: () -> q
(struct empty-rule
  (final-state) #:transparent)

;; symbol for epsilon rules
(define epsilon (gensym))
;; special symbol for matching unlabeled trees
(define unlabeled-tree (gensym))

(module+ test
  ;; example fta that matches (a b c d) and no other tree
  (define ex-fta
    (fta '(q0 q1 q2 q3 q4 q6)
         '(a b c d)
         (list (labeled-rule 'a 'q1 'q2 'q0)
               (labeled-rule 'b 'q2 'q4 'q1)
               (labeled-rule 'c 'q2 'q6 'q4)
               (labeled-rule 'd 'q2 'q2 'q6))
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
  (let* ([q (labeled-rule-final-state rule)]
        [f (labeled-rule-sym-name rule)]
        [n.label (cond
                   [(eq? f unlabeled-tree) f]
                   [(eq? f epsilon) f]
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

#;
(define (select-rule fta node state)
  (filter (λ (r) (rule-match? fta r node state))
          (fta-labeled-rules fta)))

#;
(module+ test
  (check-equal? (select-rule ex-fta '(a b c d) 'q0) (list (list-ref (fta-labeled-rules ex-fta) 0)))
  (check-equal? (select-rule ex-fta 'b 'q1) (list (list-ref (fta-labeled-rules ex-fta) 1)))
  (check-equal? (select-rule ex-fta 'd 'q6) (list (list-ref (fta-labeled-rules ex-fta) 3)))
  (check-equal? (select-rule ex-fta '(a b c d) 'q1) '()))


(define (leaf? node) (or (not (list? node)) (empty? (cdr node))))
(define (children node (labeled #t))
  (cond
    [(not (list? node)) '()]
    [(not labeled) node]
    [else (cdr node)]))
(define (leftchild node) (cadr node))
(define (child-siblings node) (cddr node))

(define (error) (shift k #f))
(define-syntax (or/err stx)
  (syntax-case stx ()
    [(_ bodies ...) #'(or bodies ... (error))]))

(define (epsilon-closure fta state)
  (let loop ([estates (list state)])
    (define estates*
      (set-union estates
                 (map (λ (r) (labeled-rule-out-state r))
                      (filter (λ (r) (and (eq? epsilon (labeled-rule-sym-name r))
                                          (eq? state (labeled-rule-final-state r))))
                              (fta-labeled-rules fta)))))
    (if (set=? estates estates*)
        estates
        (loop estates*))))

(define (match-empty fta state)
  (or/err
   (not (empty? (set-intersect (epsilon-closure fta state)
                               (map empty-rule-final-state (fta-empty-rules fta)))))))

(define-syntax-rule (combine-result child-result sibling-result) (begin child-result sibling-result))

(define (match-with-rule fta rule node siblings state)
  (match rule
    [(labeled-rule f qin qout _)
     (define cs (children node (not (eq? unlabeled-tree f))))
     (combine-result
      (if (null? cs)
          (match-empty fta qin)
          (match-node fta (car cs) (cdr cs) qin))
      (if (empty? siblings)
         (match-empty fta qout)
         (match-node fta (car siblings) (cdr siblings) qout)))]))

(define (match-node fta node siblings state)
  ;; predicates for partitioning rules
  (define matches? (λ (r) (rule-match? fta r node state)))
  (define repeats? (λ (r) (eq? (labeled-rule-out-state r) (labeled-rule-final-state r))))
  (define eps? (λ (r) (eq? epsilon (labeled-rule-sym-name r))))
  (define neither? (λ (r) (not (or (repeats? r) (eps? r)))))
  
  (let ()
    (define matching-rules (filter matches? (fta-labeled-rules fta)))
    (define-values (epsilon-rules non-epsilon-rules) (partition eps? matching-rules))
    (define reordered-rules (let-values ([(a b) (partition repeats? non-epsilon-rules)]) (append a b)))
    (or/err
     (for/or ([r reordered-rules])
       (reset (match-with-rule fta r node siblings state)))
     (for/or ([r epsilon-rules])
       (reset (match-node fta node siblings (labeled-rule-out-state r))))))
  
;  ;; partition and reorder rules lazily
;  (define matching-rules (stream-filter matches? (fta-labeled-rules fta)))
;  (define repeating-rules (stream-filter repeats? matching-rules))
;  (define epsilon-rules (stream-filter eps? matching-rules))
;  (define neither-rules (stream-filter neither? matching-rules))
;  (define reordered-rules (stream-append repeating-rules neither-rules epsilon-rules))
;
;  (or/error
;   (for/or ([r (in-stream reordered-rules)])
;    (reset (match-with-rule fta r node siblings state))))
  )

(module+ test
  (check-not-false (match-node ex-fta '(a b c d) '() 'q0))
  (check-not-false (match-node ex-fta 'b '(c d) 'q1))
  (check-not-false (match-node ex-fta 'd '() 'q6))
  (check-false (match-node ex-fta '(a b) '() 'q0))
  (check-false (match-node ex-fta '(a c) '() 'q0)))

;; run automaton fta against tree
(define (fta-match fta tree)
  (for/or ([q (fta-final-states fta)])
    (reset (match-node fta tree '() q))))

(module+ test
  (check-not-false (fta-match ex-fta '(a b c d)))
  (check-false (fta-match ex-fta '(b d)))
  (check-false (fta-match ex-fta 'b))
  (check-false (fta-match ex-fta '(a b c)))
  (check-false (fta-match ex-fta '(a c b d)))
  
  ;; =/= (rec q (| 1 (@ + (+ q))))
  (define complex-fta
    (fta null
         null
         (list (labeled-rule epsilon 'qe 'q1 'q0)
               (labeled-rule 1 'qe 'q2 'q1)
               (labeled-rule epsilon 'qe 'qe 'q2)
               (labeled-rule epsilon 'qe 'q4 'q0)
               (labeled-rule '+ 'q6 'q5 'q4)
               (labeled-rule epsilon 'qe 'qe 'q5)
               (labeled-rule epsilon 'qe 'q7 'q6)
               (labeled-rule epsilon 'qe 'q8 'q7)
               (labeled-rule 1 'qe 'q9 'q8)
               (labeled-rule epsilon 'qe 'q10' q9)
               (labeled-rule epsilon 'qe 'q7 'q10)
               (labeled-rule epsilon 'qe 'q11 'q7)
               (labeled-rule '+ 'q6 'q12 'q11)
               (labeled-rule epsilon 'qe 'q10 'q12))
         (list (empty-rule 'qe) (empty-rule 'q10))
         '(q0)
         null
         null))
  
  (check-not-false (fta-match complex-fta 1))
  (check-not-false (fta-match complex-fta '(+ 1 1 1)))
  (check-not-false (fta-match complex-fta '(+ 1 1 (+ 1))))
  )

;; ---------------------------------------------------------------------------------------------------
;; abstract syntax

;; literal atom or 'symbol
(struct ast-lit-node
  (literal
  private))

;; (@ symbol rte ...) or (symbol rte ...)
(struct ast-sym-node
  (symbol
  children
  private))

;; (^ rte ...)
(struct ast-unlabelled-node
  (children
   private))

;; (* rte ...) or (+ rte ...) or (? rte ...)
(struct ast-seq-node
  (quantifier
  child
  private))

;; (| rte ...)
(struct ast-choice-node
  (children
   private))

;;; compile

(define (ast->fta ast)
  ;(define (new-state) (gensym 'q))
  (define new-state (generator () (let loop ([i 0]) (begin (yield i) (loop (+ i 1)))) ))

  (define qf (new-state))
  (define empty-state (new-state))

  (define (make-rules label child-states transitions)
    (for*/list ([trans transitions]
                [child-state child-states])
      (match trans
        [`(,q ,qout)
          (labeled-rule label child-state qout q)])))

  (define (make-transitions current-state out-states repeat?)
    (for/fold ([trans (if repeat? `(,current-state ,current-state) '())])
              ([o out-states])
      (cons `(,current-state ,o) trans)))

  (define (compile-node ast-node current-state out-states [repeat? #f])

    (define (compile-children children) null)

    (match ast
      [(ast-lit-node lit priv)
       (values (list current-state)
               (make-rules lit (list empty-state) (make-transitions current-state out-states repeat?))
               '())]

      [(ast-seq-node quantifier child priv)
       (define-values (next-states lrules erules)
         (compile-node child out-states (not (eq? quantifier '?))))
       null
       ]
      )
    )

  (define-values (states rules emprules)
    ; return (values states rules emp-rules)
    (let loop ([ast ast] [qf qf] [qout empty-state])
      (match ast
        [(ast-lit-node lit priv)
         (values '()
                 (list (labeled-rule lit empty-state qout qf))
                 '())]

        [(ast-choice-node children priv)
         (for/fold ([child-states '()]
                    [child-rules '()]
                    [child-erules '()])
                   ([c children])
           (let-values ([(s r e) (loop c qf qout)])
             (values (append s child-states)
                     (append r child-rules)
                     (append e child-erules))))]

        [(ast-sym-node symbol children priv)
         (define-values (states rules erules in-state)
           (for/fold ([child-states '()]
                    [child-rules '()]
                    [child-erules '()]
                    [last-state empty-state])
                   ([c (reverse children)])
             (define q (new-state))
             (let-values ([(s r e) (loop c q last-state)])
               (values (append s child-states)
                       (append r child-rules)
                       (append e child-erules)
                       q))))
         (values states
                 (cons (labeled-rule symbol in-state qout qf)
                       rules)
                 erules)]

        [(ast-seq-node quantifier child priv)
         (unless (eq? quantifier '+) (raise-argument-error 'ast->fta '+ quantifier))

         (define-values (child-states child-rules child-erules)
           (loop child null null))
         (values null null null)]

        )))

  (fta states null rules (cons (empty-rule empty-state) emprules) (list qf) null null)
  )
#;
(module+ test

  ;;; sequences

  (check-not-false
   (fta-match (ast->fta (ast-sym-node 'a (list (ast-seq-node '+ (ast-lit-node 42 null) null)) null))
              '(a 42)))
  (check-not-false
   (fta-match (ast->fta (ast-sym-node 'a (list (ast-seq-node '+ (ast-lit-node 42 null) null)) null))
              '(a 42 42)))
  (check-not-false
   (fta-match (ast->fta (ast-sym-node 'a (list (ast-seq-node '+ (ast-lit-node 42 null) null)) null))
              '(a 42 42 42)))
  (check-false
   (fta-match (ast->fta (ast-sym-node 'a (list (ast-seq-node '+ (ast-lit-node 42 null) null)) null))
              '(a)))
  (check-false
   (fta-match (ast->fta (ast-sym-node 'a (list (ast-seq-node '+ (ast-lit-node 42 null) null)) null))
              '(a 42 1 42)))
  (check-false
   (fta-match (ast->fta (ast-sym-node 'a (list (ast-seq-node '+ (ast-lit-node 42 null) null)) null))
              '(a 42 42 42 'x)))

  (check-not-false
   (fta-match (ast->fta (ast-sym-node 'a (list (ast-seq-node '+ (ast-lit-node 42 null) null)
                                               (ast-lit-node 1 null)) null))
              '(a 1)))
  (check-not-false
   (fta-match (ast->fta (ast-sym-node 'a (list (ast-seq-node '+ (ast-lit-node 42 null) null)
                                               (ast-lit-node 1 null)) null))
              '(a 42 1)))
  (check-not-false
   (fta-match (ast->fta (ast-sym-node 'a (list (ast-seq-node '+ (ast-lit-node 42 null) null)
                                               (ast-lit-node 1 null)) null))
              '(a 42 42 1)))
  (check-false
   (fta-match (ast->fta (ast-sym-node 'a (list (ast-seq-node '+ (ast-lit-node 42 null) null)
                                               (ast-lit-node 1 null)) null))
              '(a 42 42)))
  )

;; ---------------------------------------------------------------------------------------------------
;; interface

(define (trx-match fta tree)
  #f)

(define-syntax-rule (trx rte)
  #f)

(module+ test
  #;(check-not-false (trx-match (trx 'a) 'a)))
