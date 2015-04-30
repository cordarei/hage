#lang racket/base

(require hage/parser)
(provide (all-from-out hage/parser))

(define (tree-traverse tree visit initial-state)
  (if (leaf? tree)
      (visit tree initial-state empty)
      (visit tree
             initial-state
             (???))))
