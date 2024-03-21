#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "interp-Lif.rkt")
(require "type-check-Lif.rkt")
(require "compiler.rkt")

;(debug-level 1)
(AST-output-syntax 'concrete-syntax)

;; all the files in the tests/ directory with extension ".rkt".
(define all-tests
  (map (lambda (p) (car (string-split (path->string p) ".")))
       (filter (lambda (p)
                 (string=? (cadr (string-split (path->string p) ".")) "rkt"))
               (directory-list (build-path (current-directory) "tests")))))

(define (tests-for r)
  (map (lambda (p)
         (caddr (string-split p "_")))
       (filter
        (lambda (p)
          (string=? r (car (string-split p "_"))))
        all-tests)))

(define test-class (vector-ref (current-command-line-arguments) 0))
(define test-family (string-append test-class "_test"))

;; The following tests the intermediate-language outputs of the passes.
(interp-tests "cond" type-check-Lif
              compiler-passes interp-Lif test-family (tests-for test-class))

;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
(compiler-tests "var" type-check-Lif compiler-passes test-family (tests-for test-class))
