#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Lfun.rkt")
(require "interp-Cfun.rkt")
(require "type-check-Lfun.rkt")
(require "interp-Lwhile.rkt")
(require "type-check-Lwhile.rkt")
(require "type-check-Lif.rkt")
(require "interp.rkt")
(require "compiler.rkt")

(debug-level 1)
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

;; The following tests the intermediate-language outputs of the passes.
(interp-tests "functions" type-check-Lfun compiler-passes interp-Lfun "functions_test" (tests-for "functions"))

;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
;; (compiler-tests "vectors" type-check-Lvec compiler-passes "vectors_test" (tests-for "vectors"))
