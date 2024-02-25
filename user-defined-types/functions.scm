#| -*-Scheme-*-

Copyright (C) 2019, 2020, 2021 Chris Hanson and Gerald Jay Sussman

This file is part of SDF.  SDF is software supporting the book
"Software Design for Flexibility", by Chris Hanson and Gerald Jay
Sussman.

SDF is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

SDF is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with SDF.  If not, see <https://www.gnu.org/licenses/>.

|#

;;; The resulting predicate represents a "function space" for the
;;; given sets.
(define function-predicate-codomain
  (predicate-template-accessor 'codomain function-template))

(define (simple-function-codomain function)
  (function-predicate-codomain
   (simple-function-predicate function)))

(define (simple-function-arity function)
  (length (simple-function-domains function)))

(define (apply-union-function function args)
  (let ((fit (union-function-apply-fit function args)))
    (if (not fit)
        (error 'apply-union-function "Inapplicable functio" function args))
    (fit)))

(define make-function-predicate
  (predicate-template-instantiator function-template))

(define function-predicate?
  (predicate-template-predicate function-template))

(define (function-predicate-arity predicate)
  (length (function-predicate-domains predicate)))

(define (extend-function-predicate domain-extender
                                   codomain-extender
                                   function-predicate)
  (make-function-predicate
   (map domain-extender
        (function-predicate-domains function-predicate))
   (codomain-extender
    (function-predicate-codomain function-predicate))))

(define (selectively-extend-function-predicate domain-extender
                                               codomain-extender
                                               function-predicate
                                               selector)
  (let ((maybe-map
         (lambda (extender)
           (lambda (select? predicate)
             (if select?
                 (extender predicate)
                 predicate)))))
    (make-function-predicate
     (map (maybe-map domain-extender)
          (selector 'domains)
          (function-predicate-domains function-predicate))
     ((maybe-map codomain-extender)
      (selector 'codomain)
      (function-predicate-codomain function-predicate)))))

(define (make-signature-selector arity domain-index
                                 codomain-index)
  (guarantee nonnegative? arity)
  (guarantee (index-predicate arity) domain-index)
  (guarantee (index-predicate 1) codomain-index)
  (lambda (operator)
    (case operator
      ((domains) (index->booleans domain-index arity))
      ((codomain) (car (index->booleans codomain-index 1)))
      (else (error "Unknown operator:" operator)))))


;;;; Union functions

(define (union-function-name union)
  `(union
    ,@(map simple-function-name
           (union-function-components union))))

(define (union-function-predicate union)
  (let ((predicates
         (map simple-function-predicate
              (union-function-components union))))
    (make-function-predicate (apply map
                                    disjoin
                                    (map function-predicate-domains
                                         predicates))
                             (disjoin*
                              (map function-predicate-codomain
                                   predicates)))))
;;;; Functions

(define (apply-function function args)
  (apply function args))

(define (function-name function)
  (cond ((simple-function? function)
         (simple-function-name function))
        ((union-function? function)
         (union-function-name function))
        (else
         (error:not-a function? function))))

(define (function-tag function)
  (cond ((simple-function? function)
         (simple-function-tag function))
        ((union-function? function)
         (predicate->tag (union-function-predicate function)))
        (else
         (error:not-a function? function))))

(define (function-predicate function)
  (tag->predicate (function-tag function)))



(define (map-function procedure function)
  (union-function*
   (map procedure (function-components function))))

(define (append-map-function procedure function)
  (union-function*
   (append-map procedure (function-components function))))

;;;; Simple functions


(define (make-simple-function name predicate procedure)
  (letrec
      ((function
        (make-object-applicable
         predicate
         (make-simple-function-metadata name procedure)
         (lambda args (apply-simple-function function args)))))
    function))


(define (apply-simple-function function args)
  (let ((fit (simple-function-apply-fit function args)))
    (if (not fit)
        (error "Inapplicable functio" function args))
    (fit)))

(define (simple-generic-function? object)
  (and (simple-function? object)
       (generic-procedure? (simple-function-procedure object))))

(define func-sgf (begin
		   (register-predicate! simple-generic-function?
					'simple-generic-function)
		   
		   (set-predicate<=! simple-generic-function? simple-function?)
		   
		   (define-generic-procedure-handler value-restriction
		     (match-args simple-generic-function? predicate?)
		     (lambda (value predicate)
		       (let ((handlers
			      (filter predicate
				      (generic-procedure-handlers
				       (simple-function-procedure value)))))
			 (and (pair? handlers)
			      (lambda ()
				(union-function* handlers))))))))

;;;; Endo-functions

(define (endo-function-predicate? object)
  (and (function-predicate? object)
       (let ((domains (function-predicate-domains object)))
         (and (pair? domains)
              (eqv? (car domains)
                    (function-predicate-codomain object))
              (null? (cdr domains))))))

(define func-efp (begin
		   (register-predicate! endo-function-predicate?
                     'endo-function-predicate)
		   (set-predicate<=! endo-function-predicate? function-predicate?)))

(define (make-endo-function-predicate domain)
  (make-function-predicate (list domain) domain))

(define (endo-function-predicate-domain predicate)
  (guarantee endo-function-predicate? predicate)
  (car (function-predicate-domains predicate)))

(define (simple-endo-function? object)
  (and (simple-function? object)
       (endo-function-predicate?
        (simple-function-predicate object))))

(define func-sef (begin
		   (register-predicate! simple-endo-function? 'simple-endo-function)
		   (set-predicate<=! simple-endo-function? simple-function?)))

(define (simple-endo-function-domain function)
  (endo-function-predicate-domain
   (simple-function-predicate function)))

;;;; Union functions

(define (union-function function . functions)
  (union-function* (cons function functions)))

(define func-uf (define-generic-procedure-handler value-restriction
		  (match-args union-function? predicate?)
		  (lambda (value predicate)
		    (let ((components
    		   (filter predicate
				   (union-function-components value))))
		      (and (pair? components)
			   (lambda () (union-function* components)))))))


