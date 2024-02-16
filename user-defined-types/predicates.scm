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

;;;; Predicate registration


;; Needed by code in common


;; Needed by code in common.
(define (register-compound-predicate! joint-predicate operator ;这个也不同于predicate-metadata.scm 2024年1月20日18:30:58
                                      components)
  (guarantee procedure? joint-predicate)
  (guarantee have-compound-operator-registrar? operator)
  (guarantee list? components)
  (tag->predicate
   ((get-compound-operator-registrar operator)
    joint-predicate
    operator
    (map predicate->tag components))))

(define (simple-abstract-predicate name data-test)
  (make-simple-predicate name data-test tagging-strategy:always))

(define udp-predicates-store (make-alist-store eq?))

(define have-compound-operator-registrar? (udp-predicates-store 'has?))
(define get-compound-operator-registrar (udp-predicates-store 'get))
(define define-compound-operator-registrar (udp-predicates-store 'put!))

(define (make-compound-tag name data-test tagging-strategy
                           operator components)
  (%invoke-tagging-strategy tagging-strategy name data-test
                            (lambda (shared)
                              (%make-compound-tag shared
                                                  operator
                                                  components))))

(define (standard-compound-tag data-test operator components)
  (make-compound-tag (cons operator (map tag-name components))
                     data-test
                     tagging-strategy:optional
                     operator
                     components))

(define (make-listish-memoizer)
  (simple-list-memoizer eq?
    (lambda (data-test operator tags)
      ;; (declare (ignore data-test operator))
      tags)
    (lambda (data-test operator tags)parametric-tag?
	    (standard-compound-tag data-test operator tags))))

(define pred-llpc (begin
		  (define-compound-operator-registrar 'is-list-of
		    (make-listish-memoizer))

		  (define-compound-operator-registrar 'is-non-empty-list-of
		    (make-listish-memoizer))

		  (define-compound-operator-registrar 'is-pair-of
		    (make-listish-memoizer))

		  (define-compound-operator-registrar 'complement
		    (make-listish-memoizer))))

(define (joinish wrap-constructor)
  (let ((memoizer
         (simple-lset-memoizer eq?
           (lambda (data-test operator tags post-process)
             ;; (declare (ignore data-test operator post-process))
             tags)
           (lambda (data-test operator tags post-process)
             (let ((joint-tag
                    (standard-compound-tag data-test
                                           operator
                                           tags)))
               (post-process joint-tag tags)
               joint-tag)))))
    (lambda (data-test operator tags)
      (let ((tags
             (delete-duplicates
              (append-map
               (lambda (tag)
                 (if (and (compound-tag? tag)
                          (eq? operator
                               (compound-tag-operator tag)))
                     (compound-tag-components tag)
                     (list tag)))
               tags)
              eq?)))
        (if (and (pair? tags) (null? (cdr tags)))
            (car tags)
            (wrap-constructor
             tags
             (lambda (post-process)
               (memoizer data-test operator tags
                         post-process))))))))

(define (true-tag<= tag1 tag2) ;; (declare (ignore tag1 tag2))
  #t)

(define any-object? (conjoin))
(define no-object? (disjoin))

(define top-tag (predicate->tag any-object?))
(define bottom-tag (predicate->tag no-object?))

(define (top-tag? object) (eqv? top-tag object))
(define (non-top-tag? object) (not (top-tag? object)))

(define (bottom-tag? object) (eqv? bottom-tag object))
(define (non-bottom-tag? object) (not (bottom-tag? object)))

(define pred-cor (begin
		   (define-compound-operator-registrar 'disjoin
		     (joinish
		      (lambda (tags continue)
			(or (find top-tag? tags)
			    (continue
			     (lambda (joint-tag tags)
			       (for-each (lambda (tag)
					   (set-tag<=! tag joint-tag))
					 tags)))))))

		   (define-compound-operator-registrar 'conjoin
		     (joinish
		      (lambda (tags continue)
			(or (find bottom-tag? tags)
			    (continue
			     (lambda (joint-tag tags)
			       (for-each (lambda (tag)
					   (set-tag<=! joint-tag tag))
					 tags)))))))
		   ))

;;;; Simple predicates

(define (simple-predicate? object)
  (and (predicate? object)
       (simple-tag? (predicate->tag object))))

;;;; Compound predicates

(define (compound-predicate? object)
  (and (predicate? object)
       (compound-tag? (predicate->tag object))))

(define (compound-predicate-components predicate)
  (map tag->predicate
       (compound-tag-components (predicate->tag predicate))))

(define (compound-predicate-predicate operator)
  (lambda (object)
    (and (predicate? object)
         (let ((tag (predicate->tag object)))
           (and (compound-tag? tag)
                (eq? operator (compound-tag-operator tag)))))))

(define disjunction? (compound-predicate-predicate 'disjoin))
(define conjunction? (compound-predicate-predicate 'conjoin))

;;;; Parametric predicates

;; (define (define-tag-record-printer record-type)
;;   (define-record-printer record-type
;;     (lambda (tag) (list (tag-name tag)))))

;;;; Generic tag operations
(define (get-all-tag-supersets tag)
  (let loop ((queue (list tag)) (supersets '()))
    (if (pair? queue)
        (let ((tag (car queue))
              (queue (cdr queue)))
          (let ((new-sets
                 (lset-difference eqv?
                                  (get-tag-supersets tag)
                                  supersets)))
            (if (pair? new-sets)
                (loop (append new-sets queue)
                      (append new-sets supersets))
                (loop queue supersets))))
        supersets)))

(define (all-predicate-supersets predicate)
  (map tag->predicate
       (get-all-tag-supersets (predicate->tag predicate))))

(define (cached-tag>= tag1 tag2)
  (cached-tag<= tag2 tag1))

;; These will be modified below.

(define (define-tag<= predicate1 predicate2 handler)
  (define-generic-procedure-handler generic-tag<=
    (match-args predicate1 predicate2)
    handler))

(define (tag-data predicate data)
  ((predicate-constructor predicate) data))
;;;; Registrations for this file

;; These must be the first registrations!


;; Now that we've got those objects, we can properly set the top
;; and bottom tags.
;; (set! top-tag (predicate->tag any-object?))
;; (set! bottom-tag (predicate- >tag no-object?))
(define (maybe-register-compound-predicate! datum-test
                                            operator operands)
  (if (every predicate? operands)
      (register-compound-predicate! datum-test operator operands)
      datum-test))

(define pred-rp (begin

		  (define-tag<= bottom-tag? tag? true-tag<=)
		  (define-tag<= tag? top-tag? true-tag<=)

		  (define-tag<= non-bottom-tag? bottom-tag? false-tag<=)
		  (define-tag<= top-tag? non-top-tag? false-tag<=)

		  (define-tag<= parametric-tag? parametric-tag?
		    (lambda (tag1 tag2)
		      (and (eqv? (parametric-tag-template tag1)
				 (parametric-tag-template tag2))
			   (every (lambda (bind1 bind2)
				    (let ((tags1 (parameter-binding-values bind1))
					  (tags2 (parameter-binding-values bind2)))
				      (and (= (length tags1) (length tags2))
					   (every (case (parameter-binding-polarity
							 bind1)
						    ((+) cached-tag<=)
						    ((-) cached-tag>=)
						    (else tag=))
						  tags1
						  tags2))))
				  (parametric-tag-bindings tag1)
				  (parametric-tag-bindings tag2)))))

		  (define-tag<= compound-tag? compound-tag?
		    (lambda (tag1 tag2)
		      (cond ((and (eq? 'disjoin (compound-tag-operator tag1))
				  (eq? 'disjoin (compound-tag-operator tag2)))
			     (every (lambda (component1)
				      (any (lambda (component2)
					     (tag<= component1 component2))
					   (compound-tag-components tag2)))
				    (compound-tag-components tag1)))
			    ;; TODO(cph): add more rules here.
			    (else #f))))
		  
		  (register-predicate! predicate? 'predicate)
		  (register-predicate! simple-predicate? 'simple-predicate)
		  (register-predicate! compound-predicate? 'compound-predicate)

		  (register-predicate! disjunction? 'disjunction)
		  (register-predicate! conjunction? 'conjunction)

		  (set-predicate<=! simple-predicate? predicate?)
		  (set-predicate<=! compound-predicate? predicate?)
		  (set-predicate<=! parametric-predicate? predicate?)
		  (set-predicate<=! disjunction? compound-predicate?)
		  (set-predicate<=! conjunction? compound-predicate?)

		  (register-predicate! tag? 'tag)

		  (register-predicate! simple-tag? 'simple-tag)
		  (register-predicate! compound-tag? 'compound-tag)
		  (register-predicate! parametric-tag? 'parametric-tag)

		  (set-predicate<=! simple-tag? tag?)

		  (set-predicate<=! compound-tag? tag?)
		  (set-predicate<=! parametric-tag? tag?)

		  (register-predicate! tagged-data? 'tagged-data)))
