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


;;;; Compound predicates
(define-record-type (<compound-tag> %make-compound-tag compound-tag?)
  (fields (immutable shared compound-tag-shared)
	  (immutable operator compound-tag-operator)
	  (immutable components compound-tag-components))
    )

(define ct    
  (begin
    (define-tag-type compound-tag? compound-tag-shared)))

;; (define-tag-record-printer <compound-tag>)
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


(define compound-reg
  (begin
    (register-predicate! compound-tag? 'compound-tag)
    (set-predicate<=! compound-tag? tag?)
    (register-predicate! compound-predicate? 'compound-predicate)
    (set-predicate<=! compound-predicate? predicate?)
    
    ))

;; Needed by code in common.
;; (define udp-predicates-store (make-alist-store eq?)) ;这个应该可以换成hash  2024年2月22日17:58:32
(define udp-predicates-store (make-hash-table-store make-key-weak-eq-hash-table)) 

(define have-compound-operator-registrar? (udp-predicates-store 'has?))
(define get-compound-operator-registrar (udp-predicates-store 'get))
(define define-compound-operator-registrar (udp-predicates-store 'put!))

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

(define (maybe-register-compound-predicate! datum-test
                                            operator operands)
  (if (every predicate? operands)
      (register-compound-predicate! datum-test operator operands)
      datum-test))

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
    (lambda (data-test operator tags)
      (standard-compound-tag data-test operator tags))))

(define (is-list-of predicate)		;对register-compound-predicate!的简单封装,变成仅支持扩展list形式的谓词,比如苹果类型,组件谓词可以是水果 木本 被子植物
  (guarantee predicate? predicate)
  (register-compound-predicate! (lambda (object) ;这个过程是个md谓词,判断传入的obj的任意list组件是否符合全部pred 2024年1月15日19:45:03
                                  (and (list? object)
                                       (every predicate object))) ;就guarantee在不出现意外时候返回object本身这件事来看,这里的pred可以直接用上面的表达式替换 2024年1月15日19:36:17
                                'is-list-of
                                (list predicate)))

(define (is-non-empty-list-of predicate) ;非空且有至少两个元素? 2024年1月15日19:47:21
  (guarantee predicate? predicate)
  (register-compound-predicate! (lambda (object)
                                  (and (pair? object)
                                       (list? (cdr object))
                                       (every predicate object)))
                                'is-non-empty-list-of
                                (list predicate)))

(define (is-pair-of car-predicate cdr-predicate)
  (guarantee predicate? car-predicate)
  (guarantee predicate? cdr-predicate)
  (register-compound-predicate!
   (lambda (object)
     (and (pair? object)
          (car-predicate (car object))
          (cdr-predicate (cdr object))))
   'is-pair-of
   (list car-predicate cdr-predicate)))

(define (complement predicate)		;谓词的补语 2024年1月15日19:50:07
  (maybe-register-compound-predicate!
   (lambda (object)
     (not (predicate object)))
   'complement
   (list predicate)))

(define (disjoin . predicates)
  (disjoin* predicates))

(define (disjoin* predicates)		;谓词的析取 2024年1月15日19:56:13
  (maybe-register-compound-predicate!
   (lambda (object)
     (any (lambda (predicate)
            (predicate object))
          predicates))
   'disjoin
   predicates))

(define (conjoin . predicates)		;谓词的合取 2024年1月15日19:57:39
  (conjoin* predicates))

(define (conjoin* predicates)
  (maybe-register-compound-predicate!
   (lambda (object)
     (every (lambda (predicate)
              (predicate object))
            predicates))
   'conjoin
   predicates))

(define disjunction? (compound-predicate-predicate 'disjoin))
(define conjunction? (compound-predicate-predicate 'conjoin))

(define pred-llpc (begin
		    (register-predicate! disjunction? 'disjunction)
		    (register-predicate! conjunction? 'conjunction)
		    (set-predicate<=! disjunction? compound-predicate?)
		    (set-predicate<=! conjunction? compound-predicate?)
		    
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

(define (top-tag? object) (eqv? top-tag object))
(define (bottom-tag? object) (eqv? bottom-tag object))

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

(define (true-tag<= tag1 tag2) ;; (declare (ignore tag1 tag2))
  #t)

(define any-object? (conjoin))
(define no-object? (disjoin))

(define top-tag (predicate->tag any-object?))
(define bottom-tag (predicate->tag no-object?))

(define (non-top-tag? object) (not (top-tag? object)))

(define (non-bottom-tag? object) (not (bottom-tag? object)))

;;;; Parametric predicates

;; (define (define-tag-record-printer record-type)
;;   (define-record-printer record-type
;;     (lambda (tag) (list (tag-name tag)))))

;;;; Generic tag operations

(define (cached-tag>= tag1 tag2)
  (cached-tag<= tag2 tag1))

;; These will be modified below.
(define (define-tag<= predicate1 predicate2 handler)  ;扩展了taggin中的generic-tag<=,但是只用于了 parametric-tag? 和 compound-tag
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


;;; 应该得用上面这个把与或非三件套重新定义一下. 2024年2月27日21:16:06

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
					   (every (case (parameter-binding-polarity ;templates中定义的  2024年2月24日20:07:22
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
		  ))
