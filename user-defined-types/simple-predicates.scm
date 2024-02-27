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
;;; predicates的部分 2024年1月30日22:35:04
;;;; Basic tag structure
;;; 原predicate的简单替换 2024年1月30日21:31:23
(define predicate->tag get-predicate-metadata) ;common 中 pred-md-get 的简单替换 从metadata实现的pred中取东西出来.  2024年1月10日21:39:59

(define tag?
  (simple-generic-procedure 'tag? 1
			    (constant-generic-procedure-handler #f)))

(define get-tag-shared
  (simple-generic-procedure 'get-tag-shared 1 #f))

(define (define-tag-type predicate get-shared) 	;对各个不同的tag扩展其get-tag-shared gp 的过程... 2024年2月3日17:44:12
  (define-generic-procedure-handler tag? (match-args predicate)
    (lambda (object)
      ;; (declare (ignore object))
      #t))
  (define-generic-procedure-handler get-tag-shared
    (match-args predicate)
    get-shared))

(define-record-type (<tag-shared> %make-tag-shared tag-shared?)
  (fields (immutable name tag-shared-name)
	   (immutable predicate tag-shared-predicate)
	   (immutable constructor tag-shared-constructor)
	   (immutable accessor tag-shared-accessor)
	  (immutable supersets tag-shared-supersets)
	  )
  )

(define (tag-name tag)
  (tag-shared-name (get-tag-shared tag)))

(define (tag->predicate tag)
  (tag-shared-predicate (get-tag-shared tag)))

(define (tag-constructor tag)
  (tag-shared-constructor (get-tag-shared tag)))

(define (tag-accessor tag)
  (tag-shared-accessor (get-tag-shared tag)))

(define (tag-supersets tag)
  (tag-shared-supersets (get-tag-shared tag)))

(define (tags->predicates tags)
  (map tag->predicate tags))

(define (get-tag-supersets tag)
  (((tag-supersets tag) 'get-elements)))

(define (get-all-tag-supersets tag)
  (let loop ((queue (list tag))
	     (supersets '()))
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

(define (make-tag-shared name predicate constructor accessor)
  (guarantee procedure? predicate 'make-tag-shared)
  (guarantee procedure? constructor 'make-tag-shared)
  (guarantee procedure? accessor 'make-tag-shared)
  (%make-tag-shared name predicate constructor accessor
                    (make-weak-eq-set)))

(define (%invoke-tagging-strategy tagging-strategy name data-test
                                  maker)
  (tagging-strategy			;比如tagging-strategy:never,传入构造器和参数,返回构造的结果,即tag
   name
   data-test
   (lambda (predicate constructor accessor)  ;tagging-strategy:never 需要的make-tag,constructor已经定义在其中,而accessor是λ:x->x
     (let ((tag
            (maker			;构造simple-tag的maker,所以构造一个槽子是record的record的目的何在??? 2024年2月3日17:33:05
             (make-tag-shared name predicate constructor ;构造tag-shared的构造器...
                              accessor)))) ;
       (set-predicate-metadata! predicate tag) ;建立了md的k pred v tag关联
       tag))))

;;;; Simple predicates
(define-record-type (<simple-tag> %make-simple-tag simple-tag?)
  (fields (immutable shared simple-tag-shared)))

;; (define-tag-record-printer <simple-tag>)  ;为了避免出现lib化报语法错误的权宜之计.... 2024年2月3日17:48:18

(define tagging-st (define-tag-type simple-tag? simple-tag-shared))

(define (make-simple-tag name data-test tagging-strategy)
  (%invoke-tagging-strategy tagging-strategy name data-test
                            %make-simple-tag))

(define (simple-predicate? object)
  (and (predicate? object)
       (simple-tag? (predicate->tag object))))

(define (make-simple-predicate name data-test tagging-strategy)	;从tag-rtd中获取pred
  (tag->predicate
   (make-simple-tag name data-test tagging-strategy)))

(define (simple-abstract-predicate name data-test)
  (make-simple-predicate name data-test tagging-strategy:always))

(define (register-predicate! predicate name) ;predicate-metadata.scm 当中已经定义过了,这里覆盖了,之前的版本只是构造mdht中的name pred键值对,单纯的原生谓词,无法构造结构和层次.这里没有明显的put,不知道怎么能和之前的md起作用 2024年1月20日18:30:17
  (guarantee procedure? predicate)
  (make-simple-predicate name predicate tagging-strategy:never))

(define pred-reg
  (begin
    (register-predicate! tagged-data? 'tagged-data)
    (register-predicate! tag? 'tag)
    (register-predicate! predicate? 'predicate)
    (register-predicate! simple-predicate? 'simple-predicate)))

(define (predicate-name predicate)	;这里的pred是md  2024年2月16日21:21:21
  (tag-name (predicate->tag predicate)))

(define (parametric-predicate? object)
  (and (predicate? object)
       (parametric-tag? (predicate->tag object))))

(define (predicate-constructor predicate)
  (tag-constructor (predicate->tag predicate)))

(define (predicate-accessor predicate)
  (tag-accessor (predicate->tag predicate)))

(define (predicate-supersets predicate)
  (map tag->predicate
       (get-tag-supersets (predicate->tag predicate))))

(define (all-predicate-supersets predicate)
  (map tag->predicate
       (get-all-tag-supersets (predicate->tag predicate))))

;;; 用来判断标签1是否是标签2的子集
(define (false-tag<= tag1 tag2) ;; (declare (ignore tag1 tag2)),values的部分 使用了下面的过程,这个定义应该没必要. 2024年2月18日20:42:26
  ;; predicates文件引用了这个过程,用来扩展多个gp 2024年2月19日19:03:27
  #f)
 
(define generic-tag<=
  (simple-generic-procedure 'generic-tag<= 2 false-tag<=))

(define (uncached-tag<= tag1 tag2)
  (or (eqv? tag1 tag2)
      (generic-tag<= tag1 tag2)
      (any (lambda (tag)
             (cached-tag<= tag tag2))
           (get-tag-supersets tag1))))

(define tag<=-cache
  (make-equal-hash-table))

(define (cached-tag<= tag1 tag2)
  (hash-table-intern! tag<=-cache
                      (cons tag1 tag2)
                      (lambda () (uncached-tag<= tag1 tag2))))

(define (tag<= tag1 tag2)		;这个东西..  2024年1月20日22:04:07
  (guarantee tag? tag1)
  (guarantee tag? tag2)
  (cached-tag<= tag1 tag2))

(define (tag>= tag1 tag2)
  (tag<= tag2 tag1))

(define (tag= tag1 tag2)
  (guarantee tag? tag1)
  (guarantee tag? tag2)
  (eqv? tag1 tag2))

(define (set-tag<=! tag superset)
  (if (tag>= tag superset)
      (error 'set-tag<=! "Not allowed to create a superset loop:"
             tag superset))
  (if (not (tag<= tag superset))
      (((tag-supersets tag) 'add-element!) superset))
  (hash-table-clear! tag<=-cache))

(define (predicate<= predicate1 predicate2)
  (tag<= (predicate->tag predicate1)
         (predicate->tag predicate2)))

(define (predicate>= predicate1 predicate2)
  (predicate<= predicate2 predicate1))

(define (predicate= predicate1 predicate2)
  (tag= (predicate->tag predicate1)
        (predicate->tag predicate2)))

(define (set-predicate<=! predicate superset)
  (set-tag<=! (predicate->tag predicate)
              (predicate->tag superset)))

(define any-object? (conjoin))
(define no-object? (disjoin))

(define simple-pred-rl
  (begin
    (register-predicate! simple-tag? 'simple-tag)
    (set-predicate<=! simple-tag? tag?)
    (set-predicate<=! simple-predicate? predicate?))
  )
