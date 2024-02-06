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

(define-record-type (<tagged-data> %make-tagged-data tagged-data?)
  (fields (immutable tag tagged-data-tag) (immutable data tagged-data-data))
  )

(define (tagging-strategy:optional name data-test make-tag) ;data的tag和给定tag eq?时才加tag  2024年1月20日17:45:26

  (define (constructor data)
    (if (not (data-test data))
        (error 'tagging-strategy:optional (string-append "Ill-formed data for " (symbol->string name) ":")
               data))
    (if (eq? tag (get-tag data))	;这个tag哪来的? 2024年1月20日17:45:16
        data
        (%make-tagged-data tag data)))

  (define (predicate object)
    (or (and (tagged-data? object)
             (tag<= (tagged-data-tag object) tag)
             (data-test (tagged-data-data object)))
        (data-test object)))

  (define (accessor object)
    (if (tagged-data? object)
        (tagged-data-data object)
        object))

  (define tag
    (make-tag predicate constructor accessor))

  tag)

;;; taggs 的部分,得插在tagging的中间... 2024年2月1日21:22:07
(define (primitive-predicate name data-test)
  (if (not (predicate? data-test))
      (register-predicate! data-test name ;; (symbol 'n: name) 感觉没必要加n: 2024年1月19日21:00:00
			   ))
  (let ((predicate
         (make-simple-predicate name data-test
                                tagging-strategy:optional)))
    (set-predicate<=! data-test predicate) ;这个调用了一个348行的 set-tag<=! 在下面几个gp重定义谓词中,从number?开始就被error:not-a-type捕捉到异常 2024年1月20日12:17:38
    predicate))

;;;; Standard predicates

;;; This extends base-predicate to work for tagged data.  The
;;; constructor only wraps the data when the implementation tag
;;; is different.



;;; 下面的谓词前面全部都去掉了 n: 2024年1月19日21:00:45
;;; 然后因为define complex? 这种操作会导致complex?没有bound 前面全部加了gp- 2024年1月19日21:17:15
;; (define (boolean? b)
;;   (or (eq? #t b) (eq? #f b)))

(define gp-boolean?
  (primitive-predicate 'boolean boolean?))

(define gp-complex?
  (primitive-predicate 'complex complex?))

(define gp-exact-integer?
  (primitive-predicate 'exact-integer exact-integer?))

;; (define gp-exact-rational?
;;   (primitive-predicate 'exact-rational rational?))   mit才有的定义 2024年1月19日21:21:15

(define gp-inexact-real?
  (primitive-predicate 'inexact-real flonum?))

(define gp-integer?
  (primitive-predicate 'integer integer?))

(define gp-null?
  (primitive-predicate 'null null?))

(define gp-pair?
  (primitive-predicate 'pair pair?))

(define gp-rational?
  (primitive-predicate 'rational rational?))

(define gp-real?
  (primitive-predicate 'real real?))

(define gp-string?
  (primitive-predicate 'string string?))

(define gp-vector?
  (primitive-predicate 'vector vector?))

;;; 下面两个去掉了exact的部分  2024年1月19日21:24:47
(define gp-exact-nonnegative-integer?
  (primitive-predicate 'exact-nonnegative-integer
                       nonnegative?))

(define gp-exact-positive-integer?
  (primitive-predicate 'exact-positive-integer
                       positive?))

(define gp-list?
  (primitive-predicate 'list list?))

(define gp-non-empty-list?
  (primitive-predicate 'non-empty-list non-empty-list?))

(define gp-number?
  (primitive-predicate 'number number?)) ;number symbol? boolean? 这几个在predicate-metadata.scm 已经注册过了,由于predicates文件中的tag<= 报错 2024年1月19日21:43:45

(define gp-symbol?
  (primitive-predicate 'symbol symbol?))

(define taggs-relation (begin
			 (set-predicate<=! gp-complex? gp-number?)
			 ;; (set-predicate<=! gp-exact-integer? gp-integer?)
			 (set-predicate<=! gp-exact-nonnegative-integer? gp-integer?)
			 (set-predicate<=! gp-exact-positive-integer? gp-integer?)
			 ;; (set-predicate<=! gp-exact-rational? gp-rational?)
			 (set-predicate<=! gp-inexact-real? gp-real?)
			 (set-predicate<=! gp-integer? gp-rational?)
			 (set-predicate<=! gp-non-empty-list? gp-list?)
			 (set-predicate<=! gp-null? gp-list?)
			 (set-predicate<=! gp-rational? gp-real?)
			 (set-predicate<=! gp-real? gp-complex?)

			 (register-predicate! procedure? 'procedure)))

;;; 原predicate的简单替换 2024年1月30日21:31:23
(define predicate->tag get-predicate-metadata) ;从metadata实现的pred中取东西出来,给common的重命名了.  2024年1月10日21:39:59
;;; taggs的部分 2024年1月30日21:13:09
(define %object-tag-map
  (make-key-weak-eqv-hash-table))

(define (implementation-tag-helper pred name)
  (hash-table-intern! %object-tag-map name (lambda () (predicate->tag (register-predicate!  pred name)))))

(define implementation-tag		 ;由于没找到chez及R6RS获取obj type的方法,只能手撸一个 2024年1月21日17:33:25
  (let ((boolean-tag (predicate->tag gp-boolean?))
        (null-tag (predicate->tag gp-null?)))
    (lambda (object)
      (cond ((eq? object #t) boolean-tag)
            ((eq? object '()) null-tag)
	    ((pair? object) (implementation-tag-helper pair? 'pair))
	    ((integer? object) (implementation-tag-helper integer? 'integer))
	    ((rational? object) (implementation-tag-helper rational? 'rational))
	    ((real? object) (implementation-tag-helper real? 'real))
	    ((complex? object) (implementation-tag-helper complex? 'complex))
	    ((number? object) (implementation-tag-helper number? 'number))
	    ((char? object) (implementation-tag-helper char? 'char))
	    ((string? object) (implementation-tag-helper string? 'string))
	    ((vector? object) (implementation-tag-helper vector? 'vector))
	    ((symbol? object) (implementation-tag-helper symbol? 'symbol))
	    ((procedure? object) (implementation-tag-helper procedure? 'procedure))
	    ((bytevector? object) (implementation-tag-helper bytevector? 'bytevector))
	    ((hashtable? object) (implementation-tag-helper hashtable? 'hashtable))
	    ((record? object) (implementation-tag-helper record? (record-type-name (record-rtd object))))
	    (else
             (error 'implementation-tag "Unkown implementation type:" object))))))

(define (%predefine-tags predicate name . type-names)
  ;; (declare (ignore name))
  (for-each (lambda (type-name)
              (hashtable-set! %object-tag-map
                               type-name
                               (predicate->tag predicate)))
            type-names))

(define taggs-pre (begin
		     (%predefine-tags gp-boolean? 'boolean 'false)
		     (%predefine-tags gp-complex? 'complex 'recnum)
		     (%predefine-tags gp-exact-integer? 'exact-integer 'bignum 'fixnum)
		     ;; (%predefine-tags gp-exact-rational? 'exact-rational 'ratnum)
		     (%predefine-tags gp-inexact-real? 'real 'flonum)
		     (%predefine-tags gp-pair? 'pair 'pair)
		     (%predefine-tags procedure? 'procedure
				      'extended-procedure 'procedure 'entity
				      'primitive 'compiled-entry)
		     (%predefine-tags gp-string? 'string 'string)
		     (%predefine-tags gp-symbol? 'symbol
				      'interned-symbol 'uninterned-symbol)
		     (%predefine-tags gp-vector? 'vector 'vector)
))

;;; 原tagging的部分  2024年1月30日21:13:00
;;;; Generic tag access

(define get-tag				;tag的gp  2024年1月20日13:33:13
  (simple-generic-procedure 'get-tag 1
    (lambda (object)
      (implementation-tag object))))



(define tagging-gt (define-generic-procedure-handler get-tag ;扩展tag的gp,基于上面的rtd  2024年1月20日13:33:32
		     (match-args tagged-data?)
		     tagged-data-tag))


(define (get-predicate object)
  (tag->predicate (get-tag object)))

(define get-data
  (simple-generic-procedure 'get-data 1
			    (lambda (object) object)))

(define (tagged-data= t1 t2)
  (and (eq? (tagged-data-tag t1) (tagged-data-tag t2))
       (equal*? (tagged-data-data t1) (tagged-data-data t2))))

(define tagging-gd (begin (define-generic-procedure-handler get-data
			    (match-args tagged-data?)
			    tagged-data-data)
			  (define-generic-procedure-handler equal*? ;顺手再扩展equal?的gp 2024年1月20日13:36:41
			    (match-args tagged-data? tagged-data?)
			    tagged-data=)))

(define values-gt (begin (define-generic-procedure-handler get-tag
			   (match-args applicable-object?)
			   (lambda (object)
			     (applicable-object-metadata-tag
			      (applicable-object-metadata object))))
			 (define-generic-procedure-handler get-data
			   (match-args applicable-object?)
			   (lambda (object)
			     (get-data (applicable-object->object object)))))
  )
;;;; Tagged data



(define tagged-data-representation
  ((generic-procedure-constructor make-chaining-dispatch-store)
   'tagged-data-representation 1
   (lambda (tagged-data)
     (list (tagged-data-data tagged-data)))))

;;; 可以定义一个print的gp,然后对不同的类型进行扩展 2024年1月20日13:38:04
;;; MIT/GNU Scheme: integrate with printer
;; (define-print-method tagged-data?
;;   (standard-print-method
;;       (lambda (tagged-data)
;;         (tag-name (tagged-data-tag tagged-data)))
;;     tagged-data-representation))



;;; MIT/GNU Scheme: integrate with pretty-printer
;; (define-pp-describer tagged-data?
;;   tagged-data-description)

;;;; Tagging strategies
(define tagged-data-description
  (most-specific-generic-procedure 'tagged-data-description 1
				   (constant-generic-procedure-handler #f)))


(define (tagging-strategy:always name data-test make-tag) ;任意对象都加tag 2024年1月20日17:42:55

  (define (constructor data)
    (if (not (data-test data))
        (error 'tagging-strategy:always (string-append "Ill-formed data for " (symbol->string name) ":")
               data))
    (%make-tagged-data tag data))

  (define (predicate object)
    (and (tagged-data? object)
         (tag<= (tagged-data-tag object) tag)
         (data-test (tagged-data-data object))))

  (define tag
    (make-tag predicate constructor tagged-data-data))

  tag)


