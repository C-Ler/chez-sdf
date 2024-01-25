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

;;;; Standard predicates

;;; This extends base-predicate to work for tagged data.  The
;;; constructor only wraps the data when the implementation tag
;;; is different.


(define (primitive-predicate name data-test)
  (if (not (predicate? data-test))
      (register-predicate! data-test name ;; (symbol 'n: name) 感觉没必要加n: 2024年1月19日21:00:00
			   ))
  (let ((predicate
         (make-simple-predicate name data-test
                                tagging-strategy:optional)))
    (set-predicate<=! data-test predicate) ;这个调用了一个348行的 set-tag<=! 在下面几个gp重定义谓词中,从number?开始就被error:not-a-type捕捉到异常 2024年1月20日12:17:38
    predicate))
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

(define gp-symbol?
  (primitive-predicate 'symbol symbol?))

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

(register-predicate! procedure? 'procedure)

;;;; Implementation tags

;; (define implementation-tag		;这个过程当中必须实现两个implementation相关的,一个返回obj的type,一个返回对应的谓词,然后将之注册,得到同(predicate->tag gp-boolean?) 一样的结果;这个过程仅在taggin.scm中被用于扩展get-tag的gp 2024年1月21日17:17:04
;;   (let ((boolean-tag (predicate->tag gp-boolean?))
;;         (null-tag (predicate->tag gp-null?)))
;;     (lambda (object)
;;       (cond ((eq? object #t) boolean-tag)
;;             ((eq? object '()) null-tag)
;; 	    ((pair? object) (hash-table-intern! %object-tag-map 'pair
;; 						(lambda ()
;; 						  (predicate->tag
;; 						   (register-predicate!
;; 						    pair?
;; 						    'pair)))))
;;             (else
;;              (let ((name (implementation-type-name object)))
;;                (hash-table-intern! %object-tag-map name
;;                  (lambda ()
;;                    (predicate->tag
;;                     (register-predicate!
;;                      (implementation-type-predicate name)
;;                      name))))))))))

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

;;; MIT/GNU Scheme specific:

(define %object-tag-map
  (make-key-weak-eqv-hash-table))

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

;;; End MIT/GNU Scheme specific
