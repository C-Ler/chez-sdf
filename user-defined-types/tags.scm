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

;;; taggs
;;; taggs 的部分,得插在tagging的中间... 2024年2月1日21:22:07
;;; lib化之后得放在这里 2024年2月15日11:13:12
(define (primitive-predicate name data-test) ;用来将不是原生谓词转化为gp-udp的谓词的  2024年2月22日17:07:54
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

(define primitive-predicate-convert
  (begin
    (primitive-predicate 'boolean boolean?)
    (primitive-predicate 'complex complex?)
    (primitive-predicate 'exact-integer exact-integer?)
    ;; (define gp-exact-rational?
    ;;   (primitive-predicate 'exact-rational rational?))   mit才有的定义 2024年1月19日21:21:15

    (primitive-predicate 'inexact-real flonum?)
    
    (primitive-predicate 'integer integer?)

    (primitive-predicate 'null null?)
    
    (primitive-predicate 'pair pair?)
    

    (primitive-predicate 'rational rational?)

    (primitive-predicate 'real real?)

    (primitive-predicate 'string string?)

    (primitive-predicate 'vector vector?)

;;; 下面两个去掉了exact的部分  2024年1月19日21:24:47
    (primitive-predicate 'exact-nonnegative-integer
			 nonnegative?)

    (primitive-predicate 'exact-positive-integer
			 positive?)

    (primitive-predicate 'list list?)

    (primitive-predicate 'non-empty-list non-empty-list?)

    (primitive-predicate 'number number?) ;number symbol? boolean? 这几个在predicate-metadata.scm 已经注册过了,由于predicates文件中的tag<= 报错 2024年1月19日21:43:45
    (primitive-predicate 'symbol symbol?)))

(define taggs-relation (begin
			 (set-predicate<=! complex? number?)
			 ;; (set-predicate<=! exact-integer? integer?)
			 (set-predicate<=! nonnegative? integer?)
			 (set-predicate<=! positive? integer?)
			 ;; (set-predicate<=! exact-rational? rational?)
			 ;; (set-predicate<=! real? real?)
			 (set-predicate<=! integer? rational?)
			 (set-predicate<=! non-empty-list? list?)
			 (set-predicate<=! null? list?)
			 (set-predicate<=! rational? real?)
			 (set-predicate<=! real? complex?)

			 (register-predicate! procedure? 'procedure)))


(define %object-tag-map
  (make-key-weak-eqv-hash-table))

(define (implementation-tag-helper pred name)
  (hash-table-intern! %object-tag-map name (lambda () (predicate->tag (register-predicate!  pred name)))))

(define implementation-tag		 ;由于没找到chez及R6RS获取obj type的方法,只能手撸一个 2024年1月21日17:33:25
  (let ((boolean-tag (predicate->tag boolean?))
        (null-tag (predicate->tag null?)))
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

(define (%predefine-tags predicate name . type-names) ;下面这部分预定义,对于adven的部分可能无用,但是arith估计有用  2024年2月24日20:22:12
  ;; (declare (ignore name))
  (for-each (lambda (type-name)
              (hashtable-set! %object-tag-map
                               type-name
                               (predicate->tag predicate)))
            type-names))

(define taggs-pre (begin
		     (%predefine-tags boolean? 'boolean 'false)
		     (%predefine-tags complex? 'complex 'recnum)
		     (%predefine-tags exact-integer? 'exact-integer 'bignum 'fixnum)
		     ;; (%predefine-tags exact-rational? 'exact-rational 'ratnum)
		     ;; (%predefine-tags inexact-real? 'real 'flonum)
		     (%predefine-tags pair? 'pair 'pair)
		     (%predefine-tags procedure? 'procedure
				      'extended-procedure 'procedure 'entity
				      'primitive 'compiled-entry)
		     (%predefine-tags string? 'string 'string)
		     (%predefine-tags symbol? 'symbol
				      'interned-symbol 'uninterned-symbol)
		     (%predefine-tags vector? 'vector 'vector)
))

;;; tagging 的另一部分,需要implementation-tag 2024年2月24日19:40:58
(define get-tag				;tag的gp  2024年1月20日13:33:13
  (simple-generic-procedure 'get-tag 1
    (lambda (object)
      (implementation-tag object))))

(define tagging-gt (define-generic-procedure-handler get-tag ;扩展tag的gp,基于上面的rtd  2024年1月20日13:33:32
		     (match-args tagged-data?)
		     tagged-data-tag))

(define (get-predicate object)		;最好紧跟在上面这个扩展的之后 2024年2月25日12:10:13
  (tag->predicate (get-tag object)))

(define (tagged-data= t1 t2)		;最好紧跟在上面这个扩展的之后 2024年2月25日12:10:13
  (and (eq? (tagged-data-tag t1) (tagged-data-tag t2))
       (equal*? (tagged-data-data t1) (tagged-data-data t2))))

(define get-data
  (simple-generic-procedure 'get-data 1
			    (lambda (object) object)))

(define tagging-gd (begin (define-generic-procedure-handler get-data
			    (match-args tagged-data?)
			    tagged-data-data)
			  (define-generic-procedure-handler equal*? ;顺手再扩展equal?的gp 2024年1月20日13:36:41
			    (match-args tagged-data? tagged-data?)
			    tagged-data=)))

