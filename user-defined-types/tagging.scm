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




;;; 原tagging的部分  2024年1月30日21:13:00
;;;; Generic tag access
(define tagging-gt (define-generic-procedure-handler get-tag ;扩展tag的gp,基于上面的rtd  2024年1月20日13:33:32
		     (match-args tagged-data?)
		     tagged-data-tag))


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


