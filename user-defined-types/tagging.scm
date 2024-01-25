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

;;;; Generic tag access

(define get-tag				;tag的gp  2024年1月20日13:33:13
  (simple-generic-procedure 'get-tag 1
    (lambda (object)
      (implementation-tag object))))

(define (get-predicate object)
  (tag->predicate (get-tag object)))

(define get-data
  (simple-generic-procedure 'get-data 1
    (lambda (object) object)))

;;;; Tagged data

(define-record-type (<tagged-data> %make-tagged-data tagged-data?)
  (fields (immutable tag tagged-data-tag) (immutable data tagged-data-data))
    
  
  )

(define-generic-procedure-handler get-tag ;扩展tag的gp,基于上面的rtd  2024年1月20日13:33:32
  (match-args tagged-data?)
  tagged-data-tag)

(define-generic-procedure-handler get-data
  (match-args tagged-data?)
  tagged-data-data)

(define (tagged-data= t1 t2)
  (and (eq? (tagged-data-tag t1) (tagged-data-tag t2))
       (equal*? (tagged-data-data t1) (tagged-data-data t2))))

(define-generic-procedure-handler equal*? ;顺手再扩展equal?的gp 2024年1月20日13:36:41
  (match-args tagged-data? tagged-data?)
  tagged-data=)

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

(define tagged-data-description
  (most-specific-generic-procedure 'tagged-data-description 1
    (constant-generic-procedure-handler #f)))

;;; MIT/GNU Scheme: integrate with pretty-printer
;; (define-pp-describer tagged-data?
;;   tagged-data-description)

;;;; Tagging strategies

(define (tagging-strategy:never name data-test make-tag) ;不加tag  2024年1月20日17:42:47

  (define (constructor data)		
    (if (not (data-test data))		;加了一个重复出现的结构,判断data是否满足data-test的,这种东西到处出现 2024年1月20日13:40:15
        (error 'agging-strategy:never (string-append "Ill-formed data for " (symbol->string name) ":")
               data))
    data)

  (define tag
    (make-tag data-test constructor (lambda (object) object)))

  tag)

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
