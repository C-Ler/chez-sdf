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

;;;; Log number of uses of registered predicates,谓词的频率?不知道后面调用来做什么了  2024年1月15日20:32:37

;;; 关于hashtable的部分做了R6RS替换
(define %predicate-counts
  (make-parameter (make-eqv-hashtable)))

(define (reset-predicate-counts!)
  (hashtable-clear! (%predicate-counts)))

;; (reset-predicate-counts!)

(define (increment-predicate-count! predicate)
  (hashtable-update! (%predicate-counts)
                     predicate
		     (lambda (count) (fix:+ count 1)) ;count 在默认情况下是个过程,类似丘奇计数,fix:+是mit scheme的接受整数参数,返回整数参数的加法 2023年12月7日22:43:21
		     1
		     ;; (lambda () 1)
		     )
  )

;; (define (fix:+ x n)
;;   (lambda ()
;;     x))  ;使用了chez-mit,不需要自己实现了 2023年12月16日16:54:23

(define (get-predicate-count predicate)
  (hashtable-ref (%predicate-counts) predicate 0))

(define (get-predicate-counts)
  (hashtable->alist (%predicate-counts)))

(define (hashtable->alist someht)
  (let-values ([(keys values) (hashtable-entries someht)])
    (let loop ((n (- (vector-length keys) 1))
	       (acc '()))
      (if (< n 0)
	  acc
	  (loop (- n 1)
		(cons (cons (vector-ref keys n) (vector-ref values n))
		      acc))))
    ))

(define (with-predicate-counts thunk)
  (parameterize ((%predicate-counts (make-eqv-hashtable)))
    (let ((value (thunk)))
      (for-each (lambda (p)
                  (write-line (list (cdr p)
                                    (or (predicate-name (car p))
                                        (car p)))
                              (
			       current-output-port
			       ;; notification-output-port  ;r6rs没有这个,mit手册有一堆类似的,用来将各种过程的信息分流 2023年12月16日21:39:17
			       )))
                (get-predicate-counts))
      value)))

;; (call-with-output-string		
;;     (lambda (port)
;;       (write object port)))
