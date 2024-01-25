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

(define (make-subsetting-dispatch-store-maker choose-handler) ;应该是定义了另一种ds的maker,对simple-dispatch-store扩展了一下,只能取出,不能放入  2024年1月17日21:54:12
  ;; ;; P190
  (lambda ()
    (let ((delegate (make-simple-dispatch-store)))

      (define (get-handler args)
        (let ((matching
               (filter (lambda (rule)
                         (is-generic-handler-applicable?
                          rule args))
                       ((delegate 'get-rules)))))
          (and (pair? matching)
               (choose-handler
                (map cdr (sort rule< matching))	;mit的sort 接受参数的顺序和R6RS相反...  2024年1月9日22:25:43
                ((delegate 'get-default-handler))))))

      (lambda (message)
        (case message
          ((get-handler) get-handler)
          (else (delegate message)))))))

(define (is-generic-handler-applicable? rule args)
  (if (simple-function? (cdr rule))
      (simple-function-apply-fit (cdr rule) args)
      (predicates-match? (car rule) args)))

(define (rule< r1 r2)
  (let loop ((ps1 (car r1)) (ps2 (car r2)))
    (if (pair? ps1)
        (cond ((eqv? (car ps1) (car ps2))
               (loop (cdr ps1) (cdr ps2)))
              ((predicate<= (car ps1) (car ps2))
               #t)
              ((predicate<= (car ps2) (car ps1))
               #f)
              (else
               (loop (cdr ps1) (cdr ps2))))
        #f)))

(define make-most-specific-dispatch-store
  ;; P190的第一种方法,选择已经排序的handler的第一个
  (make-subsetting-dispatch-store-maker
   (lambda (handlers default-handler)	;作为一个接受两个参数的choose-handler,这个λ相当于只传入了一个参数....((delegate 'get-default-handler))根本没用,所以是最符合条件的ds 2024年1月17日22:01:01
     ;; (declare (ignore default-handler))  ;看了下http://computer-programming-forum.com/40-scheme/804b827200ac5c30.htm 这个mit-s的保留syntax是防止内建过程被重定义的  2024年1月2日17:14:04
     (car handlers))))

(define make-chaining-dispatch-store
  ;; P190的第二种方法,另一种存储方式,子集的handler可以替代超集的部分而不用修改,冒险游戏的clock handler就使用了这个
  (make-subsetting-dispatch-store-maker
   (lambda (handlers default-handler)
     (let loop ((handlers handlers))
       (if (pair? handlers)
           (let ((handler (car handlers))
                 (next-handler (loop (cdr handlers))))
             (lambda args
               (apply handler (cons next-handler args)))) ;这个看起来是(handler1 (handler2 (handler3 ...这样  2024年1月17日22:03:35
           default-handler)))))

(define (make-cached-most-specific-dispatch-store)
  (cache-wrapped-dispatch-store
   (make-most-specific-dispatch-store)
   get-tag))

(define (make-cached-chaining-dispatch-store)
  (cache-wrapped-dispatch-store
   (make-chaining-dispatch-store)
   get-tag))

(define most-specific-generic-procedure
  (generic-procedure-constructor
   make-cached-most-specific-dispatch-store))

(define chaining-generic-procedure
  (generic-procedure-constructor
   make-cached-chaining-dispatch-store))

(set! make-default-dispatch-store
  make-cached-most-specific-dispatch-store)
