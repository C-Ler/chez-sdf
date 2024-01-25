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
;;;; Applicability

;;; An applicability attribute is a list of lists, representing
;;; an OR of some per-argument ANDs

(define (applicability? object)		;applicability attribute 是lol, 是 过程pattern 的ls的ls 是cdr的每部分ls的长度都同其car相同的lol 2024年1月15日22:43:25
  (and (list? object)
       (every (lambda (pattern)
                (and (list? pattern)
                     (every procedure? pattern)))
              object)
       (or (not (pair? object))
           (let ((arity (length (car object))))
             (every (lambda (pattern)
                      (= arity (length pattern)))
                    (cdr object))))))

(define (applicability-arity applicability) ;返回参数长度 2024年1月15日22:43:37
  (guarantee applicability? applicability)
  (if (pair? applicability)
      (length (car applicability))
      0))

(define (is-applicable? applicability args) ;判断是否存在一个 and-clause(谓词,applicability的ls们) 能对args返回#t 2024年1月15日22:53:08
  (any (lambda (and-clause)
         (predicates-match? and-clause args))
       applicability))

(define (predicates-match? predicates args) ;每一个args是否都能使对应pred返回#t  2024年1月15日22:51:44
  (and (= (length predicates) (length args))
       (every (lambda (predicate arg)	;
                (increment-predicate-count! predicate) ;不太懂为什么谓词调用一次就要计数增加一次 2024年1月15日22:47:16
                (predicate arg))	
              predicates
              args)))

(define (match-args . predicates)
  (list predicates))

(define (all-args arity predicate)	;根据arity数量构造全是某一个谓词的applicability  2024年1月15日22:54:46
  (list (make-list arity predicate)))

(define (any-arg arity predicate base-predicate)
  (if (= 0 arity)
      '()
      (cdr (all-sequences-of arity base-predicate predicate))))	;这个过程在utlis中,单独复制到了sdf,(all-sequences-of 2 'a 'b ) -> ((a a) (a b) (b a) (b b)) 会返回一个 2024年1月15日23:03:11

(define (applicability-union . applicabilities) ;对applicability进行集合化 2024年1月15日22:56:20
  (applicability-union* applicabilities))

(define (applicability-union* applicabilities) 
  (apply lset-union equal? applicabilities))
