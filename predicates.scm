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
;;;; Predicates
(define pred-association (make-metadata-association)) ;collection.scm 中定义的,用hashtable实现的  2024年1月15日19:17:11

(define predicate? (pred-association 'has?)) 
(define get-predicate-metadata (pred-association 'get))
(define set-predicate-metadata! (pred-association 'put!))


;;; 下面的过程总是报参数数量不对,将!optional 全部干掉了  2023年12月5日22:44:35
;;; 后来在chez-mit找到了扩展后的define*,支持这种语法 2024年1月5日23:20:12
;;; 这部分是用来提供例外提示的 2024年1月11日22:32:48
(define* (guarantee predicate object #:optional caller)	;
  (if (not (predicate object))
      (error:not-a predicate object caller))
  object)

(define* (error:not-a predicate object #:optional caller) ;仅判断某个实例的类型 2024年1月15日19:34:52
  (error:wrong-type-argument object
                             (predicate-description predicate)
                             caller))


(define* (guarantee-list-of predicate object #:optional caller)	 ;在某个ls的类型不满足谓词ls的时候警告,封装了下面,但是就后来的实际用法来看,这个东西有些多余 2024年1月15日19:34:11
  (if (not (list-of-type? object predicate))
      (error:not-a-list-of predicate object caller))
  object)

(define* (error:not-a-list-of predicate object #:optional caller)
  (error:wrong-type-argument object	;在sdf.ss中定义,用了简单的error实现 2024年1月15日19:33:25
                             (string-append
                              "list of "
                              (predicate-description predicate)) ;这个谓词不是原生的那种,是metadata扩展后的谓词,所以可以通过这个取得谓词的描述 2023年12月22日19:22:09
                             caller))

(define (predicate-description predicate)
  (if (predicate? predicate)		;has的简单替换,判断哈希表是否存在这个谓词  2024年1月15日19:37:34
      (object->description (predicate-name predicate)) ;predicate-name 在 common/predicate-metadata.scm 中直接对get-predicate-metadata更名得到;user-defined-types/predicates.scm先取tag,再取tag的name  2024年1月11日22:34:11
      (string-append "object satisfying "
                     (object->description predicate))))

(define (object->description object)	;这个太草了,就是简单得把对象以string的形式显示出来 2024年1月11日22:40:01
  (call-with-output-string		
    (lambda (port)
      (write object port))))

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

(define (maybe-register-compound-predicate! datum-test
                                            operator operands) ;操作对象全都是已经存在哈希表的谓词时,将datum-test作为谓词,操作符作为对象组合存入? 2024年1月15日19:49:26
  (if (every predicate? operands)	
      (register-compound-predicate! datum-test operator operands)
      datum-test))

(define (equality-predicate-maker name =) ;将等价谓词扩展进md的方法,最后注册进去的key值谓词就是let绑定的接受一个参数的lambda,最后实际上 2024年1月15日20:01:50
  (lambda (object)
    (let ((predicate
           (lambda (object*)
             (= object object*))))
      (register-predicate! predicate (list name =))
      predicate)))

(define eq-predicate			;注册进htmd,同时返回一个单参数过程,接受某个对象,最后用起来像这样((eq-predicate '我) '20) -> #f 2024年1月15日20:11:47
  (equality-predicate-maker 'eq? eq?))
(define eqv-predicate
  (equality-predicate-maker 'eqv? eqv?))
(define equal-predicate
  (equality-predicate-maker 'equal? equal?))
