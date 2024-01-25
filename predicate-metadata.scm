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

;;;; Simple predicate metadata

(define (register-predicate! predicate name)
  (set-predicate-metadata! predicate name) ;在predicate.scm中被定义,单纯的加入哈希表,返回本谓词.  2024年1月15日19:14:50
  predicate)

(define (register-compound-predicate! predicate type components) ;为了实现组合谓词的加入,将类型同其组件的谓词关联到一起 type的形式:atom,list,最后会是lol 2024年1月15日19:32:31
  (register-predicate! predicate
                       (cons type
                             (map predicate-name components))))

(define predicate-name get-predicate-metadata) ;取出的是metadata中哈希值的部分,根据后register-compound-predicate!,可以推测这个值是个lol  2024年1月15日19:31:14

;;;(define any-object? (conjoin))

(define (any-object? object) #t)

;; (register-predicate! any-object? 'any-object)   ;注释掉之后移到了predicates.scm中 2023年12月18日20:38:02

;; (register-predicate! number? 'number)
;; (register-predicate! symbol? 'symbol)
;; (register-predicate! boolean? 'boolean)
(define (gp-pred-md-init)
  ;; 由于这个闭包的存在,无法将代码放入 library,因为1:include的本质是将内容粘贴到出现的地方2:library中只能出现define
  (register-predicate! any-object? 'any-object)
  (register-predicate! number? 'number)
  (register-predicate! symbol? 'symbol)
  (register-predicate! boolean? 'boolean)
  )
