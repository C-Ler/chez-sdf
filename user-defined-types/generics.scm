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

;;; values的部分,generic需要..  2024年1月30日22:06:05
(define udp-values-association (make-metadata-association))
(define applicable-object? (udp-values-association 'has?))
(define applicable-object-metadata (udp-values-association 'get))
(define set-applicable-object-metadata! (udp-values-association 'put!))

(define values-ao (register-predicate! applicable-object? 'applicable-object))

(define value-restriction
  (simple-generic-procedure 'value-restriction 2
			    (constant-generic-procedure-handler #f)))

(define (value-fit value predicate)	
  (if (predicate value)
      (lambda () value)
      (value-restriction value predicate)))

(define-record-type (<applicable-object-metadata> make-applicable-object-metadata applicable-object-metadata?)
  (fields (immutable tag applicable-object-metadata-tag)
	  (immutable object applicable-object-metadata-object)
	  (immutable applicator applicable-object-metadata-applicator))
  )

(define (applicable-object->object object)
  (applicable-object-metadata-object
   (applicable-object-metadata object)))

(define (applicable-object-tag object)
  (applicable-object-metadata-tag
   (applicable-object-metadata object)))

(define (combine-fits procedure fits)
  (lambda ()
    (procedure
     (map (lambda (fit) (fit))
          fits))))

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

;;; templates的部分 generic需要 2024年2月24日21:29:51
(define (template-pattern-operator? object) ;模板匹配操作符的枚举值,目的不明 2024年2月25日13:14:52
  (memq object '(? ?* ?+)))

(define (polarity? object)		;极性的枚举值,目的不知道是什么 2024年2月25日13:14:31
  (memq object '(+ = -)))

;;; 又开始rtd里面嵌套rtd了....
(define-record-type (<parametric-tag> %make-parametric-tag parametric-tag?)
  (fields (immutable shared parametric-tag-shared)
	  (immutable template parametric-tag-template)
	  (immutable bindings parametric-tag-bindings))
  )

(define (parametric-predicate? object)
  (and (predicate? object)
       (parametric-tag? (predicate->tag object))))

(define parametric-reg
  (begin
    (define-tag-type parametric-tag? parametric-tag-shared)
    (register-predicate! parametric-tag? 'parametric-tag)
    (set-predicate<=! parametric-tag? tag?)
    (register-predicate! parametric-predicate? 'parametric-predicate)
    (set-predicate<=! parametric-predicate? predicate?)))

;; (define-tag-record-printer <parametric-tag>)
(define (parametric-predicate-template predicate)
  (parametric-tag-template (predicate->tag predicate)))

(define-record-type (<predicate-template> %make-predicate-template predicate-template?)
  (fields (immutable name predicate-template-name)
          (immutable pattern predicate-template-pattern)
          (immutable instantiator predicate-template-tag-instantiator)
          (immutable predicate predicate-template-predicate)))

(define temp-pt (register-predicate! predicate-template? 'predicate-template))

(define-record-type (<parameter-binding> make-parameter-binding parameter-binding?)
  (fields  (immutable element parameter-binding-element)
	   (immutable value parameter-binding-value)))

;;; 下面这三个可能会导致debug变得困难  2024年2月1日19:20:13
(define (template-pattern-element-operator element) ;? ?* ?+中的一个
  (car element))

(define (template-pattern-element-name element)
  (cadr element))

(define (template-pattern-element-polarity element) ;+ = -中的一个,默认是+
  (if (null? (cddr element))
      '+
      (caddr element)))

(define (template-pattern-element-single-valued? element)
  (eq? '? (template-pattern-element-operator element)))

;;; 下面这四个都是为了实现template-pattern?  2024年2月25日13:49:28
(define (parameter-binding-name binding)
  (template-pattern-element-name
   (parameter-binding-element binding)))

(define (parameter-binding-polarity binding) ;组合谓词调用  2024年2月29日21:35:40
  (template-pattern-element-polarity
   (parameter-binding-element binding)))

(define (parameter-binding-values binding)
  (if (template-pattern-element-single-valued?
       (parameter-binding-element binding))
      (list (parameter-binding-value binding))
      (parameter-binding-value binding)))

(define (template-pattern-name? object)
  (and (symbol? object)
       (not (template-pattern-operator? object))
       (not (polarity? object))))

(define (template-pattern-element? object)
  (and (pair? object)
       (template-pattern-operator? (car object))
       (pair? (cdr object))
       (template-pattern-name? (cadr object))
       (or (null? (cddr object))
           (and (pair? (cddr object))
                (polarity? (caddr object))
                (null? (cdddr object))))))

(define (template-pattern->names pattern)
  (map template-pattern-element-name pattern))

(define (template-pattern? object)
  (and (non-empty-list? object)
       (every template-pattern-element? object)
       (list-of-unique-symbols?
        (template-pattern->names object))))

(define temp-tp (register-predicate! template-pattern? 'template-pattern))

(define (predicate-template-accessor name template)
  (let ((elt
         (find (lambda (elt)
                 (eq? (template-pattern-element-name elt)
                      name))
               (predicate-template-pattern template))))
    (if (not elt)
        (error 'predicate-template-accessor "Unknown parameter name:" name template))
    (let ((valid? (predicate-template-predicate template))
          (convert
           (if (template-pattern-element-single-valued? elt)
               tag->predicate
               tags->predicates)))
      (lambda (predicate)
        (guarantee valid? predicate)
        (convert
         (parameter-binding-value
          (find (lambda (binding)
                  (eqv? name (parameter-binding-name binding)))
                (parametric-tag-bindings
                 (predicate->tag predicate)))))))))

;;; 下面这四个可以紧跟在rtd和template-pattern-element访问器之后 2024年2月25日13:26:00
(define (make-parametric-tag name data-test tagging-strategy
                             template bindings)
  (%invoke-tagging-strategy tagging-strategy name data-test
                            (lambda (shared)
                              (%make-parametric-tag shared
                                                    template
                                                    bindings))))

(define (match-template-pattern pattern values value-predicate)
  (guarantee list? values)
  (if (not (= (length values) (length pattern)))
      (error 'match-template-pattern "Wrong number of values:" values pattern))
  (map (lambda (element value)
         (case (template-pattern-element-operator element)
           ((?)
            (if (not (value-predicate value))
                (error 'match-template-pattern "Mismatch:" element value)))
           ((?*)
            (if (not (and (list? value)
                          (every value-predicate value)))
                (error 'match-template-pattern "Mismatch:" element value)))
           ((?+)
            (if (not (and (non-empty-list? value)
                          (every value-predicate value)))
                (error 'match-template-pattern "Mismatch:" element value)))
           (else
            (error:not-a template-pattern? pattern)))
         (make-parameter-binding element value))
       pattern
       values))

(define (map-template-pattern pattern object value-procedure)
  (map (lambda (element o)
         (case (template-pattern-element-operator element)
           ((?) (value-procedure o))
           ((?* ?+) (map value-procedure o))
           (else (error:not-a template-pattern? pattern))))
       pattern
       object))

(define (make-predicate-template-tag-instantiator
           name pattern make-data-test tagging-strategy
           get-template)
  (lambda patterned-tags
    (letrec
        ((tag
          (make-parametric-tag		;递归构造tag
           (cons name
                 (map-template-pattern pattern
                                       patterned-tags
                                       tag-name))
           (make-data-test (lambda () tag))
           tagging-strategy
           (get-template)
           (match-template-pattern pattern
                                   patterned-tags
                                   tag?))))
      tag)))

(define (make-predicate-template name pattern tagging-strategy
                                 make-data-test)
  (guarantee template-pattern? pattern)
  (letrec*
      ((instantiator
        (make-predicate-template-tag-instantiator
         name
         pattern
         make-data-test
         tagging-strategy
         (lambda () template)))
       (predicate
        (lambda (object)
          (and (parametric-predicate? object)
               (eqv? (parametric-predicate-template object)
                     template))))
       (template
        (%make-predicate-template
         name
         pattern
         (simple-list-memoizer equal?
                               (lambda parameters parameters)
                               instantiator)
         predicate)))
    (register-predicate! predicate (symbol-append name '-predicate))
    (set-predicate<=! predicate parametric-predicate?)
    template))


;;; functions的部分 generic需要 2024年2月24日21:22:52
;;; functions的部分,由于simple-function?这个东西,必须放在generic的前面...  2024年1月30日22:08:29
(define-record-type (<simple-function-metadata> make-simple-function-metadata simple-function-metadata?)
  (fields (immutable name simple-function-metadata-name)
	  (immutable procedure simple-function-metadata-procedure))
  )

(define (simple-function-name function)
  (simple-function-metadata-name
   (applicable-object->object function)))

(define (simple-function-procedure function)
  (simple-function-metadata-procedure
   (applicable-object->object function)))

(define (simple-function? object)
  (and (applicable-object? object)	;定义于values  2024年1月30日22:00:36
       (simple-function-metadata?	;本文件的record 谓词 2024年1月30日22:01:45
        (applicable-object->object object)))) ;values中定义 2024年1月30日22:02:25

(define function-template		;这个报错 error-generic-procedure-handler: Inapplicable generic procedure: with irritants (get-tag-shared  2024年2月2日12:47:44
  ;; 上面的异常是因为没有对gp进行handler扩展  2024年2月3日19:00:37
  ;; error: invalid message argument #<eqv hashtable> (who = "No such key in hashtable.", irritants = (#<procedure parametric-predicate? at generics.scm:5453>))
  (make-predicate-template 'function
                           '((?* domains -) (? codomain))
                           tagging-strategy:never
    (lambda (get-tag)
      (lambda (object)
        (and (simple-function? object)
             (tag<= (applicable-object-tag object) (get-tag)))))))

(define (simple-function-tag function)
  (applicable-object-tag function))

(define (simple-function-predicate function)
  (tag->predicate (simple-function-tag function)))

(define function-predicate-domains
  (predicate-template-accessor 'domains function-template))

(define (simple-function-domains function)
  (function-predicate-domains
   (simple-function-predicate function)))

(define (simple-function-apply-fit function args)
  (let ((domains (simple-function-domains function)))
    (and (= (length domains) (length args))
         (let ((fits (map value-fit args domains)))
           (and (not (memq #f fits))
                (combine-fits
                 (lambda (args)
                   (apply (simple-function-procedure function)
                          args))
                 fits))))))
;;; 原generic的部分,由于get-tag的定义需要implementation-tag %predefine-tags 无法前置... 2024年2月24日18:57:25
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
  (if (simple-function? (cdr rule)) ;functions中定义... 2024年1月30日22:12:49
      (simple-function-apply-fit (cdr rule) args) ;functions中定义... 2024年1月30日22:12:49
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
  ;; P190的第一种方法,选择已经排序的handler的第一个,仅在本文件中被引用 2024年1月30日21:58:06
  (make-subsetting-dispatch-store-maker
   (lambda (handlers default-handler)	;作为一个接受两个参数的choose-handler,这个λ相当于只传入了一个参数....((delegate 'get-default-handler))根本没用,所以是最符合条件的ds 2024年1月17日22:01:01
     ;; (declare (ignore default-handler))  ;看了下http://computer-programming-forum.com/40-scheme/804b827200ac5c30.htm 这个mit-s的保留syntax是防止内建过程被重定义的  2024年1月2日17:14:04
     (car handlers))))

(define make-chaining-dispatch-store
  ;; P190的第二种方法,另一种存储方式,子集的handler可以替代超集的部分而不用修改,冒险游戏的clock handler就使用了这个,tagging中用于实现tagged-data-description  2024年1月30日21:56:49
  (make-subsetting-dispatch-store-maker
   (lambda (handlers default-handler)
     (let loop ((handlers handlers))
       (if (pair? handlers)
           (let ((handler (car handlers))
                 (next-handler (loop (cdr handlers))))
             (lambda args
               (apply handler (cons next-handler args)))) ;这个看起来是(handler1 (handler2 (handler3 ...这样  2024年1月17日22:03:35
           default-handler)))))

(define (make-cached-most-specific-dispatch-store) ;仅在本文件中被引用  2024年1月30日21:51:04
  (cache-wrapped-dispatch-store
   (make-most-specific-dispatch-store)
   get-tag))

(define (make-cached-chaining-dispatch-store) ;;仅在本文件中被引用  2024年1月30日21:51:04
  (cache-wrapped-dispatch-store
   (make-chaining-dispatch-store)
   get-tag))

(define most-specific-generic-procedure	;tagging用于实现tagged-data-description 冒险游戏中频繁引用  2024年1月30日21:51:59
  (generic-procedure-constructor
   make-cached-most-specific-dispatch-store))

(define chaining-generic-procedure	;冒险游戏中有所引用,实现了某些gp,比如set-up! tear-down! enter-place!  2024年1月30日21:53:02
  (generic-procedure-constructor
   make-cached-chaining-dispatch-store))

;; (set! make-default-dispatch-store	;替换了原本common中的该过程,但是没被引用,注释掉好了 2024年1月30日21:54:20
;;   make-cached-most-specific-dispatch-store)

;;; tagging依赖于generic的部分,adventure游戏有用到 2024年2月24日18:59:19
;;;; Tagged data

(define tagged-data-representation
  ((generic-procedure-constructor make-chaining-dispatch-store)
   'tagged-data-representation 1
   (lambda (tagged-data)
     (list (tagged-data-data tagged-data)))))

(define tagged-data-description
  (most-specific-generic-procedure 'tagged-data-description 1
				   (constant-generic-procedure-handler #f)))

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




