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


本文件仅被 tagging 引用 2024年1月30日22:13:47
|#

;;; tagging 的部分  2024年2月1日20:07:31


(define (tagging-strategy:never name data-test make-tag) ;不加tag  2024年1月20日17:42:47

  (define (constructor data)		
    (if (not (data-test data))		;加了一个重复出现的结构,判断data是否满足data-test的,这种东西到处出现 2024年1月20日13:40:15
        (error 'agging-strategy:never (string-append "Ill-formed data for " (symbol->string name) ":")
               data))
    data)

  (define tag
    (make-tag data-test constructor (lambda (object) object)))

  tag)

;;; predicates的部分 2024年1月30日22:35:04
;;;; Basic tag structure
(define predicate->tag get-predicate-metadata) ;common 中 pred-md-get 的简单替换 2024年2月3日21:18:28

(define tag?
  (simple-generic-procedure 'tag? 1
			    (constant-generic-procedure-handler #f)))

(define get-tag-shared
  (simple-generic-procedure 'get-tag-shared 1 #f))

(define (define-tag-type predicate get-shared) 	;对各个不同的tag扩展其get-tag-shared gp 的过程... 2024年2月3日17:44:12
  (define-generic-procedure-handler tag? (match-args predicate)
    (lambda (object)
      ;; (declare (ignore object))
      #t))
  (define-generic-procedure-handler get-tag-shared
    (match-args predicate)
    get-shared))

(define-record-type (<tag-shared> %make-tag-shared tag-shared?)
  (fields (immutable name tag-shared-name)
	   (immutable predicate tag-shared-predicate)
	   (immutable constructor tag-shared-constructor)
	   (immutable accessor tag-shared-accessor)
	  (immutable supersets tag-shared-supersets)
	  )
  )

(define (tag-name tag)
  (tag-shared-name (get-tag-shared tag)))

(define (tag->predicate tag)
  (tag-shared-predicate (get-tag-shared tag)))

(define (tag-constructor tag)
  (tag-shared-constructor (get-tag-shared tag)))

(define (tag-accessor tag)
  (tag-shared-accessor (get-tag-shared tag)))

(define (tag-supersets tag)
  (tag-shared-supersets (get-tag-shared tag)))

(define (tags->predicates tags)
  (map tag->predicate tags))

(define (get-tag-supersets tag)
  (((tag-supersets tag) 'get-elements)))

(define (make-tag-shared name predicate constructor accessor)
  (guarantee procedure? predicate 'make-tag-shared)
  (guarantee procedure? constructor 'make-tag-shared)
  (guarantee procedure? accessor 'make-tag-shared)
  (%make-tag-shared name predicate constructor accessor
                    (make-weak-eq-set)))

(define (%invoke-tagging-strategy tagging-strategy name data-test
                                  maker)
  (tagging-strategy			;比如tagging-strategy:never,传入构造器和参数,返回构造的结果,即tag
   name
   data-test
   (lambda (predicate constructor accessor)  ;tagging-strategy:never 需要的make-tag,constructor已经定义在其中,而accessor是λ:x->x
     (let ((tag
            (maker			;构造simple-tag的maker,所以构造一个槽子是record的record的目的何在??? 2024年2月3日17:33:05
             (make-tag-shared name predicate constructor ;构造tag-shared的构造器...
                              accessor)))) ;
       (set-predicate-metadata! predicate tag) ;建立了md的k pred v tag关联
       tag))))

(define-record-type (simple-tag %make-simple-tag simple-tag?)
  (fields (immutable shared simple-tag-shared)))

(define pred=st (define-tag-type simple-tag? simple-tag-shared))
;; (define-tag-record-printer <simple-tag>)  ;为了避免出现lib化报语法错误的权宜之计.... 2024年2月3日17:48:18

(define (make-simple-tag name data-test tagging-strategy)
  (%invoke-tagging-strategy tagging-strategy name data-test
                            %make-simple-tag))

(define-record-type (<parametric-tag> %make-parametric-tag parametric-tag?)
  (fields (immutable shared parametric-tag-shared) (immutable template parametric-tag-template) (immutable bindings parametric-tag-bindings))
  )

(define-tag-type parametric-tag? parametric-tag-shared)
;; (define-tag-record-printer <parametric-tag>)

(define-record-type (<compound-tag> %make-compound-tag compound-tag?)
    (fields (immutable shared compound-tag-shared) (immutable operator compound-tag-operator) (immutable components compound-tag-components))
    )

(define-tag-type compound-tag? compound-tag-shared)
;; (define-tag-record-printer <compound-tag>)

(define (make-parametric-tag name data-test tagging-strategy
                             template bindings)
  (%invoke-tagging-strategy tagging-strategy name data-test
                            (lambda (shared)
                              (%make-parametric-tag shared
                                                    template
                                                    bindings))))

(define (make-simple-predicate name data-test tagging-strategy)
  (tag->predicate
   (make-simple-tag name data-test tagging-strategy)))

(define (register-predicate! predicate name) ;predicate-metadata.scm 当中已经定义过了,这里覆盖了,之前的版本只是构造mdht中的name pred键值对,单纯的原生谓词,无法构造结构和层次.这里没有明显的put,不知道怎么能和之前的md起作用 2024年1月20日18:30:17
  (guarantee procedure? predicate)
  (make-simple-predicate name predicate tagging-strategy:never))

(define (predicate-name predicate)
  (tag-name (predicate->tag predicate)))

(define (parametric-predicate? object)
  (and (predicate? object)
       (parametric-tag? (predicate->tag object))))

(define pred-pp (begin
		  (register-predicate! parametric-predicate? 'parametric-predicate)))

(define (predicate-constructor predicate)
  (tag-constructor (predicate->tag predicate)))

(define (predicate-accessor predicate)
  (tag-accessor (predicate->tag predicate)))

(define (predicate-supersets predicate)
  (map tag->predicate
       (get-tag-supersets (predicate->tag predicate))))

(define (parametric-predicate-template predicate)
  (parametric-tag-template (predicate->tag predicate)))

;;; 用来存储标签顺序关系的
(define (false-tag<= tag1 tag2) ;; (declare (ignore tag1 tag2)) 
  #f)

(define generic-tag<=
  (simple-generic-procedure 'generic-tag<= 2 false-tag<=))

(define tag<=-cache
  (make-equal-hash-table))

(define (uncached-tag<= tag1 tag2)
  (or (eqv? tag1 tag2)
      (generic-tag<= tag1 tag2)
      (any (lambda (tag)
             (cached-tag<= tag tag2))
           (get-tag-supersets tag1))))

(define (cached-tag<= tag1 tag2)
  (hash-table-intern! tag<=-cache
                      (cons tag1 tag2)
                      (lambda () (uncached-tag<= tag1 tag2))))

(define (tag<= tag1 tag2)		;这个东西..  2024年1月20日22:04:07
  (guarantee tag? tag1)
  (guarantee tag? tag2)
  (cached-tag<= tag1 tag2))

(define (tag>= tag1 tag2)
  (tag<= tag2 tag1))


(define (set-tag<=! tag superset)
  (if (tag>= tag superset)
      (error 'set-tag<=! "Not allowed to create a superset loop:"
             tag superset))
  (if (not (tag<= tag superset))
      (((tag-supersets tag) 'add-element!) superset))
  (hash-table-clear! tag<=-cache))

(define (predicate<= predicate1 predicate2)
  (tag<= (predicate->tag predicate1)
         (predicate->tag predicate2)))

(define (predicate>= predicate1 predicate2)
  (predicate<= predicate2 predicate1))

(define (tag= tag1 tag2)
  (guarantee tag? tag1)
  (guarantee tag? tag2)
  (eqv? tag1 tag2))

(define (predicate= predicate1 predicate2)
  (tag= (predicate->tag predicate1)
        (predicate->tag predicate2)))

(define (set-predicate<=! predicate superset)
  (set-tag<=! (predicate->tag predicate)
              (predicate->tag superset)))



;;; values的部分  2024年1月30日22:06:05
(define udp-values-association (make-metadata-association))
(define applicable-object? (udp-values-association 'has?))
(define applicable-object-metadata (udp-values-association 'get))
(define set-applicable-object-metadata! (udp-values-association 'put!))

(define values-ao (register-predicate! applicable-object? 'applicable-object))

(define value-restriction
  (simple-generic-procedure 'value-restriction 2
    (constant-generic-procedure-handler #f)))

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

(define (value-fit value predicate)
  (if (predicate value)
      (lambda () value)
      (value-restriction value predicate)))
;;; templates的部分  2024年1月30日22:39:23
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
(define (template-pattern-element-operator element)
  (car element))

(define (template-pattern-element-name element)
  (cadr element))

(define (template-pattern-element-polarity element)
  (if (null? (cddr element))
      '+
      (caddr element)))

(define (template-pattern-element-single-valued? element)
  (eq? '? (template-pattern-element-operator element)))

(define (parameter-binding-name binding)
  (template-pattern-element-name
   (parameter-binding-element binding)))

(define (parameter-binding-polarity binding)
  (template-pattern-element-polarity
   (parameter-binding-element binding)))

(define (parameter-binding-values binding)
  (if (template-pattern-element-single-valued?
       (parameter-binding-element binding))
      (list (parameter-binding-value binding))
      (parameter-binding-value binding)))

(define (predicate-template-accessor name template)
  (let ((elt
         (find (lambda (elt)
                 (eq? (template-pattern-element-name elt)
                      name))
               (predicate-template-pattern template))))
    (if (not elt)
        (error "Unknown parameter name:" name template))
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

(define (template-pattern-operator? object)
  (memq object '(? ?* ?+)))

(define (polarity? object)
  (memq object '(+ = -)))

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
          (make-parametric-tag
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

(define (simple-function-domains function)
  (function-predicate-domains
   (simple-function-predicate function)))

;;; functions的部分  2024年1月30日22:08:29
(define-record-type (<simple-function-metadata> make-simple-function-metadata simple-function-metadata?)
  (fields (immutable name simple-function-metadata-name) (immutable  procedure simple-function-metadata-procedure))
  )

(define (simple-function? object)
  (and (applicable-object? object)	;定义于values  2024年1月30日22:00:36
       (simple-function-metadata?	;本文件的record 谓词 2024年1月30日22:01:45
        (applicable-object->object object)))) ;values中定义 2024年1月30日22:02:25

;;;; Function predicates

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

(define function-predicate-codomain
  (predicate-template-accessor 'codomain function-template))

(define (simple-function-tag function)
  (applicable-object-tag function))

(define (simple-function-predicate function)
  (tag->predicate (simple-function-tag function)))

(define (simple-function-codomain function)
  (function-predicate-codomain
   (simple-function-predicate function)))

(define (simple-function-procedure function)
  (simple-function-metadata-procedure
   (applicable-object->object function)))

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

(define function-predicate-domains
  (predicate-template-accessor 'domains function-template))

(define (simple-function-arity function)
  (length (simple-function-domains function)))

(define (apply-union-function function args)
  (let ((fit (union-function-apply-fit function args)))
    (if (not fit)
        (error 'apply-union-function "Inapplicable functio" function args))
    (fit)))

(define (union-function-apply-fit function args)
  (let ((fits (union-function-component-fits function args)))
    (and (pair? fits)
         (combine-fits object-union* fits))))

(define (is-function-subsumed? function functions)
  (let ((predicate (simple-function-predicate function)))
    (any (lambda (function*)
           (let ((predicate*
                  (simple-function-predicate function*)))
             (and (not (eqv? predicate* predicate))
                  (every
                   (lambda (domain* domain)
                     (predicate<= domain* domain))
                   (function-predicate-domains predicate*)
                   (function-predicate-domains predicate)))))
         functions)))

(define (union-function-components union)
  (object-union-components (applicable-object->object union)))

(define (function-components function)
  (cond ((simple-function? function)
         (list function))
        ((union-function? function)
         (union-function-components function))
        (else
         (error:not-a function? function))))

(define (union-function-component-fits function args)
  (let ((fits
         (map (lambda (function)
                (simple-function-apply-fit
                   function args))
              (union-function-components function))))
    (let ((functions
           (filter-map (lambda (function fit)
                         (and fit function))
                       (union-function-components function)
                       fits)))
      (filter-map (lambda (function fit)
                    (and fit
                         (not
                          (is-function-subsumed? function
                                                 functions))
                         fit))
                  (union-function-components function)
                  fits))))

(define (union-function* functions)
  (guarantee-list-of function? functions)
  (if (null? functions)
      (error union-function* "Can't make an empty union function."))
  (let ((simple-functions
         (append-map function-components functions)))
    (let ((arity (simple-function-arity (car simple-functions))))
      (for-each
       (lambda (simple-function)
         (if (not (= arity
                       (simple-function-arity simple-function)))
             (error 'union-function*-for-each "Inconsistent arity in unio"
                    arity
                    (simple-function-arity simple-function))))
       (cdr simple-functions)))
    (if (and (pair? simple-functions)
             (null? (cdr simple-functions)))
        (car simple-functions)
        (letrec
            ((union-function
              (let ((union (make-object-union simple-functions)))
                (make-object-applicable
                 (get-predicate union)
                 union
                 (lambda args
                   (apply-union-function union-function
                                         args))))))
          union-function))))

(define (union-function? object)
  (and (applicable-object? object)
       (let ((object* (applicable-object->object object)))
         (and (object-union? object*)
              (every simple-function?
                     (object-union-components object*))))))

(define func-uf (register-predicate! union-function? 'union-function))

(define (function? object)
  (or (simple-function? object)
      (union-function? object)))

(define func-func  (begin (register-predicate! function? 'function)
			  (set-predicate<=! union-function? function?)
			  (register-predicate! simple-function? 'simple-function)
			  (set-predicate<=! simple-function? function?)
			  ))


;;; 原generic 的部分
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
