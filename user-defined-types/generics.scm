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
;;; 原generic 的部分
;;; tagging 的部分  2024年2月1日20:07:31
(define-record-type (<tagged-data> %make-tagged-data tagged-data?)
  (fields (immutable tag tagged-data-tag) (immutable data tagged-data-data))
  )

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

(define (tagging-strategy:never name data-test make-tag) ;不加tag  2024年1月20日17:42:47

  (define (constructor data)		
    (if (not (data-test data))		;加了一个重复出现的结构,判断data是否满足data-test的,这种东西到处出现 2024年1月20日13:40:15
        (error 'tagging-strategy:never (string-append "Ill-formed data for " (symbol->string name) ":")
               data))
    data)

  (define tag
    (make-tag data-test constructor (lambda (object) object)))
  
  tag)

;;; predicates的部分 2024年1月30日22:35:04
;;;; Basic tag structure
;;; 原predicate的简单替换 2024年1月30日21:31:23
(define predicate->tag get-predicate-metadata) ;common 中 pred-md-get 的简单替换 从metadata实现的pred中取东西出来.  2024年1月10日21:39:59

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

(define (get-all-tag-supersets tag)
  (let loop ((queue (list tag))
	     (supersets '()))
    (if (pair? queue)
        (let ((tag (car queue))
              (queue (cdr queue)))
          (let ((new-sets
                 (lset-difference eqv?
                                  (get-tag-supersets tag)
                                  supersets)))
            (if (pair? new-sets)
                (loop (append new-sets queue)
                      (append new-sets supersets))
                (loop queue supersets))))
        supersets)))

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

;;;; Simple predicates
(define-record-type (<simple-tag> %make-simple-tag simple-tag?)
  (fields (immutable shared simple-tag-shared)))

;; (define-tag-record-printer <simple-tag>)  ;为了避免出现lib化报语法错误的权宜之计.... 2024年2月3日17:48:18

(define tagging-st (define-tag-type simple-tag? simple-tag-shared))

(define (make-simple-tag name data-test tagging-strategy)
  (%invoke-tagging-strategy tagging-strategy name data-test
                            %make-simple-tag))

(define (simple-predicate? object)
  (and (predicate? object)
       (simple-tag? (predicate->tag object))))

(define (make-simple-predicate name data-test tagging-strategy)	;从tag-rtd中获取pred
  (tag->predicate
   (make-simple-tag name data-test tagging-strategy)))

(define (simple-abstract-predicate name data-test)
  (make-simple-predicate name data-test tagging-strategy:always))

(define (register-predicate! predicate name) ;predicate-metadata.scm 当中已经定义过了,这里覆盖了,之前的版本只是构造mdht中的name pred键值对,单纯的原生谓词,无法构造结构和层次.这里没有明显的put,不知道怎么能和之前的md起作用 2024年1月20日18:30:17
  (guarantee procedure? predicate)
  (make-simple-predicate name predicate tagging-strategy:never))

(define pred-reg
  (begin
    (register-predicate! tagged-data? 'tagged-data)
    (register-predicate! tag? 'tag)
    (register-predicate! predicate? 'predicate)
    (register-predicate! simple-predicate? 'simple-predicate)))

(define (predicate-name predicate)	;这里的pred是md  2024年2月16日21:21:21
  (tag-name (predicate->tag predicate)))

(define (parametric-predicate? object)
  (and (predicate? object)
       (parametric-tag? (predicate->tag object))))

(define (predicate-constructor predicate)
  (tag-constructor (predicate->tag predicate)))

(define (predicate-accessor predicate)
  (tag-accessor (predicate->tag predicate)))

(define (predicate-supersets predicate)
  (map tag->predicate
       (get-tag-supersets (predicate->tag predicate))))

(define (all-predicate-supersets predicate)
  (map tag->predicate
       (get-all-tag-supersets (predicate->tag predicate))))

;;; 用来判断标签1是否是标签2的子集
(define (false-tag<= tag1 tag2) ;; (declare (ignore tag1 tag2)),values的部分 使用了下面的过程,这个定义应该没必要. 2024年2月18日20:42:26
  ;; predicates文件引用了这个过程,用来扩展多个gp 2024年2月19日19:03:27
  #f)
 
(define generic-tag<=
  (simple-generic-procedure 'generic-tag<= 2 false-tag<=))

(define (uncached-tag<= tag1 tag2)
  (or (eqv? tag1 tag2)
      (generic-tag<= tag1 tag2)
      (any (lambda (tag)
             (cached-tag<= tag tag2))
           (get-tag-supersets tag1))))

(define tag<=-cache
  (make-equal-hash-table))

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

(define (tag= tag1 tag2)
  (guarantee tag? tag1)
  (guarantee tag? tag2)
  (eqv? tag1 tag2))

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

(define (predicate= predicate1 predicate2)
  (tag= (predicate->tag predicate1)
        (predicate->tag predicate2)))

(define (set-predicate<=! predicate superset)
  (set-tag<=! (predicate->tag predicate)
              (predicate->tag superset)))

(define any-object? (conjoin))
(define no-object? (disjoin))

(define simple-pred-rl
  (begin
    (register-predicate! simple-tag? 'simple-tag)
    (set-predicate<=! simple-tag? tag?)
    (set-predicate<=! simple-predicate? predicate?))
  )

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


;;; taggs的部分 2024年1月30日21:13:09
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

(define parametric-re
  (bebin
   (register-predicate! parametric-tag? 'parametric-tag)
   (set-predicate<=! parametric-tag? tag?)
   (set-predicate<=! parametric-predicate? predicate?)))

;; (define-tag-record-printer <parametric-tag>)
(define (parametric-predicate-template predicate)
  (parametric-tag-template (predicate->tag predicate)))

(define pred-pp (begin
		  (define-tag-type parametric-tag? parametric-tag-shared)
		  (register-predicate! parametric-predicate? 'parametric-predicate)))

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




