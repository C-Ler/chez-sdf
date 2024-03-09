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

;;;; Properties,用了record实现,但是因为二次修饰了,导致后面定义一个属性就得手工构造record本来可以自动构造的东西....  2024年3月4日19:55:16
(define-record-type (<property> %make-property property?)
  (fields (immutable name property-name)
	  (immutable predicate property-predicate)
	  (immutable default-supplier property-default-supplier))
  )

(define (make-property name . plist)	;构造属性的方法,对record做了封装,plist可以换成hashtable  2023年12月31日16:26:26
  (guarantee symbol? name)		;相较于书中的示例代码,少了提示的文本 2023年12月31日16:14:51
  (guarantee property-list? plist)
  (%make-property name
                  (get-predicate-property plist)
                  (get-default-supplier-property plist)))

(define (property-list? object)
  (and (plist? object)
       (<= (count (lambda (keyword)	;(count number? '(1 2)) -> 2  2024年1月22日19:46:18
                    (not (default-object?
                           (plist-value object keyword))))
                  property-default-keywords)
           1)))

(define (get-predicate-property plist)
   (let ((predicate (plist-value plist 'predicate)))
     (if (not (default-object? predicate))
         predicate
         any-object?)))

(define (get-default-supplier-property plist)
  (let ((value (plist-value plist 'default-value))
        (supplier (plist-value plist 'default-supplier))
        (property (plist-value plist 'default-to-property)))
    (cond ((not (default-object? value))
           (lambda (lookup) value))	;有点迷惑  2023年12月31日16:28:14
          ((not (default-object? supplier))
           (lambda (lookup) (supplier)))
          ((not (default-object? property))
           (lambda (lookup) (lookup property)))
          (else #f))))

(define property-default-keywords
  '(default-value default-supplier default-to-property))

(define property-keywords
  `(predicate ,@property-default-keywords))

(define (property-optional? property)
  (if (property-default-supplier property) #t #f))

;; (define-record-printer <property>	;需要引用utlis中定义的过程,暂时先注释掉 2023年12月31日21:49:26
;;   (lambda (property)
;;     (list (property-name property))))

;;;; Types

(define (make-type name properties)	;基于属性谓词的类型构造,type就是名字加属性list构造的gp,实际使用的时候被create-xxtype 封装  2024年1月22日19:51:23
  (guarantee-list-of property? properties)
  (let ((type (simple-abstract-predicate name instance-data?)))
    (%set-type-properties! type properties)
    type))

(define (get-binding property instance)	
  (instance-data-binding property (tagged-data-data instance)))	

;;; Simplified interface for text -- GJS

(define (get-property-value property object) ;获取实例的属性  2024年1月22日21:01:17
  ((get-binding property object)))

(define (set-property-value! property object value) ;给实例的指定属性赋值 2024年1月22日21:01:32
  ((get-binding property object) value))

(define (type-properties type)		;某一type的全部属性,封装了下面的过程 2024年1月22日21:01:55
  (append-map %type-properties
              (cons type (all-supertypes type))))

(define (all-supertypes type)
  (filter type? (all-predicate-supersets type)))

(define type?)
(define %type-properties)
(define %set-type-properties!)

(let ((association (make-metadata-association)))
  (set! type? (association 'has?))
  (set! %type-properties (association 'get))
  (set! %set-type-properties! (association 'put!)))

;;;; Instantiation

(define (type-instantiator type)	;某一type实例的构造器,构造了type之后应该自动生成一个对应的,原代码目前没实现  2024年1月22日21:03:20
  (let ((constructor (predicate-constructor type)) 
        (properties (type-properties type)))
    (lambda plist
      (let ((object
             (constructor (parse-plist plist properties))))
        (set-up! object)
        object))))

;;; TODO: use properties as the keys in the plist.
(define (parse-plist plist properties)	;这个plist形如'(k1 v1 k2 v2 ...)
  (define (lookup-value property)
    (let ((value (plist-value plist (property-name property))))
      (if (default-object? value)
          (begin
            (if (not (property-optional? property))
                (error 'parse-plist "Missing required property:"
                       (property-name property)
                       plist))
            ((property-default-supplier property) lookup-value))
          value)))

  (make-instance-data
   (map (lambda (property)
          (cons property (lookup-value property)))
        properties)))

(define set-up!				;error-generic-procedure-handler: Inapplicable generic procedure: with irritants (get-tag-shared (#[#{simple-tag ggb5i5qobi1g1l6270n43mnon-63} #[...]]))
  (chaining-generic-procedure 'set-up! 1
    (constant-generic-procedure-handler #f)))

(define tear-down!
  (chaining-generic-procedure 'tear-down! 1
    (constant-generic-procedure-handler #f)))

;;;; Instance data

(define instance-data?			;type的实例是一个gp谓词过程,用于构造属性 2024年1月22日19:58:52
  (simple-abstract-predicate 'instance-data procedure?))

(define make-instance-data		;用于parse-plist,实例化type用 2024年1月22日21:07:32
  (let ((constructor
         (predicate-constructor instance-data?)))
    (lambda (bindings)
      (constructor
       (lambda* (#:optional property)
         (if (default-object? property)
             (map car bindings)
             (let ((p (assv property bindings)))
               (if (not p)
                   (error 'make-instance-data "Unknown property:" property))
               (lambda* (#:optional new-value)
			(if (default-object? new-value)
			    (cdr p)
			    (set-cdr! p new-value))))))))))

(define instance-data-bindings
  (predicate-accessor instance-data?))	;这个东西返回的过程报错 incorrect number of arguments to #<procedure at adventure-substrate.scm:5110> ,这种问题十分难以定位,过于恶心 2024年1月10日20:41:35

(define (instance-data-properties instance-data)
  ((instance-data-bindings instance-data)))

(define (instance-data-binding property instance-data)  
  ((instance-data-bindings instance-data) property))

;;;; Methods

(define (property-getter property type)
  (let ((procedure
         (most-specific-generic-procedure
          (symbol-append 'get-  (property-name property))
          1
          (lambda (object)
	    (display (get-name object))
	    (newline)))))
    (define-generic-procedure-handler procedure
      (match-args type)
      (lambda (object)
        (get-property-value property object)))
    procedure))

(define (property-setter property type value-predicate)	;如果两个类型拥有同一个属性呢?
  (let ((procedure
         (most-specific-generic-procedure
          (symbol-append 'set- (property-name property) '!)
          2
          #f)))
    (define-generic-procedure-handler procedure
      (match-args type value-predicate)
      (lambda (object value)
	(let ((binding (get-binding property object))) ;获取这个binding到调用的过程,没有任何问题
          (%binding-set-prefix property value (binding) object)	;纯粹用来方便debug的... 2024年3月4日18:48:31
          (binding value))))
    procedure))

;; (define-syntax property-setter
;;   (syntax-rules ()
;;     [(_ property type value-predicate)
;;      (let ((name (symbol-append 'set- (property-name property) '!)))
;;        (define name (most-specific-generic-procedure
;; 		     (symbol-append 'set- (property-name property) '!)
;; 		     2
;; 		     #f))
;;        (define-generic-procedure-handler name
;; 	 (match-args type value-predicate)
;; 	 (lambda (object value)
;; 	   (let ((binding (get-binding property object))) ;获取这个binding到调用的过程,没有任何问题
;;              (%binding-set-prefix property value (binding) object)	;纯粹用来方便debug的... 2024年3月4日18:48:31
;;              (binding value)))))]))

(define (%binding-set-prefix property new-value old-value object)
  (if debug-output
      (begin
        (send-message! (list ";setting" (possessive object)
                             (property-name property)
                             "to" new-value)
                       debug-output)
        (send-message! (list ";previous value was" old-value)
                       debug-output))))

(define (property-modifier property type value-predicate
                           noun modifier)
  (let ((procedure
         (most-specific-generic-procedure
          (symbol-append (property-name property) '- noun)
          2
          #f)))
    (define-generic-procedure-handler procedure
      (match-args type value-predicate)
      (lambda (object item)
        (let* ((binding (get-binding property object))
               (old-value (binding))
               (new-value (modifier item old-value)))
          (%binding-set-prefix property new-value old-value
                               object)
          (binding new-value))))
    procedure))

(define (property-adder property type value-predicate)
  (property-modifier property type value-predicate 'adder
                     (lambda (value values)
                       (lset-adjoin eqv? values value))))

(define (property-remover property type value-predicate)
  (property-modifier property type value-predicate 'remover
                     (lambda (value values)
                       (delv value values))))

;;; Misc
;;; 冒险游戏需要用到的其它东西
(define (direction? object)
  (if (memv object known-directions) #t #f))

(register-predicate! direction? 'direction)

(define known-directions
  '(north south east west in out up down skew))

(define (display-to-string object)
  (call-with-output-string
    (lambda (port)
      (display object port))))

(define (random-choice items)
  (guarantee list? items)
  (and (pair? items)
       (list-ref items (random (length items)))))

(define (random-number n)
  (+ (random n) 1))

(define (bias? object)
  (and (real? object)
       (<= 0 object 1)))
(register-predicate! bias? 'bias)

(define (random-bias weight)
  (/ 1 (random-number weight)))

(define (flip-coin bias)
  (>= (random 1.0) bias))

;;; Base object type

(define object:name
  (make-property 'name))

(define object:description
  (make-property 'description
                 'default-to-property object:name))

(define object?
  (make-type 'object (list object:name object:description)))

(define get-name 			;;这里报错 variable symbol is not bound 2024年1月8日20:31:47
  (property-getter object:name object?))

(define get-description			
  (property-getter object:description object?))

(define (find-object-by-name name objects)
  (find (lambda (object)
          (eqv? name (get-name object)))
        objects))

(define-generic-procedure-handler tagged-data-representation ;这两个可能起到某种作用,比如pp 示例中的各种obj  2024年2月19日20:56:38
  (match-args object?)
  (lambda (super object)
    (append (super object)
            (list (get-name object)))))

(define-generic-procedure-handler tagged-data-description
  (match-args object?)
  (lambda (object)
    (let ((instance-data (tagged-data-data object)))
      (map (lambda (property)
             (list (property-name property)
                   ((instance-data-binding property
                                           instance-data))))
           (instance-data-properties instance-data)))))

;;; Messaging

(define send-message!			;这个gp在 adventure-obj中,只扩展了对thing? place? avatar?的情况  2024年1月22日21:27:12
  (most-specific-generic-procedure 'send-message! 2 (lambda (msg obj)
						      (match-args message? object?)
  (let ((scr (make-screen 'name 'the-screen))) ;原本只是个#f,接着报错了,怀疑是捡起东西后提示某物到哪过于简陋 2024年1月23日21:49:58
    (lambda (message thing)
      (display-message (type-properties thing))
      (display-message message (get-port scr)))))))

(define (narrate! message person-or-place)
  (send-message! message
                 (if (person? person-or-place)
                     (get-location person-or-place)
                     person-or-place))
  (if debug-output
      (send-message! message debug-output)))

(define (tell! message person)
  (send-message! message person)
  (if debug-output
      (send-message! message debug-output)))

(define (say! person message)
  (narrate! (append (list person "says:") message)
            person))

(define (announce! message)
  (for-each (lambda (place)
              (send-message! message place))
            (get-all-places))
  (if debug-output
      (send-message! message debug-output)))

(define debug-output #f)

(define (enable-debugging)
  (if (not debug-output)
      (set! debug-output (make-screen 'name 'debug))))

(define (disable-debugging)
  (if debug-output
      (set! debug-output #f)))

(define (display-message message port)
  (guarantee message? message 'display-message)
  (if (pair? message)
      (begin
        (fresh-line port)
        (display-item (car message) port)
        (for-each (lambda (item)
                    (display " " port)
                    (display-item item port))
                  (cdr message)))))

(define (display-item item port)
  (display (if (object? item) (get-name item) item) port))

(define (message? object)
  (list? object))

(register-predicate! message? 'message)

(define (possessive person)
  (string-append (display-to-string (get-name person))
                 "'s"))

;;; Screen

(define screeport
  (make-property 'port
                 'predicate output-port?
                 'default-supplier current-output-port))

(define screen?
  (make-type 'screen (list screeport)))

(set-predicate<=! screen? object?)

(define make-screen
  (type-instantiator screen?))

(define get-port
  (property-getter screeport screen?))

(define-generic-procedure-handler send-message!
  (match-args message? screen?)
  (lambda (message screen)
    (display-message message (get-port screen))))

;;; Clock

(define (make-clock)
  (%make-clock 0 '()))

(define-record-type (<clock> %make-clock clock?)
  (fields (mutable current-time current-time set-current-time!)
	  (mutable things clock-things set-clock-things!)))

(define (register-with-clock! thing clock) ;下面这两个函数调用了clock-things 传入的clock参数为<void>  2024年1月11日19:51:59 只被objct 的set-up!调用 2024年1月11日20:47:13
  (guard (x [(error? x) (显示thing) (搞个新的clock)])
    (set-clock-things! clock
		       (lset-adjoin eqv?
                                    (clock-things clock)
                                    thing))))

(define (unregister-with-clock! thing clock)
  (set-clock-things! clock
                     (delv thing (clock-things clock))))

(define (tick! clock)
  (set-current-time! clock (+ (current-time clock) 1))
  (for-each (lambda (thing) (clock-tick! thing))
            (clock-things clock)))

(define clock-tick!
  (chaining-generic-procedure 'clock-tick! 1
    (constant-generic-procedure-handler #f)))

(define (define-clock-handler type action)
  (define-generic-procedure-handler clock-tick!
    (match-args type)
    (lambda (super object)
      (super object)
      (action object))))
