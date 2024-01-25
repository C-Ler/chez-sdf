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
;;;; Generic procedures
(define gp-association (make-metadata-association))

(define generic-procedure? (gp-association 'has?))
(define %generic-procedure-metadata (gp-association 'get))
(define set-generic-procedure-metadata! (gp-association 'put!))

(define (n:exact-nonnegative-integer? n)
  (and (integer? n) (>= n 0)))

(define (generic-procedure-constructor dispatch-store-maker)
  ;; P140,避免了硬编码
  ;; (generic-procedure-constructor make-simple-dispatch-store) -> simple-generic-procedure
  ;; 根据上面的示例,调用这个过程会返回一个用来构造gp的过程,但是没法对同一个gp使用多种匹配存储的形式,对于参数数量不确定的过程也是个问题  2023年12月4日19:26:14
  ;; 一个名字如同generic-move!的gp中,会保持一个metadata的闭包
  ;; 得让metadata有个接口,能够访问和修改,先修改dispatch-store,再修改metadata,还要保证返回的the-generic-procedure可以直接(gp args ...)  2023年12月4日22:33:21
  ;; 没提供(get-gp-metadata gp)的方法,一个很关键的问题,metadata为什么要包含名称,参数数量?如果直接用dispatch-store取代呢?  2023年12月4日22:29:21
  ;; 修改默认的rule,提供一个特殊谓词,对应一个handler,用来获取metadata,另一个set-metadata-handler!用来将修改后的metadata替换,如果接口恰好被重名,会有问题.  2023年12月4日22:40:35
  ;; 据说这种方式允许define-genericprocedure-handler 修改metadata  2023年12月5日19:23:29
  (lambda (name arity default-handler)
    (guarantee n:exact-nonnegative-integer? arity) ;确保参数个数是正整数  2024年1月16日22:17:07 
    (let ((metadata
           (make-generic-metadata name	;在下面用record实现了 2024年1月16日22:39:22
                                  arity
                                  (dispatch-store-maker) ;传入的过程参数,比如下面那个make-simple-dispatch-store
				  (or default-handler
				      (error-generic-procedure-handler name)))))
      (define (the-generic-procedure . args)
        (generic-procedure-dispatch metadata args)) ;P143给出实现,是另外一个过程的封装,从metadata中根据args匹配合适的handler并apply到args
      (set-generic-procedure-metadata! the-generic-procedure ;md的assoc中的put!将gp作为key,md作为value存入 2024年1月16日22:41:18
                                       metadata)
      the-generic-procedure)))

(define (generic-procedure-dispatch metadata args)
  ;; P143 核心,GP这种lambda在接受参数后不会直接求值,会先根据参数的类型匹配适合的过程handler,然后apply,上面的实现是为了实现这个功能.  2023年12月3日17:45:13
  ;; 被generic-procedure-constructor中的the-generic-procedure引用
  ;; P175 开始改良
  (let ((handler (get-generic-procedure-handler metadata args)))
    (if (trace-generic-dispatch?)	;相较于原书多出来的  2024年1月17日22:07:25
        (trace-generic-dispatch metadata args handler))
    (apply handler args)))

(define (constant-generic-procedure-handler constant)
  (hash-table-intern! %constant-generic-procedure-handlers
                      constant
                      (lambda ()
                        (lambda args
                          ;; (declare (ignore args)) ;ignore没找到定义,这个过程应该与参数无关 直接注释掉试试 2023年12月22日21:29:38
                          constant))))  

(define %constant-generic-procedure-handlers
  (make-eqv-hashtable))

(define (error-generic-procedure-handler name) ;只能匹配到默认gp的时候就会用到这个 2024年1月21日21:13:38
   (lambda args
    (error 'error-generic-procedure-handler "Inapplicable generic procedure:" name args)))

(define (trace-generic-dispatch metadata args handler)
  (parameterize ((trace-generic-dispatch? #f))
    (let ((port (trace-output-port)))
      (fresh-line port)
      (display ";Calling method of " port) ;display不知道能不能接受trace-output-port  2024年1月17日20:44:45
      (display (generic-metadata-name metadata) port)
      (display ": " port)
      (write handler port)
      (for-each (lambda (arg)
                  (display " " port)
                  (write arg port))
                args)
      (newline port))))

(define trace-generic-dispatch?
  (make-parameter #f))
					;下面这部分都是gpmd的二次封装 2024年1月17日21:02:54
(define (get-generic-procedure-handler metadata args)
  ;; p143
  ;; generic-metadata-getter and generic-metadata-defaultgetter
  ;; retrieve the get-handler procedure and the get-defaulthandler
  ;; procedure from the dispatch-store instance stored in the
  ;; metadata of the generic procedure
  (or ((generic-metadata-getter metadata) args)
      ((generic-metadata-default-getter metadata))))

(define (define-generic-procedure-handler generic-procedure
          applicability
          handler)
  (((generic-metadata-dispatch-store	;gpmd返回dispatch槽的访问器  2024年1月17日21:00:05
     (generic-procedure-metadata generic-procedure))
    'add-handler!)
   applicability
   handler))

(define (generic-procedure-name proc)
  (generic-metadata-name (generic-procedure-metadata proc)))

(define (generic-procedure-arity proc)
  (generic-metadata-arity (generic-procedure-metadata proc)))

(define (generic-procedure-rules proc)
  (((generic-metadata-dispatch-store
     (generic-procedure-metadata proc))
    'get-rules)))

(define (generic-procedure-handlers proc)
  (map cdr (generic-procedure-rules proc)))

(define (generic-procedure-metadata object)
  (define (try-object candidate)
    (if (generic-procedure? candidate)
        (%generic-procedure-metadata candidate)
        (let loop ((extractors generic-procedure-extractors))
          (if (not (pair? extractors))
              (error:not-a generic-procedure? candidate))
          (let ((val ((cdar extractors) candidate)))
            (if val
                (try-object val)
                (loop (cdr extractors)))))))
  (try-object object))

(define (define-generic-procedure-extractor name extractor)
  (let ((p (assq name generic-procedure-extractors)))
    (if p
        (set-cdr! p extractor)
        (let ((p (cons name extractor)))
          (set! generic-procedure-extractors
                (cons p generic-procedure-extractors))))))

(define generic-procedure-extractors '())

(define (assign-handler! procedure handler . preds) ;P154
  (define-generic-procedure-handler procedure
    (apply match-args preds)
    handler))

;;;; Metadata

(define-record-type (<generic-metadata> %make-generic-metadata generic-metadata?)
  (fields (immutable name generic-metadata-name)
	  (immutable arity generic-metadata-arity)
	  (immutable dispatcher generic-metadata-dispatch-store)
	  (immutable getter generic-metadata-getter)
          (immutable default-getter generic-metadata-default-getter)))

(define (make-generic-metadata name arity dispatcher
                               default-handler)
  ((dispatcher 'set-default-handler!) default-handler)
  (%make-generic-metadata name
                          arity
                          dispatcher
                          (dispatcher 'get-handler)
                          (dispatcher 'get-default-handler)))

;;;; Dispatcher implementations

(define (make-simple-dispatch-store)
  ;; P141
  ;; P175开始改良,对于一套参数来讲,可能有多个谓词组在同样的位置出现同样的谓词,因此效率很低,然后引入了Tries数据结构
  ;; P184为了实现谓词的组合,使用了tag,表示类型,更像ch2了.不过遇到素数这种东西,tag反而不如谓词.
  (let ((rules '())
        (default-handler #f))

    (define (get-handler args)
      ;; P142,对应的参数匹配会返回rules,否则#f
      ;; 这个过程是简单的返回第一个匹配的handle,如果有多个适配的话,也可以全部返回,对比结果,找出最好的.
      (let ((rule			;rules会形如((preds . handler) ...)
             (find (lambda (rule)	;简单得通过find来实现从list的rules中找到匹配所有参数类型的handler,如果用hash-table实现的话,得先取得所有键值,再遍历键值...
		     ;; 接受一个rule参数,形如(preds handler)的构造,通过predicates-match? 
                     (predicates-match? (car rule) args))
                   rules)))
        (and rule (cdr rule))))		;;在find到的rule不是#f的情况下通过cdr 返回handle

    (define (add-handler! applicability handler)
      ;; P142 简单的将已有的类型的handle替换,或者不存在的类型的handle加入assoc的头部
      (for-each (lambda (predicates)
                  (let ((p (assoc predicates rules)))
                    (if p
                        (set-cdr! p handler) ;rules是一个键值为参数类型匹配用的一组谓词和handler构成的p组成的list,可以换成hashtable
                        (set! rules
                              (cons (cons predicates handler)
                                    rules)))))
                applicability))

    (define (get-default-handler)
      default-handler)

    (define (set-default-handler! handler)
      (set! default-handler handler))

    (lambda (message)
      (case message
        ((get-handler) get-handler)
        ((add-handler!) add-handler!)
        ((get-default-handler) get-default-handler)
        ((set-default-handler!) set-default-handler!)
        ((get-rules) (lambda () rules))
        (else (error 'simple-dispatch-store "Unknown message:" message))))))

(define (make-trie-dispatch-store)	;这里用到了trie.scm,无法冗余,还是不够好  2024年1月16日22:48:35
  (let ((delegate (make-simple-dispatch-store))
        (trie (make-trie)))

    (define (get-handler args)
      (get-a-value trie args))

    (define (add-handler! applicability handler)
      ((delegate 'add-handler!) applicability handler)
      (for-each (lambda (path)
                  (set-path-value! trie path handler))
                applicability))

    (lambda (message)
      (case message
        ((get-handler) get-handler)
        ((add-handler!) add-handler!)
        (else (delegate message))))))

(define (cache-wrapped-dispatch-store dispatch-store get-key) ;这里用到了memoizer.scm  2024年1月16日22:49:18
  ;; P184
  ;; 第二个参数传入 get-tag这样的过程,如果用hash替代的话,可能可以直接用现成的实现来替代get-tag
  (let ((get-handler
         (simple-list-memoizer eqv?
                               (lambda (args) (map get-key args))
                               (dispatch-store 'get-handler))))
    (lambda (message)
      (case message
        ((get-handler) get-handler)
        (else (dispatch-store message))))))

(define simple-generic-procedure
  (generic-procedure-constructor make-simple-dispatch-store))

;;; API
(define make-default-dispatch-store
  make-simple-dispatch-store)

;;; Extensible equality predicate.
(define equal*?
  (simple-generic-procedure 'equal*? 2 equal?))

(define equal*-predicate
  (equality-predicate-maker 'equal*? equal*?))
