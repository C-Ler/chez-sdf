(library-directories 
 '("D:\\lib" "D:\\lib\\thunderchez-trunk"
   "D:\\lib" "D:\\lib\\scheme-lib\\packages"
   "D:\\lib" "D:\\lib\\slib"
   ))


(library (sdf sdf)
  (export
   ;; 测试用
   call-with-output-string
   ;; gp
   gp-pred-md-init			;将一些r6rs谓词注册为htmd谓词  2024年1月15日20:13:24
   simple-generic-procedure
   define-generic-procedure-handler
   match-args
   generic-procedure-name
   generic-procedure-arity
   generic-procedure-rules
   generic-procedure-handlers
   generic-procedure-metadata
   simple-list-memoizer
   simple-lset-memoizer
   make-simple-dispatch-store
   make-trie-dispatch-store		;当把默认的dispatch-store换为这个之后就得到了效率高的GP,但是无法通过这个实现谓词组合的匹配  2024年3月8日16:09:56
   cache-wrapped-dispatch-store		;使用了simple-list-memoizer,传入make-xx-dispatch-store,一般是hashtable,用于实现基于tag的匹配方式,避免apply谓词同时支持谓词组合  2024年3月8日22:02:52
   ;; make-default-dispatch-store 用的时候根据需要来定义 2024年1月1日19:26:55
   generic-procedure-constructor	;(generic-procedure-constructor make-simple-dispatch-store) -> simple-generic-procedure
   make-metadata-association
   make-hash-table-store		;测试make-metadata-association的void过程源头用
   make-alist-store
   make-key-weak-eq-hash-table
   make-key-weak-eqv-hash-table
   predicate?
   get-predicate-metadata
   set-predicate-metadata!
   generic-procedure?
   %generic-procedure-metadata
   set-generic-procedure-metadata!
   ;; register-predicate!   ;在udp的predicates中重新定义了 2024年1月25日22:43:47
   constant-generic-procedure-handler
   guarantee
   guarantee-list-of
   error:not-a
   error:wrong-type-argument
   ;; applicability
   predicates-match? 
   ;; chaining-generic-procedure
   ;; define-record-printer  ;utlis提供的set-predicate-metadata!
   ;; c pred-md
   predicate-description
   ;; common predicates
   is-list-of
   is-non-empty-list-of
   is-pair-of
   complement
   conjoin
   disjoin
   
   equal*?
   equal*-predicate
   make-equal-hash-table
   make-weak-eq-set
  
   fix:+
   hash-table-intern!
   hash-table-clear!
   every
   any
   default-object?
   plist?
   count
   plist-value
   symbol-append
   lset-difference
   append-map
   exact-integer?
   non-empty-list?
   list-of-unique-symbols?
   n:pair?
   lset-adjoin
   eq-predicate
   eqv-predicate
   equal-predicate
   lset-union
   all-sequences-of
   delete-duplicates
   filter-map
   lset=
   ;;
   index-predicate
   index->booleans
   ;; chez-mit
   delv
   delq!
   lambda*
   define*
   )
  
  (import
   (except (chezscheme) make-hash-table) ;应该给这句前面加个prefix 来避免修改 n:pair?这类
   (only (srfi s1 lists) reduce-right append-map take drop lset-adjoin lset-difference lset-union delete-duplicates lset= filter-map )
   (srfi s8 receive)			;因为部分过程引用了 srfi的..... 2023年12月11日21:42:19
   (mit curry)
   (only (mit core) write-line declare default-object? exact-integer? delv)		;srfi出了问题,strings import private let-opt,单独import也没问题,但是export的:optional依然是未绑定变量,如果load let-opt再import就不会报错...  2023年12月21日19:24:31
   ;; 两个路径都有srfi造成的... 2023年12月21日22:19:38
   (only (chez-srfi %3a1) count)
   ;; (only (chez-srfi %3a39) make-parameter)  chez有定义 2024年1月15日20:17:54
   (only (chez-srfi %3a125) hash-table-intern! make-hash-table
	 hash-table-keys hash-table-ref hash-table-set! hash-table-contains? hash-table-clear!) ;本质上是对R6RS的过程进行了扩展  2024年1月6日20:16:43
   ;; (only (chez-srfi %3a69)  hash-table-exists?)  ;69是荒废的....调用过程时候有个warning,提示了,查阅了文档,说是R6RS定义了等价的hashtable-contains?  2024年1月6日15:57:54
   (only (mit hash-tables) make-key-weak-eq-hash-table make-key-weak-eqv-hash-table strong-hash-table/constructor equal-hash-mod eqv-hash-mod)
   (only (mit arithmetic) fix:+)
   (only (mit list) alist?  delq!)
   ;; (only (chez-srfi %3a128) make-list-hash)
   )

  (define n:pair? pair?)

  (define (symbol-append . x)
    (string->symbol (apply string-append (map symbol->string x))))

  (define every for-all)			;扩展实现every
  (define any exists)

  (define (list-of-unique-symbols? ls)
    (for-all symbol? ls))

  (define (non-empty-list? ls) (not (null? ls)))

  (define hash-table-exists? hash-table-contains?)

  (define eq-hash equal-hash)		;memorizers中未定义的过程的简单替换 2023年12月23日17:00:13
  (define eqv-hash equal-hash)

  (define weak-list->list (lambda (x) x))
  (define weak-memq memq)

  (define (make-equal-hash-table)	;目前引用这个的过程会报错,tagging.scm,试图load adventure-world的时候,第二遍load就会变成另一种异常  2024年1月5日23:19:05
    ((strong-hash-table/constructor equal-hash-mod equal? #t
				    ;; hash-table-entry-type:strong
				    ))	
    )
  ;;
  (define default-object void)		;这个东西个debug增加了难度... 2024年3月3日20:52:53
  
  ;; utlis 这个实现远不如hash,只是为了方便得将('name "爱宠" 'health 3)转化为冒险游戏的属性 2024年3月2日17:19:43
  (define (plist? object)
    (and (list? object)
	 (even? (length object))))

  (define (plist->alist plist)
    (guarantee plist? plist 'plist->alist)
    (let loop ((plist plist))
      (if (pair? plist)
          (cons (cons (car plist)
                      (cadr plist))
		(loop (cddr plist)))
          '())))

  (define (alist->plist alist)
    (guarantee alist? alist 'alist->plist)
    (let loop ((alist alist))
      (if (pair? alist)
          (cons (car (car alist))
		(cons (cdr (car alist))
                      (loop (cdr alist))))
          '())))

  (define (plist-value plist key)
    (define (loop plist)
      (if (pair? plist)
          (begin
            (if (not (pair? (cdr plist)))
		(lose))
            (if (eqv? (car plist) key)
		(car (cdr plist))
		(loop (cdr (cdr plist)))))
          (begin
            (if (not (null? plist))
		(lose))
            (default-object))))

    (define (lose)
      (error:not-a plist? plist 'plist-value))

    (loop plist))

  ;; predicates.scm 需要的过程
  (define sdf-void (void))

  (define (void? x)
    (eq? x sdf-void))
  
  (define (error:wrong-type-argument datum type operator) ;用于实现guarantee及其对ls的扩展,这个expected应该是个gp谓词的predicate-description返回值,但是实际结果是这个谓词的描述是某种内建对象,根本不是str,直接将内建对象write到port了... 2024年1月27日11:42:02
    
    (error  (if (void? operator)
		'error:wrong-type-argument
		operator)
	    (string-append "wrong argument type, expected: " type " and datum as:") datum))

  (define (list-of-type? object predicate)
    (let loop ((l1 object) (l2 object))
      (if (pair? l1)
          (and (predicate (car l1))
               (let ((l1 (cdr l1)))
		 (and (not (eq? l1 l2))
                      (if (pair? l1)
                          (and (predicate (car l1))
                               (loop (cdr l1) (cdr l2)))
                          (null? l1)))))
          (null? l1))))

  ;; 
  (define (%cars+cdrs lists)
    (let loop ((lists lists) (cars '()) (cdrs '()))
      (if (pair? lists)
	  (if (null? (car lists) #f)
	      (values '() '())
	      (loop (cdr lists)
		    (cons (caar lists) cars)
		    (cons (cdar lists) cdrs)))
	  (values (reverse! cars) (reverse! cdrs)))))

  (define call-with-output-string
    (lambda (f)
      (let ((outsp (open-output-string)))
	(f outsp)
	(let ((s (get-output-string outsp)))
	  (close-output-port outsp)
	  s))))

  ;;来自 utlis ,应该把这个东西自己单独定义成library  2023年12月18日20:53:45
  (define (all-sequences-of arity zero one) ;对一个(0 1 2) (0 1 2 3 4) 2的参数个数次方调用了 inde->choices 2024-1-15 23:08:27
    (map (lambda (index)
           (index->choices index arity zero one))
	 (iota (expt 2 arity))))

  (define (index->choices index arity zero one)
    (let loop ((i 0) (index index) (choices '()))
      (if (< i arity)
          (loop (+ i 1)
		(quotient index 2)	;index的步进是 index和2的商??
		(cons (if (odd? index) one zero)
                      choices))
          choices)))

  (include "collections.scm")

  (include "predicates.scm")		;是用metadata扩展后的谓词  2023年12月18日20:38:02
  (include "predicate-metadata.scm")
  (include "predicate-counter.scm")

  (include "applicability.scm")

  (include "trie.scm")
  (include "memoizers.scm")
  (include "generic-procedures.ss")

  (include "indexes.scm")

  ;; (include "utils.scm")			;会有重复定义,只能局部搬运 2024年1月6日22:22:06
  
  )
