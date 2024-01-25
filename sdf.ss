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
   make-trie-dispatch-store
   cache-wrapped-dispatch-store
   ;; make-default-dispatch-store 用的时候根据需要来定义 2024年1月1日19:26:55
   generic-procedure-constructor
   make-metadata-association
   make-hash-table-store		;测试make-metadata-association的void过程源头用
   make-alist-store
   make-key-weak-eqv-hash-table
   predicate?
   get-predicate-metadata
   set-predicate-metadata!
   generic-procedure?
   %generic-procedure-metadata
   set-generic-procedure-metadata!
   register-predicate!
   constant-generic-procedure-handler
   guarantee
   guarantee-list-of
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
   lambda*
   define*
   equal*?
   equal*-predicate
   make-equal-hash-table
   make-weak-eq-set
   conjoin
   disjoin
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
   is-list-of
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
   ;; chez-mit
   delv
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
   (only (mit hash-tables) make-key-weak-eqv-hash-table strong-hash-table/constructor equal-hash-mod eqv-hash-mod)
   (only (mit arithmetic) fix:+)
   (only (mit list) alist?)
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
  (define default-object void)
  ;; utlis
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
  (define (error:wrong-type-argument value expected caller)
    (error  'error:wrong-type-argument (string-append "wrong argument type, expected " expected "and caller value:") caller value))

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

  ;; (include "utils.scm")			;会有重复定义,只能局部搬运 2024年1月6日22:22:06

  
  (include "user-defined-types\\tags.scm")
  (include "user-defined-types\\tagging.scm") ;通过在gp及record的基础上实现谓词tag相关过程,进而实现tagged data  2024年1月24日21:24:38
  (include "user-defined-types\\predicates.scm") ;谓词的md就是tag,tag data是基于谓词和data构造的,还有谓词的组合,关系,tag及基础关系谓词的注册 2024年1月24日21:31:12
  (include "user-defined-types\\templates.scm")	;参数匹配用 2024年1月24日21:32:46
  (include "user-defined-types\\values.scm")  ;没详细阅读 2024年1月24日21:39:04
  
  (include "user-defined-types\\functions.scm")	;没细读,疑似对原有函数的扩展 2024年1月24日21:42:31
  (include "user-defined-types\\generics.scm") ;SDF P90 多种匹配存储的构造方式  2024年1月24日21:23:35
  
  )
