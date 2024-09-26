(library-directories 
 '("D:\\lib" "D:\\lib\\thunderchez-trunk"
   "D:\\lib" "D:\\lib\\scheme-lib\\packages"
   "D:\\lib" "D:\\lib\\slib"
   ))


(library (sdf sdf-udp)
  (export
   ;; adventure-game needed
   ;; generic
   chaining-generic-procedure
   most-specific-generic-procedure
   ;; tagging
   tagged-data-data
   tagged-data-representation
   tagged-data-description
   ;; simple-predicates
   predicate->tag
   get-tag-shared
   simple-abstract-predicate
   register-predicate!			;注册,增加md
   predicate-constructor
   predicate-accessor   
   set-predicate<=!
   any-object?
   all-predicate-supersets

   ;; predicates
   is-list-of
   is-non-empty-list-of
   is-pair-of
   complement
   disjoin
   conjoin

   ;; maybe be used
   ;;simple-predicates 
   simple-predicate?
   predicate<=
   predicate>=
   predicate=
   ;; standard-arith needed
   make-predicate-template
   tagging-strategy:always
   predicate-template-instantiator
   predicate-template-predicate
   predicate-template-accessor
   predicate-constructor
   )
  
  (import
   (chezscheme)
   (except (sdf sdf) is-non-empty-list-of is-list-of is-pair-of complement conjoin disjoin)
   )

  ;; 下面这个文件中的过程,定义顺序很乱.... 2024年1月27日11:20:49
  ;; 将所有的register还有谓词关系全部后置,可能可行  2024年1月30日21:59:45
  
  (include "user-defined-types\\tagging.scm") ;通过在gp及record的基础上实现谓词tag相关过程,进而实现tagged data  2024年1月24日21:24:38
  (include "user-defined-types\\simple-predicates.scm")
  (include "user-defined-types\\tags.scm")
  (include "user-defined-types\\generics.scm") ;SDF P90 多种匹配存储的构造方式  2024年1月24日21:23:35
  
  (include "user-defined-types\\predicates.scm") ;谓词的md就是tag,tag data是基于谓词和data构造的,还有谓词的组合,关系,tag及基础关系谓词的注册 2024年1月24日21:31:12
  
  (include "user-defined-types\\templates.scm")	;参数匹配用 2024年1月24日21:32:46
  (include "user-defined-types\\values.scm")  ;没详细阅读 2024年1月24日21:39:04
  (include "user-defined-types\\functions.scm")	;没细读,疑似对原有函数的扩展 2024年1月24日21:42:31

  
 
 
  
  )
