(library-directories 
 '("D:\\lib" "D:\\lib\\thunderchez-trunk"
   "D:\\lib" "D:\\lib\\scheme-lib\\packages"
   "D:\\lib" "D:\\lib\\slib"
   ))


(library (sdf sdf-udp)
  (export
   chaining-generic-procedure
   get-tag-shared
   simple-abstract-predicate
   predicate-constructor
   predicate-accessor
   register-predicate!
   any-object?
   most-specific-generic-procedure
   tagged-data-data
   tagged-data-representation
   tagged-data-description
   set-predicate<=!
   all-predicate-supersets
   )
  
  (import
   (chezscheme)
   (sdf sdf)
   )

  ;; 下面这个文件中的过程,定义顺序很乱.... 2024年1月27日11:20:49
  ;; 将所有的register还有谓词关系全部后置,可能可行  2024年1月30日21:59:45
  
  (include "user-defined-types\\generics.scm") ;SDF P90 多种匹配存储的构造方式  2024年1月24日21:23:35
  (include "user-defined-types\\tagging.scm") ;通过在gp及record的基础上实现谓词tag相关过程,进而实现tagged data  2024年1月24日21:24:38
  (include "user-defined-types\\predicates.scm") ;谓词的md就是tag,tag data是基于谓词和data构造的,还有谓词的组合,关系,tag及基础关系谓词的注册 2024年1月24日21:31:12
  
  (include "user-defined-types\\templates.scm")	;参数匹配用 2024年1月24日21:32:46
  (include "user-defined-types\\values.scm")  ;没详细阅读 2024年1月24日21:39:04
  
  (include "user-defined-types\\functions.scm")	;没细读,疑似对原有函数的扩展 2024年1月24日21:42:31
 
  
  )
