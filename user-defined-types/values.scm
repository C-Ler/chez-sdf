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

;;; values
(define-record-type (<object-union> %make-object-union object-union?)
  (fields (immutable tag object-union-tag)
	  (immutable components object-union-components)))

(define (make-object-union components)
  (%make-object-union (predicate->tag
                       (disjoin*
                        (map get-predicate components)))
                      components))

(define (object-union* components)
  (guarantee list? components)
  (if (and (pair? components)
           (null? (cdr components)))
      (car components)
      (let ((components
             (delete-duplicates
              (append-map (lambda (object)
                            (if (object-union? object)
                                (object-union-components object)
                                (list object)))
                          components)
              eqv?)))
        (cond ((not (pair? components))
               (make-object-union components))
              ((null? (cdr components))
               (car components))
              ((every function? components)
               (union-function* components))
              (else
               (make-object-union components))))))

(define (object-union . components)
  (object-union* components))

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

(define func-uf? (register-predicate! union-function? 'union-function))

(define (function? object)
  (or (simple-function? object)
      (union-function? object)))

(define func-func  (begin (register-predicate! function? 'function)
			  (set-predicate<=! union-function? function?)
			  (register-predicate! simple-function? 'simple-function)
			  (set-predicate<=! simple-function? function?)
			  ))


;;;; restriction of values

(define (restriction-error value predicate)
  (error 'restriction-error "Value doesn't fit predicate:" value predicate))

(define (make-object-applicable predicate object applicator)
  (guarantee procedure? applicator)
  ;; The procedure that is the applicable object must not be the
  ;; APPLICATOR argument.  This is so we can have several
  ;; applicable objects that share the same procedure but with
  ;; different metadata.
  (let ((applicable-object
         (lambda args (apply applicator args))))
    (set-applicable-object-metadata!
     applicable-object
     (make-applicable-object-metadata (predicate->tag predicate)
                                      object
                                      applicator))
    applicable-object))

(define (applicable-object-predicate object)
  (tag->predicate (applicable-object-tag object)))

(define (strip-applicable-wrapper object)
  (if (applicable-object? object)
      (applicable-object->object object)
      object))

;;;; Unions of objects

(define values-gt2 (begin
		     (register-predicate! object-union? 'object-union)

		     (define-generic-procedure-handler get-tag
		       (match-args object-union?)
		       object-union-tag)
		     
		     (define-generic-procedure-handler value-restriction
		       (match-args object-union? predicate?)
		       (lambda (value predicate)
			 (let ((components
				(filter predicate
					(object-union-components value))))
			   (and (pair? components)
				(lambda () (object-union* components))))))))

;; (define-record-printer <object-union>
;;   object-union-components)

(define (map-object-union procedure union)
  (object-union*
   (map procedure
        (object-union-components union))))

(define (append-map-object-union procedure union)
  (object-union*
   (append-map procedure
               (object-union-components union))))

(define (object-union= u1 u2)
  (lset= equal*?
         (object-union-components u1)
         (object-union-components u2)))

(define values-ou (define-generic-procedure-handler equal*?
		    (match-args object-union? object-union?)
		    object-union=))

;;;; Various debugging tools for tagged data

;; (define (pt object)
;;   (pp (rewrite-tags object)))		;估计是pretty-print

(define (rewrite-tags object)
  (cond ((tag? object)
         (tag-name object))
        ((predicate? object)
         (tag-name (predicate->tag object)))
        ((simple-function? object)
         `(function
           ,(simple-function-name object)
           ,(tag-name (simple-function-tag object))
           ,(strip-tags (simple-function-procedure object))))
        ((tagged-data? object)
         `(tagged-data ,(tag-name (tagged-data-tag object))
                       ,(strip-tags (tagged-data-data object))))
        ((applicable-object? object)
         `(applicable
           ,(rewrite-tags (applicable-object->object object))))
        ((object-union? object)
         `(union
           ,@(map rewrite-tags
                  (object-union-components object))))
        ((pair? object)
         (cons (rewrite-tags (car object))
               (rewrite-tags (cdr object))))
        ((vector? object)
         (vector-map rewrite-tags object))
        (else object)))

;; (define (pto object)
;;   (pp (tags-of object)))

(define (tags-of object)
  (cond ((tag? object)
         (tag-name object))
        ((predicate? object)
         (tag-name (predicate->tag object)))
        ((simple-function? object)
         (tag-name (simple-function-tag object)))
        ((tagged-data? object)
         (tag-name (tagged-data-tag object)))
        ((applicable-object? object)
         (tags-of (applicable-object->object object)))
        ((pair? object)
         (cons (tags-of (car object))
               (tags-of (cdr object))))
        ((vector? object)
         (vector-map tags-of object))
        (else
         (tag-name (get-tag object)))))

(define (strip-tags object)
  (cond ((simple-function? object)
         (strip-tags (simple-function-procedure object)))
        ((tagged-data? object)
         (strip-tags (tagged-data-data object)))
        ((applicable-object? object)
         (strip-tags (applicable-object->object object)))
        ((pair? object)
         (cons (strip-tags (car object))
               (strip-tags (cdr object))))
        ((vector? object)
         (vector-map strip-tags object))
        (else object)))
