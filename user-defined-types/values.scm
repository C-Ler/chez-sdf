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

;;; functions
(define (simple-function-name function)
  (simple-function-metadata-name
   (applicable-object->object function)))

;;;; Restriction of values

(define (restriction-error value predicate)
  (error "Value doesn't fit predicate:" value predicate))

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
