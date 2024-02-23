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

;;; 原tagging的部分  2024年1月30日21:13:00
;;;; Generic tag access

(define (tagged-data= t1 t2)
  (and (eq? (tagged-data-tag t1) (tagged-data-tag t2))
       (equal*? (tagged-data-data t1) (tagged-data-data t2))))

(define tagging-gd (begin (define-generic-procedure-handler get-data
			    (match-args tagged-data?)
			    tagged-data-data)
			  (define-generic-procedure-handler equal*? ;顺手再扩展equal?的gp 2024年1月20日13:36:41
			    (match-args tagged-data? tagged-data?)
			    tagged-data=)))

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




;;;; Tagging strategies






