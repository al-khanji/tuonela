;;;; package.lisp

(defpackage #:tuonela
  (:use #:cl)
  (:shadow #:read-byte
	   #:read-sequence
	   #:file-position
	   #:import
	   #:export))
