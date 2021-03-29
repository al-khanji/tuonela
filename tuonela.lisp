;;;; tuonela.lisp

(in-package #:tuonela)

(defclass module ()
  ((magic :initarg :magic :initform nil)
   (version :initarg :version :initform nil)
   (sections :initarg :sections :initform nil)))

(defclass section ()
  ((id :initarg :id )
   (size :initarg :size)
   (start :initarg :start)
   (end :initarg :end)))

(defclass unknown-section (section)
  ((bytes :initarg :bytes)))

(defclass custom-section (section)
  ((name :initarg :name)
   (bytes :initarg :bytes)))

(defmethod print-object ((module module) stream)
  (with-slots (magic version sections) module
    (print-unreadable-object (module stream :type t)
      (format stream "~<magic=~A~>~<version=~A~>~<sections=~A~>" magic version sections))))

(defmethod print-object ((section section) stream)
  (with-slots (id size start end) section
    (print-unreadable-object (section stream :type t)
      (format stream "id=~A size=~A start=~A end=~A" id size start end))))

(defun read-bytes (stream count)
  (let ((array (make-array count :element-type '(unsigned-byte 8))))
    (read-sequence array stream)
    array))

(defgeneric read-wasm-type (stream type))

(defmethod read-wasm-type (stream (type (eql '(unsigned-byte 32))))
  (loop repeat 4
	for chunk = (read-byte stream)
	collect chunk
	until (< chunk #b10000000)))

(defmethod read-wasm-type (stream (type (eql '(unsigned-byte 8))))
  (read-byte stream))

(defun read-wasm-vector (stream type)
  (let* ((length (read-wasm-type stream 'u32))
	 (vector (make-array length)))
    (dotimes (i length vector)
      (setf (aref vector i) (read-wasm-type stream type)))))

(defmethod read-wasm-type (stream (type (eql 'name)))
  (read-wasm-vector stream '(unsigned-byte 8)))

(defgeneric read-wasm-section (stream size id))

(defmethod read-wasm-section (stream size id)
  (let* ((start-pos (file-position stream))
	 (bytes (read-bytes stream size)))
    (make-instance 'unknown-section
		   :id id
		   :size size
		   :start start-pos
		   :end (file-position stream)
		   :bytes bytes)))

(defmethod read-wasm-section (stream size (id (eql 0)))
  (let* ((start-pos (file-position stream))
	 (name (read-wasm-type stream 'name))
	 (second-pos (file-position stream))
	 (bytes (read-bytes stream (- size (- second-pos start-pos)))))
    (make-instance 'custom-section
		   :id id
		   :size size
		   :start start-pos
		   :end (file-position stream)
		   :name name
		   :bytes bytes)))

(defun read-wasm-module (stream)
  (let* ((magic (read-bytes stream 4))
	 (version (read-bytes stream 4))
	 (sections (loop for id = (read-byte stream nil nil)
			 while id
			 for size = (read-wasm-type stream '(unsigned-byte 32))
			 collect (read-wasm-section stream size id))))
    (make-instance 'module
		   :magic magic
		   :version version
		   :sections sections)))
