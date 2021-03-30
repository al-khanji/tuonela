;;;; tuonela.lisp

(in-package #:tuonela)

(defclass module ()
  ((magic :initarg magic)
   (version :initarg version)
   (sections :initarg sections)))

(defclass section ()
  ((id :initarg id)
   (size :initarg size)
   (start :initarg start)
   (end :initarg end)))

(defclass unknown-section (section)
  ((bytes :initarg bytes)))

(defclass custom-section (section)
  ((name :initarg name)
   (bytes :initarg bytes)))

(defclass type-section (section)
  ((functypes :initarg functypes)))

(defclass function-section (section)
  ((typeidxs :initarg typeidxs)))

(defmethod print-object ((module module) stream)
  (with-slots (magic version sections) module
    (print-unreadable-object (module stream :type t)
      (format stream "~@<magic=~A ~:_version=~A ~:_sections=~A~:>" magic version sections))))

(defmethod print-object ((section section) stream)
  (with-slots (id size start end) section
    (print-unreadable-object (section stream :type t)
      (format stream "~@<id=~A ~:_size=~A ~:_start=~A ~:_end=~A~:>" id size start end))))

(defun read-bytes (stream count)
  (let ((array (make-array count :element-type '(unsigned-byte 8))))
    (read-sequence array stream)
    array))

(defun leb128-chunks (i &optional (step 7))
  (check-type i integer)
  (check-type step integer)
  (do ((bytes)
       (len (* step
	       (ceiling (/ (integer-length i)
			   step))))
       (byte (ldb (byte step 0) i)
	     (ldb (byte step p) i))
       (p step (+ step p)))
      ((> p len) bytes)
    (push byte bytes)))

(defun integer->leb128 (i &optional (step 7))
  (check-type i integer)
  (check-type step integer)
  (let* ((chunks (leb128-chunks i step))
	 (result (list (or (car chunks) 0))))
    (dolist (chunk (cdr chunks) result)
      (push (dpb 1 (byte 1 step) chunk) result))))

(defun unsigned->signed (n length chunk-size)
  (let* ((bits (* length chunk-size))
	 (negative-offset (expt 2 bits))
	 (max (1- (/ negative-offset 2))))
    (if (> n max)
	(- n negative-offset)
	n)))

(defun leb128->integer (chunks &key signed (step 7))
  (loop for index from 0
	and chunk in chunks
	for chunklet = (ldb (byte step 0) chunk)
	for result = chunklet then (dpb chunklet
					(byte step (* step index))
					result)
	finally (progn
		  (assert (< chunk (ash 1 step)))
		  (return (if signed
			      (unsigned->signed result (1+ index) step)
			      result)))))

(defgeneric read-wasm-type (stream type))

(macrolet
    ((make-integer-reader (type signed size)
       `(defmethod read-wasm-type (stream (type (eql ',type)))
	  (let ((chunks (loop repeat ,(/ size 8)
			      for chunk = (read-byte stream)
			      collect chunk
			      until (< chunk ,(ash 1 7)))))
	    (leb128->integer chunks :signed ,signed))))
     (frobber ()
       `(progn
	  ,@(loop for size in '(8 16 32 64)
		  append (loop for (prefix signed) in '((u nil) (i nil) (s t))
			       for type = (read-from-string (format nil "~A~A" prefix size))
			       collect `(make-integer-reader ,type ,signed ,size))))))
  (frobber))

(defmethod read-wasm-type (stream (type (eql 'functype)))
  (let ((magic (read-byte stream)))
    (assert (= magic #x60))
    (let* ((rt1 (read-wasm-vector stream 'u8))
	   (rt2 (read-wasm-vector stream 'u8)))
      (list rt1 rt2))))

(defun read-wasm-vector (stream type)
  (let* ((length (read-wasm-type stream 'u32))
	 (vector (make-array length)))
    (dotimes (i length vector)
      (setf (aref vector i) (read-wasm-type stream type)))))

(defmethod read-wasm-type (stream (type (eql 'name)))
  (read-wasm-vector stream 'u8))

(defgeneric read-wasm-section (stream size id))

(defmethod read-wasm-section (stream size id)
  (let* ((start-pos (file-position stream))
	 (bytes (read-bytes stream size)))
    (make-instance 'unknown-section
		   'id id
		   'size size
		   'start start-pos
		   'end (file-position stream)
		   'bytes bytes)))

(defmethod read-wasm-section (stream size (id (eql 0)))
  (let* ((start-pos (file-position stream))
	 (name (read-wasm-type stream 'name))
	 (second-pos (file-position stream))
	 (bytes (read-bytes stream (- size (- second-pos start-pos)))))
    (make-instance 'custom-section
		   'id id
		   'size size
		   'start start-pos
		   'end (file-position stream)
		   'name name
		   'bytes bytes)))

(defmethod read-wasm-section (stream size (id (eql 1)))
  (let* ((start-pos (file-position stream))
	 (functypes (read-wasm-vector stream 'functype)))
    (make-instance 'type-section
		   'id id
		   'size size
		   'start start-pos
		   'end (file-position stream)
		   'functypes functypes)))

(defmethod read-wasm-section (stream size (id (eql 3)))
  (let* ((start-pos (file-position stream))
	 (typeidxs (read-wasm-vector stream 'u32)))
    (make-instance 'function-section
		   'id id
		   'size size
		   'start start-pos
		   'end (file-position stream)
		   'typeidxs typeidxs)))

(defun read-wasm-module (stream)
  (let* ((magic (read-bytes stream 4))
	 (version (read-bytes stream 4))
	 (sections (loop for id = (read-byte stream nil nil)
			 while id
			 for size = (read-wasm-type stream 'u32)
			 collect (read-wasm-section stream size id))))
    (make-instance 'module
		   'magic magic
		   'version version
		   'sections sections)))
