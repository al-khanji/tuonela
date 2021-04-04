;;;; tuonela.lisp

(in-package #:tuonela)

(defmacro print-values (values stream)
  (let ((format-string (format nil "~~@<~{~A=~~A~^ ~~:_~}~~:>" values)))
    `(format ,stream ,format-string ,@values)))

(defmacro print-object-slots (slots object stream)
  `(with-slots ,slots ,object
     (print-values ,slots ,stream)))

(defclass module ()
  ((magic :initarg magic :accessor magic)
   (version :initarg version :accessor version)
   (sections :initarg sections :accessor sections)))

(defmethod print-object ((module module) stream)
  (print-unreadable-object (module stream :type t)
    (let ((*print-base* 16)
	  (*print-radix* t))
      (print-object-slots (magic version sections) module stream))))

(defclass section ()
  ((id :initarg id :accessor id)
   (size :initarg size :accessor size)
   (start :initarg start :accessor start)))

(defmacro defsection (name slot-names)
  `(prog1
     (defclass ,name (section)
       ,(loop for slot-name in slot-names
	      collect (list slot-name
			    :initarg slot-name
			    :accessor slot-name)))
     (defmethod print-object ((section ,name) stream)
       (print-unreadable-object (section stream :type t)
	 (with-slots (id size start ,@slot-names) section
	   (let ((end (+ size start)))
	     (let ((*print-base* 16)
		   (*print-radix* t))
	       (print-values (id size start end ,@slot-names) stream))))))))

(defsection unknown-section (bytes))
(defsection custom-section (name bytes))
(defsection type-section (functypes))
(defsection import-section (imports))
(defsection function-section (typeidxs))
;; table
;; memory
;; global
(defsection export-section (exports))
;; start
;; element
(defsection code-section (codes))
;; data
;; data count

(declaim (inline leb128-length))
(defun leb128-length (i)
  (* 7 (ceiling (integer-length i) 7)))

(defun integer->leb128 (i)
  (declare (type integer i))
  (loop for pos from 0 by 7 below (leb128-length i)
	for chunk = (ldb (byte 7 pos) i)
	for octet = chunk then (logior chunk (ash 1 7))
	collect octet))

(declaim (inline unsigned->signed))
(defun unsigned->signed (n size)
  (logior n (- (mask-field (byte 1 (1- size)) n))))

(defun leb128->integer (chunks &key signed)
  (loop for bits from 0 by 7
	for chunk in chunks
	for septet = (mask-field (byte 7 0) chunk)
	for result = septet then (dpb septet (byte 7 bits) result)
	finally (return (if signed
			    (unsigned->signed result bits)
			    result))))

(defun leb128-roundtrip (n &optional (signed (< n 0)))
  (let* ((encoded (integer->leb128 n))
	 (decoded (leb128->integer encoded :signed signed)))
    (values n encoded decoded)))

(defgeneric read-wasm-type (stream type))

(macrolet
    ((make-integer-reader (type signed size)
       `(defmethod read-wasm-type (stream (type (eql ',type)))
	  (let ((chunks (loop repeat ,(ceiling size 7)
			      for chunk = (read-byte stream)
			      collect chunk
			      until (< chunk ,(ash 1 7)))))
	    (leb128->integer chunks :signed ,signed))))
     (frobber ()
       `(progn
	  ,@(loop for size in '(8 16 32 64)
		  append (loop for (prefix signed) in '((#\u nil) (#\i nil) (#\s t))
			       for type = (read-from-string (format nil "~C~D" prefix size))
			       collect `(make-integer-reader ,type ,signed ,size))))))
  (frobber))

(defmethod read-wasm-type (stream (type (eql 'valtype)))
  (let ((b (read-wasm-type stream 'byte)))
    (ecase b
      (#x7F 'i32)
      (#x7E 'i64)
      (#x7D 'f32)
      (#x7C 'f64)
      (#x70 'funcref)
      (#x6F 'externref))))

(defmethod read-wasm-type (stream (type (eql 'functype)))
  (let ((magic (read-byte stream)))
    (assert (= magic #x60))
    (let* ((rt1 (read-wasm-vector stream 'valtype))
	   (rt2 (read-wasm-vector stream 'valtype)))
      (list rt1 rt2))))

(defun read-wasm-vector (stream type &key (element-type t))
  (let* ((length (read-wasm-type stream 'u32))
	 (vector (make-array length :element-type element-type)))
    (dotimes (i length vector)
      (setf (aref vector i) (read-wasm-type stream type)))))

(defmethod read-wasm-type (stream (type (eql 'name)))
  (let ((bytes (read-wasm-vector stream 'byte
				 :element-type '(unsigned-byte 8))))
    (or
     #+sbcl (sb-ext:octets-to-string bytes :external-format :utf-8)
     #-sbcl (map 'string #'code-char bytes))))

(defmethod read-wasm-type (stream (type (eql 'byte)))
  (read-byte stream))

(defmethod read-wasm-type (stream (type (eql 'importdesc)))
  (let ((type (read-wasm-type stream 'byte))
	(desc (read-wasm-type stream 'u32)))
    (list (ecase type
	    (#x00 'typeidx)
	    (#x01 'tabletype)
	    (#x02 'memtype)
	    (#x03 'globaltype))
	  desc)))

(defmethod read-wasm-type (stream (type (eql 'import)))
  (let* ((mod (read-wasm-type stream 'name))
	 (nm (read-wasm-type stream 'name))
	 (d (read-wasm-type stream 'importdesc)))
    `((mod . ,mod)
      (nm . ,nm)
      (d . ,d))))

(defmethod read-wasm-type (stream (type (eql 'exportdesc)))
  (let ((type (read-wasm-type stream 'byte))
	(desc (read-wasm-type stream 'u32)))
    (list (ecase type
	    (#x00 'typeidx)
	    (#x01 'tabletype)
	    (#x02 'memtype)
	    (#x03 'globaltype))
	  desc)))

(defmethod read-wasm-type (stream (type (eql 'export)))
  (let* ((nm (read-wasm-type stream 'name))
	 (d (read-wasm-type stream 'exportdesc)))
    `((nm . ,nm)
      (d . ,d))))

(defmethod read-wasm-type (stream (type (eql 'code)))
  (let* ((size (read-wasm-type stream 'u32))
	 (locals-start-pos (file-position stream))
	 (locals (read-wasm-vector stream 'valtype))
	 (expr-start-pos (file-position stream))
	 (expr-count (- size (- expr-start-pos
				locals-start-pos)))
	 (expr (read-bytes stream expr-count)))
    (assert (= #x0b (aref expr (1- expr-count))))
    `((size . ,size)
      (locals . ,locals)
      (expr . ,expr))))

(defun section-id->section-type (id)
  (case id
    (0 'custom-section)
    (1 'type-section)
    (2 'import-section)
    (3 'function-section)
    ;; table
    ;; memory
    ;; global
    (7 'export-section)
    ;; start
    ;; element
    (10 'code-section)
    ;; data
    ;; data count
    (t 'unknown-section)))

(defun read-wasm-section (stream size id)
  (let ((section (make-instance (section-id->section-type id)
				'id id
				'size size
				'start (file-position stream))))
    (initialize-section-from-stream section stream)
    section))

(defgeneric initialize-section-from-stream (section stream))

(defmethod initialize-section-from-stream :around ((section section) stream)
  (call-next-method)
  (let ((current (file-position stream))
	(expected (+ (start section) (size section))))
    (unless (= current expected)
      (let ((*print-base* 16)
	    (*print-radix* t))
	(format t "currently at ~A but expected ~A after reading ~:_~A ~%"
		current expected section)
	(file-position stream expected)))))

(defmethod initialize-section-from-stream ((section unknown-section) stream)
  (setf (bytes section) (read-bytes stream (size section))))

(defmethod initialize-section-from-stream ((section custom-section) stream)
  (let* ((name (read-wasm-type stream 'name))
	 (bytes-start (file-position stream))
	 (bytes (read-bytes stream (- (size section)
				      (- bytes-start
					 (start section))))))
    (setf (name section) name
	  (bytes section) bytes)))

(defmethod initialize-section-from-stream ((section type-section) stream)
  (setf (functypes section) (read-wasm-vector stream 'functype)))

(defmethod initialize-section-from-stream ((section import-section) stream)
  (setf (imports section) (read-wasm-vector stream 'import)))

(defmethod initialize-section-from-stream ((section function-section) stream)
  (setf (typeidxs section) (read-wasm-vector stream 'u32)))

(defmethod initialize-section-from-stream ((section export-section) stream)
  (setf (exports section) (read-wasm-vector stream 'export)))

(defmethod initialize-section-from-stream ((section code-section) stream)
  (setf (codes section) (read-wasm-vector stream 'code)))

(defun read-bytes (stream count)
  (let ((array (make-array count :element-type '(unsigned-byte 8))))
    (values array (read-sequence array stream))))

(defun %make-stream-slurper (stream)
  (lambda (cmd &rest args)
    (ecase cmd
      (position (if (null args)
		     (file-position stream)
		     (apply #'file-position (cons stream args))))
      (get-byte (read-byte stream nil nil))
      (get-bytes (let* ((n-bytes (car args))
			 (array (make-array n-bytes :element-type '(unsigned-byte 8))))
		    (values array (read-sequence array stream)))))))

(defun %read-wasm-module (slurper)
  (let* ((magic (slurper 'get-bytes 4))
	 (version (slurper 'get-bytes 4))
	 (sections (loop for id = (slurper 'get-byte)
			 while id
			 for size = (%read-wasm-type slurper 'u32)
			 collect (%read-wasm-section slurper size id))))
    (make-instance 'module
		   'magic magic
		   'version version
		   'sections sections)))

(defun read-wasm-module (stream)
  (%read-wasm-module (%make-stream-slurper stream)))

(defun slurp-wasm-module (filename)
  (with-open-file (s filename :element-type '(unsigned-byte 8))
    (read-wasm-module s)))

(defvar *wast-package* (make-package 'tuonela-wast :use nil))

(defun wast-module (&rest arguments)
  (let (name bindata exprs)
    (loop for (x . xs) on arguments
	  if (string-equal 'binary x)
	    return (setf bindata (apply #'concatenate 'vector xs))
	  else
	  if (char= #\$ (char (string x) 0))
	     do (push x name)
	  else
	    return (setf exprs xs))
    (push (or bindata exprs)
	  name)
    (nreverse name)))

(defun wast-assert_malformed (form msg)
  (list 'yoyo form (sb-ext:octets-to-string msg)))

(setf (symbol-function (intern "module" *wast-package*)) #'wast-module)
(setf (symbol-function (intern "assert_malformed" *wast-package*)) #'wast-assert_malformed)

(defmacro with-wast-io-syntax (&body body)
  `(with-standard-io-syntax 
     (labels ((escaped-char-reader (stream char)
		(declare (ignore char))
		(let* ((b (read-byte stream))
		       (c (code-char b)))
		  (case c
		    (#\t #x09)
		    (#\n #x0A)
		    (#\r #x0D)
		    (#\" #x22)
		    (#\' #x27)
		    (#\\ #x5C)
		    (t (parse-integer (coerce (list c (code-char (read-byte stream)))
					      'string)
				      :radix 16)))))
	      (double-quote-reader (stream char)
		(declare (ignore char))
		(loop for b = (read-byte stream)
		      for c = (code-char b)
		      for count from 0
		      until (char= #\" c)
		      if (char= #\\ c)
			collect (escaped-char-reader stream b) into chars
		      else
			collect b into chars
		      finally (return (make-array count
						  :element-type '(unsigned-byte 8)
						  :initial-contents chars)))))
       (let* ((*package* *wast-package*)
	      (*readtable* (copy-readtable))
	      (*read-eval* nil))
	 (set-macro-character #\" #'double-quote-reader *readtable*)
	 (setf (readtable-case *readtable*) :preserve)
	 (progn ,@body)))))

(defun read-wast (stream)
  (with-wast-io-syntax
    (loop with eof-marker = 'read-wast-eof
	  for form = (read-preserving-whitespace stream nil eof-marker)
	  until (eq form eof-marker)
	  collect form)))

(defun eval-wast (form)
  (if (atom form)
      form
      (apply (symbol-function (car form))
	     (mapcar #'eval-wast (cdr form)))))
