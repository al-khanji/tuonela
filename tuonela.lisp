;;;; tuonela.lisp

(in-package #:tuonela)

;; LEB128

(declaim (inline leb128-length))
(defun leb128-length (i)
  (* 7 (ceiling (integer-length i) 7)))

(defun integer->leb128 (i)
  (mapl (lambda (x)
	  (when (cdr x)
	    (rplaca x (+ (car x) #x80))))
	(loop for pos from 0 by 7 below (leb128-length i)
	      collect (ldb (byte 7 pos) i))))

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

;; Stream stuff

(defclass sequence-stream-wrapper ()
  ((seq :initarg :sequence)
   (pos :initarg :start :initform 0)
   (length)))

(defmethod initialize-instance :after ((ssw sequence-stream-wrapper) &rest initargs)
  (declare (ignore initargs))
  (with-slots (seq length) ssw
    (setf length (length seq))))

(defmacro with-input-from-sequence ((var seq &optional (start 0)) &body body)
  `(let ((,var (make-instance 'sequence-stream-wrapper :sequence ,seq :start ,start)))
     ,@body))

(defgeneric read-byte (stream &optional eof-error-p eof-value))

(defmethod read-byte ((stream stream) &optional (eof-error-p t) (eof-value nil))
  (cl:read-byte stream eof-error-p eof-value))

(defmethod read-byte ((stream sequence-stream-wrapper) &optional (eof-error-p t) (eof-value nil))
  (with-slots (seq pos length) stream
    (if (< pos length)
	(prog1 (elt seq pos)
	  (incf pos))
	(if eof-error-p
	    (error 'end-of-file :stream stream)
	    eof-value))))

(defgeneric read-sequence (sequence stream &key start end))

(defmethod read-sequence (sequence (stream stream) &key (start 0) (end nil))
  (cl:read-sequence sequence stream :start start :end end))

(defmethod read-sequence (sequence (stream sequence-stream-wrapper) &key (start 0) (end nil))
  (when (null end) (setf end (length sequence)))
  (loop while (< start end)
	for elem = (read-byte stream nil nil)
	while elem
	do (setf (elt sequence start) elem)
	do (incf start)
	finally (return start)))

(defgeneric file-position (stream &optional position-spec))

(defmethod file-position ((stream stream) &optional (position 0 position-supplied-p))
  (if position-supplied-p
      (cl:file-position stream position)
      (cl:file-position stream)))

(defmethod file-position ((stream sequence-stream-wrapper) &optional (position 0 position-supplied-p))
  (with-slots (pos length) stream
    (if position-supplied-p
	(if (< position length)
	    (progn (setf pos position)
		   t)
	    nil)
	pos)))

(defun read-bytes (count in &optional (seq (make-array count :element-type '(unsigned-byte 8))))
  (read-sequence seq in :start 0 :end count)
  seq)

;; Embedding

(defstruct (store (:constructor store-init))
  funcs tables mems globals elems datas)

(defstruct moduleinst
  types funcaddrs tableaddrs memaddrs globaladdrs elemaddrs dataaddrs exports)

(defstruct module
  types funcs tables mems globals elems datas start imports exports custom)

(defstruct functype
  parameters results)

(defstruct func
  type locals body)

(defstruct import
  module name desc)

(defstruct export
  name desc)

(defun module-decode (bytes)
  (with-input-from-sequence (in bytes)
    (read-binary-module in)))

(defun module-validate (module)
  t)

(defun module-instantiate (store module externvals)
  )

;; Binary Format
(define-condition bad-binary-module (error)
  ((msg :initarg :msg :reader msg :initform "")))

(defmacro with-gensyms ((&rest names) &body body)
  `(let ,(loop for n in names collect `(,n (gensym ,(string n))))
     ,@body))

(defun check-magic (in &rest expected)
  (flet ((okay (expected actual)
	   (= actual
	      (etypecase expected
		(character (char-code expected))
		(integer expected)))))
    (loop for expected in expected
	  for actual = (read-byte in)
	  if (okay expected actual)
	    collect actual
	  else
	    do (error 'bad-binary-module))))

(defgeneric read-binary-value (type in))

(defmethod read-binary-value ((type (eql 'byte)) in)
  (read-byte in))

(defmacro define-integer-readers (&rest sizes)
  (labels ((make-integer-reader (name max-bytes signed)
	     `(defmethod read-binary-value ((type (eql ',name)) in)
		(loop repeat ,max-bytes
		      for byte = (read-binary-value 'byte in)
		      collect byte into chunks
		      until (< byte #x80)
		      finally (return (if (< byte #x80)
					  (leb128->integer chunks :signed ,signed)
					  (error 'bad-binary-module))))))
	   (make-integer-readers (size)
	     (loop for type in '(u s i)	       
		   for name = (read-from-string (format nil "~A~A" type size))
		   for max-bytes = (ceiling size 7)
		   for signed = (ecase type
				  (u nil)
				  ((s i) t))
		   collect (make-integer-reader name max-bytes signed))))
    `(progn ,@(loop for size in sizes
		    append (make-integer-readers size)))))

(define-integer-readers 7 8 16 32 64)

(defmacro define-index-readers (&rest indexes)
  (flet ((make-reader (index)
	   `(defmethod read-binary-value ((type (eql ',index)) in)
	      (read-binary-value 'u32 in))))
    (cons 'progn (loop for index in indexes
		       collect (make-reader index)))))

(define-index-readers
  typeidx
  funcidx
  tableidx
  memidx
  globalidx
  elemidx
  dataidx
  localidx
  labelidx)

(defmethod read-binary-value ((type (eql 'name)) in)
  (sb-ext:octets-to-string (read-binary-vector 'byte in
					       :element-type '(unsigned-byte 8))
			   :external-format :utf-8))

(defmethod read-binary-value ((type (eql 'functype)) in)
  (check-magic in #x60)
  (make-functype :parameters (read-binary-vector 'valtype in)
		 :results (read-binary-vector 'valtype in)))

(defmethod read-binary-value ((type (eql 'import)) in)
  (make-import :module (read-binary-value 'name in)
	       :name (read-binary-value 'name in)
	       :desc (read-binary-value 'importdesc in)))

(defmethod read-binary-value ((type (eql 'export)) in)
  (make-export :name (read-binary-value 'name in)
	       :desc (read-binary-value 'exportdesc in)))

(defmethod read-binary-value ((type (eql 'importdesc)) in)
  (case (read-binary-value 'byte in)
    (#x00 (list 'func (read-binary-value 'typeidx in)))
    (#x01 (list 'table (read-binary-value 'tabletype in)))
    (#x02 (list 'mem (read-binary-value 'memtype in)))
    (#x03 (list 'global (read-binary-value 'globaltype in)))))

(defmethod read-binary-value ((type (eql 'exportdesc)) in)
  (case (read-binary-value 'byte in)
    (#x00 (list 'func (read-binary-value 'funcidx in)))
    (#x01 (list 'table (read-binary-value 'tableidx in)))
    (#x02 (list 'mem (read-binary-value 'memidx in)))
    (#x03 (list 'global (read-binary-value 'globalidx in)))))

(defmethod read-binary-value ((type (eql 'code)) in)
  (let* ((size (read-binary-value 'u32 in))
	 (start (file-position in))
	 (locals (read-binary-vector 'valtype in))
	 (elem-count (- size (- (file-position in) start)))
	 (elems (read-bytes elem-count in)))
    (list locals elems)))

(defparameter *numtypes*
  '((#x7F . i32)
    (#x7E . i64)
    (#x7D . f32)
    (#x7C . f64)))

(defparameter *reftypes*
  '((#x70 . funcref)
    (#x6F . externref)))

(defparameter *valtypes* (append *numtypes* *reftypes*))

(defmacro make-byte-mapper (type byte-map)
  `(defmethod read-binary-value ((type (eql ',type)) in)
     (let* ((byte (read-binary-value 'byte in))
	    (result (rest (assoc byte ,byte-map))))
       (if result
	   result
	   (error 'bad-binary-module)))))

(make-byte-mapper numtype *numtypes*)
(make-byte-mapper reftype *reftypes*)
(make-byte-mapper valtype *valtypes*)

(defun read-binary-vector (type in &key (element-type t) (constructor #'identity))
  (let* ((count (read-binary-value 'u32 in))
	 (vector (make-array count :element-type element-type)))
    (dotimes (i count)
      (setf (aref vector i)
	    (funcall constructor (read-binary-value type in))))
    vector))

(defparameter *binary-sections* nil)

(defgeneric read-binary-section (id size module in))

(defmacro define-binary-section (id name &body spec)
  (with-gensyms (idvar)
    `(progn
       (eval-when (:load-toplevel)
	 (push (cons ,id ',name) *binary-sections*))
       
       ,(destructuring-bind ((size module in) &body body) (rest (assoc :reader spec)) 
          `(defmethod read-binary-section ((,idvar (eql ,id)) ,size ,module ,in)
	     ,@body)))))

(define-binary-section 0 customsec
  (:reader
   (size module in)
   (let* ((startpos (file-position in))
	  (name (read-binary-value 'name in))
	  (byte-count (- size (- (file-position in) startpos)))
	  (bytes (read-bytes byte-count in)))
     (with-slots (custom) module
       (push (cons name bytes) custom)))))

(define-binary-section 1 typesec
  (:reader
   (size module in)
   (setf (slot-value module 'types)
	 (read-binary-vector 'functype in))))

(define-binary-section 2 importsec
  (:reader
   (size module in)
   (setf (slot-value module 'imports)
	 (read-binary-vector 'import in))))

(define-binary-section 3 funcsec
  (:reader
   (size module in)
   (setf (slot-value module 'funcs)
	 (read-binary-vector 'typeidx in
			     :constructor (lambda (type) (make-func :type type))))))

(define-binary-section 7 exportsec
  (:reader
   (size module in)
   (setf (slot-value module 'exports)
	 (read-binary-vector 'export in))))

(define-binary-section 10 codesec
  (:reader
   (size module in)
   (let ((code-count (read-binary-value 'u32 in))
	 (module-funcs (module-funcs module)))
     (when (/= code-count (length module-funcs))
       (error 'bad-binary-module))
     (loop repeat code-count
	   for func across module-funcs
	   do (destructuring-bind (locals exprs) (read-binary-value 'code in)
		(setf (func-locals func) locals
		      (func-body func) exprs))))))

(defparameter *binary-section-order*
  '(typesec
    importsec
    funcsec
    tablesec
    memsec
    globalsec
    exportsec
    startsec
    elemsec
    datacountsec
    codesec
    datasec))

(defun check-section-id-order (prev next)
  ;; this is broken
  (let ((prev-position (position prev *binary-section-order*))
	(next-position (position next *binary-section-order*)))
    (cond ((and prev-position next-position)
	   (if (< prev-position next-position)
	       next
	       (error 'bad-binary-module)))
	  (next-position next)
	  (t prev))))

(defun read-binary-module (in)
  (let* ((module (make-instance 'module))
	 (magic (check-magic in #\Nul #\a #\s #\m))
	 (version (check-magic in 1 0 0 0)))
    (loop for id = (read-byte in nil nil)
	  while id
	  for old-id = nil then (check-section-id-order old-id id)
	  for size = (read-binary-value 'u32 in)
	  do (read-binary-section id size module in))
    (values module magic version)))
