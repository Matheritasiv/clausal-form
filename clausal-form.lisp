;;{{{ Input Macro Setup
(defvar *fun*     (make-symbol "FUN"))
(defvar *var*     (make-symbol "VAR"))
(defvar *true*    (make-symbol "TRUE"))
(defvar *false*   (make-symbol "FALSE"))
(defvar *wedge*   (make-symbol "WEDGE"))
(defvar *vee*     (make-symbol "VEE"))
(defvar *neg*     (make-symbol "NEG"))
(defvar *implies* (make-symbol "IMPLIES"))
(defvar *iff*     (make-symbol "IFF"))
(defvar *forall*  (make-symbol "FORALL"))
(defvar *exists*  (make-symbol "EXISTS"))
(set-macro-character #\$
  #'(lambda (stream char)
      (declare (ignore char))
      (let ((ch (peek-char nil stream t nil t)))
        (cond
          ((char-equal ch #\&)
             (read-char stream t nil t)
             (if (integerp (setf ch (read stream t nil t)))
               (list *fun* ch)))
          (t (case (setf ch (read stream t nil t))
               ((t) *true*)
               (f   *false*)
               (^   *wedge*)
               (v   *vee*)
               (~   *neg*)
               (=>  *implies*)
               (<=> *iff*)
               (a   *forall*)
               (e   *exists*)
               (otherwise
                 (if (integerp ch)
                   (list *var* ch)))))))))
;;}}}

;;{{{ Preprocess and Check
(defun desugar (l)
  (cond
    ((atom l)
     (if (symbolp l) l))
    ((or (eq (car l) *wedge*)
         (eq (car l) *vee*))
     (case (length l)
       (1 (if (eq (car l) *wedge*)
            *true* *false*))
       (2 (desugar (cadr l)))
       (otherwise
         (let ((arg1 (desugar (cadr l)))
               (arg2 (desugar (cons (car l)
                                    (cddr l)))))
           (if (and arg1 arg2)
             (list (car l) arg1 arg2))))))
    ((eq (car l) *neg*)
     (if (= (length l) 2)
       (let ((arg1 (desugar (cadr l))))
         (if arg1
           (list *neg* arg1)))))
    ((eq (car l) *implies*)
     (if (= (length l) 3)
       (let ((arg1 (desugar (cadr l)))
             (arg2 (desugar (caddr l))))
         (if (and arg1 arg2)
           (list *vee*
             (list *neg* arg1)
             arg2)))))
    ((eq (car l) *iff*)
     (if (= (length l) 3)
       (let ((arg1 (desugar (cadr l)))
             (arg2 (desugar (caddr l))))
         (if (and arg1 arg2)
           (list *wedge*
             (list *vee*
               (list *neg* arg1)
               arg2)
             (list *vee*
               (list *neg* (copy-tree arg2))
               (copy-tree arg1)))))))
    ((or (eq (car l) *forall*)
         (eq (car l) *exists*))
     (if (and (= (length l) 3)
              (or (and (symbolp (cadr l))
                       (cadr l))
                  (and (eq (caadr l) *var*)
                       (integerp (cadadr l))
                       (null (cddadr l)))))
       (let ((arg2 (desugar (caddr l))))
         (if arg2
           (list (car l) (cadr l) arg2)))))
    (t (labels
         ((check-term (l &optional (f nil))
            (if (or
                  (atom l)
                  (and
                    (or
                      (and (symbolp (car l))
                           (car l))
                      (and (eq (caar l) *fun*)
                           (integerp (cadar l))
                           (null (cddar l))))
                    (not
                      (and f
                           (or (eq (car l) *var*)
                               (eq (car l) *fun*))
                           (integerp (cadr l))
                           (null (cddr l))))
                    (null
                      (dolist (l (cdr l))
                        (if (null (check-term l))
                          (return t))))))
              l)))
         (check-term l t)))))
;;}}}
;;{{{ Neg-in
(defun deneg (l &optional (neg nil))
  (if neg
    (cond
      ((atom l)
       (cond
         ((eq l *true*) *false*)
         ((eq l *false*) *true*)
         (t (list *neg* l))))
      ((eq (car l) *wedge*)
       (list *vee*
         (deneg (cadr l) t)
         (deneg (caddr l) t)))
      ((eq (car l) *vee*)
       (list *wedge*
         (deneg (cadr l) t)
         (deneg (caddr l) t)))
      ((eq (car l) *neg*)
       (deneg (cadr l)))
      ((eq (car l) *forall*)
       (list *exists* (cadr l)
         (deneg (caddr l) t)))
      ((eq (car l) *exists*)
       (list *forall* (cadr l)
         (deneg (caddr l) t)))
      (t (list *neg* l)))
    (cond
      ((atom l) l)
      ((or (eq (car l) *wedge*)
           (eq (car l) *vee*))
       (list (car l)
         (deneg (cadr l))
         (deneg (caddr l))))
      ((eq (car l) *neg*)
       (deneg (cadr l) t))
      ((or (eq (car l) *forall*)
           (eq (car l) *exists*))
       (list (car l) (cadr l)
         (deneg (caddr l))))
      (t l))))
;;}}}
;;{{{ To-PNF and Skolemization
(defun dequant (l)
  (let ((var-index nil) (fun-index nil) (skfun-ptr nil)
        (sym-stack nil) (sym-global nil) (ex-stack nil) (s) (skl))
    (labels
      ((subst-term (l)
         (cond
           ((and (symbolp l) l)
            (cond
              ((setf s (assoc l sym-stack))
               (if (cddr s)
                 (progn
                   (push
                     (cons (list *fun* (cadr s))
                       (copy-list
                         (cdr (assoc (cadr s) ex-stack))))
                     skfun-ptr)
                   (car skfun-ptr))
                 (cadr s)))
              ((setf s (assoc l sym-global))
               (cdr s))
              (t
               (push (cons l (gensym)) sym-global)
               (cdar sym-global))))
           ((atom l) l)
           ((and (eq (car l) *var*)
                 (integerp (cadr l))
                 (null (cddr l)))
            (let ((r (assoc (cadr l) var-index)))
              (when (null r)
                (setf r (cons (cadr l) (gensym)))
                (push r var-index))
              (subst-term (cdr r))))
           (t
            (if (consp (car l))
              (push (cadar l) fun-index))
            (cons (car l)
                  (mapcar #'subst-term (cdr l))))))
       (dequantr (l)
         (cond
           ((atom l) l)
           ((or (eq (car l) *wedge*)
                (eq (car l) *vee*)
                (eq (car l) *neg*))
            (cons (car l)
                  (mapcar #'dequantr (cdr l))))
           ((or (setf s (eq (car l) *exists*))
                (eq (car l) *forall*))
            (if (consp (cadr l))
              (let ((r (assoc (cadadr l) var-index)))
                (when (null r)
                  (setf r (cons (cadadr l) (gensym)))
                  (push r var-index))
                (push (list* (cdr r) (gensym) s) sym-stack))
              (push (list* (cadr l) (gensym) s) sym-stack))
            (if s
              (push (cons (cadar sym-stack)
                      (nreverse
                        (mapcar #'cadr
                          (remove-if #'cddr
                            sym-stack))))
                    ex-stack))
            (prog1
              (dequantr (caddr l))
              (if s (pop ex-stack))
              (pop sym-stack)))
           (t (subst-term l)))))
      (setf skl (dequantr l)))
    (setf sym-global (nreverse (mapcar #'cdr sym-global)))
    (setf ex-stack nil)
    (setf s 0)
    (dolist (item (nreverse skfun-ptr))
      (let ((ex (assoc (cadar item) ex-stack)))
        (when (null ex)
          (do nil ((not (find (incf s) fun-index)) nil))
          (setf ex (cons (cadar item) s))
          (push ex ex-stack))
        (setf (cadar item) (cdr ex)))
      (setf (cdr item) (append sym-global (cdr item))))
    skl))
;;}}}
;;{{{ To-CNF
(defun devee (l)
  (labels
    ((deveer (l)
       (cond
         ((eq l *true*) (list *wedge*))
         ((eq l *false*) (list *vee*))
         ((atom l) (list *vee* l))
         ((eq (car l) *wedge*)
          (cons *wedge*
                (mapcan
                  #'(lambda (l)
                      (if (eq (car l) *wedge*)
                        (cdr l) (list l)))
                  (mapcar #'deveer (cdr l)))))
         ((eq (car l) *vee*)
          (case (length l)
            (1 (list *vee*))
            (2 (deveer (cadr l)))
            (otherwise
              (let ((arg1 (deveer (cadr l)))
                    (arg2 (deveer (cons *vee* (cddr l)))))
                (if (and (eq (car arg1) *vee*)
                         (eq (car arg2) *vee*))
                  (append arg1 (cdr arg2))
                  (progn
                    (setf arg1
                      (if (eq (car arg1) *wedge*)
                        (cdr arg1) (list arg1)))
                    (setf arg2
                      (if (eq (car arg2) *wedge*)
                        (cdr arg2) (list arg2)))
                    (cons *wedge*
                      (mapcan
                        #'(lambda (x)
                            (mapcar
                              #'(lambda (y)
                                  (deveer
                                    (list *vee* x y)))
                              arg2))
                        arg1))))))))
         (t (list *vee* l)))))
    (deveer (list *wedge* l *true*))))
;;}}}
;;{{{ Rename to Clauses
(defun dename (l)
  (let ((sym-table nil) (s 0))
    (labels
      ((denamer (l &optional (f nil))
         (cond
           ((and (symbolp l) l)
            (if f l
              (let ((ind (assoc l sym-table)))
                (unless ind
                  (setf ind (cons l (incf s)))
                  (push ind sym-table))
                (list *var* (cdr ind)))))
           ((atom l) l)
           ((and f (eq (car l) *neg*))
            (list *neg* (denamer (cadr l) t)))
           (t
            (cons (car l)
                  (mapcar #'denamer (cdr l)))))))
      (cons *wedge*
        (mapcar
          #'(lambda (l)
              (setf sym-table nil)
              (cons *vee*
                (mapcar
                  #'(lambda (l)
                      (denamer l t))
                  (cdr l))))
          (cdr l))))))
;;}}}

;;{{{ Output
(defun Clausal-Form (l)
  (let ((res (desugar l)))
    (if res
      (let ((res
              (dename
                (devee
                  (dequant
                    (deneg res))))))
        (format t "Clausal Form:~%")
        (format t "{~%")
        (dolist (item (cdr res))
          (format t "  [~%")
          (dolist (item (cdr item))
            (format t "    ~a~%" item))
          (format t "  ]~%"))
        (format t "}~%"))
      (format t "Check input please.~%"))))
;;}}}

(let ((form '(
        ;($e z ($a x ($e y ($v ($=> ($v (P x) (Q x)) (R y)) (U z)))))
        ;($a x ($=> ($a y (P x y)) ($~ ($a y ($=> (Q x y) (R x y))))))
        ;($^ ($<=> a ($v b e)) ($=> e d) ($=> ($^ c f) ($~ b)) ($=> e b) ($=> b f) ($=> b c))
        ($~ ($=> ($a |x|
                     ($=> (|Horse| |x|)
                          (|Animal| |x|)))
                 ($a |x|
                     ($=> ($e |y|
                              ($^ (|Horse| |y|)
                                  (|HeadOf| |x| |y|)))
                          ($e |y|
                              ($^ (|Animal| |y|)
                                  (|HeadOf| |x| |y|)))))))
      )) (detail t)
      (funarray (vector #'identity #'desugar #'deneg #'dequant #'devee #'dename)))
  (format t "--------------------------------~%")
  (dolist (form form)
    (if detail
      (let ((form form))
        (dotimes (i (length funarray))
          (format t "Step ~d:~%  ~a~%~%" i
            (setf form (funcall (aref funarray i) form))))))
    (Clausal-Form form)
    (format t "--------------------------------~%")))
