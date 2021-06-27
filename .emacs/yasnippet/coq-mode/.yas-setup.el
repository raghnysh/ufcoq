;;; Functions used in yasnippet templates for Coq mode

;;; ==================================================================
;;; Generate random alphanumeric labels
;;; ==================================================================

(require 'calc-bin)

(defun coq:base-36 (number)
  "Return the base 36 representation of NUMBER."
  (let ((calc-number-radix 36))
    (downcase (math-format-radix number))))

(defun coq:label (maxlength &optional padded padright)
  "Return a lower-case alphanumeric label of length at most MAXLENGTH.
If PADDED is non-nil, the label is padded with `0' characters so
that its length equals MAXLENGTH.  If PADRIGHT is also non-nil,
the padding is inserted on the right rather than the left."
  (let* ((limit (expt 36 maxlength))
         (template (concat "%"
                           (if padded
                               (concat (if padright "-" "") "0")
                             "")
                           (int-to-string maxlength)
                           "a"))
         (number (random limit))
         (spec-alist (list (cons ?a (coq:base-36 number)))))
    (format-spec template spec-alist)))

;;; End of file
