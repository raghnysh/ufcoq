;;; Select fragments that match a given pattern

;; This file contains code that uses the Emacs Helm package to select
;; one or more fragments from files, insert the name part of every
;; selected fragment into the current file, and display the content of
;; every selected fragment into a separate Help buffer.
;;
;; Data about the fragments is stored in a delimiter-separated values
;; (DSV) file, one fragment per line.  Each line has five fields that
;; are delimited by the control character "":
;;
;;   field 0: the label of the fragment
;;   field 1: the name of the fragment
;;   field 2: file (lines begin-end)
;;   field 3: lhs or content of the fragment
;;   field 4: arguments declarations in the fragment
;;
;; The main component of the code is a Helm file source.  The
;; candidates of the source are read from the above DSV file, one
;; candidate per line.  The filtered candidate transformer splits each
;; candidate into its constituent fields, and returns a list
;; constructed from those fields.  The first element of the list is
;; the display value shown for the candidate during selection, and
;; uses all the five fields of the candidate.  The second element of
;; the list is the name of the fragment corresponding to the
;; candidate.
;;
;; The final command defined in this file inserts the second element
;; of each chosen list into the current buffer, and shows the first
;; element of each chosen list (the above-mentioned display value) in
;; a separate Help buffer.

(require 'helm)

(defun helm-fragments:action (_candidate)
  "Function used as an action in the Helm source for fragments."
  (helm-marked-candidates))

(defvar helm-fragments:actions
  (helm-make-actions "Helm-Fragments action" #'helm-fragments:action)
  "The actions of the Helm source for fragments of project files.")

(defun helm-fragments:candidate-to-list (candidate)
  "Split each CANDIDATE into fields and return a consolidated list."
  (let* ((fields (split-string candidate ""))
         ;; 0: label
         ;; 1: name
         ;; 2: file (lines begin-end)
         ;; 3: lhs or content
         ;; 4: arguments
         (info (format "%s %s\n%s\n%s"
                       (nth 0 fields)
                       (nth 2 fields)
                       (string-replace "\\n" "\n" (nth 3 fields))
                       (string-replace "\\n" "\n" (nth 4 fields))))
         (name (nth 1 fields)))
    (list info name info)))

(defun helm-fragments:filtered-candidate-transformer (candidates _source)
  "Convert CANDIDATES into a more presentable string."
  (mapcar #'helm-fragments:candidate-to-list candidates))

(defvar helm-fragments:dsv-file
  (expand-file-name "misc/fragments/fragments.dsv" project:root)
  "The DSV file containing the data about fragments of project files.")

(defvar helm-fragments:source
  (helm-build-in-file-source "Helm fragments source" helm-fragments:dsv-file
    :filtered-candidate-transformer #'helm-fragments:filtered-candidate-transformer
    :multiline t
    :action helm-fragments:actions)
  "Helm source for fragments of project files.")

(defun helm-fragments:choose ()
  "Choose fragments using Helm."
  (helm :sources '(helm-fragments:source)
        :buffer "*Helm fragments buffer (1)*"))

(defun helm-fragments:run ()
  "Insert selected fragment names in current buffer.
Show more information about selected fragments in a Help buffer."
  (interactive)
  (let* ((chosen (helm-fragments:choose))
         (final (mapconcat #'car chosen "\n"))
         (help
          (mapconcat #'cadr
                     chosen
                     (concat "\n" helm-candidate-separator "\n"))))
    (insert final)
    (with-output-to-temp-buffer "*Helm fragments buffer (2)*"
      (princ help))))

(provide 'helm-fragments)

;;; End of file
