;;; Project Emacs settings for Coq mode

;;; ==================================================================
;;; Common settings
;;; ==================================================================

(load (expand-file-name "common.el" project:emacs-directory)
      t nil t)

;;; ==================================================================
;;; Coq compilation settings
;;; ==================================================================

(defvar-local coq:physical-root
  (expand-file-name "_build/default/src" project:root)
  "The root of the physical paths of the Coq modules of the project.")

(defvar-local coq:logical-root "ufcoq"
  "The root of the logical names of the Coq modules of the project.")

;; Do not use a Coq project file to get options for `coqtop'.  They
;; are supplied below.
(setq-local coq-use-project-file nil)

;; Options for `coqtop' as mentioned above.
(setq-local coq-prog-args `("-emacs"
                            "-noinit"
                            "-indices-matter"
                            "-set" "Universe Polymorphism"
                            "-set" "Polymorphic Inductive Cumulativity"
                            "-unset" "Universe Minimization ToSet"
                            "-set" "Primitive Projections"))

;;; ==================================================================
;;; Makefile settings
;;; ==================================================================

(defun coq:make (&optional target)
  "Build the Coq part of the project."
  (save-some-buffers t)
  (let* ((default-directory project:root)
         (path (format "%s:%s"
                       (expand-file-name "bin" project:nix-build-link)
                       (getenv "PATH")))
         (compilation-environment (cons (format "PATH=%s" path)
                                        compilation-environment))
         (argument (if target (format " %s" target) ""))
         (compile-command (format "make%s" argument)))
    (recompile)))

(defun coq:make-default ()
  (interactive)
  (coq:make))

(defun coq:make-clean ()
  (interactive)
  (coq:make "clean"))

;;; ==================================================================
;;; The tags table for Coq files
;;; ==================================================================

(defvar-local coq:tags-table
  (expand-file-name "TAGS" project:emacs-directory)
  "The tags table for the project.")

(defun coq:make-tags ()
  "Rebuild the project tags table and visit it."
  (interactive)
  (let ((default-directory project:emacs-directory))
    (let ((status (shell-command "make VERBOSE=1 tags")))
      (when (zerop status)
        (let ((tags-buffer (get-file-buffer coq:tags-table)))
          (when tags-buffer
            (with-current-buffer tags-buffer
              (revert-buffer t t))))
        (visit-tags-table coq:tags-table t)))))

(coq:make-tags)

;;; ==================================================================
;;; Indentation
;;; ==================================================================

;; The standard indentation provided by Coq mode does not suit me, so
;; I am using a trivial indentation function which is a small
;; modification of `tab-to-tab-stop'.

(defvar-local coq:original-indent-line-function indent-line-function
  "The standard indentation function of Coq mode.")

(defvar-local coq:indent 2
  "The basic amount of indentation in Coq mode.")

(defun coq:indent-line ()
  "Indent to `coq:indent' columns from the current column.
Modification of `tab-to-tab-stop'."
  (interactive)
  (and abbrev-mode (= (char-syntax (preceding-char)) ?w)
       (expand-abbrev))
  (let ((nexttab (+ coq:indent (current-column))))
    (delete-horizontal-space t)
    (indent-to nexttab)))

;; Use the above function for indentation in Coq mode.
(setq-local indent-line-function #'coq:indent-line)

;; Do not indent after expanding a snippet.
(when (featurep 'yasnippet)
  (setq-local yas-indent-line nil))

;; Do not reindent lines automatically.
(electric-indent-local-mode 0)

(defun coq:original-indent ()
  "Indent current line according to standard Coq mode indentation."
  (interactive)
  (let ((indent-line-function coq:original-indent-line-function))
    (indent-for-tab-command)))

;;; ==================================================================
;;; Key bindings
;;; ==================================================================

(when (boundp 'coq-mode-map)
  (define-key coq-mode-map (kbd "<backtab>") #'coq:original-indent)
  (define-key coq-mode-map (kbd "<kp-left>") #'coq:make-default)
  (define-key coq-mode-map (kbd "<kp-right>") #'coq:make-clean)
  (define-key coq-mode-map (kbd "<kp-up>") #'coq:make-tags))

;;; ==================================================================
;;; Disable automatic formatting
;;; ==================================================================

;; Disable the filling of paragraphs.  It creates havoc when an open
;; comment is filled; it then fills all the code in the following
;; lines, destroying my manual formatting.
(setq-local fill-paragraph-function #'(lambda (arg) t))

;;; ==================================================================
;;; Windows
;;; ==================================================================

;; Do not use the usual layout with windows for source, goal, and
;; response.  I rarely use the goals buffer.
(proof-three-window-toggle 0)

;; Do not raise buffers to display output.
(proof-auto-raise-toggle 0)

;;; End of file
