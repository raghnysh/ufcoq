;;; Project Emacs settings common to all major modes

;;; ==================================================================
;;; Nix settings
;;; ==================================================================

(defvar-local project:nix-build-link
  (expand-file-name ".nix" project:root)
  "The absolute path of the symbolic link created by `nix-build'.")

;;; ==================================================================
;;; Settings for the yasnippet Emacs package
;;; ==================================================================

(when (require 'yasnippet nil t)
  (yas-minor-mode-on)
  (setq-local yas-snippet-dirs
              (list (expand-file-name "yasnippet"
                                      project:emacs-directory)))
  (yas-reload-all))

;;; End of file
