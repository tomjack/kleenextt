;;; kleenextt-mode.el --- Major mode for kleenextt .ktt files  -*- lexical-binding: t; -*-

;; Package-Requires: ((emacs "28.1"))

;;; Commentary:

;; Highlighting, the Lean Unicode input method, `kleenextt check' under
;; `compile', and `kleenextt --server' as a language server through lsp-mode
;; or eglot.  Needs lean4-mode (leanprover-community/lean4-mode) on the
;; `load-path' for its syntax table, input method and progress fringe:
;;
;;   (add-to-list 'load-path "~/Documents/lean4-mode")
;;   (add-to-list 'load-path "~/Documents/kleenextt/editors/emacs")
;;   (require 'kleenextt-mode)

;;; Code:

(require 'rx)
(require 'compile)
(require 'lean4-syntax)
(require 'lean4-input)

(defgroup kleenextt nil
  "Kleene cubical type theory."
  :group 'languages)

(defcustom kleenextt-executable "kleenextt"
  "The kleenextt executable, when the project has not built one in .lake/build/bin."
  :type 'string
  :group 'kleenextt)

(defun kleenextt-executable ()
  "The enclosing project's built kleenextt, else `kleenextt-executable'."
  (let* ((root (locate-dominating-file default-directory "lakefile.toml"))
         (built (and root (expand-file-name ".lake/build/bin/kleenextt" root))))
    (if (and built (file-executable-p built))
        built
      kleenextt-executable)))

(defun kleenextt-start-lsp ()
  "Start lsp-mode or eglot, whichever is installed, given the executable."
  (when (executable-find (kleenextt-executable))
    (cond ((fboundp 'lsp) (lsp))
          ((fboundp 'eglot-ensure) (eglot-ensure)))))

(defcustom kleenextt-mode-hook (list #'kleenextt-start-lsp)
  "Hook run after entering `kleenextt-mode'."
  :type 'hook
  :group 'kleenextt)

(defconst kleenextt-keywords
  '("import" "def" "data" "case" "hlevel" "let"))

(defconst kleenextt-commands
  '("#nf" "#time" "#trace" "#term" "#type" "#head" "#overlaps" "#stable"
    "#conv" "#differ" "#fail"))

(defconst kleenextt-primitives
  '("Type" "I" "Path" "PathP" "isContr" "fiber" "isEquiv" "Equiv"
    "fst" "snd" "Glue" "glue" "unglue" "glueU" "transp" "hcomp" "ghcomp"
    "comp" "hfill" "coe" "hcom"))

(defconst kleenextt-symbols
  '("λ" "↦" "→" "->" "=>" ":=" "×" "∧" "∨" "¬"))

(defconst kleenextt-font-lock-keywords
  `((,(rx-to-string `(seq bow (or "def" "data") eow (+ space) (group (+ (not (any space ?\n ?: ?=))))))
     1 font-lock-function-name-face)
    (,(rx-to-string `(seq bow (or ,@kleenextt-keywords) eow)) . font-lock-keyword-face)
    (,(rx-to-string `(seq (or ,@kleenextt-commands) eow)) . font-lock-preprocessor-face)
    (,(rx bow "sorry" eow) . font-lock-warning-face)
    (,(rx-to-string `(seq bow (or ,@kleenextt-primitives) eow)) . font-lock-builtin-face)
    (,(regexp-opt kleenextt-symbols) . font-lock-constant-face)))

(defvar kleenextt-mode-syntax-table (make-syntax-table lean4-syntax-table)
  "Lean's syntax table: `--' and `/- -/' comments, Unicode letters in words.")

(defvar kleenextt-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-l") #'kleenextt-check)
    map))

(defun kleenextt-check-command ()
  "The `kleenextt check' command for this buffer's file."
  (format "%s check %s"
          (shell-quote-argument (kleenextt-executable))
          (shell-quote-argument (file-relative-name buffer-file-name))))

(defun kleenextt-check ()
  "Check this file with `kleenextt check' in a compilation buffer.
Its `FILE:LINE:COL: error:' lines are what `next-error' expects."
  (interactive)
  (compile (kleenextt-check-command)))

;;;###autoload
(define-derived-mode kleenextt-mode prog-mode "Kleenextt"
  "Major mode for kleenextt files.

\\{kleenextt-mode-map}"
  :group 'kleenextt
  (setq-local comment-start "--")
  (setq-local comment-start-skip "[-/]-[ \t]*")
  (setq-local comment-end "")
  (setq-local comment-end-skip "[ \t]*\\(-/\\|\\s>\\)")
  (setq-local comment-padding 1)
  (setq-local comment-use-syntax t)
  (setq-local font-lock-defaults '(kleenextt-font-lock-keywords))
  (setq-local indent-tabs-mode nil)
  (setq-local electric-indent-inhibit t)
  (when buffer-file-name
    (setq-local compile-command (kleenextt-check-command)))
  (set-input-method "Lean"))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.ktt\\'" . kleenextt-mode))

;;;###autoload
(modify-coding-system-alist 'file "\\.ktt\\'" 'utf-8)

(defvar lsp-language-id-configuration)
(defvar eglot-server-programs)
(declare-function lsp-register-client "lsp-mode")
(declare-function make-lsp-client "lsp-mode")
(declare-function lsp-stdio-connection "lsp-mode")
(declare-function lean4-fringe-update "lean4-fringe")

(with-eval-after-load 'lsp-mode
  (require 'lean4-fringe)
  (add-to-list 'lsp-language-id-configuration '(kleenextt-mode . "kleenextt"))
  (let ((handlers (make-hash-table :test 'equal)))
    (puthash "$/lean/fileProgress" #'lean4-fringe-update handlers)
    (lsp-register-client
     (make-lsp-client
      :new-connection (lsp-stdio-connection
                       (lambda () (list (kleenextt-executable) "--server")))
      :major-modes '(kleenextt-mode)
      :server-id 'kleenextt
      :notification-handlers handlers))))

(with-eval-after-load 'eglot
  (add-to-list 'eglot-server-programs
               `(kleenextt-mode . ,(lambda (_interactive)
                                     (list (kleenextt-executable) "--server")))))

(provide 'kleenextt-mode)
;;; kleenextt-mode.el ends here
