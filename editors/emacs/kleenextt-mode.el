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

(defcustom kleenextt-time-budget 5
  "Seconds a command may take when checked automatically.
Past it, the command is stopped and checked at its type only, until
`kleenextt-check-to-point' runs it in full.  0 for no budget."
  :type 'number
  :group 'kleenextt)

(defun kleenextt--init-options ()
  "The server's initialization options."
  (list :timeBudget kleenextt-time-budget))

(declare-function lsp-request "lsp-mode")
(declare-function lsp--text-document-identifier "lsp-mode")
(declare-function lsp--cur-position "lsp-mode")
(declare-function eglot--current-server-or-lose "eglot")
(declare-function eglot--TextDocumentIdentifier "eglot")
(declare-function eglot--pos-to-lsp-position "eglot")
(declare-function jsonrpc-request "jsonrpc")

(defun kleenextt--check-request (position)
  "Ask the server to check in full up to POSITION, or the whole file if nil."
  (cond
   ((bound-and-true-p lsp-mode)
    (lsp-request "$/kleenextt/check"
                 (append (list :textDocument (lsp--text-document-identifier))
                         (and position (list :position (lsp--cur-position))))))
   ((bound-and-true-p eglot--managed-mode)
    (jsonrpc-request (eglot--current-server-or-lose) :$/kleenextt/check
                     (append (list :textDocument (eglot--TextDocumentIdentifier))
                             (and position (list :position (eglot--pos-to-lsp-position))))))
   (t (user-error "No language server for this buffer"))))

(defun kleenextt-check-to-point ()
  "Check the file in full up to point, past the time budget."
  (interactive)
  (kleenextt--check-request (point)))

(defun kleenextt-check-buffer ()
  "Check the whole file in full, past the time budget."
  (interactive)
  (kleenextt--check-request nil))

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
    (define-key map (kbd "C-c C-<return>") #'kleenextt-check-to-point)
    (define-key map (kbd "C-c C-b") #'kleenextt-check-buffer)
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
      :initialization-options #'kleenextt--init-options
      :notification-handlers handlers))))

(with-eval-after-load 'eglot
  (add-to-list 'eglot-server-programs
               `(kleenextt-mode . ,(lambda (_interactive)
                                     (list (kleenextt-executable) "--server"
                                           :initializationOptions (kleenextt--init-options))))))

(provide 'kleenextt-mode)
;;; kleenextt-mode.el ends here
