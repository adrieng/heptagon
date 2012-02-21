;;; hept-mode.el --- major mode for Heptagon files

;; Copyright (C) 1999, 2000, 2001 Free Software Foundation, Inc.
;;
;; Author: adrien.guatto@ens.fr
;; Keywords: languages
;; Version: 1.0
;; X-URL: http://heptagon.gforge.inria.fr

;; This file is not part of GNU Emacs.

;;; Commentary:

;; Major mode for editing Heptagon files, usually files ending
;; with `.ept' and `.epi'.

;; This package provides the following features:
;;  * Syntax coloring (via font-lock) for grammar symbols and
;;    builtin functions and variables
;;  * Indentation for the current line (TAB) and selected region (C-M-\).
;;  * Switching between file.vert and file.frag
;;    with S-lefttab (via ff-find-other-file)

;;; Installation:

;; If hept-mode is not part of your distribution, put this file into your
;; load-path and the following into your ~/.emacs:
;;   (autoload 'hept-mode "hept-mode" nil t)
;;   (add-to-list 'auto-mode-alist '("\\.ept\\'" . hept-mode))
;;   (add-to-list 'auto-mode-alist '("\\.epi\\'" . hept-mode))

;; To customize, use `M-x customize-group RET antlr RET' or the custom browser
;; (Emacs->Programming->Languages->Antlr).

;;; Code:

(provide 'hept-mode)

(eval-when-compile
  (require 'find-file))

(defconst hept-version "1.0"
  "Heptagon major mode version number.")

(defvar hept-mode-hook nil)

(defvar hept-mode-map
  (let ((hept-mode-map (make-sparse-keymap)))
    (define-key hept-mode-map [S-iso-lefttab] 'ff-find-other-file)
    hept-mode-map)
  "Keymap for Heptagon major mode")

(add-to-list 'auto-mode-alist '("\\.ept\\'" . hept-mode))
(add-to-list 'auto-mode-alist '("\\.ept\\'" . hept-mode))

;; (regexp-opt '(
;;             "fun" "node" "returns" "open" "inlined" "let" "tel" "var" "const"
;;               )
;;             t)

;; (regexp-opt '(
;;               "bool" "int" "float"
;;               )
;;             t)

;; (regexp-opt '(
;;               "with" "merge" "when" "whenot"
;;               "fby" "pre" "on" "onot" "not" "end" "automaton" "state"
;;               "switch" "every" "reset" "until" "unless"
;;               "last" "if" "then" "else" "default" "do" "done" "in" "continue"
;;               "contract" "assume" "enforce" "with"
;;               "map" "fold" "mapfold" "mapi" "foldi" "mapfoldi"
;;               )
;;             t)

(defconst hept-font-lock-keywords-1
  (list
   '(
     "\\<\\(const\\|fun\\|inlined\\|let\\|node\\|open\\|returns\\|tel\\|var\\)\\>"
     .
     font-lock-variable-name-face)
   '("\\<\\(bool\\|\\(?:floa\\|in\\)t\\)\\>"
     .
     font-lock-builtin-face)
   '(
     "\\<\\(a\\(?:ssume\\|utomaton\\)\\|cont\\(?:inue\\|ract\\)\\|d\\(?:efault\\|o\\(?:ne\\)?\\)\\|e\\(?:lse\\|n\\(?:d\\|force\\)\\|very\\)\\|f\\(?:by\\|oldi?\\)\\|i[fn]\\|last\\|m\\(?:ap\\(?:foldi?\\|i\\)?\\|erge\\)\\|on\\(?:ot\\)?\\|pre\\|reset\\|s\\(?:tate\\|witch\\)\\|not\\|then\\|un\\(?:less\\|til\\)\\|w\\(?:hen\\(?:ot\\)?\\|ith\\)\\)\\>"
     .
     font-lock-keyword-face)
   )
  "Minimal highlighting expressions for Heptagon mode")

(defvar hept-font-lock-keywords hept-font-lock-keywords-1
  "Default highlighting expressions for Heptagon mode")

(defvar hept-mode-syntax-table
  (let ((hept-mode-syntax-table (make-syntax-table)))
    (modify-syntax-entry ?( "()1n" hept-mode-syntax-table)
    (modify-syntax-entry ?) ")(4n" hept-mode-syntax-table)
    (modify-syntax-entry ?* ". 23" hept-mode-syntax-table)
    (modify-syntax-entry ?< "(>" hept-mode-syntax-table)
    (modify-syntax-entry ?> ")<" hept-mode-syntax-table)
    (modify-syntax-entry ?\ "\\" hept-mode-syntax-table)
    (modify-syntax-entry ?_ "_" hept-mode-syntax-table)
    (modify-syntax-entry ?: "." hept-mode-syntax-table)
;    (modify-syntax-entry ?\n "> b" hept-mode-syntax-table)
    hept-mode-syntax-table)
  "Syntax table for hept-mode")

(defun hept-indent-line ()
  "Indent current line as Heptagon code"
  (interactive)
  (if (bobp)
      (indent-line-to 0)
    (let ((not-indented t) cur-indent)
      (save-excursion
        (while not-indented
          (forward-line -1)
          (if (looking-at "^[ \t]*\\(tel\\|end\\|done\\|every\\)")
              (progn
                (setq cur-indent (current-indentation))
                (setq not-indented nil))
                                        ; Check for rule 4
            (if (looking-at
                 "^[ \t]*\\(let\\|automaton\\)")
                (progn
                  (setq cur-indent (+ (current-indentation) default-tab-width))
                  (setq not-indented nil))
              (if (looking-at "^[ \t]*\\(do\\|reset\\)")
                  (progn
                    (setq cur-indent (+ (current-indentation) 3))
                    (setq not-indented nil))
                (if (bobp) ; Check for rule 5
                    (setq not-indented nil)))))))
      (if cur-indent
          (indent-line-to cur-indent)
        (indent-line-to 0)))))

(defvar hept-other-file-alist
  '(("\\.ept$" (".epi"))
    ("\\.epi$" (".ept")))
  "Alist of extensions to find given the current file's extension")

(define-derived-mode hept-mode fundamental-mode "Heptagon"
  "Major mode for editing Heptagon files."
  :syntax-table hept-mode-syntax-table
  (set (make-local-variable 'comment-start) "(*")
  (set (make-local-variable 'comment-end) "*)")
  (set (make-local-variable 'indent-line-function) 'hept-indent-line)
  (set (make-local-variable 'font-lock-defaults) '(hept-font-lock-keywords))
  (set (make-local-variable 'ff-other-file-alist) 'hept-other-file-alist)
  )

;;; hept-mode.el ends here