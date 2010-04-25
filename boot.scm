(current-load-relative-directory (current-directory))

(require "ar.scm")
(require "ac.scm")
(require "brackets.scm")
(use-bracket-readtable)

(acompile "arc.arc")
(acompile "ac.arc")
