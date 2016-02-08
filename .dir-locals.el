;; Specify coq-load path relative to project root
((coq-mode . ((eval . (flet
                          ((pre (s) (concat (locate-dominating-file buffer-file-name ".dir-locals.el") s)))
                        (setq coq-load-path
                              `((rec ,(pre "lib/sflib") "sflib")
                                (rec ,(pre "src") "cmem")))))
              (coq-prog-args . ("-emacs-U")))))
