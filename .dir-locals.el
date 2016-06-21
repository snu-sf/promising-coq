;; Specify coq-load path relative to project root
((coq-mode . ((eval . (flet
                          ((pre (s) (concat (locate-dominating-file buffer-file-name ".dir-locals.el") s)))
                        (setq coq-load-path
                              `((rec ,(pre "lib/sflib") "sflib")
                                (rec ,(pre "lib/paco/src") "Paco")
                                (rec ,(pre "src/axiomatic") "cmem")
                                (rec ,(pre "src/lib") "cmem")
                                (rec ,(pre "src/opt") "cmem")
                                (rec ,(pre "src/lang") "cmem")
                                (rec ,(pre "src/drf") "cmem")
                                (rec ,(pre "src/hahn") "cmem")
                                (rec ,(pre "src/while") "cmem")
                               ))))
              (coq-prog-args . ("-emacs-U")))))
