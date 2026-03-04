(lang dune 3.21)
(name rocq-promising)
(using coq 0.8)

(source (github snu-sf/promising-coq))
(license "MIT")
(authors
  "Jeehoon Kang" "Chung-Kil Hur" "Ori Lahav"
  "Viktor Vafeiadis" "Derek Dreyer")
(maintainers "yeji.han@sf.snu.ac.kr")

(package
 (name rocq-promising)
 (synopsis "Rocq formalization of the Promising Semantics")
 (depends
  (coq-core (>= 9.0))
  rocq-stdlib
  (coq-sflib (>= 2.1.0))
  (coq-paco (>= 4.2.3))
  (coq-promising-lib (>= 2.1.0))
  (dune (>= 3.21)))
 (maintainers "yeji.han@sf.snu.ac.kr"))
