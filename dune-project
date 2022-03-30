(lang dune 3.0)

(name m_tree)

(generate_opam_files true)

(source
 (github jfeser/mtree))

(authors "Jack Feser")

(maintainers "Maintainer Name")

(license MIT)

(documentation https://jfeser.github.io/mtree/index.html)

(package
 (name m_tree)
 (synopsis "An implementation of M-trees")
 (description "M-trees are an index for metric data that support efficient insertion and range queries.")
 (depends
   ocaml
   dune
  (iter (>= 1.4))
  (core (and :with-test (>= v0.14)))
  (core_bench (and :with-test (>= v0.14)))
  (ppx_expect (and :with-test (>= v0.14)))
  (ppx_sexp_message (and :with-test (>= v0.14)))
  (ppx_sexp_conv (and :with-test (>= v0.14)))
  (ppx_compare (and :with-test (>= v0.14)))
  (ppx_assert (and :with-test (>= v0.14)))))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
