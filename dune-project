(lang dune 3.6)

(name tinyml)

(generate_opam_files true)

(source
 (github panyuewh/tinyml))

(authors "Yue Pan")

(maintainers "Yue Pan")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name tinyml)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml dune)
 (tags
  (topics "to describe" your project))
 (allow_empty))

(using menhir 2.1)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
