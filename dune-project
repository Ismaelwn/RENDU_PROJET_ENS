(lang dune 3.0)

(using menhir 2.1)

(name minirust)

(generate_opam_files true)

(authors "Jacques-Henri JOURDAN")

(maintainers "Jacques-Henri JOURDAN")

(license MIT)

(package
 (name minirust)
 (allow_empty)
 (synopsis "Borrow checker")
 (description "")
 (depends
  (ocaml
   (>= 5.1.1))
  ocamlformat
  dune
  menhir
  fix))
