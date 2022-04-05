(lang dune 2.7)

(generate_opam_files true)

(name skonverto)
(source (github Deducteam/SKonverto))
(authors "Deducteam")
(maintainers "dedukti-dev@inria.fr")
(license CECILL-2.1)

(package
 (name skonverto)
 (synopsis "Proof deskolemizer")
 (description
"This package provides a tool generating a Dedukti proof of a TFF formula from a Dedukti proof of its skolemized version.")
 (depends
   (lambdapi (>= 2.1.0))))
