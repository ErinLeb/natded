
NatDed : a Coq encoding of Natural Deduction
============================================

## Authors

 - Pierre Letouzey (IRIF), 2019-2020
 - Samuel Ben Hamou (ENS Paris Saclay), internship June-July 2020

## Description

This Coq development is an attempt to formalize as directly as possible a typical logic course about 1st-order predicate calculus using the Natural Deduction style. We followed here a [logic course](http://www.irif.fr/~letouzey/preuves/cours.pdf) (in French) due to Alexandre Miquel. Showing parts of this Coq development to Master students (at least the definitions and proof statements and proof sketchs) is now an teaching alternative instead of using the original course pdf, or in complement of it.

Natural Deduction and some of its meta-theory have been formalized (such as a subsitution lemma), including classical models (seen as Coq types + functions + propositions), and the completeness theorem (following the Henkin approach).

Trying to be faithful to the original document, formulas are first encoded using names (i.e. strings) in quantifiers. As expected, this triggers difficulties (name capture) during substitutions, and leads to the use of alpha-equivalence. Then another encoding is proposed (locally nameless) which is immune to these issues, while avoiding most of the technicalities of the approach of De Bruijn indices. A two-way conversion between these named and locally-nameless encodings is provided and proved correct. The rest of the meta-theorical study is performed on the locally-nameless representation.

## Summary

Main files :

 - [Defs](Defs.v) : common basic structures (names, variables, signatures, ...)
 - [Nam](Nam.v) : encoding of Natural Deduction (terms, formulas, derivations ...) using names as binders
 - [Mix](Mix.v) : same, but using a Locally Nameless representation of binders
 - [Subst](Subst.v) : basic properties of renamings and substitutions for [Nam](Nam.v)
 - [Equiv](Equiv.v), [Equiv2](Equiv2.v) : conversions between the [Nam](Nam.v) and [Mix](Mix.v) encodings
 - [Toolbox](Toolbox.v) : basic properties of [Mix](Mix.v) utility functions like lift, bsubst, vmap, ...
 - [Meta](Meta.v) : some meta-theoretical results about [Mix](Mix.v), e.g. substitution lemma and some admissible rules
 - [ProofExamples](ProofExemples.v) : some usual 1st-order proofs via [Mix](Mix.v), both intuitionistic or classical
 - [Wellformed](Wellformed.v) : well-formed terms, formula, ... corrrectly use a signature and binders
 - [Restrict](Restrict.v) : restrict a proof or derivation to a signature and/or a binder level
 - [Theories](Theories.v) : notion of 1st-order theory, consistency, extensions, Henkin theorem, completion, ...
 - [PreModels](PreModels.v) : interpretation of formulas as Coq propositions, validity theorem
 - [Models](Models.v) : notion of model, build of a syntactic model for a consistent theory, completeness theorem
 - [Skolem](Skolem.v) : Skolem theorem stating that any skolem extension is conservative
 - [Peano](Peano.v) : example theory (Peano Arithmetic) and its Coq model
 - [ZF](ZF.v) : example theory (Zermelo-Fraenkel set theory) and its Coq model (based on Benjamin Werner [ZFC contribution](https://github.com/coq-contribs/zfc))
 - [Lambda](Lambda.v) : relate propositional proofs in [Mix](Mix.v) with a (extended) lambda-calculus, Curry-Howard theorem

Auxiliary files :

 - [AsciiOrder](AsciiOrder.v) [StringOrder](StringOrder.v) [StringUtils](StringUtils.v) : ordering of chars and strings, plus a few things about strings
 - [Utils](Utils.v) : a generic notion of boolean equalities, some utility functions and proofs about lists, ...
 - [NameProofs](NameProofs.v) : proofs about name set (i.e. sets of strings)
 - [Countable](Countable.v) : explicit enumeration of countable types (such as strings or terms or formulas)
 - [AltSubst](AltSubst.v) : an earlier substitution and alpha-equivalence for [Nam](Nam.v) via structural simultaneous definitions.
 - [Nary](Nary.v) : extension of Coq [NaryFunctions]

## Documentation

 - A [talk](https://www.irif.fr/\_media/rencontres/pps2019/letouzey.pdf) presenting the state of this development in September 2019 (Journéees PPS).
   The [markdown file](talk/expose.md) of these slides

 - Soon, the internship report of Samuel Ben Hamon (summer 2020). In the meanwhile, see [Rapport](Rapport).

## Usage

To be used with Coq >= 8.8. Just run `make` to compile.

## External dependencies

This work reuse a file from Benjamin Werner's ZFC contribution https://github.com/coq-contribs/zfc
See also the [corresponding article](http://www.lix.polytechnique.fr/Labo/Benjamin.Werner/publis/tacs97.pdf).
For now, we have chosen to embed here a copy of the only necessary file, see [contribs/zfc](contribs/zfc).

## License

This work is released under the Creative Commons Zero License (CC0), except the file [contribs/zfc/zfc.v](contribs/zfc/zfc.v).
See files [LICENSE](LICENSE) and [COPYING](COPYING) for more about the CC0 license.

The file [contribs/zfc/zfc.v](contribs/zfc/zfc.v) is an excerpt of Benjamin Werner's [ZFC contribution](https://github.com/coq-contribs/zfc) released under the [LGPL >= 2.1 License](https://github.com/coq-contribs/zfc/blob/master/LICENSE).
