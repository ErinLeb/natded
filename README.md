
NatDed : a Coq encoding of Natural Deduction
============================================

## Author

Pierre Letouzey (IRIF), 2019

## Description

This Coq development is an attempt to formalize as directly as possible a typical logic course about 1st-order predicate calculus using the Natural Deduction style. We followed here a [logic course](http://www.irif.fr/~letouzey/preuves/cours.pdf) (in French) due to Alexandre Miquel. Showing parts of this Coq development to Master students (at least the definitions and proof statements and proof sketchs) is now an teaching alternative instead of using the original course pdf, or in complement of it.

I have formalized Natural Deduction and some of its meta-theory (such as a subsitution lemma), including classical models (seen as Coq types + functions + propositions), and the completeness theorem (following the Henkin approach).

Trying to be faithful to the original document, we use first encode formulas using names (i.e. strings) in quantifiers. As expected, this triggers difficulties (name capture) during substitutions, and leads to the use of alpha-equivalence. Then I switch to another encoding (locally nameless) which is immune to these issues, while avoiding most of the technicalities of the approach of De Bruijn indices. I provide a two-way conversion between these named and locally-nameless encodings, and prove it correct. The rest of the meta-theorical study is performed on the locally-nameless representation.

## Summary

Main files :

 - [Defs](Defs.v) : common basic structures (names, variables, signatures, ...)
 - [Nam](Nam.v) : encoding of Natural Deduction (terms, formulas, derivations ...) using names as binders
 - [Mix](Mix.v) : same, but using a Locally Nameless representation of binders
 - [Alpha](Alpha.v), [Alpha2](Alpha2.v) : equivalence between various definitions of substitutions and alpha-equivalences for [Nam](Nam.v)
 - [Equiv](Equiv.v), [Equiv2](Equiv2.v) : conversions between the [Nam](Nam.v) and [Mix](Mix.v) encodings
 - [Meta](Meta.v) : some meta-theoretical results about [Mix](Mix.v) (e.g. substitution lemma)
 - [Theories](Theories.v) : notion of 1st-order theory, consistency, extensions, Henkin theorem, completion, ...
 - [PreModels](PreModels.v) : interpretation of formulas as Coq propositions, validity theorem
 - [Models](Models.v) : notion of model, build of a syntactic model for a consistent theory, completeness theorem
 
Auxiliary files :

 - [AsciiOrder](AsciiOrder.v) [StringOrder](StringOrder.v) [StringUtils](StringUtils.v) : ordering of chars and strings, plus a few things about strings
 - [Utils](Utils.v) : a generic notion of boolean equalities, some utility functions and proofs about lists, ...
 - [NameProofs](NameProofs.v) : proofs about name set (i.e. sets of strings)
 - [Countable](Countable.v) : explicit enumeration of countable types (such as strings or terms or formulas)

## Usage

To be used with Coq 8.8. Just run `make` to compile.

## License

This work is free software, released under the Creative Commons Zero License (CC0). See files [LICENSE](LICENSE) and [COPYING](COPYING) for more.
