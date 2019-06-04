(* Grammar for 1st-order formulas *)
(* To be used with a recent menhir (with Coq backend). *)
(* /!\ NOT FINISHED YET : lacks a lexer + resync with the rest of the project *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

%{

Require Import Defs.
Require Nam.
Import ListNotations.
Local Open Scope string_scope.

%}

%token TRUE FALSE AND OR IFF IMPL ALL EX NOT LPAREN RPAREN LCURL RCURL COMMA
%token EQ IN PLUS MULT EOF
%token<nat> INT
%token<string> ID

%right COMMA (* pour les quantificateurs *)
%right IMPL
%nonassoc IFF
%right OR
%right AND
%left PLUS
%left MULT
%nonassoc NOT

%start<Nam.formula> parse_formula
%start<Nam.term> parse_term
%type<list Nam.term> p_termlist
%type<Nam.term> p_term
%type<Nam.formula> p_form
%type<list Nam.term> inner

%%

parse_formula : p_form EOF    { $1 }

parse_term : p_term EOF       { $1 }

p_form :
  TRUE                        { Nam.True }
| FALSE                       { Nam.False }
| NOT p_form                  { Nam.Not $2 }
| p_form AND p_form           { Nam.Op And $1 $3 }
| p_form OR p_form            { Nam.Op Or $1 $3 }
| p_form IMPL p_form          { Nam.Op Impl $1 $3 }
| p_form IFF p_form           { Nam.Iff $1 $3 }
| ID                          { Nam.Pred $1 [] }
| ID p_termlist               { Nam.Pred $1 $2 }
| p_term EQ p_term            { Nam.Pred "=" [$1;$3] }
| p_term IN p_term            { Nam.Pred "∈" [$1;$3] }
| ALL ID COMMA p_form         { Nam.Quant All $2 $4 }
| EX ID COMMA p_form          { Nam.Quant Ex $2 $4 }
| LCURL p_form RCURL          { $2 }

p_term :
  ID                          { Nam.Var $1 }
| ID p_termlist               { Nam.Fun $1 $2 }
| p_term PLUS p_term          { Nam.Fun "+" [$1;$3] }
| p_term MULT p_term          { Nam.Fun "*" [$1;$3] }
| INT                         { Nam.nat2term $1 }
| LPAREN p_term RPAREN        { $2 }

p_termlist :
 LPAREN inner                 { $2 }

inner :
  RPAREN                       { [] }
| p_term COMMA inner           { $1 :: $3 }
