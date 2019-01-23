Require Import List.
Require Import Int31.
Require Import Syntax.
Require Import Tuples.
Require Import Alphabet.
Require Grammar.
Require Automaton.

Unset Elimination Schemes.

Module Import Gram <: Grammar.T.

Local Obligation Tactic := intro x; case x; reflexivity.

Inductive terminal' : Set :=
| ALL't
| AND't
| COMMA't
| EOF't
| EQ't
| EX't
| FALSE't
| ID't
| IFF't
| IMPL't
| IN't
| INT't
| LCURL't
| LPAREN't
| MULT't
| NOT't
| OR't
| PLUS't
| RCURL't
| RPAREN't
| TRUE't.
Definition terminal := terminal'.

Program Instance terminalNum : Numbered terminal :=
  { inj := fun x => match x return _ with | ALL't => Int31.On | AND't => Int31.In | COMMA't => (twice Int31.In) | EOF't => (twice_plus_one Int31.In) | EQ't => (twice (twice Int31.In)) | EX't => (twice_plus_one (twice Int31.In)) | FALSE't => (twice (twice_plus_one Int31.In)) | ID't => (twice_plus_one (twice_plus_one Int31.In)) | IFF't => (twice (twice (twice Int31.In))) | IMPL't => (twice_plus_one (twice (twice Int31.In))) | IN't => (twice (twice_plus_one (twice Int31.In))) | INT't => (twice_plus_one (twice_plus_one (twice Int31.In))) | LCURL't => (twice (twice (twice_plus_one Int31.In))) | LPAREN't => (twice_plus_one (twice (twice_plus_one Int31.In))) | MULT't => (twice (twice_plus_one (twice_plus_one Int31.In))) | NOT't => (twice_plus_one (twice_plus_one (twice_plus_one Int31.In))) | OR't => (twice (twice (twice (twice Int31.In)))) | PLUS't => (twice_plus_one (twice (twice (twice Int31.In)))) | RCURL't => (twice (twice_plus_one (twice (twice Int31.In)))) | RPAREN't => (twice_plus_one (twice_plus_one (twice (twice Int31.In)))) | TRUE't => (twice (twice (twice_plus_one (twice Int31.In)))) end;
    surj := (fun n => match n return _ with | 0 => ALL't | 1 => AND't | 2 => COMMA't | 3 => EOF't | 4 => EQ't | 5 => EX't | 6 => FALSE't | 7 => ID't | 8 => IFF't | 9 => IMPL't | 10 => IN't | 11 => INT't | 12 => LCURL't | 13 => LPAREN't | 14 => MULT't | 15 => NOT't | 16 => OR't | 17 => PLUS't | 18 => RCURL't | 19 => RPAREN't | 20 => TRUE't | _ => ALL't end)%int31;
    inj_bound := 21%int31 }.
Instance TerminalAlph : Alphabet terminal := _.

Inductive nonterminal' : Set :=
| inner'nt
| p_form'nt
| p_term'nt
| p_termlist'nt
| parse_formula'nt
| parse_term'nt.
Definition nonterminal := nonterminal'.

Program Instance nonterminalNum : Numbered nonterminal :=
  { inj := fun x => match x return _ with | inner'nt => Int31.On | p_form'nt => Int31.In | p_term'nt => (twice Int31.In) | p_termlist'nt => (twice_plus_one Int31.In) | parse_formula'nt => (twice (twice Int31.In)) | parse_term'nt => (twice_plus_one (twice Int31.In)) end;
    surj := (fun n => match n return _ with | 0 => inner'nt | 1 => p_form'nt | 2 => p_term'nt | 3 => p_termlist'nt | 4 => parse_formula'nt | 5 => parse_term'nt | _ => inner'nt end)%int31;
    inj_bound := 6%int31 }.
Instance NonTerminalAlph : Alphabet nonterminal := _.

Include Grammar.Symbol.

Definition terminal_semantic_type (t:terminal) : Type:=
  match t with
  | TRUE't => unit%type
  | RPAREN't => unit%type
  | RCURL't => unit%type
  | PLUS't => unit%type
  | OR't => unit%type
  | NOT't => unit%type
  | MULT't => unit%type
  | LPAREN't => unit%type
  | LCURL't => unit%type
  | INT't =>       (int)%type
  | IN't => unit%type
  | IMPL't => unit%type
  | IFF't => unit%type
  | ID't =>       (string)%type
  | FALSE't => unit%type
  | EX't => unit%type
  | EQ't => unit%type
  | EOF't => unit%type
  | COMMA't => unit%type
  | AND't => unit%type
  | ALL't => unit%type
  end.

Definition nonterminal_semantic_type (nt:nonterminal) : Type:=
  match nt with
  | parse_term'nt =>       (term)%type
  | parse_formula'nt =>       (formula)%type
  | p_termlist'nt =>      (list term)%type
  | p_term'nt =>      (term)%type
  | p_form'nt =>      (formula)%type
  | inner'nt =>      (list term)%type
  end.

Definition symbol_semantic_type (s:symbol) : Type:=
  match s with
  | T t => terminal_semantic_type t
  | NT nt => nonterminal_semantic_type nt
  end.

Inductive production' : Set :=
| Prod'parse_term'0
| Prod'parse_formula'0
| Prod'p_termlist'0
| Prod'p_term'5
| Prod'p_term'4
| Prod'p_term'3
| Prod'p_term'2
| Prod'p_term'1
| Prod'p_term'0
| Prod'p_form'13
| Prod'p_form'12
| Prod'p_form'11
| Prod'p_form'10
| Prod'p_form'9
| Prod'p_form'8
| Prod'p_form'7
| Prod'p_form'6
| Prod'p_form'5
| Prod'p_form'4
| Prod'p_form'3
| Prod'p_form'2
| Prod'p_form'1
| Prod'p_form'0
| Prod'inner'1
| Prod'inner'0.
Definition production := production'.

Program Instance productionNum : Numbered production :=
  { inj := fun x => match x return _ with | Prod'parse_term'0 => Int31.On | Prod'parse_formula'0 => Int31.In | Prod'p_termlist'0 => (twice Int31.In) | Prod'p_term'5 => (twice_plus_one Int31.In) | Prod'p_term'4 => (twice (twice Int31.In)) | Prod'p_term'3 => (twice_plus_one (twice Int31.In)) | Prod'p_term'2 => (twice (twice_plus_one Int31.In)) | Prod'p_term'1 => (twice_plus_one (twice_plus_one Int31.In)) | Prod'p_term'0 => (twice (twice (twice Int31.In))) | Prod'p_form'13 => (twice_plus_one (twice (twice Int31.In))) | Prod'p_form'12 => (twice (twice_plus_one (twice Int31.In))) | Prod'p_form'11 => (twice_plus_one (twice_plus_one (twice Int31.In))) | Prod'p_form'10 => (twice (twice (twice_plus_one Int31.In))) | Prod'p_form'9 => (twice_plus_one (twice (twice_plus_one Int31.In))) | Prod'p_form'8 => (twice (twice_plus_one (twice_plus_one Int31.In))) | Prod'p_form'7 => (twice_plus_one (twice_plus_one (twice_plus_one Int31.In))) | Prod'p_form'6 => (twice (twice (twice (twice Int31.In)))) | Prod'p_form'5 => (twice_plus_one (twice (twice (twice Int31.In)))) | Prod'p_form'4 => (twice (twice_plus_one (twice (twice Int31.In)))) | Prod'p_form'3 => (twice_plus_one (twice_plus_one (twice (twice Int31.In)))) | Prod'p_form'2 => (twice (twice (twice_plus_one (twice Int31.In)))) | Prod'p_form'1 => (twice_plus_one (twice (twice_plus_one (twice Int31.In)))) | Prod'p_form'0 => (twice (twice_plus_one (twice_plus_one (twice Int31.In)))) | Prod'inner'1 => (twice_plus_one (twice_plus_one (twice_plus_one (twice Int31.In)))) | Prod'inner'0 => (twice (twice (twice (twice_plus_one Int31.In)))) end;
    surj := (fun n => match n return _ with | 0 => Prod'parse_term'0 | 1 => Prod'parse_formula'0 | 2 => Prod'p_termlist'0 | 3 => Prod'p_term'5 | 4 => Prod'p_term'4 | 5 => Prod'p_term'3 | 6 => Prod'p_term'2 | 7 => Prod'p_term'1 | 8 => Prod'p_term'0 | 9 => Prod'p_form'13 | 10 => Prod'p_form'12 | 11 => Prod'p_form'11 | 12 => Prod'p_form'10 | 13 => Prod'p_form'9 | 14 => Prod'p_form'8 | 15 => Prod'p_form'7 | 16 => Prod'p_form'6 | 17 => Prod'p_form'5 | 18 => Prod'p_form'4 | 19 => Prod'p_form'3 | 20 => Prod'p_form'2 | 21 => Prod'p_form'1 | 22 => Prod'p_form'0 | 23 => Prod'inner'1 | 24 => Prod'inner'0 | _ => Prod'parse_term'0 end)%int31;
    inj_bound := 25%int31 }.
Instance ProductionAlph : Alphabet production := _.

Definition prod_contents (p:production) :
  { p:nonterminal * list symbol &
    arrows_left (map symbol_semantic_type (rev (snd p)))
                (symbol_semantic_type (NT (fst p))) }
 :=
  let box := existT (fun p =>
    arrows_left (map symbol_semantic_type (rev (snd p)))
                (symbol_semantic_type (NT (fst p))))
  in
  match p with
  | Prod'inner'0 => box
    (inner'nt, [T RPAREN't])
    (fun _1 =>
                               ( [] )
)
  | Prod'inner'1 => box
    (inner'nt, [NT inner'nt; T COMMA't; NT p_term'nt])
    (fun _3 _2 _1 =>
                               ( _1 :: _3 )
)
  | Prod'p_form'0 => box
    (p_form'nt, [T TRUE't])
    (fun _1 =>
                              ( True )
)
  | Prod'p_form'1 => box
    (p_form'nt, [T FALSE't])
    (fun _1 =>
                              ( False )
)
  | Prod'p_form'2 => box
    (p_form'nt, [NT p_form'nt; T NOT't])
    (fun _2 _1 =>
                              ( Not(_2) )
)
  | Prod'p_form'3 => box
    (p_form'nt, [NT p_form'nt; T AND't; NT p_form'nt])
    (fun _3 _2 _1 =>
                              ( Op(And,_1,_3) )
)
  | Prod'p_form'4 => box
    (p_form'nt, [NT p_form'nt; T OR't; NT p_form'nt])
    (fun _3 _2 _1 =>
                              ( Op(Or,_1,_3) )
)
  | Prod'p_form'5 => box
    (p_form'nt, [NT p_form'nt; T IMPL't; NT p_form'nt])
    (fun _3 _2 _1 =>
                              ( Op(Impl,_1,_3) )
)
  | Prod'p_form'6 => box
    (p_form'nt, [NT p_form'nt; T IFF't; NT p_form'nt])
    (fun _3 _2 _1 =>
                              ( iff _1 _3 )
)
  | Prod'p_form'7 => box
    (p_form'nt, [T ID't])
    (fun _1 =>
                              ( Pred(_1,[]) )
)
  | Prod'p_form'8 => box
    (p_form'nt, [NT p_termlist'nt; T ID't])
    (fun _2 _1 =>
                              ( Pred(_1,_2) )
)
  | Prod'p_form'9 => box
    (p_form'nt, [NT p_term'nt; T EQ't; NT p_term'nt])
    (fun _3 _2 _1 =>
                              ( Pred("=",[_1;_3]) )
)
  | Prod'p_form'10 => box
    (p_form'nt, [NT p_term'nt; T IN't; NT p_term'nt])
    (fun _3 _2 _1 =>
                              ( Pred("∈",[_1;_3]) )
)
  | Prod'p_form'11 => box
    (p_form'nt, [NT p_form'nt; T COMMA't; T ID't; T ALL't])
    (fun _4 _3 _2 _1 =>
                              ( Quant(All,_2,_4) )
)
  | Prod'p_form'12 => box
    (p_form'nt, [NT p_form'nt; T COMMA't; T ID't; T EX't])
    (fun _4 _3 _2 _1 =>
                              ( Quant(Ex,_2,_4) )
)
  | Prod'p_form'13 => box
    (p_form'nt, [T RCURL't; NT p_form'nt; T LCURL't])
    (fun _3 _2 _1 =>
                              ( _2 )
)
  | Prod'p_term'0 => box
    (p_term'nt, [T ID't])
    (fun _1 =>
                              ( Var _1 )
)
  | Prod'p_term'1 => box
    (p_term'nt, [NT p_termlist'nt; T ID't])
    (fun _2 _1 =>
                              ( Fun (_1,_2) )
)
  | Prod'p_term'2 => box
    (p_term'nt, [NT p_term'nt; T PLUS't; NT p_term'nt])
    (fun _3 _2 _1 =>
                              ( Fun ("+",[_1;_3]) )
)
  | Prod'p_term'3 => box
    (p_term'nt, [NT p_term'nt; T MULT't; NT p_term'nt])
    (fun _3 _2 _1 =>
                              ( Fun ("*",[_1;_3]) )
)
  | Prod'p_term'4 => box
    (p_term'nt, [T INT't])
    (fun _1 =>
                              ( int2term _1 )
)
  | Prod'p_term'5 => box
    (p_term'nt, [T RPAREN't; NT p_term'nt; T LPAREN't])
    (fun _3 _2 _1 =>
                              ( _2 )
)
  | Prod'p_termlist'0 => box
    (p_termlist'nt, [NT inner'nt; T LPAREN't])
    (fun _2 _1 =>
                              ( _2 )
)
  | Prod'parse_formula'0 => box
    (parse_formula'nt, [T EOF't; NT p_form'nt])
    (fun _2 _1 =>
                              ( _1 )
)
  | Prod'parse_term'0 => box
    (parse_term'nt, [T EOF't; NT p_term'nt])
    (fun _2 _1 =>
                              ( _1 )
)
  end.

Definition prod_lhs (p:production) :=
  fst (projT1 (prod_contents p)).
Definition prod_rhs_rev (p:production) :=
  snd (projT1 (prod_contents p)).
Definition prod_action (p:production) :=
  projT2 (prod_contents p).

Include Grammar.Defs.

End Gram.

Module Aut <: Automaton.T.

Local Obligation Tactic := intro x; case x; reflexivity.

Module Gram := Gram.
Module GramDefs := Gram.

Definition nullable_nterm (nt:nonterminal) : bool :=
  match nt with
  | parse_term'nt => false
  | parse_formula'nt => false
  | p_termlist'nt => false
  | p_term'nt => false
  | p_form'nt => false
  | inner'nt => false
  end.

Definition first_nterm (nt:nonterminal) : list terminal :=
  match nt with
  | parse_term'nt => [LPAREN't; INT't; ID't]
  | parse_formula'nt => [TRUE't; NOT't; LPAREN't; LCURL't; INT't; ID't; FALSE't; EX't; ALL't]
  | p_termlist'nt => [LPAREN't]
  | p_term'nt => [LPAREN't; INT't; ID't]
  | p_form'nt => [TRUE't; NOT't; LPAREN't; LCURL't; INT't; ID't; FALSE't; EX't; ALL't]
  | inner'nt => [RPAREN't; LPAREN't; INT't; ID't]
  end.

Inductive noninitstate' : Set :=
| Nis'53
| Nis'52
| Nis'49
| Nis'48
| Nis'46
| Nis'45
| Nis'44
| Nis'43
| Nis'42
| Nis'41
| Nis'40
| Nis'39
| Nis'38
| Nis'37
| Nis'36
| Nis'35
| Nis'34
| Nis'33
| Nis'32
| Nis'31
| Nis'30
| Nis'29
| Nis'28
| Nis'27
| Nis'26
| Nis'25
| Nis'24
| Nis'23
| Nis'22
| Nis'21
| Nis'20
| Nis'19
| Nis'18
| Nis'17
| Nis'16
| Nis'15
| Nis'14
| Nis'13
| Nis'12
| Nis'11
| Nis'10
| Nis'9
| Nis'8
| Nis'7
| Nis'6
| Nis'5
| Nis'4
| Nis'3
| Nis'2
| Nis'1.
Definition noninitstate := noninitstate'.

Program Instance noninitstateNum : Numbered noninitstate :=
  { inj := fun x => match x return _ with | Nis'53 => Int31.On | Nis'52 => Int31.In | Nis'49 => (twice Int31.In) | Nis'48 => (twice_plus_one Int31.In) | Nis'46 => (twice (twice Int31.In)) | Nis'45 => (twice_plus_one (twice Int31.In)) | Nis'44 => (twice (twice_plus_one Int31.In)) | Nis'43 => (twice_plus_one (twice_plus_one Int31.In)) | Nis'42 => (twice (twice (twice Int31.In))) | Nis'41 => (twice_plus_one (twice (twice Int31.In))) | Nis'40 => (twice (twice_plus_one (twice Int31.In))) | Nis'39 => (twice_plus_one (twice_plus_one (twice Int31.In))) | Nis'38 => (twice (twice (twice_plus_one Int31.In))) | Nis'37 => (twice_plus_one (twice (twice_plus_one Int31.In))) | Nis'36 => (twice (twice_plus_one (twice_plus_one Int31.In))) | Nis'35 => (twice_plus_one (twice_plus_one (twice_plus_one Int31.In))) | Nis'34 => (twice (twice (twice (twice Int31.In)))) | Nis'33 => (twice_plus_one (twice (twice (twice Int31.In)))) | Nis'32 => (twice (twice_plus_one (twice (twice Int31.In)))) | Nis'31 => (twice_plus_one (twice_plus_one (twice (twice Int31.In)))) | Nis'30 => (twice (twice (twice_plus_one (twice Int31.In)))) | Nis'29 => (twice_plus_one (twice (twice_plus_one (twice Int31.In)))) | Nis'28 => (twice (twice_plus_one (twice_plus_one (twice Int31.In)))) | Nis'27 => (twice_plus_one (twice_plus_one (twice_plus_one (twice Int31.In)))) | Nis'26 => (twice (twice (twice (twice_plus_one Int31.In)))) | Nis'25 => (twice_plus_one (twice (twice (twice_plus_one Int31.In)))) | Nis'24 => (twice (twice_plus_one (twice (twice_plus_one Int31.In)))) | Nis'23 => (twice_plus_one (twice_plus_one (twice (twice_plus_one Int31.In)))) | Nis'22 => (twice (twice (twice_plus_one (twice_plus_one Int31.In)))) | Nis'21 => (twice_plus_one (twice (twice_plus_one (twice_plus_one Int31.In)))) | Nis'20 => (twice (twice_plus_one (twice_plus_one (twice_plus_one Int31.In)))) | Nis'19 => (twice_plus_one (twice_plus_one (twice_plus_one (twice_plus_one Int31.In)))) | Nis'18 => (twice (twice (twice (twice (twice Int31.In))))) | Nis'17 => (twice_plus_one (twice (twice (twice (twice Int31.In))))) | Nis'16 => (twice (twice_plus_one (twice (twice (twice Int31.In))))) | Nis'15 => (twice_plus_one (twice_plus_one (twice (twice (twice Int31.In))))) | Nis'14 => (twice (twice (twice_plus_one (twice (twice Int31.In))))) | Nis'13 => (twice_plus_one (twice (twice_plus_one (twice (twice Int31.In))))) | Nis'12 => (twice (twice_plus_one (twice_plus_one (twice (twice Int31.In))))) | Nis'11 => (twice_plus_one (twice_plus_one (twice_plus_one (twice (twice Int31.In))))) | Nis'10 => (twice (twice (twice (twice_plus_one (twice Int31.In))))) | Nis'9 => (twice_plus_one (twice (twice (twice_plus_one (twice Int31.In))))) | Nis'8 => (twice (twice_plus_one (twice (twice_plus_one (twice Int31.In))))) | Nis'7 => (twice_plus_one (twice_plus_one (twice (twice_plus_one (twice Int31.In))))) | Nis'6 => (twice (twice (twice_plus_one (twice_plus_one (twice Int31.In))))) | Nis'5 => (twice_plus_one (twice (twice_plus_one (twice_plus_one (twice Int31.In))))) | Nis'4 => (twice (twice_plus_one (twice_plus_one (twice_plus_one (twice Int31.In))))) | Nis'3 => (twice_plus_one (twice_plus_one (twice_plus_one (twice_plus_one (twice Int31.In))))) | Nis'2 => (twice (twice (twice (twice (twice_plus_one Int31.In))))) | Nis'1 => (twice_plus_one (twice (twice (twice (twice_plus_one Int31.In))))) end;
    surj := (fun n => match n return _ with | 0 => Nis'53 | 1 => Nis'52 | 2 => Nis'49 | 3 => Nis'48 | 4 => Nis'46 | 5 => Nis'45 | 6 => Nis'44 | 7 => Nis'43 | 8 => Nis'42 | 9 => Nis'41 | 10 => Nis'40 | 11 => Nis'39 | 12 => Nis'38 | 13 => Nis'37 | 14 => Nis'36 | 15 => Nis'35 | 16 => Nis'34 | 17 => Nis'33 | 18 => Nis'32 | 19 => Nis'31 | 20 => Nis'30 | 21 => Nis'29 | 22 => Nis'28 | 23 => Nis'27 | 24 => Nis'26 | 25 => Nis'25 | 26 => Nis'24 | 27 => Nis'23 | 28 => Nis'22 | 29 => Nis'21 | 30 => Nis'20 | 31 => Nis'19 | 32 => Nis'18 | 33 => Nis'17 | 34 => Nis'16 | 35 => Nis'15 | 36 => Nis'14 | 37 => Nis'13 | 38 => Nis'12 | 39 => Nis'11 | 40 => Nis'10 | 41 => Nis'9 | 42 => Nis'8 | 43 => Nis'7 | 44 => Nis'6 | 45 => Nis'5 | 46 => Nis'4 | 47 => Nis'3 | 48 => Nis'2 | 49 => Nis'1 | _ => Nis'53 end)%int31;
    inj_bound := 50%int31 }.
Instance NonInitStateAlph : Alphabet noninitstate := _.

Definition last_symb_of_non_init_state (noninitstate:noninitstate) : symbol :=
  match noninitstate with
  | Nis'1 => T TRUE't
  | Nis'2 => T NOT't
  | Nis'3 => T LPAREN't
  | Nis'4 => T INT't
  | Nis'5 => T ID't
  | Nis'6 => T LPAREN't
  | Nis'7 => T RPAREN't
  | Nis'8 => NT p_term'nt
  | Nis'9 => T PLUS't
  | Nis'10 => NT p_term'nt
  | Nis'11 => T MULT't
  | Nis'12 => NT p_term'nt
  | Nis'13 => T COMMA't
  | Nis'14 => NT inner'nt
  | Nis'15 => NT inner'nt
  | Nis'16 => NT p_termlist'nt
  | Nis'17 => NT p_term'nt
  | Nis'18 => T RPAREN't
  | Nis'19 => T LCURL't
  | Nis'20 => T ID't
  | Nis'21 => NT p_termlist'nt
  | Nis'22 => T FALSE't
  | Nis'23 => T EX't
  | Nis'24 => T ID't
  | Nis'25 => T COMMA't
  | Nis'26 => T ALL't
  | Nis'27 => T ID't
  | Nis'28 => T COMMA't
  | Nis'29 => NT p_term'nt
  | Nis'30 => T IN't
  | Nis'31 => NT p_term'nt
  | Nis'32 => T EQ't
  | Nis'33 => NT p_term'nt
  | Nis'34 => NT p_form'nt
  | Nis'35 => T OR't
  | Nis'36 => NT p_form'nt
  | Nis'37 => T AND't
  | Nis'38 => NT p_form'nt
  | Nis'39 => T IMPL't
  | Nis'40 => NT p_form'nt
  | Nis'41 => T IFF't
  | Nis'42 => NT p_form'nt
  | Nis'43 => NT p_form'nt
  | Nis'44 => NT p_form'nt
  | Nis'45 => T RCURL't
  | Nis'46 => NT p_form'nt
  | Nis'48 => NT p_form'nt
  | Nis'49 => T EOF't
  | Nis'52 => NT p_term'nt
  | Nis'53 => T EOF't
  end.

Inductive initstate' : Set :=
| Init'50
| Init'0.
Definition initstate := initstate'.

Program Instance initstateNum : Numbered initstate :=
  { inj := fun x => match x return _ with | Init'50 => Int31.On | Init'0 => Int31.In end;
    surj := (fun n => match n return _ with | 0 => Init'50 | 1 => Init'0 | _ => Init'50 end)%int31;
    inj_bound := 2%int31 }.
Instance InitStateAlph : Alphabet initstate := _.

Include Automaton.Types.

Definition start_nt (init:initstate) : nonterminal :=
  match init with
  | Init'0 => parse_formula'nt
  | Init'50 => parse_term'nt
  end.

Definition action_table (state:state) : action :=
  match state with
  | Init Init'0 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | TRUE't => Shift_act Nis'1 (eq_refl _)
    | NOT't => Shift_act Nis'2 (eq_refl _)
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | LCURL't => Shift_act Nis'19 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'20 (eq_refl _)
    | FALSE't => Shift_act Nis'22 (eq_refl _)
    | EX't => Shift_act Nis'23 (eq_refl _)
    | ALL't => Shift_act Nis'26 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'1 => Default_reduce_act Prod'p_form'0
  | Ninit Nis'2 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | TRUE't => Shift_act Nis'1 (eq_refl _)
    | NOT't => Shift_act Nis'2 (eq_refl _)
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | LCURL't => Shift_act Nis'19 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'20 (eq_refl _)
    | FALSE't => Shift_act Nis'22 (eq_refl _)
    | EX't => Shift_act Nis'23 (eq_refl _)
    | ALL't => Shift_act Nis'26 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'3 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'5 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'4 => Default_reduce_act Prod'p_term'4
  | Ninit Nis'5 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Reduce_act Prod'p_term'0
    | RCURL't => Reduce_act Prod'p_term'0
    | PLUS't => Reduce_act Prod'p_term'0
    | OR't => Reduce_act Prod'p_term'0
    | MULT't => Reduce_act Prod'p_term'0
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | IN't => Reduce_act Prod'p_term'0
    | IMPL't => Reduce_act Prod'p_term'0
    | IFF't => Reduce_act Prod'p_term'0
    | EQ't => Reduce_act Prod'p_term'0
    | EOF't => Reduce_act Prod'p_term'0
    | COMMA't => Reduce_act Prod'p_term'0
    | AND't => Reduce_act Prod'p_term'0
    | _ => Fail_act
    end)
  | Ninit Nis'6 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'7 (eq_refl _)
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'5 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'7 => Default_reduce_act Prod'inner'0
  | Ninit Nis'8 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | PLUS't => Shift_act Nis'9 (eq_refl _)
    | MULT't => Shift_act Nis'11 (eq_refl _)
    | COMMA't => Shift_act Nis'13 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'9 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'5 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'10 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Reduce_act Prod'p_term'2
    | RCURL't => Reduce_act Prod'p_term'2
    | PLUS't => Reduce_act Prod'p_term'2
    | OR't => Reduce_act Prod'p_term'2
    | MULT't => Shift_act Nis'11 (eq_refl _)
    | IN't => Reduce_act Prod'p_term'2
    | IMPL't => Reduce_act Prod'p_term'2
    | IFF't => Reduce_act Prod'p_term'2
    | EQ't => Reduce_act Prod'p_term'2
    | EOF't => Reduce_act Prod'p_term'2
    | COMMA't => Reduce_act Prod'p_term'2
    | AND't => Reduce_act Prod'p_term'2
    | _ => Fail_act
    end)
  | Ninit Nis'11 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'5 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'12 => Default_reduce_act Prod'p_term'3
  | Ninit Nis'13 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'7 (eq_refl _)
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'5 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'14 => Default_reduce_act Prod'inner'1
  | Ninit Nis'15 => Default_reduce_act Prod'p_termlist'0
  | Ninit Nis'16 => Default_reduce_act Prod'p_term'1
  | Ninit Nis'17 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RPAREN't => Shift_act Nis'18 (eq_refl _)
    | PLUS't => Shift_act Nis'9 (eq_refl _)
    | MULT't => Shift_act Nis'11 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'18 => Default_reduce_act Prod'p_term'5
  | Ninit Nis'19 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | TRUE't => Shift_act Nis'1 (eq_refl _)
    | NOT't => Shift_act Nis'2 (eq_refl _)
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | LCURL't => Shift_act Nis'19 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'20 (eq_refl _)
    | FALSE't => Shift_act Nis'22 (eq_refl _)
    | EX't => Shift_act Nis'23 (eq_refl _)
    | ALL't => Shift_act Nis'26 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'20 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RCURL't => Reduce_act Prod'p_form'7
    | PLUS't => Reduce_act Prod'p_term'0
    | OR't => Reduce_act Prod'p_form'7
    | MULT't => Reduce_act Prod'p_term'0
    | LPAREN't => Shift_act Nis'6 (eq_refl _)
    | IN't => Reduce_act Prod'p_term'0
    | IMPL't => Reduce_act Prod'p_form'7
    | IFF't => Reduce_act Prod'p_form'7
    | EQ't => Reduce_act Prod'p_term'0
    | EOF't => Reduce_act Prod'p_form'7
    | AND't => Reduce_act Prod'p_form'7
    | _ => Fail_act
    end)
  | Ninit Nis'21 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RCURL't => Reduce_act Prod'p_form'8
    | PLUS't => Reduce_act Prod'p_term'1
    | OR't => Reduce_act Prod'p_form'8
    | MULT't => Reduce_act Prod'p_term'1
    | IN't => Reduce_act Prod'p_term'1
    | IMPL't => Reduce_act Prod'p_form'8
    | IFF't => Reduce_act Prod'p_form'8
    | EQ't => Reduce_act Prod'p_term'1
    | EOF't => Reduce_act Prod'p_form'8
    | AND't => Reduce_act Prod'p_form'8
    | _ => Fail_act
    end)
  | Ninit Nis'22 => Default_reduce_act Prod'p_form'1
  | Ninit Nis'23 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Shift_act Nis'24 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'24 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COMMA't => Shift_act Nis'25 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'25 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | TRUE't => Shift_act Nis'1 (eq_refl _)
    | NOT't => Shift_act Nis'2 (eq_refl _)
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | LCURL't => Shift_act Nis'19 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'20 (eq_refl _)
    | FALSE't => Shift_act Nis'22 (eq_refl _)
    | EX't => Shift_act Nis'23 (eq_refl _)
    | ALL't => Shift_act Nis'26 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'26 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Shift_act Nis'27 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'27 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COMMA't => Shift_act Nis'28 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'28 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | TRUE't => Shift_act Nis'1 (eq_refl _)
    | NOT't => Shift_act Nis'2 (eq_refl _)
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | LCURL't => Shift_act Nis'19 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'20 (eq_refl _)
    | FALSE't => Shift_act Nis'22 (eq_refl _)
    | EX't => Shift_act Nis'23 (eq_refl _)
    | ALL't => Shift_act Nis'26 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'29 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | PLUS't => Shift_act Nis'9 (eq_refl _)
    | MULT't => Shift_act Nis'11 (eq_refl _)
    | IN't => Shift_act Nis'30 (eq_refl _)
    | EQ't => Shift_act Nis'32 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'30 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'5 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'31 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RCURL't => Reduce_act Prod'p_form'10
    | PLUS't => Shift_act Nis'9 (eq_refl _)
    | OR't => Reduce_act Prod'p_form'10
    | MULT't => Shift_act Nis'11 (eq_refl _)
    | IMPL't => Reduce_act Prod'p_form'10
    | IFF't => Reduce_act Prod'p_form'10
    | EOF't => Reduce_act Prod'p_form'10
    | AND't => Reduce_act Prod'p_form'10
    | _ => Fail_act
    end)
  | Ninit Nis'32 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'5 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'33 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RCURL't => Reduce_act Prod'p_form'9
    | PLUS't => Shift_act Nis'9 (eq_refl _)
    | OR't => Reduce_act Prod'p_form'9
    | MULT't => Shift_act Nis'11 (eq_refl _)
    | IMPL't => Reduce_act Prod'p_form'9
    | IFF't => Reduce_act Prod'p_form'9
    | EOF't => Reduce_act Prod'p_form'9
    | AND't => Reduce_act Prod'p_form'9
    | _ => Fail_act
    end)
  | Ninit Nis'34 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RCURL't => Reduce_act Prod'p_form'11
    | OR't => Shift_act Nis'35 (eq_refl _)
    | IMPL't => Shift_act Nis'39 (eq_refl _)
    | IFF't => Shift_act Nis'41 (eq_refl _)
    | EOF't => Reduce_act Prod'p_form'11
    | AND't => Shift_act Nis'37 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'35 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | TRUE't => Shift_act Nis'1 (eq_refl _)
    | NOT't => Shift_act Nis'2 (eq_refl _)
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | LCURL't => Shift_act Nis'19 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'20 (eq_refl _)
    | FALSE't => Shift_act Nis'22 (eq_refl _)
    | EX't => Shift_act Nis'23 (eq_refl _)
    | ALL't => Shift_act Nis'26 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'36 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RCURL't => Reduce_act Prod'p_form'4
    | OR't => Shift_act Nis'35 (eq_refl _)
    | IMPL't => Reduce_act Prod'p_form'4
    | IFF't => Reduce_act Prod'p_form'4
    | EOF't => Reduce_act Prod'p_form'4
    | AND't => Shift_act Nis'37 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'37 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | TRUE't => Shift_act Nis'1 (eq_refl _)
    | NOT't => Shift_act Nis'2 (eq_refl _)
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | LCURL't => Shift_act Nis'19 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'20 (eq_refl _)
    | FALSE't => Shift_act Nis'22 (eq_refl _)
    | EX't => Shift_act Nis'23 (eq_refl _)
    | ALL't => Shift_act Nis'26 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'38 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RCURL't => Reduce_act Prod'p_form'3
    | OR't => Reduce_act Prod'p_form'3
    | IMPL't => Reduce_act Prod'p_form'3
    | IFF't => Reduce_act Prod'p_form'3
    | EOF't => Reduce_act Prod'p_form'3
    | AND't => Shift_act Nis'37 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'39 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | TRUE't => Shift_act Nis'1 (eq_refl _)
    | NOT't => Shift_act Nis'2 (eq_refl _)
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | LCURL't => Shift_act Nis'19 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'20 (eq_refl _)
    | FALSE't => Shift_act Nis'22 (eq_refl _)
    | EX't => Shift_act Nis'23 (eq_refl _)
    | ALL't => Shift_act Nis'26 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'40 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RCURL't => Reduce_act Prod'p_form'5
    | OR't => Shift_act Nis'35 (eq_refl _)
    | IMPL't => Shift_act Nis'39 (eq_refl _)
    | IFF't => Shift_act Nis'41 (eq_refl _)
    | EOF't => Reduce_act Prod'p_form'5
    | AND't => Shift_act Nis'37 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'41 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | TRUE't => Shift_act Nis'1 (eq_refl _)
    | NOT't => Shift_act Nis'2 (eq_refl _)
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | LCURL't => Shift_act Nis'19 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'20 (eq_refl _)
    | FALSE't => Shift_act Nis'22 (eq_refl _)
    | EX't => Shift_act Nis'23 (eq_refl _)
    | ALL't => Shift_act Nis'26 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'42 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RCURL't => Reduce_act Prod'p_form'6
    | OR't => Shift_act Nis'35 (eq_refl _)
    | IMPL't => Reduce_act Prod'p_form'6
    | EOF't => Reduce_act Prod'p_form'6
    | AND't => Shift_act Nis'37 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'43 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RCURL't => Reduce_act Prod'p_form'12
    | OR't => Shift_act Nis'35 (eq_refl _)
    | IMPL't => Shift_act Nis'39 (eq_refl _)
    | IFF't => Shift_act Nis'41 (eq_refl _)
    | EOF't => Reduce_act Prod'p_form'12
    | AND't => Shift_act Nis'37 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'44 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RCURL't => Shift_act Nis'45 (eq_refl _)
    | OR't => Shift_act Nis'35 (eq_refl _)
    | IMPL't => Shift_act Nis'39 (eq_refl _)
    | IFF't => Shift_act Nis'41 (eq_refl _)
    | AND't => Shift_act Nis'37 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'45 => Default_reduce_act Prod'p_form'13
  | Ninit Nis'46 => Default_reduce_act Prod'p_form'2
  | Ninit Nis'48 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | OR't => Shift_act Nis'35 (eq_refl _)
    | IMPL't => Shift_act Nis'39 (eq_refl _)
    | IFF't => Shift_act Nis'41 (eq_refl _)
    | EOF't => Shift_act Nis'49 (eq_refl _)
    | AND't => Shift_act Nis'37 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'49 => Default_reduce_act Prod'parse_formula'0
  | Init Init'50 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LPAREN't => Shift_act Nis'3 (eq_refl _)
    | INT't => Shift_act Nis'4 (eq_refl _)
    | ID't => Shift_act Nis'5 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'52 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | PLUS't => Shift_act Nis'9 (eq_refl _)
    | MULT't => Shift_act Nis'11 (eq_refl _)
    | EOF't => Shift_act Nis'53 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'53 => Default_reduce_act Prod'parse_term'0
  end.

Definition goto_table (state:state) (nt:nonterminal) :=
  match state, nt return option { s:noninitstate | NT nt = last_symb_of_non_init_state s } with
  | Init Init'0, parse_formula'nt => None  | Init Init'0, p_term'nt => Some (exist _ Nis'29 (eq_refl _))
  | Init Init'0, p_form'nt => Some (exist _ Nis'48 (eq_refl _))
  | Ninit Nis'2, p_term'nt => Some (exist _ Nis'29 (eq_refl _))
  | Ninit Nis'2, p_form'nt => Some (exist _ Nis'46 (eq_refl _))
  | Ninit Nis'3, p_term'nt => Some (exist _ Nis'17 (eq_refl _))
  | Ninit Nis'5, p_termlist'nt => Some (exist _ Nis'16 (eq_refl _))
  | Ninit Nis'6, p_term'nt => Some (exist _ Nis'8 (eq_refl _))
  | Ninit Nis'6, inner'nt => Some (exist _ Nis'15 (eq_refl _))
  | Ninit Nis'9, p_term'nt => Some (exist _ Nis'10 (eq_refl _))
  | Ninit Nis'11, p_term'nt => Some (exist _ Nis'12 (eq_refl _))
  | Ninit Nis'13, p_term'nt => Some (exist _ Nis'8 (eq_refl _))
  | Ninit Nis'13, inner'nt => Some (exist _ Nis'14 (eq_refl _))
  | Ninit Nis'19, p_term'nt => Some (exist _ Nis'29 (eq_refl _))
  | Ninit Nis'19, p_form'nt => Some (exist _ Nis'44 (eq_refl _))
  | Ninit Nis'20, p_termlist'nt => Some (exist _ Nis'21 (eq_refl _))
  | Ninit Nis'25, p_term'nt => Some (exist _ Nis'29 (eq_refl _))
  | Ninit Nis'25, p_form'nt => Some (exist _ Nis'43 (eq_refl _))
  | Ninit Nis'28, p_term'nt => Some (exist _ Nis'29 (eq_refl _))
  | Ninit Nis'28, p_form'nt => Some (exist _ Nis'34 (eq_refl _))
  | Ninit Nis'30, p_term'nt => Some (exist _ Nis'31 (eq_refl _))
  | Ninit Nis'32, p_term'nt => Some (exist _ Nis'33 (eq_refl _))
  | Ninit Nis'35, p_term'nt => Some (exist _ Nis'29 (eq_refl _))
  | Ninit Nis'35, p_form'nt => Some (exist _ Nis'36 (eq_refl _))
  | Ninit Nis'37, p_term'nt => Some (exist _ Nis'29 (eq_refl _))
  | Ninit Nis'37, p_form'nt => Some (exist _ Nis'38 (eq_refl _))
  | Ninit Nis'39, p_term'nt => Some (exist _ Nis'29 (eq_refl _))
  | Ninit Nis'39, p_form'nt => Some (exist _ Nis'40 (eq_refl _))
  | Ninit Nis'41, p_term'nt => Some (exist _ Nis'29 (eq_refl _))
  | Ninit Nis'41, p_form'nt => Some (exist _ Nis'42 (eq_refl _))
  | Init Init'50, parse_term'nt => None  | Init Init'50, p_term'nt => Some (exist _ Nis'52 (eq_refl _))
  | _, _ => None
  end.

Definition past_symb_of_non_init_state (noninitstate:noninitstate) : list symbol :=
  match noninitstate with
  | Nis'1 => []
  | Nis'2 => []
  | Nis'3 => []
  | Nis'4 => []
  | Nis'5 => []
  | Nis'6 => []
  | Nis'7 => []
  | Nis'8 => []
  | Nis'9 => [NT p_term'nt]
  | Nis'10 => [T PLUS't; NT p_term'nt]
  | Nis'11 => [NT p_term'nt]
  | Nis'12 => [T MULT't; NT p_term'nt]
  | Nis'13 => [NT p_term'nt]
  | Nis'14 => [T COMMA't; NT p_term'nt]
  | Nis'15 => [T LPAREN't]
  | Nis'16 => [T ID't]
  | Nis'17 => [T LPAREN't]
  | Nis'18 => [NT p_term'nt; T LPAREN't]
  | Nis'19 => []
  | Nis'20 => []
  | Nis'21 => [T ID't]
  | Nis'22 => []
  | Nis'23 => []
  | Nis'24 => [T EX't]
  | Nis'25 => [T ID't; T EX't]
  | Nis'26 => []
  | Nis'27 => [T ALL't]
  | Nis'28 => [T ID't; T ALL't]
  | Nis'29 => []
  | Nis'30 => [NT p_term'nt]
  | Nis'31 => [T IN't; NT p_term'nt]
  | Nis'32 => [NT p_term'nt]
  | Nis'33 => [T EQ't; NT p_term'nt]
  | Nis'34 => [T COMMA't; T ID't; T ALL't]
  | Nis'35 => [NT p_form'nt]
  | Nis'36 => [T OR't; NT p_form'nt]
  | Nis'37 => [NT p_form'nt]
  | Nis'38 => [T AND't; NT p_form'nt]
  | Nis'39 => [NT p_form'nt]
  | Nis'40 => [T IMPL't; NT p_form'nt]
  | Nis'41 => [NT p_form'nt]
  | Nis'42 => [T IFF't; NT p_form'nt]
  | Nis'43 => [T COMMA't; T ID't; T EX't]
  | Nis'44 => [T LCURL't]
  | Nis'45 => [NT p_form'nt; T LCURL't]
  | Nis'46 => [T NOT't]
  | Nis'48 => []
  | Nis'49 => [NT p_form'nt]
  | Nis'52 => []
  | Nis'53 => [NT p_term'nt]
  end.
Extract Constant past_symb_of_non_init_state => "fun _ -> assert false".

Definition state_set_1 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'2 | Ninit Nis'19 | Ninit Nis'25 | Ninit Nis'28 | Ninit Nis'35 | Ninit Nis'37 | Ninit Nis'39 | Ninit Nis'41 => true
  | _ => false
  end.
Extract Inlined Constant state_set_1 => "assert false".

Definition state_set_2 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'2 | Ninit Nis'3 | Ninit Nis'6 | Ninit Nis'9 | Ninit Nis'11 | Ninit Nis'13 | Ninit Nis'19 | Ninit Nis'25 | Ninit Nis'28 | Ninit Nis'30 | Ninit Nis'32 | Ninit Nis'35 | Ninit Nis'37 | Ninit Nis'39 | Ninit Nis'41 | Init Init'50 => true
  | _ => false
  end.
Extract Inlined Constant state_set_2 => "assert false".

Definition state_set_3 (s:state) : bool :=
  match s with
  | Ninit Nis'3 | Ninit Nis'6 | Ninit Nis'9 | Ninit Nis'11 | Ninit Nis'13 | Ninit Nis'30 | Ninit Nis'32 | Init Init'50 => true
  | _ => false
  end.
Extract Inlined Constant state_set_3 => "assert false".

Definition state_set_4 (s:state) : bool :=
  match s with
  | Ninit Nis'5 | Ninit Nis'20 => true
  | _ => false
  end.
Extract Inlined Constant state_set_4 => "assert false".

Definition state_set_5 (s:state) : bool :=
  match s with
  | Ninit Nis'6 | Ninit Nis'13 => true
  | _ => false
  end.
Extract Inlined Constant state_set_5 => "assert false".

Definition state_set_6 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'2 | Ninit Nis'3 | Ninit Nis'6 | Ninit Nis'13 | Ninit Nis'19 | Ninit Nis'25 | Ninit Nis'28 | Ninit Nis'30 | Ninit Nis'32 | Ninit Nis'35 | Ninit Nis'37 | Ninit Nis'39 | Ninit Nis'41 | Init Init'50 => true
  | _ => false
  end.
Extract Inlined Constant state_set_6 => "assert false".

Definition state_set_7 (s:state) : bool :=
  match s with
  | Ninit Nis'8 | Ninit Nis'17 | Ninit Nis'29 | Ninit Nis'31 | Ninit Nis'33 | Ninit Nis'52 => true
  | _ => false
  end.
Extract Inlined Constant state_set_7 => "assert false".

Definition state_set_8 (s:state) : bool :=
  match s with
  | Ninit Nis'9 => true
  | _ => false
  end.
Extract Inlined Constant state_set_8 => "assert false".

Definition state_set_9 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'2 | Ninit Nis'3 | Ninit Nis'6 | Ninit Nis'9 | Ninit Nis'13 | Ninit Nis'19 | Ninit Nis'25 | Ninit Nis'28 | Ninit Nis'30 | Ninit Nis'32 | Ninit Nis'35 | Ninit Nis'37 | Ninit Nis'39 | Ninit Nis'41 | Init Init'50 => true
  | _ => false
  end.
Extract Inlined Constant state_set_9 => "assert false".

Definition state_set_10 (s:state) : bool :=
  match s with
  | Ninit Nis'8 | Ninit Nis'10 | Ninit Nis'17 | Ninit Nis'29 | Ninit Nis'31 | Ninit Nis'33 | Ninit Nis'52 => true
  | _ => false
  end.
Extract Inlined Constant state_set_10 => "assert false".

Definition state_set_11 (s:state) : bool :=
  match s with
  | Ninit Nis'11 => true
  | _ => false
  end.
Extract Inlined Constant state_set_11 => "assert false".

Definition state_set_12 (s:state) : bool :=
  match s with
  | Ninit Nis'8 => true
  | _ => false
  end.
Extract Inlined Constant state_set_12 => "assert false".

Definition state_set_13 (s:state) : bool :=
  match s with
  | Ninit Nis'13 => true
  | _ => false
  end.
Extract Inlined Constant state_set_13 => "assert false".

Definition state_set_14 (s:state) : bool :=
  match s with
  | Ninit Nis'6 => true
  | _ => false
  end.
Extract Inlined Constant state_set_14 => "assert false".

Definition state_set_15 (s:state) : bool :=
  match s with
  | Ninit Nis'5 => true
  | _ => false
  end.
Extract Inlined Constant state_set_15 => "assert false".

Definition state_set_16 (s:state) : bool :=
  match s with
  | Ninit Nis'3 => true
  | _ => false
  end.
Extract Inlined Constant state_set_16 => "assert false".

Definition state_set_17 (s:state) : bool :=
  match s with
  | Ninit Nis'17 => true
  | _ => false
  end.
Extract Inlined Constant state_set_17 => "assert false".

Definition state_set_18 (s:state) : bool :=
  match s with
  | Ninit Nis'20 => true
  | _ => false
  end.
Extract Inlined Constant state_set_18 => "assert false".

Definition state_set_19 (s:state) : bool :=
  match s with
  | Ninit Nis'23 => true
  | _ => false
  end.
Extract Inlined Constant state_set_19 => "assert false".

Definition state_set_20 (s:state) : bool :=
  match s with
  | Ninit Nis'24 => true
  | _ => false
  end.
Extract Inlined Constant state_set_20 => "assert false".

Definition state_set_21 (s:state) : bool :=
  match s with
  | Ninit Nis'26 => true
  | _ => false
  end.
Extract Inlined Constant state_set_21 => "assert false".

Definition state_set_22 (s:state) : bool :=
  match s with
  | Ninit Nis'27 => true
  | _ => false
  end.
Extract Inlined Constant state_set_22 => "assert false".

Definition state_set_23 (s:state) : bool :=
  match s with
  | Ninit Nis'29 => true
  | _ => false
  end.
Extract Inlined Constant state_set_23 => "assert false".

Definition state_set_24 (s:state) : bool :=
  match s with
  | Ninit Nis'30 => true
  | _ => false
  end.
Extract Inlined Constant state_set_24 => "assert false".

Definition state_set_25 (s:state) : bool :=
  match s with
  | Ninit Nis'32 => true
  | _ => false
  end.
Extract Inlined Constant state_set_25 => "assert false".

Definition state_set_26 (s:state) : bool :=
  match s with
  | Ninit Nis'28 => true
  | _ => false
  end.
Extract Inlined Constant state_set_26 => "assert false".

Definition state_set_27 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'19 | Ninit Nis'25 | Ninit Nis'28 | Ninit Nis'35 | Ninit Nis'39 | Ninit Nis'41 => true
  | _ => false
  end.
Extract Inlined Constant state_set_27 => "assert false".

Definition state_set_28 (s:state) : bool :=
  match s with
  | Ninit Nis'34 | Ninit Nis'36 | Ninit Nis'40 | Ninit Nis'42 | Ninit Nis'43 | Ninit Nis'44 | Ninit Nis'48 => true
  | _ => false
  end.
Extract Inlined Constant state_set_28 => "assert false".

Definition state_set_29 (s:state) : bool :=
  match s with
  | Ninit Nis'35 => true
  | _ => false
  end.
Extract Inlined Constant state_set_29 => "assert false".

Definition state_set_30 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'19 | Ninit Nis'25 | Ninit Nis'28 | Ninit Nis'35 | Ninit Nis'37 | Ninit Nis'39 | Ninit Nis'41 => true
  | _ => false
  end.
Extract Inlined Constant state_set_30 => "assert false".

Definition state_set_31 (s:state) : bool :=
  match s with
  | Ninit Nis'34 | Ninit Nis'36 | Ninit Nis'38 | Ninit Nis'40 | Ninit Nis'42 | Ninit Nis'43 | Ninit Nis'44 | Ninit Nis'48 => true
  | _ => false
  end.
Extract Inlined Constant state_set_31 => "assert false".

Definition state_set_32 (s:state) : bool :=
  match s with
  | Ninit Nis'37 => true
  | _ => false
  end.
Extract Inlined Constant state_set_32 => "assert false".

Definition state_set_33 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'19 | Ninit Nis'25 | Ninit Nis'28 | Ninit Nis'39 => true
  | _ => false
  end.
Extract Inlined Constant state_set_33 => "assert false".

Definition state_set_34 (s:state) : bool :=
  match s with
  | Ninit Nis'34 | Ninit Nis'40 | Ninit Nis'43 | Ninit Nis'44 | Ninit Nis'48 => true
  | _ => false
  end.
Extract Inlined Constant state_set_34 => "assert false".

Definition state_set_35 (s:state) : bool :=
  match s with
  | Ninit Nis'39 => true
  | _ => false
  end.
Extract Inlined Constant state_set_35 => "assert false".

Definition state_set_36 (s:state) : bool :=
  match s with
  | Ninit Nis'41 => true
  | _ => false
  end.
Extract Inlined Constant state_set_36 => "assert false".

Definition state_set_37 (s:state) : bool :=
  match s with
  | Ninit Nis'25 => true
  | _ => false
  end.
Extract Inlined Constant state_set_37 => "assert false".

Definition state_set_38 (s:state) : bool :=
  match s with
  | Ninit Nis'19 => true
  | _ => false
  end.
Extract Inlined Constant state_set_38 => "assert false".

Definition state_set_39 (s:state) : bool :=
  match s with
  | Ninit Nis'44 => true
  | _ => false
  end.
Extract Inlined Constant state_set_39 => "assert false".

Definition state_set_40 (s:state) : bool :=
  match s with
  | Ninit Nis'2 => true
  | _ => false
  end.
Extract Inlined Constant state_set_40 => "assert false".

Definition state_set_41 (s:state) : bool :=
  match s with
  | Init Init'0 => true
  | _ => false
  end.
Extract Inlined Constant state_set_41 => "assert false".

Definition state_set_42 (s:state) : bool :=
  match s with
  | Ninit Nis'48 => true
  | _ => false
  end.
Extract Inlined Constant state_set_42 => "assert false".

Definition state_set_43 (s:state) : bool :=
  match s with
  | Init Init'50 => true
  | _ => false
  end.
Extract Inlined Constant state_set_43 => "assert false".

Definition state_set_44 (s:state) : bool :=
  match s with
  | Ninit Nis'52 => true
  | _ => false
  end.
Extract Inlined Constant state_set_44 => "assert false".

Definition past_state_of_non_init_state (s:noninitstate) : list (state -> bool) :=
  match s with
  | Nis'1 => [ state_set_1 ]
  | Nis'2 => [ state_set_1 ]
  | Nis'3 => [ state_set_2 ]
  | Nis'4 => [ state_set_2 ]
  | Nis'5 => [ state_set_3 ]
  | Nis'6 => [ state_set_4 ]
  | Nis'7 => [ state_set_5 ]
  | Nis'8 => [ state_set_5 ]
  | Nis'9 => [ state_set_7; state_set_6 ]
  | Nis'10 => [ state_set_8; state_set_7; state_set_6 ]
  | Nis'11 => [ state_set_10; state_set_9 ]
  | Nis'12 => [ state_set_11; state_set_10; state_set_9 ]
  | Nis'13 => [ state_set_12; state_set_5 ]
  | Nis'14 => [ state_set_13; state_set_12; state_set_5 ]
  | Nis'15 => [ state_set_14; state_set_4 ]
  | Nis'16 => [ state_set_15; state_set_3 ]
  | Nis'17 => [ state_set_16; state_set_2 ]
  | Nis'18 => [ state_set_17; state_set_16; state_set_2 ]
  | Nis'19 => [ state_set_1 ]
  | Nis'20 => [ state_set_1 ]
  | Nis'21 => [ state_set_18; state_set_1 ]
  | Nis'22 => [ state_set_1 ]
  | Nis'23 => [ state_set_1 ]
  | Nis'24 => [ state_set_19; state_set_1 ]
  | Nis'25 => [ state_set_20; state_set_19; state_set_1 ]
  | Nis'26 => [ state_set_1 ]
  | Nis'27 => [ state_set_21; state_set_1 ]
  | Nis'28 => [ state_set_22; state_set_21; state_set_1 ]
  | Nis'29 => [ state_set_1 ]
  | Nis'30 => [ state_set_23; state_set_1 ]
  | Nis'31 => [ state_set_24; state_set_23; state_set_1 ]
  | Nis'32 => [ state_set_23; state_set_1 ]
  | Nis'33 => [ state_set_25; state_set_23; state_set_1 ]
  | Nis'34 => [ state_set_26; state_set_22; state_set_21; state_set_1 ]
  | Nis'35 => [ state_set_28; state_set_27 ]
  | Nis'36 => [ state_set_29; state_set_28; state_set_27 ]
  | Nis'37 => [ state_set_31; state_set_30 ]
  | Nis'38 => [ state_set_32; state_set_31; state_set_30 ]
  | Nis'39 => [ state_set_34; state_set_33 ]
  | Nis'40 => [ state_set_35; state_set_34; state_set_33 ]
  | Nis'41 => [ state_set_34; state_set_33 ]
  | Nis'42 => [ state_set_36; state_set_34; state_set_33 ]
  | Nis'43 => [ state_set_37; state_set_20; state_set_19; state_set_1 ]
  | Nis'44 => [ state_set_38; state_set_1 ]
  | Nis'45 => [ state_set_39; state_set_38; state_set_1 ]
  | Nis'46 => [ state_set_40; state_set_1 ]
  | Nis'48 => [ state_set_41 ]
  | Nis'49 => [ state_set_42; state_set_41 ]
  | Nis'52 => [ state_set_43 ]
  | Nis'53 => [ state_set_44; state_set_43 ]
  end.
Extract Constant past_state_of_non_init_state => "fun _ -> assert false".

Definition lookahead_set_1 : list terminal :=
  [OR't; IMPL't; IFF't; EOF't; AND't].
Extract Inlined Constant lookahead_set_1 => "assert false".

Definition lookahead_set_2 : list terminal :=
  [PLUS't; MULT't; IN't; EQ't].
Extract Inlined Constant lookahead_set_2 => "assert false".

Definition lookahead_set_3 : list terminal :=
  [TRUE't; RPAREN't; RCURL't; PLUS't; OR't; NOT't; MULT't; LPAREN't; LCURL't; INT't; IN't; IMPL't; IFF't; ID't; FALSE't; EX't; EQ't; EOF't; COMMA't; AND't; ALL't].
Extract Inlined Constant lookahead_set_3 => "assert false".

Definition lookahead_set_4 : list terminal :=
  [RCURL't; OR't; IMPL't; IFF't; EOF't; AND't].
Extract Inlined Constant lookahead_set_4 => "assert false".

Definition lookahead_set_5 : list terminal :=
  [RPAREN't; PLUS't; MULT't].
Extract Inlined Constant lookahead_set_5 => "assert false".

Definition lookahead_set_6 : list terminal :=
  [RPAREN't; RCURL't; PLUS't; OR't; MULT't; IN't; IMPL't; IFF't; EQ't; EOF't; COMMA't; AND't].
Extract Inlined Constant lookahead_set_6 => "assert false".

Definition lookahead_set_7 : list terminal :=
  [PLUS't; MULT't; COMMA't].
Extract Inlined Constant lookahead_set_7 => "assert false".

Definition lookahead_set_8 : list terminal :=
  [RCURL't; OR't; IMPL't; IFF't; AND't].
Extract Inlined Constant lookahead_set_8 => "assert false".

Definition lookahead_set_9 : list terminal :=
  [RCURL't; PLUS't; OR't; MULT't; IN't; IMPL't; IFF't; EQ't; EOF't; AND't].
Extract Inlined Constant lookahead_set_9 => "assert false".

Definition lookahead_set_10 : list terminal :=
  [RCURL't; PLUS't; OR't; MULT't; IMPL't; IFF't; EOF't; AND't].
Extract Inlined Constant lookahead_set_10 => "assert false".

Definition lookahead_set_11 : list terminal :=
  [PLUS't; MULT't; EOF't].
Extract Inlined Constant lookahead_set_11 => "assert false".

Definition items_of_state_0 : list item :=
  [ {| prod_item := Prod'p_form'0; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'1; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'2; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'3; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'7; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'8; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'9; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'10; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'11; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'12; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'13; dot_pos_item := 0; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'parse_formula'0; dot_pos_item := 0; lookaheads_item := lookahead_set_3 |} ].
Extract Inlined Constant items_of_state_0 => "assert false".

Definition items_of_state_1 : list item :=
  [ {| prod_item := Prod'p_form'0; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ].
Extract Inlined Constant items_of_state_1 => "assert false".

Definition items_of_state_2 : list item :=
  [ {| prod_item := Prod'p_form'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'2; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'2; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'3; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'7; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'8; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'9; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'10; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'11; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'12; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'13; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |} ].
Extract Inlined Constant items_of_state_2 => "assert false".

Definition items_of_state_3 : list item :=
  [ {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |} ].
Extract Inlined Constant items_of_state_3 => "assert false".

Definition items_of_state_4 : list item :=
  [ {| prod_item := Prod'p_term'4; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |} ].
Extract Inlined Constant items_of_state_4 => "assert false".

Definition items_of_state_5 : list item :=
  [ {| prod_item := Prod'p_term'0; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_termlist'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |} ].
Extract Inlined Constant items_of_state_5 => "assert false".

Definition items_of_state_6 : list item :=
  [ {| prod_item := Prod'inner'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'inner'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'p_termlist'0; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |} ].
Extract Inlined Constant items_of_state_6 => "assert false".

Definition items_of_state_7 : list item :=
  [ {| prod_item := Prod'inner'0; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |} ].
Extract Inlined Constant items_of_state_7 => "assert false".

Definition items_of_state_8 : list item :=
  [ {| prod_item := Prod'inner'1; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 1; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 1; lookaheads_item := lookahead_set_7 |} ].
Extract Inlined Constant items_of_state_8 => "assert false".

Definition items_of_state_9 : list item :=
  [ {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |} ].
Extract Inlined Constant items_of_state_9 => "assert false".

Definition items_of_state_10 : list item :=
  [ {| prod_item := Prod'p_term'2; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |} ].
Extract Inlined Constant items_of_state_10 => "assert false".

Definition items_of_state_11 : list item :=
  [ {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |} ].
Extract Inlined Constant items_of_state_11 => "assert false".

Definition items_of_state_12 : list item :=
  [ {| prod_item := Prod'p_term'2; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 1; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |} ].
Extract Inlined Constant items_of_state_12 => "assert false".

Definition items_of_state_13 : list item :=
  [ {| prod_item := Prod'inner'0; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'inner'1; dot_pos_item := 0; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'inner'1; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |};
    {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_7 |} ].
Extract Inlined Constant items_of_state_13 => "assert false".

Definition items_of_state_14 : list item :=
  [ {| prod_item := Prod'inner'1; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |} ].
Extract Inlined Constant items_of_state_14 => "assert false".

Definition items_of_state_15 : list item :=
  [ {| prod_item := Prod'p_termlist'0; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |} ].
Extract Inlined Constant items_of_state_15 => "assert false".

Definition items_of_state_16 : list item :=
  [ {| prod_item := Prod'p_term'1; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |} ].
Extract Inlined Constant items_of_state_16 => "assert false".

Definition items_of_state_17 : list item :=
  [ {| prod_item := Prod'p_term'2; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 1; lookaheads_item := lookahead_set_5 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 2; lookaheads_item := lookahead_set_6 |} ].
Extract Inlined Constant items_of_state_17 => "assert false".

Definition items_of_state_18 : list item :=
  [ {| prod_item := Prod'p_term'5; dot_pos_item := 3; lookaheads_item := lookahead_set_6 |} ].
Extract Inlined Constant items_of_state_18 => "assert false".

Definition items_of_state_19 : list item :=
  [ {| prod_item := Prod'p_form'0; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'1; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'2; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'3; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'7; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'8; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'9; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'10; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'11; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'12; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'13; dot_pos_item := 0; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'13; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |} ].
Extract Inlined Constant items_of_state_19 => "assert false".

Definition items_of_state_20 : list item :=
  [ {| prod_item := Prod'p_form'7; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'8; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_term'0; dot_pos_item := 1; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 1; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_termlist'0; dot_pos_item := 0; lookaheads_item := lookahead_set_9 |} ].
Extract Inlined Constant items_of_state_20 => "assert false".

Definition items_of_state_21 : list item :=
  [ {| prod_item := Prod'p_form'8; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 2; lookaheads_item := lookahead_set_2 |} ].
Extract Inlined Constant items_of_state_21 => "assert false".

Definition items_of_state_22 : list item :=
  [ {| prod_item := Prod'p_form'1; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ].
Extract Inlined Constant items_of_state_22 => "assert false".

Definition items_of_state_23 : list item :=
  [ {| prod_item := Prod'p_form'12; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ].
Extract Inlined Constant items_of_state_23 => "assert false".

Definition items_of_state_24 : list item :=
  [ {| prod_item := Prod'p_form'12; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |} ].
Extract Inlined Constant items_of_state_24 => "assert false".

Definition items_of_state_25 : list item :=
  [ {| prod_item := Prod'p_form'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'2; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'3; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'7; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'8; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'9; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'10; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'11; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'12; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'12; dot_pos_item := 3; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'13; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |} ].
Extract Inlined Constant items_of_state_25 => "assert false".

Definition items_of_state_26 : list item :=
  [ {| prod_item := Prod'p_form'11; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ].
Extract Inlined Constant items_of_state_26 => "assert false".

Definition items_of_state_27 : list item :=
  [ {| prod_item := Prod'p_form'11; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |} ].
Extract Inlined Constant items_of_state_27 => "assert false".

Definition items_of_state_28 : list item :=
  [ {| prod_item := Prod'p_form'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'2; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'3; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'7; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'8; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'9; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'10; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'11; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'11; dot_pos_item := 3; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'12; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'13; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |} ].
Extract Inlined Constant items_of_state_28 => "assert false".

Definition items_of_state_29 : list item :=
  [ {| prod_item := Prod'p_form'9; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'10; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 1; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 1; lookaheads_item := lookahead_set_2 |} ].
Extract Inlined Constant items_of_state_29 => "assert false".

Definition items_of_state_30 : list item :=
  [ {| prod_item := Prod'p_form'10; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |} ].
Extract Inlined Constant items_of_state_30 => "assert false".

Definition items_of_state_31 : list item :=
  [ {| prod_item := Prod'p_form'10; dot_pos_item := 3; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 1; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 1; lookaheads_item := lookahead_set_10 |} ].
Extract Inlined Constant items_of_state_31 => "assert false".

Definition items_of_state_32 : list item :=
  [ {| prod_item := Prod'p_form'9; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_10 |} ].
Extract Inlined Constant items_of_state_32 => "assert false".

Definition items_of_state_33 : list item :=
  [ {| prod_item := Prod'p_form'9; dot_pos_item := 3; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 1; lookaheads_item := lookahead_set_10 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 1; lookaheads_item := lookahead_set_10 |} ].
Extract Inlined Constant items_of_state_33 => "assert false".

Definition items_of_state_34 : list item :=
  [ {| prod_item := Prod'p_form'3; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'11; dot_pos_item := 4; lookaheads_item := lookahead_set_4 |} ].
Extract Inlined Constant items_of_state_34 => "assert false".

Definition items_of_state_35 : list item :=
  [ {| prod_item := Prod'p_form'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'2; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'3; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'7; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'8; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'9; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'10; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'11; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'12; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'13; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |} ].
Extract Inlined Constant items_of_state_35 => "assert false".

Definition items_of_state_36 : list item :=
  [ {| prod_item := Prod'p_form'3; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 3; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ].
Extract Inlined Constant items_of_state_36 => "assert false".

Definition items_of_state_37 : list item :=
  [ {| prod_item := Prod'p_form'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'2; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'3; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'3; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'7; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'8; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'9; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'10; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'11; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'12; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'13; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |} ].
Extract Inlined Constant items_of_state_37 => "assert false".

Definition items_of_state_38 : list item :=
  [ {| prod_item := Prod'p_form'3; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'3; dot_pos_item := 3; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ].
Extract Inlined Constant items_of_state_38 => "assert false".

Definition items_of_state_39 : list item :=
  [ {| prod_item := Prod'p_form'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'2; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'3; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'7; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'8; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'9; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'10; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'11; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'12; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'13; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |} ].
Extract Inlined Constant items_of_state_39 => "assert false".

Definition items_of_state_40 : list item :=
  [ {| prod_item := Prod'p_form'3; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 3; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ].
Extract Inlined Constant items_of_state_40 => "assert false".

Definition items_of_state_41 : list item :=
  [ {| prod_item := Prod'p_form'0; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'1; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'2; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'3; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'7; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'8; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'9; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'10; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'11; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'12; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'13; dot_pos_item := 0; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_2 |} ].
Extract Inlined Constant items_of_state_41 => "assert false".

Definition items_of_state_42 : list item :=
  [ {| prod_item := Prod'p_form'3; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 3; lookaheads_item := lookahead_set_4 |} ].
Extract Inlined Constant items_of_state_42 => "assert false".

Definition items_of_state_43 : list item :=
  [ {| prod_item := Prod'p_form'3; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'12; dot_pos_item := 4; lookaheads_item := lookahead_set_4 |} ].
Extract Inlined Constant items_of_state_43 => "assert false".

Definition items_of_state_44 : list item :=
  [ {| prod_item := Prod'p_form'3; dot_pos_item := 1; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 1; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 1; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 1; lookaheads_item := lookahead_set_8 |};
    {| prod_item := Prod'p_form'13; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |} ].
Extract Inlined Constant items_of_state_44 => "assert false".

Definition items_of_state_45 : list item :=
  [ {| prod_item := Prod'p_form'13; dot_pos_item := 3; lookaheads_item := lookahead_set_4 |} ].
Extract Inlined Constant items_of_state_45 => "assert false".

Definition items_of_state_46 : list item :=
  [ {| prod_item := Prod'p_form'2; dot_pos_item := 2; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'3; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 1; lookaheads_item := lookahead_set_4 |} ].
Extract Inlined Constant items_of_state_46 => "assert false".

Definition items_of_state_48 : list item :=
  [ {| prod_item := Prod'p_form'3; dot_pos_item := 1; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'4; dot_pos_item := 1; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'5; dot_pos_item := 1; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'p_form'6; dot_pos_item := 1; lookaheads_item := lookahead_set_1 |};
    {| prod_item := Prod'parse_formula'0; dot_pos_item := 1; lookaheads_item := lookahead_set_3 |} ].
Extract Inlined Constant items_of_state_48 => "assert false".

Definition items_of_state_49 : list item :=
  [ {| prod_item := Prod'parse_formula'0; dot_pos_item := 2; lookaheads_item := lookahead_set_3 |} ].
Extract Inlined Constant items_of_state_49 => "assert false".

Definition items_of_state_50 : list item :=
  [ {| prod_item := Prod'p_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'p_term'1; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'p_term'2; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'p_term'4; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'p_term'5; dot_pos_item := 0; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'parse_term'0; dot_pos_item := 0; lookaheads_item := lookahead_set_3 |} ].
Extract Inlined Constant items_of_state_50 => "assert false".

Definition items_of_state_52 : list item :=
  [ {| prod_item := Prod'p_term'2; dot_pos_item := 1; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'p_term'3; dot_pos_item := 1; lookaheads_item := lookahead_set_11 |};
    {| prod_item := Prod'parse_term'0; dot_pos_item := 1; lookaheads_item := lookahead_set_3 |} ].
Extract Inlined Constant items_of_state_52 => "assert false".

Definition items_of_state_53 : list item :=
  [ {| prod_item := Prod'parse_term'0; dot_pos_item := 2; lookaheads_item := lookahead_set_3 |} ].
Extract Inlined Constant items_of_state_53 => "assert false".

Definition items_of_state (s:state) : list item :=
  match s with
  | Init Init'0 => items_of_state_0
  | Ninit Nis'1 => items_of_state_1
  | Ninit Nis'2 => items_of_state_2
  | Ninit Nis'3 => items_of_state_3
  | Ninit Nis'4 => items_of_state_4
  | Ninit Nis'5 => items_of_state_5
  | Ninit Nis'6 => items_of_state_6
  | Ninit Nis'7 => items_of_state_7
  | Ninit Nis'8 => items_of_state_8
  | Ninit Nis'9 => items_of_state_9
  | Ninit Nis'10 => items_of_state_10
  | Ninit Nis'11 => items_of_state_11
  | Ninit Nis'12 => items_of_state_12
  | Ninit Nis'13 => items_of_state_13
  | Ninit Nis'14 => items_of_state_14
  | Ninit Nis'15 => items_of_state_15
  | Ninit Nis'16 => items_of_state_16
  | Ninit Nis'17 => items_of_state_17
  | Ninit Nis'18 => items_of_state_18
  | Ninit Nis'19 => items_of_state_19
  | Ninit Nis'20 => items_of_state_20
  | Ninit Nis'21 => items_of_state_21
  | Ninit Nis'22 => items_of_state_22
  | Ninit Nis'23 => items_of_state_23
  | Ninit Nis'24 => items_of_state_24
  | Ninit Nis'25 => items_of_state_25
  | Ninit Nis'26 => items_of_state_26
  | Ninit Nis'27 => items_of_state_27
  | Ninit Nis'28 => items_of_state_28
  | Ninit Nis'29 => items_of_state_29
  | Ninit Nis'30 => items_of_state_30
  | Ninit Nis'31 => items_of_state_31
  | Ninit Nis'32 => items_of_state_32
  | Ninit Nis'33 => items_of_state_33
  | Ninit Nis'34 => items_of_state_34
  | Ninit Nis'35 => items_of_state_35
  | Ninit Nis'36 => items_of_state_36
  | Ninit Nis'37 => items_of_state_37
  | Ninit Nis'38 => items_of_state_38
  | Ninit Nis'39 => items_of_state_39
  | Ninit Nis'40 => items_of_state_40
  | Ninit Nis'41 => items_of_state_41
  | Ninit Nis'42 => items_of_state_42
  | Ninit Nis'43 => items_of_state_43
  | Ninit Nis'44 => items_of_state_44
  | Ninit Nis'45 => items_of_state_45
  | Ninit Nis'46 => items_of_state_46
  | Ninit Nis'48 => items_of_state_48
  | Ninit Nis'49 => items_of_state_49
  | Init Init'50 => items_of_state_50
  | Ninit Nis'52 => items_of_state_52
  | Ninit Nis'53 => items_of_state_53
  end.
Extract Constant items_of_state => "fun _ -> assert false".

End Aut.

Require Import Main.

Module Parser := Main.Make Aut.
Theorem safe:
  Parser.safe_validator () = true.
Proof eq_refl true<:Parser.safe_validator () = true.

Theorem complete:
  Parser.complete_validator () = true.
Proof eq_refl true<:Parser.complete_validator () = true.

Definition parse_formula := Parser.parse safe Aut.Init'0.

Theorem parse_formula_correct iterator buffer:
  match parse_formula iterator buffer with
  | Parser.Inter.Parsed_pr sem buffer_new =>
    exists word,
      buffer = Parser.Inter.app_str word buffer_new /\
      inhabited (Gram.parse_tree (NT parse_formula'nt) word sem)
  | _ => True
  end.
Proof. apply Parser.parse_correct. Qed.

Theorem parse_formula_complete (iterator:nat) word buffer_end (output:      (formula)):
  forall tree:Gram.parse_tree (NT parse_formula'nt) word output,
  match parse_formula iterator (Parser.Inter.app_str word buffer_end) with
  | Parser.Inter.Fail_pr => False
  | Parser.Inter.Parsed_pr output_res buffer_end_res =>
    output_res = output /\ buffer_end_res = buffer_end  /\
    le (Gram.pt_size tree) iterator
  | Parser.Inter.Timeout_pr => lt iterator (Gram.pt_size tree)
  end.
Proof. apply Parser.parse_complete with (init:=Aut.Init'0); exact complete. Qed.

Definition parse_term := Parser.parse safe Aut.Init'50.

Theorem parse_term_correct iterator buffer:
  match parse_term iterator buffer with
  | Parser.Inter.Parsed_pr sem buffer_new =>
    exists word,
      buffer = Parser.Inter.app_str word buffer_new /\
      inhabited (Gram.parse_tree (NT parse_term'nt) word sem)
  | _ => True
  end.
Proof. apply Parser.parse_correct. Qed.

Theorem parse_term_complete (iterator:nat) word buffer_end (output:      (term)):
  forall tree:Gram.parse_tree (NT parse_term'nt) word output,
  match parse_term iterator (Parser.Inter.app_str word buffer_end) with
  | Parser.Inter.Fail_pr => False
  | Parser.Inter.Parsed_pr output_res buffer_end_res =>
    output_res = output /\ buffer_end_res = buffer_end  /\
    le (Gram.pt_size tree) iterator
  | Parser.Inter.Timeout_pr => lt iterator (Gram.pt_size tree)
  end.
Proof. apply Parser.parse_complete with (init:=Aut.Init'50); exact complete. Qed.
