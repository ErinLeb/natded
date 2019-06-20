
Require Import Ascii String AsciiOrder StringOrder.
Require Import parser.
Import MenhirLibParser.Inter.
Open Scope string_scope.
Open Scope bool_scope.

(** No such thing as an empty buffer, instead we use
    an infinite stream of EOF *)

CoFixpoint TheEnd : buffer := Buf_cons (EOF tt) TheEnd.

Fixpoint ntail n s :=
  match n, s with
  | 0, _ => s
  | _, "" => s
  | S n, String _ s => ntail n s
  end.

Definition is_digit c := (("0" <=? c) && (c <=? "9"))%char.

Definition is_alpha c :=
  ((("a" <=? c) && (c <=? "z")) ||
   (("A" <=? c) && (c <=? "Z")) ||
   (c =? "_"))%char.

Fixpoint identsize s :=
  match s with
  | "" => 0
  | String c s =>
    if is_alpha c || is_digit c then S (identsize s)
    else 0
  end.

Fixpoint readnum acc s :=
  match s with
  | String "0" s => readnum (acc*10) s
  | String "1" s => readnum (acc*10+1) s
  | String "2" s => readnum (acc*10+2) s
  | String "3" s => readnum (acc*10+3) s
  | String "4" s => readnum (acc*10+4) s
  | String "5" s => readnum (acc*10+5) s
  | String "6" s => readnum (acc*10+6) s
  | String "7" s => readnum (acc*10+7) s
  | String "8" s => readnum (acc*10+8) s
  | String "9" s => readnum (acc*10+9) s
  | _ => (acc,s)
  end.

Definition chartoken c :=
  match c with
  | "(" => Some LPAREN
  | ")" => Some RPAREN
  | "{" => Some LCURL
  | "}" => Some RCURL
  | "," => Some COMMA
  | "=" => Some EQ
  | "+" => Some PLUS
  | "*" => Some MULT
  | "~" => Some NOT
  | _ => None
  end%char.

Fixpoint lex_string_cpt n s :=
  match n with
  | 0 => None
  | S n =>
    match s with
    | "" => Some TheEnd
    | String " " s => lex_string_cpt n s
    | String "010" s => lex_string_cpt n s
    | String "013" s => lex_string_cpt n s
    | String c _ =>
      match chartoken c with
      | Some tok => option_map (Buf_cons (tok tt)) (lex_string_cpt n (ntail 1 s))
      | None =>
        if is_digit c then
          let (m,s) := readnum 0 s in
          option_map (Buf_cons (INT m)) (lex_string_cpt n s)
        else if is_alpha c then
          let k := identsize s in
          let id := substring 0 k s in
          let s := ntail k s in
          if id =? "True" then
            option_map (Buf_cons (TRUE tt)) (lex_string_cpt n s)
          else if id =? "False" then
            option_map (Buf_cons (FALSE tt)) (lex_string_cpt n s)
          else option_map (Buf_cons (ID id)) (lex_string_cpt n s)
        else if prefix "/\" s then
          option_map (Buf_cons (AND tt)) (lex_string_cpt n (ntail 2 s))
        else if prefix "\/" s then
          option_map (Buf_cons (OR tt)) (lex_string_cpt n (ntail 2 s))
        else if prefix "->" s then
          option_map (Buf_cons (IMPL tt)) (lex_string_cpt n (ntail 2 s))
        else if prefix "<->" s then
          option_map (Buf_cons (IFF tt)) (lex_string_cpt n (ntail 3 s))
        else if prefix "∀" s then
          option_map (Buf_cons (ALL tt)) (lex_string_cpt n (ntail (length "∀") s))
        else if prefix "∃" s then
          option_map (Buf_cons (EX tt)) (lex_string_cpt n (ntail (length "∃") s))
        else if prefix "∈" s then
          option_map (Buf_cons (IN tt)) (lex_string_cpt n (ntail (length "∈") s))
        else None
      end
    end
  end.

Definition lex_string s := lex_string_cpt (length s) s.

Definition string2formula s :=
  match option_map (parse_formula 50) (lex_string s) with
  | Some (Parsed_pr f _) => Some f
  | _ => None
  end.

Compute string2formula "∀x,A->A".
