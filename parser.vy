%token TRUE FALSE AND OR IFF IMPL ALL EX NOT LPAREN RPAREN LCURL RCURL COMMA
%token EQ IN PLUS MULT EOF
%token<int> INT
%token<string> ID

%right COMMA (* pour les quantificateurs *)
%right IMPL
%nonassoc IFF
%right OR
%right AND
%left PLUS
%left MULT
%nonassoc NOT

%start<formula> parse_formula
%start<term> parse_term
%type<list term> p_termlist
%type<term> p_term
%type<formula> p_form
%type<list term> inner

%%

parse_formula : p_form EOF    { $1 }

parse_term : p_term EOF       { $1 }

p_form :
  TRUE                        { True }
| FALSE                       { False }
| NOT p_form                  { Not($2) }
| p_form AND p_form           { Op(And,$1,$3) }
| p_form OR p_form            { Op(Or,$1,$3) }
| p_form IMPL p_form          { Op(Impl,$1,$3) }
| p_form IFF p_form           { iff $1 $3 }
| ID                          { Pred($1,[]) }
| ID p_termlist               { Pred($1,$2) }
| p_term EQ p_term            { Pred("=",[$1;$3]) }
| p_term IN p_term            { Pred("∈",[$1;$3]) }
| ALL ID COMMA p_form         { Quant(All,$2,$4) }
| EX ID COMMA p_form          { Quant(Ex,$2,$4) }
| LCURL p_form RCURL          { $2 }

p_term :
  ID                          { Var $1 }
| ID p_termlist               { Fun ($1,$2) }
| p_term PLUS p_term          { Fun ("+",[$1;$3]) }
| p_term MULT p_term          { Fun ("*",[$1;$3]) }
| INT                         { int2term $1 }
| LPAREN p_term RPAREN        { $2 }

p_termlist :
 LPAREN inner                 { $2 }

inner :
  RPAREN                       { [] }
| p_term COMMA inner           { $1 :: $3 }
