%{
  module Concrete = Smt2d.Concrete
%}

%token EOF

%token OPEN CLOSE
%token <string> NUMERAL DECIMAL HEXADECIMAL BINARY STRING SYMBOL OTHER_KEYWORD

%token UNDERSCORE

%token AS

%token LET FORALL EXISTS ATTRIBUTE

%token CLAUSES CONCLUSION
       
%start step
%type <Proof.prestep> step
			      
%%

numeral_plus:
  | NUMERAL                 { [$1] }
  | NUMERAL numeral_plus    { $1 :: $2 }
;

symbol_plus:
  | SYMBOL                { [$1] }
  | SYMBOL symbol_plus    { $1 :: $2 }
;

keyword:
  | CLAUSES          { ":clauses" }
  | CONCLUSION       { ":conclusion" }
  | OTHER_KEYWORD    { $1 }
;

spec_constant:
  | NUMERAL        { Concrete.Numeral $1 }
  | DECIMAL        { Concrete.Decimal $1 }
  | HEXADECIMAL    { Concrete.Hexadecimal $1 }
  | BINARY         { Concrete.Binary $1 }
  | STRING         { Concrete.String $1 }
;

s_expr:
  | spec_constant             { Concrete.Spec_constant_expr $1 }
  | SYMBOL                    { Concrete.Symbol_expr $1 }
  | keyword                   { Concrete.Keyword_expr $1 }
  | OPEN s_expr_star CLOSE    { Concrete.List_expr $2 }
;

s_expr_star:
  |                       { [] }
  | s_expr s_expr_star    { $1 :: $2 }
;

identifier:
  | SYMBOL                                       { ($1,[]) }
  | OPEN UNDERSCORE SYMBOL numeral_plus CLOSE    { ($3,$4) }
;

sort:
  | identifier                         { Concrete.Sort ($1,[]) }
  | OPEN identifier sort_plus CLOSE    { Concrete.Sort ($2,$3) }
;

sort_plus:
  | sort              { [$1] }
  | sort sort_plus    { $1 :: $2 }
;

attribute_value:
  | spec_constant             { Concrete.Spec_constant_value $1 }
  | SYMBOL                    { Concrete.Symbol_value $1 }
  | OPEN s_expr_star CLOSE    { Concrete.S_expr_list_value $2 }
;

attribute:
  | keyword                    { ($1,None) }
  | keyword attribute_value    { ($1,Some $2) }
;

attribute_plus:
  | attribute                   { [$1] }
  | attribute attribute_plus    { $1 :: $2 }
;

qual_identifier:
  | identifier                       { ($1,None) }
  | OPEN AS identifier sort CLOSE    { ($3,Some $4) }
;

var_binding:
  | OPEN SYMBOL term CLOSE    { ($2,$3) }
;

var_binding_plus:
  | var_binding                     { [$1] }
  | var_binding var_binding_plus    { $1 :: $2 }
;

sorted_var:
  | OPEN SYMBOL sort CLOSE    { ($2,$3) }
;

sorted_var_plus:
  | sorted_var                    { [$1] }
  | sorted_var sorted_var_plus    { $1 :: $2 }
;

term:
  | spec_constant                                        { Concrete.Spec_constant_term $1 }
  | qual_identifier                                      { Concrete.Qual_identifier_term $1 }
  | OPEN qual_identifier term_plus CLOSE                 { Concrete.App_term ($2,$3) }
  | OPEN LET OPEN var_binding_plus CLOSE term CLOSE      { Concrete.Let_term ($4,$6) }
  | OPEN FORALL OPEN sorted_var_plus CLOSE term CLOSE    { Concrete.Forall_term ($4,$6) }
  | OPEN EXISTS OPEN sorted_var_plus CLOSE term CLOSE    { Concrete.Exists_term ($4,$6) }
  | OPEN ATTRIBUTE term attribute_plus CLOSE             { Concrete.Attributed_term ($3,$4) }
;

term_star:
  |                   { [] }
  | term term_star    { $1 :: $2 }
;

term_plus:
  | term              { [$1] }
  | term term_plus    { $1 :: $2 }
;

clauses:
  |                                   { [] }
  | CLAUSES OPEN symbol_plus CLOSE    { $3 }
;    

conclusion:
  | CONCLUSION OPEN term_star CLOSE    { $3 } 
;

step:
  | OPEN SYMBOL SYMBOL OPEN SYMBOL clauses conclusion CLOSE CLOSE
	 { { Proof.id = $3;
	     Proof.rule = $5;
	     Proof.clauses = $6;
	     Proof.conclusion = $7; } }
  | EOF    { raise End_of_file }
;

%%
