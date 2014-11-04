%{
  open Parsetree
%}
  
%token OPEN
%token CLOSE
%token LET
%token FORALL
%token EXISTS
%token BANG

%token TRUE
%token FALSE
%token NOT
%token IMPLY
%token AND
%token OR
%token XOR
%token EQ
%token DISTINCT
%token ITE

%token SET
%token <string> STEP

%token INPUT
%token EQ_REFL
%token EQ_TRANS
%token EQ_CONGR
%token RESOLUTION

%token CONCLUSION
%token CLAUSES

%token <string> SYM

%token EOF

%start step
%type <Parsetree.line> step
  
%%

step :
 | OPEN SET STEP OPEN rule clauses conclusion CLOSE CLOSE { Line ($3, $5, $6, $7) }
 | EOF { raise Global.EndOfFile }
;

rule :
 | INPUT { Global.Input }
 | EQ_REFL { Global.Eq_reflexive }
 | EQ_TRANS { Global.Eq_transitive }
 | EQ_CONGR { Global.Eq_congruent }
 | RESOLUTION { Global.Resolution }
 | SYM { Global.Anonrule ($1) }
 | AND { Global.Anonrule ("and") }
 | OR { Global.Anonrule ("or") }

clauses :
 | { [] }
 | CLAUSES OPEN stepids CLOSE { $3 }

conclusion :
 | CONCLUSION OPEN smtterms CLOSE { $3 }

smtterms :
 | { [] }
 | smtterm smtterms { $1 :: $2 }

smtterm :
 | TRUE { Core (True) }
 | FALSE { Core (False) }
 | OPEN NOT smtterm CLOSE  { Core (Not $3) }
 | OPEN IMPLY smtterms CLOSE { Core (Imply $3) }
 | OPEN AND smtterms CLOSE { Core (And $3) }
 | OPEN OR smtterms CLOSE { Core (Or $3) }
 | OPEN XOR smtterms CLOSE { Core (Xor $3) }
 | OPEN EQ smtterms CLOSE { Core (Eq $3) }
 | OPEN DISTINCT smtterms CLOSE { Core (Distinct $3) }
 | OPEN ITE smtterm smtterm smtterm CLOSE 
	{ Core (Ite ($3, $4, $5)) }
 | OPEN SYM smtterms CLOSE { Fun (Symbol $2, $3) }
 | SYM { Var (Symbol $1) }

stepids :
 | { [] }
 | STEP stepids  { $1 :: $2 }

%%
