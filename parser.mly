%{
  module Tr = Trace
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
%type <Trace.line> step
  
%%

step :
 | OPEN SET STEP OPEN rule clauses conclusion CLOSE CLOSE { Tr.Line ($3, $5, $6, $7) }
 | EOF { raise Error.EndOfFile }
;

rule :
 | INPUT { Tr.Input }
 | EQ_REFL { Tr.Eq_reflexive }
 | EQ_TRANS { Tr.Eq_transitive }
 | EQ_CONGR { Tr.Eq_congruent }
 | RESOLUTION { Tr.Resolution }
 | SYM { Tr.Anonrule ($1) }
 | AND { Tr.Anonrule ("and") }
 | OR { Tr.Anonrule ("or") }

clauses :
 | { [] }
 | CLAUSES OPEN stepids CLOSE { $3 }

conclusion :
 | CONCLUSION OPEN smtterms CLOSE { $3 }

smtterms :
 | { [] }
 | smtterm smtterms { $1 :: $2 }

smtterm :
 | SYM { Tr.Var (Tr.Symbol $1) }
 | OPEN SYM smtterms CLOSE { Tr.Fun (Tr.Symbol $2, $3) }
 | OPEN LET OPEN smtvarbindings CLOSE smtterm CLOSE { Tr.Let ($4, $6) }
 | TRUE { Tr.Core (Tr.True) }
 | FALSE { Tr.Core (Tr.False) }
 | OPEN NOT smtterm CLOSE  { Tr.Core (Tr.Not $3) }
 | OPEN IMPLY smtterms CLOSE { Tr.Core (Tr.Imply $3) }
 | OPEN AND smtterms CLOSE { Tr.Core (Tr.And $3) }
 | OPEN OR smtterms CLOSE { Tr.Core (Tr.Or $3) }
 | OPEN XOR smtterms CLOSE { Tr.Core (Tr.Xor $3) }
 | OPEN EQ smtterms CLOSE { Tr.Core (Tr.Eq $3) }
 | OPEN DISTINCT smtterms CLOSE { Tr.Core (Tr.Distinct $3) }
 | OPEN ITE smtterm smtterm smtterm CLOSE 
	{ Tr.Core (Tr.Ite ($3, $4, $5)) }

stepids :
 | { [] }
 | STEP stepids  { $1 :: $2 }

smtvarbindings :
 | smtvarbinding { [$1] }
 | smtvarbinding smtvarbindings { $1 :: $2 }

smtvarbinding :
 | OPEN SYM smtterm CLOSE { Tr.Varbinding (Tr.Symbol $2, $3) }

%%