%{
  open Global
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

%token <string> ID

%token EOF

%start step
%type <Global.step> step
  
%%

step :
 | OPEN SET STEP OPEN rule clauses conclusion CLOSE CLOSE { Step ($3, $5, $6, $7) }
 | EOF { raise EndOfFile }
;

rule :
 | INPUT { Input }
 | EQ_REFL { Eq_reflexive }
 | EQ_TRANS { Eq_transitive }
 | EQ_CONGR { Eq_congruent }
 | RESOLUTION { Resolution }
 | ID { Anonrule ($1) }
 | AND { Anonrule ("and") }
 | OR { Anonrule ("or") }

clauses :
 | { [] }
 | CLAUSES OPEN stepids CLOSE { $3 }

conclusion :
 | CONCLUSION OPEN props CLOSE { $3 }

props :
 | { [] }
 | prop props { $1 :: $2 }

prop :
 | TRUE { assert false }
 | FALSE { assert false }
 | OPEN NOT prop CLOSE  { Core (Not $3) }
 | OPEN IMPLY props CLOSE { assert false }
 | OPEN AND props CLOSE { 
   let coreand p1 p2 = Core (And (p1, p2)) in
   let rec xcoreand ps = 
   match List.rev ps with 
   | [] | [_] -> assert false
   | [p1; p2] -> coreand p2 p1
   | p1 :: ps -> coreand (xcoreand (List.rev ps)) p1 in
   xcoreand $3 }
 | OPEN OR props CLOSE { match $3 with [p1; p2] -> Core (Or (p1, p2)) | _ -> assert false }
 | OPEN XOR props CLOSE { assert false }
 | OPEN EQ terms CLOSE { match $3 with [t1; t2] -> Core (Eq (t1, t2)) | _ -> assert false }
 | OPEN DISTINCT terms CLOSE { assert false }
 | OPEN ITE CLOSE { assert false }
 | OPEN ID terms CLOSE { Pred($2, $3)}

stepids :
 | { [] }
 | STEP stepids  { $1 :: $2 }

terms :
 | { [] }
 | term terms  { $1 :: $2 }

term :
 | ID { Var($1) }
 | OPEN ID terms CLOSE { Fun($2, $3) }

%%
