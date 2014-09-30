%{
  open Global
%}
  
%token OPEN
%token CLOSE
%token SET
%token <string> STEP

%token INPUT
%token EQ_REFL
%token EQ_TRANS
%token RESOLUTION
%token AND

%token CONCLUSION
%token CLAUSES

%token NOT
%token EQ
%token FALSE
%token <string> ID

%token EOF

%start step
%type <Global.step> step
  
%%

step :
 | OPEN SET STEP OPEN rule clauses conclusion CLOSE CLOSE {Step ($3, $5, $6, $7)}
 | EOF {raise EndOfFile}
;

rule :
 | INPUT {Input}
 | EQ_REFL {Eq_reflexive}
 | EQ_TRANS {Eq_transitive}
 | RESOLUTION {Resolution}
 | AND {Rand}
 | ID {Anonrule($1)}

clauses :
 | {[]}
 | CLAUSES OPEN stepids CLOSE {$3}

conclusion :
 | CONCLUSION OPEN props CLOSE {$3}

props :
 | {[]}
 | prop props {$1 :: $2}

prop :
 | OPEN NOT prop CLOSE {Not($3)}
 | OPEN AND prop prop CLOSE {And($3, $4)}
 | OPEN EQ term term CLOSE {Eq($3, $4)}
 | FALSE {False}

stepids :
 | {[]}
 | STEP stepids  {$1 :: $2}

terms :
 | {[]}
 | term terms  {$1 :: $2}

term :
 | ID {Var($1)}
 | OPEN ID terms CLOSE {Fun($2, $3)}

%%
