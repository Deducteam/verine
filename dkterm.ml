open Printf

type dkvar = string

type dkterm = 
  | Dkvar of dkvar
  | Dklam of dkvar * dkterm * dkterm
  | Dkapp of dkterm list
  | Dkarrow of dkterm * dkterm
  | Dktermtype
  | Dkproptype
  | Dknot
  | Dkand
  | Dkimply
  | Dkfalse
  | Dkeq
  | Dkprf

type dkline =
  | Dkdecl of dkvar * dkterm
  | Dkdeftype of dkvar * dkterm * dkterm
  | Dkprelude of string

let mk_var var = Dkvar var
let mk_lam var t1 t2 = Dklam (var, t1, t2)
let mk_app ts = Dkapp ts
let mk_app2 t1 t2 = mk_app [t1; t2]
let mk_app3 t1 t2 t3 = mk_app [t1; t2; t3]
let mk_arrow t1 t2 = Dkarrow (t1, t2)
let mk_termtype = Dktermtype
let mk_proptype = Dkproptype
let mk_not term = mk_app [Dknot; term]
let mk_and p q = mk_app [Dkand; p; q]
let mk_imply p q = mk_app [Dkimply; p; q]
let mk_false = Dkfalse
let mk_eq t1 t2 = mk_app [Dkeq; t1; t2]
let mk_prf t = mk_app [Dkprf; t]

let mk_decl var term = Dkdecl (var, term)
let mk_deftype var termtype term = Dkdeftype (var, termtype, term)
let mk_prelude name = Dkprelude (name)

let p_var out var = fprintf out "%s" var

let rec p_term out term =
  match term with
  | Dkvar (var) -> p_var out var
  | Dklam (var, t1, t2) -> 
    fprintf out "%a: %a => %a"
      p_var var p_term_p t1 p_term_p t2
  | Dkapp (ts) -> p_terms out ts
  | Dkarrow (t1, t2) -> 
    fprintf out "%a -> %a"
      p_term_p t1 p_term_p t2
  | Dktermtype -> fprintf out "logic.Term"
  | Dkproptype -> fprintf out "logic.Prop"
  | Dknot -> fprintf out "logic.not"
  | Dkand -> fprintf out "logic.and"
  | Dkimply -> fprintf out "logic.imply"
  | Dkfalse -> fprintf out "logic.False"
  | Dkeq -> fprintf out "logic.equal"
  | Dkprf -> fprintf out "logic.prf"

and p_term_p out term = 
  match term with
  | Dklam _ | Dkapp _ | Dkarrow _ ->
    fprintf out "(%a)" p_term term
  | _ -> p_term out term

and p_terms out terms = 
  match terms with
  | [] -> ()
  | [t] -> p_term_p out t
  | t :: q -> 
    fprintf out "%a %a"
      p_term_p t p_terms q

let p_line out line =
  match line with
  | Dkdecl (var, term) -> 
    fprintf out "%a: %a.\n" 
      p_var var
      p_term term
  | Dkdeftype (var, typeterm, term) ->
    fprintf out "%a: %a:= %a.\n"
      p_var var
      p_term typeterm
      p_term term
  | Dkprelude (name) -> fprintf out "#NAME %s.\n" name;
