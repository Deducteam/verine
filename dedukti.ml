open Printf

type var = string

type const = 
  | Lterm
  | Lprop
  | Ltrue
  | Lfalse
  | Lnot
  | Limply
  | Land
  | Lor
  | Leq
  | Lprf

type term = 
  | Var of var
  | Lam of var * term * term
  | App of term list                (* at least two arguments, the first is not an App *)
  | Arrow of term * term
  | Const of const

type line =
  | Declaration of term * term
  | Definition of term * term * term
  | Prelude of string

let var var = Var var
let lam var t term = Lam (var, t, term)
let lams vars types e = 
  List.fold_left2 (fun term var t -> lam var t term) e (List.rev vars) (List.rev types)
let app t ts = 
  match t, ts with
  | _, [] -> t
  | App (us), _ -> App (us @ ts)
  | _, _ -> App (t :: ts)
let app2 t1 t2 = app t1 [t2]
let app3 t1 t2 t3 = app t1 [t2; t3]
let arrow t1 t2 = Arrow (t1, t2)

let l_term = Const Lterm
let l_prop = Const Lprop
let l_true = Const Ltrue
let l_false = Const Lfalse
let l_not p = app2 (Const Lnot) p
let l_imply p q = app3 (Const Limply) p q
let l_and p q = app3 (Const Land) p q
let l_or p q = app3 (Const Lor) p q
let l_eq t1 t2 = app3 (Const Leq) t1 t2
let l_prf t = app2 (Const Lprf) t

let declaration t term = Declaration (t, term)
let definition t termtype term = Definition (t, termtype, term)
let prelude name = Prelude (name)

let print_var out var = fprintf out "%s" var

let rec print_const out const =
  match const with
  | Lterm -> output_string out "logic.Term"
  | Lprop -> output_string out "logic.Prop"
  | Lnot -> output_string out "logic.not"
  | Land -> output_string out "logic.and"
  | Lor -> output_string out "logic.or"
  | Limply -> output_string out "logic.imply"
  | Ltrue -> output_string out "logic.True"
  | Lfalse -> output_string out "logic.False"
  | Leq -> output_string out "logic.equal"
  | Lprf -> output_string out "logic.prf"

let rec print_term out term =
  match term with
  | Var (var) -> print_var out var
  | Lam (v, t1, t2) ->
    fprintf out "%a: %a => %a"
      print_var v print_term_p t1 print_term_p t2
  | App (ts) -> print_terms out ts
  | Arrow (t1, t2) ->
    fprintf out "%a -> %a"
      print_term_p t1 print_term_p t2
  | Const c -> print_const out c

and print_term_p out term = 
  match term with
  | Lam _ | App _ | Arrow _ ->
    fprintf out "(%a)" print_term term
  | _ -> print_term out term

and print_terms out terms = 
  match terms with
  | [] -> ()
  | [t] -> print_term_p out t
  | t :: q -> 
    fprintf out "%a %a"
      print_term_p t print_terms q

let print_line out line =
  match line with
  | Declaration (t, term) -> 
    fprintf out "%a: %a.\n" 
      print_term t
      print_term term
  | Definition (t, typeterm, term) ->
    fprintf out "%a: %a:= %a.\n"
      print_term t
      print_term typeterm
      print_term term
  | Prelude (name) -> fprintf out "#NAME %s.\n" name;
