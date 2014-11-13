open Printf

type var = string

type const = 
  | Dkterm
  | Dkprop
  | Dktrue
  | Dkfalse
  | Dknot
  | Dkimply
  | Dkand
  | Dkor
  | Dkeq
  | Dkprf

type term = 
  | Var of var
  | Lam of var * term * term
  | App of term list                (* at least two arguments, the first is not an App *)
  | Arrow of term * term
  | Const of const

type line =
  | Dkdecl of term * term
  | Dkdeftype of term * term * term
  | Dkprelude of string

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

let l_term = Const Dkterm
let l_prop = Const Dkprop
let l_true = Const Dktrue
let l_false = Const Dkfalse
let l_not p = app2 (Const Dknot) p
let l_imply p q = app3 (Const Dkimply) p q
let l_and p q = app3 (Const Dkand) p q
let l_or p q = app3 (Const Dkor) p q
let l_eq t1 t2 = app3 (Const Dkeq) t1 t2
let l_prf t = app2 (Const Dkprf) t

let declaration t term = Dkdecl (t, term)
let definition t termtype term = Dkdeftype (t, termtype, term)
let prelude name = Dkprelude (name)

let print_var out var = fprintf out "%s" var

let rec print_const out const =
  match const with
  | Dkterm -> output_string out "logic.Term"
  | Dkprop -> output_string out "logic.Prop"
  | Dknot -> output_string out "logic.not"
  | Dkand -> output_string out "logic.and"
  | Dkor -> output_string out "logic.or"
  | Dkimply -> output_string out "logic.imply"
  | Dktrue -> output_string out "logic.True"
  | Dkfalse -> output_string out "logic.False"
  | Dkeq -> output_string out "logic.equal"
  | Dkprf -> output_string out "logic.prf"

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
  | Dkdecl (t, term) -> 
    fprintf out "%a: %a.\n" 
      print_term t
      print_term term
  | Dkdeftype (t, typeterm, term) ->
    fprintf out "%a: %a:= %a.\n"
      print_term t
      print_term typeterm
      print_term term
  | Dkprelude (name) -> fprintf out "#NAME %s.\n" name;
