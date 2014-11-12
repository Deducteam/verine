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

let dkvar var = Var var
let dklam var t term = Lam (var, t, term)
let dklams vars types e = 
  List.fold_left2 (fun term var t -> dklam var t term) e (List.rev vars) (List.rev types)
let dkapp t ts = 
  match t, ts with
  | _, [] -> t
  | App (us), _ -> App (us @ ts)
  | _, _ -> App (t :: ts)
let dkapp2 t1 t2 = dkapp t1 [t2]
let dkapp3 t1 t2 t3 = dkapp t1 [t2; t3]
let dkarrow t1 t2 = Arrow (t1, t2)

let dkterm = Const Dkterm
let dkprop = Const Dkprop
let dktrue = Const Dktrue
let dkfalse = Const Dkfalse
let dknot term = dkapp2 (Const Dknot) term
let dkimply p q = dkapp3 (Const Dkimply) p q
let dkand p q = dkapp3 (Const Dkand) p q
let dkor p q = dkapp3 (Const Dkor) p q
let dkeq t1 t2 = dkapp3 (Const Dkeq) t1 t2
let dkprf t = dkapp2 (Const Dkprf) t

let dkdecl t term = Dkdecl (t, term)
let dkdeftype t termtype term = Dkdeftype (t, termtype, term)
let dkprelude name = Dkprelude (name)

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
