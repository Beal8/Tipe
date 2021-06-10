open Ast;;
open Printf;;
open Hashtbl;;

(* Parsing *)
let parse s =
    let lexbuf = Lexing.from_string s in
    let ast = Parser.prog Lexer.read lexbuf in
    ast;;

let parse_type s =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.set_only Lexer.read lexbuf in ast;;

(* Print functions *)
let print_with_neg e =
  let rec print_expr_with_neg = function
    |Lam (x,b) -> sprintf ("λ%s.%s") x (print_expr_with_neg b)
    |Wedge (e1,e2) -> sprintf ("%s ∧ %s") (print_expr_with_neg e1) (print_expr_with_neg e2)
    |Hole n -> sprintf ("?%i") n
    |App (e1,e2) -> sprintf ("%s (%s)") (print_expr_with_neg e1) (print_expr_with_neg e2)
    |Var x -> sprintf ("%s") x
    |Rm_wedge0 e -> sprintf ("∧elim0 %s") (print_expr_with_neg e)
    |Rm_wedge1 e -> sprintf ("∧elim1 %s") (print_expr_with_neg e)
    |Dj_intro0 e -> sprintf ("∨intro0 %s") (print_expr_with_neg e)
    |Dj_intro1 e -> sprintf ("∨intro1 %s") (print_expr_with_neg e)
    |Dj_elim (e1,e2,e3) -> sprintf ("(∨elim (%s) (%s) (%s))") (print_expr_with_neg e1) (print_expr_with_neg e2) (print_expr_with_neg e3)
    |Bot_elim e -> sprintf ("⊥-elim %s") (print_expr_with_neg e)
    |Ann (e,t) -> sprintf ("%s : %s") (print_expr_with_neg e) (print_type_with_neg t)
  and print_type_with_neg = function
    |Arrow (t,Bottom) -> sprintf ("¬%s") (print_type_with_neg t)
    |Arrow (t1,t2) -> sprintf ("(%s -> %s)") (print_type_with_neg t1)  (print_type_with_neg t2)
    |Conj (t1,t2) -> sprintf ("(%s ∧ %s)") (print_type_with_neg t1) (print_type_with_neg t2)
    |Disj (t1,t2) -> sprintf ("(%s ∨ %s)") (print_type_with_neg t1) (print_type_with_neg t2)
    |Set t -> sprintf ("%s") t
    |Bottom -> sprintf ("⊥")
  in print_expr_with_neg e;;


let rec pretty_print_type = function
  |Arrow (t1,t2) -> sprintf ("(%s -> %s)") (pretty_print_type t1)  (pretty_print_type t2)
  |Conj (t1,t2) -> sprintf ("(%s ∧ %s)") (pretty_print_type t1) (pretty_print_type t2)
  |Disj (t1,t2) -> sprintf ("(%s ∨ %s)") (pretty_print_type t1) (pretty_print_type t2)
  |Set t -> sprintf ("%s") t
  |Bottom -> sprintf ("⊥")
and pretty_print_expr = function
  |Lam (x,b) -> sprintf ("λ%s.%s") x (pretty_print_expr b)
  |Wedge (e1,e2) -> sprintf ("%s ∧ %s") (pretty_print_expr e1) (pretty_print_expr e2)
  |Hole n -> sprintf ("?%i") n
  |App (e1,e2) -> sprintf ("%s (%s)") (pretty_print_expr e1) (pretty_print_expr e2)
  |Var x -> sprintf ("%s") x
  |Rm_wedge0 e -> sprintf ("∧elim0 %s") (pretty_print_expr e)
  |Rm_wedge1 e -> sprintf ("∧elim1 %s") (pretty_print_expr e)
  |Dj_intro0 e -> sprintf ("∨intro0 %s") (pretty_print_expr e)
  |Dj_intro1 e -> sprintf ("∨intro1 %s") (pretty_print_expr e)
  |Dj_elim (e1,e2,e3) -> sprintf ("(∨elim (%s) (%s) (%s))") (pretty_print_expr e1) (pretty_print_expr e2) (pretty_print_expr e3)
  |Bot_elim e -> sprintf ("⊥-elim %s") (pretty_print_expr e)
  |Ann (e,t) -> sprintf ("%s : %s") (pretty_print_expr e) (pretty_print_type t)
and pretty_print_context = function
    |[] -> ""
    |(x,t)::q -> (sprintf "%s : %s \n" x (pretty_print_type t)) ^ (pretty_print_context q);;

let pretty_print e = pretty_print_expr e;;

(* Racket fonction qui recherche un élément 'a dans une liste de couple ('a* 'b) et renvoit le couple s'il existe et une erreur sinon*)
let rec assoc elt clist = match clist with
  |[] -> failwith "y a pas"
  |(f,s)::q -> if elt = f then (f,s) else assoc elt q;;

let current =  ref (-1);;

let use_hole () =
  incr current; !current;;

(* bool ref pour savoir si on est en train de rempllir un but *)
let refining = ref false;;

(* table de hachage (id : int), (value : (type, ctxt)) *)
let goal_table = create 1000;;

let history = create 1000;;

(* deux fonctions basiques d'affichage d'erreurs qd on soumet une preuve invalide *)
let cannot_check ctx expr t = failwith (sprintf "impossible de vérifier que le type de %s est bien %s dans le contexte : \n %s" (pretty_print_expr expr) (pretty_print_type t) (pretty_print_context ctx));;
let cannot_synth ctx expr = failwith (sprintf "impossible de synthétiser le type de %s dans le contexte : \n %s" (pretty_print_expr expr) (pretty_print_context ctx))

(* application directe des règles d'inférences afin de déterminer la validité d'une preuve *)
let rec type_check ctx expr t = match expr with
  |Lam (x,a) -> begin
    match t with
    |Arrow (tt,tw) -> type_check ((x,tt)::ctx) a tw
    |_ -> cannot_check ctx expr t end
  |Hole n when n = (-1) -> true
  |Hole n when !refining -> replace goal_table n (t,ctx); true
  |Wedge (e1,e2) -> begin
      match t with
      |Conj(t1,t2) -> type_check ctx e1 t1 && type_check ctx e2 t2
      |_ -> cannot_check ctx expr t end
  |Dj_intro0 e -> begin
      match t with
      |Disj (t1,_) -> type_check ctx e t1
      |_ -> cannot_check ctx expr t end
  |Dj_intro1 e -> begin
      match t with
      |Disj (_,t2) -> type_check ctx e t2
      |_ -> cannot_check ctx expr t end
  |Dj_elim (e1,e2,e3) -> begin let d = type_synth ctx e1 in
      match d with
      |Disj (t1,t2) -> type_check ctx e2 (Arrow(t1,t)) && type_check ctx e3 (Arrow(t2,t))
      |_ -> cannot_check ctx expr t end
  |Bot_elim e -> type_check ctx e Bottom
  |Rm_wedge0 e -> begin
      match type_synth ctx e with
      |Conj(t1,_) -> t1 = t
      |_ -> cannot_check ctx expr t end
  |Rm_wedge1 e -> begin
      match type_synth ctx e with
      |Conj(_,t2) -> t2 = t
      |_ -> cannot_check ctx expr t end
  |_ -> if (type_synth ctx expr) = t then true else cannot_check ctx expr t
and type_synth ctx expr = match expr with
    |Lam (_,_) -> cannot_synth ctx expr
    |Ann(e,t) -> if (type_check ctx e t) then t else cannot_synth ctx expr
    |App (f,a) -> begin let tf = type_synth ctx f in
        match tf with
        |Arrow (tt,tw) when (type_check ctx a tt) -> tw
        |_ -> cannot_synth ctx expr end
    |Wedge (e1,e2) -> Conj (type_synth ctx e1, type_synth ctx e2)
    |Rm_wedge0 e -> begin let t = type_synth ctx e in
        match t with
        |Conj (t1,_) -> t1
        |_ -> cannot_synth ctx expr end
    |Rm_wedge1 e ->  begin let t = type_synth ctx e in
        match t with
        |Conj (_,t2) -> t2
        |_ -> cannot_synth ctx expr end
    |Var x -> let (_,t) = assoc x ctx in t
    |Hole _ -> cannot_synth ctx expr
    |_ -> cannot_synth ctx expr;;

(* essaie de synthétiser le type de l'expression e dans le contexte c si la fonction termine alors on a une preuve de la propriété synthétisée *)
let check c e = type_synth c e;;

(* vérifie la validité d'une preuve *)
let check_proof p = print_string (pretty_print_type (check [] (parse p))); true;;

(* ref stockant la propriété à prouver avec la preuve entrain d'être construite *)
let current_expr = ref (Hole (-1));;

(*affiche la propriété à prouver*)
let print_task () = print_string ((pretty_print !current_expr)^"\n");;

(* défini la propriété à prouver *)
let set_task s = clear goal_table; clear history; current := (-1);
  let t = parse_type s in
  begin add goal_table 0 (t,[]) ; current_expr := Ann (Hole (use_hole()), t) end;
  print_task();;

(* affiche tous les buts non encore résolus dans leur contexte *)
let rec print_goal ?(n = -1) () = if n = -1 then
    iter (fun nb _ -> print_goal ~n:nb ()) goal_table
  else
    begin
      let t,ctx = find goal_table n in
      if ctx = [] then print_string (sprintf ("Goal %i : %s \n") n (pretty_print_type t))
      else print_string (sprintf ("Goal %i : %s dans le contexte \n %s \n") n (pretty_print_type t) (pretty_print_context ctx))
    end;;

(*numérote les buts encore non numérotés*)
let rec numbered e = match e with
  |Lam (x,e) -> Lam (x,numbered e)
  |Ann (e,t) -> Ann(numbered e,t)
  |App (f,x) -> App(numbered f, numbered x)
  |Var x -> Var x
  |Wedge (e1,e2) -> Wedge(numbered e1, numbered e2)
  |Rm_wedge0 e -> Rm_wedge0 (numbered e)
  |Rm_wedge1 e -> Rm_wedge1 (numbered e)
  |Dj_intro0 e -> Dj_intro0 (numbered e)
  |Dj_intro1 e -> Dj_intro1 (numbered e)
  |Dj_elim (e1,e2,e3) -> Dj_elim (numbered e1, numbered e2, numbered e3)
  |Bot_elim e -> Bot_elim (numbered e)
  |Hole n -> if n=(-1) then Hole (use_hole()) else Hole n;;

(*remplace le but numéro n dans l'expression e avec l'expression repl*)
let rec replace_goal_with n repl e = match e with
  |Lam (x,e) -> Lam (x,replace_goal_with n repl e)
  |Ann (e,t) -> Ann(replace_goal_with n repl e,t)
  |App (f,x) -> App(replace_goal_with n repl f, replace_goal_with n repl x)
  |Var x -> Var x
  |Wedge (e1,e2) -> Wedge(replace_goal_with n repl e1, replace_goal_with n repl e2)
  |Rm_wedge0 e -> Rm_wedge0 (replace_goal_with n repl e)
  |Rm_wedge1 e -> Rm_wedge1 (replace_goal_with n repl e)
  |Dj_intro0 e -> Dj_intro0 (replace_goal_with n repl e)
  |Dj_intro1 e -> Dj_intro1 (replace_goal_with n repl e)
  |Dj_elim (e1,e2,e3) -> Dj_elim (replace_goal_with n repl e1, replace_goal_with n repl e2, replace_goal_with n repl e3)
  |Bot_elim e -> Bot_elim (replace_goal_with n repl e)
  |Hole m -> if m=n then repl else Hole m;;

(*remplace le but n avec l'expression s dans current_expr si l'expression s est correcte dons le contexte du but n*)
let refine n s =
  let (t,ctx) = find goal_table n
  and e = parse s in
  let () = assert (type_check ctx e t) in
  let en = numbered e in refining := true;
  let () = assert (type_check ctx en t) in refining := false;
  add history (!current) (n, find goal_table n, !current_expr); remove goal_table n; current_expr := (replace_goal_with n en !current_expr);
  let nb_goal = length goal_table in
  if nb_goal = 0 then print_string (sprintf "Preuve terminée : %s" (print_with_neg !current_expr))
    else begin
  print_string (sprintf "La tache avec %s est maintenant " (sprintf "%i but%s" nb_goal (if nb_goal = 1 then "" else "s")));
  print_task();
  print_goal() end;;

let undo () =
  try let n,gt,expr = find history !current in
  for i=n to !current do
    remove goal_table i
  done;
  current_expr := expr;
  add goal_table n gt;
  remove history !current;
  current := n;
  let nb_goal = length goal_table in
  if nb_goal = 0 then print_string (sprintf "Preuve terminée : %s" (print_with_neg !current_expr))
    else begin
  print_string (sprintf "La tache avec %s est maintenant " (sprintf "%i but%s" nb_goal (if nb_goal = 1 then "" else "s")));
  print_task();
  print_goal() end with _ -> failwith "impossible de remonter encore dans l'historique";;



let alphabet = [|"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"|]

let rec find_type t = function
  |[] -> raise Not_found
  |(_,a)as h::q -> if a=t then h else find_type t q;;

exception Pas_de_solution

let rec auto_proof n max_iter =
  if max_iter = 0 then failwith "impossible de trouver une solution" else
  let t,ctx = find goal_table n in
  match t with
  |Arrow _ -> begin printf "arrow"; try refine n (sprintf ("(λx%d.?)") (n)); auto_proof (!current) (max_iter-1) with _ -> remplir_avec_ctx n t ctx max_iter end
  |Conj _ -> begin try refine n ("(? ∧-intro ?)"); let c = !current in auto_proof (c - 1) (max_iter-1); auto_proof (c) (max_iter-1) with _ -> remplir_avec_ctx n t ctx max_iter end
  |Disj (t1,t2) -> begin let rec find_possible = function
      |[]->remplir_avec_ctx n t ctx max_iter
      |(x,tt)::q -> begin match tt with
        |_ when tt = t1 -> refine n ("(∨-intro0 " ^ x ^ ")")
        |_ when tt = t2 -> refine n ("(∨-intro1 " ^ x ^ ")")
        |Arrow (ti,ta) when ta = t1 -> begin try let xi,_ = find_type ti ctx in refine n ("(∨-intro0 ("^x^ " " ^xi^" ))") with _ -> remplir_avec_ctx n t ctx max_iter end
        |Arrow (ti,ta) when ta = t2 -> begin try let xi,_ = find_type ti ctx in refine n ("(∨-intro1 ("^x^" "^xi^"))") with _ -> remplir_avec_ctx n t ctx max_iter end
        |_ -> find_possible q end
    in find_possible ctx end
  |_ -> remplir_avec_ctx n t ctx max_iter
and remplir_avec_ctx n t ctx max_iter = match ctx with
      |[] -> begin try refine n ("(⊥-elim ?)"); auto_proof n (max_iter-1) with _ -> raise Pas_de_solution end
      |(x,tt)::q -> match tt with
        |_ when tt=t -> refine n x
        |Bottom -> refine n ("(⊥-elim " ^ x ^ ")")
        |Arrow (_,t2) when t2 = t -> begin try refine n ("(" ^ x ^ " ?" ^ ")"); auto_proof !current (max_iter-1) with |_ -> (remplir_avec_ctx n t q max_iter) end
        |Conj (_,t2) when t2 = t -> refine n ("(∧-elim1"^ x ^")")
        |Conj (t1,_) when t1 = t -> refine n ("(∧-elim0 "^x^")")
        |Disj _ -> begin try refine n ("(∨-elim " ^ x ^ " ? ?)"); let c = !current in auto_proof (c - 1) (max_iter-1); auto_proof c (max_iter-1) with |_ -> remplir_avec_ctx n t q max_iter end
        |_ -> remplir_avec_ctx n t q max_iter;;
