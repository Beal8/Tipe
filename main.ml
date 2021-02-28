open Ast;;
open Printf;;
open Hashtbl;;

let parse s =
    let lexbuf = Lexing.from_string s in
    let ast = Parser.prog Lexer.read lexbuf in
    ast;;

let parse_type s =
  let lexbuf = Lexing.from_string s in
  let ast = TypeParser.prog TypeLexer.read lexbuf in ast;;

let rec pretty_print_type = function
  |Arrow (t1,t2) -> sprintf ("(%s -> %s)") (pretty_print_type t1)  (pretty_print_type t2)
  |Conj (t1,t2) -> sprintf ("(%s ∧ %s)") (pretty_print_type t1) (pretty_print_type t2)
  |Set t -> sprintf ("%s") t
and pretty_print_expr = function
  |Lam (x,b) -> sprintf ("λ%s.%s") x (pretty_print_expr b)
  |Wedge (e1,e2) -> sprintf ("%s Λ %s") (pretty_print_expr e1) (pretty_print_expr e2)
  |Hole n -> sprintf ("?%i") n
  |App (e1,e2) -> sprintf ("%s (%s)") (pretty_print_expr e1) (pretty_print_expr e2)
  |Var x -> sprintf ("%s") x
  |Rm_wedge0 e -> sprintf ("Λelim0 %s") (pretty_print_expr e)
  |Rm_wedge1 e -> sprintf ("Λelim1 %s") (pretty_print_expr e)
  |Ann (e,t) -> sprintf ("%s : %s") (pretty_print_expr e) (pretty_print_type t)
and pretty_print_context = function
    |[] -> ""
    |(x,t)::q -> (sprintf "%s : %s \n" x (pretty_print_type t)) ^ (pretty_print_context q);;


let pretty_print e = pretty_print_expr e;;

let rec assoc elt clist = match clist with
  |[] -> failwith "y a pas"
  |(f,s)::q -> if elt = f then (f,s) else assoc elt q;;

let current =  ref (-1);;

let use_hole () =
  incr current; !current;;

let refining = ref false;;
(* table de hachage id : int value : (type, ctxt) *)
let goal_table = create 10;;

let rec type_check ctx expr t = match expr with
  |Lam (x,a) -> begin
    match t with
    |Arrow (tt,tw) -> type_check ((x,tt)::ctx) a tw
    |_ -> failwith "pas comprendre" end
  |Hole n when !refining -> replace goal_table n (t,ctx); true
  |Hole n when n = (-1) -> true
  |Wedge (e1,e2) -> begin
      match t with
      |Conj(t1,t2) -> type_check ctx e1 t1 && type_check ctx e2 t2
      |_ -> failwith "Conjontion dans la preuve qui n'est pas présente dans le type" end
  |_ -> if (type_synth ctx expr) = t then true else failwith "caca"
and type_synth ctx expr = match expr with
    |Lam (_,_) -> failwith "pas possible"
    |Ann(e,t) -> if (type_check ctx e t) then t else failwith "chelou"
    |App (f,a) -> begin let tf = type_synth ctx f in
        match tf with
        |Arrow (tt,tw) when (type_check ctx a tt) -> tw
        |_ -> failwith"ca marche po" end
    |Wedge (e1,e2) -> Conj (type_synth ctx e1, type_synth ctx e2)
    |Rm_wedge0 e -> begin let t = type_synth ctx e in
        match t with
        |Conj (t1,_) -> t1
        |_ -> failwith "Conjontion dans l'expression qui n'est pas preésente dans la preuve" end
    |Rm_wedge1 e ->  begin let t = type_synth ctx e in
        match t with
        |Conj (_,t2) -> t2
        |_ -> failwith "Conjontion dans l'expression qui n'est pas preésente dans la preuve" end
    |Var x -> let (_,t) = assoc x ctx in t
    |Hole _ -> failwith "pas possible again";;

let check c e = type_synth c e;;

let check_proof p = print_string (pretty_print_type (check [] (parse p))); true;;

let current_expr = ref (Hole (-1));;

let print_task () = print_string ((pretty_print !current_expr)^"\n");;

let set_task s = clear goal_table; current := (-1);
  let t = parse_type s in
  begin add goal_table 0 (t,[]) ; current_expr := Ann (Hole(use_hole()), t) end;
  print_task();;

let rec print_goal ?(n = -1) () = if n = -1 then
    iter (fun nb _ -> print_goal ~n:nb ()) goal_table
  else
    begin
      let t,ctx = find goal_table n in
      if ctx = [] then print_string (sprintf ("Goal %i : %s \n") n (pretty_print_type t))
      else print_string (sprintf ("Goal %i : %s dans le contexte \n %s \n") n (pretty_print_type t) (pretty_print_context ctx))
    end;;

let rec numbered e = match e with
  |Lam (x,e) -> Lam (x,numbered e)
  |Ann (e,t) -> Ann(numbered e,t)
  |App (f,x) -> App(numbered f, numbered x)
  |Var x -> Var x
  |Wedge (e1,e2) -> Wedge(numbered e1, numbered e2)
  |Rm_wedge0 e -> Rm_wedge0 (numbered e)
  |Rm_wedge1 e -> Rm_wedge1 (numbered e)
  |Hole n -> if n=(-1) then Hole (use_hole()) else Hole n;;

let rec replace_goal_with n repl e = match e with
  |Lam (x,e) -> Lam (x,replace_goal_with n repl e)
  |Ann (e,t) -> Ann(replace_goal_with n repl e,t)
  |App (f,x) -> App(replace_goal_with n repl f, replace_goal_with n repl x)
  |Var x -> Var x
  |Wedge (e1,e2) -> Wedge(replace_goal_with n repl e1, replace_goal_with n repl e2)
  |Rm_wedge0 e -> Rm_wedge0 (replace_goal_with n repl e)
  |Rm_wedge1 e -> Rm_wedge1 (replace_goal_with n repl e)
  |Hole m -> if m=n then repl else Hole m;;

let refine n s =
  let (t,ctx) = find goal_table n
  and e = parse s in
  let () = assert (type_check ctx e t) in
  let en = numbered e in refining := true;
  let () = assert (type_check ctx en t) in refining := false;
  remove goal_table n; current_expr := (replace_goal_with n en !current_expr);
  let nb_goal = length goal_table in
  print_string (sprintf "La tache avec %s est maintenant " (sprintf "%i but%s" nb_goal (if nb_goal = 1 then "" else "s")));
  print_task();
  print_goal();;
