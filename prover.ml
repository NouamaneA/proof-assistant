type tvar = string
          
type var = string
         
type ty =
  | TVar of tvar
  | Imp of ty * ty
  | And of ty * ty
  | Or of ty * ty
  | True
  | False
  | Nat

type tm =
  | Var of var
  | App of tm * tm
  | Abs of var * ty * tm
  | Pair of tm * tm
  | Fst of tm
  | Snd of tm
  | Case of tm * var * tm * var * tm
  | Unit
  | Left of tm * ty
  | Right of ty * tm
  | Absurd of tm * ty
  | Zero
  | Suc of tm
  | Rec of tm * tm * tm
         
let rec string_of_ty t =
  match t with
  | TVar v -> v
  | Imp (t1, t2) -> "(" ^ (string_of_ty t1) ^ " => " ^ (string_of_ty t2) ^ ")"
  | And (t1, t2) -> "(" ^ (string_of_ty t1) ^ " /\\ " ^ (string_of_ty t2) ^ ")"
  | Or (t1, t2) -> "(" ^ (string_of_ty t1) ^ " \\/ " ^ (string_of_ty t2) ^ ")"
  | True -> "T"
  | False -> "_"
  | Nat -> "Nat"

let rec string_of_tm term =
  match term with 
  | Var v -> v 
  | App (t1, t2) -> "(" ^ (string_of_tm t1) ^ " " ^ (string_of_tm t2) ^ ")"
  | Abs (x, typ, term) -> "(fun " ^ "(" ^ x ^ ": " ^ (string_of_ty typ) ^ ")." ^ (string_of_tm term) ^ ")"
  | Pair (t1, t2) -> "<" ^ (string_of_tm t1) ^ ", " ^ (string_of_tm t2) ^ ">"
  | Fst t1 -> "(fst (" ^ (string_of_tm t1) ^ "))"
  | Snd t1 -> "(snd (" ^ (string_of_tm t1) ^ "))"
  | Case (t, x, u, y, v) -> "(case " ^ (string_of_tm t) ^ " of " ^ x ^ " -> " ^ (string_of_tm u) ^ " | " ^ y ^ " -> " ^ (string_of_tm v) ^ ")"
  | Unit -> "()"
  | Left (tm, ty) -> "left (" ^ (string_of_tm tm) ^ ", " ^ (string_of_ty ty) ^ ")"
  | Right (ty, tm) -> "right (" ^ (string_of_ty ty) ^ ", " ^ (string_of_tm tm) ^ ")"
  | Absurd (t, a) -> "absurd (" ^ (string_of_tm t) ^ ", " ^ (string_of_ty a) ^ ")"
  | Zero -> "zero"
  | Suc n -> "suc (" ^ (string_of_tm n) ^ ")"
  | Rec (n, m, p) -> "rec (" ^ (string_of_tm n) ^ ", " ^ (string_of_tm m) ^ ", " ^ (string_of_tm p) ^ ")"

type context = (string * ty) list

exception Type_error
        
let rec infer_type env t =
  match t with 
  | Var x -> (try List.assoc x env with Not_found -> raise Type_error)
  | Abs (x, a, t) -> Imp (a, infer_type ((x, a)::env) t)
  | App (t, u) -> (
    match infer_type env t with 
    | Imp (a, b) -> check_type env u a ; b
    | _ -> raise Type_error
  )
  | Pair (t1, t2) -> And (infer_type env t1, infer_type env t2)
  | Fst t' -> (
    match infer_type env t' with 
    | And (a, b) -> a
    | _ -> raise Type_error
  )
  | Snd t' -> (
    match infer_type env t' with 
    | And (a, b) -> b
    | _ -> raise Type_error
  )
  | Case (t, x, u, y, v) -> (
    match infer_type env t with
    | Or (left, right) -> (
      match (infer_type ((x, left)::env) u, infer_type ((y, right)::env) v) with
      | (t1, t2) when t1 = t2 -> t1
      | _ -> raise Type_error
    )
    | _ -> raise Type_error
  )
  | Unit -> True
  | Left (tm, ty) -> Or (infer_type env tm, ty)
  | Right (ty, tm) -> Or (ty, infer_type env tm)
  | Absurd (t, a) -> (
    match infer_type env t with
    | False -> a
    | _ -> raise Type_error
  )
  | Zero -> Nat
  | Suc n -> (match infer_type env n with
              | Nat -> Nat
              | _ -> raise Type_error)
  | Rec (n, m, p) ->
     (match ((infer_type env n), (infer_type env m), (infer_type env p)) with
      | (Nat, t1, Imp (Imp (Nat, t2), t3)) 
        | (Nat, t1, Imp (Nat, Imp (t2, t3))) when t1 = t2 && t2 = t3 -> t1
      | _ -> raise Type_error)
and check_type env t a = 
  if infer_type env t <> a then raise Type_error
  
  
let and_com = Abs("x", And(TVar "A", TVar "B"), Pair (Snd (Var "x"), Fst (Var "x")))
            
let _ = print_endline (string_of_ty (infer_type [] and_com))
      
let truth = Abs ("x", Imp (True, TVar "A"), App (Var "x", Unit))
          
let _ = print_endline (string_of_ty (infer_type [] truth))
      
let or_com = Abs ("x", Or (TVar "A", TVar "B"), Case (Var "x", "y", Right (TVar "B", Var "y"), "z", Left (Var "z", TVar "A")))
           
let a_et_a_imp_faux_imp_b = Abs ("x", And (TVar "A", Imp (TVar "A", False)), Absurd (App (Snd (Var "x"), Fst (Var "x")), TVar "B"))
                          
let _ = print_endline (string_of_ty (infer_type [] a_et_a_imp_faux_imp_b))
      
(* begin parser *)
let () = Printexc.record_backtrace true
exception Parse_error
let must_kwd s k = match Stream.next s with Genlex.Kwd k' when k' = k -> () | _ -> raise Parse_error
let peek_kwd s k = match Stream.peek s with Some (Genlex.Kwd k') when k' = k -> let _ = Stream.next s in true | _ -> false
let stream_is_empty s = try Stream.empty s; true with Stream.Failure -> false
let ident s = match Stream.next s with Genlex.Ident x -> x | _ -> raise Parse_error
let lexer = Genlex.make_lexer ["("; ")"; "=>"; "/\\"; "\\/"; "fun"; "->"; ","; ":"; "fst"; "snd"; "T"; "left"; "right"; "not"; "case"; "of"; "|"; "absurd"; "_"; "Nat"; "zero"; "suc"; "rec"]
let ty_of_tk s =
  let rec ty () = arr ()
  and arr () =
    let a = prod () in
    if peek_kwd s "=>" then Imp (a, arr ()) else a
  and prod () =
    let a = sum () in
    if peek_kwd s "/\\" then And (a, prod ()) else a
  and sum () =
    let a = base () in
    if peek_kwd s "\\/" then Or (a, sum ()) else a
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> TVar x
    | Genlex.Kwd "(" ->
       let a = ty () in
       must_kwd s ")";
       a
    | Genlex.Kwd "T" -> True
    | Genlex.Kwd "_" -> False
    | Genlex.Kwd "not" ->
       let a = base () in
       Imp (a, False)
    | Genlex.Kwd "Nat" -> Nat
    | _ -> raise Parse_error
  in
  ty ()
let tm_of_tk s =
  let noapp = List.map (fun k -> Some (Genlex.Kwd k)) [")"; ","; "case"; "fun"; "of"; "->"; "|"] in
  let ty () = ty_of_tk s in
  let rec tm () = app ()
  and app () =
    let t = ref (abs ()) in
    while not (stream_is_empty s) && not (List.mem (Stream.peek s) noapp) do
      t := App (!t, abs ())
    done;
    !t
  and abs () =
    if peek_kwd s "fun" then
      (
        must_kwd s "(";
        let x = ident s in
        must_kwd s ":";
        let a = ty () in
        must_kwd s ")";
        must_kwd s "->";
        let t = tm () in
        Abs (x, a, t)
      )
    else if peek_kwd s "case" then
      (
        let t = tm () in
        must_kwd s "of";
        let x = ident s in
        must_kwd s "->";
        let u = tm () in
        must_kwd s "|";
        let y = ident s in
        must_kwd s "->";
        let v = tm () in
        Case (t, x, u, y, v)
      )
    else
      base ()
  and base () =
    match Stream.next s with
    | Genlex.Ident x -> Var x
    | Genlex.Kwd "(" ->
       if peek_kwd s ")" then
         Unit
       else
         let t = tm () in
         if peek_kwd s "," then
           let u = tm () in
           must_kwd s ")";
           Pair (t, u)
         else
           (
             must_kwd s ")";
             t
           )
    | Genlex.Kwd "fst" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ")";
       Fst t
    | Genlex.Kwd "snd" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ")";
       Snd t
    | Genlex.Kwd "left" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ",";
       let b = ty () in
       must_kwd s ")";
       Left (t, b)
    | Genlex.Kwd "right" ->
       must_kwd s "(";
       let a = ty () in
       must_kwd s ",";
       let t = tm () in
       must_kwd s ")";
       Right (a, t)
    | Genlex.Kwd "absurd" ->
       must_kwd s "(";
       let t = tm () in
       must_kwd s ",";
       let a = ty () in
       must_kwd s ")";
       Absurd (t, a)
    | _ -> raise Parse_error
  in
  tm ()
let ty_of_string a = ty_of_tk (lexer (Stream.of_string a))
let tm_of_string t = tm_of_tk (lexer (Stream.of_string t))
(* end parser *)
                   
let () =
  let l = [
      "A => B";
      "A /\\ B";
      "T";
      "A \\/ B";
      "_";
      "not A"
    ]
  in
  List.iter (fun s -> Printf.printf "the parsing of %S is %s\n%!" s (string_of_ty (ty_of_string s))) l

let () =
  let l = [
      "t u";
      "fun (x : A) -> t";
      "(t , u)";
      "fst(t)";
      "snd(t)";
      "()";
      "case t of x -> u | y -> v";
      "left(t,B)";
      "right(A,t)";
      "absurd(t,A)"
    ]
  in
  List.iter (fun s -> Printf.printf "the parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))) l
  
let string_of_ctx env = String.concat " , " (List.map (fun (x,t) -> x ^ " : " ^ (string_of_ty t)) env)
                      
let _ = print_endline(string_of_ctx [("x", Imp (TVar "A", TVar "B")); ("y", And (TVar "A", TVar "B")); ("Z", True)])
      
type sequent = context * ty
             
let string_of_seq s =
  let (env, t) = s in
  (string_of_ctx env) ^ " |- " ^ (string_of_ty t)
  
(* proving part *)
let rec prove env a =
  print_endline (string_of_seq (env,a));
  print_string "? "; flush_all ();
  let error e = print_endline e; prove env a in
  let cmd, arg =
    let cmd = input_line stdin in
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    c, a
  in
  match cmd with
  | "intro" ->
     (
       match a with
       | Imp (a, b) ->
          if arg = "" then error "Please provide an argument for intro." else
            let x = arg in
            let t = prove ((x,a)::env) b in
            Abs (x, a, t)
       | And (a, b) ->
          let t = prove env a in
          let u = prove env b in
          Pair (t, u)
       | True -> Unit
       | _ -> error "Don't know how to introduce this."
     )
  | "exact" ->
     let t = tm_of_string arg in
     if infer_type env t <> a then error "Not the right type."
     else t
  | "elim" ->
     let f = tm_of_string arg in (
         match infer_type env f with
         | Imp (f1, f2) when f2 = a -> (
           let t = prove env f1 in
           App (f, t)
         )
         | Imp (_, _) -> error "Not the right type."
      | Or (left, right) ->
         let t = prove ((arg ^ "l", left)::env) a in
         let u = prove ((arg ^ "r", right)::env) a in
         Case (f, arg ^ "l", t, arg ^ "r", u)
      | False -> Absurd (f, a)
      | _ -> error "Please provide an argument for elim."
       )
  | "cut" ->
     let b = ty_of_string arg in
     let t = prove env (Imp (b, a)) in
     let u = prove env b in
     App (t, u)
  | "fst" ->
     let p = tm_of_string arg in (
         match infer_type env p with
         | And (t, u) -> if t <> a then error "Not the right type." else (Fst p)
    | _ -> error "Not the right type."
       )
  | "snd" ->
     let p = tm_of_string arg in (
         match infer_type env p with
         | And (t, u) -> if u <> a then error "Not the right type." else (Snd p)
         | _ -> error "Not the right type."
       )
  | "left" -> (
    match a with
    | Or (a, b) ->
       let t = prove env a in 
       Left (t, b)
    | _ -> error "Not the right type."
    )
  | "right" -> (
    match a with
    | Or (a, b) ->
       let t = prove env b in
       Right (a, t)
    | _ -> error "Not the right type."
  )
  | cmd -> error ("Unknown command: " ^ cmd)
         
let () =
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string  "Typechecking... "; flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok.";
