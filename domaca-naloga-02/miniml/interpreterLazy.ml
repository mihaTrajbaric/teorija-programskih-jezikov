module S = Syntax

let rec eval_exp = function
  | S.Var _ -> failwith "Expected a closed term"
  | (S.Int _ | S.Bool _ | S.Lambda _ | S.RecLambda _ | S.Nil) as e -> e
  | S.Plus (e1, e2) ->
      let n1 = eval_int e1 and n2 = eval_int e2 in
      S.Int (n1 + n2)
  | S.Minus (e1, e2) ->
      let n1 = eval_int e1 and n2 = eval_int e2 in
      S.Int (n1 - n2)
  | S.Times (e1, e2) ->
      let n1 = eval_int e1 and n2 = eval_int e2 in
      S.Int (n1 * n2)
  | S.Equal (e1, e2) ->
      let n1 = eval_int e1 and n2 = eval_int e2 in
      S.Bool (n1 = n2)
  | S.Less (e1, e2) ->
      let n1 = eval_int e1 and n2 = eval_int e2 in
      S.Bool (n1 < n2)
  | S.Greater (e1, e2) ->
      let n1 = eval_int e1 and n2 = eval_int e2 in
      S.Bool (n1 > n2)
  | S.IfThenElse (e, e1, e2) -> (
      match eval_exp e with
      | S.Bool true -> eval_exp e1
      | S.Bool false -> eval_exp e2
      | _ -> failwith "Boolean expected")
  | S.Apply (e1, v) -> (
      let f = eval_exp e1 in
      match f with
      | S.Lambda (x, e) -> eval_exp (S.subst_exp [ (x, v) ] e)
      | S.RecLambda (f, x, e) as rec_f ->
          eval_exp (S.subst_exp [ (f, rec_f); (x, v) ] e)
      | _ -> failwith "Function expected")
  | S.Pair (e1, e2) -> 
      let v1 = eval_exp e1 and v2 = eval_exp e2 in
      S.Pair (v1, v2)
  | S.Fst e -> (
      match eval_exp e with
      | S.Pair(e1, _) -> 
        let v1 = eval_exp e1 in v1
      | _ -> failwith "Pair expected")
  | S.Snd e -> (
      match eval_exp e with
      | S.Pair(_, e2) -> 
        let v2 = eval_exp e2 in v2
      | _ -> failwith "Pair expected")
    | S.Cons (x, xs) -> 
      let v = eval_exp x and vs = eval_exp xs in
      S.Cons (v, vs)
  | S.Match (e, e1, x, xs, e2) -> (
      match eval_exp e with
      | Nil -> eval_exp e1
      | S.Cons (y, ys) -> 
        (* let v = eval_exp y and vs = eval_exp ys in *)
        eval_exp (S.subst_exp [ (x, y); (xs, ys)] e2)
      | _ -> failwith "List expected"
  )   
  (* | _ -> failwith "TODO interpLazy/eval_exp" *)

and eval_int e =
  match eval_exp e with S.Int n -> n | _ -> failwith "Integer expected"

let rec is_value = function
  | S.Int _ | S.Bool _ | S.Lambda _ | S.RecLambda _ | S.Nil -> true
  | S.Pair (v1, v2) when (is_value v1) -> is_value v2
  | S.Cons (x, xs) when (is_value x) && (is_value xs) -> true
  | S.Var _ | S.Plus _ | S.Minus _ | S.Times _ | S.Equal _ | S.Less _
  | S.Greater _ | S.IfThenElse _ | S.Apply _ | S.Pair _ | S.Fst _ 
  | S.Snd _ | S.Cons _ | S.Match _->
      false
  (* | _ -> failwith "TODO interpLazy/is_value" *)

let rec step = function
  | S.Var _ | S.Int _ | S.Bool _ | S.Lambda _ | S.RecLambda _ ->
      failwith "Expected a non-terminal expression"
  | S.Plus (S.Int n1, S.Int n2) -> S.Int (n1 + n2)
  | S.Plus (S.Int n1, e2) -> S.Plus (S.Int n1, step e2)
  | S.Plus (e1, e2) -> S.Plus (step e1, e2)
  | S.Minus (S.Int n1, S.Int n2) -> S.Int (n1 - n2)
  | S.Minus (S.Int n1, e2) -> S.Minus (S.Int n1, step e2)
  | S.Minus (e1, e2) -> S.Minus (step e1, e2)
  | S.Times (S.Int n1, S.Int n2) -> S.Int (n1 * n2)
  | S.Times (S.Int n1, e2) -> S.Times (S.Int n1, step e2)
  | S.Times (e1, e2) -> S.Times (step e1, e2)
  | S.Equal (S.Int n1, S.Int n2) -> S.Bool (n1 = n2)
  | S.Equal (S.Int n1, e2) -> S.Equal (S.Int n1, step e2)
  | S.Equal (e1, e2) -> S.Equal (step e1, e2)
  | S.Less (S.Int n1, S.Int n2) -> S.Bool (n1 < n2)
  | S.Less (S.Int n1, e2) -> S.Less (S.Int n1, step e2)
  | S.Less (e1, e2) -> S.Less (step e1, e2)
  | S.Greater (S.Int n1, S.Int n2) -> S.Bool (n1 > n2)
  | S.Greater (S.Int n1, e2) -> S.Greater (S.Int n1, step e2)
  | S.Greater (e1, e2) -> S.Greater (step e1, e2)
  | S.IfThenElse (S.Bool b, e1, e2) -> if b then e1 else e2
  | S.IfThenElse (e, e1, e2) -> S.IfThenElse (step e, e1, e2)
  | S.Apply (S.Lambda (x, e), v)-> S.subst_exp [ (x, v) ] e
  | S.Apply ((S.RecLambda (f, x, e) as rec_f), v) ->
      S.subst_exp [ (f, rec_f); (x, v) ] e
  | S.Apply (e1, e2) -> S.Apply (step e1, e2)
  | S.Pair (v1, e2) when is_value v1 -> S.Pair(v1, step e2)
  | S.Pair (e1, e2) -> S.Pair(step e1, e2)
  | S.Fst(S.Pair(v1, _)) when is_value v1-> v1
  | S.Fst(S.Pair(e1, e2)) -> S.Fst (S.Pair(step e1, e2))
  | S.Fst e -> S.Fst(step e)
  | S.Snd(S.Pair(_, v2)) when is_value v2 -> v2
  | S.Snd(S.Pair(e1, e2)) -> S.Snd (S.Pair(e1, step e2))
  | S.Snd e -> S.Snd(step e)
  | S.Cons (v, xs) when is_value v -> S.Cons(v, step xs)
  | S.Cons (x, xs) -> S.Cons(step x, xs)
  | S.Match (S.Nil, v1, _, _, _) -> v1
  | S.Match (S.Cons (y, ys), _, x, xs, v2) ->
    S.subst_exp [ (x, y); (xs, ys)] v2
  | S.Match (e, e1, x, xs, e2) -> S.Match (step e, e1, x, xs, e2)
  | _ -> failwith "TODO interpLazy/step"
  

let big_step e =
  let v = eval_exp e in
  print_endline (S.string_of_exp v)

let rec small_step e =
  print_endline (S.string_of_exp e);
  if not (is_value e) then (
    print_endline "  ~>";
    small_step (step e))
