(* Expressions *)

type ide = string ;;

type exp =
	| CstInt of int
	| CstBool of bool
	| Den of ide
	| Times of exp * exp
	| Sum of exp * exp
	| Sub of exp * exp
	| Eq of exp * exp
	| Iszero of exp
	| Or of exp * exp
	| And of exp * exp
	| Not of exp
	| Ifthenelse of exp * exp * exp
	| Let of ide * exp * exp
	| Fun of ide * exp
	| Apply of exp * exp
	
	| ETree of exp tree								(* trees are also expressions *)
	
	| ApplyOver of exp * exp tree					(* application function to nodes *)
	
	| Update of (ide list) * exp * exp tree			(* node update *)
	
	| Select of (ide list) * exp * exp tree			(* node's conditional selection *)
	

and 'v tree = Empty									(* empty tree *)
	| Node of ide * 'v * 'v tree * 'v tree;;		(* binary tree *)



(* Environment *)

type 'v env = ( ide * 'v ) list ;;

type evT = Int of int
	| Bool of bool
	| VTree of evT tree
	| Closure of ide * exp * evT env
	| Unbound ;;

let emptyEnv = [ ("", Unbound) ] ;;

let bind (s: 'v env) (i:ide) (x:evT) = ( i, x ) :: s ;;

let rec lookup (s: 'v env) (i:ide) = match s with
	| [] -> Unbound
	| (j,v)::sl when j = i -> v
	| _::sl -> lookup sl i ;;



(* Type checkers *)

let typecheck (x,y) = match x with
	| "int" ->
		(match y with
				| Int(u) -> true
				| _ -> false)
	| "bool" ->
		(match y with
				| Bool(u) -> true
				| _ -> false)
	| "tree" ->
		(match y with
				| VTree(u) -> true
				| _ -> false)
	| _ -> failwith ("not a valid type");;


let is_zero x = match (typecheck("int", x), x) with
	| (true, Int(y)) -> Bool (y=0)
	| (_, _) -> failwith("run-time error");;

let int_eq(x,y) = match (typecheck("int", x), typecheck("int", y), x, y) with
	| (true, true, Int(v), Int(w)) -> Bool (v=w)
	| (_, _, _, _) -> failwith("run-time error");;

let int_plus(x,y) = match (typecheck("int", x), typecheck("int", y), x, y) with
	| (true, true, Int(v), Int(w)) -> Int(v + w)
	| (_, _, _, _) -> failwith("run-time error");;

let int_times(x,y) = match (typecheck("int", x), typecheck("int", y), x, y) with
	| (true, true, Int(v), Int(w)) -> Int(v * w)
	| (_, _, _, _) -> failwith("run-time error");;

let int_sub(x,y) = match (typecheck("int", x), typecheck("int", y), x, y) with
	| (true, true, Int(v), Int(w)) -> Int(v - w)
	| (_, _, _, _) -> failwith("run-time error");;

let bool_and(x,y) = match (typecheck("bool", x), typecheck("bool", y), x, y) with
	| (true, true, Bool(v), Bool(w)) -> Bool(v && w)
	| (_, _, _, _) -> failwith("run-time error");;

let bool_or(x,y) = match (typecheck("bool", x), typecheck("bool", y), x, y) with
	| (true, true, Bool(v), Bool(w)) -> Bool(v || w)
	| (_, _, _, _) -> failwith("run-time error");;

let bool_not(x) = match (typecheck("bool", x), x) with
	| (true, Bool(v)) -> Bool(not(v))
	| (_, _) -> failwith("run-time error");;



(* Semantic *)

let rec eval (e:exp) (s:'v env) =
	match e with
	| CstInt(n) -> Int(n)
	| CstBool(e) -> Bool(e)
	| Eq(e1, e2) -> int_eq((eval e1 s), (eval e2 s))
	| Times(e1, e2) -> int_times((eval e1 s), (eval e2 s))
	| Sum(e1, e2) -> int_plus((eval e1 s), (eval e2 s))
	| Sub(e1, e2) -> int_sub((eval e1 s), (eval e2 s))
	| And(e1, e2) -> bool_and((eval e1 s), (eval e2 s))
	| Or(e1, e2) -> bool_or((eval e1 s), (eval e2 s))
	| Not(e1) -> bool_not(eval e1 s)
	| Iszero(e1) -> is_zero(eval e1 s)		
	| Let(i, e, ebody) -> eval ebody (bind s i (eval e s))
	| Den(i) -> lookup s i
	| Ifthenelse(e1, e2, e3) ->
			let g = eval e1 s in
				(match (typecheck("bool", g), g) with
					| (true, Bool(true)) -> eval e2 s
					| (true, Bool(false)) -> eval e3 s
					| (_,_) -> failwith ("Ifthenelse: Not boolean guard"))
	| Fun(arg, ebody) -> Closure(arg, ebody, s)
	| Apply(Den(f), eArg) -> let fclosure = lookup s f in
			(match fclosure with
				| Closure(arg, fbody, fDecEnv) ->
					let aVal = eval eArg s in
					let aenv = bind fDecEnv arg aVal in
					eval fbody aenv
				| _ -> failwith ("Apply: Not functional value"))
	| Apply(_, _) -> failwith ("Apply: not first order function")
	
	| ETree(t) -> VTree(treeTraverse t s)

	| ApplyOver(Den(f), t) -> VTree(applyOver f t s)
	| ApplyOver(_, _) -> failwith ("ApplyOver: Not correct values")

	| Update(iList, Den(f), t) -> VTree(updateTree iList f t s)
	| Update(_, _, _) -> failwith ("Update: Not correct values")

	| Select(iList, Den(f), t) -> VTree(selectTree iList f t s) (*Inserire controllo che funzione restituisca booleano*)
	| Select(_, _, _) -> failwith ("Select: Not correct values")



and checkTypeFunction f s = let fclosure = lookup s f in
	(match fclosure with
		| Closure(arg, fbody, fDecEnv) ->
			(match fbody with
				| CstInt(n) -> "int"
				| CstBool(e) -> "bool"
				| Eq(e1, e2) -> "int"
				| Times(e1, e2) -> "int"
				| Sum(e1, e2) -> "int"
				| Sub(e1, e2) -> "int"
				| And(e1, e2) -> "bool"
				| Or(e1, e2) -> "bool"
				| Not(e1) -> "bool"
				| Iszero(e1) -> "int"
				| _ -> "Nan")
		| _ -> failwith ("Apply: Not functional value"))


and compatible f e s =
		let g = eval e s in
			(match g with
				| Int(u) -> if checkTypeFunction f s = "int" then true else false
				| Bool(u) -> if checkTypeFunction f s = "bool" then true else false
				| _ -> false)



and treeTraverse t s = match t with
	| Node(i, e, tl, tr) -> Node(i, eval e s, treeTraverse tl s, treeTraverse tr s)
	| Empty -> Empty


and applyOver f t s = match t with
	| Node(i, e, tl, tr) -> 
		if compatible f e s	then Node(i, eval (Apply(Den(f), e)) s, applyOver f tl s, applyOver f tr s)
			else Node(i, eval e s, applyOver f tl s, applyOver f tr s)
	| Empty -> Empty
	
	
and updateTree iList f t s = match t with
	| Node(i, e, tl, tr) ->
		if compatible f e s	&& checkPath iList i then Node(i, eval (Apply(Den(f), e)) s, updateTree iList f tl s, updateTree iList f tr s)
			else Node(i, eval e s, updateTree iList f tl s, updateTree iList f tr s)
	| Empty -> Empty


and checkPath iList i = match iList with
	| id::idl -> if id=i then true else checkPath idl i
	| [] -> false
	
	
and selectTree iList f t s = match t with
	| Node(i, e, tl, tr) -> if checkPath iList i && compatible f e s && (eval (Apply(Den(f), e)) s) = Bool(true)
								then Node(i, eval e s, selectTree iList f tl s, selectTree iList f tr s)
								else if selectTree iList f tl s = Empty
										then if selectTree iList f tr s = Empty then Empty 
																				else selectTree iList f tr s
										else selectTree iList f tl s 
	| Empty -> Empty








(* Test *)



(* Primitive operations *)

let myp = Let("x", CstInt(3), Let("y", CstInt(2), Sum(Den("x"), Den("y"))));; (* let x = 3 in y = 2 in x + y *)
eval myp emptyEnv;;
let myp' = CstInt(3);;
let e = Eq(CstInt(5),CstInt(5));;
let myite = Ifthenelse(e, myp, myp');;
eval myite emptyEnv;;

let apply = Let("f", Fun("x", Sum(Den("x"), CstInt(7))), Apply(Den("f"), CstInt(2)));; (* let f x = x+7 in f 2 *)
eval apply emptyEnv;;

(* Tree operations *)

(*

tree_test and tree_test2:

     a:1
    /   \
   /     \
  b:2     c:2
  
  
tree_test_omogeneity:

     a:1
    /   \
   /     \
  b:2     c:true
  
*)


let tree_test = ETree(Node("a", CstInt 1, Node("b", CstInt 2, Empty, Empty), Node("c", CstInt 2, Empty, Empty)));;
eval tree_test emptyEnv;;


let tree_test2 = Node("a", CstInt 1, Node("b", CstInt 2, Empty, Empty), Node("c", CstInt 2, Empty, Empty));;

let tree_test_omogeneity = Node("a", CstInt 1, Node("b", CstInt 2, Empty, Empty), Node("c", CstBool true, Empty, Empty));;


let applyOver_test = Let("f", Fun("x", Sum(Den("x"), CstInt 5)), ApplyOver(Den("f"), tree_test2));;
eval applyOver_test emptyEnv;;

let applyOver_test2 = Let("f", Fun("x", Not(Den("x"))), ApplyOver(Den("f"), tree_test_omogeneity));;
eval applyOver_test2 emptyEnv;;

let update_test = Let("f", Fun("x", Sum(Den("x"), CstInt 5)), Update(["a"; "b"; "c"], Den("f"), tree_test_omogeneity));;
eval update_test emptyEnv;;

(*

tree_test3:

     a:1
    /   \
   /     \
  b:2     c:true
            \
             \
              d:0

*)

let tree_test3 = Node("a", CstInt 1, Node("b", CstInt 2, Empty, Empty), Node("c", CstBool true, Empty, Node("d", CstInt 0, Empty, Empty)));;

let select_test = Let("f", Fun("x", Iszero(Den("x"))), Select(["c"; "d"], Den("f"), tree_test3));;
eval select_test emptyEnv;;

