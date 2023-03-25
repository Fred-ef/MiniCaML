(* ########################################################################## *)

(* definizione del tipo identificatore *)
type ide = string;;

(* definizione descrittori di tipo *)
type desc = Int | String;;

(* definizione della sintassi astratta del linguaggio *)
type exp = CstInt of int  (* valori interi *)
         | CstBool of bool  (* valori booleani *)
         | CstStr of ide  (* valore stringa *)
         | Den of ide (* costrutto per l'applicazione di un identificatore *)
         | Sum of exp * exp (* expr intera: somma tra espressioni *)
         | Times of exp * exp (* expr intera: prodotto tra espressioni *)
         | Sub of exp * exp (* expr intera: sottrazione tra espressioni *)
         | Iszero of exp  (* expr booleana: uguaglianza di espressione a 0 *)
         | Isnotzero of exp (* expr booleana: diverso da 0 *)
         | StrCmp of exp * exp  (* expr string: comprare due stringhe *)
         | Or of exp * exp  (* expr booleana: OR logico tra espressioni *)
         | And of exp * exp (* expr booleana: AND logico tra espressioni *)
         | Not of exp (* expr booleana: NOT logico su un'espressione *)
         | Eq of exp * exp  (* expr booleana: uguaglianza tra espressioni *)
         | Ifthenelse of exp * exp * exp  (* control-flow: if-then-else *)
         | Let of ide * exp * exp (* costrutto per la dichiarazione di variabili/funzioni *)
         | Letrec of ide * exp * exp  (* costrutto per la dichiarazione di funzioni ricorsive *)
         | Fun of ide * exp (* valore funzionale *)
         | RecFun of ide * ide * exp  (* valore funzionale per funzioni ricorsive *)
         | Apply of exp * exp (* costrutto per l'applicazione di funzione ad un parametro *)
         | EList of exp (* costruttore per il tipo lista *)
         | EListElem of exp * exp (* expr su liste: inserimento *)
         | EEmptyList (* descrittore lista vuota *)
         | EEmptySet (* expr Set: insieme vuoto *)
         | SetSearch of exp * exp (* ricerca su insieme *)
         | SetInsert of exp * exp (* inserimento in un insieme *)
         | SetRemove of exp * exp (* rimozione da un insieme *)
         | SetIsEmpty of exp  (* verifica insieme vuoto *)
         | SetMax of exp  (* massimo dell'insieme *)
         | SetMin of exp  (* minimo dell'insieme *)
         | SetUnion of exp * exp  (* unione fra insiemi *)
         | SetIntersection of exp * exp (* intersezione fra insiemi *)
         | SetDifference of exp * exp (* differenza tra insiemi *)
         | SetIsSubSet of exp * exp (* test inclusione fra insiemi *)
         | Empty of desc  (* costruttore per l'insieme vuoto *)
         | Singleton of exp * desc  (* costruttore per l'insieme singoletto *)
         | Of of desc * exp (* costruttore per insieme da lista *)
         | SetFilter of exp * exp (* filter su insiemi *)
         | SetMap of exp * exp (* map su insiemi *)
         | SetForAll of exp * exp (* quantificazione universale su insiemi *)
         | SetExists of exp * exp;; (* quantificazione esistenziale su insiemi *)

(* definizione dell'ambiente polimorfo *)
type 't env = (string * 't) list;;


(* tipi esprimibili a runtime *)
type evT =
  | Int of int  (* tipo intero *)
  | Bool of bool  (* tipo booleano *)
  | String of ide (* tipo stringa *)
  | Closure of (ide * exp * evT env)  (* tipo chiusura *)
  | RecClosure of (ide * ide * exp * evT env) (* tipo chiusura ricorsiva *)
  | List of evT (* lista di tipi primitivi *)
  | Cons of evT * evT (* lista con più elementi *)
  | EmptyList (* lista vuota *)
  | IntSet of evT (* insieme di interi *)
  | StringSet of evT  (* insieme di stringhe *)
  | SetElem of evT * evT * evT
  | EmptySet  (* insieme vuoto *)
  | Unbound;; (* valore per i riferimenti non risolti *)


(* definizione delle funzioni operanti sull'ambiente *)
let emptyEnv = [];;
let bind (s : 't env) (i : string) (x : 't) = (i, x)::s;;
let rec lookup (s : 't env) (i : string) = match s with
  | [] -> Unbound (* se l'ambiente è vuoto, l'ide è sicuramente unbound *)
  | (n,v)::sl when n=i -> v (* trovato il nome, restituisce il valore associato *)
  | _::sl -> lookup sl i;;  (* altrimenti continua a cercare nell'env *)


(* definizione del typechecker dinamico *)
let typecheck (x,y) = match x with
  | "int" -> (match y with
      | Int(u) -> true
      | _ -> false)
  | "bool" -> (match y with
      | Bool(u) -> true
      | _ -> false)
  | "string" -> (match y with
      | String(u) -> true
      | _ -> false)
  | "primitive" -> (match y with
      | Int(u) -> true
      | Bool(u) -> true
      | String(s) -> true
      | _ -> false)
  | "fun" -> (match y with
      | Closure(f) -> true
      | RecClosure(f) -> true
      | _ -> false)
  | "list" -> (match y with
      | List(l) -> true
      | EmptyList -> true
      | _ -> false)
  | "intset" -> (match y with
      | IntSet(_) -> true
      | _ -> false)
  | "stringset" -> (match y with
      | StringSet(_) -> true
      | _ -> false)
  | _ -> failwith "Dynamic typechecker: Invalid type";;


(* definizione delle operazioni native del linguaggio *)
let is_zero x = match (typecheck("int", x), x) with
  | (true, Int(u)) -> Bool(u=0)
  | (_,_) -> failwith "is_zero func: invalid type: type int was expected";;

let is_not_zero x = match (typecheck("int", x), x) with
  | (true, Int(u)) -> Bool(u<>0)
  | (_,_) -> failwith "is_not_zero func: invalid type: type int was expected";;

let str_cmp (x,y) = match (typecheck("string", x), typecheck("string", y), x, y) with
  | (true, true, String(s), String(t)) -> Bool(s=t)
  | (_,_,_,_) -> failwith "str_cmp func: invalid type: type (string * string) was expected"

let int_eq (x,y) = match (typecheck("int", x), typecheck ("int", y), x, y) with
  | (true, true, Int(u), Int(v)) -> Bool(u=v)
  | (_,_,_,_) -> failwith "int_eq func: invalid type: type int was expected";;

let int_plus (x,y) = match (typecheck("int", x), typecheck ("int", y), x, y) with
  | (true, true, Int(u), Int(v)) -> Int(u+v)
  | (_,_,_,_) -> failwith "int_plus func: invalid type: type int was expected";;

let int_sub (x,y) = match (typecheck("int", x), typecheck ("int", y), x, y) with
  | (true, true, Int(u), Int(v)) -> Int(u-v)
  | (_,_,_,_) -> failwith "int_sub func: invalid type: type int was expected";;

let int_times (x,y) = match (typecheck("int", x), typecheck ("int", y), x, y) with
  | (true, true, Int(u), Int(v)) -> Int(u*v)
  | (_,_,_,_) -> failwith "int_times func: invalid type: type int was expected";;

let bool_and (x,y) = match (typecheck("bool", x), typecheck ("bool", y), x, y) with
  | (true, true, Bool(u), Bool(v)) -> Bool(u&&v)
  | (_,_,_,_) -> failwith "bool_and func: invalid type: type bool was expected";;

let bool_or (x,y) = match (typecheck("bool", x), typecheck ("bool", y), x, y) with
  | (true, true, Bool(u), Bool(v)) -> Bool(u||v)
  | (_,_,_,_) -> failwith "bool_or func: invalid type: type bool was expected";;

let bool_not (x) = match (typecheck("bool", x), x) with
  | (true, Bool(u)) -> Bool(not(u))
  | (_,_) -> failwith "bool_not func: invalid type: type bool was expected";;


(* definizione delle funzioni su liste *)

(* restituisce la testa della lista *)
let head (l:evT) : (evT) = match (typecheck("list", l), l) with
  | (true, List(Cons(x, _))) -> x
  | (true, _) -> failwith "head func: couldn't retrieve first element"
  | (_,_) -> failwith "head func: invalid type: type list was expected";;


(* inserisce un elemento nella lista *)
let cons (e:evT) (l:evT) = match (typecheck("primitive", e), typecheck("list", l), e, l) with
  | (true, true, _, List(EmptyList)) -> List(Cons(e, List(EmptyList)))
  | (true, true, Int(_), List(Cons(_))) -> if (typecheck("int", head(l))) then (List(Cons(e, l))) else failwith "cons func: invalid type: cons of an int element in a non-int list"
  | (true, true, Bool(_), List(Cons(_))) -> if (typecheck("bool", head(l))) then (List(Cons(e, l))) else failwith "cons func: invalid type: cons of a bool element in a non-bool list"
  | (true, true, String(_), List(Cons(_))) -> if (typecheck("string", head(l))) then (List(Cons(e, l))) else failwith "cons func: invalid type: cons of a string element in a non-string list"
  | (false, _, _, _) -> failwith "cons func: invalid type: first operand must be a 'primitive' type"
  | (_, false, _, _) -> failwith "cons func: invalid type: second operand must be a list"
  | (_, _, _, _) -> failwith "cons func: invalid type: type (primitive * list) was expected";;


(* concatena due liste dello stesso tipo *)
let rec concat (ls1 : evT) (ls2 : evT) : (evT) = match (typecheck("list", ls1), typecheck("list", ls2), ls1, ls2) with
  | (true, true, List(a), List(b)) -> (match (a, b) with
      | (EmptyList, _) -> ls2
      | (_, EmptyList) -> ls1
      | (Cons(x, xs), Cons(y, ys)) -> concat xs (List(Cons(x, ls2)))
      | _ -> failwith "concat func: invalid type: valid list expected")
  | _ -> failwith "concat func: invalid type: (list * list) was expected";;


(* definizione delle funzioni su insieme *)

(* ricerca su insieme *)
let rec setsearch (el:evT) (set:evT) : (evT) = match el with
  | Int(n) -> (match (typecheck("intset", set), set) with
      | (true, IntSet(i)) -> (match i with
          | EmptySet -> Bool(false)
          | SetElem(lt, Int(m), rt) when n=m -> Bool(true)
          | SetElem(lt, Int(m), rt) when n<m -> setsearch el lt
          | SetElem(lt, Int(m), rt) when n>m -> setsearch el rt
          | _ -> failwith "search func: invalid int set")
      | _ -> failwith "search func: IntSet expected with an Int parameter")
  | String(s) -> (match (typecheck("stringset", set), set) with
      | (true, StringSet(i)) -> (match i with
          | EmptySet -> Bool(false)
          | SetElem(lt, String(t), rt) when s=t -> Bool(true)
          | SetElem(lt, String(t), rt) when s<t -> setsearch el lt
          | SetElem(lt, String(t), rt) when s>t -> setsearch el rt
          | _ -> failwith "search func: invalid string set")
      | _ -> failwith "search func: StringSet expected with a String parameter")
  | _ -> failwith "search func: invalid parameter type";;


(* inclusione tra insiemi *)
let rec setissubset (set1 : evT) (set2: evT) (b : evT) : (evT) = match (set1, set2) with
  | (IntSet(i), IntSet(_)) -> (match i with
      | EmptySet -> b
      | SetElem(lt, el, rt) -> if (setsearch el set2) = (Bool(true))
          then (bool_and((setissubset lt set2 b), (setissubset rt set2 b)))
          else (Bool(false))
      | _ -> failwith "setissubset func: invalid set")
  | (StringSet(i), StringSet(_)) -> (match i with
      | EmptySet -> b
      | SetElem(lt, el, rt) -> if (setsearch el set2) = (Bool(true))
          then (bool_and((setissubset lt set2 b), (setissubset rt set2 b)))
          else (Bool(false))
      | _ -> failwith "setissubset func: invalid set")
  | _ -> failwith "setissubset func: invalid type: (set * set) of same type expected";;


  (* restituisce il massimo dell'insieme *)
  let rec setmax (set:evT) : (evT) = match set with
    | IntSet(i) -> (match i with
        | EmptySet -> failwith "setmax func: set is empty"
        | SetElem(_, el, IntSet(EmptySet)) -> el
        | SetElem(_, _, rt) -> setmax rt
        | _ -> failwith "setmax func: invalid set")
    | StringSet(i) -> (match i with
        | EmptySet -> failwith "setmax func: set i empty"
        | SetElem(_, el, StringSet(EmptySet)) -> el
        | SetElem(_, _, rt) -> setmax rt
        | _ -> failwith "setmax func: invalid set")
    | _ -> failwith "setmax func: invalid type: a valid set was expected";;

  (* restituisce il minimo dell'insieme *)
  let rec setmin (set:evT) : (evT) = match set with
    | IntSet(i) -> (match i with
        | EmptySet -> failwith "setmin func: set is empty"
        | SetElem(IntSet(EmptySet), el, _) -> el
        | SetElem(lt, _, _) -> setmin lt
        | _ -> failwith "setmin func: invalid set")
    | StringSet(i) -> (match i with
        | EmptySet -> failwith "setmin func: set is empty"
        | SetElem(StringSet(EmptySet), el, _) -> el
        | SetElem(lt, _, _) -> setmin lt
        | _ -> failwith "setmin func: invalid set")
    | _ -> failwith "setmin func: invalid type: a valid set was expected";;


(* inserimento insiemistico *)
let rec setinsert (el:evT) (set:evT) : (evT) = match el with
  | Int(n) -> (match (typecheck("intset", set), set) with
      | (true, IntSet(i)) -> (match i with
          | EmptySet -> IntSet(SetElem(IntSet(EmptySet), Int(n), IntSet(EmptySet)))
          | SetElem(lt, Int(m), rt) when n=m -> IntSet(SetElem(lt, Int(m), rt))
          | SetElem(lt, Int(m), rt) when n<=m -> IntSet(SetElem(setinsert el lt, Int(m), rt))
          | SetElem(lt, Int(m), rt) when n>m -> IntSet(SetElem(lt, Int(m), setinsert el rt))
          | _ -> failwith "setinsert func: invalid set")
      | _ -> failwith "setinsert func: IntSet expected with an Int parameter")
  | String(s) -> (match (typecheck("stringset", set), set) with
      | (true, StringSet(i)) -> (match i with
          | EmptySet -> StringSet(SetElem(StringSet(EmptySet), String(s), StringSet(EmptySet)))
          | SetElem(lt, String(t), rt) when s=t -> StringSet(SetElem(lt, String(t), rt))
          | SetElem(lt, String(t), rt) when s<=t -> StringSet(SetElem(setinsert el lt, String(t), rt))
          | SetElem(lt, String(t), rt) when s>t -> StringSet(SetElem(lt, String(t), setinsert el rt))
          | _ -> failwith "setinsert func: invalid set")
      | _ -> failwith "setinsert func: StringSet expected with a String parameter")
  | _ -> failwith "setinsert func: invalid parameter type";;


(* rimozione insiemistica *)
let rec setremove (el:evT) (set:evT) : (evT) = match el with
  | Int(n) -> (match (typecheck("intset", set), set) with
      | (true, IntSet(i)) -> (match i with
          | EmptySet -> IntSet(EmptySet)
          | SetElem(lt, Int(m), rt) when n<m -> IntSet(SetElem(setremove el lt, Int(m), rt))
          | SetElem(lt, Int(m), rt) when n>m -> IntSet(SetElem(lt, Int(m), setremove el rt))
          | SetElem(IntSet(EmptySet), Int(m), IntSet(EmptySet)) -> IntSet(EmptySet)
          | SetElem(IntSet(EmptySet), Int(m), rt) -> rt
          | SetElem(lt, Int(m), IntSet(EmptySet)) -> lt
          | SetElem(lt, Int(m), rt) -> let a = setmin rt in IntSet(SetElem(lt, a, setremove a rt))
          | _ -> failwith "setremove func: invalid type: type intset was expected")
      | _ -> failwith "setremove func: IntSet expected with an Int parameter")
  | String(s) -> (match (typecheck("stringset", set), set) with
      | (true, StringSet(i)) -> (match i with
          | EmptySet -> StringSet(EmptySet)
          | SetElem(lt, String(t), rt) when s<t -> StringSet(SetElem(setremove el lt, String(t), rt))
          | SetElem(lt, String(t), rt) when s>t -> StringSet(SetElem(lt, String(t), setremove el rt))
          | SetElem(StringSet(EmptySet), String(t), StringSet(EmptySet)) -> StringSet(EmptySet)
          | SetElem(StringSet(EmptySet), String(t), rt) -> rt
          | SetElem(lt, String(t), StringSet(EmptySet)) -> lt
          | SetElem(lt, String(t), rt) -> let a = setmin rt in StringSet(SetElem(lt, a, setremove a rt))
          | _ -> failwith "setremove func: invalid type: type intset was expected")
      | _ -> failwith "setremove func: IntSet expected with an Int parameter")
  | _ -> failwith "setremove func: invalid parameter type";;


(* rimuove dall'insieme gli elementi presenti nella lista *)
let rec setremovefromlist (set : evT) (ls : evT) : (evT) = match set with
  | IntSet(_) -> (match (set, ls) with
      | (IntSet(EmptySet), _) -> set
      | (_, List(EmptyList)) -> set
      | (_, List(Cons(Int(x), xs))) -> setremovefromlist xs (setremove (Int(x)) set)
      | _ -> failwith "setremovefromlist func: invalid type: (set * list) of int expected")
  | StringSet(_) -> (match (set, ls) with
      | (StringSet(EmptySet), _) -> set
      | (_, List(EmptyList)) -> set
      | (_, List(Cons(String(x), xs))) -> setremovefromlist xs (setremove (String(x)) set)
      | _ -> failwith "setremovefromlist func: invalid type: (set * list) of string expected")
  | _ -> failwith "setremovefromlist func: invalid type: (set * list) expected";;


(* controlla che un insieme sia vuoto (true) o meno (false) *)
let setisempty (set:evT) : (evT) = match set with
  | IntSet(EmptySet) -> Bool(true)
  | StringSet(EmptySet) -> Bool(true)
  | IntSet(_) -> Bool(false)
  | StringSet(_) -> Bool(false)
  | _ -> failwith "setisempty func: invalid type: a valid set was expected";;


(* costruisce una lista a partire da un insieme *)
let rec listfromset (set : evT) (ls : evT) : (evT) = match (typecheck("list", ls), ls, set) with
  | (true, List(_), IntSet(i)) -> (match i with
      | EmptySet -> ls
      | SetElem(lt, el, rt) -> (List(Cons(el, (concat (listfromset lt ls) (listfromset rt ls)))))
      | _ -> failwith "listfromset func: invalid type: a valid set was expected")
  | (true, List(_), StringSet(i)) -> (match i with
      | EmptySet -> ls
      | SetElem(lt, el, rt) -> (List(Cons(el, (concat (listfromset lt ls) (listfromset rt ls)))))
      | _ -> failwith "listfromset func: invalid type: a valid set was expected")
  | _ -> failwith "listfromset func: invalid type: (set * list) was expected";;


(* costruisce o riempie un insieme a partire da una lista *)
let rec setfromlist (ls : evT) (set : evT) : (evT) = match set with
  | IntSet(_) -> (match ls with
      | List(EmptyList) -> set
      | List(Cons(Int(x), xs)) -> setfromlist xs (setinsert (Int(x)) set)
      | _ -> failwith "setfromlist func: type error: int list expected")
  | StringSet(_) -> (match ls with
      | List(EmptyList) -> set
      | List(Cons(String(x), xs)) -> setfromlist xs (setinsert (String(x)) set)
      | _ -> failwith "setfromlist func: type error: string list expected")
  | _ -> failwith "setfromlist func: type error: invalid set";;


(* intersezione tra insiemi *)
let rec setintersect (set1 : evT) (set2 : evT) (ls : evT) : (evT) = match (set1, set2, ls) with
  | (IntSet(i), IntSet(_), List(_)) -> (match i with
      | EmptySet -> ls
      | SetElem(lt, el, rt) -> if (setsearch el set2) = Bool(true)
          then (List(Cons(el, (concat (setintersect lt set2 ls) (setintersect rt set2 ls)))))
          else (concat (setintersect lt set2 ls) (setintersect rt set2 ls))
      | _ -> failwith "setintersect func: invalid set")
  | (StringSet(i), StringSet(_), List(_)) -> (match i with
      | EmptySet -> ls
      | SetElem(lt, el, rt) -> if (setsearch el set2) = Bool(true)
          then (List(Cons(el, (concat (setintersect lt set2 ls) (setintersect rt set2 ls)))))
          else (concat (setintersect lt set2 ls) (setintersect rt set2 ls))
      | _ -> failwith "setintersect func: invalid set")
  | _ -> failwith "setintersect func: invalid type: (set * set * list) was expected";;


(* definizione dell'interprete del linguaggio *)
let rec eval (e : exp) (s : evT env) = match e with
  | CstInt n -> Int n
  | CstBool b -> Bool b
  | CstStr t -> String t
  | Sum(e1,e2) -> int_plus((eval e1 s), (eval e2 s))
  | Times(e1,e2) -> int_times((eval e1 s), (eval e2 s))
  | Sub(e1,e2) -> int_sub((eval e1 s), (eval e2 s))
  | Iszero e -> is_zero(eval e s)
  | Isnotzero e -> is_not_zero(eval e s)
  | StrCmp(e1,e2) -> str_cmp((eval e1 s), (eval e2 s))
  | Eq(e1,e2) -> int_eq((eval e1 s), (eval e2 s))
  | And(e1,e2) -> bool_and((eval e1 s), (eval e2 s))
  | Or(e1,e2) -> bool_or((eval e1 s), (eval e2 s))
  | Not(e) -> bool_not(eval e s)
  | Ifthenelse(e1,e2,e3) -> let g=eval e1 s in (match (typecheck("bool", g), g) with
      | (true, Bool(true)) -> eval e2 s
      | (true, Bool(false)) -> eval e3 s
      | _ -> failwith "if-then-else: invalid type: boolean guard was expected")
  | Let(ename, expVal, letbody) -> eval letbody (bind s ename (eval expVal s))
  | Letrec(fname, recFunVal, letbody) -> eval letbody (bind s fname (eval recFunVal s))
  | Den i -> lookup s i
  | Fun(arg, fbody) -> Closure(arg, fbody, s)
  | RecFun(fname, arg, fbody) -> RecClosure(fname, arg, fbody, s)
  | Apply(f, eArg) -> let fclosure = eval f s in (match fclosure with
      | Closure(arg, fbody, fDeclEnv) -> let argVal = eval eArg s in
          let nEnv = bind fDeclEnv arg argVal in eval fbody nEnv
      | RecClosure(f, arg, fbody, fDeclEnv) -> let argVal = eval eArg s in
          let recEnv = bind fDeclEnv f fclosure in let nEnv = bind recEnv arg argVal in eval fbody nEnv
      | _ -> failwith "function application: functional type was expected")
  | EList(el) -> (match el with
      | EEmptyList -> eval el s
      | EListElem(_) -> eval el s
      | _ when (typecheck("primitive", eval el s)) -> List(eval (EListElem(el, EEmptyList)) s)
      | _ -> failwith "list creation: invalid type: primitive type was expected")
  | EEmptyList -> List(EmptyList)
  | EListElem(el, ls) -> cons (eval el s) (eval ls s)
  | Empty(d) -> (match d with
      | Int -> IntSet(EmptySet)
      | String -> StringSet(EmptySet))
  | Singleton(el, d) -> (match (el, d) with
      | (CstInt(n), Int) -> IntSet(SetElem(IntSet(EmptySet), (eval el s), IntSet(EmptySet)))
      | (CstStr(t), String) -> StringSet(SetElem(StringSet(EmptySet), (eval el s), StringSet(EmptySet)))
      | _ -> failwith "evalset (singleton): invalid set type")
  | Of(d, ls) -> (match (d, ls) with
      | (Int, EList(EEmptyList)) -> IntSet(EmptySet)
      | (Int, EList(EListElem(CstInt(n), xs))) -> setfromlist (eval ls s) (IntSet(EmptySet))
      | (String, EList(EEmptyList)) -> StringSet(EmptySet)
      | (String, EList(EListElem(CstStr(t), xs))) -> setfromlist (eval ls s) (StringSet(EmptySet))
      | _ -> failwith "evalset (of): invalid set type")
  | SetSearch(el, set) -> setsearch (eval el s) (eval set s)
  | SetInsert(el, set) -> setinsert (eval el s) (eval set s)
  | SetRemove(el, set) -> setremove (eval el s) (eval set s)
  | SetIsEmpty(set) -> setisempty (eval set s)
  | SetMax(set) -> setmax (eval set s)
  | SetMin(set) -> setmin (eval set s)
  | SetUnion(s1, s2) -> let i1 = eval s1 s in let i2 = eval s2 s in
      (match (i1, i2) with
          | (IntSet(_), IntSet(_)) ->
                setfromlist (listfromset (i1) (listfromset (i2) (List(EmptyList)))) (IntSet(EmptySet))
          | (StringSet(_), StringSet(_)) ->
                setfromlist (listfromset (i1) (listfromset (i2) (List(EmptyList)))) (StringSet(EmptySet))
          | _ -> failwith "union: invalid set type: expected (set * set) of same type")
  | SetIntersection(s1, s2) -> let i1 = eval s1 s in let i2 = eval s2 s in
      (match (i1, i2) with
          | (IntSet(_), IntSet(_)) ->
                setfromlist (setintersect (i1) (i2) (List(EmptyList))) (IntSet(EmptySet))
          | (StringSet(_), StringSet(_)) ->
                setfromlist (setintersect (i1) (i2) (List(EmptyList))) (StringSet(EmptySet))
          | _ -> failwith "intersection: invalid set type: expected (set * set) of same type")
  | SetDifference(s1, s2) -> let i1 = eval s1 s in let i2 = eval s2 s in
      (match (i1, i2) with
          | (IntSet(_), IntSet(_)) ->
                setremovefromlist i1 (listfromset i2 (List(EmptyList)))
          | (StringSet(_), StringSet(_)) ->
                setremovefromlist i1 (listfromset i2 (List(EmptyList)))
          | _ -> failwith "difference: invalid set type: expected (set * set) of same type")
  | SetIsSubSet(s1, s2) -> setissubset (eval s1 s) (eval s2 s) (Bool(true))
  | SetFilter(p, set) -> let fc = eval p s in let i = eval set s in (match (fc, i) with
      | (Closure(_), IntSet(_)) -> setfromlist (setfilt fc i (List(EmptyList)) s) (IntSet(EmptySet))
      | (Closure(_), StringSet(_)) -> setfromlist (setfilt fc i (List(EmptyList)) s) (StringSet(EmptySet))
      | _ -> failwith "filter: invalid type: valid predicate and set expected")
  | SetMap(f, set) -> let fc = eval f s in let i = eval set s in (match fc with
      | Closure(_) -> setmap fc i s
      | _ -> failwith "map: invalid type: functional value expected")
  | SetForAll(p, set) -> let fc = eval p s in let i = eval set s in (match fc with
      | Closure(_) -> forall fc i (Bool(true)) s
      | _ -> failwith "forall: invalid type: valid predicate expected")
  | SetExists(p, set) -> let fc = eval p s in let i = eval set s in (match fc with
      | Closure(_) -> exists fc i (Bool(false)) s
      | _ -> failwith "exists: invalid type: valid predicate expected")
  | _ -> failwith "in eval: invalid expression"

(* filter su insiemi *)
and setfilt (p:evT) (set:evT) (ls:evT) (env:evT env) : (evT) = match set with
  | IntSet(_) -> (match set with
      | IntSet(EmptySet) -> ls
      | IntSet(SetElem(lt, el, rt)) -> if ((app p el env) = (Bool(true)))
          then (List(Cons(el, (concat (setfilt p lt ls env) (setfilt p rt ls env)))))
          else (concat (setfilt p lt ls env) (setfilt p rt ls env))
      | _ -> failwith "setfilt func: invalid int set")
  | StringSet(_) -> (match set with
      | StringSet(EmptySet) -> ls
      | StringSet(SetElem(lt, el, rt)) -> if ((app p el env) = (Bool(true)))
          then (List(Cons(el, (concat (setfilt p lt ls env) (setfilt p rt ls env)))))
          else (concat (setfilt p lt ls env) (setfilt p rt ls env))
      | _ -> failwith "setfilt func: invalid string set")
  | _ -> failwith "setfilt func: invalid type: set was expected"

and setmap (f:evT) (set:evT) (env:evT env) : (evT) = match set with
  | IntSet(_) -> (match set with
      | IntSet(EmptySet) -> set
      | IntSet(SetElem(lt, el, rt)) -> IntSet(SetElem(setmap f lt env, app f el env, setmap f rt env))
      | _ -> failwith "setmap func: invalid intset")
  | StringSet(_) -> (match set with
      | StringSet(EmptySet) -> set
      | StringSet(SetElem(lt, el, rt)) -> StringSet(SetElem(setmap f lt env, app f el env, setmap f rt env))
      | _ -> failwith "setmap func: invalid stringset")
  | _ -> failwith "setmap func: invalid type: type set expected"

and forall (p:evT) (set:evT) (b:evT) (env:evT env) : (evT) = match set with
  | IntSet(_) -> (match set with
      | IntSet(EmptySet) -> b
      | IntSet(SetElem(lt, el, rt)) -> if (app p el env) = (Bool(true))
          then (bool_and(forall p lt b env, forall p rt b env))
          else (Bool(false))
      | _ -> failwith "forall func: invalid intset")
  | StringSet(_) -> (match set with
      | StringSet(EmptySet) -> b
      | StringSet(SetElem(lt, el, rt)) -> if (app p el env) = (Bool(true))
          then (bool_and(forall p lt b env, forall p rt b env))
          else (Bool(false))
      | _ -> failwith "forall func: invalid stringset")
  | _ -> failwith "forall func: invalid type: set was expected"

and exists (p:evT) (set:evT) (b:evT) (env:evT env) : (evT) = match set with
  | IntSet(_) -> (match set with
      | IntSet(EmptySet) -> b
      | IntSet(SetElem(lt, el, rt)) -> if (app p el env) = (Bool(true))
          then (Bool(true))
          else (bool_or(exists p lt b env, exists p rt b env))
      | _ -> failwith "exists func: invalid intset")
  | StringSet(_) -> (match set with
      | StringSet(EmptySet) -> b
      | StringSet(SetElem(lt, el, rt)) -> if (app p el env) = (Bool(true))
          then (Bool(true))
          else (bool_or(exists p lt b env, exists p rt b env))
      | _ -> failwith "exists func: invalid stringset")
  | _ -> failwith "exists func: invalid type: set was expected"

(* applica una funzione ad un parametro *)
and app (fclosure:evT) (argVal:evT) (env:evT env) : (evT) = match fclosure with
    | Closure(arg, fbody, fDeclEnv) ->
        let nEnv = bind fDeclEnv arg argVal in eval fbody nEnv
    | RecClosure(f, arg, fbody, fDeclEnv) ->
        let recEnv = bind fDeclEnv f fclosure in let nEnv = bind recEnv arg argVal in eval fbody nEnv
    | _ -> failwith "function application: functional type was expected";;

(* ######################### ESPRESSIONI DI ESEMPIO ######################### *)

(* creazione insieme vuoto *)
let s1 = Empty(Int);;
let v1 = eval s1 [];;

let s2 = Empty(String);;
let v2 = eval s2 [];;

(* creazione insieme singoletto *)
let s3 = Singleton(CstInt(4), Int);;
let v3 = eval s3 [];;

let s4 = Singleton(CstStr("Quattro"), String);;
let v4 = eval s4 [];;

(* creazione insieme da una lista *)
let l1 = EList(EListElem(CstInt(2), EList(EListElem(CstInt(3), EList(EEmptyList)))));;
let lv1 = eval l1 [];;
let s5 = Of(Int, l1);;
let v5 = eval s5 [];;

let l2 = EList(EListElem(CstStr("Uno"), EList(EListElem(CstStr("Due"), EList(EEmptyList)))));;
let lv2 = eval l2 [];;
let s6 = Of(String, l2);;
let v6 = eval s6 [];;

(* inserimento in insieme *)
let s7 = SetInsert(CstInt(1), s5);;
let v7 = eval s7 [];;

let s8 = SetInsert(CstStr("Tre"), s6);;
let v8 = eval s8 [];;

(* ricerca su insieme *)
let s9 = SetSearch(CstInt(2), s7);;
let v9 = eval s9 [];;

let s10 = SetSearch(CstStr("Due"), s8);;
let v10 = eval s10 [];;

(* rimozione da insieme *)
let s11 = SetRemove(CstInt(3), s7);;
let v11 = eval s11 [];;

let s12 = SetRemove(CstStr("Tre"), s8);;
let v12 = eval s12 [];;

(* controllo su insieme vuoto sì/no *)
let s13 = SetIsEmpty(s7);;
let v13 = eval s13 [];;

let s14 = SetIsEmpty(s8);;
let v14 = eval s14 [];;

(* massimo di un insieme *)
let s15 = SetMax(s7);;
let v15 = eval s15 [];;

let s16 = SetMax(s8);;
let v16 = eval s16 [];;

(* minimo di un insieme *)
let s17 = SetMin(s7);;
let v17 = eval s17 [];;

let s18 = SetMin(s8);;
let v18 = eval s18 [];;

(* unione fra insiemi *)
let s19 = SetUnion(s3, s7);;
let v19 = eval s19 [];;

let s20 = SetUnion(s4, s8);;
let v20 = eval s20 [];;

(* intersezione fra insiemi *)
let s21 = SetIntersection(s5, s7);;
let v21 = eval s21 [];;

let s22= SetIntersection(s6, s8);;
let v22 = eval s22 [];;

(* inclusione fra insiemi *)
let s23 = SetIsSubSet(s5, s7);;
let v23 = eval s23 [];;

let s24 = SetIsSubSet(s6, s8);;
let v24 = eval s24 [];;

(* filter su insiemi *)
let p1 = Fun("x", Iszero(Den("x")));;
let filt1 = SetFilter(p1, s7);;
let pv1 = eval filt1 [];;

let p2 = Fun("x", Isnotzero(Den("x")));;
let filt2 = SetFilter(p2, s7);;
let pv2 = eval filt2 [];;

let p3 = Fun("x", StrCmp(Den("x"), CstStr("Uno")));;
let filt3 = SetFilter(p3, s8);;
let pv3 = eval filt3 [];;

(* map su insiemi *)
let f1 = Fun("x", Sum(Den("x"), CstInt(1)));;
let map1 = SetMap(f1, s7);;
let fv1 = eval map1 [];;

let f2 = Fun("x", Times(Den("x"), CstInt(2)));;
let map2 = SetMap(f2, s7);;
let fv2 = eval map2 [];;

(* forall su insiemi *)
let fa1 = Fun("x", Iszero(Den("x")));;
let forall1 = SetForAll(fa1, s7);;
let fav1 = eval forall1 [];;

let fa2 = Fun("x", Isnotzero(Den("x")));;
let forall2 = SetForAll(fa2, s7);;
let fav2 = eval forall2 [];;

let fa3 = Fun("x", StrCmp(Den("x"), CstStr("Uno")));;
let forall3 = SetForAll(fa3, s8);;
let fav3 = eval forall3 [];;

(* exists su insiemi *)
let e1 = Fun("x", Iszero(Den("x")));;
let ex1 = SetExists(e1, s7);;
let ev1 = eval ex1 [];;

let e2 = Fun("x", Isnotzero(Den("x")));;
let ex2 = SetExists(e2, s7);;
let ev2 = eval ex2 [];;

let e3 = Fun("x", StrCmp(Den("x"), CstStr("Uno")));;
let ex3 = SetExists(e3, s8);;
let ev3 = eval ex3 [];;
