(*++++++++++++++++++++++++++++++++++++++*)
(*  Interpretador para L1               *)
(*  - inferência de tipos (monomórfica  *)
(*  - avaliador big step com ambiente   *)
(*++++++++++++++++++++++++++++++++++++++*)


(**+++++++++++++++++++++++++++++++++++++++++*)
(*  SINTAXE, AMBIENTE de TIPOS e de VALORES *)
(*++++++++++++++++++++++++++++++++++++++++++*)

(* tipos da linguagem L1 *)

type tipo =
    TyInt
  | TyBool
  | TyFn of tipo * tipo
  | TyPair of tipo * tipo 
  | TyRef of tipo
  | TyUnit
  
  
(* expressões da linguagem L1 *)

type ident = string 

type op = Sum | Sub | Mult | Eq | Gt | Lt | Geq | Leq

type expr =
  | Num of int
  | Var of ident
  | Bcte of bool
  | Binop of op * expr * expr
  | Pair of expr * expr
  | Fst of expr
  | Snd of expr
  | If of expr * expr * expr
  | Fn of ident * tipo * expr
  | App of expr * expr
  | Let of ident * tipo * expr * expr
  | LetRec of ident * tipo * expr  * expr
                (* extensoes *) 
  | Dolar of expr * expr 
  | Question of expr * expr * expr
  | Pipe of expr * expr
  | Asg of expr * expr
  | Dref of expr
  | New of expr
  | Seq of expr * expr
  | Whl of expr * expr 
  | Skip of unit

            

  
 (* ambiente de tipo, valores e ambiente de execução *)              

type tenv = (ident * tipo) list 
    
type mem = (int * tipo) list
    
type valor =
    VNum of int
  | VBool of bool
  | VPair of valor * valor
  | VClos  of ident * expr * renv
  | VRclos of ident * ident * expr * renv
and 
  renv = (ident * valor) list 
and
  mem = (int * valor) list 
  
 
    (* funções de busca e de atualização de ambientes *)   


let rec lookup a k  =
  match a with
    [] -> None
  | (y,i) :: tl -> if (y=k) then Some i else lookup tl k 
       
let  update a k i = (k,i) :: a  

(* NEW *)
let rec findLastKey mem k =
  match mem with
    [] -> k
  | (y, i) :: tl -> findLastKey mem k+1

let rec allocate mem k v = (findLastKey mem k, v) :: mem

let rec updateMem mem1 mem2 e1 e2 = 
  match mem2 with
   (k, v)::tl -> if k = e1 then mem1::mem2 else updateMem mem1::(k,v) tl e1 e2
  
(**+++++++++++++++++++++++++++++++++++++++++*)
(*         INFERÊNCIA DE TIPOS              *)
(*++++++++++++++++++++++++++++++++++++++++++*)

(* exceções que não devem ocorrer  *) 

exception BugParser
  
exception BugTypeInfer 
                       
(* exceções para usuário da linguagem L1 *)

exception TypeError of string


let rec typeinfer (tenv:tenv) (e:expr) : tipo =
  match e with

    (* TInt  *)
  | Num _ -> TyInt

    (* TVar *)
  | Var x ->
      (match lookup tenv x with
         Some t -> t
       | None -> raise (TypeError ("variavel nao declarada:" ^ x)))

    (* TBool *)
  | Bcte _ -> TyBool 

    (* Top+ e outros operadores binários *)
  | Binop(oper,e1,e2) ->  
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in 
      (match (t1,t2) with
         (TyInt, TyInt) -> 
           (match oper with 
              Sum | Sub | Mult         ->  TyInt
            | Eq | Gt | Lt | Geq | Leq ->  TyBool)
       | _ -> raise (TypeError "pelo menos um ds operandos de operador binário não é do tipo int"))

  (* TPair *)
  | Pair(e1,e2) -> 
      let t1 = typeinfer tenv e1 in 
      let t2 = typeinfer tenv e2 in
      TyPair(t1,t2)
 
  (* TFst *)
  | Fst e1 ->
      let t1 = typeinfer tenv e1 in 
      (match t1 with
         TyPair(t,_) -> t
       | _           -> raise (TypeError "fst espera tipo par ordenado"))
  
  (* TSnd  *)
  | Snd e1 ->
      let t1 = typeinfer tenv e1 in
      (match t1 with
         TyPair(_,t) -> t
       | _           -> raise (TypeError "snd espera tipo par ordenado"))

    (* TIf  *)
  | If(e1,e2,e3) ->
      let t1 = typeinfer tenv e1 in 
      (match t1 with
         TyBool ->
           let t2 = typeinfer tenv e2 in
           let t3 = typeinfer tenv e3
           in if t2 = t3 then t2
           else raise (TypeError "then/else com tipos diferentes")
       | _     -> raise (TypeError "condição de IF não é do tipo bool"))

    (* TFn *)
  | Fn(x,t,e1) ->
      let t1 = typeinfer (update tenv x t) e1
      in TyFn(t,t1)

    (* TApp *)
  | App(e1,e2) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in 
      (match t1 with
         TyFn(t_in, t_out) ->  
           if t2 = t_in then t_out
           else raise (TypeError "tipo argumento errado" )
       | _ -> raise (TypeError "tipo função era esperado"))

    (* TLet *)
  | Let(x,t,e1,e2) ->
      if (typeinfer tenv e1) = t then typeinfer (update tenv x t) e2
      else raise (TypeError "expr nao é do tipo declarado em Let" )

    (* TLetRec *)
  | LetRec(f,(TyFn(t1,t2) as tf), Fn(x,tx,e1), e2) ->
      let tenv_com_tf = update tenv f tf in
      let tenv_com_tf_tx = update tenv_com_tf x tx in
      if (typeinfer tenv_com_tf_tx e1) = t2
      then typeinfer tenv_com_tf e2
      else raise (TypeError "tipo da funcao diferente do declarado")
          
  | LetRec _ -> raise BugParser
                  
                  (* extensões *)

  | Dolar(e1,e2) ->  
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in 
      (match (t1, t2) with 
         (TyBool, TyInt) -> TyInt
       | _ -> raise (TypeError "pelo menos 1 dos operandos do operador $ está mal tipado" ))
                       
  | Question(e1,e2,e3) ->
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in
      let t3 = typeinfer tenv e3 in 
      (match (t1, t2, t3) with 
         (TyInt, TyBool, TyBool) -> TyBool
       | _ -> raise (TypeError "pelo menos 1 dos operandos do operador ? está mal tipado" ))
    
    
  | Pipe(e1,e2) -> 
      let t1 = typeinfer tenv e1 in
      let t2 = typeinfer tenv e2 in 
      (match t2 with 
         TyFn(t_in,t_out) ->  
           if t1 = t_in then t_out 
           else raise (TypeError "tipo de entrada da função diferente do tipo do argumento") 
       | _ -> raise (TypeError "1.o operando do pipe não é do tipo esperado pelo 2.o operando do pipe" ))
      
  | Skip -> TyUnit 
  
  | Asg (e1, e2) -> 
      let t1 = typeinfer tenv e1 in 
      let t2 = typeinfer tenv e2 in
      (match t1 with
         TyRef(t_in) ->
           if t2 = t_in then TyUnit
           else raise (TypeError "tipo de ref do primeiro argumento diferente do segundo argumento")
       | _ -> raise (TypeError "primeiro operando não é ref"))

           
  | Dref (e1) -> 
      let t1 = typeinfer tenv e1 in
      (match t1 with
         TyRef(t_in) -> t_in
       | _ -> raise (TypeError "argumento não é uma referência")) 
      
  | New (e1) ->
      let t1 = typeinfer tenv e1 
      in TyRef(t1)
        
  | Seq (e1, e2) ->
      let t1 = typeinfer tenv e1 in 
      let t2 = typeinfer tenv e2 in
      (match t1 with
         TyUnit -> t2
       | _ -> raise (TypeError "primeiro operando não é do tipo unit"))

  | Whl (e1, e2) -> 
      let t1 = typeinfer tenv e1 in 
      let t2 = typeinfer tenv e2 in
      (match t1 with
         TyBool -> 
           if t2 = TyUnit then t2
           else raise (TypeError "segundo argumento não é do tipo unit")
       | _ -> raise (TypeError "primeiro operando não é do tipo bool"))
      
(**+++++++++++++++++++++++++++++++++++++++++*)
(*                 AVALIADOR                *)
(*++++++++++++++++++++++++++++++++++++++++++*)




let rec compute (oper: op) (v1: valor) (v2: valor) : valor =
  match (oper, v1, v2) with
  
    (* operadores aritméticos com números *)
    (Sum,  VNum n1, VNum n2) -> VNum (n1 + n2)
  | (Sub,  VNum n1, VNum n2) -> VNum (n1 - n2)
  | (Mult, VNum n1, VNum n2) -> VNum (n1 * n2) 
                                                
    (* operadores relacionais com números *)
  | (Eq, VNum n1, VNum n2) -> VBool( n1 = n2) 
  | (Gt, VNum n1, VNum n2) -> VBool( n1 > n2)
  | (Lt, VNum n1, VNum n2) -> VBool( n1 < n2)
  | (Geq,VNum n1, VNum n2) -> VBool( n1 >= n2)
  | (Leq,VNum n1, VNum n2) -> VBool( n1 <= n2) 
                                
  | _ -> raise BugTypeInfer



let rec eval (renv:renv) (mem:mem) (e:expr) : valor =
  match e with
    Num n -> VNum n
               
  | Bcte b -> VBool b 

  | Var x ->
      (match lookup renv x with
         Some v -> v
       | None -> raise BugTypeInfer)
      
  | Binop(oper,e1,e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      compute oper v1 v2

  | Pair(e1,e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2
      in VPair(v1,v2)

  | Fst e ->
      (match eval renv e with
       | VPair(v1,_) -> v1
       | _ -> raise BugTypeInfer)

  | Snd e ->
      (match eval renv e with
       | VPair(_,v2) -> v2
       | _ -> raise BugTypeInfer)


  | If(e1,e2,e3) ->
      (match eval renv e1 with
         VBool true  -> eval renv e2
       | VBool false -> eval renv e3
       | _ -> raise BugTypeInfer )

  | Fn (x,_,e1) ->  VClos(x,e1,renv)

  | App(e1,e2) ->
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      (match v1 with
         VClos(x,ebdy,renv') ->
           let renv'' = update renv' x v2
           in eval renv'' ebdy

       | VRclos(f,x,ebdy,renv') ->
           let renv''  = update renv' x v2 in
           let renv''' = update renv'' f v1
           in eval renv''' ebdy
       | _ -> raise BugTypeInfer)

  | Let(x,_,e1,e2) ->
      let v1 = eval renv e1
      in eval (update renv x v1) e2

  | LetRec(f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
      let renv'= update renv f (VRclos(f,x,e1,renv))
      in eval renv' e2
        
        
  | LetRec _ -> raise BugParser 
                  
                  (* extensões *)

  | Dolar(e1,e2) -> 
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in 
      (match (v1,v2) with 
         (VBool true,  VNum n) -> VNum (n + 1)
       | (VBool false, VNum n) -> VNum (n - 1)
       | _ -> raise BugTypeInfer)
                       
                       
  | Question(e1,e2,e3) -> 
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in
      let v3 = eval renv e3 in
      (match (v1,v2,v3) with 
         (VNum 0, VBool b1, VBool b2) -> VBool (b1 && b2)
       | (VNum _, VBool b1, VBool b2) -> VBool (b1 || b2)
       | _ -> raise BugTypeInfer)
          
  | Pipe(e1,e2) -> 
      let v1 = eval renv e1 in
      let v2 = eval renv e2 in 
      (match v2 with 
         VClos(x,e,renv')    -> 
           eval  (update renv' x v1) e
       | VRclos(f,x,e,renv') -> 
           let renv'' =  update renv' x v1 in
           eval  (update  renv'' f v2) e 
       | _ -> raise BugTypeInfer)
      
  | Skip() -> unit

  | Asg(e1, e2) ->
    let exists = lookup mem e1
    let t1 = typeinfer [] exists in
    let t2 = typeinfer [] e2 in
    (match t1 with
      None -> raise (TypeError ("lista vazia, tentando atualizar valor inexistente"))
      | t2 -> Skip(updateMem [] mem e1 e2) 
      | _ -> raise BugTypeInfer)


  | Deref(e1) -> 
      (match lookup mem e1 with
       Some t -> t
     | None -> raise (TypeError ("variavel nao declarada:" ^ x)))  (* arrumar o tipo do erro *)
    
  | New(e1) -> allocate mem e1 0

      
      
  | _ -> raise BugTypeInfer
      
                  
                  
(* função auxiliar que converte tipo para string *)

let rec ttos (t:tipo) : string =
  match t with
    TyInt  -> "int"
  | TyBool -> "bool"
  | TyFn(t1,t2)   ->  "("  ^ (ttos t1) ^ " --> " ^ (ttos t2) ^ ")"
  | TyPair(t1,t2) ->  "("  ^ (ttos t1) ^ " * "   ^ (ttos t2) ^ ")"
  | _ -> raise BugTypeInfer

(* função auxiliar que converte valor para string *)

let rec vtos (v: valor) : string =
  match v with
    VNum n -> string_of_int n
  | VBool b -> string_of_bool b 
  | VPair(v1, v2) ->
      "(" ^ vtos v1 ^ "," ^ vtos v1 ^ ")"
  | VClos _ ->  "fn"
  | VRclos _ -> "fn"

(* principal do interpretador *)

let int_bse (e:expr) : unit =
  try
    let t = typeinfer [] e in
    let v = eval [] e
    in  print_string ((vtos v) ^ " : " ^ (ttos t))
  with
    TypeError msg ->  print_string ("erro de tipo - " ^ msg)
   
 (* as exceções abaixo nao devem ocorrer   *)
  | BugTypeInfer  ->  print_string "corrigir bug em typeinfer"
  | BugParser     ->  print_string "corrigir bug no parser para let rec"
                        



 (* +++++++++++++++++++++++++++++++++++++++*)
 (*                TESTES                  *)
 (*++++++++++++++++++++++++++++++++++++++++*)

let test_env = [("y", VNum 10)]

(*
     let x:int = 2 
     in let foo: int --> int = fn y:int => x + y 
        in let x: int = 5
           in foo 10 
           
    do tipo int , avalia para 12 
*)

let e'' = Let("x", TyInt, Num 5, App(Var "foo", Num 10))

let e'  = Let("foo", TyFn(TyInt,TyInt), Fn("y", TyInt, Binop(Sum, Var "x", Var "y")), e'')

let tst = Let("x", TyInt, Num(2), e') 
    
    (*
     let x:int = 2 
     in let foo: int --> int = fn y:int => x + y 
        in let x: int = 5
           in foo 
           
      do tipo int --> int avalia para uma função 
*)


let e2 = Let("x", TyInt, Num 5, Var "foo")

let e1  = Let("foo", TyFn(TyInt,TyInt), Fn("y", TyInt, Binop(Sum, Var "x", Var "y")), e2)

let tst2 = Let("x", TyInt, Num(2), e1) 


  
    (* let x:int = 10
       in let f: int --> int = fn y:int => y + x
          in let x:int  = 25
             in f 100
           
     do tipo int avalia para 110 
*)

let e3 = Let("x", TyInt, Num 25, App(Var "f", Num 100))
            
let e2 = Let("f", TyFn(TyInt,TyInt), Fn("y", TyInt, Binop(Sum, Var "y", Var "x")), e3)
            
let tst3 = Let("x", TyInt, Num 10, e2) 
    
  


  (*   com acúcar sintático:

   let rec pow (x:int) (y:int) : int = 
                  if y = 0 then 1 else x * (pow x (y-1))  
   in (pow 3) 4 
     
     sem açucar sintático:

   let rec pow: int -> (int --> int) = 
          fn x:int => fn y:int => if y = 0 then 1 else x * (pow x (y-1)) 
in (pow 3) 4 
     
do tipo int avalia para  81

*)          

let ymenos1 = Binop(Sub, Var "y", Num 1)     (* y - 1  *)
  
let powapp  =   App(App(Var "pow", Var "x"), ymenos1)   (* (pow x)  (y-1) *)
                                           
let xpow =   Binop(Mult, Var "x", powapp)    (*   x * (pow x (y-1))   *)
      
    (* fn y:int => if y=0 then 1 else x * (pow x (y-1))    *) 
let ebdy = Fn("y",
              TyInt,
              If(Binop(Eq, Var "y", Num 0) , Num 1, xpow))  
  
let pow = 
  LetRec("pow", 
         TyFn(TyInt, TyFn(TyInt,TyInt)), (* pow: int --> int --> int*)
         Fn("x", TyInt, ebdy),           (* fn x: int => ebdy  *)
         App(App(Var "pow", Num 3), Num 4)) (* in  (pow 3) 4    *)
                                            
                                            
  
    (*  5 |> inc 
        do tipo int avalia para 6   *)


let dobro = Fn("y", TyInt, Binop(Mult, Var "y", Num 2)) 
    
let inc = Fn("y", TyInt, Binop(Sum, Var "y", Num 1)) 

let pipe1 =     Pipe(Num 5, inc)
    
    (* inc (inc (dobro (dobro (inc (inc (inc 5))))))  =  34     
                                                              
    5 |> inc |> inc |> inc |> dobro |> dobro |> inc |> inc  
     
      do tipo int avalia para 34 *)
    
let pipe2 =  
  Pipe(Pipe(Pipe(Pipe(Pipe(Pipe(Pipe(Num 5, inc), inc), inc), dobro),dobro), inc) , inc)
    
    (*  $ ( 6 = (5 |> inc),  pow 3 4)    é do tipo int e  avalia para 80 
*)
let tst_dolar  = Dolar(Binop(Eq, Num 20, pipe1), pow)
    
let teste1 = Let("x", TyRef TyInt, New (Num 3),
                 Let("y", TyInt, Dref (Var "x"), 
                     Seq(Asg(Var "x", Binop(Sum, Dref(Var "x"), Num 1)), 
                         Binop(Sum, Var "y",  Dref (Var "x"))))) 
    
let counter1 = Let("counter", TyRef TyInt, New (Num 0),
                   Let("next_val", TyFn(TyUnit, TyInt),
                       Fn("w", TyUnit, 
                          Seq(Asg(Var "counter",Binop(Sum, Dref(Var "counter"), Num 1)),
                              Dref (Var "counter"))),
                       Binop(Sum, App (Var "next_val", Skip), 
                             App (Var "next_val", Skip))))
    
    
    
    
