(*************************************************)
(* Turma B                                       *)
(* Carlos Eduardo Westermann - 00327212          *)
(* Luis Guilherme Fernandes Melo - 00326620      *)
(* Théo Santiago Müller - 00301593               *) 
(*************************************************)

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
  | Skip
    
            

  
 (* ambiente de tipo, valores e ambiente de execução *)              

type tenv = (ident * tipo) list 
    
(* type mem = (int * valor) list *)
    
type valor =
    VNum of int
  | VBool of bool
  | VPair of valor * valor
  | VClos  of ident * expr * renv
  | VRclos of ident * ident * expr * renv
  | VUnit 
  | VRef of int 
and 
  renv = (ident * valor ) list
and 
  mem = ( int * valor) list 
    
  
 
    (* funções de busca e de atualização de ambientes *)   


let rec lookup a k  =
  match a with
    [] -> None
  | (y,i) :: tl -> if (y=k) then Some i else lookup tl k 
       
let  update a k i = (k,i) :: a  


(* NEW FUNCTIONS *)
let  updateMem mem k v = (k,v) :: mem

let rec findLastKey mem k =
  match mem with
    [] -> k
  | (y, i) :: tl -> findLastKey tl k+1

let rec allocate mem v = 
  let lastKey = findLastKey mem 0 in (lastKey, v)::mem

let rec searchMem mem k  =
  match mem with
    [] -> None
  | (y,i) :: tl -> if (y=k) then Some i else searchMem tl k 
          
          
let rec replaceelem ls x elem =
  match ls with
  | [] -> ls
  | (y, i) :: t -> if (x = y) then
        (y, elem)::(replaceelem t x elem )
      else
        (y, i)::(replaceelem t x elem )


          (* let rec asgMem mem1 mem2 e1 e2 = 
             match mem2 with
               (k, v)::tl -> if k = e1 then mem1::mem2 else (asgMem ((k,v)::mem1) tl e1 e2) *)
  
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



let rec eval (renv:renv) (e,s:expr * mem) : (valor * mem) =
  match e with
    (Num n) -> (VNum n , s)
               
  | (Bcte b) -> (VBool b, s)

  | (Var x) ->
      (match lookup renv x with
         Some v -> (v, s)
       | None -> raise (TypeError "variavel não definida") )
      
  | (Binop(oper,e1,e2)) ->
      let (v1, s1) = eval renv (e1, s) in
      let (v2, s2) = eval renv (e2, s1) in
      (compute oper v1 v2, s2) 

  | (Pair(e1,e2)) ->
      let (v1, s1) = eval renv (e1, s)  in
      let (v2, s2) = eval renv (e2, s1) 
      in (VPair(v1,v2), s2)

  | (Fst e) ->
      (match eval renv (e , s) with
       | (VPair(v1,_), s1) -> (v1, s1)
       | _ -> raise BugTypeInfer )

  | (Snd e) ->
      (match eval renv (e , s) with
       | (VPair(_,v2), s1) -> (v2, s1)
       | _ -> raise BugTypeInfer )


  | (If(e1,e2,e3)) ->
      (match eval renv  (e1, s)  with
         (VBool true, s1)  -> eval renv (e2, s1) 
       | (VBool false, s1) -> eval renv (e3, s1) 
       | _ ->  raise BugTypeInfer)

  | (Fn (x,_,e1)) ->  (VClos(x,e1,renv), s)

  | (App(e1,e2)) ->
      let (v1, s1) = eval renv  (e1, s)  in
      let (v2, s2) = eval renv  (e2, s1)  in
      (match v1 with
         VClos(x,ebdy,renv') ->
           let renv'' = update renv' x v2
           in eval renv'' (ebdy, s2)

       | VRclos(f,x,ebdy,renv') ->
           let renv''  = update renv' x v2 in
           let renv''' = update renv'' f v1
           in eval renv''' (ebdy, s2)
       | _ -> raise BugTypeInfer)

  | (Let(x,_,e1,e2)) ->
      let (v1, s1) = eval renv  (e1, s) 
      in eval (update renv x v1)  (e2, s1) 

  | LetRec(f,TyFn(t1,t2),Fn(x,tx,e1), e2) when t1 = tx ->
      let renv'= update renv f (VRclos(f,x,e1,renv))
      in eval renv'  (e2, s) 
        
        
  | (LetRec _) -> raise BugParser 
                  
                  (* extensões *)

  | (Dolar(e1,e2)) -> 
      let (v1, s1) = eval renv  (e1, s)  in
      let (v2, s2) = eval renv  (e2, s1)  in 
      (match (v1,v2) with 
         (VBool true,  VNum n) -> (VNum (n + 1), s2)
       | (VBool false, VNum n) -> (VNum (n - 1), s2)
       | _ -> raise BugTypeInfer)
                       
                       
  | (Question(e1,e2,e3)) -> 
      let (v1, s1) = eval renv  (e1, s)  in
      let (v2, s2) = eval renv  (e2, s1)  in
      let (v3, s3) = eval renv  (e3, s2)  in
      (match (v1,v2,v3) with 
         (VNum 0, VBool b1, VBool b2) -> (VBool (b1 && b2), s3)
       | (VNum _, VBool b1, VBool b2) -> (VBool (b1 || b2), s3)
       | _ -> raise BugTypeInfer)
          
  | (Pipe(e1,e2)) -> 
      let (v1, s1) = eval renv  (e1, s)  in
      let (v2, s2) = eval renv  (e2, s1)  in 
      (match v2 with 
         VClos(x,e,renv') -> 
           eval  (update renv' x v1) (e, s2)       
       | VRclos(f,x,e,renv') -> 
           let renv'' =  update renv' x v1 in
           eval  (update  renv'' f v2)  (e , s2) 
       | _ -> raise BugTypeInfer)
      
  | (Skip) -> (VUnit, s)
    
  | (Seq(e1, e2)) -> 
      let (v1, s1) = eval renv  (e1, s)  in
      let (v2, s2) = eval renv  (e2, s1)  in 
      (match v1 with 
         VUnit -> (v2, s2)
       | _ -> raise BugTypeInfer)
      
  | (Whl(e1, e2)) -> 
      eval renv (If(e1,(Seq(e2, Whl(e1, e2))),Skip), s)
  

  | New(e1) -> 
      let (v1, s1) = eval renv (e1, s) in 
      (match s1 with
         [] -> (VRef 0 , (0, v1)::s1)
       | (l,v)::tl ->
           let lnew  = l+1 in
           (VRef lnew, (lnew, v1)::s1)) 
      
  | Asg(e1, e2) ->
      let (v1, s1) = eval renv (e1,s) in
      let (v2,s2) = eval renv (e2,s1) in
      (match v1 with 
         VRef l -> 
           let s3 = replaceelem s2 l v2 in 
           (VUnit, s3)
       | _ ->  raise BugTypeInfer )


  | Dref(e1) ->
      let (v1, s1) = eval renv (e1, s) in 
      (match v1 with 
         VRef k ->
           (match searchMem s1 k with 
              Some v -> (v, s1)
            | None -> raise BugTypeInfer)
       | _ -> raise BugTypeInfer )
  
      
(* função auxiliar que converte tipo para string *)

let rec ttos (t:tipo) : string =
  match t with
    TyInt  -> "int"
  | TyBool -> "bool"
  | TyFn(t1,t2)   ->  "("  ^ (ttos t1) ^ " --> " ^ (ttos t2) ^ ")"
  | TyPair(t1,t2) ->  "("  ^ (ttos t1) ^ " * "   ^ (ttos t2) ^ ")"
  | TyRef(t1) -> "ref to " ^ (ttos t1)
  | TyUnit -> "unit"
    

(* função auxiliar que converte valor para string *)

let rec vtos (v: valor) : string =
  match v with
    VNum n -> string_of_int n
  | VBool b -> string_of_bool b 
  | VPair(v1, v2) ->
      "(" ^ vtos v1 ^ "," ^ vtos v1 ^ ")"
  | VClos _ ->  "fn"
  | VRclos _ -> "fn"
  | VRef n -> "idx of ref: " ^ string_of_int n
  | VUnit -> "unit"
    
let rec mtos (s: mem) : string =
  match s with 
    [] -> "" 
  | ((k, v)::tl) -> "(" ^(vtos (VNum k)) ^ ", " ^ (vtos v) ^ ")" ^ " :: " ^ (mtos tl) 

(* principal do interpretador *)

let int_bse (e:expr) : unit =
  try
    let t = typeinfer [] e in
    let (v, s1) = eval [] (e, []) 
    in  print_string ((vtos v) ^ " : " ^ (ttos t) ^ "  ---  memória:" ^ mtos(s1))
  with
    TypeError msg -> print_string ("erro de tipo - " ^ msg)
   
 (* as exceções abaixo nao devem ocorrer   *)
  | BugTypeInfer  ->  print_string "corrigir bug em typeinfer"
  | BugParser     ->  print_string "corrigir bug no parser para let rec"

 (* +++++++++++++++++++++++++++++++++++++++*)
 (*                TESTES                  *)
 (*++++++++++++++++++++++++++++++++++++++++*)


  
    (*  o programa abaixo retorna
        valor   = 7 
        memória = [(l1, 4)] 
    
    let x : int ref = new 3 in  -- x = end 1; 
    let y : int = !x in  --  y = 3
        (x := !x + 1);   -- 
        y + !x
*)
   
   
let teste1 = Let("x", TyRef TyInt, New (Num 3),
                 Let("y", TyInt, Dref (Var "x"), 
                     Seq(Asg(Var "x", Binop(Sum, Dref(Var "x"), Num 1)), 
                         Binop(Sum, Var "y",  Dref (Var "x"))))) 
     
   
    (*
        o programa abaixo retorna
        valor   = 1 
        memória = [(l1, 1)] 

     let x: int ref  = new 0 in
     let y: int ref  = x in
        x := 1;
        !y
    *)
    
    
let teste2 = Let("x", TyRef TyInt, New (Num 0),
                 Let("y", TyRef TyInt, Var "x", 
                     Seq(Asg(Var "x", Num 1), 
                         Dref (Var "y"))))
    
    
    (*  o programa abaixo retorna
        valor   = 3
        memória = [(l1, 2)]
    

      let counter : int ref = new 0  in 
      let next_val : unit -> int =
         fn ():unit  =>
            counter := (!counter) + 1;
           !counter
      in  (next_val()  + next_val())  
*)
    
    
let counter1 = Let("counter", TyRef TyInt, New (Num 0),
                   Let("next_val", TyFn(TyUnit, TyInt),
                       Fn("w", TyUnit, 
                          Seq(Asg(Var "counter",Binop(Sum, Dref(Var "counter"), Num 1)),
                              Dref (Var "counter"))),
                       Binop(Sum, App (Var "next_val", Skip), 
                             App (Var "next_val", Skip))))
    
  
    

    (*   o programa abaixo retorna
     valor = 120
     memória = [(l2, 120), (l1,0) ]
     

    let fat (x:int) : int = 

        let z : int ref = new x in
        let y : int ref = new 1 in 
        
while (!z > 0) (
    y :=  !y * !z;
    z :=  !z - 1;
  );
  ! y
in
fat 5
       
       
       
  SEM açucar sintático
    
let fat : int-->int = fn x:int => 

                           let z : int ref = new x in
                           let y : int ref = new 1 in 
        
                           while (!z > 0) (
                               y :=  !y * !z;
                               z :=  !z - 1;
                             );
                             ! y
in
fat 5
       
       
*) 
    
let whilefat = Whl(Binop(Gt, Dref (Var "z"), Num 0), 
                   Seq( Asg(Var "y", Binop(Mult, Dref (Var "y"), Dref (Var "z"))), 
                        Asg(Var "z", Binop(Sub, Dref (Var "z"), Num 1)))                       
                  ) 
                               
                             
let bodyfat = Let("z", TyRef TyInt, New (Var "x"),
                  Let("y", TyRef TyInt, New (Num 1), Seq (whilefat, Dref (Var "y"))))
    
let impfat = Let("fat", TyFn(TyInt,TyInt), Fn("x", TyInt, bodyfat), App(Var "fat", Num 5))
       
  
    
    
    
