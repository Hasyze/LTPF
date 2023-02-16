#use "analyseur.ml"





(* Exercice 1.1.1 *)


(* Definition de l'ast *)


type bexp = True | False;;

type var = C of char | B of bexp;;

type whilebmoins =
| Skip
| Affect of char * var
| Seq of whilebmoins * whilebmoins
| If of var * whilebmoins * whilebmoins
| While of var * whilebmoins;;


(* Exercice 1.1.2 *)

(* Grammaire :

  boolean :      B ::= '0' | '1' 
  variable :     V ::= 'a' | 'b' | 'c' | 'd'
  affectation :  A ::= V ':=' (B | V)
  if          :  F ::= 'i' '(' V ')' '{' I '}' '{' I '}' 
  while       :  W ::= 'w' '(' V ')' '{' I '}'
  instruction :  I ::= S | F | W | A | epsilon
  sequence    :  S ::= I ';' I

 *)


(* Exercice 1.1.3 *)

(* Grammaire non récursive à gauche :

  boolean :      B ::= '0' | '1' 
  variable :     V ::= 'a' | 'b' | 'c' | 'd' 
  affectation :  A ::= V ':=' (B | V)
  if          :  F ::= 'i' '(' (V|B) ')' '{' I '}' '{' I '}' 
  while       :  W ::= 'w' '(' (V|B) ')' '{' I '}'
  instruction :  I ::= ( F | W | A ) SI
  sequence    :  SI ::=  ';' I  |  ε

 *)

(* Exercice 1.1.4 *)

(* Grammaire non récursive à gauche :

   C ::= ’0’ | ’1’
   V ::= ’a’ | ’b’ | ’c’ | ’d’
   A ::= C | V

   E ::= T SE
   SE ::= '+' T | ε
   T ::= F ST
   ST ::= '.' F | ε 
   F ::= ’!’ F | A | ’(’ E ’)’

*)



(* Exercice 1.2.1 : SN de if
  
[[expr]]s1 = true            s1->p->s2
______________________________________
      s1->if(expr) p else q->s2

[[expr]]s1 = false           s1->q->s2
______________________________________
      s1->if(expr) p else q->s2

 *)



(* Exercice 2.1.1 version analist *)

(* en commentaire car permet de faire la version ranalist mais n'est pas demandée

let estVar : (char -> bool) = fun e ->
               match e with
               | 'a' -> true
               | 'b' -> true
               | 'c' -> true
               | 'd' -> true
               | _ -> false;;

let estBool : (char -> bool) = fun e ->
  match e with
  | '0' -> true
  | '1' -> true
  | _ -> false;;

let pa_V  :  analist =  terminal_cond estVar;;

let pa_B : analist = terminal_cond estBool ;;

let pa_A : analist = fun l -> l |>
                                     pa_V --> terminal ':' --> terminal '=' --> (pa_V -| pa_B);;
let rec pa_F : analist = fun l -> l |>
                                     terminal 'i' --> terminal '(' -->  (pa_V -| pa_B) --> terminal ')'--> terminal '{' --> pa_I --> terminal '}' --> terminal '{' --> pa_I --> terminal '}'
and pa_I :  analist = fun l' -> l' |> ( pa_F -| pa_W -| pa_A ) --> pa_SI
and pa_SI :  analist = fun l'' -> l'' |> (terminal ';' --> pa_I) -| epsilon
and pa_W :  analist = fun l''' -> l''' |> terminal 'w' -->  terminal '(' --> (pa_V -| pa_B) -->  terminal ')' --> terminal '{' --> pa_I --> terminal '}';;

 *)


(* Exercice 2.1.1 version ranalist *)



let pr_V :  char ranalist = 
                                       ( terminal 'a' -+> epsilon_res 'a')
                                       +| ( terminal 'b' -+> epsilon_res 'b')
                                       +| ( terminal 'c' -+> epsilon_res 'c')
                                       +| ( terminal 'd' -+> epsilon_res 'd');;


                                                                           

let pr_B : bexp ranalist =
  (terminal '0' -+> epsilon_res True)
  +| (terminal '1' -+> epsilon_res False);;

let pr_BV : var ranalist =(pr_V ++> fun c -> epsilon_res(C(c)))
                         +|(pr_B ++> fun c -> epsilon_res (B(c))) ;;

let pr_A : whilebmoins ranalist = fun l -> l |>
                                             pr_V ++> fun v -> terminal ':' --> terminal '=' -+> pr_BV ++> fun v' -> epsilon_res (Affect (v,v'));;

let rec pr_F :  whilebmoins ranalist = fun l -> l |>
                                                  terminal 'i' --> terminal '(' -+>  pr_BV ++> fun condf -> terminal ')'--> terminal '{' -+> pr_I ++> fun i1 -> terminal '}' --> terminal '{' -+> pr_I ++> fun i2 -> terminal '}'-+> epsilon_res ( If (condf, i1, i2))
and pr_W : whilebmoins ranalist = fun l' -> l' |> terminal 'w' -->  terminal '(' -+> pr_BV ++> fun condw ->  terminal ')' --> terminal '{' -+> pr_I ++> fun w -> terminal '}'-+> epsilon_res(While(condw,w))
and pr_I : whilebmoins ranalist = fun l' -> l' |> ( pr_F +| pr_W +| pr_A ) ++> fun i1 -> ((terminal ';' -+> pr_I ++> fun i2 -> epsilon_res (Seq(i1,i2))) +| epsilon_res(Seq(i1,Skip)));;


 


(* Exercice 2.1.3 version analist *)

(* en commentaire car permet de faire la version ranalist mais n'est pas demandée

let pa_CV : char analist = pa_V -| pa_B;;

let rec pa_E : char analist = fun l -> l |>
                              pa_T --> pa_SE
and pa_SE : char analist = fun l'-> l' |>  (terminal '+' --> pa_T) -| epsilon
and pa_T : char analist = fun l''-> l''|> pa_F --> pa_ST
and pa_ST : char analist = fun l''' -> l''' |> ( terminal '.' --> pa_F ) -| epsilon
and pa_F : char analist = fun l'''' -> l'''' |> (terminal '!' --> pa_F) -| pa_CV -| (terminal '(' --> pa_E --> terminal ')');;

 *)


(* Exercice 2.1.3 version ranalist *)


type bexp = True | False;;


type var = C of char
         | B of bexp
         | Or of var * var
         | And of var * var
         | Not of var ;;

type whileb =
  | Skip
  | Affect of char * var
  | Seq of whileb * whileb
  | If of var * whileb * whileb
  | While of var * whileb;;

let pr_V :  char ranalist = 
                                       ( terminal 'a' -+> epsilon_res 'a')
                                       +| ( terminal 'b' -+> epsilon_res 'b')
                                       +| ( terminal 'c' -+> epsilon_res 'c')
                                       +| ( terminal 'd' -+> epsilon_res 'd');;

let pr_B : bexp ranalist =
  (terminal '0' -+> epsilon_res False)
  +| (terminal '1' -+> epsilon_res True);;

let pr_A : var ranalist =(pr_V ++> fun c -> epsilon_res(C(c)))
                         +|(pr_B ++> fun c -> epsilon_res (B(c))) ;;

let rec pr_E : var ranalist = fun l -> l |>
                                     pr_T ++> fun a -> ((terminal '+' -+> pr_T ++> fun b -> epsilon_res(Or(a,b))) +| (epsilon_res((a))))
and pr_T : var ranalist = fun l' -> l' |>
                                      pr_F ++> fun c -> ((terminal '.' -+> pr_F ++> fun d -> epsilon_res(And(c,d))) +| (epsilon_res(c)))
and pr_F : var ranalist = fun l'' -> l'' |>
                                          (terminal '!' -+> pr_F ++> fun e -> epsilon_res(Not(e)))
                                       +| (pr_A ++> fun f -> epsilon_res(f))
                                          +| (terminal '(' -+> pr_E ++> fun g -> terminal ')' -+> epsilon_res(g));;





let pr_BV2 : var ranalist =(pr_V ++> fun c -> epsilon_res(C(c)))
                         +|(pr_B ++> fun c -> epsilon_res (B(c))) ;;

let pr_A2 : whileb ranalist = fun l -> l |>
                                             pr_V ++> fun v -> terminal ':' --> terminal '=' -+> pr_BV2 ++> fun v' -> epsilon_res (Affect (v,v'));;

let rec pr_F2 :  whileb ranalist = fun l -> l |>
                                                  terminal 'i' --> terminal '(' -+>  pr_BV2 ++> fun condf -> terminal ')'--> terminal '{' -+> pr_I2 ++> fun i1 -> terminal '}' --> terminal '{' -+> pr_I2 ++> fun i2 -> terminal '}'-+> epsilon_res ( If (condf, i1, i2))
and pr_W2 : whileb ranalist = fun l' -> l' |> terminal 'w' -->  terminal '(' -+> pr_BV2 ++> fun condw ->  terminal ')' --> terminal '{' -+> pr_I2 ++> fun w -> terminal '}'-+> epsilon_res(While(condw,w))
and pr_I2 : whileb ranalist = fun l' -> l' |> ( pr_F2 +| pr_W2 +| pr_A2 ) ++> fun i1 -> ((terminal ';' -+> pr_I2 ++> fun i2 -> epsilon_res (Seq(i1,i2))) +| epsilon_res(Seq(i1,Skip)));;



(* Exercice 2.2.1 *) (* on répond directement à l'xercice 2.2.2 *)


type state = (char * bool )list ;;

 exception Echec;;

let rec get (c: char) (s:state) : bool = 
  match s with
  | [] -> raise Echec
  | (c',b')::s' -> if c = c' then b' else get c s';;


let rec update (c: char) (b: bool) (s: state) : state =
                                                match s with
                                                | [] -> (c,b)::[]
                                                | (c', b')::s' -> if c = c' then (c,b)::s'
                                                                  else (c',b')::update c b s';;


let rec evalB (b: bexp) : bool =
  match b with
  | True -> true
  | False -> false ;;

let rec evalV (v: var)(s: state) : bool = match v with
  | C c -> get c s
  | B b -> evalB b 
  | Or (v1,v2) ->  (evalV v1 s) || (evalV v2 s)
  | And (v1,v2) ->  (evalV v1 s) && (evalV v2 s)
  | Not v -> not (evalV v s);;


let(a,b) =pr_F( list_of_string ("((a+(b.0))+(!1))") );;
evalV a [('a', false);('b',true)];;

let rec evalW (i:whileb) (s:state) : state =
  match i with
  |Skip -> s
  |Affect (c,v) ->update c (evalV v s) s
  |Seq (ins1,ins2) -> evalW ins2 (evalW ins1 s)
  |If (b,ins1,ins2) -> if evalV b s then evalW ins1 s else evalW ins2 s
  |While(b,ins) -> if evalV b s then evalW i (evalW ins s) else s;;


(* tests ---------------------------------------------------------------------*)

let a,b = pr_I2 (list_of_string "a:=1;b:=1;c:=1;i(1){c:=0;a:=1}{b:=0;c:=1}");;
(* val a:whileb =  Seq (Affect ('a', B True),
   Seq (Affect ('b', B True),
    Seq (Affect ('c', B True),
     Seq
      (If (B True,
        Seq (Affect ('c', B False), Seq (Affect ('a', B True), Skip)),
        Seq (Affect ('b', B False), Seq (Affect ('c', B True), Skip))),
      Skip))));;
 *)

assert (evalW a [] =  [('a', true); ('b', true); ('c', false)]);;

let c,d = pr_I2 (list_of_string "a:=1;b:=1;c:=1;d:=0;i((!d)){c:=0}{b:=0};w((a+b)){a:=0;b:=0}");;
assert (evalW c []  = [('a', true); ('b', true); ('c', true); ('d', false)]);;

let e,f = pr_I2 (list_of_string "a:=1;b:=1;c:=0;i((a.c)){d:=1}{d:=0}");;
evalW 
(* --------------------------------------------------------------------------- *)
