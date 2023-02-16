(* Utilitaire pour les tests *)

let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then [] else s.[i] :: boucle (i+1)
  in boucle 0


(* types et fonctions recupérés d'Anacomb *)

(* analist *)
type analist = char list -> char list

exception Echec

(* terminal constant *)
let terminal c : analist = fun l -> match l with
  | x :: l when x = c -> l
  | _ -> raise Echec

(* terminal conditionnel *)
let terminal_cond (p : 'term -> bool) : analist = function
  | x :: l when p x -> l
  | _ -> raise Echec

(* non-terminal vide *)
let epsilon : analist = fun l -> l

(* Composition séquentielle : a1 suivi de a2 *)
let (-->) (a1 : analist) (a2 : analist) : analist =
  fun l -> let l = a1 l in a2 l

(* Choix entre a1 ou a2 *)
let (-|) (a1 : analist) (a2 : analist) : analist =
  fun l -> try a1 l with Echec -> a2 l



(* ranalist *)
type 'res ranalist = char list -> 'res * char list

let epsilon_res (info : 'res) : 'res ranalist =
  fun l -> (info, l)

(* Terminal conditionnel avec résultat *)
let terminal_res (f : char -> 'res option) : 'res ranalist =
  fun l -> match l with
  | x :: l -> (match f x with Some y -> y, l | None -> raise Echec)
  | _ -> raise Echec


(* Choix entre a1 ou a2 informatifs *)
let (+|) (a1 : 'res ranalist) (a2 : 'res ranalist) : 'res ranalist =
  fun l -> try a1 l with Echec -> a2 l


(* a1 sans résultat suivi de a2 donnant un résultat *)
let ( -+>) (a1 : analist) (a2 : 'res ranalist) : 'res ranalist =
  fun l -> let l = a1 l in a2 l

(* a1 rendant un résultat suivi de a2 sans résultat *)
let (+->) (a1 : 'res ranalist) (a2 : analist) : analist =
  fun l -> let (x, l) = a1 l in a2 l

(* a1 rendant un résultat suivi de a2 rendant un résultat *)
let (++>) (a1 : 'resa ranalist) (a2 : 'resa -> 'resb ranalist) : 'resb ranalist =
  fun l -> let (x, l) = a1 l in a2 x l









