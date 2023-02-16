(*
|-------+--------------+--------------+--------------+--------------|
|       | MATHIEULucas |  MAIDA  Léa  | KHELIFI Aziz | NOM4-Prénom4 |
|-------+--------------+--------------+--------------+--------------|
| 1.1.1 |      X       |      X       |      X       |              |
| 1.1.2 |      X       |      X       |      X       |              |
| 1.1.3 |      X       |      X       |      X       |              |
| 1.1.4 |              |      X       |      X       |              |
| 1.2.1 |      X       |      X       |      X       |              |
|-------+--------------+--------------+--------------+--------------|
| 2.1.1 |      X       |      X       |      X       |              |
| 2.1.2 |      X       |      X       |      X       |              |
| 2.1.3 |      X       |      X       |      X       |              |
| 2.1.4 |              |              |              |              |
| 2.2.1 |      X       |      X       |      X       |              |
| 2.2.2 |              |      X       |      X       |              |
| 2.3.1 |              |              |              |              |
| 2.3.2 |              |              |              |              |
| 2.3.3 |              |              |              |              |
| 2.4.1 |      X       |      X       |      X       |              |
| 2.4.2 |      X       |      X       |      X       |              |
| 2.4.3 |      X       |      X       |      X       |              |
| 2.4.4 |      X       |              |              |              |
|-------+--------------+--------------+--------------+--------------|
| 3.1   |              |              |              |              |
| 3.2   |              |              |              |              |
| 3.3.1 |              |              |              |              |
| 3.3.2 |              |              |              |              |
| 3.3.3 |              |              |              |              |
| 3.4   |              |              |              |              |
| 3.5   |              |              |              |              |
| 3.6   |              |              |              |              |
| 3.7.1 |              |              |              |              |
| 3.7.2 |              |              |              |              |
| 3.7.3 |              |              |              |              |
| 3.7.4 |              |              |              |              |
| 3.7.5 |              |              |              |              |
| 3.8   |              |              |              |              |
| 3.9   |              |              |              |              |
|-------+--------------+--------------+--------------+--------------|
*)

(* TD9 - Sémantique petit pas                *)
(* Structural Operational Semantics (SOS)    *)


(* On importe les bibliothèques de Coq utiles pour le TD   *)

Require Import Bool Arith List.
Import List.ListNotations.

(* ========================================================================== *)
(** * Préliminaires *)
(** ** Syntaxe des expressions arithétiques *)

Inductive aexp :=
| Aco : nat -> aexp (** constantes *)
| Ava : nat -> aexp (** variables *)
| Apl : aexp -> aexp -> aexp
| Amu : aexp -> aexp -> aexp
| Amo : aexp -> aexp -> aexp
.

(** ** Syntaxe des expressions booléennes *)

Inductive bexp :=
| Btrue : bexp
| Bfalse : bexp
| Bnot : bexp -> bexp
| Band : bexp -> bexp -> bexp
| Bor : bexp -> bexp -> bexp
| Beq : bexp -> bexp -> bexp    (* test égalité de bexp *)
| Beqnat : aexp -> aexp -> bexp (* test égalité de aexp *)
.

(** ** Syntaxe du langage impératif WHILE *)

Inductive winstr :=
| Skip   : winstr
| Assign : nat -> aexp -> winstr
| Seq    : winstr -> winstr -> winstr
| If     : bexp -> winstr -> winstr -> winstr
| While  : bexp -> winstr -> winstr
.

(* -------------------------------------------------- *)
(** ** États *)

Definition state := list nat.


Fixpoint get (x:nat) (s:state) : nat :=
match x,s with
| 0   , v::_      => v
| S x1, _::l1 => get x1 l1
| _   , _         => 0
end.


Fixpoint update (s:state) (v:nat) (n:nat): state :=
match v,s with
| 0   , a :: l1 => n :: l1
| 0   , nil     => n :: nil
| S v1, a :: l1 => a :: (update l1 v1 n)
| S v1, nil     => 0 :: (update nil v1 n)
end.

(* ----------------------------------------------- *)
(** ** Sémantique fonctionnelle de aexp et de bexp *)

Fixpoint evalA (a: aexp) (s: state) : nat :=
  match a with
  | Aco n => n
  | Ava x => get x s
  | Apl a1 a2 =>  evalA a1 s + evalA a2 s
  | Amu a1 a2 =>  evalA a1 s * evalA a2 s
  | Amo a1 a2 =>  evalA a1 s - evalA a2 s
  end.

Definition eqboolb b1 b2 : bool :=
  match b1, b2  with
  | true , true  => true
  | false, false => true
  | _    , _     => false
  end.

Fixpoint eqnatb n1 n2 : bool :=
  match n1, n2 with
  | O    , O     => true
  | S n1', S n2' => eqnatb n1' n2'
  | _    , _     => false
  end.

Fixpoint evalB (b : bexp) (s : state) : bool :=
  match b with
  | Btrue => true
  | Bfalse => false
  | Bnot b => negb (evalB b s)
  | Band e1 e2 => (evalB e1 s) && (evalB e2 s)
  | Bor e1 e2 => (evalB e1 s) || (evalB e2 s)
  | Beq e1 e2 => eqboolb (evalB e1 s) (evalB e2 s)
  | Beqnat n1 n2 => eqnatb (evalA n1 s) (evalA n2 s)
  end.


(* ========================================================================== *)

(** * SOS (Sémantique opérationnelle à petits pas) du langage While *)

Inductive config :=
| Inter : winstr -> state -> config
| Final : state -> config.

(* La relation pour un pas de SOS *)

Inductive SOS_1: winstr -> state -> config -> Prop :=
| SOS_Skip     : forall s,
                 SOS_1 Skip s (Final s)

| SOS_Assign   : forall x a s,
                 SOS_1 (Assign x a) s (Final (update s x (evalA a s)))

| SOS_Seqf     : forall i1 i2 s s1,
                 SOS_1 i1 s (Final s1) ->
                 SOS_1 (Seq i1 i2) s (Inter i2 s1)
| SOS_Seqi     : forall i1 i1' i2 s s1,
                 SOS_1 i1 s (Inter i1' s1) ->
                 SOS_1 (Seq i1 i2) s (Inter (Seq i1' i2) s1)

| SOS_If_true  : forall b i1 i2 s,
                 evalB b s = true  ->
                 SOS_1 (If b i1 i2) s (Inter i1 s)
| SOS_If_false : forall b i1 i2 s,
                 evalB b s = false ->
                 SOS_1 (If b i1 i2) s (Inter i2 s)

| SOS_While    : forall b i s,
                 SOS_1 (While b i) s (Inter (If b (Seq i (While b i)) Skip) s)
.

(** Fermeture réflexive-transitive de SOS_1 *)
(** Cette sémantique donne toutes les configurations atteignables
    par un (AST de) programme en partant d'un état initial.
 *)

Inductive SOS : config -> config -> Prop :=
| SOS_stop  : forall c, SOS c c
| SOS_again : forall i1 s1 c2 c3,
              SOS_1 i1 s1 c2 -> SOS c2 c3 ->
              SOS (Inter i1 s1) c3.


(* ========================================================================== *)

Definition N0 := Aco 0.
Definition N1 := Aco 1.
Definition N2 := Aco 2.
Definition N3 := Aco 3.
Definition N4 := Aco 4.


(** * I *)

(** *** Calcul du carré avec des additions *)
(** On code dans While un programme Pcarre correspondant à
    while not (i=n) do {i:= 1+i; x:= y+x ; y:= 2+y} *)
Definition Il := 0.
Definition Ir := Ava Il.
Definition Xl := 1.
Definition Xr := Ava Xl.
Definition Yl := 2.
Definition Yr := Ava Yl.

Definition incrI := Assign Il (Apl N1 Ir).
Definition incrX := Assign Xl (Apl Yr Xr).
Definition incrY := Assign Yl (Apl N2 Yr).
Definition corps_carre := Seq incrI (Seq incrX incrY).
Definition Pcarre_2 := While (Bnot (Beqnat Ir (Aco 2))) corps_carre.
Definition Pcarre n := While (Bnot (Beqnat Ir (Aco n))) corps_carre.
(** Nouveau : on peut jouer avec des programmes qui bouclent *)
Definition Pcarre_inf := While Btrue corps_carre.

(* 2.4.2 Premier - *)
Lemma SOS_Pcarre_2_1er_tour : SOS (Inter Pcarre_2 [0;0;1]) (Inter Pcarre_2 [1; 1; 3]).
Proof.
  eapply SOS_again.
  { apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_true. cbn. reflexivity. }
  eapply SOS_again.
  { unfold corps_carre. eapply SOS_Seqi. eapply SOS_Seqf. cbv [incrI]. apply SOS_Assign. }
  cbn. eapply SOS_again.
  { eapply SOS_Seqi. eapply SOS_Seqf. cbv [incrX]. apply SOS_Assign. }
  cbn. eapply SOS_again.
  { eapply SOS_Seqf. cbv [incrY]. apply SOS_Assign. }
  cbn. (* unfold Pcarre_2. unfold corps_carre. *)
  apply SOS_stop.
Qed.

(* 2.4.2 Deuxième - L'énoncé indique que le programme Pcarre_inf avec les valeurs [0; 0; 1] passe par la configuration intermediaire où Pcarre_inf peut être exécuté avec les valeurs [1; 1; 3].*)
Theorem SOS_Pcarre_inf_1er_tour : SOS (Inter Pcarre_inf [0;0;1]) (Inter Pcarre_inf [1; 1; 3]).
Proof.
  eapply SOS_again.
  { unfold Pcarre_inf. apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_true. cbn. reflexivity. }
  eapply SOS_again.
  {  unfold corps_carre. eapply SOS_Seqi. eapply SOS_Seqf. cbv [incrI]. apply SOS_Assign. }
  cbn. eapply SOS_again.
  { eapply SOS_Seqi. eapply SOS_Seqf. cbv [incrX]. apply SOS_Assign. }
  cbn. eapply SOS_again.
  { eapply SOS_Seqf. cbv [incrY]. apply SOS_Assign. }
  cbn. (* unfold Pcarre_2. unfold corps_carre. *)
  apply SOS_stop.
Qed.

Theorem SOS_Pcarre_2_V0 : SOS (Inter Pcarre_2 [0;0;1]) (Final [2;4;5]).
Proof.
  eapply SOS_again.
  { unfold Pcarre_2. apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_true. cbn. reflexivity. }
  eapply SOS_again.
  {  unfold corps_carre. eapply SOS_Seqi. eapply SOS_Seqf. cbv [incrI]. apply SOS_Assign. }
  cbn. eapply SOS_again.
  { eapply SOS_Seqi. eapply SOS_Seqf. cbv [incrX]. apply SOS_Assign. }
  cbn. eapply SOS_again.
  { eapply SOS_Seqf. cbv [incrY]. apply SOS_Assign. }
  cbn. eapply SOS_again.
  { apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_true. cbn. reflexivity. }
  eapply SOS_again.
  {  unfold corps_carre. eapply SOS_Seqi. eapply SOS_Seqf. cbv [incrI]. apply SOS_Assign. }
  cbn. eapply SOS_again.
  { eapply SOS_Seqi. eapply SOS_Seqf. cbv [incrX]. apply SOS_Assign. }
  cbn. eapply SOS_again.
  { eapply SOS_Seqf. cbv [incrY]. apply SOS_Assign. }
  cbn. eapply SOS_again.
  { eapply SOS_While. }
  cbn. eapply SOS_again.
  { apply SOS_If_false. cbn. reflexivity. }
  eapply SOS_again.
  { apply SOS_Skip. }
  apply SOS_stop.
Qed.

(** Le but de la suite est d'éviter les redites, puis éventuellement
    de considérer le cas général Pcarre. *)

(** Propriété essentielle de SOS, qui a un intérêt pratique. *)
Theorem SOS_trans : forall c1 c2 c3, SOS c1 c2 -> SOS c2 c3 -> SOS c1 c3.
Proof.
  (* Cette propriété indique que SOS est transitif, cela veut dire que si SOS c1 => c2 et SOS c2 => c3 alors SOS c1 => c3 *)
  intro c1. intro c2. intro c3.
  intros sos1.
  induction sos1 as [ | ].
  - intro a. apply a.
  - intro a. eapply SOS_again.
    { apply H. }
    { apply IHsos1. apply a. }
Qed.

(* 2.4.2 Troisième - Le théorème indique que la configuration du programme Pcarre_2 avec les valeurs [1; 1; 3] passe par la configuration intermediaire où Pcarre_2 peut être exécuté à nouveau avec les valeurs [2; 4; 5].*)
(** Il n'est pas demandé de faire celui-ci
    (bien qu'un copié-collé d'un lemme précédent fonctionne). *)
Lemma SOS_Pcarre_2_2e_tour : SOS (Inter Pcarre_2 [1; 1; 3]) (Inter Pcarre_2 [2; 4; 5]).
Proof.
Admitted.

(* 2.4.2 Quatrième - Le théorème indique que la configuration du programme Pcarre_2 avec les valeurs [2; 4; 5] arrive à la configuration où les valeurs finales sont [2; 4; 5].*)
Theorem SOS_Pcarre_2_fini : SOS (Inter Pcarre_2 [2; 4; 5]) (Final [2; 4; 5]).
Proof.
  eapply SOS_again.
  { unfold Pcarre_2. apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_false. cbn. reflexivity. }
  eapply SOS_again.
  { apply SOS_Skip. }
  apply SOS_stop.
Qed.

(* 2.4.2 Cinquième - Le théorème indique que la configuration du programme Pcarre_2 avec les valeurs [0; 0; 1] arrive à la configuration où les valeurs finales sont [2; 4; 5] à l'aide de la transitivité passant par les différentes configurations intermédiaires.*)
(** Même énoncé que SOS_Pcarre_2_V0. Utiliser SOS_trans *)
Theorem SOS_Pcarre_2_fin_V1 : SOS (Inter Pcarre_2 [0;0;1]) (Final [2;4;5]).
Proof.
  apply SOS_trans with (Inter Pcarre_2 [1; 1; 3]).
  - apply SOS_Pcarre_2_1er_tour.
  - apply SOS_trans with (Inter Pcarre_2 [2; 4; 5]).
    apply SOS_Pcarre_2_2e_tour.
    apply SOS_Pcarre_2_fini.
Qed.

(** Généralisation à Pcarre *)

(** On a besoin de deux lemmes arithmétiques, démontrables avec la tactique ring. *)
Lemma Sn_2 n : S n + S n = S (S (n + n)).
Proof. ring. Qed.

Lemma Sn_carre n : S n * S n = S (n + n + n * n).
Proof. ring. Qed.

Definition invar_cc n := [n; n*n; S (n+n)].

(* 2.4.3 Premier - Le théorème indique que pour tout entier n, la configuration du programme corps_carre avec l'état invar_cc de n retourne une configuration finale avec comme état invar_cc de n+1 *)
Theorem SOS_corps_carre n : SOS (Inter corps_carre (invar_cc n)) (Final (invar_cc (S n))).
Proof.
  eapply SOS_again.
  { unfold corps_carre. apply SOS_Seqf. cbv [incrI]. apply SOS_Assign. }
  eapply SOS_again.
  { apply SOS_Seqf. cbv [incrX]. apply SOS_Assign. }
  cbn. eapply SOS_again.
  { cbv [incrY]. apply SOS_Assign. }
  cbn. unfold invar_cc. rewrite Sn_2. rewrite Sn_carre.
  apply SOS_stop.
Qed.

(** Celui-ci est court mais difficile. Laisser Admitted au début. *)
Fixpoint SOS_seq i1 i2 s1 s2 (so : SOS (Inter i1 s1) (Final s2)) :
  SOS (Inter (Seq i1 i2) s1) (Inter i2 s2).
Proof.
  (* Le théorème SOS_Seq indique qu'on peut changer un état final en un état intermédiaire en rajoutant une séquence i1 i2 au lieu d'avoir uniquement i1 *)
Admitted.

(* 2.4.3 Deuxième - Le théorème indique que pour tout entier n et instruction i, la configuration de la séquence du programme corps_carre et du programme i avec l'état invar_cc de n retourne une configuration intermédiaire du programme i avec comme état invar_cc de n+1 *)
(** Réutiliser les lemmes précédents (facile et très court). *)
Lemma SOS_corps_carre_inter n i :
  SOS (Inter (Seq corps_carre i) (invar_cc n)) (Inter i (invar_cc (S n))).
Proof.
  apply SOS_seq.
  apply SOS_corps_carre.
Qed.

Lemma eqnatb_refl : forall n, eqnatb n n = true.
Proof.
  intro n.
  induction n as [| n' hrecn' ].
  - reflexivity. 
  - cbn. rewrite hrecn'. reflexivity.
Qed.

(* 2.4.3 Troisième - Le théorème indique que pour tout i et n entiers, la configuration du programme Pcarre de n avec l'état invar_cc de i retourne une configuration intermédiaire du programme Pcarre de n avec l'état invar_cc de i+1 *)
(** Réutiliser les lemmes précédents (facile). *)
Lemma SOS_Pcarre_tour :
  forall n i, eqnatb i n = false ->
  SOS (Inter (Pcarre n) (invar_cc i)) (Inter (Pcarre n) (invar_cc (S i))).
Proof.
  intros n i.
  intro c.
  eapply SOS_again.
  { unfold Pcarre. apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_true. cbn. rewrite c. reflexivity. }
  apply SOS_corps_carre_inter.
Qed.

(* 2.4.3 Quatrième - Le théorème indique que pour tout n, la configuration du programme Pcarre de n avec l'état invar_cc de n retourne une configuration finale avec comme état invar_cc de n *)
(** Facile *)
Theorem SOS_Pcarre_n_fini :
  forall n, SOS (Inter (Pcarre n) (invar_cc n)) (Final (invar_cc n)).
Proof.
  intro n.
  eapply SOS_again.
  { unfold Pcarre. apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_false. cbn. rewrite eqnatb_refl. reflexivity. }
  eapply SOS_again.
  { apply SOS_Skip. }
  apply SOS_stop.
Qed.

(* 2.4.3 Cinquième -
On doit montrer que la configuration intermédiaire du programme Pcarre_2 avec l'état [0; 0; 1] retourne l'état final ayant comme valeurs [2; 4; 5].
Pour cela on commence par appliquer la transitivité de SOS, ce qui veut dire qu'on peut rajouter une étape entre SOS (Inter Pcarre_2 [0;0;1]) et (Final [2;4;5]). En faisant un tour du programme Pcarre (qui retourne invar_cc de i+1, avec dans ce cas i=0) on obtient la configuration intermédiaire du programme Pcarre_2 avec l'état ayant comme valeur invar_cc de 1 (soit [1; 1; 3]).
On repète cette étape une deuxième fois afin d'obtenir la configuration intermédiaire du programme Pcarre_2 avec l'état ayant comme valeur invar_cc de 2 (soit [2; 4; 5]).
Pour la dernière étape, on applique encore la transitivité pour refaire un tour, sauf que cette fois on peut utiliser le théorème défini plus haut étant donné qu'on a le programme Pcarre de 2 et invar_cc et à 2 également. On obtient donc la configuration finale recherchée et on a plus qu'à utiliser SOS_stop pour terminer le théorème.
*)
Theorem SOS_Pcarre_2_fin_V2 : SOS (Inter Pcarre_2 [0;0;1]) (Final [2;4;5]).
Proof.
  eapply SOS_trans.
  { apply SOS_Pcarre_tour. reflexivity. }
  eapply SOS_trans.
  { apply SOS_Pcarre_tour. reflexivity. }
  eapply SOS_trans.
  { apply SOS_Pcarre_n_fini. }
  apply SOS_stop.
Qed.

(* 2.4.3 Sixième - Le théorème indique que pour tout entier i, la configuration du programme Pcarre_inf avec l'état invar_cc de i retourne une configuration intermédiaire du programme Pcarre_inf avec comme état invar_cc de i+1 *)
(** On peut dire des choses sur la version qui boucle. *)
Lemma SOS_Pcarre_inf_tour :
  forall i,
  SOS (Inter Pcarre_inf (invar_cc i)) (Inter Pcarre_inf (invar_cc (S i))).
Proof.
  intro i.
  eapply SOS_again.
  { unfold Pcarre_inf. apply SOS_While. }
  eapply SOS_again.
  { apply SOS_If_true. cbn. reflexivity. }
  apply SOS_corps_carre_inter.
Qed.

(* 2.4.3 Septième - Le théorème indique que pour tout entier i, la configuration du programme Pcarre_inf avec l'état ayant pour valeurs [0; 0; 1] retourne une configuration intermédiaire du programme Pcarre_inf avec comme état invar_cc de i (cela est possible grâce à la transitivité car le programme passe par toutes les valeurs de invar_cc suivant le nombre de tours) *)
Theorem SOS_Pcarre_inf_n :
  forall i,
  SOS (Inter Pcarre_inf [0; 0; 1]) (Inter Pcarre_inf (invar_cc i)).
Proof.
  intro i.
  induction i as [ | i' Hrec_i ].
  { cbv [Pcarre_inf]. cbv[invar_cc]. cbn. apply SOS_stop. }
  apply SOS_trans with (Inter Pcarre_inf (invar_cc i')).
  { apply Hrec_i. }
  apply SOS_Pcarre_inf_tour. 
Qed.

(** Énoncer et démontrer le théorème général pour Pcarre *)

(* ========================================================================== *)


(** * II *)


(** ** Définir une version fonctionnelle de SOS_1 *)
Fixpoint f_SOS_1 (i : winstr) (s : state) : config :=
  match i with
  | Skip => Final s
  | Assign x a => Final (update s x (evalA a s))
  | Seq i1 i2 => let c1:=f_SOS_1 i1 s in
                 match c1 with
                 | Inter i1' s' => Inter (Seq i1' i2) s'
                 | Final s' => Inter i2 s'
                 end
  | If b i1 i2 => if evalB b s then Inter i1 s else Inter i2 s
  | While b i => Inter (If b (Seq i (While b i)) Skip) s
end.

(** ** Utilisation de f_SOS_1 pour éviter les eapply SOS_again *)

(** PC = pt de contrôle *)
Definition PC0 := Pcarre_2.
Eval cbn in (f_SOS_1 PC0 [0;0;1]).

(** Il faut un peu désosser le code pour y retrouver les points de contrôle *)

Definition PC2 := Seq corps_carre PC0.
Definition PC1 := If (Bnot (Beqnat Ir (Aco 2))) PC2 Skip.
Definition PC3 := Seq (Seq incrX incrY) PC0.
Definition PC4 := Seq incrY PC0.

(** On vérifie la progression *)
Fact fa1 : f_SOS_1 PC0 [0;0;1] = Inter PC1 [0;0;1]. reflexivity. Qed.
Eval cbn in (f_SOS_1 PC1 [0;0;1]).
(** Continuer, on retombe sur PC0 après quelques étapes. *)

(** Utilisation sur un lemme SOS *)
Lemma SOS_Pcarre_2_1er_tour_V1 :
  SOS (Inter Pcarre_2 [0;0;1]) (Inter Pcarre_2 [1; 1; 3]).
Proof.
  change Pcarre_2 with PC0.
  apply SOS_again with (f_SOS_1 PC0 [0; 0; 1]).
  { apply SOS_While. }
  apply SOS_again with (f_SOS_1 PC1 [0;0;1]).
  { apply SOS_If_true. reflexivity. }
  cbn.
  apply SOS_again with (f_SOS_1 PC2 [0;0;1]).
  { apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign. }
  cbn.
  apply SOS_again with (f_SOS_1 PC3 [1;0;1]).
  { apply SOS_Seqi. apply SOS_Seqf. apply SOS_Assign. }
  cbn.
  apply SOS_again with (f_SOS_1 PC4 [1;1;1]).
  { apply SOS_Seqf. apply SOS_Assign. }    
  apply SOS_stop.
Qed.

(** ** Théorèmes généraux reliant SOS_1 et f_SOS_1 *)

(** Court mais non trivial. *)
Lemma f_SOS_1_corr : forall i s, SOS_1 i s (f_SOS_1 i s).
Proof.
  (*case_eq (eval b s)*)
Admitted.

(** Court. Attention : utiliser la tactique injection. *)
Lemma f_SOS_1_compl : forall i s c, SOS_1 i s c -> c = f_SOS_1 i s.
Proof.
Admitted.




