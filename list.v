Require Import ZArith List Bool Mergesort Orders.

(* Linear congruential generator. This is used to produce a low quality
  sequence of random numbers. *)

Definition lcg_step (modulus a c seed : Z) := ((a * seed + c) mod modulus)%Z.

Definition iterates (modulus a c seed len : Z) :=
 Z.iter len
   (fun p : list Z * Z => let acc := fst p in let seed := snd p in
       let seed' := lcg_step modulus a c seed in
       (seed'::acc, seed')) (nil, seed).

(* We settle with a list of 2000 elements, taken between 0 and 2 ^ 32.
  The randomness is quite weak, as they alternate between odd and even
  numbers. *)
Definition rnd_list :=
    Eval compute in fst (iterates (2 ^ 32) 1664525 1013904223 33 2000).

Definition rnd_list2 :=
    Eval compute in fst (iterates (2 ^ 32) 1664525 1013904223 1937 2000).

(* For better randomness, we take only the higher 16 bits.  Then we can
  use a modulo operation to bring this inside a chosen interval. *)
Definition randp16 (rand : list Z) :=
  let p16 := (2 ^ 16)%Z in map (fun z => (z / p16)%Z) rand.

Definition nums := Eval compute in randp16 rnd_list.

Definition nums2 := Eval compute in randp16 rnd_list2.

Definition ZtoPos z :=
  match z with Z.pos x => x | Z.neg x => x | Z0 => 1%positive end.

Definition pnums := map ZtoPos nums.

Definition pnums2 := map ZtoPos nums2.

Module ZOrder <: TotalLeBool.
  Definition t := Z.
  Definition leb := Z.leb.

Theorem leb_total : forall x y, leb x y = true \/ leb y x = true.
Proof.
now intros x y; case (Zle_bool_total x y); auto.
Qed.

End ZOrder.

Module Import ZSort := Sort ZOrder.

Compute sort nums.

Fixpoint adjacent {A : Type} (l : list A) :=
  match l with
  | nil => nil
  | _ :: nil => nil
  | a :: (b :: _ as tl) => (a,b) :: adjacent tl
  end.

Compute adjacent (sort nums).

Compute length (filter (fun p => (fst p =? snd p)%Z) (adjacent (sort nums))).

Compute existsb (fun x => (x =? 0)%Z) nums.

Compute existsb (fun x => (x =? 1)%positive) pnums.

Definition set := list Z.

Definition empty : set := nil.

Definition cardinal (s : set) : nat := length s.

Definition mem (x : Z) (s : set) := existsb (fun y => x =? y)%Z s.

Lemma mem_cons (x a : Z) (s : set) :
  mem x (a :: s) = Z.eqb x a || mem x s.
Proof. intros; simpl; reflexivity. Qed.

(*
Lemma mem_In : forall (x : Z) (s : set), mem x s = true <-> In x s.
Proof.
intros x s; unfold mem; rewrite existsb_exists.
split; [intros [y [HIn Hxy]]; apply Z.eqb_eq in Hxy; rewrite Hxy; auto|].
intro HIn; exists x; split; [auto|apply Z.eqb_refl].
Qed.
*)

Lemma mem_app (x : Z) (s1 s2 : set) :
  mem x (s1 ++ s2) = mem x s1 || mem x s2.
Proof. intros; unfold mem; rewrite existsb_app; reflexivity. Qed.

Lemma mem_filter (f : Z -> bool) (x : Z) (s : set) :
  mem x (filter f s) = mem x s && f x.
Proof.
elim s; clear s; [simpl; reflexivity|].
intros a s IHs; rewrite mem_cons, andb_orb_distrib_l.
rewrite <- IHs; clear IHs; simpl.
case_eq (Z.eqb x a); [rewrite Z.eqb_eq|]; intro Hxa; [rewrite Hxa|];
case (f a); simpl; [rewrite Z.eqb_refl| |rewrite Hxa|]; reflexivity.
Qed.

Definition inter (s1 s2 : set) :=
  filter (fun x => existsb (fun y => x =? y)%Z s2) s1.

Lemma interP (x : Z) (s1 s2 : set) :
  mem x (inter s1 s2) = mem x s1 && mem x s2.
Proof. intros; unfold inter; rewrite mem_filter; reflexivity. Qed.

Definition substract (s1 s2 : set) :=
  filter (fun x => negb (existsb (fun y => x =? y)%Z s2)) s1.

Lemma substractP (x : Z) (s1 s2 : set) :
  mem x (substract s1 s2) = mem x s1 && negb (mem x s2).
Proof. intros; unfold substract; rewrite mem_filter; reflexivity. Qed.

Definition union (s1 s2 : set) := s1 ++ substract s2 s1.

Lemma unionP (x : Z) (s1 s2 : set) :
  mem x (union s1 s2) = mem x s1 || mem x s2.
Proof.
intros; unfold union; rewrite mem_app, substractP.
case (mem x s1); [|rewrite andb_true_r]; reflexivity.
Qed.

Time Compute cardinal (inter nums nums2).

Compute cardinal (union nums nums2).
Compute cardinal (substract nums nums2).

Definition select (test : Z -> bool) (s : set) := filter test s.

Lemma select2 s p1 p2 x :
  mem x (select p1 (select p2 s)) =
  mem x (select (fun y => p1 y && p2 y) s).
Proof.
unfold select; repeat rewrite mem_filter.
case (mem x s); simpl; [rewrite andb_comm|]; reflexivity.
Qed.