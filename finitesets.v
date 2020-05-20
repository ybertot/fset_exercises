Require Import ZArith List FMapPositive Bool Mergesort Orders.

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

Definition inter (l1 l2 : list Z) :=
  filter (fun x => existsb (fun y => x =? y)%Z l2) l1.

Compute existsb (fun x => (x =? 0)%Z) nums.

Compute existsb (fun x => (x =? 1)%positive) pnums.

Definition subtract (l1 l2 : list Z) :=
  filter (fun x => negb (existsb (fun y => x =? y)%Z l2)) l1.

Definition union (l1 l2 : list Z) := l1 ++ subtract l2 l1.

Time Compute length (inter nums2 nums).

Compute length (inter nums2 nums).

Compute length nums2.

Definition pnums_tree :=
  Eval vm_compute in  fold_right (fun e m => PositiveMap.add e true m)
   (PositiveMap.empty bool) pnums.

Definition pnums_card := Eval compute in PositiveMap.cardinal pnums_tree.

Compute pnums_card.

Definition pnums2_tree :=
  Eval vm_compute in  fold_right (fun e m => PositiveMap.add e true m)
   (PositiveMap.empty bool) pnums2.

Definition pnums2_card := Eval compute in PositiveMap.cardinal pnums2_tree.

Compute pnums2_card.

Import PositiveMap.

Fixpoint interm (s1 s2 : PositiveMap.tree bool) : PositiveMap.tree bool :=
  match s1, s2 with
  | Node s1_1 o1 s1_2, Node s2_1 o2 s2_2 =>
    Node (interm s1_1 s2_1)
         (match o1, o2 with
            Some v1, Some v2 => Some v1
          | _, _ => None
          end)
         (interm s1_2 s2_2)
  | _, _ => Leaf bool
  end.

Fixpoint unionm (s1 s2 : PositiveMap.tree bool) : PositiveMap.tree bool :=
  match s1, s2 with
  | Node s1_1 o1 s1_2, Node s2_1 o2 s2_2 =>
    Node (unionm s1_1 s2_1)
         (match o1, o2 with
            None, None => None
          | _, _ => Some true
          end)
         (unionm s1_2 s2_2)
  | Leaf _, t => t
  | t, Leaf _ => t
  end.

Fixpoint subtractm (s1 s2 : PositiveMap.tree bool) : PositiveMap.tree bool :=
  match s1, s2 with
  | Node s1_1 o1 s1_2, Leaf _ => s1
  | Node s1_1 o1 s1_2, Node s2_1 o2 s2_2 =>
    Node (subtractm s1_1 s2_1)
         (match o1, o2 with
            V, None => V
          | _, Some _ => None
          end)
         (subtractm s1_2 s2_2)
  | Leaf _, _ => Leaf bool
  end.
  
Definition inter2 (s1 s2 : PositiveMap.tree bool) :=
  PositiveMap.fold
   (fun k v t => 
       if PositiveMap.mem k s2 then PositiveMap.add k true t else t)
   s1 (PositiveMap.empty bool).

Definition inter_card := Eval compute in PositiveMap.cardinal
  (interm pnums_tree pnums2_tree).

Compute inter_card.

Import PositiveMap.

Lemma intermP :
  forall s1 s2 x, mem x s1 = true /\ mem x s2 = true <->
                  mem x (interm s1 s2) = true.
Proof.
induction s1 as [ | s1_1 IH1 o1 s1_2 IH2]; destruct s2 as [ | s2_1 o2 s2_2];
  intros x;
  try (destruct o1 as [v1 | ]; destruct o2 as [v2 | ]; simpl); simpl;
  try (rewrite mem_find; destruct x; simpl; intuition discriminate);
  try (destruct x as [x1 | x1 | ]; simpl;
       [ rewrite <- IH2 | rewrite <- IH1 | ]; tauto).
Qed.

Lemma unionmP :
  forall s1 s2 x, mem x s1 = true \/ mem x s2 = true <->
                  mem x (unionm s1 s2) = true.
Proof.
induction s1 as [ | s1_1 IH1 o1 s1_2 IH2]; destruct s2 as [ | s2_1 o2 s2_2];
  intros x;
  try (destruct o1 as [v1 | ]; destruct o2 as [v2 | ]; simpl); simpl;
  try (rewrite mem_find; destruct x; simpl; intuition discriminate);
  try (destruct x as [x1 | x1 | ]; simpl;
       [ rewrite <- IH2 | rewrite <- IH1 | ]; tauto).
Qed.

Lemma subtractmP :
  forall s1 s2 x, mem x s1 = true /\ mem x s2 = false <->
                  mem x (subtractm s1 s2) = true.
Proof.
induction s1 as [ | s1_1 IH1 o1 s1_2 IH2]; destruct s2 as [ | s2_1 o2 s2_2];
  intros x;
  try (destruct o1 as [v1 | ]; destruct o2 as [v2 | ]; simpl); simpl;
  try (rewrite mem_find; destruct x; simpl; intuition discriminate);
  try (destruct x as [x1 | x1 | ]; simpl;
       [ rewrite <- IH2 | rewrite <- IH1 | ]; tauto || intuition discriminate).
Qed.

Time Compute cardinal (inter2 pnums_tree pnums2_tree).
Time Compute cardinal (interm pnums_tree pnums2_tree).

Compute cardinal (unionm pnums_tree pnums2_tree).
Compute cardinal (subtractm pnums_tree pnums2_tree).

Definition selectm (test : positive -> bool) s :=
  fold (fun k v t => if test k then add k v t else t)
       s (empty bool).

Lemma fold_left_add (s : list (positive * bool)) x s2 (test : _ -> bool) :
  mem x s2 = true ->
  mem x (fold_left (fun t (p : positive * bool) =>
        if test (fst p) then add (fst p) (snd p) t else t) s s2) = true.
Proof.
revert s2; induction s as [| [y w] l IH].
  now simpl.
intros s2 mem2; simpl; case (test y); apply IH;[ | easy].
destruct (Pos.eq_dec x y) as [xisy | xny].
  now rewrite xisy, mem_find, gss.
now rewrite mem_find, gso, <- mem_find.
Qed.

Lemma selectmP test s x :
  mem x s = true /\ test x = true <-> mem x (selectm test s) = true.
Proof.
unfold selectm.
enough (main : forall s2, (mem x s = true /\ test x = true) \/
                                mem x s2 = true <->
                   mem x (fold (fun k v t => if test k then add k v t else t)
                                s s2) = true).
  rewrite <- main; split;[intros it; left | intros [it | abs];
     try (destruct x; discriminate)]; exact it.
assert (equiv :mem x s = true <-> Exists (fun p => fst p = x) (elements s)).
  split.
    rewrite mem_find; destruct (find x s) as [v | ] eqn:fxs; try discriminate.
    intros _; rewrite Exists_exists.
    exists (x, v); split;[ | easy].
    now apply elements_correct.  
  rewrite Exists_exists; intros [[x' v] [inlist xisx']].
  simpl in xisx'; rewrite xisx' in inlist; rewrite mem_find.
  now apply elements_complete in inlist; rewrite inlist.
intros s2; rewrite equiv, fold_1; generalize (elements_3w s).
clear equiv.
revert s2.
induction (elements s) as [ | [y w] l IH].
  intros s2 _.
  split.
    intros [[abs1 _] | ].
      now rewrite Exists_nil in abs1.
    now rewrite fold_left_add.
  now simpl; right.
intros s2 nodup.
assert (~SetoidList.InA (eq_key (A := bool)) (y, w) l /\
             SetoidList.NoDupA (eq_key (A:=bool)) l) as [yninl nodupl].
  inversion nodup; tauto.
clear nodup.
split.
  rewrite Exists_cons.
  intros [[[yx | xin] tx] | xs2]; simpl.
      simpl in yx; rewrite yx, tx, fold_left_add; auto.
      now rewrite mem_find, gss.
    rewrite <- IH; tauto.
  destruct (test y); rewrite fold_left_add; auto.
  rewrite mem_find.
  destruct (Pos.eq_dec x y) as [xisy | xny].
    rewrite xisy, gss; easy.
  rewrite gso, <- mem_find; easy.
simpl; rewrite <- IH; auto.
intros [[exl tx]| xys2].
  now left; rewrite Exists_cons; split;[right |].
destruct (test y) eqn:ty.
  destruct (Pos.eq_dec x y) as [xisy | xny].
    rewrite xisy; left; split;[apply Exists_cons_hd |]; easy.
  now right; rewrite mem_find; rewrite mem_find, gso in xys2.
tauto.
Qed.

Lemma selectm_2 s p1 p2 x :
  mem x (selectm p1 (selectm p2 s)) =
  mem x (selectm (fun y => p1 y && p2 y) s).
Proof.
destruct (mem x (selectm p1 (selectm p2 s))) eqn:sl1then2.
  rewrite <- selectmP in sl1then2; destruct sl1then2 as [sl2 test1].
  symmetry; rewrite <- selectmP.
  rewrite <- selectmP in sl2.
  rewrite andb_true_iff; tauto.
assert (tech : forall u : bool, u = false <-> not (u = true)).
  now intros [|]; split; auto; intros h; try discriminate; case h.
symmetry; rewrite tech; intros sl1and2; rewrite tech in sl1then2; case sl1then2.
rewrite <- !selectmP; rewrite <- selectmP in sl1and2.
rewrite andb_true_iff in sl1and2; tauto.
Qed.
