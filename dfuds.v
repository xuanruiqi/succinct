From mathcomp Require Import all_ssreflect.
Require Import compact_data_structures rank_select pred_succ.

(** DFUDS: Depth-First Unary Degree Sequence **)
(* The bit 0 is interpreted as (, bit 1 as ) *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section dfuds.

  Variable A : eqType.
  
  Definition describe_node (t : tree A) :=
    match t with
    | Node _ ch => rcons (nseq (size ch) true) false
    end.

  Fixpoint DFUDS' (t : tree A) :=
    match t with
    | Node _ ch => describe_node t ++ flatten [seq (DFUDS' t') | t' <- ch]
    end.

  Definition DFUDS t := [:: true; true; false] ++ DFUDS' t.

  Definition DFUDS_size (t : tree A) := (number_of_nodes t).*2 + 2.

  Lemma DFUDS_sizeE t : size (DFUDS t) = DFUDS_size t.
  Proof.
    rewrite /DFUDS_size /DFUDS. elim/tree_ind_eqType: t => a l //= IH.
    rewrite size_cat size_rcons size_flatten size_nseq.
    elim: l IH => [| h l IHl] IH //=.
    rewrite addSn -addn1 addnCA -addnS -addnS -addnS IHl.
    rewrite addnCA addn1 -addnS addn2 IH /number_of_nodes //=.
    by rewrite size_cat !doubleS doubleD addnCA -![in RHS]addnS addnA.
    by rewrite in_cons eq_refl. move=> x H. apply: IH. by rewrite in_cons H orbT.
  Qed.
  
End dfuds.

Section children.

  Variable A : eqType.
  
  Definition pred0 := pred false.
  Definition succ0 := succ false.

  Definition DFUDS_children B v := succ0 B v - v.

  Definition DFUDS_bits (t : tree A) := (number_of_nodes t).*2 - 1.
  
  Fixpoint DFUDS_position (t : tree A) (p : seq nat) := 3 +
    match t, p with
    | Node _ ch, [::] => 1
    | Node _ ch, h :: p' =>
      (size ch).+1 +
      sumn [seq (DFUDS_bits t') | t' <- take h ch] +
      DFUDS_position (nth t ch h) p'
    end.

  Lemma count_nseq {T : eqType} n (x y : T) : count_mem y (nseq n x) = if x == y then n else 0.
  Proof.
    elim: n x y => [| n IH] x y //=. by rewrite if_same.
    rewrite IH. case: ifP => Heq; by rewrite ?add1n ?addn0.
  Qed.

  Lemma double_gt1 n : (1 < n.*2) = (0 < n).
  Proof. by elim: n. Qed.
  
  Lemma DFUDS_bits_pos t : DFUDS_bits t > 0.
  Proof.
    rewrite /DFUDS_bits -(ltn_add2r 1) subn1 !addn1 prednK;
    by rewrite ?double_gt1 ?double_gt0 number_of_nodes_gt0.
  Qed.

  Lemma DFUDS_pos_gt_3 t p : DFUDS_position t p > 3.
  Proof.
    elim: p => [| n p IHp] //=; try (move: IHp); case: t => k ch //=.
  Qed.

  Lemma DFUDS_pos_pos t p : DFUDS_position t p > 0.
  Proof. apply: (leq_trans (n := 4)) => //=. apply: DFUDS_pos_gt_3. Qed.
  
  Lemma DFUDS_pos_node_gt_4 t n p : DFUDS_position t (n :: p) > 4.
  Proof.
    case: t => k ch //=. rewrite -[X in X < _]addn1 ltn_add2l.
    rewrite addSn addSn. rewrite -[X in _ < X]addn1 -[X in X < _]add0n.
    rewrite ltn_add2r.
    case: ch => //=. by rewrite nth_nil //= !add0n DFUDS_pos_pos.
  Qed.

  Lemma rank_nseq {T: eqType} (b : T) i (x : T) n : i <= n -> rank b i (nseq n x) = if (x == b) then i else 0.
  Proof.
    elim: n i => [| n IH] i //= Hi.
    rewrite rank_nil. move: Hi. rewrite leqn0 => /eqP ->. by rewrite if_same.
    case i_pos: (i > 0).
    rewrite -[in LHS](@prednK i) //= rank_cons IH.
    case: ifP => Hif; by rewrite ?add1n ?prednK.
    by rewrite -(leq_add2r 1) !addn1 prednK.
    move/negbT: i_pos. rewrite -leqNgt leqn0 => /eqP ->.
    by rewrite rank_select.rank0 if_same.
  Qed.
  
  Lemma DFUDS_childrenE (t : tree A) (p : seq nat) :
    let B := DFUDS t in
    valid_position t p -> children t p = DFUDS_children B (DFUDS_position t p). 
  Proof.
  Admitted.
    
End children.


Section examples.

  Definition tr : tree nat :=
    Node 1 [:: Node 2 [:: Node 5 [::]; Node 6 [::]];
              Node 3 [::];
              Node 4 [:: Node 7 [::];
                        Node 8 [:: Node 10 [::]];
                        Node 9 [::]]].

  Eval compute in DFUDS tr.

  Eval compute in DFUDS_size tr.

  About DFUDS_position.

  Eval compute in DFUDS_position tr [:: 0].

  Eval compute in DFUDS (Node 1 [::]).

End examples.
