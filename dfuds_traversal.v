From mathcomp Require Import all_ssreflect.
Require Import compact_data_structures rank_select pred_succ.

(** DFUDS: Depth-First Unary Degree Sequence **)
(* The bit 0 is interpreted as (, bit 1 as ) *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section df_traversal.

  Variable A : eqType.
  Variable B : Type.
  Variable f : tree A -> B.

  About level_traversal.
  About flatten.      
  
  Fixpoint po_traversal_st (t : tree A) :=
    match t with
    | Node _ ch => (f t) :: flatten [seq (po_traversal_st t') | t' <- ch]
    end.
  
  Lemma po_traversal_st_size t : size (po_traversal_st t) = number_of_nodes t.
  Proof.
    elim/tree_ind_eqType: t => a l IH //=.
    rewrite /number_of_nodes //= !size_flatten /shape //=.
    move: IH. elim: l => [| c l IHl] //= IH.
    rewrite -addnS IHl. by rewrite (IH c) //= in_cons eq_refl.
    move=> x Hin. by rewrite IH //= in_cons Hin orbT.
  Qed.
  
End df_traversal.

Section df_traversal_facts.

  Lemma cons_eq {A} (x : A) s t : s = t -> x :: s = x :: t.
  Proof. by move => ->. Qed.

  Variable A : eqType.
  
  Lemma number_of_nodesE {B : Type} (f : tree A -> B):
    size \o [eta po_traversal_st f] =1 (@number_of_nodes A).
  Proof. move => tr //=. by rewrite po_traversal_st_size. Qed.
    
  Lemma nodesE (t : tree A) :
    let node t := match t with Node x _ => x end in
    nodes t = po_traversal_st node t.
  Proof.
    elim/tree_ind_eqType: t => a l //= IH.
    apply: cons_eq. move: IH. elim: l => [| c l IHl] IH //=.
    rewrite IHl. rewrite (IH c) //= in_cons eq_refl //=. move=> x Hin.
    apply: IH. by rewrite in_cons Hin orbT.
  Qed.
    
  Definition po_node_list (t : tree A) := po_traversal_st id t.
    
  Lemma po_traversal_st_map {B : Type} (f : tree A -> B) (t : tree A) :
    po_traversal_st f t = map f (po_node_list t).
  Proof.
    elim/tree_ind_eqType: t => a l IH //=. rewrite /po_node_list.
    rewrite map_flatten. apply: cons_eq. move: IH. elim: l => [| c l IHl] //= IH. 
    rewrite IHl. by rewrite (IH c) /po_node_list //= in_cons eq_refl.
    move=> x Hin. apply: IH. by rewrite in_cons Hin orbT.
  Qed.

  Lemma map_po_traversal_st {B T} (f : tree A -> B) (g : B -> T) :
    map g \o [eta po_traversal_st f] =1 po_traversal_st (g \o f).
  Proof.
    move=> t //=. elim/tree_ind_eqType: t => a l IH //=.
    rewrite map_flatten -map_comp. apply: cons_eq. move: IH.
    elim: l => [| c l IHl] //= IH. rewrite IHl //=.
    by rewrite (IH c) //= in_cons eq_refl.
    move=> x H. apply: IH. by rewrite in_cons H orbT.
  Qed.

  Lemma eq_po_traversal_st {B} (f f' : tree A -> B) :
    f =1 f' -> po_traversal_st f =1 po_traversal_st f'.
  Proof.
    move=> Heq t. elim/tree_ind_eqType: t => a l //= IH.
    rewrite Heq. apply: cons_eq. move: IH.
    elim: l => [| c l IHl] //= IH.
    rewrite IHl ?(IH c) //= ?in_cons ?eq_refl //=.
    move=> t H. apply: IH. by rewrite in_cons H orbT.
  Qed.
  
End df_traversal_facts.

Section df_traversal_lt.

  Variable A : eqType.
  Variable B : Type.
  Variable f : tree A -> B.
    
  Fixpoint po_traversal_lt (t : tree A) (p : seq nat) :=
    let cl := children_of_node t in
    match p with
    | [::] => [::]
    | n :: p' =>
      f t ::
        flatten [seq (po_traversal_st f t') | t' <- take n cl] ++
        po_traversal_lt (nth t cl n) p'
    end.
  
End df_traversal_lt.


Section df_traversal_lt_facts.

  Variable A : eqType.
    
  Fixpoint po_position (t : tree A) p :=
    let cl := children_of_node t in
    match p with
    | [::] => 0
    | n :: p' =>
      1 + sumn [ seq (number_of_nodes t') | t' <- take n cl ] +
      po_position (nth t cl n) p'
    end.
    
    
  Lemma po_traversal_lt_sizeE {B} (f : tree A -> B) (t : tree A) p :
    valid_position t p -> size (po_traversal_lt f t p) = po_position t p.
  Proof.
    elim: p t => [| n p IHp] //= t /andP [Hn HBV]. set cl := children_of_node t.
    apply/eqP. rewrite add1n addSn eqSS. apply/eqP.
    rewrite size_cat size_flatten.
    rewrite (IHp (nth t cl n)) /shape //= -map_comp.
    by rewrite (eq_map (number_of_nodesE f)).
  Qed.

  Lemma subCK m n : m + n - m = n.
  Proof. by rewrite addnC addnK. Qed.
  
  Lemma take_flatten {T} (s : seq (seq T)) n :
    take (sumn (shape (take n s))) (flatten s) = flatten (take n s).
  Proof.
    elim: n s => [| n IHn] s. by rewrite take0 //= take0.
    elim: s => [| h s IHs] //=. case Hn: (n <= size s).
    rewrite take_cat -if_neg -leqNgt leq_addr subCK IHn //=.
    move/negbT: Hn. rewrite -ltnNge => Hn.
    rewrite !take_oversize //=; try (by rewrite leq_eqVlt Hn orbT).
    by rewrite size_cat size_flatten leqnn.
  Qed.

  Lemma po_traversal_ltE {B} (f : tree A -> B) (t : tree A) p :
    valid_position t p -> po_traversal_lt f t p = take (po_position t p)
                                                      (po_traversal_st f t).
  Proof.
    move=> HBV. rewrite -(po_traversal_lt_sizeE f) //=. move: HBV.
    elim: p t=> [| n p IHp] t //=. by rewrite take0.
    rewrite size_cat map_take size_flatten.
    rewrite (IHp (nth t (children_of_node t) n)).
    elim/tree_ind_eqType: t => // a l IH /andP [Hn HBV] //=.
  Admitted.
    
  Lemma nth_in_range {T} (x0 x1 : T) s n : n < size s -> nth x0 s n = nth x1 s n.
  Proof.
    elim: s n => [| h s IHs] //= [| n IHn] //=. by rewrite IHs.
  Qed.
    
  Lemma map_po_traversal_lt {B T} (f : tree A -> B) (g : B -> T) (t : tree A) p :
    valid_position t p -> map g (po_traversal_lt f t p) = po_traversal_lt (g \o f) t p.
  Proof.
    elim/tree_ind_eqType: t p => a l //= IH p.
    elim: p => [| n p IHp] //=. move/andP => [Hn HBV].
    rewrite map_cat map_flatten -map_comp (eq_map (map_po_traversal_st f g)).
    rewrite (IH (nth (Node a l) l n)) //=. by apply: mem_nth.
  Qed.

  Lemma eq_po_traversal_lt {B} (f f' : tree A -> B) :
    f =1 f' -> po_traversal_lt f =2 po_traversal_lt f'.
  Proof.
    move=> Heq t p. elim/tree_ind_eqType: t p => a l //= IH p.
    elim: p => [| n p IHp] //=.
    case Hn: (n < size l).
    rewrite (IH (nth (Node a l) l n)) //=.
    rewrite (eq_map (eq_po_traversal_st Heq)) Heq //=. by apply: mem_nth.
    move/negbT: Hn. rewrite -leqNgt => Hn. rewrite take_oversize //=.
    by rewrite (eq_map (eq_po_traversal_st Heq)) Heq //= nth_default //= IHp. 
  Qed.
    
End df_traversal_lt_facts.

Section dfuds.

  Variable A : eqType.
  
  Definition describe_node (t : tree A) :=
    let cl := children_of_node t in
    rcons (nseq (size cl) true) false.

  Definition DFUDS_st (t : tree A) := po_traversal_st describe_node t.

  Definition DFUDS_lt (t : tree A) p := po_traversal_lt describe_node t p.

  Definition DFUDS (t : tree A) :=
    [:: true; true; false] ++ flatten (DFUDS_st t).

  Definition description_length (t : tree A) :=
    let cl := children_of_node t in (size cl).+1.

  Lemma description_lengthE : size \o describe_node =1 description_length.
  Proof.
    move=> t. case: t => ? ? //=. rewrite /describe_node /description_length.
    by rewrite size_rcons size_nseq.
  Qed.
  
  Definition DFUDS_position t p :=
    let desc_l := po_traversal_lt description_length t p in
    4 + sumn desc_l.

  Lemma description_traversal_ok : [eta po_traversal_st description_length] =1
    map size \o [eta po_traversal_st describe_node].
  Proof.
    move=> t. elim/tree_ind_eqType: t => a l IH //=.
    rewrite {1}/description_length {1}/describe_node //=.
    rewrite size_rcons size_nseq map_flatten //= -map_comp.
    apply: cons_eq. move: IH. elim: l => [| c l IHl] //= IH.
    rewrite IHl. rewrite (IH c) //= in_cons eq_refl //=.
    move=> x H. apply: IH. by rewrite in_cons H orbT.
  Qed.
    
  Lemma DFUDS_positionE t p : valid_position t p ->
    DFUDS_position t p = 4 + size (flatten (DFUDS_lt t p)).
  Proof.
    rewrite /DFUDS_position /DFUDS_lt size_flatten /shape => HBV.
    apply/eqP. rewrite eqn_add2l. apply/eqP. move: HBV.
    elim: p t => [| n p IHp] t //=. set cl := children_of_node t.
    move/andP => [Hn HBV]. rewrite map_cat !sumn_cat -description_lengthE //=.
    rewrite map_flatten -map_comp IHp //=.
    apply/eqP. rewrite eqn_add2l eqn_add2r. apply/eqP.
    rewrite !sumn_flatten //= -!map_comp.
    have H_eqf: (sumn \o [eta po_traversal_st description_length]) =1
      (sumn \o (map size \o [eta po_traversal_st describe_node])).
    apply: eq_comp => //=. apply: description_traversal_ok.
    by rewrite (eq_map H_eqf).
  Qed.
    
  Definition addn4s m n p q : q <= p -> m + n + p - q = m + n + (p - q).
  Proof. move=> ?. by rewrite addnBA. Qed.
    
  Lemma addnAA m n p q : m + n + p + q = m + (n + p) + q.
  Proof. by rewrite addnA. Qed.
  
  Lemma DFUDS_sizeE t : size (DFUDS t) = (number_of_nodes t).*2.+2.
  Proof.
    rewrite /DFUDS /DFUDS_st size_cat /number_of_nodes.
    elim/tree_ind_eqType: t => a l //= IH.
    rewrite size_cat {1}/describe_node size_rcons size_nseq //=.
    rewrite /number_of_nodes //=.
    elim: l IH => [| c l IHl] //= IH.
    rewrite flatten_cat size_cat. rewrite ![X in 3 + X]addSn.
    rewrite addnA -addSn -addnS [X in 3 + X]addnC.
    rewrite addnA addnACA addnA addnAA IHl.
    rewrite doubleS addSn addnS -addn3 -addnA (IH c) //=.
    by rewrite size_cat -[in RHS]addSn doubleD doubleS !addnS !addSn addnC.
    by rewrite in_cons eq_refl. move=> x Hin. apply: IH.
    by rewrite in_cons Hin orbT.
  Qed.
    
End dfuds.

Section children.

  Variable A : eqType.

  Definition root := 4.

  Definition DFUDS_children B v := succ false B v - v.

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

  Lemma count_nseq {T : eqType} n (x y : T) : count_mem y (nseq n x) = if x == y then n else 0.
  Proof.
    elim: n x y => [| n IH] x y //=. by rewrite if_same.
    rewrite IH. case: ifP => Heq; by rewrite ?add1n ?addn0.
  Qed.
  
  Lemma po_traversal_lt_flatten_take {B} (f : tree A -> seq B) (t : tree A) p :
    valid_position t p ->
    take (sumn (po_traversal_lt (size \o f) t p))
         (flatten (po_traversal_st f t)) =
    flatten (po_traversal_lt f t p).
  Proof.
    move=> HBV. rewrite -map_po_traversal_lt //= po_traversal_ltE //=.
    by rewrite -take_flatten /shape.
  Qed.
    
  Lemma DFUDS_childrenE (t : tree A) (p : seq nat) :
    let B := DFUDS t in
    valid_position t p -> children t p = DFUDS_children B (DFUDS_position t p). 
  Proof.
    move=> B HBV. rewrite /DFUDS_children DFUDS_positionE //=.
    rewrite /succ /rank /B {B} /DFUDS add4n succnK //= !add0n add1n.
    rewrite /DFUDS_lt /DFUDS_st size_flatten /shape.
    rewrite (map_po_traversal_lt (describe_node (A:=A)) size) //=.
    rewrite po_traversal_lt_flatten_take //=.
    rewrite po_traversal_ltE //=. move: HBV.

    elim: p t => [| n p IHp] //= t //=.
    rewrite /children //= take0 //=.
    case: t => a l //=. rewrite {1}/describe_node select_cat.
    rewrite -cats1 count_cat count_nseq //= select_cat count_nseq //=.
    by rewrite size_nseq addn1 -addn4 addnK.
    case: t => a l //=. move/andP => [Hn HBV] //=.
    rewrite /children //= -addnE {1}/describe_node //= count_cat -cats1.
    rewrite count_cat count_nseq //= add0n addn0 //=.
    rewrite select_cat {2}/describe_node -cats1 count_cat count_nseq //=.
    rewrite {1 3}/describe_node //= size_rcons size_nseq //=.
    rewrite -cats1 count_cat count_nseq //= addn0 add0n add1n subn1 succnK.
    admit.
  Admitted.
    
End children.

Section examples.

  Definition tr : tree nat :=
    Node 1 [:: Node 2 [:: Node 5 [::]; Node 6 [::]];
              Node 3 [::];
              Node 4 [:: Node 7 [::];
                        Node 8 [:: Node 10 [::]];
                        Node 9 [::]]].

  Eval compute in nodes tr.

  Definition po_valid (t : tree nat) p := po_position t p < number_of_nodes t.
  
  Definition node (t : tree nat) := match t with Node x _ => x end.
  
  Eval compute in po_traversal_lt node tr [:: 2; 1].
  Eval compute in po_position tr [:: 2; 1].
  Eval compute in take (po_position tr [:: 2; 1]) (po_traversal_st node tr).
  
  Example height_tr : height tr = 4.
  Proof. rewrite //= !big_nil !big_cons !big_nil //=. Qed.

  Eval compute in DFUDS_lt tr [:: 2; 1].
  Eval compute in sumn (shape (DFUDS_lt tr [:: 2; 1])).

  Eval compute in DFUDS_position tr [:: 2; 2].
 
  
  

  Eval compute in nth 0 (po_traversal_st node tr) 7.
  
End examples.
