From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.

Require Import compact_data_structures rank_select insert_delete Program JMeq set_clear Wf_nat Compare_dec ExtrOcamlNatInt.

Set Implicit Arguments.

Tactic Notation "remember_eq" constr(expr) ident(vname) ident(eqname) := case (exist (fun x => x = expr) expr erefl) => vname eqname.

Section dynamic_dependent.

(* NB: same code in dynamic_dependent_program.v *)
Variable w : nat.
Hypothesis wordsize_gt1: w > 1.

Lemma wordsize_gt0 : w > 0.
Proof. exact/ltnW/wordsize_gt1. Qed.

Lemma wordsize_neq0 : w != 0.
Proof. rewrite -lt0n; exact wordsize_gt0. Qed.

Lemma wordsize_sqrn_gt0 : w ^ 2 > 0.
Proof. by rewrite sqrn_gt0 lt0n wordsize_neq0. Qed.

Lemma wordsize_sqrn_gt2 : w ^ 2 > 2.
Proof. by move: wordsize_gt1; case: w => // -[//|] []. Qed.

Lemma wordsize_sqrn_div2_neq0 : w ^ 2 %/ 2 <> 0.
Proof.
by move/eqP; rewrite gtn_eqF // divn_gt0 // (ltn_trans _ wordsize_sqrn_gt2).
Qed.

Section insert.
  Inductive color := Red | Black.

  (* due to technical reason *)
  Inductive tree_ml : Type :=
  | LeafML : forall(arr : seq bool), tree_ml
  | NodeML : forall(s1 s2 o1 o2 : nat) (c : color) (l r : tree_ml), tree_ml.
  (*                         *)

  Definition color_ok parent child : bool :=
    match parent,child with
    | Red,Red => false
    | _,_ => true
    end.

  Definition incr_black d c :=
    match c with
    | Black => d.+1
    | _ => d
    end.

  Definition is_black c :=
    match c with
    | Black => true
    | _ => false
    end.

  Lemma incr_black_prop d c : incr_black d c = d + is_black c.
  Proof. case: c => //=. by rewrite addn1. Qed.

  Definition inv c :=
    match c with
    | Black => Red
    | Red => Black
    end.

  Inductive param (A : Type) : Prop := Param : A -> param A.

  Definition inc_black d c :=
    match c, d with
    | Black, n => n.+1
    | _, _ => d
    end.

  (* Definition app_param (A B : Type) (f : A -> B) (x : param A) := *)
  (*   let: Param x := x in Param (f x). *)

  (* work around for program fixpoint *)
  Definition count_one arr := count_mem true arr.

  Inductive tree : nat -> nat -> nat -> color -> Type :=
  | Leaf : forall (arr : seq bool),
      (w ^ 2) %/ 2 <= size arr ->
      2 * (w ^ 2) > size arr ->
      tree (size arr) (count_one arr) 0 Black
  | Node : forall {s1 o1 s2 o2 d cl cr c},
      color_ok c cl -> color_ok c cr ->
      tree s1 o1 d cl -> tree s2 o2 d cr ->
      tree (s1 + s2) (o1 + o2) (inc_black d c) c.

  Fixpoint size_of_tree {s o d c} (t : tree s o d c) : nat :=
    match t with
    | Leaf _ _ s => 1
    | Node _ _ _ _ _ _ _ _ _ _ l r => size_of_tree l + size_of_tree r
    end.

  Lemma size_of_tree_pos num ones d c (B : tree num ones d c) :
    size_of_tree B > 0.
  Proof.
    elim: B => //= lnum lones rnum rones d' cl cr c' ok_l ok_r l IHl r IHr.
    by rewrite addn_gt0 IHl orTb.
  Qed.

  Definition rb_ok: color_ok Red Black := erefl.

  Definition bx_ok x : color_ok Black x := erefl.

  Definition rnode {s1 s2 o1 o2 d} (l : tree s1 o1 d Black)
             (r : tree s2 o2 d Black) : tree (s1 + s2) (o1 + o2) d Red :=
    Node rb_ok rb_ok l r.

  Definition bnode {s1 s2 o1 o2 d cl cr} (l : tree s1 o1 d cl)
             (r : tree s2 o2 d cr)
           : tree (s1 + s2) (o1 + o2) (inc_black d Black) Black :=
    Node (bx_ok cl) (bx_ok cr) l r.

  Inductive near_tree : nat -> nat -> nat -> color -> Type :=
  | Bad : forall {s1 o1 s2 o2 s3 o3 d},
      tree s1 o1 d Black ->
      tree s2 o2 d Black ->
      tree s3 o3 d Black ->
      near_tree (s1 + s2 + s3) (o1 + o2 + o3) d Red
  | Good: forall {s o d c} p,
      tree s o d c ->
      near_tree s o d p.

  (* Xuanrui: I see no point to define fix_color in Ltac...
   * Gallina would be much more readable here
   * Kazunari: I totally agree. sorry for being lazy. 
   *)
  
  Definition fix_color {nl ml d c} (l : near_tree nl ml d c) :=
    match l with
    | Bad _ _ _ _ _ _ _ _ _ _ => Red
    | Good _ _ _ _ _ _ => Black
    end.

  (* Xuanrui: same, programming those in Ltac makes little sense to me *)

  Definition black_of_bad {nl ml d c} (l : near_tree nl ml d c) :=
    match l with
    | Bad _ _ _ _ _ _ _ _ _ _ => Black
    | Good _ _ _ c _ _ => c
    end.

  Definition real_tree {nl ml d c} (t : near_tree nl ml d c) : tree nl ml (inc_black d (inv (fix_color t))) (black_of_bad t) :=
    match t with
    | Bad _ _ _ _ _ _ _ x y z => bnode (rnode x y) z
    | Good _ _ _ _ _ t' => t'
    end.
  
  Fixpoint dflatten {n m d c} (B : tree n m d c) :=
    match B with
    | Node _ _ _ _ _ _ _ _ _ _ l r => dflatten l ++ dflatten r
    | Leaf s _ _ => s
    end.

  Lemma dflatten_sizeK {n m d c} (B : tree n m d c) : size (dflatten B) = n.
  Proof.
    elim: B => //= nl ol nr or d' cl cr c' Hok Hok' l IHl r IHr.
    by rewrite size_cat IHl IHr.
  Qed.

  Lemma dflatten_countK {n m d c} (B : tree n m d c) : count_one (dflatten B) = m.
  Proof.
    elim: B => //= nl ol nr or d' cl cr c' Hok Hok' l IHl r IHr.
    rewrite /count_one in IHl,IHr.
    by rewrite /count_one count_cat IHl IHr.
  Qed.
  
  Definition dflattenn {n m d c} (B : near_tree n m d c) :=
    match B with
    | Bad _ _ _ _ _ _ _ x y z => dflatten x ++ dflatten y ++ dflatten z
    | Good _ _ _ _ _ t => dflatten t
    end.

  Definition balanceL {nl ml d cl cr nr mr} (p : color) (l : near_tree nl ml d cl) (r : tree nr mr d cr) :
    color_ok p (fix_color l) (* important claim! *) ->
    color_ok p cr -> 
    {tr : near_tree (nl + nr) (ml + mr) (inc_black d p) p | dflattenn tr = dflattenn l ++ dflatten r}.

    destruct l as [s1 o1 s2 o2 s3 o3 d' x y z | s o d' c' cc l'].
    (* l is bad *)
    + case: p => //= cpl cpr.
      rewrite -(addnA (s1 + s2)) -(addnA (o1 + o2)).
      exists (Good Black (rnode (bnode x y) (bnode z r))).
      by rewrite /= !catA.
    (* l is good *)
    + case: p => /= cpl cpr; last by exists (Good Black (bnode l' r)).
      case Hc': c' in cpl.
      (* bad pattern (c' and p are red) *)
      - destruct l' as [|s1 o1 s2 o2 d cl' cr' c' w1 w2 l'1 l'2] => //.
        subst c'; destruct cl', cr', cr => //.
        exists (Bad l'1 l'2 r).
        by rewrite /= !catA.
      (* otherwise *)
      - subst c'; destruct cr => //.
        by exists (Good Red (rnode l' r)).
  Defined.

  Definition balanceR {nl ml d cl cr nr mr} (p : color) (l : tree nl ml d cl) (r : near_tree nr mr d cr):
    color_ok p cl ->
    color_ok p (fix_color r) ->  (* important claim! *)
    {tr : near_tree (nl + nr) (ml + mr) (inc_black d p) p | dflattenn tr = dflatten l ++ dflattenn r}.

    destruct r as [s1 o1 s2 o2 s3 o3 d' x y z | s o d' c' cc r'].
    (* r is bad *)
    + case: p => //= cpl cpr.
      rewrite -!addnA [nl + (s1 + (s2 + s3))]addnA [ml + (o1 + (o2 + o3))]addnA.
      exists (Good Black (rnode (bnode l x) (bnode y z))).
      by rewrite /= !catA.
    (* r is good *)
    + case: p => /= cpl cpr; last by exists (Good Black (bnode l r')).
      case Hc': c' in cpr.
      (* bad pattern (c' and p are red) *)
      - destruct r' as [|s1 o1 s2 o2 d cl' cr' c' w1 w2 r'1 r'2] => //=.
        subst c'; destruct cl', cr', cl => //.
        rewrite !addnA.
        by exists (Bad l r'1 r'2).
      (* otherwise *)
      - subst c'; destruct cl => //.
        by exists (Good Red (rnode l r')).
  Defined.

  Lemma dflatten_size num ones d c (B : tree num ones d c) :
    num = size (dflatten B).
  Proof.
    elim: B => //= s1 o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr.
    by rewrite size_cat -IHl -IHr.
  Qed.

  Program Fixpoint dinsert' {n m d c} (B : tree n m d c) (b : bool) i
          {measure (size_of_tree B)} : { B' : near_tree n.+1 (m + b) d c
                              | dflattenn B' = insert1 (dflatten B) b i } :=
    match B with
    | Leaf s _ _ =>
      let s' := insert1 s b i in
      match size s' == 2 * (w ^ 2) with
      | true => let n  := (size s') %/ 2 in
                let sl := take n s' in
                let sr := drop n s' in
                Good c (rnode (Leaf sl _ _) (Leaf sr _ _))
      | false => Good c (Leaf s' _ _)
      end
    | Node s1 o1 s2 o2 d cl cr _ okl okr l r =>
      if i < s1
      then proj1_sig (balanceL c (dinsert' l b i) r _ okr)
      else proj1_sig (balanceR c l (dinsert' r b (i - s1)) okl _)
    end.
  
  Next Obligation.
    move/eqP/eqnP : Heq_anonymous => /=.
    rewrite size_take size_insert1.
    move => H.
    rewrite H.
    case: ifP => H2. by rewrite mulKn // leq_div //.
    have H3 : w ^ 2 %/ 2 <= w ^ 2. by rewrite leq_div.
    have H4 : w ^ 2 <= 2 * w ^ 2. by rewrite leq_pmull.
    by move:(leq_trans H3 H4).
  Qed.

  Next Obligation.
    move/eqP/eqnP : Heq_anonymous => /=.
    rewrite size_take size_insert1.
    move => H.
    rewrite H mulnC.
    case: ifP => //.
    rewrite mulnK //.
    have H2 : w ^ 2 > 0. by rewrite expn_gt0 wordsize_gt0.
    have H3 : w ^ 2 < w ^ 2 * 2. by rewrite -{1}[w ^ 2]muln1 ltn_mul2l H2 /=.
    by rewrite H3.
  Qed.

  Next Obligation. 
    move/eqP/eqnP : Heq_anonymous => /=.
    rewrite size_drop size_insert1.
    move => H.
    by rewrite H mulKn // mulSn mul1n -addnBA // subnKC // leq_div.
  Qed.

  Next Obligation. 
    move/eqP/eqnP : Heq_anonymous => /=.
    rewrite size_drop size_insert1.
    move => H.
    by rewrite H mulKn // mulSn mul1n -addnBA // subnKC // -{1}[w ^ 2]addn0 ltn_add2l expn_gt0 wordsize_gt0.
  Qed.

  Next Obligation. by rewrite -size_cat cat_take_drop size_insert1. Qed.

  Next Obligation.
    rewrite -count_cat cat_take_drop /count_one count_insert1.
    by destruct b.
  Qed.

  Next Obligation.
    rewrite /dflattenn /insert1.
    destruct dinsert'_func_obligation_5, dinsert'_func_obligation_6 => /=.
    by rewrite cat_take_drop.
  Qed.

  Next Obligation.
    rewrite size_insert1.
    by apply: leq_trans.
  Qed.

  Next Obligation.
    move/eqP/eqnP/eqP: Heq_anonymous => /=.
    rewrite size_insert1 neq_ltn.
    case/orP => //.
    by rewrite ltnNge wildcard'0.
  Qed.

  Next Obligation. by rewrite size_insert1. Qed.

  Next Obligation. rewrite /count_one count_insert1. by destruct b. Qed.

  Next Obligation.
    rewrite /dflattenn /insert1.
    by destruct dinsert'_func_obligation_11, dinsert'_func_obligation_12, dinsert'_func_obligation_13 => /=.
  Qed.

  Next Obligation.
    apply /ltP; by rewrite -Heq_B /= -[X in X < _]addn0 ltn_add2l size_of_tree_pos.
  Qed.

  Next Obligation. by destruct dinsert',x,c. Qed.

  Next Obligation.
    apply /ltP; by rewrite -Heq_B /= -[X in X < _]add0n ltn_add2r size_of_tree_pos.
  Qed.

  Next Obligation. by destruct dinsert',x,c. Qed.

  Next Obligation. by rewrite -addn1 -[RHS]addn1 addnA. Qed.

  Next Obligation. by rewrite [o2 + b]addnC addnA. Qed.

  Next Obligation. by rewrite -[RHS]addnA [o2 + b]addnC addnA. Qed.

  Next Obligation.
    case: ifP => /= H.
    - set B' := balanceL _ _ _ _ _.
      destruct dinsert'_func_obligation_23.
      rewrite (proj2_sig B') {B'}.
      destruct dinsert' => /=.
      by rewrite e /insert1 /insert take_cat drop_cat -dflatten_size H -!catA.
    - set B' := balanceR _ _ _ _ _.
      rewrite /dflattenn /eq_rect => /=.
      destruct dinsert'_func_obligation_23, dinsert'_func_obligation_22, dinsert'_func_obligation_21.
      rewrite -/(dflattenn (proj1_sig B')) (proj2_sig B') {B'}.
      destruct dinsert' => /=.
      by rewrite e /insert1 /insert take_cat drop_cat -dflatten_size H -!catA.
  Qed.

  Definition dinsert n m d c (B : tree n m d c) (b : bool) (i : nat) :=
    real_tree (proj1_sig (dinsert' B b i)).

  Lemma real_treeK nl ol d c (t : near_tree nl ol d c) :
    dflatten (real_tree t) = dflattenn t.
  Proof. case: t => //= n1 o1 n2 o2 n3 o3 d' x y z. by rewrite catA. Qed.
  
  Lemma dinsertK n m d c (B : tree n m d c) b i :
    dflatten (dinsert B b i) = insert1 (dflatten B) b i.
  Proof. by rewrite /dinsert real_treeK (proj2_sig (dinsert' B b i)). Qed.
  
End insert.

Section query.
  
  Fixpoint daccess {n m d c} (tr : tree n m d c) i :=
    match tr with
    | Leaf s _ _ => nth false s i
    | Node lnum _ _ _ _ _ _ _ _ _ l r =>
      if i < lnum
      then daccess l i
      else daccess r (i - lnum)
    end.

  Fixpoint drank {n m d c} (tr : tree n m d c) i :=
    match tr with
    | Leaf s _ _ => rank true i s
    | Node lnum lones rnum rones _ _ _ _ _ _ l r =>
      if i < lnum
      then drank l i
      else lones + drank r (i - lnum)
    end.

  Fixpoint dselect_0 {n m d c} (tr : tree n m d c) i :=
    match tr with
    | Leaf s _ _ => select false i s
    | Node s1 o1 s2 o2 _ _ _ _ _ _ l r =>
      let zeroes := s1 - o1
      in if i <= zeroes 
      then dselect_0 l i
      else s1 + dselect_0 r (i - zeroes)
    end.

  Fixpoint dselect_1 {n m d c} (tr : tree n m d c) i :=
    match tr with
    | Leaf s _ _ => select true i s
    | Node s1 o1 s2 o2 _ _ _ _ _ _ l r =>
      if i <= o1
      then dselect_1 l i
      else s1 + dselect_1 r (i - o1)
    end.

  Definition access (s : seq bool) i := nth false s i.

  Lemma dflatten_ones num ones d c (B : tree num ones d c) :
    ones = count_mem true (dflatten B).
  Proof.
    elim: B => //= s1 o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr.
    by rewrite count_cat -IHl -IHr.
  Qed.

  Lemma predC_bool b : predC (pred1 b) =1 pred1 (negb b).
  Proof. by case. Qed.

  Lemma count_mem_false_true (s : seq bool) :
    count_mem false s + count_mem true s = size s.
  Proof.
    by rewrite -(count_predC (pred1 false)) (eq_count (predC_bool false)).
  Qed.

  Lemma ones_lt_num num ones d c (B : tree num ones d c) :
    ones <= num.
  Proof.
    by rewrite (dflatten_ones B) [in X in _ <= X](dflatten_size B) count_size.
  Qed.

  Lemma dflatten_zeroes num ones d c (B : tree num ones d c) :
    num - ones = count_mem false (dflatten B).
  Proof.
    rewrite [in LHS](dflatten_ones B) [in X in X - _](dflatten_size B).
    apply/eqP. rewrite -(eqn_add2r (count_mem true (dflatten B))) subnK.
      by rewrite count_mem_false_true.
    by rewrite -(dflatten_ones B) -(dflatten_size B)(ones_lt_num B).
  Qed.
    
  Lemma dflatten_rank num ones d c (B : tree num ones d c) :
    ones = rank true num (dflatten B).
  Proof.
    by rewrite /rank [X in take X _](dflatten_size B) take_size -dflatten_ones.
  Qed.
    
  Lemma daccessK nums ones d c (B : tree nums ones d c) :
    daccess B =1 access (dflatten B).
  Proof.
    rewrite /access.
    elim: B => //= lnum o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr x.
    by rewrite nth_cat -dflatten_size -IHl -IHr.
  Qed.

  Lemma drankK nums ones d c (B : tree nums ones d c) i :
    drank B i = rank true i (dflatten B).
  Proof.
    elim: B i => //= lnum o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr x.
    by rewrite rank_cat -dflatten_size IHl -IHr -dflatten_rank.
  Qed.

  Lemma drank_ones num ones d c (B : tree num ones d c) :
    drank B num = ones.
  Proof.
    by rewrite [in RHS](dflatten_rank B) drankK.
  Qed.

  Lemma dselect1K nums ones d c (B : tree nums ones d c) i :
    dselect_1 B i = select true i (dflatten B).
  Proof.
    elim: B i => //= lnum o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr x.
    by rewrite select_cat -dflatten_ones IHl IHr -dflatten_size. 
  Qed.

  Lemma dselect0K nums ones d c (B : tree nums ones d c) i :
    dselect_0 B i = select false i (dflatten B).
  Proof.
    elim: B i => //= lnum o1 s2 o2 d0 cl cr c0 i i0 l IHl r IHr x.
    by rewrite select_cat -dflatten_zeroes IHl IHr -dflatten_size.
  Qed.
  
End query.

(* Section added by Xuanrui
 * because I wanted to experiment with this version as well...
 * 
 * Feel free to comment this out or remove this...
 *)


Section set_clear.

  Obligation Tactic := idtac.
  
  Program Fixpoint bset {num ones d c} (B : tree num ones d c) i
    {measure (size_of_tree B)} :
    { B'b : tree num (ones + (~~ (daccess B i)) && (i < num)) d c * bool
    | dflatten (fst B'b) = bit_set (dflatten B) i/\snd B'b = ~~ daccess B i } :=
    match B with
    | Leaf s _ _ => (Leaf (bit_set s i) _ _, ~~ (access s i))
    | Node lnum lones rnum rones _ _ _ _ col cor l r =>
      match lt_dec i lnum with
      | left H =>
        let x := bset l i
        in (Node col cor x.1 r, x.2)
      | right H =>
        let x := bset r (i - lnum)
        in (Node col cor l x.1, x.2)
      end
    end.

  Next Obligation. intros. by rewrite size_bit_set. Qed.

  Next Obligation. intros. by rewrite size_bit_set. Qed.
  
  Next Obligation. intros; apply: size_bit_set. Qed.

  Next Obligation.
    intros; case Hi: (i < size s).
    rewrite /count_one /daccess (count_bit_set false). by rewrite andbT addnC.
    by rewrite Hi.
    rewrite andbF addn0. by rewrite /count_one /daccess bit_set_over //= leqNgt Hi.
  Qed.

  Next Obligation.
    intros; subst; split => //.
    by destruct bset_func_obligation_4 , bset_func_obligation_3 => /=.
  Qed.

  Next Obligation.
    intros; subst. apply /ltP.
    rewrite -Heq_B /=.
    by rewrite -addn1 leq_add2l size_of_tree_pos.
  Qed.

  Next Obligation.
    intros; move/ltP: (H) => Hi /=.
    by rewrite Hi (ltn_addr _ Hi) addnAC.
  Qed.

  Next Obligation.
    split; subst; last first.
      destruct bset as [[l' flip][Hl' Hf]] => /=.
      move/ltP: (H) => ->.
      by rewrite -Hf.
    move=> /=.
    move: (lones + rones + _) (bset_func_obligation_7 _ _ _ _ _ _) => ones Ho.
    destruct Ho => /=.
    destruct bset as [[l' flip][Hl' Hf]] => /=.
    rewrite /= in Hl'.
    move/ltP: (H).
    rewrite Hl' /bit_set update_cat -{1}(dflatten_size l) => Hi.
    by rewrite ifT.
  Qed.

  Next Obligation.
    intros; subst. apply /ltP.
    rewrite -Heq_B /=.
    by rewrite -add1n leq_add2r size_of_tree_pos.
  Qed.

  Next Obligation.
    intros; move/ltP: (H) => Hi /=.
    rewrite -if_neg Hi !addnA.
    by rewrite -(ltn_add2l lnum) subnKC // leqNgt.
  Qed.

  Next Obligation.
    split; subst; last first.
      destruct bset as [[r' flip][Hr' Hf]] => /=.
      move/ltP: (H) => Hi.
      by rewrite -if_neg Hi -Hf.
    move=> /=.
    move: (lones + rones + _) (bset_func_obligation_10 _ _ _ _ _ _) => ones Ho.
    destruct Ho => /=.
    destruct bset as [[r' flip][Hr' Hf]] => /=.
    rewrite /= in Hr'.
    move/ltP: (H).
    rewrite Hr' /bit_set update_cat -(dflatten_size l) => Hi.
    by rewrite -if_neg Hi.
  Qed.

  Next Obligation. intuition. Qed.

End set_clear.

Section delete.

  Lemma count_delete {arr i} : count_one arr - nth false arr i = count_one (delete arr i).
  Proof.
    case_eq (i < (size arr)) => H.
     rewrite -(cat_take_drop i arr) /delete /count_one !count_cat cat_take_drop (drop_nth false) // -/(cat [:: nth false arr i] _) count_cat /= addn0.
     case: (nth false arr i) => /=.
      by rewrite [1 + _]addnC addnA addn1 subn1 -[_.+1]subn0 subSKn subn0.
     by rewrite add0n subn0.
    rewrite ltnNge in H.
    move/negPn : H => H.
    rewrite nth_default /count_one /delete // take_oversize // drop_oversize.
     by rewrite count_cat /= addn0 subn0.
    by apply: leqW.
  Qed.

  Lemma count_delete' {s o} (tr : tree s o 0 Black) (i : nat) : o - (daccess tr i) = count_one (delete (dflatten tr) i).
  Proof.
    remember_eq 0 d' deq. remember_eq Black c' ceq. move: tr. rewrite -deq -ceq => tr. destruct tr as [arr leq ueq|];last by rewrite ceq /= in deq.
    by apply count_delete.
  Qed.

  Lemma delete_oversize {arr : seq bool} {i} : size arr <= i -> arr = delete arr i.
  Proof.
    move => H.
    rewrite /= /delete take_oversize // drop_oversize.
     by rewrite cats0.
     by apply: leqW.
  Qed.

  Lemma daccess_default {n m d c} (tr : tree n m d c) : forall(i : nat), n <= i -> (daccess tr i) = false.
  Proof.
    elim: tr => /=. intros; by rewrite nth_default //.
    intros.
    case: ifP => H2.
     move: (ltn_addr s2 H2) => H3.
     move: (leq_ltn_trans H1 H3).
     by rewrite ltnn.
    move: (leq_sub2r s1 H1).
    rewrite addKn => H3.
    by apply: (H0 (i1 - s1) H3).
  Qed.

  Lemma sizeW (arr : seq bool) : w ^ 2 %/ 2 <= size arr -> 0 < size arr.
  Proof.
    move/eqP: wordsize_sqrn_div2_neq0.
    rewrite -lt0n => ltn1.
    rewrite leq_eqVlt.
    case/orP => eq2. move/eqP: eq2 => eq2. by rewrite eq2 in ltn1.
    exact: (ltn_trans ltn1 eq2).
  Qed.

  Lemma delete_cat {arr arr' : seq bool} {i} : delete (arr ++ arr') i = (if i < size arr then delete arr i ++ arr' else arr ++ delete arr' (i - (size arr))).
  Proof.
    rewrite /delete take_cat -catA.
    case: ifP => H.
     rewrite drop_cat.
     case: ifP => // H2.
     move: (negbT H2).
     rewrite -leqNgt => H3.
     have H4 : i.+1 = size arr. apply/eqP. rewrite eqn_leq. by apply/andP.
     by rewrite H4 subnn drop0 drop_oversize //.
    rewrite drop_cat.
    case: ifP => H2. move: (ltnW H2). by rewrite H.
    move: (negbT H) (negbT H2).
    rewrite -!leqNgt => H3 H4.
    by rewrite catA subSn //.
  Qed.

  Lemma addnBAC a b c : a >= c -> (a + b) - c = (a - c) + b.
  Proof. by move => ?; rewrite addnC -addnBA // addnC. Qed.

  Lemma cons_head_behead (arr: seq bool) : (size arr) > 0 -> (access arr 0) :: (behead arr) = arr.
  Proof. case: arr => /= //. Qed.

  Lemma cat_head_behead (arr arr' : seq bool) : 0 < size arr' -> (rcons arr (access arr' 0)) ++ (delete arr' 0) = arr ++ arr'.
  Proof. move => H. rewrite !cat_rcons -!cat_cons take0 drop1 /= cons_head_behead //. Qed.

  Lemma cat_last_belast (arr arr' : seq bool) : 0 < size arr -> (delete arr (size arr).-1) ++ ((access arr (size arr).-1) :: arr') = arr ++ arr'.
  Proof.
    move => H.
    rewrite /delete /access drop_oversize;last by rewrite prednK.
    rewrite cats0.
    move: H.
    elim arr => // /= b arr'' IH.
    case H : (0 < size arr'').
     by rewrite -(IH H); destruct arr''.
    move/negP/negP in H.
    rewrite leqNgt in H.
    move/negPn in H.
    move: H.
    case arr'' => //.
  Qed.

  Lemma cons_delete {i} (arr arr' : seq bool) : 0 < size arr' -> 
                                                (rcons (delete arr i) (access arr' 0)) ++ (delete arr' 0) = (delete arr i) ++ arr'.
  Proof. move => H. rewrite !cat_rcons -!catA -cat_cons take0 drop1 /= cons_head_behead //. Qed.

  Lemma size_rcons_delete {arr : seq bool} (i : nat) (b : bool) : i < size arr -> size (rcons (delete arr i) b) = size arr.
  Proof.
    move => G.
    rewrite size_rcons size_delete // -addn1 -subn1 subnK //.
    case_eq i => [H|i' H]. by rewrite H in G.
    rewrite H in G.
    exact: (ltn_trans (ltn0Sn i') G).
  Qed.

  Lemma leq_size_catr (a : nat) (arr0 arr1 : seq bool) : a <= size arr1 -> a <= size (arr0 ++ arr1).
  Proof.
    rewrite size_cat.
    move => leq.
    apply: (leq_trans leq (leq_addl (size arr0) (size arr1))).
  Qed.

  Lemma ltn_size_cat (a b : nat) (arr0 arr1 : seq bool) : size arr0 < a ->
                                                          size arr1 < b ->
                                                          size (arr0 ++ arr1) < a + b.
  Proof.
    rewrite size_cat.
    move => ltn1 ltn2.
    rewrite -(ltn_add2r b) in ltn1.
    rewrite -(ltn_add2l (size arr0)) in ltn2.
    exact: (ltn_trans ltn2 ltn1).
  Qed.

  Lemma ltn_size_catb (a : nat) (arr0 arr1 : seq bool) : size arr0 < a ->
                                                         size arr1 < a ->
                                                         size (arr0 ++ arr1) < a.*2.
  Proof.
    move => H1 H2.
    rewrite -addnn.
    exact: (ltn_size_cat _ _ arr0 arr1 H1 H2).
  Qed.

  Lemma size_delete1 {arr : seq bool} (i : nat) : size arr = (size (delete arr i)) + (i < size arr).
  Proof.
    case_eq (i < size arr).
     move/idP => G.
     rewrite size_delete // -subn1 /= subnK //.
     case_eq i => [H|i' H]. by rewrite H in G.
     rewrite H in G.
     exact: (ltn_trans (ltn0Sn i') G).
    move/negP/negP => G.
    rewrite -leqNgt in G.
    rewrite /delete take_oversize // drop_oversize // /=;last first. exact: (leqW G).
    by rewrite cats0.
  Qed.

  Lemma leq_nth_count {i arr} : nth false arr i <= count_one arr.
  Proof.
    rewrite -(cat_take_drop i arr) /count_one count_cat nth_cat size_take.
    case: ifP. case: ifP => H. by rewrite ltnn. by rewrite H.
    case: ifP.
     rewrite subnn nth0 /head /(count_mem _).
     case (drop i arr) => // b.
     destruct b => //.
     case (take i arr) => // b.
     destruct b => // /= l r.
     rewrite add0n addnA ltn_addr // ltn_addl //.
    move/negP/negP => H ?.
    rewrite -leqNgt in H.
    rewrite nth_default;last first. rewrite size_drop. move/eqP: H => H. by rewrite H leq0n.
    by rewrite /= leq0n.
  Qed.

  Lemma divn2n0 {a} : (a %/ 2 == a) = (a == 0).
  Proof.
    case a => // a'.
    case a' => // a''.
    by rewrite -addn1 addn_eq0 addn1 {2}(divn_eq a''.+2 2) muln2 -addnn -addnA -{1}[a''.+2 %/ 2]addn0 eqn_add2l -addn1 andbF addn1 -addn2 divnDr // divnn /= eq_sym !addn_eq0 andbF andFb.
  Qed.

  Lemma leq_divn2n_mul2 : forall(a : nat),a > 0 -> a %/ 2 + a %/ 2 < 2 * a.
  Proof.
    move => // a H0.
    move: (leq_div a 2).
    rewrite leq_eqVlt.
    case/orP. rewrite divn2n0. move/eqP => H1. by rewrite H1 in H0.
    by rewrite mulnC addnn -muln2 ltn_mul2r /=.
  Qed.

Lemma leq_addln a b c : a <= b -> a <= b + c.
Proof. by move/leq_trans; apply; rewrite leq_addr. Qed.

Lemma leq_addrn a b c : a <= c -> a <= b + c.
Proof. by move/leq_trans; apply; rewrite leq_addl. Qed.

  Lemma ltn_subln a b c : c > 0 -> a < b + c = (a - b < c).
  Proof.
    case H1 : (b <= a) => H2. by rewrite -[RHS](ltn_add2r b) subnK // addnC.
    move: H1; rewrite leqNgt; move/negP/negP => H1.
    rewrite ltn_addr //. move: H1.
    case: b => // n H1.
    move/eqP: (ltnW H1) => W.
    by rewrite W H2.
  Qed.

  Lemma ltn_subrn a b c : b > 0 -> a < b + c = (a - c < b).
  Proof. rewrite addnC. exact: (ltn_subln a c b). Qed.

  Lemma sizeW' {s o d c} (tr : tree s o d c) : s > 0.
  Proof. elim tr; intros; first apply sizeW => //; rewrite ltn_addr //. Qed.

  Inductive near_tree' : nat -> nat -> nat -> color -> Type := 
  | Stay : forall {s o d c} p,
      color_ok c (inv p) ->
      tree s o d c -> near_tree' s o d p
  | Down : forall {s o d},
      tree s o d Black -> near_tree' s o d.+1 Black.

  Definition dflattenn' {s o d c} (tr : near_tree' s o d c) :=
    match tr with
    | Stay _ _ _ _ _ _ t => dflatten t
    | Down _ _ _ t =>  dflatten t
   end.

  Definition black_of_red {s o d} (B : tree s o d Red) : { B' : tree s o (inc_black d Black) Black | dflatten B' = dflatten B }.

    move: B; move ceq : (Red) => c' B.
    move: B ceq => [//|? ? ? ? ? cl cr c ? ? l r] /= <-.
    by exists (bnode l r).
  Defined.

  Lemma leq_access_count {s o d c} : forall(B : tree s o d c), forall(i : nat) , i < s -> daccess B i <= o.
  Proof.
    move => B.
    elim B => /=. intros. exact: leq_nth_count.
    move => s1 o1 s2 o2 d' cl cr c' ? ? l IHl r IHr.
    move => i H.
    case: ifP => H'. apply: leq_addln (IHl i H').
    apply: leq_addrn.
    move: (IHr (i - s1)).
    rewrite -(ltn_add2r s1) subnK ;last by rewrite leqNgt H' /=.
    rewrite addnC => H''.
    exact: (H'' H).
  Qed.

  Definition merge_arrays (a b : seq bool) (i : nat) (w1 : w ^ 2 %/ 2 == size a) (w2 : w ^ 2 %/ 2 == size b) (val : i < size a + size b) :
             {tr : tree (size a + size b - (i < size a + size b)) (count_one a + count_one b - (access (a ++ b) i)) 0 Black | dflatten tr = delete (a ++ b) i}.

    move/eqP : wordsize_sqrn_div2_neq0; rewrite -lt0n => pos.
    move/eqP: w1 => w1. move/eqP: w2 => w2. move: (pos); rewrite w1 => w1p. move: (pos); rewrite w2 => w2p.
    case Hl : (i < size a).
     have ueq : size ((rcons (delete a i) (access b 0)) ++ (delete b 0)) < 2 * w ^ 2.
      rewrite size_cat size_rcons !size_delete // prednK // -subn1 addnBA // subn1 -w1 -w2 ltnW // prednK //;last rewrite ltn_addl //.
      rewrite leq_divn2n_mul2 // wordsize_sqrn_gt0 //.
     have leq : size (rcons (delete a i) (access b 0) ++ delete b 0) >= w ^ 2 %/ 2.
      rewrite size_cat size_rcons !size_delete // prednK // w1 leq_addln //.
     rewrite ltn_addr // addnC -addnBA // subn1 -(size_delete Hl) /= addnC -size_cat delete_cat addnBAC /access nth_cat Hl; last rewrite leq_nth_count //.
     rewrite count_delete -count_cat -cat_head_behead //.
     by exists (Leaf ((rcons (delete a i) (access b 0)) ++ (delete b 0)) leq ueq).
    move: val; rewrite ltn_subln // => Hr.
    have ueq : size (a ++ (delete b (i - (size a)))) < 2 * w ^ 2.
     rewrite size_cat size_delete // -w1 -w2 -subn1 addnBA // subn1 ltnW // prednK //;last rewrite ltn_addl //.
     rewrite leq_divn2n_mul2 // wordsize_sqrn_gt0 //.
    have leq : size (a ++ (delete b (i - (size a)))) >= w ^ 2 %/ 2.
    rewrite size_cat size_delete //;last rewrite -{1}w1 w2 //.
      by rewrite leq_addln // w1.
      rewrite Hr -addnBA // subn1 -(size_delete Hr) -size_cat -addnBA /access nth_cat Hl ;last rewrite leq_nth_count //.
      rewrite count_delete -count_cat.
    exists (Leaf (a ++ (delete b (i - (size a)))) leq ueq).
    by rewrite /= delete_cat Hl.
  Qed.

  Lemma xir_ok {c} : color_ok c (inv Red).
  Proof. move: c => [] //. Qed.

  Definition delete_leaves2 {s1 o1 s2 o2} p (l : tree s1 o1 0 Black) (r : tree s2 o2 0 Black) (i : nat) :
    {B' : near_tree' (s1 + s2 - (i < s1 + s2))
                    (o1 + o2 - access (dflatten l ++ dflatten r) i) (inc_black 0 p) p | dflattenn' B' = delete (dflatten l ++ dflatten r) i}.

    move/eqP : wordsize_sqrn_div2_neq0 (sizeW' l) (sizeW' r); rewrite -lt0n => pos posl posr.
    remember_eq 0 d' deq; remember_eq Black c' ceq; move: l r; rewrite -ceq -deq => l; destruct l as [al leql ueql|]; last rewrite ceq /= // in deq.
    move => {deq ceq}; remember_eq 0 d' deq; remember_eq Black c' ceq; rewrite /= -ceq -deq => r; destruct r as [ar leqr ueqr|]; last rewrite ceq /= // in deq.

    rewrite /access nth_cat.
    case: ifP => Hl.
     case bcl : (w ^ 2 %/ 2 == size al).
      case bcr : (w ^ 2 %/ 2 == size ar).
       case (merge_arrays al ar i bcl bcr (ltn_addr _ Hl)).
       rewrite /access nth_cat Hl => res resK.
       case: p;[ by exists (Stay Red xir_ok res) | by exists (Down res)].
      rewrite /=.
      rewrite leq_eqVlt bcr (size_delete1 0) posr /= addn1 in leqr,ueqr.
      rewrite -(size_rcons_delete i (access ar 0)) // in leql,ueql.
      rewrite addnC -addnBA // ltn_addl // subn1 -(size_delete Hl) addnC -size_cat addnBAC;last exact: leq_nth_count.
      rewrite count_delete -count_cat -cat_head_behead // count_cat size_cat.
      case: p;
        [ exists (Stay Red xir_ok (rnode (Leaf (rcons (delete al i) (access ar 0)) leql ueql) (Leaf (delete ar 0) leqr (ltnW ueqr))))
        | exists (Stay Black (bx_ok Red) (bnode (Leaf (rcons (delete al i) (access ar 0)) leql ueql) (Leaf (delete ar 0) leqr (ltnW ueqr)))) ];
      by rewrite delete_cat Hl /= cat_head_behead.
     rewrite leq_eqVlt bcl (size_delete1 i) Hl /= addn1 in leql,ueql.
     rewrite addnC -addnBA // ltn_addl // subn1 -(size_delete Hl) /= addnC addnBAC;last exact: leq_nth_count.
     rewrite count_delete.
      case: p;
        [ exists (Stay Red xir_ok (rnode (Leaf (delete al i) leql (ltnW ueql)) (Leaf ar leqr ueqr)))
        | exists (Stay Black (bx_ok Red) (bnode (Leaf (delete al i) leql (ltnW ueql)) (Leaf ar leqr ueqr))) ];
     by rewrite delete_cat Hl.
    case Hrl : (i < size al + size ar).
     case bcr : (w ^ 2 %/ 2 == size ar).
      case bcl : (w ^ 2 %/ 2 == size al).
       rewrite -Hrl.
       case (merge_arrays al ar i bcl bcr Hrl).
       rewrite /access nth_cat Hl => res resK.
       case: p;[ by exists (Stay Red xir_ok res) | by exists (Down res)].
      rewrite leq_eqVlt bcl (size_delete1 (size al).-1) prednK //= leqnn addn1 in leql,ueql.
      move/eqP/eqP in bcl. move/eqP in bcr.
      have leqr' : w ^ 2 %/ 2 <= size ((access al (size al).-1) :: (delete ar (i - size al))).
       rewrite /= size_delete //;last rewrite -ltn_subln //. rewrite prednK //.
      have ueqr' : size ((access al (size al).-1) :: (delete ar (i - size al))) < 2 * w ^ 2.
       rewrite /= size_delete //;last rewrite -ltn_subln //. rewrite prednK //.
     rewrite -!addnBA //;last by apply leq_nth_count.
     rewrite count_delete -count_cat /= subn1 [size ar](size_delete1 (i - size al)) -ltn_subln // Hrl -subn1 -addnBA // subnn addn0 -size_cat -cat_last_belast // size_cat count_cat.
      case: p;
        [ exists (Stay Red xir_ok (rnode (Leaf (delete al (size al).-1) leql (ltnW ueql)) (Leaf ((access al (size al).-1) :: (delete ar (i - size al))) leqr' ueqr')))
        | exists (Stay Black (bx_ok Red) (bnode (Leaf (delete al (size al).-1) leql (ltnW ueql)) (Leaf ((access al (size al).-1) :: (delete ar (i - size al))) leqr' ueqr'))) ];
     by rewrite delete_cat Hl /= cat_last_belast.
    rewrite /=.
    rewrite leq_eqVlt bcr (size_delete1 (i - size al)) -ltn_subln // Hrl addn1 /= in leqr,ueqr.
    rewrite -!addnBA //;last exact: leq_nth_count.
    rewrite count_delete subn1 [size ar](size_delete1 (i - size al)).
    rewrite -ltn_subln // Hrl -subn1 -addnBA // subnn addn0.
    case: p;
      [ exists (Stay Red xir_ok (rnode (Leaf al leql ueql) (Leaf (delete ar (i - size al)) leqr (ltnW ueqr))))
      | exists (Stay Black (bx_ok Red) (bnode (Leaf al leql ueql) (Leaf (delete ar (i - size al)) leqr (ltnW ueqr)))) ];
    by rewrite delete_cat Hl.
   rewrite /= nth_default;last rewrite ltn_subln // in Hrl;last by rewrite leqNgt Hrl.
   rewrite !subn0.
   case: p;
     [ exists (Stay Red xir_ok (rnode (Leaf al leql ueql) (Leaf ar leqr ueqr)))
     | exists (Stay Black (bx_ok Red) (bnode (Leaf al leql ueql) (Leaf ar leqr ueqr))) ];
   by rewrite -delete_oversize // size_cat leqNgt Hrl.
  Defined.

  Definition balanceR2 {s1 s2 o1 o2 d cl cr} (p : color)
             (l : tree s1 o1 d cl)
             (dr : near_tree' s2 o2 d cr) :
    color_ok p cl ->
    color_ok p cr ->
  {B' : near_tree' (s1 + s2) (o1 + o2) (inc_black d p) p |
  dflattenn' B' = dflatten l ++ dflattenn' dr}.

    move: p => [].
     move: cl cr l dr => [] [] // l dr ? ?.
     move: l dr; move ceq : (Black) => c' l dr.
     move: dr ceq l => /= [? ? d' c p ok dr|? ? d' dr] ceq l.
      move: ceq c ok l dr => <- [] // ? l dr.
      by exists (Stay Red xir_ok (rnode l dr)).
     move: l dr => {ceq c'} /=; move ceq : (Black) => c'; move deq : (d'.+1) => d'' l dr.
     move: l deq ceq dr => [//| ? ? ? ? ? ? clr c cllok clrok ll lr] deq ceq dr.
     move: ceq deq ll lr dr cllok clrok => <- /= [] <- ll lr dr clrok ?.
     move: clr lr clrok => [] lr ? {c'}.
      move: ll lr dr; move ceq : (Red) => c' ll lr dr.
      move: lr ll dr ceq => [//| ? ? ? ? ? cl' cr' cll okl okr lrl lrr] ll dr ceq.
      move: ceq cl' cr' okl okr ll lrl lrr dr => /= <- [] [] //= ? ? ll lrl lrr dr.
      rewrite !addnA -![_ + _ + _ + _]addnA.
      exists (Stay Red xir_ok (rnode (bnode ll lrl) (bnode lrr dr))).
      by rewrite /= !catA.
     rewrite -!addnA -catA.
     by exists (Stay Red xir_ok (bnode ll (rnode lr dr))).
    move => /= ? ?.
    move: dr l => [? ? d' c ? ? dr|? ? d' dr] l; first by exists (Stay Black (bx_ok Red) (bnode l dr)).
    move: dr l => /=; move deq : (d'.+1) => d'' dr l.
    move: l deq dr => [//| ? oo ? ? ? cll clr c cllok clrok ll lr] /=.
    move: clr clrok lr => [] clrok lr.
     move: c cllok clrok => [] //= ? ? [] -> dr.
     move: lr; move ceq : (Red) => c' lr.
     move: lr ceq dr ll => /= [//|? ? ? ? ? cl' cr' ? okl okr lrl lrr] ceq dr ll.
     move: ceq cl' cr' ll lrl lrr okl okr dr => <- [] [] //= ll lrl lrr ? ? dr.
     rewrite !addnA -![_ + _ + _ + _]addnA.
     exists (Stay Black (bx_ok Red) (bnode (bnode ll lrl) (bnode lrr dr))).
     by rewrite /= -!catA.
    move: c cllok clrok => [] /= cllok clrok.
     move: cll cllok ll => [] // ? ll deq.
     move: lr ll ; move ceq : (Black) => c' lr ll dr.
     move: lr ceq deq ll dr => [//| ? ? ? ? ? cl' cr' crl okl okr lrl lrr] ceq deq ll dr.
     move: ceq deq lrl lrr ll dr okl okr => /= <- [] <- lrl lrr ll dr /= ? ?.
     move: cr' lrr  => [] lrr;last first.
      rewrite -!addnA.
      exists (Stay Black (bx_ok Red) (bnode ll (bnode lrl (rnode lrr dr)))).
      by rewrite /= -!catA.
     move: lrr => /=; move ceq : (Red) => c lrr {c'}.
     move: lrr ceq lrl ll dr => [//| ? ? ? ? ? clrrl clrr c' okl okr lrrl lrrr] ceq lrl ll dr.
     move: ceq clrrl clrr lrrl lrrr lrl ll dr okl okr => <- [] [] // lrrl lrrr lrl ll dr ? ?.
     rewrite -!addnA [X in (_ + X)]addnA [X in (oo + X)]addnA.
     exists (Stay Black (bx_ok Red) (bnode ll (rnode (bnode lrl lrrl) (bnode lrrr dr)))).
     by rewrite /= -!catA.
    move => [] -> dr.
    rewrite -!addnA -!catA.
    by exists (Down (bnode ll (rnode lr dr))).
  Defined.

  Definition balanceL2 {s1 s2 o1 o2 d cl cr} (p : color)
             (dl : near_tree' s1 o1 d cl)
             (r : tree s2 o2 d cr) :
    color_ok p cl ->
    color_ok p cr ->
  {B' : near_tree' (s1 + s2) (o1 + o2) (inc_black d p) p |
  dflattenn' B' = dflattenn' dl ++ dflatten r}.

    move: p => [].
     move: cl cr dl r => [] [] // dl r ? ?.
     move: dl r; move ceq : (Black) => c' dl r.
     move: dl ceq r => /= [? ? d' c p ok dl|? ? d' dl] ceq r.
      move: ceq c ok r dl => <- [] // ? r dl.
      by exists (Stay Red xir_ok (rnode dl r)).
     move: dl r => {ceq c'} /=; move ceq : (Black) => c'; move deq : (d'.+1) => d'' dl r.
     move: r deq ceq dl => [//| ? ? ? ? ? crl ? c crlok crrok rl rr] deq ceq dl.
     move: ceq deq rl rr dl crlok crrok => <- /= [] <- rl rr dl crlok ?.
     move: crl rl crlok => [] rl ? {c'}.
      move: rl rr dl; move ceq : (Red) => c' rl rr dl.
      move: rl rr dl ceq => [//| ? ? ? ? ? cl' cr' crl okl okr rll rlr] rr dl ceq.
      move: ceq cl' cr' okl okr rr rll rlr dl => /= <- [] [] //= ? ? rr rll rlr dl.
      rewrite !addnA -![_ + _ + _ + _]addnA.
      exists (Stay Red xir_ok (rnode (bnode dl rll) (bnode rlr rr))).
      by rewrite /= !catA.
     rewrite !addnA /= !catA. 
     by exists (Stay Red xir_ok (bnode (rnode dl rl) rr)).
    move => /= ? ?.
    move: dl r => [? ? d' c ? ? dl|? ? d' dl] r; first by exists (Stay Black (bx_ok Red) (bnode dl r)).
    move: dl r => /=; move deq : (d'.+1) => d'' dl r.
    move: r deq dl => [//| ? ? ? ? ? crl crr c crlok crrok rl rr] /=.
    move: crl crlok rl => [] crlok rl.
     move: c crlok crrok => [] //= ? ? [] -> dl.
     move: rl; move ceq : (Red) => c' rl.
     move: rl ceq dl rr => /= [//|? ? ? ? ? cl' cr' crl okl okr rll rlr] ceq dl rr.
     move: ceq cl' cr' rr rll rlr okl okr dl => <- [] [] //= rr rll rlr ? ? dl.
     rewrite !addnA -![_ + _ + _ + _]addnA.
     exists (Stay Black (bx_ok Red) (bnode (bnode dl rll) (bnode rlr rr))).
     by rewrite /= -!catA.
    move: c crrok crlok => [] /= crrok crlok.
     move: crr crrok rr => [] // ? rr deq.
     move: rl rr; move ceq : (Black) => c' rl rr dl.
     move: rl ceq deq rr dl => [//| ? ? ? ? ? cl' cr' crl okl okr rll rlr] ceq deq rr dl.
     move: ceq deq rll rlr rr dl okl okr => /= <- [] <- rll rlr rr dl /= ? ?.
     move: cl' rll  => [] rll;last first.
      rewrite !addnA.
      exists (Stay Black (bx_ok Red) (bnode (bnode (rnode dl rll) rlr) rr)).
      by rewrite /= -!catA.
     move: rll; move ceq : (Red) => c rll {c'}.
     move: rll ceq rlr rr dl=> [//| ? ? ? o3 ? crll crlr c' okl okr rlll rllr] ceq rlr rr dl.
     move: ceq crll crlr rlll rllr rlr rr dl okl okr => <- [] [] // rlll rllr rlr rr dl ? ?.
     rewrite -!addnA ![_ + ( _ + (_ + (_ + _)))]addnA [X in _ + _ + X]addnA [o3 + (_ + _)]addnA.
     exists (Stay Black (bx_ok Red) (bnode (bnode dl rlll) (rnode (bnode rllr rlr) rr))).
     by rewrite /= -!catA.
    move => [] -> dl.
    rewrite !addnA !catA.
    by exists (Down (bnode (rnode dl rl) rr)).
  Defined.

  Lemma access_cat s t i : access (s ++ t) i = (if i < size s then access s i else access t (i - size s)).
  Proof. by rewrite /access nth_cat. Qed.

  Lemma ltn_trans1 (l m n : nat) : l < m -> m < n.+1 -> l < n.
  Proof.
    move => H1; case: leqP => // H2 ?.
    exact (leq_trans H1 H2).
  Qed.

  Lemma wf_nat' : forall n : nat, (forall m : nat, m < n -> Acc lt m).
  Proof.
    elim => [?|? IH ? H1]; first by rewrite ltn0.
    apply Acc_intro => ?; move/leP => H2.
    exact (IH _ (ltn_trans1 _ _ _ H2 H1)).
  Qed.

  Lemma wf_nat : well_founded lt.
  Proof.
    case => [|?]. apply Acc_intro => ?. move/leP. by rewrite ltn0.
    apply Acc_intro => m. move/leP. move: m. apply wf_nat'.
  Qed.

  Fixpoint size_of_tree' {s o d c} (tr : tree s o d c) :=
    match tr with
    | Leaf _ _ _ => 1
    | Node _ _ _ _ _ _ _ _ _ _ l r => (size_of_tree' l) + (size_of_tree' r) + 1
    end.

  Definition ltc (c c' : color) :=
    match c,c' with
    | Red,Black => true
    | _,_ => false
    end.

  Lemma ltc_trans c c' c'' : ltc c c' -> ltc c' c'' -> ltc c c''.
  Proof. case c,c',c'' => //. Qed.

  Lemma wf_color : well_founded ltc.
  Proof. case; apply Acc_intro => [] [] /=; [done | done | move => ?;apply Acc_intro => [] [] /= // | done]. Qed.

  Lemma wf_nc : forall dc, Acc (fun dc dc' =>
                                  match dc,dc' with
                                  | (d,c),(d',c') => 
                                    if d == d'
                                    then ltc c c'
                                    else d < d'
                                  end) dc.
  Proof.
    case => d; refine (Fix wf_nat (fun (d : nat) => _) _ d) => d' IH1 c; refine (Fix wf_color (fun (c : color) => _) _ c) => c' IH2;
    apply Acc_intro; case => d'' c''; (case: ifP; [ move/eqP -> => H1 | move => nH1 H1 ]);
    apply Acc_intro; case => d''' c'''; (case: ifP; [move/eqP -> => H2 | move => nH2 H2 ]);
    [ apply (IH2 _ (ltc_trans _ _ _ H2 H1))
    | move/ltP in H2; apply (IH1 _ H2 c''')
    | move/ltP in H1; apply (IH1 _ H1 c''')
    | move/ltP: (ltn_trans H2 H1) => H; apply (IH1 _ H c''') ].
  Qed.

  Lemma cic_ok {c} : color_ok c (inv c).
  Proof. by destruct c. Qed.

  Lemma ltcnS {d c c'} : (if d == d.+1 then ltc c c' else d < d.+1).
  Proof. case: ifP => //; move/eqP; elim d => // n IH; move/eqP; rewrite eqSS; move/eqP => //. Qed.

  Lemma ltcnBR {d} : (if d == d then ltc Red Black else d < d).
  Proof. rewrite eq_refl //. Qed.

  Definition ddelete (d: nat) (c: color) (num ones : nat) (i : nat) (B : tree num ones (inc_black d c) c) :
      { B' : near_tree' (num - (i < num)) (ones - (daccess B i)) (inc_black d c) c | dflattenn' B' = delete (dflatten B) i }.

    move: num ones i B ; refine (Fix_F_2 (fun (d: nat) (c: color) => _) _ (wf_nc (d,c))) => {d c} d c ddelete num ones i B.
    case val : (i < num);last first.
     move/negP/negP : val; rewrite ltnNge; move/negPn => val; rewrite daccess_default // !subn0 -delete_oversize; last by rewrite dflatten_sizeK.
     by exists (Stay c cic_ok B).
    destruct c.
     move: B; remember_eq Red c ceq; remember_eq d d' deq; rewrite /= -ceq -deq => B;
     destruct B as [|? ? ? ? d' cl cr c ? ? l r]; [ done | subst c; destruct cr; [done|]; destruct cl; [done|] ]; move: (sizeW' l) (sizeW' r) => ? ? /=; subst d.
     case: ifP => H.
      move: l r; remember_eq d' d deq; rewrite -deq => l r;
      destruct l as [arrl leql ueql| ? ? ? ? d'' ? ? cl' okll oklr ll lr]; last move: (sizeW' ll) (sizeW' lr) => ? ? /=; subst d'.
       case (delete_leaves2 Red (Leaf arrl leql ueql) r i); rewrite ltn_addr // access_cat daccessK /= H => res resK.
       exists res; by rewrite -resK.
      destruct cl' => //; move: ddelete => /= ddelete.
      case (ddelete d'' Black ltcnS _ _ i (bnode ll lr)); rewrite H; set b := (daccess _ _) => dl dK.
      rewrite ![_ + _ + _ - _]addnBAC //; last case: ifP => ?; try rewrite leq_addln // leq_access_count //; last rewrite leq_addrn // leq_access_count // -ltn_subln //.
      case (balanceL2 Red dl r erefl erefl) => res resK; exists res; by rewrite delete_cat resK size_cat !dflatten_sizeK H dK.
     destruct l as [arrl leql ueql| s1 ? s0 ? ? ? ? cl' okll oklr ll lr].
      case (delete_leaves2 Red (Leaf arrl leql ueql) r i); rewrite val access_cat daccessK /= H => res resK.
      exists res; by rewrite -resK.
     destruct cl' => //.
     case (ddelete d Black ltcnS _ _ (i - (s1 + s0)) r);
     rewrite -ltn_subln // val; set b := (daccess _ _) => dr dK.
     rewrite -!addnBA //; last rewrite leq_access_count // -ltn_subln //.
     case (balanceR2 Red (Node okll oklr ll lr) dr erefl erefl) => res resK; exists res; by rewrite delete_cat resK dflatten_sizeK H dK.

    move: B => /=; move deq : (d.+1) => d'; move ceq : (Black) => c' B;
    move: B val deq ceq => [//|s1 o1 s2 o2 d'' cl cr c cclok ccrok l r] val deq ceq; move: (sizeW' l) (sizeW' r) => slp srp /=;
    move: ceq deq l r cclok ccrok => <- /= [] <- l r {d'} cclok ccrok.
    case: ifP => H.
     move: r l ddelete ccrok cclok => [arrr leqr ueqr | ? ? ? ? d''' crl crr cr' crlok crrok rl rr] l ddelete ccrok cclok.
     move: cl l => [] l; last first.
      case (delete_leaves2 Black l (Leaf arrr leqr ueqr) i).
      rewrite daccessK //; rewrite /= access_cat dflatten_sizeK ltn_addr // H => res resK.
      exists res; by rewrite -resK.
     move: l cclok ccrok => {c'}; move ceq : (Red) => c' /=; move deq : (0) => z l cclok ccrok; move: l ceq deq H slp => [// | ? ? ? ? d''' cll clr c'' cllok clrok ll lr ] ceq deq H slp.
     move: ceq deq cll clr cllok clrok ll lr => <- /= <- [] [] // ? ? ll lr; move: (sizeW' ll) (sizeW' lr) => ? ?.
     case (delete_leaves2 Red ll lr i); rewrite H access_cat // !daccessK !dflatten_sizeK; set b := (if _ then _ else _) => dl dK.
     rewrite ![_ + _ + _ - _]addnBAC //;last first.
     subst b; case: ifP =>?; [ rewrite leq_addln // | rewrite leq_addrn // ]; rewrite -!daccessK leq_access_count //; rewrite ltn_subln // in H.
     move: lr ll b dl dK => {d'' z}; remember_eq 0 z deq'; rewrite /= -deq' => lr ll b dl dK.
     destruct dl as [? ? d'' ? ? ? dl|] => //;subst d''.
     exists (Stay Black (bx_ok Red) (bnode dl (Leaf arrr leqr ueqr))).
     by rewrite /= delete_cat size_cat !dflatten_sizeK H -dK.
     destruct cr';last first.
      destruct cl; [ case (ddelete _ Red ltcnBR _ _ i l) | case (ddelete _ Black ltcnS _ _ i l) ]; rewrite H => dl dK;
      case (balanceL2 Black dl (Node crlok crrok rl rr) erefl erefl) => res resK;
      rewrite delete_cat dflatten_sizeK H -dK -resK !addnBAC //; [| rewrite leq_access_count // | | rewrite leq_access_count //];
      by exists res.
     destruct crl,crr => //.
     destruct cl.
      case (ddelete _ _ ltcnBR _ _ i l).
      move: l => {c'}; remember_eq Red c' ceq; rewrite /= -ceq H => l dl; subst c'.
      case (balanceL2 Black dl (rnode rl rr) erefl erefl).
      rewrite -!addnBAC //; last rewrite leq_access_count //.
      move => res resK dK.
      exists res.
      by rewrite resK dK delete_cat dflatten_sizeK H.
     case (ddelete _ Red ltcnBR _ _ i (rnode l rl)).
     rewrite ltn_addr // /= H => dl dK.
     rewrite !addnA ![_ + _ + _ - _]addnBAC; last rewrite ltn_addr //; last rewrite leq_addln // leq_access_count //.
     case (balanceL2 Black dl rr erefl erefl) => /= res resK.
     exists res.
     by rewrite resK dK !delete_cat !dflatten_sizeK H -!catA.

    move: l r ddelete ccrok cclok H val => [arrl leql ueql | s3 ? s4 ? d''' cll clr cl' cllok clrok ll lr] r ddelete ccrok cclok H.
    move: cr r => [] r val;last first.
     case (delete_leaves2 Black (Leaf arrl leql ueql) r i).
     rewrite /= access_cat H !daccessK val // => res resK.
     exists res; by rewrite -resK.
    move: r cclok ccrok => {c'}; move ceq : (Red) => c' /=; move deq : (0) => z r cclok ccrok; move: r val ceq deq H slp => [// | ? ? ? ? d''' crl crr c'' crlok crrok rl rr ] val ceq deq H slp.
    move: ceq deq crl crr rl rr crlok crrok => <- /= <- [] [] // rl rr ? ?; move: (sizeW' rl) (sizeW' rr) => ? ?.
    case (delete_leaves2 Red rl rr (i - (size arrl))).
    rewrite -ltn_subln;last rewrite ltn_addr //. rewrite val access_cat !daccessK !dflatten_sizeK; set b := (if _ then _ else _) => /= dr dK.
    rewrite -![(_ + (_ + _) - _)]addnBA;last rewrite ltn_addr //; last first.
    subst b; case: ifP => ?; [ rewrite leq_addln // | rewrite leq_addrn //]; rewrite -daccessK leq_access_count // -!ltn_subln // ltn_addr //.
    move: rl rr b dr dK => {d'' z}; remember_eq 0 z deq'; rewrite /= -deq' => rl rr b dr dK.
    destruct dr as [? ? d'' ? ? ? dr|] => //;subst d''.
    exists (Stay Black (bx_ok Red) (bnode (Leaf arrl leql ueql) dr)).
    by rewrite /= delete_cat H -dK.
    move => val.
    destruct cl';last first.
     destruct cr; [ case (ddelete _ Red ltcnBR _ _ (i - (s3 + s4)) r) | case (ddelete _ Black ltcnS _ _ (i - (s3 + s4)) r) ]; rewrite -ltn_subln // val => dr dK;
     case (balanceR2 Black (Node cllok clrok ll lr) dr erefl erefl) => res resK;
     rewrite -![(_ + _ + _ - _)]addnBA //; try apply leq_access_count; try rewrite -ltn_subln //;
     exists res; by rewrite resK dK /= delete_cat size_cat !dflatten_sizeK H.
    destruct cll,clr => //.
    destruct cr.
     case (ddelete _ _ ltcnBR _ _ (i - (s3 + s4)) r).
     move: r => {c'}; remember_eq Red c' ceq; rewrite /= -ceq -ltn_subln // val => r dr; subst c'.
     case (balanceR2 Black (rnode ll lr) dr erefl erefl).
     rewrite !addnBA //; last rewrite leq_access_count // -ltn_subln // val.
     move => res resK dK.
     exists res.
     by rewrite resK dK delete_cat size_cat !dflatten_sizeK H.
    move: (sizeW' lr) => ?;
    case (ddelete _ Red ltcnBR _ _ (i - s3) (rnode lr r)).
    rewrite /= -!ltn_subln //=; last by rewrite ltn_addl.
    rewrite H addnA val => dr dK.
    case (balanceR2 Black ll dr erefl erefl); rewrite -!addnA => res resK.
    rewrite subnDA -![(_ + (_ + _) - _)]addnBA.
    exists res.
    rewrite resK dK !delete_cat !size_cat !dflatten_sizeK -ltn_subln // H -!catA subnDA //.
    rewrite leq_addrn // leq_access_count //.
    rewrite -subnDA -ltn_subln //.
    rewrite ltn_addr //.
 Defined.
End delete.

Require Import Compare_dec.

End dynamic_dependent.
Extract Inductive tree => tree_ml [ "LeafML" "(function (s1,o1,s2,o2,d,c,cl,cr,l,r) -> NodeML (s1, o1, s2, o2, c, l, r))" ]
"(fun fl fn ->
  function
  | LeafML arr -> fl arr
  | NodeML (s1,o1,s2,o2,c,(NodeML (_,_,_,_,cl,_,_) as l),(NodeML (_,_,_,_,cr,_,_) as r)) -> fn s1 o1 s2 o2 1 cl cr c l r
  | NodeML (s1,o1,s2,o2,c,(LeafML _ as l),(NodeML (_,_,_,_,cr,_,_) as r)) -> fn s1 o1 s2 o2 1 Black cr c l r
  | NodeML (s1,o1,s2,o2,c,(LeafML _ as l),(LeafML _ as r)) -> fn s1 o1 s2 o2 1 Black Black c l r
  | NodeML (s1,o1,s2,o2,c,(NodeML (_,_,_,_,cl,_,_) as l),(LeafML _ as r)) -> fn s1 o1 s2 o2 1 cl Black c l r)".
Extraction TestCompile dinsert ddelete tree_ml.
Extraction "dydep.ml" dinsert ddelete tree_ml.
