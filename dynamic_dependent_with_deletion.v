From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq.
From mathcomp Require Import choice fintype prime tuple finfun finset bigop.

Require Import compact_data_structures rank_select insert_delete Program JMeq set_clear.

Set Implicit Arguments.

Tactic Notation "remember_eq" constr(expr) ident(vname) ident(eqname) := case (exist (fun x => x = expr) expr erefl) => vname eqname.

Variable w : nat.
Axiom wordsize_gt1: w > 1.

Lemma wordsize_gt0 : w > 0.
Proof. apply ltnW. exact wordsize_gt1. Qed.

Lemma wordsize_neq0: w != 0.
Proof. rewrite -lt0n. exact wordsize_gt0. Qed.

Lemma wordsize_sqrn_gt2 : w ^ 2 > 2.
Proof.
  case_eq w => n. move: wordsize_neq0. by rewrite n.
  case_eq n => n' H. move/eqP: (ltn_eqF wordsize_gt1). by rewrite H.
  move => H'.
  rewrite -[n'.+2]addn2 sqrnD -!mulnn !muln2 -!addnn add2n addnC !addnA.
  apply/eqP.
  rewrite addnC subnDA.
  by compute.
Qed.

Lemma wordsize_sqrn_gt0 : w ^ 2 > 0.
Proof. exact: (ltnW (ltnW wordsize_sqrn_gt2)). Qed.

Lemma wordsize_sqrn_div2_neq0 : (w ^ 2 %/ 2 <> 0).
Proof.
  case_eq w => n. move: wordsize_neq0. by rewrite n.
  move => H1 H2.
  move: (divn_eq (n.+1 ^ 2) 2).
  rewrite H2 mul0n add0n.
  case_eq n => [H3|n']. rewrite H3 in H1. move/eqP: (ltn_eqF wordsize_gt1). by rewrite H1.
  move => H3 H4.
  rewrite -H3 -H1 in H4.
  have H5 : (0 < 2) => //.
  rewrite -(ltn_mod (w ^ 2) 2) -H4 in H5.
  move: wordsize_sqrn_gt2.
  rewrite ltnNge.
  move: (ltnW H5) => H6.
  by rewrite H6 /=.
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

  (* Axiom technical2 : forall(d : param nat), (inc_black d Black) <> Param 0. *)
  (* Axiom technical3 : forall(d0 d : param nat), inc_black d0 Black = inc_black d Black -> d0 = d. *)

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
Require Import Compare_dec.

Section set_clear.
  Obligation Tactic := idtac.
  
  Program Fixpoint bset {num ones d c} (B : tree num ones d c) i
    {measure (size_of_tree B)} :
    { B'b : (tree num (ones + (~~ (daccess B i)) && (i < num)) d c * bool)
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
      by rewrite /count_one /access (count_bit_set' false Hi) andbT.
    by rewrite andbF addn0 bit_set_over //= leqNgt Hi.
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

  Definition wordsize_ok {num ones d c} (B : tree num ones d c) : bool := 
    match B with
    | Leaf s _ _ => ((w ^ 2) %/ 2 < (size s)) && (2 * (w ^ 2) >= (size s))
    | Node s1 o1 s2 o2 _ _ _ _ okl okr l r => true
    end.

  Definition is_node {num ones d c} (B : tree num ones d c) : bool := 
    match B with
    | Leaf s _ _ => false
    | Node s1 o1 s2 o2 _ _ _ _ okl okr l r => true
    end.

  Definition is_leaf {num ones d c} (B : tree num ones d c) : bool := 
    match B with
    | Leaf s _ _ => true
    | Node s1 o1 s2 o2 _ _ _ _ okl okr l r => false
    end.

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

  Lemma technical1 : forall(n : nat),n * 2 <= n -> n == 0.
  Proof.
    move => n.
    move/eqP.
    rewrite muln2 -addnn -addnBA // subnn addn0.
    by move/eqP.
  Qed.

  Lemma size_of_node {n m d c} (tr : tree n m d c) : is_node tr -> n >= w ^ 2 %/ 2 * 2.
  Proof.
    dependent induction tr => // H.
    case_eq (is_node tr1) => H1.
     move: (IHtr1 H1) (leq0n s2) => leq1 leq2.
     move: (leq_add leq1 leq2).
     by rewrite addn0.
    destruct tr1 => //.
    case_eq (is_node tr2) => H2.
     move: (IHtr2 H2) (leq0n (size arr)) => leq1 leq2.
     move: (leq_add leq1 leq2).
     by rewrite addn0 addnC.
    clear H H1.
    destruct tr2 => //;last first. by rewrite /= in H2.
    clear IHtr1 IHtr2 H2.
    rewrite addnC.
    rewrite -(leq_add2r (size arr)) in i3.
    rewrite -(leq_add2l (w ^ 2 %/ 2)) addnn -muln2 in i1.
    exact: (leq_trans i1 i3).
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

    (* proof_irrevance. *)

  Lemma addsubnC : forall(a b c : nat),a >= c -> a + b - c = a - c + b.
  Proof.
    move => a b c.
    move: b a.
    elim: c => [|c IH b]. intros. by rewrite !subn0.
    move => a H.
    rewrite !subnS (IH b a (ltnW H)) -!subn1.
    elim: b => [|b IH2]. by rewrite !addn0.
    rewrite -addnBA // -addn1 -addnBA // subnn addn0 addnA -IH2.
    rewrite subn1 addn1 prednK // -(IH b a (ltnW H)).
    clear IH2.
    case: b => [|b]. by rewrite addn0 subn_gt0.
    apply/eqP.
    rewrite -[b.+1]addn1 addnA addn1 [(a + b).+1 - c]subSn.
     rewrite -addn1 subSS //.
    have H2 : a <= a + b. exact: leq_addr.
    exact: (leq_trans (ltnW H) H2).
  Qed.

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

  Lemma leq_addln : forall(a b c: nat), a <= b -> a <= b + c.
  Proof.
    move => a b c leq1.
    move: (leq0n c) => leq2.
    rewrite -(leq_add2l b) addn0 in leq2.
    exact: (leq_trans leq1 leq2).
  Qed.

  Lemma leq_addrn : forall(a b c: nat), a <= c -> a <= b + c.
  Proof. move => a b c. rewrite addnC. exact: (leq_addln a c b). Qed.

  Lemma ltn_addrn : forall(a b c: nat), a < c -> a < b + c.
  Proof.
    move => a b c ltn1.
    move: (leq0n b) => leq2.
    rewrite -(leq_add2r c) add0n in leq2.
    rewrite leq_eqVlt in leq2.
    case/orP: leq2 => [|ltn2]. move/eqP => H. by rewrite -H.
    exact: (ltn_trans ltn1 ltn2).
  Qed.

  Lemma ltn_addln : forall(a b c: nat), a < b -> a < b + c.
  Proof. move => a b c. rewrite addnC. exact: (ltn_addrn a c b). Qed.

  Lemma ltn_subln a b c : c > 0 -> a < b + c = (a - b < c).
  Proof.
    case H1 : (b <= a) => H2. by rewrite -[RHS](ltn_add2r b) subnK // addnC.
    move: H1; rewrite leqNgt; move/negP/negP => H1.
    rewrite ltn_addln //. move: H1.
    case: b => // n H1.
    move/eqP: (ltnW H1) => W.
    by rewrite W H2.
  Qed.

  Lemma ltn_subrn a b c : b > 0 -> a < b + c = (a - c < b).
  Proof. rewrite addnC. exact: (ltn_subln a c b). Qed.

  Lemma delete0_behead (arr : seq bool) : delete arr 0 = behead arr.
  Proof. case arr => /= // b l. by rewrite /delete take0 drop1 cat0s /=. Qed.

  Lemma sizeW' {s o d c} (tr : tree s o d c) : s > 0.
  Proof.
    move: (size_of_node tr).
    rewrite /= muln2 -addnn => H.
    destruct tr. exact: sizeW => //.
    move/implyP : H => /= H.
    move/eqP: wordsize_sqrn_div2_neq0.
    rewrite -lt0n => ltn1.
    move: (ltn_addrn 0 (w ^ 2 %/ 2) _ ltn1) => ltn2.
    rewrite leq_eqVlt in H.
    case/orP: H. move/eqP => H. by rewrite -H.
    move => H.
    exact: (ltn_trans ltn2 H).
  Qed.

  Inductive near_tree' : nat -> nat -> nat -> color -> Type := 
  | Stay : forall {s o d},
      near_tree s o d.+1 Black -> near_tree' s o d Black
  | Down : forall {s o d},
      near_tree s o d Black -> near_tree' s o d Black.

  Definition dflattenn' {s o d c} (tr : near_tree' s o d c) :=
    match tr with
    | Stay _ _ _ t => dflattenn t
    | Down _ _ _ t =>  dflattenn t
   end.

  Definition dflatten' {n m d c} (tr : tree n m d c) :=
    match tr with
    | Leaf s _ _ => s
    | Node _ _ _ _ _ _ _ _ _ _ l r => dflatten l ++ dflatten r
    end.

  Lemma dflatten_is_dflatten' {n m d c} (tr : tree n m d c) : dflatten tr = dflatten' tr.
  Proof. by destruct tr. Qed.

  Lemma rnode_is_not_leaf {s o d} (tr : tree s o d Red) : ~~ is_leaf tr.
  Proof. dependent destruction tr => //. Qed.

  Lemma bnode_is_color_ok {s o d c} (tr : near_tree s o d Black) : color_ok c (fix_color tr).
  Proof. destruct c => //. dependent destruction tr => //. Qed.

  Lemma dflatten_rb {s1 o1 s2 o2 d} (B1 : tree s1 o1 d Black) (B2 : tree s2 o2 d Black) : dflatten (bnode B1 B2)~= dflatten (rnode B1 B2).
  Proof. by rewrite /=. Qed.

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

  Definition black_of_red {s o d} (B : tree s o d Red) : { B' : tree s o (inc_black d Black) Black | dflatten B' = dflatten B }.

    remember_eq Red c' wc.
    move: B. rewrite -wc => B.
    destruct B as [|? ? ? ? ? cl cr c ? ? l r] => //.
    subst c. destruct cl,cr => //.
    by exists (bnode l r).
  Defined.

  Lemma pos_tree_is_not_leaf {num ones d c} (B : tree num ones d.+1 c) : ~~ is_leaf B.
  Proof. dependent inversion B  => //. Qed.

  Lemma node_is_not_leaf  {num ones d c} (B : tree num ones d c) : is_node B -> ~~ is_leaf B.
  Proof. destruct B => //. Qed.

  Lemma bzero_tree_is_leaf {num ones} (B : tree num ones 0 Black) : ~~ is_node B.
  Proof.
    remember_eq 0 d' wd.
    remember_eq Black c' wc.
    move: B. rewrite -wd -wc => B.
    destruct B as [|? ? ? ? ? ? ? c] => //.
    subst c => //.
  Qed.

  Lemma ltn_pred n : n > 0 -> n.-1 < n.
  Proof. case n => //. Qed.

  Definition makeBadL {s1 s2 o1 o2 d} (l : tree s1 o1 d Red) (r : tree s2 o2 d Black) : { tr : near_tree (s1 + s2) (o1 + o2) d Red | dflattenn tr = dflatten l ++ dflatten r }.

    remember_eq Red c' wc.
    move: l. rewrite -wc => l.
    destruct l as [|? ? ? ? ? cl cr c ? ? ll lr ] => //.
    subst c. destruct cl,cr => //.
    exists (Bad ll lr r).
    by rewrite /= catA.
  Defined.

  Definition makeBadR {s1 s2 o1 o2 d} (l : tree s1 o1 d Black) (r : tree s2 o2 d Red) : { tr : near_tree (s1 + s2) (o1 + o2) d Red | dflattenn tr = dflatten l ++ dflatten r }.

    remember_eq Red c' wc.
    move: r. rewrite -wc => r.
    destruct r as [|? ? ? ? ? cl cr c ? ? rl rr] => //.
    subst c. destruct cl,cr => //.
    rewrite !addnA.
    exists (Bad l rl rr).
    by rewrite /= catA.
  Qed.

  Definition merge_arrays (a b : seq bool) (i : nat) (w1 : w ^ 2 %/ 2 == size a) (w2 : w ^ 2 %/ 2 == size b) (val : i < size a + size b) :
             {tr : tree (size a + size b - (i < size a + size b)) (count_one a + count_one b - (access (a ++ b) i)) 0 Black | dflatten tr = delete (a ++ b) i}.

    move/eqP : wordsize_sqrn_div2_neq0; rewrite -lt0n => pos.
    move/eqP: w1 => w1. move/eqP: w2 => w2. move: (pos); rewrite w1 => w1p. move: (pos); rewrite w2 => w2p.
    case Hl : (i < size a).
     have ueq : size ((rcons (delete a i) (access b 0)) ++ (delete b 0)) < 2 * w ^ 2.
      rewrite size_cat size_rcons !size_delete // prednK // -subn1 addnBA // subn1 -w1 -w2 ltnW // prednK //;last rewrite ltn_addrn //.
      rewrite leq_divn2n_mul2 // wordsize_sqrn_gt0 //.
     have leq : size (rcons (delete a i) (access b 0) ++ delete b 0) >= w ^ 2 %/ 2.
      rewrite size_cat size_rcons !size_delete // prednK // w1 leq_addln //.
     rewrite ltn_addln // addnC -addnBA // subn1 -(size_delete Hl) /= addnC -size_cat delete_cat addsubnC /access nth_cat Hl; last rewrite leq_nth_count //.
     rewrite count_delete -count_cat -cat_head_behead //.
     by exists (Leaf ((rcons (delete a i) (access b 0)) ++ (delete b 0)) leq ueq).
    move: val; rewrite ltn_subln // => Hr.
    have ueq : size (a ++ (delete b (i - (size a)))) < 2 * w ^ 2.
     rewrite size_cat size_delete // -w1 -w2 -subn1 addnBA // subn1 ltnW // prednK //;last rewrite ltn_addrn //.
     rewrite leq_divn2n_mul2 // wordsize_sqrn_gt0 //.
    have leq : size (a ++ (delete b (i - (size a)))) >= w ^ 2 %/ 2.
    rewrite size_cat size_delete //;last rewrite -{1}w1 w2 //.
      by rewrite leq_addln // w1.
      rewrite Hr -addnBA // subn1 -(size_delete Hr) -size_cat -addnBA /access nth_cat Hl ;last rewrite leq_nth_count //.
      rewrite count_delete -count_cat.
    exists (Leaf (a ++ (delete b (i - (size a)))) leq ueq).
    by rewrite /= delete_cat Hl.
  Qed.

  (* Definition delete_leaf {s o} (t : tree s o 0 Black) (i : nat) (wt : w ^ 2 %/ 2 < s) : *)
  (*   {t' : tree (s - (i < s)) (o - access (dflatten t) i) 0 Black | dflatten t' = delete (dflatten t) i}. *)

  (*   remember_eq 0 d' deq. remember_eq Black c' ceq. *)
  (*   move: t; rewrite -ceq -deq => t; destruct t as [a l u|]; last rewrite ceq /= // in deq. *)
  (*   rewrite /= (@size_delete1 a i). *)
  (*   move: a l u wt. *)
  (*   About size_delete1. *)
  (*   exists (Leaf (delete a i) _ _). *)

  Definition delete_leaves2 {s1 o1 s2 o2} (l : tree s1 o1 0 Black) (r : tree s2 o2 0 Black) (i : nat) :
    {B' : near_tree (s1 + s2 - (i < s1 + s2))
                    (o1 + o2 - access (dflatten l ++ dflatten r) i) 0 Black | dflattenn B' = delete (dflatten l ++ dflatten r) i}.

    move/eqP : wordsize_sqrn_div2_neq0 (sizeW' l) (sizeW' r); rewrite -lt0n => pos posl posr.
    remember_eq 0 d' deq; remember_eq Black c' ceq; move: l r; rewrite -ceq -deq => l; destruct l as [al leql ueql|]; last rewrite ceq /= // in deq.
    move => {deq ceq}; remember_eq 0 d' deq; remember_eq Black c' ceq; rewrite /= -ceq -deq => r; destruct r as [ar leqr ueqr|]; last rewrite ceq /= // in deq.

    rewrite /access nth_cat.
    case: ifP => Hl.
     case bcl : (w ^ 2 %/ 2 == size al).
      case bcr : (w ^ 2 %/ 2 == size ar).
       case (merge_arrays al ar i bcl bcr (ltn_addln _ _ _ Hl)).
       rewrite /access nth_cat Hl => res resK.
       by exists (Good Black res).
      rewrite /=.
      rewrite leq_eqVlt bcr (size_delete1 0) posr /= addn1 in leqr,ueqr.
      rewrite -(size_rcons_delete i (access ar 0)) // in leql,ueql.
      rewrite addnC -addnBA // ltn_addrn // subn1 -(size_delete Hl) addnC -size_cat addsubnC;last exact: leq_nth_count.
      rewrite count_delete -count_cat -cat_head_behead // count_cat size_cat.
      exists (Good Black (rnode (Leaf (rcons (delete al i) (access ar 0)) leql ueql) (Leaf (delete ar 0) leqr (ltnW ueqr)))).
      by rewrite delete_cat Hl /= cat_head_behead.
     rewrite leq_eqVlt bcl (size_delete1 i) Hl /= addn1 in leql,ueql.
     rewrite addnC -addnBA // ltn_addrn // subn1 -(size_delete Hl) /= addnC addsubnC;last exact: leq_nth_count.
     rewrite count_delete.
     exists (Good Black (rnode (Leaf (delete al i) leql (ltnW ueql)) (Leaf ar leqr ueqr))).
     by rewrite delete_cat Hl.
    case Hrl : (i < size al + size ar).
     case bcr : (w ^ 2 %/ 2 == size ar).
      case bcl : (w ^ 2 %/ 2 == size al).
       rewrite -Hrl.
       case (merge_arrays al ar i bcl bcr Hrl).
       rewrite /access nth_cat Hl => res resK.
       by exists (Good Black res).
      rewrite leq_eqVlt bcl (size_delete1 (size al).-1) ltn_pred // addn1 /= in leql,ueql.
      move/eqP/eqP in bcl. move/eqP in bcr.
      have leqr' : w ^ 2 %/ 2 <= size ((access al (size al).-1) :: (delete ar (i - size al))).
       rewrite /= size_delete //;last rewrite -ltn_subln //. rewrite prednK //.
      have ueqr' : size ((access al (size al).-1) :: (delete ar (i - size al))) < 2 * w ^ 2.
       rewrite /= size_delete //;last rewrite -ltn_subln //. rewrite prednK //.
     rewrite -!addnBA //;last by apply leq_nth_count.
     rewrite count_delete -count_cat /= subn1 [size ar](size_delete1 (i - size al)) -ltn_subln // Hrl -subn1 -addnBA // subnn addn0 -size_cat -cat_last_belast // size_cat count_cat.
     exists (Good Black (rnode (Leaf (delete al (size al).-1) leql (ltnW ueql)) (Leaf ((access al (size al).-1) :: (delete ar (i - size al))) leqr' ueqr'))).
     by rewrite delete_cat Hl /= cat_last_belast.
    rewrite /=.
    rewrite leq_eqVlt bcr (size_delete1 (i - size al)) -ltn_subln // Hrl addn1 /= in leqr,ueqr. 
    rewrite -!addnBA //;last exact: leq_nth_count.
    rewrite count_delete subn1 [size ar](size_delete1 (i - size al)).
    rewrite -ltn_subln // Hrl -subn1 -addnBA // subnn addn0.
    exists (Good Black (rnode (Leaf al leql ueql) (Leaf (delete ar (i - size al)) leqr (ltnW ueqr)))).
    by rewrite delete_cat Hl.
   rewrite /= nth_default;last rewrite ltn_subln // in Hrl;last by rewrite leqNgt Hrl.
   rewrite !subn0.
   exists (Good Black (rnode (Leaf al leql ueql) (Leaf ar leqr ueqr))).
   by rewrite -delete_oversize // size_cat leqNgt Hrl.
  Defined.

  Obligation Tactic := idtac.

  Program Definition delete_leaves3 {s1 o1 s2 o2 s3 o3} (t1 : tree s1 o1 0 Black) (t2 : tree s2 o2 0 Black) (t3 : tree s3 o3 0 Black) (i : nat) :
    {B' : near_tree (s1 + s2 + s3 - (i < s1 + s2 + s3)) (o1 + o2 + o3 - access (dflatten t1 ++ dflatten t2 ++ dflatten t3) i) 1 Black | dflattenn B' = delete (dflatten t1 ++ dflatten t2 ++ dflatten t3) i} :=

    match (i < s1), (i - s1 - s2 < s3) with 
    | true,true => 
      (balanceL Black (delete_leaves2 t1 t2 i) t3 erefl erefl)
    | false,true =>
      (balanceR Black t1 (delete_leaves2 t2 t3 (i - s1)) erefl erefl)
    | false,false => (Good Black (bnode t1 (rnode t2 t3)))
    | true,false => False_rec _ _
    end.

  Next Obligation. move => s1 s2 s3 o1 o2 o3 t1 t2 t3 i H1' H2' H1 H2; subst H1' H2'; move : (sizeW' t1) (sizeW' t2) (sizeW' t3) => ? ? ?. rewrite !ltn_addln // -addsubnC // ltn_addln //. Qed.
  Next Obligation.
    move => s1 o1 s2 o2 s3 o3 t1 t2 t3 i H1' H2' H1 H2; subst H1' H2'; move : (sizeW' t1) (sizeW' t2) (sizeW' t3) => ? ? ?.
    rewrite /access !nth_cat !dflatten_sizeK -!H1 -addsubnC // leq_addln //.
    remember_eq Black c' ceq; remember_eq 0 d' deq; move: t1; rewrite -ceq -deq => t1. destruct t1 as [a1 l1 u1|]; last by rewrite ceq /= in deq.
     by rewrite leq_nth_count.
  Qed.
  Next Obligation.
    move => s1 o1 s2 o2 s3 o3 t1 t2 t3 i H1' H2' H1 H2; subst H1' H2'; move : (sizeW' t1) (sizeW' t2) (sizeW' t3) => ? ? ?.
    rewrite /eq_rect; destruct delete_leaves3_obligation_2,delete_leaves3_obligation_1.
    set balL := (balanceL _ _ _ _ _).
    set d2 := (delete_leaves2 _ _ _).
    by rewrite (proj2_sig balL) (proj2_sig d2) !delete_cat !dflatten_sizeK -!H1 -catA.
  Qed.
  Next Obligation.
    move => s1 o1 s2 o2 s3 o3 t1 t2 t3 i H1' H2' H1 H2; subst H1' H2'; move : (sizeW' t1) (sizeW' t2) (sizeW' t3) => ? ? ?.
    by rewrite !ltn_subln // subnDA -!H2 -!addnBA // addnA.
  Qed.
  Next Obligation.
    move => s1 o1 s2 o2 s3 o3 t1 t2 t3 i H1' H2' H1 H2; subst H1' H2'; move : (sizeW' t1) (sizeW' t2) (sizeW' t3) => ? ? ?.
    rewrite /access !nth_cat !dflatten_sizeK -H1 -addnA addnBA //.
    case: ifP => H.
     remember_eq Black c' ceq; remember_eq 0 d' deq; move: t2; rewrite -ceq -deq => t2. destruct t2; last by rewrite ceq /= in deq.
     apply leq_addln; apply leq_nth_count.
    remember_eq Black c' ceq; remember_eq 0 d' deq; move: t3; rewrite -ceq -deq => t3. destruct t3; last by rewrite ceq /= in deq.
    apply leq_addrn; apply leq_nth_count.
  Qed.
  Next Obligation.
    move => s1 o1 s2 o2 s3 o3 t1 t2 t3 i H1' H2' H1 H2; subst H1' H2'; move : (sizeW' t1) (sizeW' t2) (sizeW' t3) => ? ? ?.
    rewrite /eq_rect; destruct delete_leaves3_obligation_5,delete_leaves3_obligation_4.
    set balR := (balanceR _ _ _ _ _).
    set d2 := (delete_leaves2 _ _ _).
    by rewrite (proj2_sig balR) (proj2_sig d2) !delete_cat !dflatten_sizeK -!H1. 
  Qed.
  Next Obligation.
    move => s1 o1 s2 o2 s3 o3 t1 t2 t3 i H1' H2' H1 H2; subst H1' H2'; move : (sizeW' t1) (sizeW' t2) (sizeW' t3) => ? ? ?.
    rewrite -subnDA -ltn_subln // in H2.
    by rewrite -H2 subn0 -addnA.
  Qed.
  Next Obligation.
    move => s1 o1 s2 o2 s3 o3 t1 t2 t3 i H1' H2' H1 H2; subst H1' H2'; move : (sizeW' t1) (sizeW' t2) (sizeW' t3) => ? ? ?.
    rewrite -subnDA -ltn_subln // in H2.
    rewrite /access nth_default.
     by rewrite subn0 -addnA.
    by rewrite !size_cat !dflatten_sizeK addnA leqNgt -H2.
  Qed.
  Next Obligation.
    move => s1 o1 s2 o2 s3 o3 t1 t2 t3 i H1' H2' H1 H2; subst H1' H2'; move : (sizeW' t1) (sizeW' t2) (sizeW' t3) => ? ? ?.
    rewrite /eq_rect; destruct delete_leaves3_obligation_8,delete_leaves3_obligation_7.
    rewrite !delete_cat !dflatten_sizeK -!H1.
    case:ifP => H; first rewrite -ltn_subln // ltn_addln // in H2.
    by rewrite -delete_oversize // !dflatten_sizeK leqNgt -H2.
  Qed.
  Next Obligation.
    move => s1 o1 s2 o2 s3 o3 t1 t2 t3 i H1' H2' H1 H2; subst H1' H2'; move : (sizeW' t1) (sizeW' t2) (sizeW' t3) => ? ? ?.
    move: H2.
    rewrite -!ltn_subln //;last apply ltn_addrn => //.
    rewrite ltn_addln //.
  Qed.

  Lemma access_cat s t i : access (s ++ t) i = (if i < size s then access s i else access t (i - size s)).
  Proof. by rewrite /access nth_cat. Qed.

  Definition balanceLR {n s1 s2 s3 o1 o2 o3} {cr}
             (l : tree s1 o1 n.+1 Black)
             (dr : near_tree' s2 o2 n Black)
             (r' : tree s3 o3 n.+1 cr) : 
  {B' : near_tree (s1 + s2 + s3) (o1 + o2 + o3) n.+2 Black
  | dflattenn B' = dflatten l ++ dflattenn' dr ++ dflatten r'}.

   remember_eq n.+1 d' deq. remember_eq Black c' ceq.
   destruct dr as [? ? ? dr|? ? ? dr]; move: dr l r'; rewrite /= -ceq -deq => dr;
    destruct dr as [|? ? ? drc ? dr] => //; move: dr; rewrite /= ceq deq => dr l r'; destruct drc; rewrite catA.
     (* dr = Stay, drc = Red *)
     case (makeBadR l dr) => bad badK. rewrite -badK.
     exact (balanceL Black bad r' erefl erefl).
    (* dr = Stay, drc = Black *)
    by exists (Good Black (bnode (rnode l dr) r')).
    (* dr = Down, drc = Red *)
    case (black_of_red dr) => blacken bK. exists (Good Black (bnode (rnode l blacken) r')). by rewrite -bK. 
   (* dr = Down, drc = Black *)
   move: l dr r'. rewrite -deq -ceq => l; destruct l as [|? ? ? ? ? cl' cr' c ? ? l r] => //; destruct c => //;
   destruct cr'; move/eqP: deq l r; rewrite /= eqSS; move/eqP => /= deq; rewrite deq => l r dr r'; rewrite /= -!catA [dflatten r ++ _ ++ _]catA catA -[s1 + _ + _]addnA -[o1 + _ + _]addnA.
    case (makeBadL r dr) => bad badK. case (balanceR Black l bad erefl erefl) => fst fstK. rewrite -badK -fstK.
    exact (balanceL Black fst r' erefl erefl).
   by exists (Good Black (bnode (bnode l (rnode r dr)) r')). 
  Defined.

  Definition balanceLL {n s1 s2 s3 o1 o2 o3} {cr}
             (dl : near_tree' s1 o1 n Black)
             (r : tree s2 o2 n.+1 Black)
             (r' : tree s3 o3 n.+1 cr) :
  {B' : near_tree (s1 + s2 + s3) (o1 + o2 + o3) n.+2 Black
  | dflattenn B' = dflattenn' dl ++ dflatten r ++ dflatten r'}.

    remember_eq n.+1 d' deq. remember_eq Black c' ceq.
    destruct dl as [? ? ? dl|? ? ? dl]; move: dl r r'; rewrite /= -ceq -deq => dl;
     destruct dl as [|? ? ? dlc ? dl] => //; move: dl; rewrite /= ceq deq => dl r r'; destruct dlc; rewrite catA.
      case (makeBadL dl r) => bad badK. rewrite -badK.
      exact (balanceL Black bad r' erefl erefl).
     by exists (Good Black (bnode (rnode dl r) r')).
     case (black_of_red dl) => blacken bK. rewrite -bK. by exists (Good Black (bnode (rnode blacken r) r')).
    move: r dl r'. rewrite -deq -ceq => r. destruct r as [|? ? ? ? ? cl' cr' c ? ? l r] => //. destruct c => //.
    destruct cl'; move/eqP: deq l r; rewrite /= eqSS; move/eqP => /= deq; rewrite deq => l r dl r'; rewrite !addnA !catA.
     case (makeBadR dl l) => bad badK. case (balanceL Black bad r erefl erefl) => fst fstK. rewrite -badK -fstK. 
     exact (balanceL Black fst r' erefl erefl).
    by exists (Good Black (bnode (bnode (rnode dl l) r) r')).
  Defined.

  Definition balanceRL {n s1 s2 s3 o1 o2 o3} {cl}
             (l' : tree s1 o1 n.+1 cl)
             (dl : near_tree' s2 o2 n Black)
             (r : tree s3 o3 n.+1 Black) :
  {B' : near_tree (s1 + s2 + s3) (o1 + o2 + o3) n.+2 Black
  | dflattenn B' = dflatten l' ++ dflattenn' dl ++ dflatten r}.

    remember_eq n.+1 d' deq. remember_eq Black c' ceq.
    destruct dl as [? ? ? dl|? ? ? dl]; move: l' dl r; rewrite /= -ceq -deq => l' dl r;
     destruct dl as [|? ? ? dlc ? dl] => //; move: l' dl r; rewrite /= ceq deq => l' dl r; destruct dlc; rewrite -!addnA.
      case (makeBadL dl r) => bad badK. rewrite -badK.
      exact (balanceR Black l' bad erefl erefl). 
     by exists (Good Black (bnode l' (rnode dl r))).
     case (black_of_red dl) => blacken bK. rewrite -bK.
     by exists (Good Black (bnode l' (rnode blacken r))).
    move: r l' dl. rewrite -deq -ceq => r. destruct r as [|? ? ? ? ? cl' cr' c ? ? l r] => //. destruct c => //.
    destruct cl'; move/eqP: deq l r; rewrite /= eqSS; move/eqP => /= deq; rewrite deq => l r l' dl; rewrite [_ + (_ + s2)]addnA [_ + (_ + o2)]addnA [dflatten dl ++ _ ++ _]catA.
     case (makeBadR dl l) => bad badK. case (balanceL Black bad r erefl erefl) => fst fstK. rewrite -badK -fstK.
     exact (balanceR Black l' fst erefl erefl).
    by exists (Good Black (bnode l' (bnode (rnode dl l) r))).
  Defined.

  Definition balanceRR {n s1 s2 s3 o1 o2 o3} {cl}
             (l' : tree s1 o1 n.+1 cl)
             (l : tree s2 o2 n.+1 Black)
             (dr : near_tree' s3 o3 n Black) :
  {B' : near_tree (s1 + s2 + s3) (o1 + o2 + o3) n.+2 Black
  | dflattenn B' = dflatten l' ++ dflatten l ++ dflattenn' dr}.

   remember_eq n.+1 d' deq. remember_eq Black c' ceq.
   destruct dr as [? ? ? dr|? ? ? dr]; move: l' l dr; rewrite /= -ceq -deq => l' l dr;
    destruct dr as [|? ? ? drc ? dr] => //; move: l' l dr; rewrite /= ceq deq => l' l dr; destruct drc; rewrite -!addnA.
     case (makeBadR l dr) => bad badK. rewrite -badK.
     exact (balanceR Black l' bad erefl erefl).
    by exists (Good Black (bnode l' (rnode l dr))).
    case (black_of_red dr) => blacken bK. rewrite -bK.
    by exists (Good Black (bnode l' (rnode l blacken))).
   move: l l' dr. rewrite -deq -ceq => l. destruct l as [|? ? ? ? ? cl' cr' c ? ? l r] => //. destruct c => //.
   destruct cr'; move/eqP: deq l r; rewrite /= eqSS; move/eqP => /= deq; rewrite deq => l r l' dr; rewrite -!catA -!addnA.
    case (makeBadL r dr) => bad badK. case (balanceR Black l bad erefl erefl) => fst fstK. rewrite -badK -fstK.
    exact (balanceR Black l' fst erefl erefl).
   by exists (Good Black (bnode l' (bnode l (rnode r dr)))).
  Defined.

  Definition balanceL2 {s1 s2 o1 o2 d}
             (dl : near_tree' s1 o1 d Black)
             (r : tree s2 o2 d.+1 Black) : 
  {B' : near_tree' (s1 + s2) (o1 + o2) d.+1 Black |
  dflattenn' B' = dflattenn' dl ++ dflatten r}.

   remember_eq d.+1 d' deq. remember_eq Black c' ceq.
   destruct dl as [? ? ? dl|? ? ? dl].
    case (balanceL Black dl r erefl erefl) => res resK. by exists (Stay res).
   move: dl r. rewrite /= -ceq -deq => dl r. destruct dl as [|? ? ? dlc ? dl] => //. destruct dlc.
    move: r. rewrite /= ceq deq /= => r.
    case (black_of_red dl) => blacken bK. rewrite -bK.
    by exists (Down (Good Black (rnode blacken r))).
   destruct r as [| ? ? ? ? ? crl ? c ? ? rl rr] => //. subst c. move/eqP: deq dl. rewrite /= eqSS. move/eqP => /= deq. rewrite -deq => dl.
   destruct crl; rewrite !addnA catA.
    case (makeBadR dl rl) => bad badK. case (balanceL Black bad rr erefl erefl) => res resK.
    rewrite -badK -resK. by exists (Down res).
   by exists (Down (Good Black (bnode (rnode dl rl) rr))).
  Defined.

  Definition balanceR2 {s1 s2 o1 o2 d}
             (l : tree s1 o1 d.+1 Black)
             (dr : near_tree' s2 o2 d Black) : 
  {B' : near_tree' (s1 + s2) (o1 + o2) d.+1 Black |
  dflattenn' B' = dflatten l ++ dflattenn' dr}.

   remember_eq d.+1 d' deq. remember_eq Black c' ceq.
   destruct dr as [? ? ? dr|? ? ? dr].
    case (balanceR Black l dr erefl erefl) => res resK. by exists (Stay res).
   move: dr l. rewrite /= -ceq -deq => dr l. destruct dr as [|? ? ? drc ? dr] => //. destruct drc.
    move: l. rewrite /= ceq deq /= => l. 
    case (black_of_red dr) => blacken bK. rewrite -bK.
    by exists (Down (Good Black (rnode l blacken))).
   destruct l as [| ? ? ? ? ? ? clr c ? ? ll lr] => //. subst c. move/eqP: deq dr. rewrite /= eqSS. move/eqP => /= deq. rewrite -deq => dr.
   destruct clr; rewrite -!addnA -catA.
    case (makeBadL lr dr) => bad badK. case (balanceR Black ll bad erefl erefl) => res resK.
    rewrite -badK -resK. by exists (Down res).
   by exists (Down (Good Black (bnode ll (rnode lr dr)))).
  Defined.

  Lemma ltn_trans1 (l m n : nat) : l < m -> m < n.+1 -> l < n.
  Proof.
    move => H1.
    move/eqP => H2. rewrite subSS in H2. move/eqP : H2 => H2.
    exact (leq_trans H1 H2).
  Qed.

  Lemma wf_nat' : forall n : nat, (forall m : nat, m < n -> Acc lt m).
  Proof.
    elim => [?|? IH ? H1]. by rewrite ltn0.
    apply Acc_intro => ?. move/leP => H2.
    exact (IH _ (ltn_trans1 _ _ _ H2 H1)).
  Qed.

  Lemma wf_nat : well_founded lt.
  Proof.
    case => [|?]. apply Acc_intro => ?. move/leP. by rewrite ltn0.
    apply Acc_intro => m. move/leP. move: m. apply wf_nat'.
  Qed.

  Definition ddelete (d : nat) {num ones} (B : tree num ones d.+1 Black) i : 
    { B' : near_tree' (num - (i < num)) (ones - (daccess B i)) d Black | dflattenn' B' = delete (dflatten B) i}.

    move: num ones B i.
    refine (Fix wf_nat (fun (d : nat) => forall (num ones: nat) (B : tree num ones d.+1 Black) (i : nat), _) _ _).
    move => {d} d ddelete num ones B i.

    case val : (i < num);last first.
     move/negP/negP : val. rewrite ltnNge. move/negPn => val.
     rewrite daccess_default // !subn0 -delete_oversize;last by rewrite dflatten_sizeK.
     by exists (Stay (Good Black B)).
    rewrite -val. remember_eq d.+1 d' deq. remember_eq Black c' ceq. move: B. rewrite -deq -ceq => B.
    destruct B as [|s1 o1 s2 o2 ? cl cr c ? ? l r] => //.
    subst c. move/eqP: deq l r. rewrite /= eqSS. move/eqP => /= deq. rewrite deq => l r {deq}.
    rewrite delete_cat dflatten_sizeK.
    move: (sizeW' l) (sizeW' r) => ? ?.
    move: l r. case_eq d => [deq| n deq l r].
    (* d = 0 *)
     destruct cl,cr; [ | |
     (* black,black*)
     | move => l r; case (delete_leaves2 l r i);
       rewrite access_cat dflatten_sizeK !daccessK => res resK; exists (Down res);
       by rewrite /= resK delete_cat dflatten_sizeK
     ]; remember_eq Red c' wc; remember_eq 0 d' wd; rewrite -wc -wd => l r;
     [(* red,red *)
       case: ifP => [Hl|?];
        [ move: (leq_access_count l i Hl) r => ? r';
          destruct l as [| ? ? ? ? d' cl cr c ? ? l r] => //; destruct c,cl,cr,d' => //;
          case (delete_leaves2 l r i);
          rewrite Hl val access_cat !dflatten_sizeK /= -!daccessK;
          set b := (if _ then _ else _) => del delK;
          rewrite /= -delK addsubnC // [_ + _ - b]addsubnC //;
          case (balanceL Black del r' erefl erefl) => res resK
        | move: l val => l';
          rewrite ltn_subln // => Hr;
          move: (leq_access_count r (i - s1) Hr) => ?;
          destruct r as [| ? ? ? ? d' cl cr c ? ? l r] => //; destruct c,cl,cr,d' => //;
          case (delete_leaves2 l r (i - s1));
          rewrite Hr access_cat !dflatten_sizeK /= -!daccessK;
          set b := (if _ then _ else _) => del delK;
          rewrite /= -delK -addnBA // -[(_ + _) - b]addnBA //;
          case (balanceR Black l' del erefl erefl) => res resK ]; rewrite -resK; by exists (Stay res)
      (* red,black or black,red *)
     | move: r => c; destruct l as [| ? ? ? ? d' cl cr c' ? ? a b] => //; destruct c',cl,cr,d' => // 
     | move: l => a; destruct r as [| ? ? ? ? d' cl cr c' ? ? b c] => //; destruct c',cl,cr,d' => //; rewrite !addnA ];
     case (delete_leaves3 a b c i); rewrite /= !daccessK !delete_cat !access_cat !dflatten_sizeK;
     case:ifP => H; 
      [ move => res resK;
        rewrite /= -catA;
        case:ifP;last by rewrite ltn_addln //
      | case: ifP => H2 res resK; case: ifP; [
                    | move/negP/negP : H; rewrite ltnNge; move/negPn => H; rewrite -(ltn_add2r s1) subnK // addnC in H2; by rewrite H2 
                    | move/negP/negP : H2; move/negP/negP : H; rewrite -!leqNgt ltnNge => H; rewrite -(leq_add2r s1) subnK // addnC => H2; by rewrite H2
                    | rewrite !subnDA ]; rewrite /= -catA
      | move => res resK
      | case:ifP => ? res resK ]; exists (Stay res); by rewrite /= resK.
   
   (* d <> 0 *)
   rewrite deq /= in ddelete.
   move/leP: (ltnSn n) => ltnSn.
   case: ifP => Hl.
    move: l r.
    case ceql : cl;last first.
     case ceqr : cr;
     move => l'; move: (leq_access_count l' i Hl) => ?;
     case (ddelete _ ltnSn _ _ l' i);
     set b := (daccess _ _);
     rewrite ltn_addln // Hl => dl dK;
     rewrite addsubnC // [_ + _ - b]addsubnC // -dK.
      (* black, red*)
      rewrite -deq -ceqr => r; destruct r as [| ? ? ? ? ? cl' cr' cr ? ? l r] => //; destruct cr,cl',cr' => //; rewrite /= in deq; subst d.
      case (balanceLL dl l r) => res resK.
      rewrite -resK !addnA. by exists (Stay res).
     (* black, black *)
     move => r.
     exact (balanceL2 dl r).
   (* *, red *)
    rewrite -ceql -deq => l; destruct l as [|s1 ? ? ? ? cl' cr' c ? ? l r ] => //; destruct c,cl',cr' => //; move: deq l r => /= deq; rewrite deq => l r r'.
    move: (sizeW' l) (sizeW' r) => ? ?. rewrite delete_cat dflatten_sizeK.
    case: ifP => Hl'.
     case (ddelete _ ltnSn _ _ l i).
     move: (leq_access_count l i Hl').
     set b := (daccess _ _).
     rewrite ltn_addln // Hl' => ? dl dK. rewrite -dK.
     rewrite -!addnA addsubnC // [_ + _ - b]addsubnC // !addnA.
     case (balanceLL dl r r') => res resK.
     rewrite -catA -resK.
     by exists (Stay res).
    case (ddelete _ ltnSn _ _ r (i - s1)).
    move: (Hl); rewrite ltn_subln // => Hr.
    move: (leq_access_count r (i - s1) Hr).
    set b := (daccess _ _).
    rewrite ltn_addln // Hr => ? dr dK. rewrite -dK.
    rewrite addsubnC // [_ + _ - b]addsubnC //;last apply leq_addrn => //.
    rewrite -!addnBA //.
    case (balanceLR l dr r') => res resK.
    rewrite -catA -resK. by exists (Stay res).

   move: val; rewrite ltn_subln // => Hr.
   move: r l.
   case ceqr : cr;last first.
    case ceql : cl;
    move => r'; move: (leq_access_count r' (i - s1) Hr) => ?;
    case (ddelete _ ltnSn _ _ r' (i - s1));
    set b := (daccess _ _);
    rewrite Hr => dr dK;
    rewrite -dK -!addnBA //.
    (* red, black*)
    rewrite -deq -ceql => l. destruct l as [| s0 ? ? ? ? cl' cr' cl ? ? l r] => //; destruct cl,cl',cr' => //. move: deq l r => /= deq. rewrite deq => l r.
    case (balanceRR l r dr) => res resK. rewrite -catA -resK. by exists (Stay res).
   (* black, black *)
   move => l. exact (balanceR2 l dr).
   (* *, red *)
   rewrite -ceqr -deq => r l. move: l. destruct r as [|s3 ? ? ? ? cl' cr' c ? ? l r ] => //. destruct c,cl',cr' => // /= l'.
   move: deq l' l r => /= deq. rewrite deq => l' l r.
   move: (sizeW' l) (sizeW' r) => ? ?.
   rewrite delete_cat dflatten_sizeK.
   case: ifP => Hl'.
    case (ddelete _ ltnSn _ _ l (i - s1)).
    move: (leq_access_count l (i - s1) Hl').
    set b := (daccess _ _) => ?.
    rewrite Hr Hl' => dl dK. rewrite -dK => {dK}.
    rewrite !addnA addsubnC;last by rewrite leq_addrn.
    rewrite [_ + _ - b]addsubnC;last apply leq_addrn => //.
    rewrite -!addnBA //.
    case (balanceRL l' dl r) => res resK. rewrite -resK. by exists (Stay res).
   case (ddelete _ ltnSn  _ _ r (i - s1 - s3)).
   move: Hr; rewrite addnA ltn_subln // => Hr'.
   move: (leq_access_count r (i - s1 - s3) Hr').
   set b := (daccess _ _) => ?.
   rewrite Hr' => dr dK. rewrite -dK => {dK}.
   rewrite -!addnBA //;last by apply leq_addrn => //.
   case (balanceRR l' l dr) => res resK. rewrite !addnA -resK. by exists (Stay res).
 Defined.

End delete.

Require Import ExtrOcamlNatInt.
Extract Constant w => "8".
Extract Inductive tree => tree_ml [ "LeafML" "(function (s1,o1,s2,o2,d,c,cl,cr,l,r) -> NodeML (s1, o1, s2, o2, c, l, r))" ]
"(fun fl fn ->
  function
  | LeafML arr -> fl arr
  | NodeML (s1,o1,s2,o2,c,(NodeML (_,_,_,_,cl,_,_) as l),(NodeML (_,_,_,_,cr,_,_) as r)) -> fn s1 o1 s2 o2 0 cl cr c l r
  | NodeML (s1,o1,s2,o2,c,(LeafML _ as l),(NodeML (_,_,_,_,cr,_,_) as r)) -> fn s1 o1 s2 o2 0 Black cr c l r
  | NodeML (s1,o1,s2,o2,c,(LeafML _ as l),(LeafML _ as r)) -> fn s1 o1 s2 o2 0 Black Black c l r
  | NodeML (s1,o1,s2,o2,c,(NodeML (_,_,_,_,cl,_,_) as l),(LeafML _ as r)) -> fn s1 o1 s2 o2 0 cl Black c l r)".
Extraction TestCompile dinsert ddelete tree_ml.
Extraction "dydep.ml" dinsert ddelete tree_ml.