Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.seq Ssreflect.eqtype.
Require Import Ssreflect.choice Ssreflect.fintype.

Require Import MathComp.tuple MathComp.bigop MathComp.finfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

CoInductive hseq_nil : Type := HSeqNil.
CoInductive hseq_cons T S : Type := HSeqCons of T & S.

Delimit Scope hseq_scope with hseq.
Bind Scope hseq_scope with hseq_cons.

Notation "[ 'hseq' ]" := HSeqNil
  (at level 0, format "[ 'hseq' ]") : form_scope.
Notation "x :: y" := (HSeqCons x y) : hseq_scope.
Notation "[ 'hseq' x ; .. ; y ]" :=
  (HSeqCons x .. (HSeqCons y HSeqNil) ..)
  (at level 0, format "[ 'hseq' '['  x ; '/'  .. ; '/'  y ']' ]")
  : form_scope.

Section Def.

Variable I : Type.

Section Basic.

Variable (T_ : I -> Type).

Fixpoint hseq (idx : seq I) : Type :=
  if idx is i :: idx then hseq_cons (T_ i) (hseq idx) else hseq_nil.

Definition htags idx of hseq idx := idx.

Lemma hseq0 : all_equal_to [hseq].
Proof. by case. Qed.

Definition hshead i idx (hs : hseq (i :: idx)) : T_ i :=
  let: (x :: _)%hseq := hs in x.

Definition hsbehead idx : hseq idx -> hseq (behead idx) :=
  match idx with
  | [::]     => fun _  => [hseq]
  | _ :: idx => fun hs => let: (_ :: hs)%hseq := hs in hs
  end.

End Basic.

End Def.

Bind Scope hseq_scope with hseq.

Section HSeqEqType.

Variables (I : Type) (T_ : I -> eqType).

Fixpoint hseq_eq (idx : seq I) : rel (hseq T_ idx) :=
  match idx with
  | [::]     => fun _   _   => true
  | i :: idx => fun hs1 hs2 =>
                  (hshead hs1 == hshead hs2)
                  && hseq_eq (hsbehead hs1) (hsbehead hs2)
  end.

Lemma hseq_eqP idx : Equality.axiom (@hseq_eq idx).
Proof.
move=> hs1 hs2 /=; apply/(iffP idP) => [H|<- {hs2}].
  elim: idx hs1 hs2 H => [|i idx IH] /=
                      => [[] []|[x1 hs1] [x2 hs2]] //=.
  by move=> /andP [/eqP <- /IH <-].
elim: idx hs1 => [|i idx IH] //= [x hs] /=.
by rewrite eqxx IH.
Qed.

Definition hseq_eqMixin idx := EqMixin (@hseq_eqP idx).
Canonical hseq_eqType idx :=
  Eval hnf in EqType (hseq T_ idx) (hseq_eqMixin idx).

End HSeqEqType.

Module Import HSeqChoiceType.

Section Def.

Variables (I : Type) (T_ : I -> choiceType).

Import Choice.InternalTheory.
Import CodeSeq.

Fact hseq_choiceMixin idx : choiceMixin (hseq T_ idx).
Proof.
pose fix f idx ns {struct idx} :=
  match idx return pred (hseq T_ idx) -> option (hseq T_ idx) with
  | [::] => fun P => if P [hseq] then Some [hseq] else None
  | i :: idx' =>
    fun P =>
      if ns is n :: ns' then
        let fr x := f idx' ns' (fun hs => P (x :: hs)%hseq) in
        obind (fun x => omap (HSeqCons x) (fr x)) (find fr n)
      else None
  end.
exists (fun P n => f idx (decode n) P) => [P n hs|P [hs Hhs]|P Q E n].
- elim: idx P {n}(decode n) hs=> [|i idx IH] /= P
                              => [_ []|[|n ns] [x hs]] //.
    by case: (P _).
  case E: (find _ _) => [x'|] //=.
  have := correct E; case fE: (f _ _) => [hs'|] //= _ [Hx Hhs].
  rewrite {}Hx {}Hhs {x' hs'} in E fE; exact: IH fE.
- suff [ns H]: exists ns, f idx ns P by exists (code ns); rewrite codeK.
  elim: idx P hs Hhs=> [|i idx IH] /= P
                    => [[] ->|[x hs] H]; first by exists [::].
  have [ns Hns]: exists ns, f idx ns (fun hs => P (x :: hs)%hseq).
    by apply: IH; eauto.
  have [|n Hn] :=
    @complete _ (fun x => f idx ns (fun hs' => P (x :: hs')%hseq)).
    by eauto.
  case E: (find _ _) Hn => [x'|] //= _; have Hns' := correct E.
  exists (n :: ns); rewrite E /=.
  by case: (f _ _ _) Hns'.
elim: idx P Q E {n}(decode n) => [|i idx IH] /= P Q E => [_|[|n ns] //].
  by rewrite (E [hseq]).
pose fx (P : pred (hseq T_ (i :: idx))) x :=
  f idx ns (fun hs => P (x :: hs)%hseq).
have E' : fx P =1 fx Q by move=> x; apply: IH=> hs; apply: E.
have {IH} -> : find (fx P) =1 find (fx Q).
  by apply: extensional => x; rewrite E'.
case: (find _ _) => [x|] //=.
by rewrite /fx in E'; rewrite E'.
Qed.
Canonical hseq_choiceType idx :=
  Eval hnf in ChoiceType (hseq T_ idx) (hseq_choiceMixin idx).

End Def.

End HSeqChoiceType.

Module HSeqCountType.

Section Def.

Variables (I : Type) (T_ : I -> countType).

Fixpoint nats_of_hseq idx : hseq T_ idx -> seq nat :=
  match idx with
  | [::] => fun _ => [::]
  | i :: idx => fun hs => pickle (hshead hs) :: nats_of_hseq (hsbehead hs)
  end.

Fixpoint hseq_of_nats idx : seq nat -> option (hseq T_ idx) :=
  match idx return seq nat -> option (hseq T_ idx) with
  | [::] => fun _ => Some [hseq]
  | i :: idx =>
    fun ns =>
      let mkHs x := omap (HSeqCons x) (hseq_of_nats idx (behead ns)) in
      obind (obind mkHs \o unpickle) (ohead ns)
  end.

Lemma nats_of_hseqK idx : pcancel (@nats_of_hseq idx) (hseq_of_nats idx).
Proof.
elim: idx => [|i idx IH] => [[] //|/= [x hs] /=].
by rewrite pickleK /= IH.
Qed.

End Def.

End HSeqCountType.

Definition hseq_countMixin I T_ idx :=
  PcanCountMixin (@HSeqCountType.nats_of_hseqK I T_ idx).
Canonical hseq_countType I (T_ : I -> countType) idx :=
  Eval hnf in CountType (hseq T_ idx) (hseq_countMixin T_ idx).

Module Type FinHSeqSig.
Section FinHSeqSig.
Variables (I : Type) (T_ : I -> finType) (idx : seq I).
Parameter enum : seq (hseq T_ idx).
Axiom enumP : Finite.axiom enum.
Axiom size_enum : size enum = foldr muln 1 [seq #|T_ i| | i <- idx].
End FinHSeqSig.
End FinHSeqSig.

Module FinHSeq.
Section FinHSeq.
Variables (I : Type) (T_ : I -> finType).

Fixpoint enum idx : seq (hseq T_ idx) :=
  match idx with
  | [::] => [:: [hseq]]
  | i :: idx =>
    flatten (codom (fun x : T_ i => map (HSeqCons x) (enum  idx)))
  end.

Lemma enumP idx : Finite.axiom (enum idx).
Proof.
elim: idx=> [|i idx' IH] => /= [[]|/= [x hs]] //=.
move/(_ hs) in IH.
transitivity (x \in T_ i : nat)=> //.
rewrite -mem_enum codomE.
elim: (fintype.enum (T_ i)) (enum_uniq (T_ i))=> //= y e IHe /andP[/negPf ney].
rewrite count_cat count_map inE /preim /= {1}/eq_op /= eq_sym => {IHe}/IHe->.
by case: eqP => [->|_]; rewrite ?(ney, count_pred0, IH).
Qed.

Lemma size_enum idx : size (enum idx) = foldr muln 1 [seq #|T_ i| | i <- idx].
Proof.
elim: idx=> [|i idx' /= <-] //=; rewrite cardE /codom /image_mem.
elim: (fintype.enum (T_ i)) => //= x xs IHxs.
by rewrite size_cat {}IHxs size_map mulSn /preim /=; congr addn.
Qed.

End FinHSeq.
End FinHSeq.

Section UseFinHSeq.

Variables (I : Type) (T_ : I -> finType) (idx : seq I).

Definition hseq_finMixin := FinMixin (@FinHSeq.enumP I T_ idx).
Canonical hseq_finType := Eval hnf in FinType (hseq T_ idx) hseq_finMixin.

End UseFinHSeq.

(* Leave this out for now

Section HIdx.

Section Def.

Variable (I : eqType) (i : I) (idx : seq I).

Record hidx := HIdx {
  hival :> 'I_(size idx);
  _ : tnth (in_tuple idx) hival == i
}.

Canonical hidx_subType := [subType for hival].
Definition hidx_eqMixin := [eqMixin of hidx by <:].
Canonical hidx_eqType := EqType hidx hidx_eqMixin.
Definition hidx_choiceMixin := [choiceMixin of hidx by <:].
Canonical hidx_choiceType := ChoiceType hidx hidx_choiceMixin.
Definition hidx_countMixin := [countMixin of hidx by <:].
Canonical hidx_countType := CountType hidx hidx_countMixin.
Canonical hidx_subCountType := [subCountType of hidx].
Definition hidx_finMixin := [finMixin of hidx by <:].
Canonical hidx_finType := FinType hidx hidx_finMixin.
Canonical hidx_subFinType := [subFinType of hidx].

Lemma card_hidx : #|{: hidx}| = count (pred1 i) idx.
Proof.
rewrite card_sub -sum1_card big_mkcond /=.
pose f (x : 'I_(size idx)) := nth i idx x == i : nat.
rewrite (eq_big_seq f) /= {}/f; last first.
  by move=> i' _; rewrite /= inE (tnth_nth i).
elim: idx => /= [|i' idx' <-]; first by rewrite big_ord0.
by rewrite big_mkcond /= big_ord_recl /= -big_mkcond /=.
Qed.

Lemma tuple_of_hseq_proof T_ (hs : hseq T_ idx) : size hs == size idx.
Proof. by rewrite -[in X in _ == X](eqP (valP hs)) size_map. Qed.
Canonical tuple_of_hseq T_ (hs : hseq T_ idx) := Tuple (tuple_of_hseq_proof hs).

Lemma hnth_proof T_ (hs : hseq T_ idx) (n : hidx) :
  tag (tnth [tuple of hs] n) = i.
Proof.
case: hs n => [t /= Ht] [n /= /eqP <-] /=.
rewrite (tnth_nth i) -[in X in nth _ X _](eqP Ht).
by rewrite -tnth_map /= (tnth_nth i).
Qed.

Definition hnth T_ (hs : hseq T_ idx) (n : hidx) : T_ i :=
  eq_rect _ T_ (tagged (tnth [tuple of hs] n)) _ (hnth_proof hs n).

End Def.

Definition hidx0 {I : eqType} {i : I} {idx : seq I} : hidx i (i :: idx) :=
  HIdx (eqxx _ : tnth (in_tuple (i :: idx)) (ord0 : 'I_(size idx).+1) == i).

End HIdx.

Notation "[ 'hnth' hs i ]" :=
  (let i' := @Ordinal (size (hstags hs)) i (erefl true) in
   hnth hs (@HIdx _ _ (hstags hs) i' (eqxx (tnth (in_tuple (hstags hs)) i'))))
  (at level 0, hs, i at level 8, format "[ 'hnth'  hs  i ]") : form_scope.

*)

Section HNth.

Variables (I : Type) (T_ : I -> Type).

Fixpoint hnth' (idx : seq I) (i : I) (x : T_ i)
               : hseq T_ idx -> forall n, T_ (nth i idx n) :=
  match idx return hseq T_ idx -> forall n, T_ (nth i idx n) with
  | [::]      => fun _  n =>
                   match n with
                   | 0 => x
                   | S _ => x
                   end
  | i' :: idx => fun hs n =>
                   match n with
                   | 0 => hshead hs
                   | S n' => hnth' x (hsbehead hs) n'
                   end
  end.

Lemma hnth_default (idx : seq I) (hs : hseq T_ idx) (n : 'I_(size idx))
  : {i : I & T_ i}.
Proof.
case: idx hs n=> [|i idx] hs n; first by case: n.
exact: Tagged T_ (hshead hs).
Qed.

Definition hnth (idx : seq I) (hs : hseq T_ idx) (n : 'I_(size idx)) :=
  hnth' (tagged (hnth_default hs n)) hs n.

End HNth.

Notation "[ 'hnth' hs i ]" :=
  (hnth hs (@Ordinal (size (htags hs%hseq)) i (erefl true)))
  (at level 0, hs, i at level 8, format "[ 'hnth'  hs  i ]") : form_scope.

Lemma hseq_eta (I : Type) (T_ : I -> Type) i idx :
  forall hs : hseq T_ (i :: idx),
    hs = (hshead hs :: hsbehead hs)%hseq.
Proof. by case. Qed.

Fixpoint hmap (I : Type) (T_ S_ : I -> Type) (idx : seq I)
              (f : forall i, T_ i -> S_ i)
              : hseq T_ idx -> hseq S_ idx :=
  match idx with
  | [::]     => fun hs => hs
  | i :: idx => fun hs => (f _ (hshead hs) :: hmap f (hsbehead hs))%hseq
  end.

Lemma hmapK (I : eqType) T_ S_ idx
            (f : forall i : I, T_ i -> S_ i)
            (g : forall i : I, S_ i -> T_ i) :
  (forall i, cancel (f i) (g i)) ->
  cancel (hmap f : hseq T_ idx -> _) (hmap g).
Proof.
move=> fK; elim: idx=> [|i idx IH] //= [x hs] /=.
by rewrite IH fK.
Qed.

Fixpoint split_tuple T ns :
  (sumn ns).-tuple T -> hseq (fun n => n.-tuple T) ns :=
  match ns with
  | [::] => fun t => [hseq]
  | n :: ns' =>
    fun t =>
      let t1 := [tuple of take n t] in
      let ts := [tuple of drop n t] in
      (tcast (minn_idPl (leq_addr (sumn ns') n)) t1 ::
             split_tuple (tcast (addKn n (sumn ns')) ts))%hseq
  end.

Fixpoint merge_tuple T ns :
  hseq (fun n => n.-tuple T) ns -> (sumn ns).-tuple T :=
  match ns with
  | [::] =>
    fun hs => [tuple]
  | n :: ns' =>
    fun hs => [tuple of hshead hs ++ merge_tuple (hsbehead hs)]
  end.

Lemma merge_tupleK T ns : cancel (@merge_tuple T ns) (@split_tuple T ns).
Proof.
elim: ns => [|n ns IH] /= hs; first by rewrite [in RHS]hseq0.
case: hs=> t hs /=.
congr HSeqCons.
  set t' := [tuple of take _ _]; move: (minn_idPl _)=> E.
  have : val t' = val t by rewrite /t' /= take_size_cat //= size_tuple.
  by move: (E) t'; rewrite {}E=> E t'; rewrite tcast_id; apply: val_inj.
set t' := [tuple of drop _ _]; move: (addKn _ _) => E.
suff -> : tcast E t' = merge_tuple hs by rewrite IH.
have : val t' = val (merge_tuple hs).
  by rewrite /t' /= drop_size_cat // ?size_tuple // mkhseqE //=.
by move: (E) t'; rewrite {}E=> E t'; rewrite tcast_id; apply: val_inj.
Qed.

Lemma split_tupleK T ns : cancel (@split_tuple T ns) (@merge_tuple T ns).
Proof.
elim: ns => [|n ns IH] /= t //=; first by rewrite [in RHS]tuple0.
have H : forall m (E : m = n) t', val (tcast E t') = val t'.
  by move=> T' m E; move: (E); rewrite {}E => E t'; rewrite tcast_id.
apply: val_inj=> /=; rewrite !{}H /=.
rewrite -[in RHS](cat_take_drop n t); congr cat.
rewrite -[drop n t]/(val [tuple of drop n t]).
move: (addKn _ _) [tuple of drop n t] => E; move: (E); rewrite {}E=> E t'.
by rewrite tcast_id -[in RHS](IH t') /=; congr merge_tuple; apply: val_inj.
Qed.
