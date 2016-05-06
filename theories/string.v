From mathcomp Require Import
  ssreflect ssrfun ssrbool eqtype choice seq.

Require Import Coq.Strings.Ascii Coq.Strings.String.

Require Import ord nominal.

Notation string := string.

Definition tuple_of_ascii c :=
  let: Ascii x1 x2 x3 x4 x5 x6 x7 x8 := c in
  (x1, x2, x3, x4, x5, x6, x7, x8).

Definition ascii_of_tuple t :=
  let: (x1, x2, x3, x4, x5, x6, x7, x8) := t in
  Ascii x1 x2 x3 x4 x5 x6 x7 x8.

Lemma tuple_of_asciiK : cancel tuple_of_ascii ascii_of_tuple.
Proof. by case. Qed.

Definition ascii_eqMixin := CanEqMixin tuple_of_asciiK.
Canonical ascii_eqType := Eval hnf in EqType ascii ascii_eqMixin.
Definition ascii_choiceMixin := CanChoiceMixin tuple_of_asciiK.
Canonical ascii_choiceType := Eval hnf in ChoiceType ascii ascii_choiceMixin.
Definition ascii_ordMixin := CanOrdMixin tuple_of_asciiK.
Canonical ascii_ordType :=
  Eval hnf in OrdType ascii ascii_ordMixin.

Fixpoint seq_of_string s :=
  if s is String c s' then c :: seq_of_string s'
  else [::].

Fixpoint string_of_seq s :=
  if s is c :: s' then String c (string_of_seq s')
  else EmptyString.

Lemma seq_of_stringK : cancel seq_of_string string_of_seq.
Proof. by elim=> [|c s /= ->]. Qed.

Definition string_eqMixin := CanEqMixin seq_of_stringK.
Canonical string_eqType := Eval hnf in EqType string string_eqMixin.
Definition string_choiceMixin := CanChoiceMixin seq_of_stringK.
Canonical string_choiceType :=
  Eval hnf in ChoiceType string string_choiceMixin.
Definition string_ordMixin := CanOrdMixin seq_of_stringK.
Canonical string_ordType := Eval hnf in OrdType string string_ordMixin.
Canonical string_nominalType := Eval hnf in [nominalType for string by //].
Canonical string_trivialNominalType :=
  Eval hnf in [trivialNominalType for string].
