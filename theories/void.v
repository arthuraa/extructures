From mathcomp Require Import ssreflect ssrfun eqtype choice fintype.

Notation void := Empty_set.

Definition unit_of_void (x : void) : unit := tt.
Definition void_of_unit (x : unit) : option void := None.

Lemma unit_of_voidK : pcancel unit_of_void void_of_unit.
Proof. by case. Qed.

Definition void_eqMixin := PcanEqMixin unit_of_voidK.
Canonical void_eqType := Eval hnf in EqType void void_eqMixin.
Definition void_choiceMixin := PcanChoiceMixin unit_of_voidK.
Canonical void_choiceType := Eval hnf in ChoiceType void void_choiceMixin.
Definition void_countMixin := PcanCountMixin unit_of_voidK.
Canonical void_countType := Eval hnf in CountType void void_countMixin.
Definition void_finMixin := PcanFinMixin unit_of_voidK.
Canonical void_finType := Eval hnf in FinType void void_finMixin.
