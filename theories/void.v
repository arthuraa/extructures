From mathcomp Require Import ssreflect ssrfun eqtype choice fintype.

Notation void := Empty_set.

Definition of_void T (x : void) : T := match x with end.
Definition to_void T (x : T) : option void := None.

Lemma of_voidK T : pcancel (@of_void T) (@to_void T).
Proof. by case. Qed.

Definition void_eqMixin := PcanEqMixin (of_voidK unit).
Canonical void_eqType := Eval hnf in EqType void void_eqMixin.
Definition void_choiceMixin := PcanChoiceMixin (of_voidK unit).
Canonical void_choiceType := Eval hnf in ChoiceType void void_choiceMixin.
Definition void_countMixin := PcanCountMixin (of_voidK unit).
Canonical void_countType := Eval hnf in CountType void void_countMixin.
Definition void_finMixin := PcanFinMixin (of_voidK unit).
Canonical void_finType := Eval hnf in FinType void void_finMixin.
