Require Export PnV.Prelude.Prelude.
Require Export PnV.Prelude.ClassicalFacts.
Require Export Stdlib.Logic.EqdepFacts.

Module Quotient.

Export Quot.

Section INDUCTION.

Let subst (A : Type) (B : A -> Type) (a : A) (a' : A) (p : a = a') (b : B a) : B a' :=
  @eq_rect A a B b a' p.

Context {X : Type} {SETOID : isSetoid X} {Q : Type} {QUOTIENT : isQuotientOf Q X}.

Lemma Quot_ind_aux {Y : Type} (f : X -> Y) (p : Y -> Q)
  (f_cong : forall x1, forall x2, x1 == x2 -> f x1 = f x2)
  (f_respect : forall x, p (f x) = mk x)
  : forall q, p (lift f f_cong q) = q.
Proof .
  assert (claim1 : forall q, p (lift f f_cong q) = lift mk sound q).
  { eapply lift_unique. intro x. rewrite lift_compute. eapply f_respect. }
  intro q. specialize claim1 with (q := q). rewrite claim1. symmetry.
  exact (lift_unique mk sound (fun q => q) (fun x => eq_refl) q).
Qed.

Theorem Quot_ind (phi : Q -> Type)
  (f : forall x, phi (mk x))
  (f_cong : forall x1 : X, forall x2 : X, forall EQUIV : x1 == x2, subst Q phi (mk x1) (mk x2) (sound x1 x2 EQUIV) (f x1) = f x2)
  : forall q, phi q.
Proof.
  pose (f' := fun x => @existT Q phi (mk x) (f x)).
  assert (f'_cong : forall x1, forall x2, x1 == x2 -> f' x1 = f' x2).
  { intros x1 x2 EQUIV. subst f'. eapply eq_sigT_sig_eq. exists (sound x1 x2 EQUIV). eapply f_cong. }
  pose (g := fun q => projT2 (lift f' f'_cong q)).
  pose proof (Quot_ind_aux f' (fun x => projT1 x) f'_cong (fun x => @eq_refl _ (mk x))) as claim1.
  intro q. exact (subst Q phi (projT1 (lift f' f'_cong q)) q (claim1 q) (g q)).
Qed.

End INDUCTION.

#[universes(polymorphic=yes)]
Parameter t@{u} : forall X : Type@{u}, isSetoid X -> Type@{u}.

#[universes(polymorphic=yes)]
Axiom Quotient_always_exists : forall X : Type, forall SETOID : isSetoid X, isQuotientOf (Quotient.t@{U_discourse} X SETOID) X (SETOID := SETOID).

#[global] Existing Instance Quotient_always_exists.

End Quotient.

Notation Quot := Quotient.t@{_}.

Section UNIVERSE_TEST.

Let Quot_nat : Set :=
  Quot nat (@mkSetoid_from_eq nat).

End UNIVERSE_TEST.
