Require Export PnV.Prelude.Prelude.
Require Export Stdlib.Logic.ChoiceFacts.
Require Export Stdlib.Logic.ClassicalChoice.
Require Export Stdlib.Logic.EqdepFacts.

Module AxiomOfChoice.

Lemma AC {A : Type} {B : A -> Type} (R : forall x : A, forall y : B x, Prop)
  (EXISTENCE : forall x, exists y, R x y)
  : exists f : forall x : A, B x, forall x, R x (f x).
Proof.
  eapply non_dep_dep_functional_choice; [exact choice | exact EXISTENCE].
Defined.

End AxiomOfChoice.

Module Quot.

#[universes(polymorphic)]
Parameter t@{u} : forall X : Type@{u}, isSetoid X -> Type@{u}.

#[local] Notation Quot := Quot.t.

Axiom Quotient_always_exists : forall X : Type, forall SETOID : isSetoid X, isQuotientOf (Quot X SETOID) X (SETOID := SETOID).

#[global] Existing Instance Quotient_always_exists.

Section INDUCTION.

Let subst (A : Type) (B : A -> Type) (a : A) (a' : A) (p : a = a') (b : B a) : B a' :=
  @eq_rect A a B b a' p.

Context {X : Type} {SETOID : isSetoid X} {Q : Type} {QUOTIENT : isQuotientOf Q X}.

Lemma Quot_ind_aux {Y : Type} (f : X -> Y) (p : Y -> Q)
  (f_cong : forall x1, forall x2, x1 == x2 -> f x1 = f x2)
  (f_respect : forall x, p (f x) = prj x)
  : forall q, p (rec f f_cong q) = q.
Proof .
  assert (claim1 : forall q, p (rec f f_cong q) = rec prj prj_eq q).
  { eapply rec_unique. intro x. rewrite rec_compute. eapply f_respect. }
  intro q. specialize claim1 with (q := q). rewrite claim1. symmetry.
  exact (rec_unique prj prj_eq (fun q => q) (fun x => eq_refl) q).
Qed.

Theorem Quot_ind (phi : Q -> Type)
  (f : forall x, phi (prj x))
  (f_cong : forall x1 : X, forall x2 : X, forall EQUIV : x1 == x2, subst Q phi (prj x1) (prj x2) (prj_eq x1 x2 EQUIV) (f x1) = f x2)
  : forall q, phi q.
Proof.
  pose (f' := fun x => existT phi (prj x) (f x)).
  assert (f'_cong : forall x1, forall x2, x1 == x2 -> f' x1 = f' x2).
  { intros x1 x2 EQUIV. subst f'. eapply eq_sigT_sig_eq. exists (prj_eq x1 x2 EQUIV). eapply f_cong. }
  pose (g := fun q => projT2 (rec f' f'_cong q)).
  pose proof (Quot_ind_aux f' (fun x => projT1 x) f'_cong (fun x => @eq_refl _ (prj x))) as claim1.
  intro q. exact (subst Q phi (projT1 (rec f' f'_cong q)) q (claim1 q) (g q)).
Qed.

End INDUCTION.

End Quot.

Notation Quot := Quot.t.
