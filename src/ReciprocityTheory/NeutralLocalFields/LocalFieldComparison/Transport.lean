module

public import ReciprocityTheory.Hypotheses.GalCohDefs
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA

@[expose] public section

noncomputable section

namespace ReciprocityTheory.Neutral.Bridge

open ReciprocityTheory.Gal

variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]

def FinCd2 (rho : Representation R G M) : Prop :=
  Finite (H0 rho) ∧ Finite (H1 rho) ∧ Finite (H2 rho) ∧ ∀ n, 3 ≤ n → Subsingleton (Hn rho n)

def DualityFor (χ : G →* Rˣ) (rho : Representation R G M) (hrho : ContAction rho) : Prop :=
  Nonempty (H2 (charRep χ) ≃ₗ[R] R) ∧
    Function.Bijective (cupH0H2TwistedDual χ rho (MonoidHom.id _)) ∧
    Function.Bijective (cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id)) ∧
    Function.Bijective (cupH1H1TwistedDual χ rho (MonoidHom.id _) (hrho.comp' continuous_id)).flip ∧
    Function.Bijective (cup20 χ rho (MonoidHom.id _))

theorem contAction_comp (e : G ≃ₜ* G') {rho : Representation R G' M} (h : ContAction rho) :
    ContAction (rho.comp (e : G →* G')) := by
  unfold ReciprocityTheory.Gal.ContAction at h ⊢
  exact h.comp ((map_continuous e).prodMap continuous_id)

theorem card_H0_comp_equiv (e : G ≃ₜ* G') (rho : Representation R G' M) :
    Nat.card (H0 (rho.comp (e : G →* G'))) = Nat.card (H0 rho) :=
  (Nat.card_congr (equivH0OfIso e rho (rho.comp (e : G →* G')) (fun _ _ => rfl)).toEquiv).symm

theorem card_H1_comp_equiv (e : G ≃ₜ* G') (rho : Representation R G' M) :
    Nat.card (H1 (rho.comp (e : G →* G'))) = Nat.card (H1 rho) :=
  (Nat.card_congr (equivH1OfIso e rho (rho.comp (e : G →* G')) (fun _ _ => rfl)).toEquiv).symm

theorem card_H2_comp_equiv (e : G ≃ₜ* G') (rho : Representation R G' M) :
    Nat.card (H2 (rho.comp (e : G →* G'))) = Nat.card (H2 rho) :=
  (Nat.card_congr (equivH2OfIso e rho (rho.comp (e : G →* G')) (fun _ _ => rfl)).toEquiv).symm

theorem FinCd2.of_comp (e : G ≃ₜ* G') {rho : Representation R G' M} (h : FinCd2 (rho.comp (e : G →* G'))) :
    FinCd2 rho := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  let rho' := rho.comp (e : G →* G')
  have hc : ∀ g m, rho (e g) m = rho' g m := fun _ _ => rfl
  exact ⟨Finite.of_injective _ (equivH0OfIso e rho rho' hc).injective,
    Finite.of_injective _ (equivH1OfIso e rho rho' hc).injective,
    Finite.of_injective _ (equivH2OfIso e rho rho' hc).injective, fun n hn => by
      have := h3 n hn
      exact (isoHn e rho rho' hc n).toEquiv.subsingleton⟩

theorem DualityFor.of_comp (e : G ≃ₜ* G') (χ : G' →* Rˣ) {rho : Representation R G' M} (hrho : ContAction rho)
    (h : DualityFor (χ.comp (e : G →* G')) (rho.comp (e : G →* G')) (contAction_comp e hrho)) :
    DualityFor χ rho hrho := by
  obtain ⟨⟨h0⟩, h1, h2, h3, h4⟩ := h
  refine ⟨⟨(equivH2OfIso e (charRep χ) (charRep (χ.comp (e : G →* G'))) (fun _ _ => rfl)).trans h0⟩,
    ?_, ?_, ?_, ?_⟩
  · exact bijective_of_iso
      (equivH0OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
        (fun _ _ => rfl))
      (equivH2OfIso e _ _ (twDual_compat e χ rho))
      (equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl))
      _ _ (cupZeroTwo_equiv e χ rho) h1
  · exact bijective_of_iso
      (equivH1OfIso e _ _ (twDual_compat e χ rho))
      (equivH1OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
        (fun _ _ => rfl))
      (equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl))
      _ _ (cupOneOne_equivH1 e χ rho _ _) h2
  · exact bijective_flip_of_iso
      (equivH1OfIso e _ _ (twDual_compat e χ rho))
      (equivH1OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
        (fun _ _ => rfl))
      (equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl))
      _ _ (cupOneOne_equivH1 e χ rho _ _) h3
  · exact bijective_of_iso
      (equivH2OfIso e (rho.comp (MonoidHom.id G')) ((rho.comp (e : G →* G')).comp (MonoidHom.id G))
        (fun _ _ => rfl))
      (equivH0OfIso e _ _ (twDual_compat e χ rho))
      (equivH2OfIso e ((charRep χ).comp (MonoidHom.id G'))
        ((charRep (χ.comp (e : G →* G'))).comp (MonoidHom.id G)) (fun _ _ => rfl))
      _ _ (cupTwoZero_equiv e χ rho) h4

end ReciprocityTheory.Neutral.Bridge
