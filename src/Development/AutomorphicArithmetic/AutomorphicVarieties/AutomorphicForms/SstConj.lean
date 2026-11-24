module

import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsGalRepOfOfIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SatOfFixed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.CoeffExt TensorProduct Module

namespace UpperTheory.V.Af

theorem isSst_of_coord {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra ℚ_[l] LL] [Algebra ℚ_[l] LL'] [Algebra LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    [Module LL' V'] [IsScalarTower ℚ_[l] LL' V'] [IsScalarTower LL LL' V']
    {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL' ↥(GK K) V'}
    {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)} (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i))
    (hι : finrank LL LL' = Fintype.card ι) [Nonempty ι] (h : IsSst P ρ) : IsSst P ρ' := by
  unfold IsSst at h ⊢
  have e : ↥(Dst P ρ') ≃ₗ[LL] (ι → ↥(Dst P ρ)) :=
    subEquiv (tensCoord E (Bst P)) ((Dst P ρ').restrictScalars LL) _ fun x => by
      simp only [Submodule.restrictScalars_mem, mem_Dst]
      rw [forall_comm]
      refine forall_congr' fun g => ?_
      rw [← (tensCoord E (Bst P)).injective.eq_iff, funext_iff]
      simp only [GlobalTheory.PstExt.tensCoord_stRep P hE]
  have h1 := e.finrank_eq
  have h2 := E.finrank_eq
  rw [finrank_fun', ← Module.finrank_mul_finrank LL LL', hι] at h1 h2
  have hp : 0 < Fintype.card ι := Fintype.card_pos
  rw [Nat.eq_of_mul_eq_mul_left hp h1, Nat.eq_of_mul_eq_mul_left hp h2, h]

theorem isSstAt_conj {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O)
    {a : ℕ} {r r' : ↥Gw →* GL (Fin a) (Om l)} (A : GL (Fin a) (Om l)) (hc : ∀ g, r' g = A * r g * A⁻¹)
    (h : IsSstAt P Bw r) : IsSstAt P Bw r' := by
  intros
  apply _root_.UpperTheory.V.Af.ExLib.isSstAt_conj <;> assumption

theorem sat_ae_of_smooth (hS : SatLoc) {F : Type} [Field F] [NumberField F] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    [Nontrivial V] (ρ : Representation ℂ (GL (Fin n) (Af F)) V) (hρ : GlobalTheory.PRep.IsSmooth ρ)
    (hi : ∀ w, ∃ σ, LocIsotypic ρ w σ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, GlobalTheory.LFun.HasSatGL w (ρ.comp (locGL F n w)) B := by
  intros
  apply _root_.UpperTheory.V.Af.ExLib.eventually_sat <;> assumption

end UpperTheory.V.Af

end
