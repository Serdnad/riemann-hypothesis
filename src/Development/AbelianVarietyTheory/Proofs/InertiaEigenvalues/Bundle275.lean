module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle249
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle248
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle251
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle250
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem avg_equiv : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (G' : Type) [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G'] [SecondCountableTopology G'] [T2Space G'] (Γ : AddSubgroup G) (Γ' : AddSubgroup G'), IsCoLat Γ → IsCoLat Γ' → ∀ e : G ≃ₜ+ G', (∀ x, e x ∈ Γ' ↔ x ∈ Γ) → ∀ Φ : G' → ℂ, Per Γ' Φ → avg Γ (fun x => Φ (e x)) = avg Γ' Φ := by
  intro G _ _ _ _ _ _ G' _ _ _ _ _ _ Γ Γ' hΓ hΓ' e he Φ hΦ
  letI mG : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  letI mG' : MeasurableSpace G' := borel G'
  haveI : BorelSpace G' := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G Γ hΓ
  let f : G ≃ᵐ G' := e.toHomeomorph.toMeasurableEquiv
  haveI := hμ
  have hμ' : (μ.map f).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let eΓ : Γ' ≃ Γ :=
    { toFun := fun g => ⟨e.symm g, (he _).1 (by simpa using g.2)⟩
      invFun := fun x => ⟨e x, (he x).2 x.2⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  have hqmp : Measure.QuasiMeasurePreserving f.toEquiv.symm (μ.map f) μ :=
    MeasurePreserving.quasiMeasurePreserving ⟨f.symm.measurable, f.map_symm_map⟩
  have h𝓕' : IsAddFundamentalDomain Γ' (f '' 𝓕) (μ.map f) := by
    refine h𝓕.image_of_equiv f.toEquiv hqmp eΓ fun g x => ?_
    show e (e.symm (g : G') + x) = (g : G') + e x
    rw [map_add (f := _), ContinuousAddEquiv.apply_symm_apply]
  have hm : (μ.map f) (f '' 𝓕) = 1 := by
    rw [MeasurableEquiv.map_apply, Set.preimage_image_eq _ f.injective, h1]
  have hΦ' : Per Γ (fun x => Φ (e x)) :=
    ⟨hΦ.1.comp e.continuous, fun γ hγ x => by show Φ (e (γ + x)) = Φ (e x); rw [map_add (f := _)]; exact hΦ.2 _ ((he γ).2 hγ) _⟩
  have A := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G' Γ' hΓ' (μ.map f) (f '' 𝓕) hμ' h𝓕' Φ hΦ).2.2.2
  have B := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ h𝓕 _ hΦ').2.2.2
  rw [hm] at A
  rw [h1] at B
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at A B
  rw [← A, ← B, f.measurableEmbedding.setIntegral_map, Set.preimage_image_eq _ f.injective]
  rfl

end GlobalTheory.CuspGeneric
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem continuous_avg_of_periodic : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ →
    ∀ (X : Type) [TopologicalSpace X] (F : X × G → ℂ), Continuous F →
      (∀ x, ∀ γ ∈ Γ, ∀ y, F (x, γ + y) = F (x, y)) → Continuous fun x => avg Γ (fun y => F (x, y)) := by
  intro G _ _ _ _ _ _ Γ hΓ X _ F hF hper
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩

  obtain ⟨μ, D, hμ, hD, hD1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G Γ hΓ
  have hsec : ∀ x : X, Continuous fun y : G => F (x, y) := fun x =>
    hF.comp (continuous_const.prodMk continuous_id)
  have hfacts : ∀ x : X, μ D ≠ 0 ∧ μ D ≠ ⊤ ∧ IntegrableOn (fun y => F (x, y)) D μ ∧
      ∫ y in D, F (x, y) ∂μ = ((μ D).toReal : ℂ) * avg Γ (fun y => F (x, y)) := fun x =>
    GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ D hμ hD (fun y => F (x, y)) ⟨hsec x, fun γ hγ y => hper x γ hγ y⟩

  have hrepr : (fun x => avg Γ (fun y => F (x, y))) = fun x => ∫ y in D, F (x, y) ∂μ := by
    funext x
    rw [(hfacts x).2.2.2, hD1]
    simp
  rw [hrepr]
  obtain ⟨-, K, hK, hcov⟩ := hΓ
  rw [Metric.continuous_iff']
  intro x₀ ε hε

  have hnear : ∀ᶠ x in nhds x₀, ∀ k ∈ K, dist (F (x, k)) (F (x₀, k)) < ε / 2 := by
    refine hK.eventually_forall_of_forall_eventually fun k _ => ?_
    have h1 : ∀ᶠ z : X × G in nhds (x₀, k), dist (F z) (F (x₀, k)) < ε / 4 :=
      Metric.tendsto_nhds.mp (hF.tendsto (x₀, k)) _ (by positivity)
    have h2 : ∀ᶠ z : X × G in nhds (x₀, k), dist (F (x₀, z.2)) (F (x₀, k)) < ε / 4 :=
      Metric.tendsto_nhds.mp (((hsec x₀).comp continuous_snd).tendsto (x₀, k)) _ (by positivity)
    filter_upwards [h1, h2] with z hz1 hz2
    calc dist (F (z.1, z.2)) (F (x₀, z.2))
        ≤ dist (F (z.1, z.2)) (F (x₀, k)) + dist (F (x₀, z.2)) (F (x₀, k)) :=
          dist_triangle_right _ _ _
      _ < ε / 4 + ε / 4 := add_lt_add hz1 hz2
      _ = ε / 2 := by ring
  filter_upwards [hnear] with x hx

  have hall : ∀ y : G, ‖F (x, y) - F (x₀, y)‖ ≤ ε / 2 := by
    intro y
    obtain ⟨γ, hγ, hγK⟩ := hcov y
    rw [← hper x γ hγ y, ← hper x₀ γ hγ y, ← dist_eq_norm]
    exact (hx _ hγK).le
  rw [dist_eq_norm, ← integral_sub (hfacts x).2.2.1 (hfacts x₀).2.2.1]
  calc ‖∫ y in D, (F (x, y) - F (x₀, y)) ∂μ‖ ≤ ε / 2 * μ.real D :=
        norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr (hfacts x).2.1)
          fun y _ => hall y
    _ = ε / 2 := by simp [Measure.real, hD1]
    _ < ε := half_lt_self hε

end GlobalTheory.CuspGeneric
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem avg_add_right (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G) (hΓ : IsCoLat Γ) (Φ : G → ℂ) (hΦ : Per Γ Φ) (y : G) :
    avg Γ (fun x => Φ (x + y)) = avg Γ Φ := by
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G Γ hΓ
  have hΨ : Per Γ (fun x => Φ (x + y)) :=
    ⟨hΦ.1.comp (continuous_add_const y), fun γ hγ x => by simp only [add_assoc, hΦ.2 γ hγ]⟩

  have hpres : MeasurePreserving (fun x : G => x - y) μ μ := by
    simpa [sub_eq_add_neg] using measurePreserving_add_right μ (-y)
  have h𝓕' : IsAddFundamentalDomain Γ ((fun x : G => x - y) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv hpres.quasiMeasurePreserving (e := id) Function.bijective_id (fun γ x => by
      simp only [id, AddSubgroup.vadd_def, vadd_eq_add]; abel)
  have hm' : μ ((fun x : G => x - y) ⁻¹' 𝓕) = 1 := by
    rw [hpres.measure_preimage h𝓕.nullMeasurableSet, h1]
  have hA := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ h𝓕 _ hΨ).2.2.2
  have hB := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ _ hμ h𝓕' Φ hΦ).2.2.2
  rw [h1] at hA
  rw [hm'] at hB
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hA hB
  rw [← hA, ← hB]
  have hpres2 : MeasurePreserving (fun x : G => x + y) μ μ := measurePreserving_add_right μ y
  have hemb : MeasurableEmbedding (fun x : G => x + y) := (MeasurableEquiv.addRight y).measurableEmbedding
  have := hpres2.setIntegral_preimage_emb hemb Φ ((fun x : G => x - y) ⁻¹' 𝓕)
  rw [← this]
  have hs : (fun x : G => x + y) ⁻¹' ((fun x : G => x - y) ⁻¹' 𝓕) = 𝓕 := by
    ext x; simp
  rw [hs]

end GlobalTheory.CuspGeneric
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

section Prod

variable {G₁ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁]
  {G₂ : Type} [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂]

theorem isCoLat_prod {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} (h₁ : IsCoLat Γ₁) (h₂ : IsCoLat Γ₂) :
    IsCoLat (Γ₁.prod Γ₂) := by
  obtain ⟨d₁, K₁, hK₁, c₁⟩ := h₁
  obtain ⟨d₂, K₂, hK₂, c₂⟩ := h₂
  refine ⟨?_, K₁ ×ˢ K₂, hK₁.prod hK₂, fun z => ?_⟩
  · refine DiscreteTopology.of_continuous_injective
      (f := fun z : Γ₁.prod Γ₂ => ((⟨z.1.1, (AddSubgroup.mem_prod.1 z.2).1⟩ : Γ₁),
        (⟨z.1.2, (AddSubgroup.mem_prod.1 z.2).2⟩ : Γ₂))) ?_ ?_
    · exact ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    · intro a b h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 h.2)
  · obtain ⟨γ₁, hγ₁, e₁⟩ := c₁ z.1
    obtain ⟨γ₂, hγ₂, e₂⟩ := c₂ z.2
    exact ⟨(γ₁, γ₂), AddSubgroup.mem_prod.2 ⟨hγ₁, hγ₂⟩, ⟨e₁, e₂⟩⟩

end Prod

section FD

open Pointwise

variable {G₁ : Type} [AddCommGroup G₁] [MeasurableSpace G₁]
  {G₂ : Type} [AddCommGroup G₂] [MeasurableSpace G₂]

theorem vadd_prod_set {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} (g : Γ₁.prod Γ₂) (A : Set G₁) (B : Set G₂) :
    g +ᵥ (A ×ˢ B) = ((g : G₁ × G₂).1 +ᵥ A) ×ˢ ((g : G₁ × G₂).2 +ᵥ B) := by
  ext ⟨x, y⟩
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_prod]
  rfl

theorem isAddFundamentalDomain_prod {Γ₁ : AddSubgroup G₁} {Γ₂ : AddSubgroup G₂} {μ₁ : Measure G₁} {μ₂ : Measure G₂}
    [SFinite μ₁] [SFinite μ₂] {𝓕₁ : Set G₁} {𝓕₂ : Set G₂}
    (h₁ : IsAddFundamentalDomain Γ₁ 𝓕₁ μ₁) (h₂ : IsAddFundamentalDomain Γ₂ 𝓕₂ μ₂) :
    IsAddFundamentalDomain (Γ₁.prod Γ₂) (𝓕₁ ×ˢ 𝓕₂) (μ₁.prod μ₂) := by
  refine ⟨h₁.nullMeasurableSet.prod h₂.nullMeasurableSet, ?_, ?_⟩
  · have a₁ : ∀ᵐ z ∂μ₁.prod μ₂, ∃ γ : Γ₁, γ +ᵥ z.1 ∈ 𝓕₁ := Measure.quasiMeasurePreserving_fst.ae h₁.ae_covers
    have a₂ : ∀ᵐ z ∂μ₁.prod μ₂, ∃ γ : Γ₂, γ +ᵥ z.2 ∈ 𝓕₂ := Measure.quasiMeasurePreserving_snd.ae h₂.ae_covers
    filter_upwards [a₁, a₂] with z ⟨γ₁, e₁⟩ ⟨γ₂, e₂⟩
    exact ⟨⟨((γ₁ : G₁), (γ₂ : G₂)), AddSubgroup.mem_prod.2 ⟨γ₁.2, γ₂.2⟩⟩, ⟨e₁, e₂⟩⟩
  · intro g g' hne
    change μ₁.prod μ₂ ((g +ᵥ (𝓕₁ ×ˢ 𝓕₂)) ∩ (g' +ᵥ (𝓕₁ ×ˢ 𝓕₂))) = 0
    rw [vadd_prod_set, vadd_prod_set, Set.prod_inter_prod, Measure.prod_prod]
    by_cases e : (g : G₁ × G₂).1 = (g' : G₁ × G₂).1
    · have e2 : (g : G₁ × G₂).2 ≠ (g' : G₁ × G₂).2 := fun e2 => hne (Subtype.ext (Prod.ext e e2))
      have := h₂.aedisjoint (i := ⟨(g : G₁ × G₂).2, (AddSubgroup.mem_prod.1 g.2).2⟩)
        (j := ⟨(g' : G₁ × G₂).2, (AddSubgroup.mem_prod.1 g'.2).2⟩) (fun h => e2 (congrArg Subtype.val h))
      rw [show μ₂ (((g : G₁ × G₂).2 +ᵥ 𝓕₂) ∩ ((g' : G₁ × G₂).2 +ᵥ 𝓕₂)) = 0 from this, mul_zero]
    · have := h₁.aedisjoint (i := ⟨(g : G₁ × G₂).1, (AddSubgroup.mem_prod.1 g.2).1⟩)
        (j := ⟨(g' : G₁ × G₂).1, (AddSubgroup.mem_prod.1 g'.2).1⟩) (fun h => e (congrArg Subtype.val h))
      rw [show μ₁ (((g : G₁ × G₂).1 +ᵥ 𝓕₁) ∩ ((g' : G₁ × G₂).1 +ᵥ 𝓕₁)) = 0 from this, zero_mul]

end FD

section Main

theorem avg_prod (G₁ : Type) [AddCommGroup G₁] [TopologicalSpace G₁] [IsTopologicalAddGroup G₁]
    [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁]
    (G₂ : Type) [AddCommGroup G₂] [TopologicalSpace G₂] [IsTopologicalAddGroup G₂]
    [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂]
    (Γ₁ : AddSubgroup G₁) (Γ₂ : AddSubgroup G₂) (h₁ : IsCoLat Γ₁) (h₂ : IsCoLat Γ₂)
    (Φ : G₁ × G₂ → ℂ) (hΦ : Per (Γ₁.prod Γ₂) Φ) :
    avg (Γ₁.prod Γ₂) Φ = avg Γ₁ (fun x => avg Γ₂ (fun y => Φ (x, y))) := by
  letI m₁ : MeasurableSpace G₁ := borel G₁
  haveI : BorelSpace G₁ := ⟨rfl⟩
  letI m₂ : MeasurableSpace G₂ := borel G₂
  haveI : BorelSpace G₂ := ⟨rfl⟩
  have e₁ : ∃ p : Measure G₁ × Set G₁, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ₁ p.2 p.1 ∧ p.1 p.2 = 1 := by
    obtain ⟨μ, F, a, b, c⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G₁ Γ₁ h₁
    exact ⟨(μ, F), a, b, c⟩
  have e₂ : ∃ p : Measure G₂ × Set G₂, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ₂ p.2 p.1 ∧ p.1 p.2 = 1 := by
    obtain ⟨μ, F, a, b, c⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G₂ Γ₂ h₂
    exact ⟨(μ, F), a, b, c⟩
  have A₁ : ∀ Ψ : G₁ → ℂ, avg Γ₁ Ψ = ∫ x in e₁.choose.2, Ψ x ∂e₁.choose.1 := fun Ψ => dif_pos e₁
  have A₂ : ∀ Ψ : G₂ → ℂ, avg Γ₂ Ψ = ∫ y in e₂.choose.2, Ψ y ∂e₂.choose.1 := fun Ψ => dif_pos e₂
  obtain ⟨H₁, F₁, M₁⟩ := e₁.choose_spec
  obtain ⟨H₂, F₂, M₂⟩ := e₂.choose_spec
  set μ₁ := e₁.choose.1
  set 𝓕₁ := e₁.choose.2
  set μ₂ := e₂.choose.1
  set 𝓕₂ := e₂.choose.2
  have hFD : IsAddFundamentalDomain (Γ₁.prod Γ₂) (𝓕₁ ×ˢ 𝓕₂) (μ₁.prod μ₂) := isAddFundamentalDomain_prod F₁ F₂
  have hM : μ₁.prod μ₂ (𝓕₁ ×ˢ 𝓕₂) = 1 := by rw [Measure.prod_prod, M₁, M₂, one_mul]
  obtain ⟨-, -, hI, hE⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average (G₁ × G₂) (Γ₁.prod Γ₂) (isCoLat_prod h₁ h₂) (μ₁.prod μ₂) (𝓕₁ ×ˢ 𝓕₂)
    inferInstance hFD Φ hΦ
  rw [hM, ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hE
  rw [← hE, setIntegral_prod _ hI, A₁]
  simp only [A₂]

end Main

end GlobalTheory.CuspGeneric
end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

variable {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι]

theorem dot_add_right (ξ : ι → E) (x y : ι → Ad E) : dot ξ (x + y) = dot ξ x + dot ξ y := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_add_left (ξ η : ι → E) (x : ι → Ad E) : dot (ξ + η) x = dot ξ x + dot η x := by
  simp only [dot, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem dot_zero_left (x : ι → Ad E) : dot (0 : ι → E) x = 0 := by
  simp [dot]

theorem dot_rat (ξ c : ι → E) :
    dot ξ (fun t => algebraMap E (Ad E) (c t)) = algebraMap E (Ad E) (∑ t, ξ t * c t) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dot, map_sum, map_mul]

theorem dot_single [DecidableEq ι] (t : ι) (c : E) (x : ι → Ad E) :
    dot (Pi.single t c) x = algebraMap E (Ad E) c * x t := by
  rw [dot, Finset.sum_eq_single t]
  · simp
  · intro s _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

theorem StdPsi.forall_dot_eq_one_iff {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (x : ι → Ad E) :
    (∀ ξ : ι → E, ψ (-dot ξ x) = 1) ↔ x ∈ ratV E ι := by
  classical
  constructor
  · intro h
    have hx : ∀ t, ∃ d : E, x t = algebraMap E (Ad E) d := by
      intro t
      refine hψ.ann _ fun c => ?_
      have h1 := h (Pi.single t c)
      rw [dot_single, AddChar.map_neg_eq_inv, inv_eq_one] at h1
      rwa [mul_comm]
    choose d hd using hx
    exact ⟨d, funext fun t => (hd t).symm⟩
  · rintro ⟨c, rfl⟩ ξ
    have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom ι) c =
        fun t => algebraMap E (Ad E) (c t) := rfl
    rw [e, dot_rat, AddChar.map_neg_eq_inv, hψ.rat, inv_one]

theorem StdPsi.per_twist {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {Φ : (ι → Ad E) → ℂ} (hΦ : Per (ratV E ι) Φ)
    (ξ : ι → E) : Per (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x) := by
  refine ⟨(hψ.cont.comp (continuous_dot ξ).neg).mul hΦ.1, ?_⟩
  rintro _ ⟨c, rfl⟩ x
  have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom ι) c =
      fun t => algebraMap E (Ad E) (c t) := rfl
  have h2 := hΦ.2 _ ⟨c, rfl⟩ x
  simp only
  rw [h2, AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv, e, hψ.map_dot ξ c x]

theorem eq_zero_of_avg_character_eq_zero : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι]
    (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ Φ : (ι → Ad E) → ℂ, Per (ratV E ι) Φ →
    (∀ ξ : ι → E, avg (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x) = 0) → Φ = 0 := by
  intro E _ _ ι _ ψ hψ Φ hΦ hco
  letI : MeasurableSpace (ι → Ad E) := borel _
  haveI : BorelSpace (ι → Ad E) := ⟨rfl⟩
  have hL := isCoLat_ratV E ι
  obtain ⟨hd, K, hK, hcov⟩ := id hL
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice (ι → Ad E) (ratV E ι) hL
  haveI := hd
  refine GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (ι → Ad E) (ratV E ι) K hK hcov (ι → E)
    (fun ξ x => ψ (-dot ξ x)) (fun ξ => hψ.cont.comp (continuous_dot ξ).neg) ?_ ?_ ?_
    (fun ξ x => hψ.norm _) (hψ.forall_dot_eq_one_iff) μ 𝓕 hμ h𝓕 Φ hΦ.1 hΦ.2 ?_
  · intro ξ x y
    rw [dot_add_right, neg_add, AddChar.map_add_eq_mul]
  · intro ξ η x
    rw [dot_add_left, neg_add, AddChar.map_add_eq_mul]
  · intro x
    rw [dot_zero_left, neg_zero, AddChar.map_zero_eq_one]
  · intro ξ
    have h2 := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average (ι → Ad E) (ratV E ι) hL μ 𝓕 hμ h𝓕 _ (hψ.per_twist hΦ ξ)).2.2.2
    rw [h2, hco ξ, mul_zero]

end GlobalTheory.CuspGeneric
end
end

section

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.HV

namespace GlobalTheory

namespace PowerSeriesEvalAlgCl

theorem isIntegral_iff_norm_le_one {l : ℕ} [Fact l.Prime] (y : PadicAlgCl l) :
    IsIntegral ℤ_[l] y ↔ ‖y‖ ≤ 1 := by
  have hm : (minpoly ℚ_[l] y).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral y)
  have key : ‖y‖ ≤ 1 ↔ ∀ n, ‖(minpoly ℚ_[l] y).coeff n‖ ≤ 1 := spectralValue_le_one_iff hm
  rw [key]
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · obtain ⟨q, hq, -, hq'⟩ := lifts_and_degree_eq_and_monic
      ((lifts_iff_coeff_lifts (f := algebraMap ℤ_[l] ℚ_[l]) _).2 fun n => ⟨⟨_, h n⟩, rfl⟩) hm
    refine ⟨q, hq', ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq]
    exact minpoly.aeval ℚ_[l] y

theorem exists_coef_ge_finset {l : ℕ} [Fact l.Prime] (c : Coef l) (s : Finset (PadicAlgCl l))
    (hs : ∀ y ∈ s, IsIntegral ℤ_[l] y) : ∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ y ∈ s, y ∈ c'.O := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨c, le_rfl, by simp⟩
  | insert a s _ ih =>
    obtain ⟨c₁, h₁, h₂⟩ := ih fun y hy => hs y (Finset.mem_insert_of_mem hy)
    obtain ⟨c₂, h₃, h₄⟩ := (coefSup l).2.2.1 c₁ a (hs a (Finset.mem_insert_self _ _))
    refine ⟨c₂, h₁.trans h₃, fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact h₄
    · exact h₃ (h₂ y hy)

end PowerSeriesEvalAlgCl

end GlobalTheory
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acris_gauss_norm_eventually_monomial : ∀ (l : ℕ) [Fact l.Prime] (N : ℝ → Per.Acris l → ℝ), (∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N r x ∧ N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧ (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ ∀ a : Per.Ainf l, N r (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ b : Per.Acris l, N (l : ℝ)⁻¹ b ≠ 0 → ∃ (r₁ c : ℝ) (k : ℤ), (l : ℝ)⁻¹ < r₁ ∧ r₁ < 1 ∧ 0 < c ∧ ∀ r, (l : ℝ)⁻¹ < r → r < r₁ → N r b = c * r ^ k := by
  first | exact @GlobalTheory.MemLoc.gauss_slope | exact GlobalTheory.MemLoc.gauss_slope | (intros; apply GlobalTheory.MemLoc.gauss_slope <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.axLemma_padicComplex_fixed_element_approximation : ∀ (l : ℕ) [Fact l.Prime], ∃ c : ℝ, 0 < c ∧ ∀ (H : Subgroup (GQ l)) (y : ℂ_[l]) (r : ℝ), 0 < r → (∀ g ∈ H, ‖Per.σC g y - y‖ ≤ r) → ∃ z : Om l, (∀ g ∈ H, g z = z) ∧ ‖y - (z : ℂ_[l])‖ ≤ c * r := by
  first | exact @GlobalTheory.AxLemma.ax_lemma_complete | exact GlobalTheory.AxLemma.ax_lemma_complete | (intros; apply GlobalTheory.AxLemma.ax_lemma_complete <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.IneAway

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem placesOver_finite_of_prime (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 hw

theorem isoLoc_cusp (D : D7) {a : ℕ} (π : D.naut.CG a) (w : PlE D.host) :
    isoLoc D.nd D.naut [⟨a, π, 1⟩] w = D.naut.locG π w := by
  simp [isoLoc, spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]

end GlobalTheory.IneAway
end
end
