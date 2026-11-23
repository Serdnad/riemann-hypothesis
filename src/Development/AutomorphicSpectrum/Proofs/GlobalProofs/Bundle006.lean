module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.CompanionTheory.Principalise

theorem isIso_of_isIso_comp_of_dense_range {A P V : Scheme.{0}} (a : A ⟶ P) (b : P ⟶ V) [IsIso (a ≫ b)]
    [IsSeparated b] [IsReduced P] (hd : Dense (Set.range a)) : IsIso b ∧ IsIso a := by
  obtain ⟨σ, hσdef⟩ : ∃ σ : V ⟶ P, σ = inv (a ≫ b) ≫ a := ⟨_, rfl⟩
  have hσ : σ ≫ b = 𝟙 V := by simp [hσdef]
  have haσ : (a ≫ b) ≫ σ = a := by simp [hσdef]
  have hid : IsIso (σ ≫ b) := by rw [hσ]; infer_instance
  have : IsClosedImmersion (σ ≫ b) := by rw [hσ]; infer_instance
  have : IsClosedImmersion σ := IsClosedImmersion.of_comp σ b
  have hr : Set.range a ⊆ Set.range σ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(a ≫ b) x, by rw [← Scheme.Hom.comp_apply, haσ]⟩
  have hcl : IsClosed (Set.range σ) := σ.isClosedEmbedding.isClosed_range
  have : Surjective σ := ⟨Set.range_eq_univ.1 (by
    have h := (hd.mono hr).closure_eq
    rwa [hcl.closure_eq] at h)⟩
  have : IsIso σ := isIso_of_isClosedImmersion_of_surjective σ
  have hb : IsIso b := IsIso.of_isIso_comp_left σ b
  exact ⟨hb, IsIso.of_isIso_comp_right a b⟩

theorem isEmpty_of_effCartier_bot {W : Scheme.{0}} (h : FinalTheorems.EffCartier (⊥ : W.IdealSheafData)) : IsEmpty W := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, f, hx, hf, e⟩ := h x
  have hf0 : f = 0 := by
    have : f ∈ (⊥ : W.IdealSheafData).ideal U := e ▸ Ideal.mem_span_singleton_self f
    simpa using this
  have : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  exact nonZeroDivisors.ne_zero hf hf0

theorem dense_range_restrict_of_blowup {X₁ X₂ : Scheme.{0}} [IsIntegral X₁] [Nonempty X₂] {π : X₂ ⟶ X₁}
    {Z : X₁.IdealSheafData} (hB : FinalTheorems.Blowup π Z) (U : X₁.Opens) : Dense (Set.range (π ∣_ U)) := by
  have hZ : Z ≠ ⊥ := by
    rintro rfl
    have h := hB.1
    rw [Scheme.IdealSheafData.comap_bot] at h
    exact (isEmpty_of_effCartier_bot h).false (Nonempty.some inferInstance)
  have hO := GlobalTheory.Principalise.nonempty_compl_support hZ
  have hiso : IsIso (π ∣_ Z.support.compl) :=
    GlobalTheory.Principalise.isIso_restrict_of_blowup hB _ fun x hx => hx
  have hdO : Dense (Z.support.compl : Set X₁) := Z.support.compl.isOpen.dense hO
  have hdU : Dense (U.ι ⁻¹' (Z.support.compl : Set X₁)) := hdO.preimage U.ι.isOpenMap
  refine hdU.mono fun x hx => ?_
  obtain ⟨y, hy⟩ := (π ∣_ Z.support.compl).surjective ⟨x.1, hx⟩
  have hw : π y.1 = x.1 := by
    have := morphismRestrict_base_coe π Z.support.compl y
    rw [hy] at this
    exact this.symm
  refine ⟨⟨y.1, show π y.1 ∈ U by rw [hw]; exact x.2⟩, Subtype.ext ?_⟩
  exact (morphismRestrict_base_coe π U ⟨y.1, _⟩).trans hw

theorem isIso_restrict_of_isIso_restrict_comp_blowup : ∀ {X X₁ X₂ : Scheme.{0}} (s : X₁ ⟶ X) (π : X₂ ⟶ X₁)
    (Z : X₁.IdealSheafData) (V : X.Opens), IsIntegral X₁ → IsSeparated s → FinalTheorems.Blowup π Z → Nonempty X₂ →
    IsIso ((π ≫ s) ∣_ V) → IsIso (s ∣_ V) ∧ IsIso (π ∣_ (s ⁻¹ᵁ V)) := by
  intro X X₁ X₂ s π Z V hX hs hB hne he
  have he' : IsIso (π ∣_ (s ⁻¹ᵁ V) ≫ s ∣_ V) := by
    rw [← morphismRestrict_comp]
    exact he
  exact isIso_of_isIso_comp_of_dense_range (π ∣_ (s ⁻¹ᵁ V)) (s ∣_ V) (dense_range_restrict_of_blowup hB _)

end GlobalTheory.CompanionTheory.Principalise
end
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.ResKCoords

theorem map_maximalIdeal_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) :
    Ideal.map e (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
  ext x
  rw [← Ideal.comap_symm, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  exact isUnit_map_iff e.symm x

theorem rsp_of_ringEquiv {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) (m : ℕ) (r : Fin m → R) (h : FinalTheorems.Rsp R m r) :
    FinalTheorems.Rsp S m (fun i => e (r i)) := by
  refine ⟨?_, h.2.trans (ringKrullDim_eq_of_ringEquiv e)⟩
  have h1 : Set.range (fun i => e (r i)) = (e : R → S) '' Set.range r := by
    rw [← Set.range_comp]; rfl
  rw [h1, ← map_maximalIdeal_of_ringEquiv e, ← h.1]
  exact (Ideal.map_span e (Set.range r)).symm

theorem stalk_to_localization : ∀ (Y : Scheme.{0}) (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1),
    IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
    FinalTheorems.Rsp (Y.presheaf.stalk y) m (fun i => Y.presheaf.germ U.1 y hy (f i)) →
    IsRegularLocalRing (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) ∧
    FinalTheorems.Rsp (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) m
      (fun i => algebraMap Γ(Y, U.1) _ (f i)) ∧
    ∀ s : Γ(Y, U.1), y ∈ Y.basicOpen s ↔ s ∉ (U.2.primeIdealOf ⟨y, hy⟩).asIdeal := by
  intro Y U y hy hreg m f hr
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hy⟩ : U.1)
  haveI hloc : IsLocalization.AtPrime (Y.presheaf.stalk y) (U.2.primeIdealOf ⟨y, hy⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨y, hy⟩
  let e : Y.presheaf.stalk y ≃+* Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal :=
    (IsLocalization.algEquiv (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)).toRingEquiv
  have he : ∀ a : Γ(Y, U.1), e (Y.presheaf.germ U.1 y hy a) = algebraMap Γ(Y, U.1) _ a := fun a =>
    (IsLocalization.algEquiv (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)).commutes a
  refine ⟨IsRegularLocalRing.of_ringEquiv e, ?_, fun s => ?_⟩
  · have h := rsp_of_ringEquiv e m _ hr
    simpa only [he] using h
  · rw [Scheme.mem_basicOpen Y s y hy]
    have h := IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y)
      (U.2.primeIdealOf ⟨y, hy⟩).asIdeal s
    exact h.trans Iff.rfl

end GlobalTheory.CompanionTheory.ResKCoords
end
