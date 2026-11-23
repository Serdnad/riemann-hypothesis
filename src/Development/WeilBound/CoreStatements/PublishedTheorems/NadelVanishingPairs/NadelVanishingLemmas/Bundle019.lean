module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle979
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle015
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle012
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle013
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle018
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierProjectionProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.spread_out_smooth_proper : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), Smooth f → IsProper f → ∀ (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (h : ∀ i, (L i).IsLB) (M : LB X) (hM : M.IsLB), ∃ (R : Subring k) (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R) (π : X ⟶ X₁) (L₁ : Fin s → LB X₁) (σ₁ : ∀ i, (L₁ i).Sec) (h₁ : ∀ i, (L₁ i).IsLB) (M₁ : LB X₁) (hM₁ : M₁.IsLB), Algebra.FiniteType ℤ R ∧ Smooth f₁ ∧ IsProper f₁ ∧ IsPullback π f f₁ (spMap R.subtype) ∧ (∀ i, cls (L i) (h i) = CechPic.pull π (cls (L₁ i) (h₁ i))) ∧ (∀ i, SameDiv (σ i) (Cartier.secPull (σ₁ i) π)) ∧ cls M hM = CechPic.pull π (cls M₁ hM₁) := by
  first | exact @_root_.GlobalTheory.LogPair.exists_model_with_sections | exact _root_.GlobalTheory.LogPair.exists_model_with_sections | (intros; apply _root_.GlobalTheory.LogPair.exists_model_with_sections <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem GlobalTheory.LogPair.relSnc_spread : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [Smooth f] [IsProper f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), IsPullback π f' f (spMap φ) → (∀ i, (L i).IsLB) → RelSnc f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T), IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → RelSnc g d (fun i => (L i).pull ρ) (fun i => Cartier.secPull (σ i) ρ) := by
  intro R k _ _ φ X X' f f' π _ _ d s L σ hpb hL hrel
  let W : X.Opens := ⨆ C : SncChart f d L σ, C.U
  have hW : π ⁻¹ᵁ W = ⊤ := by
    refine top_unique fun y _ => ?_
    obtain ⟨C', hC'⟩ := hrel.chart y
    obtain ⟨C, hC⟩ := GlobalTheory.T.snc_chart_descends R k φ X X' f f' π d s L σ C' y hpb hC'
    show π y ∈ W
    exact (Opens.mem_iSup).2 ⟨C, hC⟩
  obtain ⟨a, ha, h⟩ := GlobalTheory.T.universallyClosed_open_containing_fibre_contains_nearby R k φ X X' f f' π W hpb hW
  refine ⟨a, ha, fun T _ χ hχ Z g ρ hρ => ?_⟩
  have hZ := h T χ hχ Z g ρ hρ
  refine ⟨fun i => LB.isLB_pull (hL i) ρ, fun z => ?_⟩
  have hz : ρ z ∈ W := by
    have : z ∈ ρ ⁻¹ᵁ W := by rw [hZ]; trivial
    exact this
  obtain ⟨C, hC⟩ := (Opens.mem_iSup).1 hz
  obtain ⟨C', hC'⟩ := GlobalTheory.T.snc_chart_base_change R T χ X Z f g ρ d s L σ C hρ
  refine ⟨C', ?_⟩
  rw [hC']
  exact hC
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR

theorem mem_chartForms_iff_sum_card {K : Type} [Field K] (A : Subring K) {n : ℕ} (x : Fin n → Kˣ)
    (J : Finset (Fin n)) (t : Kˣ) (a : ℕ) (η : abelian₂ K) :
    η ∈ chartForms A x J t a ↔ ∃ d : {I : Finset (Fin n) // I.card = a} → K, (∀ I, d I ∈ A) ∧
      η = ∑ I, d I • (((t⁻¹ * ∏ j ∈ I.1 \ J, x j : Kˣ) : K) • logWedge x I.1) := by
  classical
  rw [GlobalTheory.T.mem_chart_forms_iff K A n x J t a η]
  have ht : (t : K) ≠ 0 := t.ne_zero
  have hP : ∀ I : Finset (Fin n), ∏ j ∈ I \ J, (x j : K) ≠ 0 := fun I =>
    Finset.prod_ne_zero_iff.2 fun j _ => (x j).ne_zero
  have hsplit : ∀ f : Finset (Fin n) → abelian₂ K, (∀ I, I.card ≠ a → f I = 0) →
      ∑ I, f I = ∑ I : {I : Finset (Fin n) // I.card = a}, f I.1 := by
    intro f hf
    rw [← Fintype.sum_subtype_add_sum_subtype (fun I : Finset (Fin n) => I.card = a) f,
      Finset.sum_eq_zero (s := (Finset.univ : Finset {I : Finset (Fin n) // ¬ I.card = a}))
        (fun I _ => hf I.1 I.2), add_zero]
  constructor
  · rintro ⟨c, hc0, hcA, rfl⟩
    refine ⟨fun I => c I.1 * t / ∏ j ∈ I.1 \ J, (x j : K), fun I => hcA I.1, ?_⟩
    rw [hsplit (fun I => c I • logWedge x I) (fun I hI => by simp only [hc0 I hI, zero_smul])]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [smul_smul]
    congr 1
    have := hP I.1
    push_cast
    field_simp
  · rintro ⟨d, hdA, rfl⟩
    refine ⟨fun I => if h : I.card = a then d ⟨I, h⟩ * ((t⁻¹ * ∏ j ∈ I \ J, x j : Kˣ) : K) else 0,
      ?_, ?_, ?_⟩
    · intro I hI
      simp [hI]
    · intro I
      by_cases hI : I.card = a
      · dsimp only
        rw [dite_eq_left hI]
        have e : d ⟨I, hI⟩ * ((t⁻¹ * ∏ j ∈ I \ J, x j : Kˣ) : K) * t / ∏ j ∈ I \ J, (x j : K) =
            d ⟨I, hI⟩ := by
          have := hP I
          push_cast
          field_simp
        rw [e]
        exact hdA _
      · dsimp only
        rw [dif_neg hI, zero_mul, zero_div]
        exact zero_mem A
    · rw [hsplit (fun I => (if h : I.card = a then d ⟨I, h⟩ * ((t⁻¹ * ∏ j ∈ I \ J, x j : Kˣ) : K)
          else 0) • logWedge x I) (fun I hI => by simp only [dif_neg hI, zero_smul])]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [dite_eq_left I.2, smul_smul]

theorem latModel_logAt_isFiniteQC : ∀ (X : Scheme.{0}) [IsIntegral X] {C : Type} [Fintype C]
    (E : C → CartierDiv X) {n : ℕ} {ι : Type} (𝒜 : SncAtlas E n ι) (G : CartierDiv X) (a : ℕ)
    (F : X.Modules), LatModel (logAt (suppAll E) G a) F → GlobalTheory.QCoh.IsFiniteQC F := by
  intro X _ C _ E n ι 𝒜 G a F hF
  refine GlobalTheory.T.lattice_model_finite_quasicoherent X _ F hF fun y => ?_
  obtain ⟨i, hi⟩ : ∃ i, y ∈ 𝒜.U i := by
    have : y ∈ (⨆ i, 𝒜.U i) := by rw [𝒜.cover]; trivial
    simpa [Opens.mem_iSup] using this
  obtain ⟨t, ht⟩ := G.exists_isEqn y
  obtain ⟨W, hyW, hW⟩ := ht.exists_nhds
  obtain ⟨f, hfW, hyf⟩ := (𝒜.affine i).exists_basicOpen_le (V := W) ⟨y, hyW⟩ hi
  let S := {I : Finset (Fin n) // I.card = a}
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let u : S → X.functionFieldˣ := fun I => t⁻¹ * ∏ j ∈ I.1 \ 𝒜.J i, 𝒜.x i j
  let g : S → abelian₂ X.functionField := fun I => ((u I : X.functionFieldˣ) : X.functionField) • logWedge (𝒜.x i) I.1
  refine ⟨X.basicOpen f, Fintype.card S, fun k => g (e k), hyf, (𝒜.affine i).basicOpen f, ?_, ?_⟩
  · have hc : IsCoord (𝒜.x i) := ((𝒜.chart i).chart _ (𝒜.gen i)).coord
    have h1 := (GlobalTheory.LogDR.logWedge_basis _ n (𝒜.x i) hc).1.comp (fun k => (e k).1)
      (Subtype.val_injective.comp e.injective)
    exact h1.units_smul (fun k => u (e k))
  · intro z hz w
    have hzU : z ∈ 𝒜.U i := X.basicOpen_le f hz
    have hzt : G.IsEqn z t := hW z (hfW hz)
    rw [GlobalTheory.T.log_forms_eq_chart_forms (suppAll E) (𝒜.U i) (𝒜.x i) (𝒜.J i) G z t a (𝒜.chart i) hzU hzt,
      mem_chartForms_iff_sum_card]
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨fun k => d (e k), fun k => hd _, (e.sum_comp fun I => d I • g I).symm⟩
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun I => c (e.symm I), fun I => hc _, ?_⟩
      rw [← e.sum_comp]
      simp only [Equiv.symm_apply_apply]
      rfl

end GlobalTheory.LogDR
end
end

section

open GlobalTheory GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.cartier_projection_properties : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) (x : Fin n → Kˣ), IsCoord x → ∃ (h Q : abelian₂ K →+ abelian₂ K) (π : K →+ K), (∀ η, η - Q η = extD K (h η) + h (extD K η)) ∧ (∀ c I, Q (c • logWedge x I) = π c • logWedge x I) ∧ (∀ c, ∃ g : K, π c = g ^ p) ∧ (∀ g : K, π (g ^ p) = g ^ p) ∧ (∀ η, Q (extD K η) = 0) ∧ ∀ T : ℕ → AddSubgroup (abelian₂ K), (∀ q, ∀ η ∈ T q, extD K η ∈ T (q + 1)) → (∀ i θ, IsEulerContraction x i θ → (∀ q, ∀ η ∈ T (q + 1), θ η ∈ T q) ∧ ∀ η ∈ T 0, θ η = 0) → (∀ q, ∀ η ∈ T (q + 1), h η ∈ T q) ∧ (∀ η ∈ T 0, h η = 0) ∧ ∀ q, ∀ η ∈ T q, Q η ∈ T q := by
  first | exact @_root_.GlobalTheory.CartierHomotopy.cartier_projector_homotopic | exact _root_.GlobalTheory.CartierHomotopy.cartier_projector_homotopic | (intros; apply _root_.GlobalTheory.CartierHomotopy.cartier_projector_homotopic <;> assumption)
end
