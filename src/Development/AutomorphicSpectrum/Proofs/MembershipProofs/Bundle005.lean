module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle345
public import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle004
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

@[expose] public section

section

open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal

namespace GlobalTheory.CompanionTheory.WeilCoinv

theorem exists_dotProduct_ne_one {k : Type} [Field k] {κ : Type} [Fintype κ] {ψ : AddChar k ℂ} (hψ : ψ ≠ 1)
    {x : κ → k} (hx : x ≠ 0) : ∃ y : κ → k, ψ (x ⬝ᵥ y) ≠ 1 := by
  classical
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.mp hψ
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hi' : x i ≠ 0 := hi
  refine ⟨Pi.single i (t / x i), ?_⟩
  have hxt : x i * (t / x i) = t := by field_simp
  rw [dotProduct_single, hxt]
  exact ht

theorem exists_eq_mul_apply_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (κ : Type) [Fintype κ] (ψ : AddChar k ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ,
    (∀ y, ∀ φ ∈ SB (κ → k), l (schr ψ (0, y) φ) = l φ) → ∃ a : ℂ, ∀ φ ∈ SB (κ → k), l φ = a * φ 0 := by
  intro k _ _ _ _ _ κ _ ψ hψc hψ l hl
  classical
  haveI : NonarchimedeanAddGroup k := GlobalTheory.WeilM.nonarch_field k
  haveI : NonarchimedeanAddGroup (κ → k) := GlobalTheory.WeilM.nonarch_pi k κ
  have hψlc : IsLocallyConstant ψ := GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψc
  have hχ : ∀ y : κ → k, IsLocallyConstant (fun x : κ → k => ψ (x ⬝ᵥ y)) := fun y =>
    hψlc.comp_continuous (continuous_id.dotProduct continuous_const)
  have key : ∀ t : Finset (κ → k), ∀ φ ∈ SB (κ → k),
      (∀ x, φ x ≠ 0 → ∃ y ∈ t, ψ (x ⬝ᵥ y) ≠ 1) → l φ = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro φ _ h
      have hz : φ = 0 := funext fun x => by
        by_contra hx
        obtain ⟨y, hy, -⟩ := h x hx
        simp at hy
      rw [hz, map_zero]
    | @insert y t hyt ih =>
      intro φ hφ h
      obtain ⟨hφl, hφc⟩ := hφ
      obtain ⟨φ₁, hφ₁⟩ : ∃ f : (κ → k) → ℂ, f = fun x => if ψ (x ⬝ᵥ y) = 1 then φ x else 0 := ⟨_, rfl⟩
      obtain ⟨g, hg⟩ : ∃ f : (κ → k) → ℂ,
          f = fun x => if ψ (x ⬝ᵥ y) = 1 then 0 else φ x / (ψ (x ⬝ᵥ y) - 1) := ⟨_, rfl⟩
      have hφ₁SB : φ₁ ∈ SB (κ → k) := by
        refine ⟨?_, hφc.mono ?_⟩
        · rw [hφ₁]
          exact (hχ y).comp₂ hφl (fun a b => if a = 1 then b else 0)
        · intro x hx
          rw [Function.mem_support] at hx ⊢
          intro h0
          apply hx
          simp [hφ₁, h0]
      have hgSB : g ∈ SB (κ → k) := by
        refine ⟨?_, hφc.mono ?_⟩
        · rw [hg]
          exact (hχ y).comp₂ hφl (fun a b => if a = 1 then 0 else b / (a - 1))
        · intro x hx
          rw [Function.mem_support] at hx ⊢
          intro h0
          apply hx
          simp [hg, h0]
      have hsch : schr ψ ((0 : κ → k), y) g = fun x => ψ (x ⬝ᵥ y) * g x := by
        funext x
        simp [GlobalTheory.WeilM.schr]
      have hdiff : φ = φ₁ + (schr ψ ((0 : κ → k), y) g - g) := by
        rw [hsch]
        funext x
        simp only [Pi.add_apply, Pi.sub_apply, hφ₁, hg]
        split_ifs with h1
        · simp
        · have hne : ψ (x ⬝ᵥ y) - 1 ≠ 0 := sub_ne_zero.mpr h1
          rw [zero_add, ← sub_one_mul]
          field_simp
      rw [hdiff, map_add (f := _), map_sub, hl y g hgSB, sub_self, add_zero]
      refine ih φ₁ hφ₁SB ?_
      intro x hx
      have hx1 : ψ (x ⬝ᵥ y) = 1 := by
        by_contra hne
        apply hx
        simp [hφ₁, hne]
      have hx2 : φ x ≠ 0 := by
        intro h0
        apply hx
        simp [hφ₁, h0]
      obtain ⟨y', hy', hy'ne⟩ := h x hx2
      rcases Finset.mem_insert.mp hy' with rfl | hy't
      · exact absurd hx1 hy'ne
      · exact ⟨y', hy't, hy'ne⟩
  have vanish : ∀ φ ∈ SB (κ → k), φ 0 = 0 → l φ = 0 := by
    intro φ hφ h0
    obtain ⟨hφl, hφc⟩ := hφ
    have hsupp : IsClosed (Function.support φ) := (hφl.isOpen_fiber 0).isClosed_compl
    have hK : IsCompact (Function.support φ) := by
      have hc := hφc.isCompact
      rwa [tsupport, hsupp.closure_eq] at hc
    have hcov : Function.support φ ⊆ ⋃ y : κ → k, {x | ψ (x ⬝ᵥ y) ≠ 1} := by
      intro x hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        exact hx h0
      obtain ⟨y, hy⟩ := exists_dotProduct_ne_one hψ hx0
      exact Set.mem_iUnion.mpr ⟨y, hy⟩
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : κ → k => {x | ψ (x ⬝ᵥ y) ≠ 1})
      (fun y => ((hχ y).isClosed_fiber 1).isOpen_compl) hcov
    refine key t φ ⟨hφl, hφc⟩ ?_
    intro x hx
    have hxt := ht hx
    simp only [Set.mem_iUnion] at hxt
    obtain ⟨y, hy, hxy⟩ := hxt
    exact ⟨y, hy, hxy⟩
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : κ → k)
  obtain ⟨O, hO⟩ := NonarchimedeanAddGroup.is_nonarchimedean C hC0
  have hOc : IsCompact (O : Set (κ → k)) := hC.of_isClosed_subset O.isClosed hO
  have hO0 : (0 : κ → k) ∈ O := O.zero_mem
  obtain ⟨φ₀, hφ₀d⟩ : ∃ f : (κ → k) → ℂ, f = fun x => if x ∈ O then 1 else 0 := ⟨_, rfl⟩
  have hφ₀ : φ₀ ∈ SB (κ → k) := by
    refine ⟨?_, HasCompactSupport.intro' hOc O.isClosed fun x hx => ?_⟩
    · rw [IsLocallyConstant.iff_exists_open]
      intro x
      by_cases hx : x ∈ O
      · refine ⟨O, O.isOpen, hx, fun x' hx' => ?_⟩
        have hx'' : x' ∈ O := hx'
        simp [hφ₀d, hx, hx'']
      · refine ⟨(O : Set (κ → k))ᶜ, O.isClosed.isOpen_compl, hx, fun x' hx' => ?_⟩
        have hx'' : x' ∉ O := hx'
        simp [hφ₀d, hx, hx'']
    · have hx' : x ∉ O := hx
      simp [hφ₀d, hx']
  refine ⟨l φ₀, fun φ hφ => ?_⟩
  have h1 : φ - φ 0 • φ₀ ∈ SB (κ → k) := Submodule.sub_mem _ hφ (Submodule.smul_mem _ _ hφ₀)
  have h2 : (φ - φ 0 • φ₀) 0 = 0 := by simp [hφ₀d, hO0]
  have h3 := vanish _ h1 h2
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h3
  rw [h3, mul_comm]

end GlobalTheory.CompanionTheory.WeilCoinv
end

section

open GlobalTheory.CompanionTheory.VacLoc ValuativeRel GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.VacLoc.GoodInh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem goodChar_of_hasConductor (χ : AddChar k Circle) (c : kˣ) (hχ : HasConductor χ c) :
    GoodChar (Circle.coeHom.compAddChar χ) 𝒪[k] c := by
  have hcoe : ∀ z, (Circle.coeHom.compAddChar χ) z = 1 ↔ χ z = 1 := fun z => by
    show ((χ z : Circle) : ℂ) = 1 ↔ _
    exact Circle.coe_eq_one
  refine ⟨fun x => ?_, IsNonarchimedeanLocalField.isCompact_closedBall k 1, Valuation.isOpen_integer,
    fun x => ?_, fun U hU => ?_, fun x => ?_⟩
  · show ‖((χ x : Circle) : ℂ)‖ = 1
    exact Circle.norm_coe _
  · have key : (∀ y ∈ 𝒪[k], (Circle.coeHom.compAddChar χ) (x * y) = 1) ↔
        ∀ y, ValuativeRel.valuation k y ≤ ValuativeRel.valuation k x → χ y = 1 := by
      simp only [hcoe]
      constructor
      · intro H y hy
        by_cases hx : x = 0
        · have h0 : ValuativeRel.valuation k y = 0 := by
            rw [hx, map_zero] at hy
            exact le_antisymm hy zero_le'
          rw [(Valuation.zero_iff _).1 h0, AddChar.map_zero_eq_one]
        · have hmem : x⁻¹ * y ∈ 𝒪[k] := by
            rw [Valuation.mem_integer_iff, map_mul]
            calc ValuativeRel.valuation k x⁻¹ * ValuativeRel.valuation k y
                ≤ ValuativeRel.valuation k x⁻¹ * ValuativeRel.valuation k x :=
                  mul_le_mul_of_nonneg_left hy zero_le'
              _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hx, map_one]
          have h1 := H _ hmem
          rwa [mul_inv_cancel_left₀ hx] at h1
      · intro H y hy
        apply H
        rw [map_mul]
        calc ValuativeRel.valuation k x * ValuativeRel.valuation k y
            ≤ ValuativeRel.valuation k x * 1 :=
              mul_le_mul_of_nonneg_left ((Valuation.mem_integer_iff _ _).1 hy) zero_le'
          _ = ValuativeRel.valuation k x := mul_one _
    rw [key, hχ x, Valuation.mem_integer_iff, map_mul]
    constructor
    · intro hle
      calc ValuativeRel.valuation k ((c⁻¹ : kˣ) : k) * ValuativeRel.valuation k x
          ≤ ValuativeRel.valuation k ((c⁻¹ : kˣ) : k) * ValuativeRel.valuation k (c : k) :=
            mul_le_mul_of_nonneg_left hle zero_le'
        _ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    · intro hle
      calc ValuativeRel.valuation k x
          = ValuativeRel.valuation k ((c : k) * (((c⁻¹ : kˣ) : k) * x)) := by
            rw [← mul_assoc, Units.mul_inv, one_mul]
        _ = ValuativeRel.valuation k (c : k) *
            ValuativeRel.valuation k (((c⁻¹ : kˣ) : k) * x) := map_mul _ _ _
        _ ≤ ValuativeRel.valuation k (c : k) * 1 := by
            rw [map_mul]
            exact mul_le_mul_of_nonneg_left hle zero_le'
        _ = ValuativeRel.valuation k (c : k) := mul_one _
  · obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).1 hU
    obtain ⟨δ, hδ0, hδ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := k)
    obtain ⟨ϖ, hϖ⟩ := ValuativeRel.valuation_surjective (K := k) δ
    obtain ⟨z, hz⟩ := ValuativeRel.valuation_surjective (K := k)
      (γ : ValuativeRel.ValueGroupWithZero k)
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hz
      exact γ.ne_zero hz.symm
    have hϖ0 : ϖ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hϖ
      exact hδ0.ne hϖ
    refine ⟨Units.mk0 (z * ϖ) (mul_ne_zero hz0 hϖ0), fun y hy => hγ ?_⟩
    have hy' : ValuativeRel.valuation k y ≤ 1 := (Valuation.mem_integer_iff _ _).1 hy
    show ValuativeRel.valuation k (z * ϖ * y) < γ
    rw [map_mul, map_mul, hz, hϖ]
    calc (γ : ValuativeRel.ValueGroupWithZero k) * δ * ValuativeRel.valuation k y
        ≤ γ * δ * 1 := mul_le_mul_of_nonneg_left hy' zero_le'
      _ = γ * δ := mul_one _
      _ < γ * 1 := mul_lt_mul_of_pos_left hδ1 (zero_lt_iff.2 γ.ne_zero)
      _ = γ := mul_one _
  · by_cases hx : ValuativeRel.valuation k x ≤ 1
    · exact ⟨1, by simp, by simpa [Valuation.mem_integer_iff] using hx⟩
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      refine ⟨(Units.mk0 x hx0)⁻¹, ?_, ?_⟩
      · rw [Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, Units.val_mk0, Valuation.map_inv]
        exact (inv_le_one₀ ((Valuation.pos_iff _).2 hx0)).2 (le_of_lt (not_le.1 hx))
      · rw [Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hx0]
        exact one_mem _

theorem exists_goodChar :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      (∃ ψ : AddChar k ℂ, GoodChar ψ 𝒪[k] 1) ∧
      ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ x, ‖ψ x‖ = 1) → ψ ≠ 1 → ∃ u : kˣ, GoodChar ψ 𝒪[k] u := by
  intro k _ _ _ _
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  refine ⟨?_, fun ψ hψc hψn hψ1 => ?_⟩
  · obtain ⟨-, ⟨χ, -, -, hχ⟩, -⟩ := GlobalTheory.SplitWeil.conductor_exists k
    exact ⟨_, goodChar_of_hasConductor χ 1 hχ⟩
  · let χ : AddChar k Circle :=
      { toFun := fun x => ⟨ψ x, mem_sphere_zero_iff_norm.2 (hψn x)⟩
        map_zero_eq_one' := Circle.ext (by simp)
        map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul ψ a b) }
    have hχψ : Circle.coeHom.compAddChar χ = ψ := AddChar.ext _ _ fun x => rfl
    have hχc : Continuous χ := hψc.subtype_mk _
    have hχ1 : χ ≠ 1 := by
      intro h1
      apply hψ1
      rw [← hχψ, h1]
      exact AddChar.ext _ _ fun x => by simp
    obtain ⟨c, hc⟩ := GlobalTheory.SplitWeil.exists_hasConductor_of_continuous χ hχc hχ1
    exact ⟨c, hχψ ▸ goodChar_of_hasConductor χ c hc⟩

end GlobalTheory.CompanionTheory.VacLoc.GoodInh
end

section

noncomputable section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SchrSys

section Pair

variable {R : Type} [TopologicalSpace R] {κ : Type}

theorem integrable_pair (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ)
    (φ φ' : SB (κ → R)) :
    @Integrable ℂ _ _ _ (borel _) (fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ' : (κ → R) → ℂ) x) μ := by
  letI : MeasurableSpace (κ → R) := borel _
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  have h1 : Continuous (φ : (κ → R) → ℂ) := φ.2.1.continuous
  have h2 : Continuous (φ' : (κ → R) → ℂ) := φ'.2.1.continuous
  have h3 : HasCompactSupport (φ' : (κ → R) → ℂ) := φ'.2.2
  exact Continuous.integrable_of_hasCompactSupport ((Complex.continuous_conj.comp h1).mul h2)
    (HasCompactSupport.mul_left (f := fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x)) h3)

def pairForm (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ) :
    SB (κ → R) →ₗ⋆[ℂ] SB (κ → R) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun φ φ' => pair μ φ φ')
    (by
      intro f f' g
      simp only [pair, Submodule.coe_add, Pi.add_apply, map_add (f := _), add_mul]
      exact integral_add (integrable_pair μ hμ f g) (integrable_pair μ hμ f' g))
    (by
      intro a f g
      simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
      exact integral_const_mul _ _)
    (by
      intro f g g'
      simp only [pair, Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_pair μ hμ f g) (integrable_pair μ hμ f g'))
    (by
      intro a f g
      simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ a]
      exact integral_const_mul _ _)

theorem pair_conj (μ : @Measure (κ → R) (borel _)) (φ φ' : (κ → R) → ℂ) :
    (starRingEnd ℂ) (pair μ φ φ') = pair μ φ' φ := by
  letI : MeasurableSpace (κ → R) := borel _
  unfold pair
  rw [← integral_conj]
  congr 1
  funext x
  simp [mul_comm]

theorem pair_pos (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ)
    (hμ' : @Measure.IsOpenPosMeasure _ _ (borel _) μ) (φ : SB (κ → R)) (hφ : φ ≠ 0) : 0 < (pair μ φ φ).re := by
  letI : MeasurableSpace (κ → R) := borel _
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  have h1 : Continuous (φ : (κ → R) → ℂ) := φ.2.1.continuous
  have h3 : HasCompactSupport (φ : (κ → R) → ℂ) := φ.2.2
  have e : pair μ φ φ = ((∫ x, ‖(φ : (κ → R) → ℂ) x‖ * ‖(φ : (κ → R) → ℂ) x‖ ∂μ : ℝ) : ℂ) := by
    unfold pair
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    rw [Complex.conj_mul']
    simp [sq]
  rw [e, Complex.ofReal_re]
  obtain ⟨x, hx⟩ : ∃ x, (φ : (κ → R) → ℂ) x ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (Subtype.ext (funext h))
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x) (h1.norm.mul h1.norm)
    (HasCompactSupport.mul_left (f := fun x => ‖(φ : (κ → R) → ℂ) x‖) h3.norm)
    (fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
  have := norm_pos_iff.2 hx
  exact (mul_pos this this).ne'

end Pair

theorem exists_isModel : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) , GoodChar ψ O u → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ S : Sys W (SB (κ → R)), IsModel ψ d μ S := by
  intro R _ _ _ _ _ _ ψ O u W _ _ B κ _ d μ hψ hμ
  have law := fun w w' φ φ' => GlobalTheory.CompanionTheory.SchrLaw.schr_law ψ O u d μ w w' φ φ' hψ hμ
  have hc : @IsFiniteMeasureOnCompacts _ (borel _) _ μ := hμ.toIsFiniteMeasureOnCompacts
  have ho : @Measure.IsOpenPosMeasure _ _ (borel _) μ := hμ.toIsOpenPosMeasure
  let rho : W → SB (κ → R) →ₗ[ℂ] SB (κ → R) := fun w =>
    { toFun := fun φ => ⟨d.rho ψ w φ, (law w 0 φ 0).2.2.1 φ.2⟩
      map_add' := fun φ φ' => by
        apply Subtype.ext
        funext x
        simp [Darboux.rho, schr, mul_add]
      map_smul' := fun a φ => by
        apply Subtype.ext
        funext x
        simp [Darboux.rho, schr, mul_left_comm] }
  refine ⟨{ c := fun w w' => ψ (⅟(2 : R) * B w w')
            rho := rho
            B := pairForm μ hc
            c_add_left := ?_
            c_add_right := ?_
            c_self := ?_
            c_norm := fun _ _ => hψ.norm_one _
            rho_zero := fun φ => Subtype.ext (law 0 0 φ 0).2.1
            rho_rho := fun w w' φ => Subtype.ext (law w w' φ 0).1
            B_conj := fun φ φ' => pair_conj μ φ φ'
            B_pos := fun φ hφ => pair_pos μ hc ho φ hφ
            B_rho := fun w φ φ' => (law w 0 φ φ').2.2.2 },
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro x x' y
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [d.form, map_add (f := _), Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    ring
  · intro x y y'
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [d.form, map_add (f := _), Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    ring
  · intro x
    simp [d.form]

end GlobalTheory.CompanionTheory.SchrSys
end
end

section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

theorem _root_.GlobalTheory.T.indicator_in_schrodinger_span : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {κ : Type} [Fintype κ] (v : Rˣ), GoodChar ψ O u → (v : R) ∈ O → (Set.indicator {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} fun _ => (1 : ℂ)) ∈ Submodule.span ℂ {f : (κ → R) → ℂ | ∃ y : κ → R, f = schr ψ (0, y) (Set.indicator {x : κ → R | ∀ i, x i ∈ O} fun _ => (1 : ℂ))} := by
  first | exact @GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span | exact GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span | (intros; apply GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span <;> assumption)
end
