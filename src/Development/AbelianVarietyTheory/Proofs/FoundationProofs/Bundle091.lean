module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle059
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle061
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle005

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.hasQExpansionSumAbove_basic_properties : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), (∀ (C C' : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω), C ≤ C' → HS ε C φ h → HS ε C' φ h) ∧ (∀ (C : ℝ) (φ ψ : ℂ → ℂ) (h h' : HahnSeries ℚ Ω), HS ε C φ h → HS ε C ψ h' → HS ε C (φ + ψ) (h + h') ∧ HS ε C (φ - ψ) (h - h')) ∧ (∀ (C : ℝ) (r : ℚ) (c : Ω), HS ε C (fun z => ε c * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (HahnSeries.single r c)) ∧ (∀ (C : ℝ) (φ ψ : ℂ → ℂ) (h : HahnSeries ℚ Ω), (∀ z : ℂ, C < z.im → φ z = ψ z) → HS ε C φ h → HS ε C ψ h) := by
  first | exact @GlobalTheory.FNHS.hs_props | exact GlobalTheory.FNHS.hs_props | (intros; apply GlobalTheory.FNHS.hs_props <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.fixingSubgroupOfIntermediateField_properties : ∀ (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [Algebra.IsAlgebraic F Ω],
 (∀ g : Ω ≃ₐ[F] Ω, g ∈ GlobalTheory.K4.geo F K Ω ↔ ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x) ∧
 (∃ e : (Ω ≃ₐ[K] Ω) ≃* GlobalTheory.K4.geo F K Ω, (∀ g x, ((e g : GlobalTheory.K4.geo F K Ω) : Ω ≃ₐ[F] Ω) x = g x) ∧ Continuous e ∧ Continuous e.symm) ∧
 (Normal F K → (GlobalTheory.K4.geo F K Ω).Normal) ∧ (IsGalois K Ω → IsCompact (GlobalTheory.K4.geo F K Ω : Set (Ω ≃ₐ[F] Ω))) ∧
 (∀ (B : ValuationSubring Ω) (r g : Ω ≃ₐ[F] Ω), GlobalTheory.NeedB.Inert B r → GlobalTheory.NeedB.Inert (B.comap (g : Ω →+* Ω)) (g⁻¹ * r * g)) := by
  first | exact @GlobalTheory.K4.geo_facts | exact GlobalTheory.K4.geo_facts | (intros; apply GlobalTheory.K4.geo_facts <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

theorem _root_.GlobalTheory.T.admissible_of_sl2_action : ∀ (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), admitted c x → admitted c (act x γ) := by
  first | exact @GlobalTheory.Sieg.admissible_act_SL2 | exact GlobalTheory.Sieg.admissible_act_SL2 | (intros; apply GlobalTheory.Sieg.admissible_act_SL2 <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

theorem _root_.GlobalTheory.T.oddThetaProductSiegel_eq_zero_iff_lattice : ∀ (τ : ℍ) (z : ℂ), th z τ = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) * (τ : ℂ) + n := by
  first | exact @GlobalTheory.ThZero.th_eq_zero_iff | exact GlobalTheory.ThZero.th_eq_zero_iff | (intros; apply GlobalTheory.ThZero.th_eq_zero_iff <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

theorem _root_.GlobalTheory.T.smoothedThetaQProduct_eq_oddThetaProduct_quotient : ∀ (c : ℕ) (τ : ℍ) (z : ℂ), 1 < c → Nat.Coprime c 6 → th ((c : ℂ) * z) τ ≠ 0 → cth c (ee (τ : ℂ)) (ee z) = (-1) ^ (c * (c - 1) / 2) * th z τ ^ (c ^ 2) / th ((c : ℂ) * z) τ := by
  first | exact @GlobalTheory.Sieg.ThQuot.cth_eq_th_quot | exact GlobalTheory.Sieg.ThQuot.cth_eq_th_quot | (intros; apply GlobalTheory.Sieg.ThQuot.cth_eq_th_quot <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.hahnSeries_commonDenominator_eq_monomial_mul_powerSeries : ∀ (Ω : Type) [Field Ω] (h : HahnSeries ℚ Ω), Den h → h ≠ 0 → ∃ (N : ℕ) (n₀ : ℤ) (a : ℕ → Ω), 0 < N ∧ a 0 ≠ 0 ∧ (∀ k : ℕ, h.coeff (((n₀ + k : ℤ) : ℚ) / N) = a k) ∧ ∀ r : ℚ, (∀ k : ℕ, r ≠ ((n₀ + k : ℤ) : ℚ) / N) → h.coeff r = 0 := by
  first | exact @GlobalTheory.fnShape | exact GlobalTheory.fnShape | (intros; apply GlobalTheory.fnShape <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.isCuspExpansionAtInfinity_comp_rat_affine : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f f' : ℍ → ℂ) (l m : ℚ) (h h' : HahnSeries ℚ Ω), 0 < l → (∀ z ∈ Hs, up f' z = up f ((l : ℂ) * z + m)) → (∀ r : ℚ, ε (h'.coeff (r * l)) = Complex.exp (2 * Real.pi * Complex.I * ((r * m : ℚ) : ℂ)) * ε (h.coeff r)) → IsExp ε f h → IsExp ε f' h' := by
  first | exact @GlobalTheory.FN.isExp_comp_affine | exact GlobalTheory.FN.isExp_comp_affine | (intros; apply GlobalTheory.FN.isExp_comp_affine <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.qExpansionAllCoeffs_comp_upper_triangular : ∀ (E : Subring ℂ) (N a d : ℕ) (b : ℤ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) → 0 < N → 0 < a → 0 < d → QAll (· ∈ E) N f → QAll (· ∈ E) (N * d) fun τ => up f (((a : ℂ) * τ + b) / d) := by
  first | exact @GlobalTheory.FNQ.qAll_affine | exact GlobalTheory.FNQ.qAll_affine | (intros; apply GlobalTheory.FNQ.qAll_affine <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.hasCommonExponentDenominator_ring_operations : ∀ (Ω : Type) [Field Ω], (∀ h h' : HahnSeries ℚ Ω, Den h → Den h' → Den (h + h') ∧ Den (h - h') ∧ Den (h * h')) ∧ ∀ (r : ℚ) (c : Ω), Den (HahnSeries.single r c : HahnSeries ℚ Ω) := by
  first | exact @GlobalTheory.FN.den_ring | exact GlobalTheory.FN.den_ring | (intros; apply GlobalTheory.FN.den_ring <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FNExpJ

variable {Ω : Type} [Field Ω]

theorem ofPowerSeries_coeff_of_ne (P : PowerSeries Ω) {r : ℚ} (hr : ∀ n : ℕ, (n : ℚ) ≠ r) :
    (HahnSeries.ofPowerSeries ℚ Ω P).coeff r = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_image_support
  rintro ⟨n, -, hn⟩
  exact hr n (by simpa using hn)

theorem expansion_j : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω,
    IsExp ε jT h ∧ h.coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → h.coeff r = 0) ∧
      ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  intro Ω _ ε
  obtain ⟨c, hc⟩ := GlobalTheory.exists_hasSum_modularJ_sub_inv
  set P : PowerSeries Ω := PowerSeries.mk fun n => (c n : Ω) with hPdef
  have hP : ∀ n : ℕ, (HahnSeries.ofPowerSeries ℚ Ω P).coeff (n : ℚ) = (c n : Ω) := fun n => by
    rw [HahnSeries.ofPowerSeries_apply_coeff, hPdef, PowerSeries.coeff_mk]
  have h0 : ∀ r : ℚ, (∀ n : ℕ, (n : ℚ) ≠ r) → (HahnSeries.ofPowerSeries ℚ Ω P).coeff r = 0 :=
    fun r hr => ofPowerSeries_coeff_of_ne P hr
  have hneg : ∀ r : ℚ, r < 0 → ∀ n : ℕ, (n : ℚ) ≠ r := fun r hr n hn => by
    have : (0 : ℚ) ≤ n := n.cast_nonneg
    linarith
  refine ⟨HahnSeries.single (-1 : ℚ) (1 : Ω) + HahnSeries.ofPowerSeries ℚ Ω P,
    ⟨?_, 0, ?_⟩, ?_, ?_, ?_⟩
  · refine ⟨1, one_pos, fun r hr => ?_⟩
    by_cases h1 : r = -1
    · exact ⟨-1, by simp [h1]⟩
    by_cases h2 : ∃ n : ℕ, (n : ℚ) = r
    · obtain ⟨n, rfl⟩ := h2
      exact ⟨n, by simp⟩
    · push_neg at h2
      exfalso
      apply hr
      rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, h0 r h2, add_zero]
  · intro z hz
    set τ : ℍ := ⟨z, hz⟩ with hτ
    have hup : up jT z = GlobalTheory.modularJ τ := by
      simp only [up, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      rfl
    have hq : Function.Periodic.qParam 1 (τ : ℂ) = Complex.exp (2 * Real.pi * Complex.I * z) := by
      simp [Function.Periodic.qParam, hτ]
    have H1 : HasSum (fun r : ℚ => ε ((HahnSeries.single (-1 : ℚ) (1 : Ω)).coeff r) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (Function.Periodic.qParam 1 (τ : ℂ))⁻¹ := by
      have := hasSum_single (f := fun r : ℚ => ε ((HahnSeries.single (-1 : ℚ) (1 : Ω)).coeff r) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (-1) (fun r hr => by
          simp [HahnSeries.coeff_single_of_ne hr])
      convert this using 1
      rw [hq, HahnSeries.coeff_single_same, map_one, one_mul, ← Complex.exp_neg]
      congr 1
      push_cast
      ring
    have H2 : HasSum (fun r : ℚ => ε ((HahnSeries.ofPowerSeries ℚ Ω P).coeff r) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z))
        (GlobalTheory.modularJ τ - (Function.Periodic.qParam 1 (τ : ℂ))⁻¹) := by
      refine (Function.Injective.hasSum_iff (g := fun n : ℕ => (n : ℚ)) Nat.cast_injective
        (fun r hr => ?_)).mp ?_
      · rw [h0 r (fun n hn => hr ⟨n, hn⟩), map_zero, zero_mul]
      · convert hc τ using 1
        funext n
        simp only [Function.comp_apply, hP, map_intCast, hq, ← Complex.exp_nat_mul]
        congr 2
        push_cast
        ring
    convert H1.add H2 using 1
    · funext r
      rw [HahnSeries.coeff_add, map_add (f := _), add_mul]
    · rw [hup]
      ring
  · rw [HahnSeries.coeff_add, HahnSeries.coeff_single_same, h0 _ (hneg _ (by norm_num)), add_zero]
  · intro r hr
    rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne hr.ne, h0 r (hneg r (by linarith)),
      add_zero]
  · intro r
    by_cases h1 : r = -1
    · subst h1
      refine ⟨1, ?_⟩
      rw [HahnSeries.coeff_add, HahnSeries.coeff_single_same, h0 _ (hneg _ (by norm_num))]
      simp
    by_cases h2 : ∃ n : ℕ, (n : ℚ) = r
    · obtain ⟨n, rfl⟩ := h2
      refine ⟨c n, ?_⟩
      rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, hP, zero_add]
    · push_neg at h2
      exact ⟨0, by rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, h0 r h2]; simp⟩

end GlobalTheory.FNExpJ
end
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

theorem _root_.GlobalTheory.T.modular_law_of_s_and_t : ∀ (P : (Fin 2 → ℚ) → Prop) (f : (Fin 2 → ℚ) → ℍ → ℂ), (∀ x γ, P x → P (act x γ)) → (∀ x τ, P x → f x (ModularGroup.S • τ) = f (act x ModularGroup.S) τ) → (∀ x τ, P x → f x (ModularGroup.T • τ) = f (act x ModularGroup.T) τ) → ∀ (γ : SL(2, ℤ)) x τ, P x → f x (γ • τ) = f (act x γ) τ := by
  first | exact @GlobalTheory.Sieg.modular_law_of_generators | exact GlobalTheory.Sieg.modular_law_of_generators | (intros; apply GlobalTheory.Sieg.modular_law_of_generators <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

theorem _root_.GlobalTheory.T.smoothedSiegelUnit_modularGroupT_smul : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), sg c x (ModularGroup.T • τ) = sg c (act x ModularGroup.T) τ := by
  first | exact @GlobalTheory.Sieg.sg_T_smul | exact GlobalTheory.Sieg.sg_T_smul | (intros; apply GlobalTheory.Sieg.sg_T_smul <;> assumption)
end
