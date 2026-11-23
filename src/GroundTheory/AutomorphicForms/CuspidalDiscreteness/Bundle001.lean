module

public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsLintegralConstantTermL2SqLe
public import GroundTheory.AutomorphicForms.Bundle004
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.TorusDifference
import GroundTheory.GlobalFields.Adele.Topology
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne (K := K) (n := n)

variable (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

instance completeSpace_cuspidalL2 : CompleteSpace (cuspidalL2 μ) :=
  (isClosed_cuspidalL2 μ).completeSpace_coe

def cuspRep : UnitaryRep (normOneGL (K := K) (n := n)) (cuspidalL2 μ) :=
  (rightRegularRep Γ₁ μ).restrict (cuspidalL2 μ) (isInvariant_cuspidalL2 μ)

theorem subtypeL_comp_integrated (f : (normOneGL (K := K) (n := n)) →₁[μ] ℂ) :
    (cuspidalL2 μ).subtypeL ∘L (cuspRep μ).integrated μ f =
      (rightRegularRep Γ₁ μ).integrated μ f ∘L (cuspidalL2 μ).subtypeL :=
  UnitaryRep.comp_integrated_of_mem_intertwiners (cuspRep μ) μ
    (UnitaryRep.subtypeL_mem_intertwiners _ _ _) f

theorem isCompactOperator_of_forall_norm_rconv_le
    (f : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ) (B : ℝ)
    (hB : ∀ φ ∈ cuspidalL2 μ, ∀ x, ‖rconv Γ₁ μ f φ x‖ ≤ B * ‖φ‖) :
    IsCompactOperator ((cuspRep μ).integrated μ (UnitaryRep.ccToL1 μ f)) := by
  have := isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  let T := (cuspRep μ).integrated μ (UnitaryRep.ccToL1 μ f)
  let T' : cuspidalL2 μ →L[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ) := (cuspidalL2 μ).subtypeL ∘L T
  have hT' : T' = (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) ∘L
      (cuspidalL2 μ).subtypeL := subtypeL_comp_integrated μ _
  let e : RightCosetSpace Γ₁ → StrongDual ℂ (cuspidalL2 μ) := fun q =>
    (rconvCLM Γ₁ μ f (Quotient.out q)).comp (cuspidalL2 μ).subtypeL
  have he : ∀ q, ‖e q‖ ≤ max B 0 := by
    intro q
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun v => ?_
    change ‖rconv Γ₁ μ f (v : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (Quotient.out q)‖ ≤ _
    refine (hB v v.2 _).trans ?_
    rw [Submodule.coe_norm]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hout : ∀ (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (q : RightCosetSpace Γ₁),
      rconvQ Γ₁ μ f φ q = rconv Γ₁ μ f φ (Quotient.out q) := by
    intro φ q
    obtain ⟨a, rfl⟩ := mk_surjective Γ₁ q
    obtain ⟨γ, hγ⟩ := (mk_eq_mk_iff (Γ := Γ₁)).1 (Quotient.out_eq (mk Γ₁ a))
    rw [rconvQ_mk, ← hγ]
    exact (rconv_mul_left Γ₁ μ f φ γ.2 a).symm
  have hae : ∀ v, T' v =ᵐ[quotientMeasure Γ₁ μ] fun q => e q v := by
    intro v
    have h1 : T' v = (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f)
        (v : Lp ℂ 2 (quotientMeasure Γ₁ μ)) := by
      rw [hT']
      rfl
    rw [h1]
    filter_upwards [integrated_ae_eq_rconvQ Γ₁ μ f (v : Lp ℂ 2 (quotientMeasure Γ₁ μ))] with q hq
    exact hq.trans (hout _ q)
  have hHS : IsHilbertSchmidt T' := isHilbertSchmidt_of_ae_eq_dual T' e (max B 0) he hae
  have hc : IsCompactOperator T' := hHS.isCompactOperator
  have hmem : ∀ v, (fun v => T' v) v ∈ cuspidalL2 μ := fun v => (T v).2
  have hfun : (T : cuspidalL2 μ → cuspidalL2 μ) =
      Set.codRestrict (fun v => T' v) (cuspidalL2 μ) hmem :=
    funext fun v => Subtype.ext rfl
  rw [show ((cuspRep μ).integrated μ (UnitaryRep.ccToL1 μ f) : cuspidalL2 μ → cuspidalL2 μ) =
    (T : cuspidalL2 μ → cuspidalL2 μ) from rfl, hfun]
  exact hc.codRestrict hmem (isClosed_cuspidalL2 μ)

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end

section

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace CuspidalSpectrum

open Reduction AutomorphicForm RightCosetSpace

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne (K := K) (n := n)

def truncInf {r : ℕ} (s : UPos n r → 𝔸[K]) : UPos n r → 𝔸[K] := fun p => ((s p).1, 0)

def truncFin {r : ℕ} (s : UPos n r → 𝔸[K]) : UPos n r → 𝔸[K] := fun p => (0, (s p).2)

theorem truncInf_add_truncFin {r : ℕ} (s : UPos n r → 𝔸[K]) : truncInf s + truncFin s = s := by
  funext p
  change ((s p).1 + 0, 0 + (s p).2) = s p
  rw [add_zero, zero_add]
  rfl

variable (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

theorem rconv_mul_right (f : normOneGL (K := K) (n := n) → ℂ) (φ : Lp ℂ 2 (quotientMeasure Γ₁ μ))
    {g : normOneGL (K := K) (n := n)} (hf : ∀ w, f (g⁻¹ * w) = f w) (y : normOneGL (K := K) (n := n)) :
    rconv Γ₁ μ f φ (y * g) = rconv Γ₁ μ f φ y := by
  unfold rconv
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  change f ((y * g)⁻¹ * z) * _ = f (y⁻¹ * z) * _
  rw [mul_inv_rev, mul_assoc, hf]

theorem exists_isCompact_superset_scaledUnipFD (r : ℕ) {M : ℕ} (hM : 0 < M) :
    ∃ C : Set (UPos n r → 𝔸[K]), IsCompact C ∧ scaledUnipFD K n r M ⊆ C := by
  set Cf : Set (FiniteAdeleRing (𝓞 K) K) := (fun a => (M : FiniteAdeleRing (𝓞 K) K) * a) ''
    (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K))
  have hCf : IsCompact Cf := (GroundTheory.Global.isCompact_integralFiniteAdeles K).image (continuous_const_mul _)
  refine ⟨univ.pi fun _ => scaledInfSet K M ×ˢ Cf,
    isCompact_univ_pi fun _ => (isCompact_scaledInfSet M).prod hCf, fun X hX p _ => ?_⟩
  obtain ⟨a, ha, hXa⟩ := exists_finite_eq_natCast_mul hM hX p
  exact ⟨infinite_mem_scaledInfSet hM hX p, a, ha, hXa.symm⟩

theorem norm_rconv_le_of_altSum (f : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ)
    {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} (hφ : φ ∈ cuspidalL2 μ) {r : ℕ} (hr : 0 < r) (hrn : r < n)
    {M : ℕ} (hM : 0 < M) (x : normOneGL (K := K) (n := n)) (k : ℕ) {B : ℝ}
    (hB : ∀ y : Fin k → UPos n r → 𝔸[K], (∀ i, y i ∈ scaledUnipFD K n r M) →
      ‖altSum k (fun s => rconv Γ₁ μ f φ (unipOne (K := _) (n := _) r s * x)) y 0‖ ≤ B) :
    ‖rconv Γ₁ μ f φ x‖ ≤ B := by
  set H : (UPos n r → 𝔸[K]) → ℂ := fun s => rconv Γ₁ μ f φ (unipOne (K := _) (n := _) r s * x)
  have hHc : Continuous H :=
    (continuous_rconv Γ₁ μ f φ).comp ((continuous_unipOne r).mul continuous_const)
  have hper : ∀ ξ ∈ unipLattice K n r, ∀ s, H (ξ + s) = H s := by
    intro ξ hξ s
    simp only [H]
    rw [unipOne_add, mul_assoc, rconv_mul_left Γ₁ μ f φ (unipOne_mem_rationalGLOne r ⟨ξ, hξ⟩)]
  have hD := isAddFundamentalDomain_scaledUnipFD (K := K) (n := n) (r := r) hM
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_scaledUnipFD (K := K) (n := n) r hM
  have hint : ∀ t, IntegrableOn (fun y => H (t + y)) (scaledUnipFD K n r M) (unipMeasure K n r) :=
    fun t => ((hHc.comp (continuous_const.add continuous_id)).continuousOn.integrableOn_compact
      hC).mono_set hDC
  have hmean : ∫ y in scaledUnipFD K n r M, H y ∂unipMeasure K n r = 0 := by
    rw [hD.setIntegral_eq isAddFundamentalDomain_unipFundamentalDomain fun ξ s => hper ξ ξ.2 s]
    exact integral_rconv_unip_eq_zero μ f hφ hr hrn x
  have h0 := norm_le_of_forall_altSum_le hD (unipMeasure_scaledUnipFD hM) k H hper hint hmean B hB
  simpa [H, unipOne_zero] using h0

theorem norm_rconv_le_of_altSum_inf (f : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ)
    {φ : Lp ℂ 2 (quotientMeasure Γ₁ μ)} (hφ : φ ∈ cuspidalL2 μ) {r : ℕ} (hr : 0 < r) (hrn : r < n)
    {M : ℕ} (hM : 0 < M) (x : normOneGL (K := K) (n := n))
    (hfin : ∀ z : UPos n r → 𝔸[K], (∀ p, (z p).1 = 0) →
      (∀ p, ∃ a ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K,
        (z p).2 = (M : FiniteAdeleRing (𝓞 K) K) * a) →
      ∀ w, f ((x⁻¹ * unipOne (K := _) (n := _) r z * x)⁻¹ * w) = f w)
    (k : ℕ) {B : ℝ}
    (hB : ∀ y : Fin k → UPos n r → 𝔸[K], (∀ i, y i ∈ scaledUnipFD K n r M) →
      ‖altSum k (fun s => rconv Γ₁ μ f φ (unipOne (K := _) (n := _) r (truncInf s) * x)) y 0‖ ≤ B) :
    ‖rconv Γ₁ μ f φ x‖ ≤ B := by
  refine norm_rconv_le_of_altSum μ f hφ hr hrn hM x k fun y hy => ?_
  have key : ∀ ε : Fin k → Bool,
      rconv Γ₁ μ f φ (unipOne (K := _) (n := _) r (0 + altPoint y ε) * x) =
        rconv Γ₁ μ f φ (unipOne (K := _) (n := _) r (truncInf (0 + altPoint y ε)) * x) := by
    intro ε
    rw [zero_add]
    have hfinP := hfin (truncFin (altPoint y ε)) (fun p => rfl) fun p => by
      obtain ⟨a, ha, hPa⟩ := exists_finite_altPoint_eq_natCast_mul hM y hy ε p
      exact ⟨a, ha, hPa⟩
    have hP : unipOne (K := _) (n := _) r (altPoint y ε) * x = unipOne (K := _) (n := _) r (truncInf (altPoint y ε)) * x *
        (x⁻¹ * unipOne (K := _) (n := _) r (truncFin (altPoint y ε)) * x) := by
      simp only [mul_assoc, mul_inv_cancel_left]
      rw [← mul_assoc, ← unipOne_add, truncInf_add_truncFin]
    rw [hP]
    exact rconv_mul_right μ f φ hfinP _
  have heq : altSum k (fun s => rconv Γ₁ μ f φ (unipOne (K := _) (n := _) r s * x)) y 0 =
      altSum k (fun s => rconv Γ₁ μ f φ (unipOne (K := _) (n := _) r (truncInf s) * x)) y 0 := by
    rw [altSum_eq_sum, altSum_eq_sum]
    exact Finset.sum_congr rfl fun ε _ => congrArg (altSign ε • ·) (key ε)
  rw [heq]
  exact hB y hy

end CuspidalSpectrum

end

end GroundTheory.Automorphic
end
