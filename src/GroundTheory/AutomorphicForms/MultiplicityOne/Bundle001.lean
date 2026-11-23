module

public import GroundTheory.AutomorphicForms.Bundle012
public import GroundTheory.AutomorphicForms.GL2.GJGlobalHaar
import GroundTheory.GlobalFields.Adele.Topology
public import GroundTheory.AutomorphicForms.FourierWhittaker
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Measure Topology Filter Set IsDedekindDomain NumberField

namespace GroundTheory.Automorphic

namespace Whittaker

noncomputable section

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)

theorem isMulRightInvariant_finite (μ : Measure (AdelicGLn.FiniteAdelicGL K n)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (AdelicGLn.FiniteAdelicGL K 0) :=
      ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    refine ⟨fun g => ?_⟩
    rw [Subsingleton.elim g 1]
    simp only [mul_one]
    exact Measure.map_id
  let _ : MeasurableSpace (AdelicGLn.InfiniteAdelicGL K n) := _root_.borel _
  have : BorelSpace (AdelicGLn.InfiniteAdelicGL K n) := ⟨rfl⟩
  set μi : Measure (AdelicGLn.InfiniteAdelicGL K n) := Measure.haar
  set P := μi.prod μ
  set e := AdelicGLn.prodEquiv K n
  set ν : Measure (AdelicGLn.AdelicGL K n) := Measure.haar
  have hν := GJGlobal.isMulRightInvariant_haar ν hn
  have he : Measurable e := e.continuous.measurable
  have : (ν.map e).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map ν e.toMulEquiv e.continuous e.symm.continuous
  have hν' : ∀ p, (ν.map e).map (· * p) = ν.map e := by
    intro p
    have hcomp : (· * p) ∘ e = e ∘ (· * e.symm p) := by
      funext x
      simp only [Function.comp_apply, map_mul, ContinuousMulEquiv.apply_symm_apply]
    rw [Measure.map_map (measurable_mul_const p) he, hcomp,
      ← Measure.map_map he (measurable_mul_const _), map_mul_right_eq_self]

  set_option synthInstance.maxHeartbeats 400000 in
  set c := haarScalarFactor (ν.map e) P
  have hc : ν.map e = c • P := isMulLeftInvariant_eq_smul (ν.map e) P
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    have hne := isOpen_univ.measure_ne_zero (ν.map e) univ_nonempty
    rw [hc] at hne
    exact hne rfl
  have hP : ∀ p, P.map (· * p) = P := by
    intro p
    have h1 : P = c⁻¹ • ν.map e := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h1, Measure.map_smul _ (measurable_mul_const p).aemeasurable, hν']
  refine ⟨fun g => ?_⟩
  have hprod : P.map (· * ((1 : AdelicGLn.InfiniteAdelicGL K n), g)) = μi.prod (μ.map (· * g)) := by
    have hf : (· * ((1 : AdelicGLn.InfiniteAdelicGL K n), g)) = Prod.map id (· * g) := by
      funext p
      exact Prod.ext (mul_one p.1) rfl
    rw [hf, ← Measure.map_prod_map μi μ measurable_id (measurable_mul_const g), Measure.map_id]
  rw [hP] at hprod
  obtain ⟨A, hAc, hA⟩ := exists_compact_mem_nhds (1 : AdelicGLn.InfiniteAdelicGL K n)
  have hA0 : μi A ≠ 0 := (measure_pos_of_mem_nhds μi hA).ne'
  have hAt : μi A ≠ ⊤ := hAc.measure_lt_top.ne
  refine Measure.ext fun B hB => ?_
  have h1 := congrArg (fun m : Measure _ => m (A ×ˢ B)) hprod
  simp only [P, Measure.prod_prod] at h1
  exact ((ENNReal.mul_right_inj hA0 hAt).1 h1).symm

end

end Whittaker

end GroundTheory.Automorphic
end

section

open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open AutomorphicForm FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem partialCoeff_succ_eq_zero {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hc : Continuous ϕ)
    (hl : IsLeftInvariant ϕ) (hcusp : IsCuspidal ϕ) {V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n)}
    (hV : ∀ g, ∀ v ∈ V, ϕ (g * finEmb K n v) = ϕ g) {k : ℕ} (hk0 : 0 < k) (hk : k < n)
    (h0 : ∀ g, partialCoeff ϕ k g = 0) (g : AdelicGLn.AdelicGL K n) :
    partialCoeff ϕ (k + 1) g = 0 := by
  classical
  obtain ⟨δ, hδ, hδV⟩ := exists_integer_colGL_mem (n := n) k V (AdelicGLn.prodEquiv K n g).2
  have hδK : (algebraMap (𝓞 K) K δ) ≠ 0 := by
    simpa using (RingOfIntegers.coe_ne_zero_iff).2 hδ
  set u : Kˣ := Units.mk0 _ hδK
  set D := AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹))
  have hconj : ∀ w : Fin k → 𝔸[K], colGL k w * D =
      D * colGL k (fun i => algebraMap K 𝔸[K] u * w i) := by
    intro w
    simp only [D]
    rw [diagonal_blockGL, colGL_mul_blockGL hk, mulVec_map_inv, ← map_inv, inv_inv, coe_scalarGL,
      matVec_scalar]
  have hfin : ∀ (x : Fin k → 𝔸[K]) (z : Fin k → FiniteAdeleRing (𝓞 K) K),
      (∀ i, z i ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 K) K) →
        partialCoeff ϕ (k + 1) (colGL k (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) * (D * g)) =
          partialCoeff ϕ (k + 1) (colGL k x * (D * g)) := by
    intro x z hz
    have e1 : (fun i => algebraMap K 𝔸[K] (u : K) * GroundTheory.Global.finiteAdeleInr (z i)) =
        fun i => GroundTheory.Global.finiteAdeleInr (algebraMap K (FiniteAdeleRing (𝓞 K) K)
          (algebraMap (𝓞 K) K δ) * z i) := by
      funext i; rw [GroundTheory.Global.algebraMap_mul_finiteAdeleInr]; rfl
    rw [colGL_add, mul_assoc (colGL k x),
      ← mul_assoc (colGL k fun i => GroundTheory.Global.finiteAdeleInr (z i)), hconj, e1,
      colGL_finiteAdeleInr, mul_assoc D, finEmb_mul_eq, ← mul_assoc,
      ← mul_assoc, partialCoeff_mul_finEmb hV _ _ (hδV z hz), mul_assoc]
  set F : (Fin k → 𝔸[K]) → ℂ := fun x => partialCoeff ϕ (k + 1) (colGL k x * (D * g))
  have hFc : Continuous F :=
    (continuous_partialCoeff hc _).comp ((continuous_colGL k).mul continuous_const)
  have hper : ∀ ξ ∈ vecLattice K (Fin k), ∀ x, F (ξ + x) = F x := by
    intro ξ hξ x
    obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
    simp only [F]
    rw [colGL_add, mul_assoc, ← diagonal_colGL, partialCoeff_succ_diagonal_colGL hl hk]
  have hip : IsIntegralPeriodic F := ⟨hFc, hper, fun x z hz => hfin x z hz⟩
  have hcoeff : ∀ ξ : Fin k → K, vecCoeff F ξ = 0 := by
    intro ξ
    by_cases hξ : ξ = 0
    · rw [hξ]
      exact vecCoeff_zero_of_isCuspidal hc hl hcusp hk0 hk (D * g)
    · have h1 := partialCoeff_diagonal_blockGL_eq_vecCoeff hl hk (rowCompletion ξ) (D * g)
      rw [vecMul_rowCompletion hξ] at h1
      rw [← h1]
      exact h0 _
  have hsum : Summable (vecCoeff F) := by
    have : vecCoeff F = 0 := funext hcoeff
    rw [this]
    exact summable_zero
  have H := hip.hasSum_vecCoeff hsum 0
  simp only [hcoeff, zero_mul] at H
  have hF0 : F 0 = 0 := (hasSum_zero.unique H).symm
  have hDg : partialCoeff ϕ (k + 1) (D * g) = 0 := by
    simpa [F, colGL_zero] using hF0
  rw [← partialCoeff_succ_diagonal_blockGL hl hk (scalarGL k u⁻¹) g]
  exact hDg

theorem eq_zero_of_whittaker_eq_zero {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hc : Continuous ϕ)
    (hl : IsLeftInvariant ϕ) (hcusp : IsCuspidal ϕ)
    (hV : ∃ V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n),
      ∀ g, ∀ v ∈ V, ϕ (g * finEmb K n v) = ϕ g)
    (hW : ∀ g, whittaker ϕ g = 0) : ϕ = 0 := by
  obtain ⟨V, hV⟩ := hV
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    funext g
    rw [← partialCoeff_self ϕ, ← whittaker_eq_partialCoeff_zero hc g]
    exact hW g
  · have key : ∀ k, 0 < k → k ≤ n → ∀ g, partialCoeff ϕ k g = 0 := by
      intro k
      induction k with
      | zero => intro h; exact absurd h (lt_irrefl 0)
      | succ m ih =>
        intro _ hm g
        rcases Nat.eq_zero_or_pos m with rfl | hm0
        · rw [← whittaker_eq_partialCoeff hc hn g]
          exact hW g
        · exact partialCoeff_succ_eq_zero hc hl hcusp hV hm0 (by omega) (ih hm0 (by omega)) g
    funext g
    rw [← partialCoeff_self ϕ]
    exact key n hn le_rfl g

end MultiplicityOne

end

end GroundTheory.Automorphic
end
