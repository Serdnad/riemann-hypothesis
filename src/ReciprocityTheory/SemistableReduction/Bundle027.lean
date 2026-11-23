module

public import ReciprocityTheory.SemistableReduction.Bundle001
public import ReciprocityTheory.SemistableReduction.Bundle013
public import ReciprocityTheory.SemistableReduction.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.SemistableReduction.Bundle014
public import ReciprocityTheory.SemistableReduction.Bundle019
public import ReciprocityTheory.SemistableReduction.Bundle020
public import ReciprocityTheory.SemistableReduction.Bundle026
public import ReciprocityTheory.SemistableReduction.SjHolds
public import ReciprocityTheory.SemistableReduction.Bundle024
public import ReciprocityTheory.SemistableReduction.Bundle021

@[expose] public section

section

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

theorem sphereLinLog : SphereLinLogStatement := sjCore_holds

theorem sj : SJStatement := sj_holds sphereLinLog

theorem sphereLogIntegrable : SphereLogIntegrableStatement := sphereLogIntegrable_holds sj

theorem gauss_height_additivity : HeightAdditiveStatement := gauss_height_add_of_sphere sphereLogIntegrable

theorem sphere_height_lower_bound : HeightLowerBoundStatement := heightLowerBound_of_sj_of_sphereLogIntegrable sj sphereLogIntegrable

theorem torusMeanBasic : TorusMeanBasicStatement := torusMean_holds.1

theorem torusCoeff : TorusCoeffStatement := torusMean_holds.2

theorem torusLex : TorusLexStatement := (torusLex_holds torusMeanBasic torusCoeff).1

theorem torus_l2_cauchy_inequality : TorusL2Cauchy := (torusLex_holds torusMeanBasic torusCoeff).2

theorem gram : GramStatement := gram_holds torusMeanBasic torusLex torus_l2_cauchy_inequality

theorem sphereLeTorus : SphereLeTorusStatement := sphereTorus_holds sphereLogIntegrable torusMeanBasic

end ReciprocityTheory.MultiplicativeHeights.Closed
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField
open scoped ComplexOrder

theorem boundedBall_holds : BoundedBallStatement := by
  intro r p H s hH hJ hs0 hs1 hP u
  have hHh : Hᴴ = H := hH.isHermitian
  have hsurj := sb_setup hH hJ hP
  have hTT : ∀ v, signMat p r *ᵥ (H *ᵥ (signMat p r *ᵥ (H *ᵥ v))) = v := fun v => by
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc H, hJ, sb_J_mul_J, one_mulVec]
  have hHx : ∀ x, signMat p r *ᵥ (H *ᵥ x) = x → H *ᵥ x = signMat p r *ᵥ x := fun x hx => by
    calc H *ᵥ x = signMat p r *ᵥ (signMat p r *ᵥ (H *ᵥ x)) := by
          rw [mulVec_mulVec, sb_J_mul_J, one_mulVec]
      _ = _ := by rw [hx]
  have hHy : ∀ y, signMat p r *ᵥ (H *ᵥ y) = -y → H *ᵥ y = -(signMat p r *ᵥ y) := fun y hy => by
    calc H *ᵥ y = signMat p r *ᵥ (signMat p r *ᵥ (H *ᵥ y)) := by
          rw [mulVec_mulVec, sb_J_mul_J, one_mulVec]
      _ = _ := by rw [hy, mulVec_neg]
  have horth : ∀ x y, signMat p r *ᵥ (H *ᵥ x) = x → signMat p r *ᵥ (H *ᵥ y) = -y →
      star x ⬝ᵥ (signMat p r *ᵥ y) = 0 := by
    intro x y hx hy
    have e := sb_herm_swap hHh x y
    rw [hHy y hy, hHx x hx, dotProduct_neg, ← sb_herm_swap (sb_J_herm p r)] at e
    linear_combination (-1 / 2 : ℂ) * e
  have horth' : ∀ x y, signMat p r *ᵥ (H *ᵥ x) = x → signMat p r *ᵥ (H *ᵥ y) = -y →
      star y ⬝ᵥ (signMat p r *ᵥ x) = 0 := by
    intro x y hx hy
    have e := sb_herm_swap hHh y x
    rw [hHx x hx, hHy y hy, star_neg, neg_dotProduct, ← sb_herm_swap (sb_J_herm p r)] at e
    linear_combination (1 / 2 : ℂ) * e
  have hNprop : ∀ y, signMat p r *ᵥ (H *ᵥ y) = -y → posSq p y ≤ s ^ 2 * negSq p y := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hsurj y
    have o := horth x y hx hy
    rw [sb_dot_J, sub_eq_zero, hxy] at o
    have hA : posSq p y = (star (sbDn p r *ᵥ x) ⬝ᵥ (sbDn p r *ᵥ y)).re := by
      rw [← o, sb_re_star_dot, sb_posSq_eq]
    have cs := sb_cs (sbDn p r *ᵥ x) (sbDn p r *ᵥ y)
    rw [← hA, ← sb_negSq_eq, ← sb_negSq_eq] at cs
    have hx' := hP x hx
    have hpx : posSq p x = posSq p y := by rw [sb_posSq_eq, sb_posSq_eq, hxy]
    have hA0 : 0 ≤ posSq p y := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
    have hD0 : 0 ≤ negSq p y := by rw [sb_negSq_eq]; exact sb_normSq_nonneg _
    rw [hpx] at hx'
    rcases hA0.eq_or_lt with h | h
    · rw [← h]; positivity
    · have h2 := mul_le_mul_of_nonneg_right hx' hD0
      exact le_of_mul_le_mul_left (by nlinarith : posSq p y * posSq p y ≤
        posSq p y * (s ^ 2 * negSq p y)) h
  have hdec : ∃ x y, signMat p r *ᵥ (H *ᵥ x) = x ∧ signMat p r *ᵥ (H *ᵥ y) = -y ∧ x + y = u :=
    ⟨(1 / 2 : ℂ) • (u + signMat p r *ᵥ (H *ᵥ u)), (1 / 2 : ℂ) • (u - signMat p r *ᵥ (H *ᵥ u)),
      by rw [mulVec_smul, mulVec_smul, mulVec_add, mulVec_add, hTT, add_comm],
      by rw [mulVec_smul, mulVec_smul, mulVec_sub, mulVec_sub, hTT, ← smul_neg, neg_sub],
      by ext k; simp; ring⟩
  obtain ⟨x, y, hx, hy, rfl⟩ := hdec
  have hPx := hP x hx
  have hPy := hNprop y hy
  set t := (star (sbDp p r *ᵥ x) ⬝ᵥ (sbDp p r *ᵥ y)).re with htdef
  have ht2 : (star (sbDn p r *ᵥ x) ⬝ᵥ (sbDn p r *ᵥ y)).re = t := by
    have o := horth x y hx hy
    rw [sb_dot_J, sub_eq_zero] at o
    rw [htdef, o]
  have hq_eq : hq H (x + y) = posSq p x - negSq p x - posSq p y + negSq p y := by
    have e1 := sb_re_dot_J p x
    have e2 := sb_re_dot_J p y
    rw [hq, mulVec_add, hHx x hx, hHy y hy, star_add]
    simp only [add_dotProduct, dotProduct_add, dotProduct_neg]
    rw [horth x y hx hy, horth' x y hx hy]
    simp only [Complex.add_re, Complex.neg_re, Complex.zero_re]
    linarith
  have hn_eq : normSq (x + y) =
      posSq p x + negSq p x + posSq p y + negSq p y + 4 * t := by
    have a3 : (star x ⬝ᵥ y).re = 2 * t := by rw [sb_dot_split p, Complex.add_re, ht2]; ring
    have a4 : (star y ⬝ᵥ x).re = 2 * t := by rw [sb_re_dot_comm, a3]
    rw [← sb_re_star_dot, star_add]
    simp only [add_dotProduct, dotProduct_add, Complex.add_re]
    rw [a3, a4, sb_re_star_dot, sb_re_star_dot, sb_normSq_split p x, sb_normSq_split p y]
    ring
  have hA0 : 0 ≤ posSq p x := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
  have hB0 : 0 ≤ negSq p x := by rw [sb_negSq_eq]; exact sb_normSq_nonneg _
  have hC0 : 0 ≤ posSq p y := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
  have hD0 : 0 ≤ negSq p y := by rw [sb_negSq_eq]; exact sb_normSq_nonneg _
  have hts1 : t ^ 2 ≤ posSq p x * posSq p y := by
    rw [sb_posSq_eq, sb_posSq_eq]; exact sb_cs _ _
  have hts2 : t ^ 2 ≤ negSq p x * negSq p y := by
    rw [← ht2, sb_negSq_eq, sb_negSq_eq]; exact sb_cs _ _
  have hsq : ∀ z : ℝ, 0 ≤ z → Real.sqrt (s ^ 2 * z) = s * Real.sqrt z := fun z hz => by
    rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs0]
  have hb : Real.sqrt (negSq p x) ≤ s * Real.sqrt (posSq p x) :=
    (Real.sqrt_le_sqrt hPx).trans (le_of_eq (hsq _ hA0))
  have hc : Real.sqrt (posSq p y) ≤ s * Real.sqrt (negSq p y) :=
    (Real.sqrt_le_sqrt hPy).trans (le_of_eq (hsq _ hD0))
  have h1 : |t| ≤ Real.sqrt (posSq p x) * Real.sqrt (posSq p y) := by
    rw [← Real.sqrt_mul hA0]; exact Real.abs_le_sqrt hts1
  have h2 : |t| ≤ Real.sqrt (negSq p x) * Real.sqrt (negSq p y) := by
    rw [← Real.sqrt_mul hB0]; exact Real.abs_le_sqrt hts2
  obtain ⟨hU, hL⟩ := sb_real_bounds _ _ _ _ s t (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hs0 hs1 hb hc h1 h2
  rw [Real.sq_sqrt hA0, Real.sq_sqrt hB0, Real.sq_sqrt hC0, Real.sq_sqrt hD0] at hU hL
  have h1s : 0 < 1 - s := by linarith
  rw [hq_eq, hn_eq]
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ h1s]; nlinarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ h1s]; nlinarith

end ReciprocityTheory.MultiplicativeHeights
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem isIntegralElt_add {K : Type} [Field K] [NumberField K] {x y : K} (hx : IsIntegralElt x)
    (hy : IsIntegralElt y) : IsIntegralElt (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by push_cast; rfl⟩

theorem isIntegralElt_c {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) {x : K}
    (hx : IsIntegralElt x) : IsIntegralElt (S.c x) := by
  obtain ⟨z, rfl⟩ := hx
  exact ⟨RingOfIntegers.mapRingHom S.c z, rfl⟩

theorem norm_c {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (z : K) :
    Algebra.norm ℚ (S.c z) = Algebra.norm ℚ z := by
  have hs : Function.Surjective S.c := fun x => ⟨S.c x, S.c_invol x⟩
  let e : K ≃+* K := RingEquiv.ofBijective S.c ⟨S.c.injective, hs⟩
  let e' : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := e) (fun q => by simp [e])
  exact Algebra.norm_eq_of_algEquiv e' z

def projLt (K : Type) [Field K] [NumberField K] (r e : ℕ) : (Fin r → K) →ₗ[𝓞 K] (Fin r → K) where
  toFun x i := if (i : ℕ) < e then x i else 0
  map_add' x y := by
    funext i
    by_cases h : (i : ℕ) < e <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : (i : ℕ) < e <;> simp [h]

theorem spanIdx_pair {K : Type} [Field K] [NumberField K] {r : ℕ} (j p : Fin r)
    (hjp : (j : ℕ) < p) (Gj Gp : Submodule (𝓞 K) (Fin r → K)) (hj : ∀ x ∈ Gj, IsAt j x)
    (hp : ∀ x ∈ Gp, IsAt p x) (x0 y : Fin r → K) (hx0 : x0 ∈ Gj) (hy : y ∈ Gp) :
    spanIdx (Gj ⊔ Gp) ![x0, y] = spanIdx Gj ![x0] * spanIdx Gp ![y] := by
  unfold spanIdx
  have hspan : Submodule.span (𝓞 K) (Set.range ![x0, y]) =
      Submodule.span (𝓞 K) {x0} ⊔ Submodule.span (𝓞 K) {y} := by
    rw [Matrix.range_cons_cons_empty, Submodule.span_insert]
  have h1 : Set.range ![x0] = {x0} := Matrix.range_cons_empty _ _
  have h2 : Set.range ![y] = {y} := Matrix.range_cons_empty _ _
  rw [hspan, h1, h2, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup]
  set X0 := (Submodule.span (𝓞 K) {x0}).toAddSubgroup
  set Y := (Submodule.span (𝓞 K) {y}).toAddSubgroup
  have hX0 : X0 ≤ Gj.toAddSubgroup := by
    show Submodule.span (𝓞 K) {x0} ≤ Gj
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hx0
  have hY : Y ≤ Gp.toAddSubgroup := by
    show Submodule.span (𝓞 K) {y} ≤ Gp
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hy
  have key := AddSubgroup.relIndex_mul_relIndex _ _ _ (sup_le_sup_left hY X0)
    (sup_le_sup_right hX0 Gp.toAddSubgroup)
  rw [← key, mul_comm (X0.relIndex _)]
  congr 1
  · refine relIndex_sup_proj (projGe K r p).toAddMonoidHom X0 Y Gp.toAddSubgroup hY ?_ ?_
    · intro a ha
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 ha
      show projGe K r p (t • x0) = 0
      rw [map_smul]
      have : projGe K r p x0 = 0 := by
        funext i
        show (if (p : ℕ) ≤ i then x0 i else 0) = 0
        split_ifs with h
        · exact hj x0 hx0 i (fun hi => by rw [hi] at h; omega)
        · rfl
      rw [this, smul_zero]
    · intro x hx
      show projGe K r p x = x
      funext i
      show (if (p : ℕ) ≤ i then x i else 0) = x i
      split_ifs with h
      · rfl
      · exact (hp x hx i (fun hi => by rw [hi] at h; omega)).symm
  · rw [sup_comm X0, sup_comm Gj.toAddSubgroup]
    refine relIndex_sup_proj (projLt K r p).toAddMonoidHom Gp.toAddSubgroup X0 Gj.toAddSubgroup
      hX0 ?_ ?_
    · intro x hx
      show projLt K r p x = 0
      funext i
      show (if (i : ℕ) < p then x i else 0) = 0
      split_ifs with h
      · exact hp x hx i (fun hi => by rw [hi] at h; omega)
      · rfl
    · intro x hx
      show projLt K r p x = x
      funext i
      show (if (i : ℕ) < p then x i else 0) = x i
      split_ifs with h
      · rfl
      · exact (hj x hx i (fun hi => by rw [hi] at h; omega)).symm

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end
