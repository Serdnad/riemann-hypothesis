module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCasimirInverseTopDegreeBound
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle049
public import Formalism.LocalToGlobal.ProjectiveLattices.PtOfSPf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle059
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Bool

@[expose] public section

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

noncomputable section
namespace GlobalTheory.TypeSum.CasBasis.Expand
variable {n : ℕ}

theorem sum_get {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → M) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  rw [Fin.sum_univ_def]
  conv_rhs => rw [← List.map_get_finRange l]
  rw [List.map_map]
  rfl

theorem trace_mul_unitE (U : Mx n) (a b : Fin n) : trace (U * unitE a b) = U b a := by
  simpa [unitE] using (Matrix.trace_mul_single U a b 1)

theorem sum_flatMap {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem filter_split {α M : Type*} [AddCommMonoid M] (l : List α) (c d : α → Bool) (F : α → M) :
    ((l.filter fun p => c p && (d p == true)).map F).sum + ((l.filter fun p => c p && (d p == false)).map F).sum =
      (l.map fun p => if c p then F p else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    cases hc : c a <;> cases hd : d a <;> simp [← ih] <;> abel

theorem sum_map_neg' {α M : Type*} [AddCommGroup M] (l : List α) (f : α → M) :
    (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, neg_add]

theorem sum_product_list {M : Type*} [AddCommMonoid M] (G : Fin n × Fin n → M) :
    ((List.product (List.finRange n) (List.finRange n)).map G).sum = ∑ a, ∑ b, G (a, b) := by
  simp [List.product, List.map_flatMap, sum_flatMap, List.map_map, Fin.sum_univ_def, Function.comp_def]

variable {ε : Fin n → Bool}

theorem diag_re {U : Mx n} (hU : U ∈ lieSet ε) (a : Fin n) : (U a a).re = 0 := by
  have h := (mem_lieSet_iff_entry.mp hU) a a
  rcases ha : ε a <;> simp [ha] at h <;> have h2 := congrArg Complex.re h <;> simp at h2 <;> linarith

theorem entry_same {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a = ε b) : U b a = -star (U a b) := by
  have h1 := (mem_lieSet_iff_entry.mp hU) a b
  rw [h] at h1
  have : (starRingEnd ℂ) (U b a) = -U a b := by
    rcases hb : ε b <;> simp [hb] at h1 <;> first | linear_combination h1 | linear_combination -h1
  have h3 := congrArg (starRingEnd ℂ) this
  simp at h3
  simpa [Complex.star_def] using h3

theorem entry_opp {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a ≠ ε b) : U b a = star (U a b) := by
  have h1 := (mem_lieSet_iff_entry.mp hU) a b
  have : star (U b a) = U a b := by
    rcases ha : ε a <;> rcases hb : ε b <;> simp_all <;> first | linear_combination h1 | linear_combination -h1
  have h3 := congrArg star this
  simpa using h3

abbrev tm (U X : Mx n) : Mx n := (trace (U * X)).re • X

theorem tm_diag {U : Mx n} (hU : U ∈ lieSet ε) (a : Fin n) :
    tm U (Complex.I • unitE a a) = -(U a a • unitE a a) := by
  have h := diag_re hU a
  simp only [tm, Matrix.mul_smul, trace_smul, trace_mul_unitE, ← Complex.coe_smul, smul_smul, ← neg_smul]
  congr 1
  apply Complex.ext <;> simp [h]

theorem tm_same {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a = ε b) :
    tm U (invSqrtTwo • (unitE a b - unitE b a)) + tm U ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) =
      -(U a b • unitE a b + U b a • unitE b a) := by
  have hba := entry_same hU h
  simp only [tm, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_add, trace_smul, trace_sub, trace_add, trace_mul_unitE,
    ← Complex.coe_smul, hba]
  match_scalars <;> simp only [smul_eq_mul] <;> apply Complex.ext <;>
    simp [invSqrtTwo, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im] <;> field_simp
  all_goals (try rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]) <;> ring

theorem tm_opp {U : Mx n} (hU : U ∈ lieSet ε) {a b : Fin n} (h : ε a ≠ ε b) :
    tm U (invSqrtTwo • (unitE a b + unitE b a)) + tm U ((invSqrtTwo * Complex.I) • (unitE a b - unitE b a)) =
      U a b • unitE a b + U b a • unitE b a := by
  have hba := entry_opp hU h
  simp only [tm, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_add, trace_smul, trace_sub, trace_add, trace_mul_unitE,
    ← Complex.coe_smul, hba]
  match_scalars <;> simp only [smul_eq_mul] <;> apply Complex.ext <;>
    simp [invSqrtTwo, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im] <;> field_simp
  all_goals (try rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]) <;> ring

abbrev pairTerm (U : Mx n) (p : Fin n × Fin n) : Mx n := U p.1 p.2 • unitE p.1 p.2 + U p.2 p.1 • unitE p.2 p.1

theorem decomp (U : Mx n) :
    U = ∑ a, U a a • unitE a a + ∑ a, ∑ b, if a < b then pairTerm U (a, b) else 0 := by
  ext r t
  simp only [Matrix.add_apply, Matrix.sum_apply, apply_ite (fun M : Mx n => M r t), pairTerm, Matrix.smul_apply,
    single_apply, smul_eq_mul, Matrix.zero_apply]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  rcases lt_trichotomy r t with h | rfl | h
  · rw [Finset.sum_eq_single r (fun x _ hx => Finset.sum_eq_zero fun y _ => by split_ifs <;> grind) (by simp),
      Finset.sum_eq_single t (fun y _ hy => by split_ifs <;> grind) (by simp)]
    simp [h, h.ne, not_lt.mpr h.le]
  · simp only [lt_self_iff_false, if_true]
    rw [Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => by split_ifs <;> grind]
    simp
  · rw [Finset.sum_eq_single t (fun x _ hx => Finset.sum_eq_zero fun y _ => by split_ifs <;> grind) (by simp),
      Finset.sum_eq_single r (fun y _ hy => by split_ifs <;> grind) (by simp)]
    simp [h, h.ne, h.ne', not_lt.mpr h.le]

theorem pairs_split (U : Mx n) :
    ((pairs ε true).map (pairTerm U)).sum + ((pairs ε false).map (pairTerm U)).sum =
      ∑ a, ∑ b, if a < b then pairTerm U (a, b) else 0 :=
  (filter_split _ (fun p : Fin n × Fin n => decide (p.1 < p.2)) (fun p : Fin n × Fin n => ε p.1 == ε p.2)
    (pairTerm U)).trans (by rw [sum_product_list]; simp)

theorem sum_k {U : Mx n} (hU : U ∈ lieSet ε) :
    ∑ i, tm U (kB ε i) = -(∑ a, U a a • unitE a a + ((pairs ε true).map (pairTerm U)).sum) := by
  rw [show (∑ i, tm U (kB ε i)) = ((kList ε).map (tm U)).sum from sum_get _ _]
  simp only [kList, List.map_append, List.sum_append, List.map_map, List.map_flatMap, sum_flatMap, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, Function.comp_def, tm_diag hU]
  rw [List.map_congr_left (g := fun p => -pairTerm U p) (fun p hp => by
    have hs : ε p.1 = ε p.2 := by
      simp [pairs] at hp
      exact hp.2.2
    exact tm_same hU hs), Fin.sum_univ_def, sum_map_neg', sum_map_neg', neg_add]

theorem sum_p {U : Mx n} (hU : U ∈ lieSet ε) :
    ∑ b, tm U (pB ε b) = ((pairs ε false).map (pairTerm U)).sum := by
  rw [show (∑ b, tm U (pB ε b)) = ((pList ε).map (tm U)).sum from sum_get _ _]
  simp only [pList, List.map_flatMap, sum_flatMap, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [List.map_congr_left (g := pairTerm U) (fun p hp => by
    have hs : ε p.1 ≠ ε p.2 := by
      simp [pairs] at hp
      exact hp.2.2
    exact tm_opp hU hs)]

end GlobalTheory.TypeSum.CasBasis.Expand

namespace GlobalTheory.TypeSum.CasBasis


open Expand in
theorem lieSet_expand_bases : ∀ (n : ℕ) (ε : Fin n → Bool), ∀ U ∈ lieSet ε,
    U = ∑ b, (trace (U * pB ε b)).re • pB ε b - ∑ i, (trace (U * kB ε i)).re • kB ε i := by
  intro n ε U hU
  have h1 := sum_p hU
  have h2 := sum_k hU
  simp only [tm] at h1 h2
  rw [h1, h2, sub_neg_eq_add]
  conv_lhs => rw [decomp U]
  rw [← pairs_split (ε := ε)]
  abel

end GlobalTheory.TypeSum.CasBasis
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.integral_normSq_reproducingKernel_le_finrank : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), IsKer ε i e → ∫ k, ‖e k‖ ^ 2 ∂(muK ε) ≤ (Module.finrank ℂ (polyV ε i) : ℝ) := by
  first | exact @GlobalTheory.KFourier.integral_norm_sq_ker_le | exact GlobalTheory.KFourier.integral_norm_sq_ker_le | (intros; apply GlobalTheory.KFourier.integral_norm_sq_ker_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.compactUnitaryRightDeriv_real_linear_direction : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ), φ ∈ polyV ε d → ∀ {r : ℕ} (X : Fin r → Mx n) (c : Fin r → ℝ), (∀ j, inK ε (X j)) → rder ε [∑ j, (c j : ℂ) • X j] φ = ∑ j, (c j : ℂ) • rder ε [X j] φ := by
  first | exact @GlobalTheory.KFourier.rder_real_linear | exact GlobalTheory.KFourier.rder_real_linear | (intros; apply GlobalTheory.KFourier.rder_real_linear <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.poly_translation_l2_bound : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ), φ ∈ polyV ε d → ∀ Y : Mx n, inK ε Y → ∫ x, ‖φ x - φ (x * expK ε Y 1)‖ ^ 2 ∂(muK ε) ≤ ∫ x, ‖rder ε [Y] φ x‖ ^ 2 ∂(muK ε) := by
  first | exact @GlobalTheory.KFourier.norm_sub_expK_sq_le | exact GlobalTheory.KFourier.norm_sub_expK_sq_le | (intros; apply GlobalTheory.KFourier.norm_sub_expK_sq_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.compactUnitaryCasimir_inverse_topDegree_bound : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ j, inK ε (X j)) → ∀ (i : ℕ) (l : ℝ), 0 < l → (∀ p ∈ polyV ε i, (∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) → l * ∫ k, ‖p k‖ ^ 2 ∂(muK ε) ≤ ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε)) → ∀ (M : ℕ) (e : KG ε → ℂ), e ∈ polyV ε i → (∀ q ∈ lowV ε i, ∫ k, q k * e k ∂(muK ε) = 0) → ∃ s ∈ polyV ε i, (fun φ : KG ε → ℂ => ∑ j, rder ε [X j, X j] φ)^[M] s = e ∧ ∫ k, ‖s k‖ ^ 2 ∂(muK ε) ≤ (l ^ (2 * M))⁻¹ * ∫ k, ‖e k‖ ^ 2 ∂(muK ε) := by
  first | exact @GlobalTheory.KFourier.casimir_inverse_bound | exact GlobalTheory.KFourier.casimir_inverse_bound | (intros; apply GlobalTheory.KFourier.casimir_inverse_bound <;> assumption)
end

section




noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.T0

namespace GlobalTheory.SecPoint

section Rec

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  (N : ℕ) {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

theorem range_mul_step {m : ℕ} {x y : X.Forms} (hx : x ∈ LinearMap.range (X.inc (addL (wt0 D j) wL m)))
    (hy : y ∈ LinearMap.range (X.inc wL)) : x * y ∈ LinearMap.range (X.inc (addL (wt0 D j) wL (m + 1))) := by
  obtain ⟨F, rfl⟩ := hx
  obtain ⟨G, rfl⟩ := hy
  obtain ⟨H, hH⟩ := X.inc_mul wL _ G F
  rw [← wadd_addL, mul_comm, hH]
  exact ⟨H, rfl⟩

theorem range_pow {m : ℕ} {y x : X.Forms} (hy : y ∈ LinearMap.range (X.inc (addL (wt0 D j) wL m)))
    (hx : x ∈ LinearMap.range (X.inc wL)) (e : ℕ) :
    y * x ^ e ∈ LinearMap.range (X.inc (addL (wt0 D j) wL (m + e))) := by
  induction e with
  | zero => simpa using hy
  | succ e ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc]
    exact range_mul_step X ih hx

theorem range_prod (d : Fin N →₀ ℕ) {m : ℕ} {y : X.Forms}
    (hy : y ∈ LinearMap.range (X.inc (addL (wt0 D j) wL m))) (s : Finset (Fin N)) :
    y * ∏ i ∈ s, X.inc wL (w i) ^ d i ∈ LinearMap.range (X.inc (addL (wt0 D j) wL (m + ∑ i ∈ s, d i))) := by
  classical
  refine Finset.induction_on s (by rwa [Finset.prod_empty, Finset.sum_empty, mul_one, add_zero]) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  have e1 : y * (X.inc wL (w a) ^ d a * ∏ i ∈ s, X.inc wL (w i) ^ d i) =
      (y * ∏ i ∈ s, X.inc wL (w i) ^ d i) * X.inc wL (w a) ^ d a := by ring
  have e2 : m + (d a + ∑ i ∈ s, d i) = m + ∑ i ∈ s, d i + d a := by ring
  rw [e1, e2]
  exact range_pow X ih ⟨w a, rfl⟩ (d a)

theorem range_aeval {k : ℕ} (Pw : MvPolynomial (Fin N) B.KO) (hPw : Pw.IsHomogeneous k) {m : ℕ} {y : X.Forms}
    (hy : y ∈ LinearMap.range (X.inc (addL (wt0 D j) wL m))) :
    y * MvPolynomial.aeval (fun i => X.inc wL (w i)) Pw ∈ LinearMap.range (X.inc (addL (wt0 D j) wL (m + k))) := by
  classical

  rw [Pw.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, mul_left_comm, ← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have hdeg : ∑ i ∈ d.support, d i = k := by
    have := hPw (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have h := range_prod X N w d hy d.support
  rw [hdeg] at h
  exact h

theorem exists_ratio {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)
    (hB : CurveLoc.BirAt X N w gF) (hk : ∃ k, gF (X.inc wL (w k)) ≠ 0) (a : Ω) :
    ∃ (m : ℕ) (p q : B.Cusp j (addL (wt0 D j) wL m)), gF (X.inc _ p) ≠ 0 ∧ a * gF (X.inc _ p) = gF (X.inc _ q) := by
  obtain ⟨k0, hk0⟩ := hk
  obtain ⟨k, g, Pw, hPw, hne, he⟩ := hB a
  have h1 : X.inc wL (w k0) ∈ LinearMap.range (X.inc (addL (wt0 D j) wL 1)) := by
    rw [add_zero_weight_one_eq]; exact ⟨_, rfl⟩
  obtain ⟨p, hp⟩ := range_aeval X N w Pw hPw h1
  have hG : X.inc wL (w k0) * X.inc (wsmul k wL) g ∈ LinearMap.range (X.inc (addL (wt0 D j) wL (1 + k))) := by
    obtain ⟨H, hH⟩ := X.inc_mul wL _ (w k0) g
    rw [add_comm, ← wadd_addL, addL, zero_weight_add, hH]
    exact ⟨H, rfl⟩
  obtain ⟨q, hq⟩ := hG
  have hPv : gF (MvPolynomial.aeval (fun i => X.inc wL (w i)) Pw) =
      MvPolynomial.aeval (fun i => gF (X.inc wL (w i))) Pw :=
    MvPolynomial.comp_aeval_apply (fun i => X.inc wL (w i)) gF Pw
  refine ⟨1 + k, p, q, ?_, ?_⟩
  · rw [hp, map_mul, hPv]
    exact mul_ne_zero hk0 hne
  · rw [hp, hq, map_mul, map_mul, hPv, ← he]
    ring

def evK {F : Type} [Field F] (ev : Rp X la N →+* F) : Kp X la N →+* F :=
  ev.comp (algebraMap (Kp X la N) (Rp X la N))

theorem ev_smul {F : Type} [Field F] (ev : Rp X la N →+* F) (c : Kp X la N) (g : Rp X la N) :
    ev (c • g) = evK X la N ev c * ev g := by
  rw [Algebra.smul_def, map_mul]; rfl

theorem lift_algKp {F : Type} [Field F] (ev : Rp X la N →+* F) (hu : IsUnit (ev (sec X la w 0))) (c : Kp X la N) :
    IsLocalization.Away.lift (sec X la w 0) hu
      ((algebraMap (Kp X la N) ↥(Frac0 X la w) c : ↥(Frac0 X la w)) : Lw X la w) = evK X la N ev c := by
  show IsLocalization.Away.lift (sec X la w 0) hu (algebraMap (Kp X la N) (Lw X la w) c) = _
  rw [IsScalarTower.algebraMap_apply (Kp X la N) (Rp X la N) (Lw X la w), liftEv_alg]
  rfl

section Fam

variable {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)

theorem exists_point [Finite ι]
    (hinj : ∀ (u : WeightFamilies.Wt D j) (G : B.Cusp j u), (∀ Z, gF Z (X.inc u G) = 0) → G = 0)
    (hsplit : ∀ (Z : ι) (k : Fin N), ∃ g : B.Cusp j wL, gF Z (X.inc wL g) = gF Z (X.inc wL (w k)) ∧
      ∀ Z', Z' ≠ Z → gF Z' (X.inc wL g) = 0)
    (hB : ∀ Z, CurveLoc.BirAt X N w (gF Z)) (hC : ∀ Z, CurveLoc.CountQAt X la N w (gF Z))
    {F : Type} [Field F] (ev : Rp X la N →+* F) (hu : IsUnit (ev (sec X la w 0)))
    (honS : ∀ i : Fin (WeightFamilies.dimY D j), ev (sec X la w i.succ) = 0) :
    ∃ (Z : ι) (τ : Ω Z →+* F) (σ : F), σ ≠ 0 ∧
      (∀ (u : WeightFamilies.Wt D j) (G : B.Cusp j u), gF Z (X.inc u G) = 0 → ev (emb X la N (X.inc u G)) = 0) ∧
      (∀ a : B.KO, τ (algebraMap B.KO (Ω Z) a) =
        evK X la N ev (algebraMap (X.Kl la) (Kp X la N) (algebraMap B.KO (X.Kl la) a))) ∧
      ∀ (k : ℕ) (G : X.Forms), emb X la N G ∈ Vw X la N (addL (wt0 D j) wL k) →
        ev (emb X la N G) = τ (gF Z G) * σ ^ k := by
  classical
  have := Fintype.ofFinite ι
  letI : Algebra (Kp X la N) F := (evK X la N ev).toAlgebra
  let ψ : ↥(Frac0 X la w) →ₐ[Kp X la N] F :=
    { (IsLocalization.Away.lift (sec X la w 0) hu).comp (Frac0 X la w).val.toRingHom with
      commutes' := fun c => lift_algKp X la N w ev hu c }
  have hψ : ∀ (x : ↥(Frac0 X la w)) (k : ℕ) (g : Rp X la N), (x : Lw X la w) = frac X la w k g →
      ψ x = ev g * (ev (sec X la w 0))⁻¹ ^ k := fun x k g hx => by
    show IsLocalization.Away.lift (sec X la w 0) hu (x : Lw X la w) = _
    rw [hx, liftEv_frac]
  have hQ : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime _
  have hJ : Jid X la w ≤ RingHom.ker ψ := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hψ _ 1 _ (coe_sfr X la w i.succ), honS, zero_mul]
  have hinf : (Finset.univ : Finset ι).inf (fun Z => RingHom.ker (phiZ X la N (Ω Z) (gF Z) w)) ≤ RingHom.ker ψ := by
    intro f hf
    have hf' : ∀ Z, phiZ X la N (Ω Z) (gF Z) w f = 0 := fun Z =>
      RingHom.mem_ker.1 (Finset.inf_le (f := fun Z => RingHom.ker (phiZ X la N (Ω Z) (gF Z) w))
        (Finset.mem_univ Z) hf)
    rw [CurveInj.fraction_zero_injective X la N Ω gF w hinj f hf']
    exact Ideal.zero_mem _
  obtain ⟨Z, -, hZ⟩ := (Ideal.IsPrime.inf_le' hQ).1 hinf
  obtain ⟨χ, hχ⟩ := pos_factor (phiZ X la N (Ω Z) (gF Z) w) ψ
    (fun f hf => RingHom.mem_ker.1 (hZ (RingHom.mem_ker.2 hf))) (fun r => by
      obtain ⟨a, p, hp, hr⟩ := CurveLoc.loc_of_bir X la N w (gF Z) (hB Z) (hC Z) r
      exact ⟨a, p, fun h0 => hp _ hQ hJ hZ (RingHom.mem_ker.2 h0), hr⟩)
  have hs := pos_sec_ne X la N w (gF Z) χ
  have hs0 := hu.ne_zero
  refine ⟨Z, χ.toRingHom.comp (CurveLoc.psiZ X la N w (gF Z)), ev (sec X la w 0) *
    (χ (algebraMap (RZ X la N (Ω Z)) (RZs X la N (Ω Z) (gF Z) w) (rzMap X la N (Ω Z) (gF Z) (sec X la w 0))))⁻¹,
    mul_ne_zero hs0 (inv_ne_zero hs), fun u G h0 => ?_,
    fun a => (congrArg χ (pos_psiZ_alg X la N w (gF Z) a)).trans (χ.commutes _), fun k G hG => ?_⟩
  · choose g hg using hsplit Z
    have hmem : frac X la w 1 (CurveLoc.secOf X la N g) ∈ Frac0 X la w :=
      Algebra.subset_adjoin (frac_mem_Hfr X la w (by rw [add_zero_weight_one_eq]; exact CurveLoc.secOf_mem X la N g))
    have h1 : (⟨_, hmem⟩ : ↥(Frac0 X la w)) - 1 ∈ RingHom.ker (phiZ X la N (Ω Z) (gF Z) w) := by
      rw [RingHom.mem_ker, map_sub, map_one, CurveLoc.phiZ_of_eq X la N w (gF Z) _ 1 _ rfl,
        CurveLoc.rzMap_secOf X la N (gF Z) g w (fun k => (hg k).1), CurveLoc.secOf_self, pow_one,
        CurveLoc.weight_zero_section_mul_inv, sub_self]
    have h2 := hZ h1
    rw [RingHom.mem_ker, map_sub, map_one, hψ _ 1 _ rfl, pow_one, sub_eq_zero] at h2
    have he : ev (CurveLoc.secOf X la N g) ≠ 0 := left_ne_zero_of_mul_eq_one h2
    have hHe : emb X la N (X.inc u G) * CurveLoc.secOf X la N g = 0 :=
      CurveInj.vw_inj X la N Ω gF (wadd u wL) (hinj _)
        (mul_mem_Vw X la N (emb_mem_Vw X la N u G) (CurveLoc.secOf_mem X la N g))
        fun Z' => by
          rw [map_mul]
          by_cases hZ' : Z' = Z
          · subst hZ'
            rw [rzMap_emb, h0, TensorProduct.tmul_zero, TensorProduct.tmul_zero, zero_mul]
          · rw [CurveLoc.rzMap_secOf_zero X la N (gF Z') g (fun k => (hg k).2 Z' hZ'), mul_zero]
    have h3 := congrArg ev hHe
    rw [map_mul, map_zero] at h3
    exact (mul_eq_zero.1 h3).resolve_right he
  · have h1 := ((hχ _).trans (hψ _ k _ rfl)).symm.trans (phi_fraction_base_value X la N w (gF Z) χ k G hG)
    show _ = χ (CurveLoc.psiZ X la N w (gF Z) (gF Z G)) * _
    rw [mul_pow, mul_left_comm, ← h1, mul_left_comm, ← mul_pow, mul_inv_cancel₀ hs0, one_pow, mul_one]

end Fam

section One

variable {Ω : Type} [Field Ω] [Algebra B.KO Ω] (gF : X.Forms →ₐ[B.KO] Ω)

theorem ev_sec {F : Type} [Field F] (ev : Rp X la N →+* F) (τ : Ω →+* F) (σ : F)
    (hc : ∀ (k : ℕ) (G : X.Forms), emb X la N G ∈ Vw X la N (addL (wt0 D j) wL k) →
      ev (emb X la N G) = τ (gF G) * σ ^ k) (i : Fin (WeightFamilies.dimY D j + 1)) :
    ev (sec X la w i) = (∑ k, evK X la N ev (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k))) *
      τ (gF (X.inc wL (w k)))) * σ := by
  unfold Formalism.MainNotions.Gaps.EtaleWeightGaps.sec

  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ev_smul, hc 1 _ (by rw [add_zero_weight_one_eq]; exact emb_mem_Vw X la N wL (w k)), pow_one, mul_assoc]

end One

end Rec

end GlobalTheory.SecPoint
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.sqrt_integral_norm_sq_le_integral_kernel_mul_translate : ∀ {n : ℕ} (ε : Fin n → Bool) (p : KG ε → ℂ) (κ : KG ε → ℝ), Continuous p → Continuous κ → (∀ k, 0 ≤ κ k) → ∫ k, κ k ∂(muK ε) = 1 → (∀ k, ∫ x, star (p x) * (κ (x⁻¹ * k) : ℂ) ∂(muK ε) = 0) → Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) ≤ ∫ k, κ k * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) ∂(muK ε) := by
  first | exact @GlobalTheory.KFourier.sqrt_integral_normSq_le_integral_kernel_mul_translate | exact GlobalTheory.KFourier.sqrt_integral_normSq_le_integral_kernel_mul_translate | (intros; apply GlobalTheory.KFourier.sqrt_integral_normSq_le_integral_kernel_mul_translate <;> assumption)
end
