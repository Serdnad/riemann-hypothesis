module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle012
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFlagpairOfFrames
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle011
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle019
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle008

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem lineIso_algebra : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)), IsMultiProjPrime P → (∀ a, IsLineIso P a a 1 1) ∧ (∀ a b f g, IsLineIso P a b f g → IsLineIso P b a g f) ∧ (∀ a b c f g f' g', IsLineIso P a b f g → IsLineIso P b c f' g' → IsLineIso P a c (f * f') (g * g')) ∧ (∀ a b a' b' f g f' g', IsLineIso P a b f g → IsLineIso P a' b' f' g' → IsLineIso P (a + a') (b + b') (f * f') (g * g')) ∧ ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (P' : Ideal (MRing ι')), IsBlockMap κ v → imageZ v P' = P → ∀ a b f g, IsLineIso P a b f g → IsLineIso P' (pullDeg κ a) (pullDeg κ b) (rename v f) (rename v g) :=
  @PositivityTheory.UnitarySelfGeneration.i_algebra

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section

set_option maxSynthPendingDepth 1

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

noncomputable section

variable {n : ℕ}

theorem continuous_pairing_pointOf (h : HermNorm n) (u : Fin n → ℂ) :
    Continuous fun y : EuclideanSpace ℂ (Fin n) => ∑ j, u j * h.pointOf y j := by
  have hp : Continuous (fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y) := by
    unfold HermNorm.pointOf; fun_prop
  exact continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hp)

theorem pairing_pointOf_smul (h : HermNorm n) (u : Fin n → ℂ) (t : ℂ)
    (y : EuclideanSpace ℂ (Fin n)) :
    ∑ j, u j * h.pointOf (t • y) j = t * ∑ j, u j * h.pointOf y j := by
  have hpt : h.pointOf (t • y) = t • h.pointOf y := by
    simp only [HermNorm.pointOf]
    rw [← Matrix.mulVec_smul]
    congr 1
  rw [hpt, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem dualNorm_pointOf_eq (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.dualNorm (h.pointOf y) = ‖y‖ := by
  have hA : IsUnit h.matᵀ.det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  rw [HermNorm.dualNorm, HermNorm.pointOf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA,
    Matrix.one_mulVec, EuclideanSpace.norm_eq]

theorem hermNorm_pos (h : HermNorm n) {u : Fin n → ℂ} (hu : u ≠ 0) : 0 < h.norm u := by
  have hne : h.mat *ᵥ u ≠ 0 := by
    intro h0
    apply hu
    have h1 := congrArg (fun v => h.mat⁻¹ *ᵥ v) h0
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det] using h1
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  rw [HermNorm.norm]
  refine Real.sqrt_pos.mpr (Finset.sum_pos' (fun _ _ => by positivity)
    ⟨i, Finset.mem_univ _, ?_⟩)
  have : 0 < ‖(h.mat *ᵥ u) i‖ := norm_pos_iff.mpr hi
  positivity

theorem lt_logGap_iff (h : HermNorm n) {u : Fin n → ℂ} (hu : u ≠ 0) {s : ℝ≥0∞} (hs : s ≠ ⊤)
    (y : EuclideanSpace ℂ (Fin n)) :
    s < logGap h u y ↔
      ‖∑ j, u j * h.pointOf y j‖ < Real.exp (-s.toReal) * h.norm u * ‖y‖ := by
  have hN := hermNorm_pos h hu
  unfold logGap
  by_cases hy : y = 0
  · subst hy
    simp [HermNorm.pointOf]
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hc : 0 < Real.exp (-s.toReal) * h.norm u * ‖y‖ := by positivity
  by_cases hp : ∑ j, u j * h.pointOf y j = 0
  · simp [hy, hp, hs.lt_top, hc]
  · have hpn : 0 < ‖∑ j, u j * h.pointOf y j‖ := norm_pos_iff.mpr hp
    rw [if_neg hy, if_neg hp, ENNReal.lt_ofReal_iff_toReal_lt hs, fsLog, dualNorm_pointOf_eq,
      Real.log_div hpn.ne' hy'.ne', ← Real.log_lt_log_iff hpn hc,
      Real.log_mul (by positivity) hy'.ne', Real.log_mul (Real.exp_pos _).ne' hN.ne', Real.log_exp]
    constructor <;> intro hh <;> linarith

theorem lt_logGap_zero_iff (h : HermNorm n) {s : ℝ≥0∞} (hs : s ≠ ⊤)
    (y : EuclideanSpace ℂ (Fin n)) : s < logGap h 0 y ↔ y ≠ 0 := by
  unfold logGap
  by_cases hy : y = 0
  · simp [hy]
  · simp [hy, hs.lt_top]

theorem logGap_levelSet_top (h : HermNorm n) (u : Fin n → ℂ) :
    {y | (⊤ : ℝ≥0∞) < logGap h u y} = ∅ := by
  ext y
  simp

theorem logGap_levelSet (h : HermNorm n) (u : Fin n → ℂ) (s : ℝ≥0∞) :
    IsOpen {y | s < logGap h u y} ∧ IsScaleStable {y | s < logGap h u y} := by
  by_cases hs : s = ⊤
  · subst hs
    rw [logGap_levelSet_top]
    exact ⟨isOpen_empty, fun y hy => hy.elim⟩
  by_cases hu : u = 0
  · subst hu
    have hset : {y | s < logGap h 0 y} = {y : EuclideanSpace ℂ (Fin n) | y ≠ 0} :=
      Set.ext fun y => lt_logGap_zero_iff h hs y
    rw [hset]
    exact ⟨isOpen_ne, fun y hy t ht => smul_ne_zero ht hy⟩
  have hset : {y | s < logGap h u y} = {y : EuclideanSpace ℂ (Fin n) |
      ‖∑ j, u j * h.pointOf y j‖ < Real.exp (-s.toReal) * h.norm u * ‖y‖} :=
    Set.ext fun y => lt_logGap_iff h hu hs y
  rw [hset]
  refine ⟨isOpen_lt (continuous_pairing_pointOf h u).norm (continuous_const.mul continuous_norm),
    fun y hy t ht => ?_⟩
  have ht' : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hy' : ‖∑ j, u j * h.pointOf y j‖ < Real.exp (-s.toReal) * h.norm u * ‖y‖ := hy
  show ‖∑ j, u j * h.pointOf (t • y) j‖ < Real.exp (-s.toReal) * h.norm u * ‖t • y‖
  rw [pairing_pointOf_smul, norm_mul, norm_smul]
  calc ‖t‖ * ‖∑ j, u j * h.pointOf y j‖
      < ‖t‖ * (Real.exp (-s.toReal) * h.norm u * ‖y‖) := mul_lt_mul_of_pos_left hy' ht'
    _ = Real.exp (-s.toReal) * h.norm u * (‖t‖ * ‖y‖) := by ring

theorem logGap_basic : ∀ (n : ℕ) (h : HermNorm n) (u : Fin n → ℂ),
    Measurable (logGap h u) ∧
      ∀ s : ℝ≥0∞, IsOpen {y | s < logGap h u y} ∧ IsScaleStable {y | s < logGap h u y} := by
  intro n h u
  exact ⟨measurable_of_Ioi fun s => (logGap_levelSet h u s).1.measurableSet,
    logGap_levelSet h u⟩

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem eq_zero_of_hermNorm_eq_zero {n : ℕ} (h : HermNorm n) {u : Fin n → ℂ} (hu : h.norm u = 0) :
    u = 0 := by
  have hs : ∑ i, ‖(h.mat *ᵥ u) i‖ ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => by positivity)).mp hu
  have hz : h.mat *ᵥ u = 0 := by
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).mp hs i (Finset.mem_univ i)
    simpa using hi
  have := congrArg (fun w => h.mat⁻¹ *ᵥ w) hz
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det] using this

theorem eval_scale_groups {k n δ : ℕ} {q : MvPolynomial (Fin k × Fin n) ℂ} (hq : IsMultiHomog δ q)
    (c : Fin k → ℂ) (v : Fin k × Fin n → ℂ) :
    eval (fun ij => c ij.1 * v ij) q = (∏ i, c i ^ δ) * eval v q := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw := hq (mem_support_iff.mp hd)
  have hrow : ∀ i, ∑ j, d (i, j) = δ := by
    intro i
    have := congrFun hw i
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at this
    simp [groupWeight, Fintype.sum_prod_type, Pi.single_apply, Finset.sum_apply] at this
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)] at this
    simpa using this
  have hc : ∏ ij : Fin k × Fin n, c ij.1 ^ d ij = ∏ i, c i ^ δ := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hrow]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem eval_nrmGroups_ne_zero {k n δ : ℕ} (h : HermNorm n) {q : MvPolynomial (Fin k × Fin n) ℂ}
    (hq : IsMultiHomog δ q) {v : Fin k × Fin n → ℂ} (hv : eval v q ≠ 0) :
    eval (nrmGroups h k v) q ≠ 0 := by
  classical
  have e : nrmGroups h k v =
      fun ij => (fun i => ((h.norm fun j => v (i, j) : ℝ) : ℂ)⁻¹) ij.1 * v ij := rfl
  rw [e, eval_scale_groups hq (fun i => ((h.norm fun j => v (i, j) : ℝ) : ℂ)⁻¹) v]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) hv
  rcases Nat.eq_zero_or_pos δ with rfl | hpos
  · simp
  refine pow_ne_zero _ fun hc => hv ?_
  have hn : h.norm (fun j => v (i, j)) = 0 := by simpa using hc
  have hr := eq_zero_of_hermNorm_eq_zero h hn
  have hv' : v = fun ij => (Function.update (1 : Fin k → ℂ) i 0) ij.1 * v ij := by
    funext ⟨a, j⟩
    by_cases ha : a = i
    · subst ha
      simpa using congrFun hr j
    · simp [Function.update_of_ne ha]
  rw [hv', eval_scale_groups hq, Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hpos.ne']), zero_mul]

theorem exists_poly_eval_coefRows {n e : ℕ} (h : HermNorm n) {q : MvPolynomial (Fin e × Fin n) ℂ}
    (hq : q ≠ 0) :
    ∃ Q : MvPolynomial (Fin (e + 1) × Fin n) ℂ, Q ≠ 0 ∧
      ∀ π : Fin (e + 1) → Fin n → ℂ, eval (fun ij => π ij.1 ij.2) Q = eval (coefRows h π) q := by
  let f : Fin e × Fin n → MvPolynomial (Fin (e + 1) × Fin n) ℂ :=
    fun ij => ∑ k, C (h.mat⁻¹ ij.2 k) * X (ij.1.succ, k)
  have key : ∀ π : Fin (e + 1) → Fin n → ℂ,
      eval (fun ij => π ij.1 ij.2) (bind₁ f q) = eval (coefRows h π) q := by
    intro π
    have hf : (fun ij => eval (fun ij => π ij.1 ij.2) (f ij)) = coefRows h π := by
      funext ij
      simp [f, coefRows, Matrix.mulVec, dotProduct]
    rw [← hf]
    exact eval₂Hom_bind₁ _ _ _ _
  refine ⟨bind₁ f q, fun hQ => hq (MvPolynomial.funext fun v => ?_), key⟩
  have hv : coefRows h (Fin.cons 0 fun i => h.mat *ᵥ fun j => v (i, j)) = v := by
    funext ij
    simp [coefRows, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det]
  rw [map_zero, ← hv, ← key, hQ, map_zero]

theorem ae_eval_nrmGroups_coefRows_ne_zero :
    ∀ (n e δ : ℕ) (h : HermNorm n) (q : MvPolynomial (Fin e × Fin n) ℂ), q ≠ 0 → IsMultiHomog δ q →
      ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, eval (nrmGroups h e (coefRows h π)) q ≠ 0 := by
  intro n e δ h q hq hδ
  obtain ⟨Q, hQ, key⟩ := exists_poly_eval_coefRows h hq
  filter_upwards [ConeFibreDegree.ae_eval_matrix_ne_zero Q hQ] with π hπ
  rw [key] at hπ
  exact eval_nrmGroups_ne_zero h hδ hπ

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open TopologicalSpace

variable {m n : ℕ}

theorem isClosed_linProj_meets_compact {K : Set (EuclideanSpace ℂ (Fin n))} (hK : IsCompact K) :
    IsClosed {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) | ∃ y ∈ K, linProj p.1 y = p.2} := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun q : ((Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m)) × K =>
      linProj q.1.1 (q.2 : EuclideanSpace ℂ (Fin n))) := by
    unfold linProj
    fun_prop
  have hC : IsClosed {q : ((Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m)) × K |
      linProj q.1.1 (q.2 : EuclideanSpace ℂ (Fin n)) = q.1.2} :=
    isClosed_eq hc (continuous_snd.comp continuous_fst)
  have h2 := isClosedMap_fst_of_compactSpace _ hC
  convert h2 using 1
  ext p
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨(p, ⟨y, hy⟩), h, rfl⟩
  · rintro ⟨⟨p', y⟩, h, rfl⟩
    exact ⟨y, y.2, h⟩

theorem isSigmaCompact_of_isOpen_euclidean {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) :
    IsSigmaCompact U := by
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance

theorem measurableSet_linProj_meets {S U : Set (EuclideanSpace ℂ (Fin n))} (hS : IsSigmaCompact S)
    (hU : IsOpen U) :
    MeasurableSet {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
      ∃ y ∈ S ∩ U, linProj p.1 y = p.2} := by
  obtain ⟨K, hK, hKS⟩ := hS
  obtain ⟨L, hL, hLU⟩ := isSigmaCompact_of_isOpen_euclidean hU
  have hEq : {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) | ∃ y ∈ S ∩ U, linProj p.1 y = p.2} =
      ⋃ k, ⋃ l, {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
        ∃ y ∈ K k ∩ L l, linProj p.1 y = p.2} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨y, ⟨hyS, hyU⟩, h⟩
      rw [← hKS, Set.mem_iUnion] at hyS
      rw [← hLU, Set.mem_iUnion] at hyU
      obtain ⟨k, hk⟩ := hyS
      obtain ⟨l, hl⟩ := hyU
      exact ⟨k, l, y, ⟨hk, hl⟩, h⟩
    · rintro ⟨k, l, y, ⟨hk, hl⟩, h⟩
      refine ⟨y, ⟨?_, ?_⟩, h⟩
      · rw [← hKS]; exact Set.mem_iUnion.mpr ⟨k, hk⟩
      · rw [← hLU]; exact Set.mem_iUnion.mpr ⟨l, hl⟩
  rw [hEq]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun l =>
    (isClosed_linProj_meets_compact ((hK k).inter (hL l))).measurableSet

theorem natCast_le_encard_ptsOver_iff (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin m → Fin n → ℂ)
    (w : EuclideanSpace ℂ (Fin m)) (N : ℕ) :
    (N : ℕ∞) ≤ (ptsOver S π w).encard ↔
      ∃ f : Fin N → countableBasis (EuclideanSpace ℂ (Fin n)),
        (∀ i j, i ≠ j → Disjoint (f i : Set (EuclideanSpace ℂ (Fin n))) (f j)) ∧
        ∀ i, ∃ y ∈ S ∩ (f i : Set (EuclideanSpace ℂ (Fin n))), linProj π y = w := by
  constructor
  · intro hN
    obtain ⟨t, htS, htN⟩ := Set.exists_subset_encard_eq hN
    have htf : t.Finite := Set.finite_of_encard_eq_coe htN
    have hcard : htf.toFinset.card = N := by
      have := htf.encard_eq_coe_toFinset_card
      rw [htN] at this
      exact_mod_cast this.symm
    let e : Fin N ≃ {x // x ∈ htf.toFinset} := (htf.toFinset.equivFinOfCardEq hcard).symm
    let g : Fin N → EuclideanSpace ℂ (Fin n) := fun i => (e i : EuclideanSpace ℂ (Fin n))
    have hg_mem : ∀ i, g i ∈ t := fun i => htf.mem_toFinset.mp (e i).2
    have hg_inj : Function.Injective g := by
      intro i j hij
      exact e.injective (Subtype.ext hij)
    obtain ⟨V, hV, hVd⟩ := (Set.finite_range g).t2_separation
    have hB : ∀ i, ∃ v ∈ countableBasis (EuclideanSpace ℂ (Fin n)), g i ∈ v ∧ v ⊆ V (g i) := fun i =>
      (isBasis_countableBasis (EuclideanSpace ℂ (Fin n))).exists_subset_of_mem_open (hV (g i)).1 (hV (g i)).2
    choose v hvB hgv hvV using hB
    refine ⟨fun i => ⟨v i, hvB i⟩, ?_, ?_⟩
    · intro i j hij
      have hne : g i ≠ g j := fun h => hij (hg_inj h)
      exact (hVd (Set.mem_range_self i) (Set.mem_range_self j) hne).mono (hvV i) (hvV j)
    · intro i
      have := htS (hg_mem i)
      exact ⟨g i, ⟨this.1, hgv i⟩, this.2⟩
  · rintro ⟨f, hfd, hf⟩
    choose y hy hyw using hf
    have hinj : Function.Injective y := by
      intro i j hij
      by_contra hne
      have hd := hfd i j hne
      exact Set.disjoint_left.mp hd (hy i).2 (hij ▸ (hy j).2)
    have hsub : Set.range y ⊆ ptsOver S π w := by
      rintro _ ⟨i, rfl⟩
      exact ⟨(hy i).1, hyw i⟩
    calc (N : ℕ∞) = (Set.range y).encard := by
          rw [← Set.image_univ, hinj.encard_image, Set.encard_univ]; simp
      _ ≤ (ptsOver S π w).encard := Set.encard_le_encard hsub

theorem measurableSet_natCast_le_encard_ptsOver {S : Set (EuclideanSpace ℂ (Fin n))}
    (hS : IsSigmaCompact S) (N : ℕ) :
    MeasurableSet {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
      (N : ℕ∞) ≤ (ptsOver S p.1 p.2).encard} := by
  haveI : Countable (countableBasis (EuclideanSpace ℂ (Fin n))) :=
    (countable_countableBasis (EuclideanSpace ℂ (Fin n))).to_subtype
  have hEq : {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
      (N : ℕ∞) ≤ (ptsOver S p.1 p.2).encard} =
      ⋃ f : Fin N → countableBasis (EuclideanSpace ℂ (Fin n)),
        ({_p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
          ∀ i j, i ≠ j → Disjoint (f i : Set (EuclideanSpace ℂ (Fin n))) (f j)} ∩
        ⋂ i, {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
          ∃ y ∈ S ∩ (f i : Set (EuclideanSpace ℂ (Fin n))), linProj p.1 y = p.2}) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
    exact natCast_le_encard_ptsOver_iff S p.1 p.2 N
  rw [hEq]
  exact MeasurableSet.iUnion fun f => (MeasurableSet.const _).inter
    (MeasurableSet.iInter fun i => measurableSet_linProj_meets hS (isOpen_of_mem_countableBasis (f i).2))

theorem measurable_cntOver : ∀ (n m : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsSigmaCompact S →
    Measurable (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) => cntOver S p.1 p.2) := by
  intro n m S hS
  have h : (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) => cntOver S p.1 p.2) =
      fun p => ⨆ N : ℕ, {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
        (N : ℕ∞) ≤ (ptsOver S p.1 p.2).encard}.indicator (fun _ => (N : ℝ≥0∞)) p := by
    funext p
    simp only [cntOver, Set.indicator_apply, Set.mem_setOf_eq]
    generalize (ptsOver S p.1 p.2).encard = e
    induction e using ENat.recTopCoe with
    | top => simp [ENNReal.iSup_natCast]
    | coe k =>
      apply le_antisymm
      · exact le_iSup_of_le k (by simp)
      · refine iSup_le fun N => ?_
        split_ifs with hN
        · have : N ≤ k := by exact_mod_cast hN
          simpa using this
        · exact zero_le
  rw [h]
  exact Measurable.iSup fun N => measurable_const.indicator (measurableSet_natCast_le_encard_ptsOver hS N)

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.VertDiv

theorem commensurable_vertical : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (b b' : K → ℤ) (u : Ω), u ≠ 0 → (∀ s, mseg x s ≠ 0 → (∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) ∧ ∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * (u * chartMon x s b') = r * chartMon x s b) → ∃ f g : MRing ι O, IsVerticalDivisor (pointIdeal O x) ϖ (b - b') f g ∧ aeval x f = u * aeval x g :=
  @PositivityTheory.Xgn.t_vertdiv_commensurable

end GlobalTheory.CompanionTheory.Ar.Num.VertDiv
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.FlagPairOfFrames

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' → ∀ (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K → ℤ), IsFlagFrame x E w b → IsFlagFrame x E' w' b' → (∀ i j : Fin N, i < j → w.repr (w' i) j = 0) → SameGenericFibre ϖ E E' ∧ ∃ f g : Fin N → MRing ι O, IsFlagPair ϖ x E E' w w' b b' f g :=
  @PositivityTheory.Xgn.t_flagpair_of_frames

end GlobalTheory.CompanionTheory.Ar.FlagPairOfFrames
end

section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem _root_.GlobalTheory.T.chart_rings_noetherian_fraction : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), (∀ c, IsNoetherianRing (chartRing O (mseg x) c)) ∧ (fnField O x = ⊤ → ∀ c, mseg x c ≠ 0 → IsFractionRing (chartRing O (mseg x) c) Ω) ∧ ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), (fnField O x = ⊤ → fnField O (joinCoord x z) = ⊤) ∧ ∀ c, mseg (joinCoord x z) c ≠ 0 → mseg x (restrictChart c) ≠ 0 ∧ (chartRing O (mseg x) (restrictChart c)) ≤ (chartRing O (mseg (joinCoord x z)) c) :=
  @_root_.PositivityTheory.Xgn.t_chart_noeth_frac
end

section

open TensorProduct

theorem _root_.GlobalTheory.T.module_flat_of_flat_and_fibre_flat : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)], Module.Flat R B → (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) (IsScalarTower.toAlgHom R A B)).toRingHom.Flat → Module.Flat A B := by
  first | exact @GlobalTheory.CompanionTheory.Relay.module_flat_of_flat_and_fibre_flat | exact GlobalTheory.CompanionTheory.Relay.module_flat_of_flat_and_fibre_flat | (intros; apply GlobalTheory.CompanionTheory.Relay.module_flat_of_flat_and_fibre_flat <;> assumption)
end
