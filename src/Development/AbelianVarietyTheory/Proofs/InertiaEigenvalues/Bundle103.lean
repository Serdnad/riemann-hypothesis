module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.RingTheory.Idempotents
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle069
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Valuation.Integral
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.OKCompact

theorem continuous_coeff_charpoly {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {n : ℕ}
    (k : ℕ) : Continuous fun M : Matrix (Fin n) (Fin n) A => M.charpoly.coeff k := by
  have : (fun M : Matrix (Fin n) (Fin n) A => M.charpoly.coeff k) = fun M =>
      MvPolynomial.eval (fun p : Fin n × Fin n => M p.1 p.2)
        (MvPolynomial.map (Int.castRingHom A) ((Matrix.charpoly.univ ℤ (Fin n)).coeff k)) := by
    funext M
    rw [MvPolynomial.eval_map]
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (Int.castRingHom A) (fun p => M p.1 p.2) k).symm
  rw [this]
  exact (MvPolynomial.continuous_eval _).comp (by fun_prop)

theorem charpoly_smul_eq_scaleRoots {K : Type} [Field K] [Infinite K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    {c : K} (hc : c ≠ 0) : (c • M).charpoly = M.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [Polynomial.scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

variable {F : Type} [NontriviallyNormedField F] {K : Type} [CommRing K] [Algebra F K] [Module.Finite F K]

theorem coeff_charpoly_lmul_smul [Infinite F] (z : K) {c : F} (hc : c ≠ 0) (k : ℕ) :
    (LinearMap.charpoly (Algebra.lmul F K (c • z))).coeff k =
      (LinearMap.charpoly (Algebra.lmul F K z)).coeff k * c ^ (Module.finrank F K - k) := by
  let b := Module.finBasis F K
  rw [← LinearMap.charpoly_toMatrix (Algebra.lmul F K (c • z)) b,
    ← LinearMap.charpoly_toMatrix (Algebra.lmul F K z) b, map_smul, map_smul,
    charpoly_smul_eq_scaleRoots _ hc, Polynomial.coeff_scaleRoots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem continuous_coeff_lmul [TopologicalSpace K] [IsModuleTopology F K] (k : ℕ) :
    Continuous fun z : K => (LinearMap.charpoly (Algebra.lmul F K z)).coeff k := by
  let b := Module.finBasis F K
  have h : (fun z : K => (LinearMap.charpoly (Algebra.lmul F K z)).coeff k) =
      (fun M : Matrix _ _ F => M.charpoly.coeff k) ∘ (fun z => Algebra.leftMulMatrix b z) := by
    funext z
    simp only [Function.comp, Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
  rw [h]
  refine (continuous_coeff_charpoly k).comp ?_
  refine continuous_matrix fun i j => ?_
  let l : K →ₗ[F] F :=
    { toFun := fun z => Algebra.leftMulMatrix b z i j
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  exact IsModuleTopology.continuous_of_linearMap l

end GlobalTheory.JR.OKCompact

namespace GlobalTheory.JR.OKCompact

theorem okCompact : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), IsCompact A.OK := by
  intro F E _ _ _ _ hU A
  haveI : CharZero F := hU.charZero
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank F A.K = n := ⟨_, rfl⟩
  let e : A.K ≃ₗ[F] (Fin n → F) := (Module.finBasisOfFinrankEq F A.K hn).equivFun
  have hes : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let P : ℕ → A.K → F := fun k z => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff k
  have hPc : ∀ k, Continuous (P k) := fun k => continuous_coeff_lmul k
  have hcl : IsClosed A.OK := by
    have : A.OK = ⋂ k, {z | ‖P k z‖ ≤ 1} := by ext z; simp [Et.OK, P]
    rw [this]
    exact isClosed_iInter fun k => isClosed_le (continuous_norm.comp (hPc k)) continuous_const
  have hzero : ∀ z : A.K, (∀ k < n, P k z = 0) → z = 0 := by
    intro z hz
    have hp : LinearMap.charpoly (Algebra.lmul F A.K z) = Polynomial.X ^ n := by
      ext k
      rw [Polynomial.coeff_X_pow]
      rcases lt_trichotomy k n with hk | hk | hk
      · rw [if_neg hk.ne]; exact hz k hk
      · rw [if_pos hk]
        have := (LinearMap.charpoly_monic (Algebra.lmul F A.K z)).coeff_natDegree
        rwa [LinearMap.charpoly_natDegree, hn, ← hk] at this
      · rw [if_neg hk.ne']
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [LinearMap.charpoly_natDegree, hn]; exact hk
    have hCH := LinearMap.aeval_self_charpoly (Algebra.lmul F A.K z)
    rw [hp, map_pow, Polynomial.aeval_X, ← map_pow] at hCH
    have h1 := LinearMap.congr_fun hCH 1
    have h2 : z ^ n = 0 := by simpa using h1
    exact IsReduced.eq_zero z ⟨n, h2⟩
  obtain ⟨a, ha⟩ := NormedField.exists_one_lt_norm F
  let T : Set (Fin n → F) := {v | 1 ≤ ‖v‖ ∧ ‖v‖ ≤ ‖a‖}
  have hT : IsCompact T := (isCompact_closedBall (0 : Fin n → F) ‖a‖).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
      (fun v hv => mem_closedBall_zero_iff.2 hv.2)
  let h : (Fin n → F) → ℝ := fun v => ∑ k ∈ Finset.range n, ‖P k (e.symm v)‖
  have hc : Continuous h := continuous_finsetSum _ fun k _ => continuous_norm.comp ((hPc k).comp hes)
  have hpos : ∀ v ∈ T, 0 < h v := by
    intro v hv
    by_contra hle
    push_neg at hle
    have hsum : h v = 0 := le_antisymm hle (Finset.sum_nonneg fun k _ => norm_nonneg _)
    have h0 : ∀ k < n, P k (e.symm v) = 0 := by
      intro k hk
      exact norm_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun k _ => norm_nonneg (P k (e.symm v))).1 hsum k
        (Finset.mem_range.2 hk))
    have hv0 : v = 0 := by simpa using congrArg e (hzero _ h0)
    have := hv.1
    rw [hv0, norm_zero] at this
    linarith
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ v ∈ T, m ≤ h v := by
    rcases T.eq_empty_or_nonempty with hTe | hTn
    · exact ⟨1, one_pos, fun v hv => by rw [hTe] at hv; exact hv.elim⟩
    · obtain ⟨v₀, hv₀, hmin⟩ := hT.exists_isMinOn hTn hc.continuousOn
      exact ⟨h v₀, hpos v₀ hv₀, fun v hv => hmin hv⟩
  have hsub : A.OK ⊆ e.symm '' Metric.closedBall 0 (‖a‖ * max 1 (n / m)) := by
    intro z hz
    refine ⟨e z, ?_, e.symm_apply_apply z⟩
    rw [mem_closedBall_zero_iff]
    have hR : ‖a‖ ≤ ‖a‖ * max 1 (n / m) := le_mul_of_one_le_right (norm_nonneg _) (le_max_left _ _)
    by_cases hv : e z = 0
    · rw [hv, norm_zero]; linarith
    obtain ⟨d, hd0, hd1, hd2, -⟩ := rescale_to_shell ha (by linarith : (0 : ℝ) < ‖a‖) hv
    have hwT : d • e z ∈ T := ⟨by rwa [div_self (by linarith : ‖a‖ ≠ 0)] at hd2, hd1.le⟩
    have hvw : e z = d⁻¹ • (d • e z) := by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
    have hnv : ‖e z‖ = ‖d⁻¹‖ * ‖d • e z‖ := by rw [← norm_smul, ← hvw]
    have hsc : ∀ k, P k (e.symm (e z)) = P k (e.symm (d • e z)) * d⁻¹ ^ (n - k) := by
      intro k
      conv_lhs => rw [hvw, map_smul]
      have := coeff_charpoly_lmul_smul (F := F) (e.symm (d • e z)) (inv_ne_zero hd0) k
      rw [hn] at this
      exact this
    have hhv : h (e z) ≤ n := by
      calc h (e z) ≤ ∑ k ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
              show ‖P k (e.symm (e z))‖ ≤ 1
              rw [e.symm_apply_apply]; exact hz k
        _ = n := by simp
    by_cases hc1 : ‖d⁻¹‖ ≤ 1
    · calc ‖e z‖ = ‖d⁻¹‖ * ‖d • e z‖ := hnv
        _ ≤ 1 * ‖a‖ := mul_le_mul hc1 hwT.2 (norm_nonneg _) zero_le_one
        _ ≤ _ := by rw [one_mul]; exact hR
    · push_neg at hc1
      have hlow : ‖d⁻¹‖ * m ≤ h (e z) := by
        calc ‖d⁻¹‖ * m ≤ ‖d⁻¹‖ * h (d • e z) := mul_le_mul_of_nonneg_left (hm _ hwT) (norm_nonneg _)
          _ = ∑ k ∈ Finset.range n, ‖d⁻¹‖ * ‖P k (e.symm (d • e z))‖ := Finset.mul_sum _ _ _
          _ ≤ ∑ k ∈ Finset.range n, ‖P k (e.symm (e z))‖ := Finset.sum_le_sum fun k hk => by
              rw [hsc k, norm_mul, norm_pow, mul_comm]
              apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
              have hk' : 1 ≤ n - k := by have := Finset.mem_range.1 hk; omega
              calc ‖d⁻¹‖ = ‖d⁻¹‖ ^ 1 := (pow_one _).symm
                _ ≤ ‖d⁻¹‖ ^ (n - k) := pow_le_pow_right₀ hc1.le hk'
      have hcm : ‖d⁻¹‖ ≤ n / m := by rw [le_div_iff₀ hm0]; linarith
      calc ‖e z‖ = ‖d⁻¹‖ * ‖d • e z‖ := hnv
        _ ≤ (n / m) * ‖a‖ := mul_le_mul hcm hwT.2 (norm_nonneg _) (by positivity)
        _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)
  exact ((isCompact_closedBall 0 _).image hes).of_isClosed_subset hcl hsub

end GlobalTheory.JR.OKCompact
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.OKOpen

private theorem contCoeff {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem continuous_coeff {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (i : ℕ) :
    Continuous fun z : A.K => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i := by
  let b := Module.finBasis F A.K
  have h : (fun z : A.K => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i) =
      fun z => (LinearMap.toMatrix b b (Algebra.lmul F A.K z)).charpoly.coeff i := by
    funext z; rw [LinearMap.charpoly_toMatrix]
  rw [h]
  refine (contCoeff _ i).comp ?_
  refine continuous_pi fun r => continuous_pi fun s => ?_
  have hl : (fun z : A.K => LinearMap.toMatrix b b (Algebra.lmul F A.K z) r s) =
      fun z => (b.coord r) (z * b s) := by
    funext z; simp [LinearMap.toMatrix_apply]
  rw [hl]
  exact IsModuleTopology.continuous_of_linearMap ((b.coord r).comp (LinearMap.mulRight F (b s)))

theorem isOpen_OK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), IsOpen A.OK := by
  intro F E _ _ _ _ hU A
  haveI : IsUltrametricDist F := hU.ultraF
  have hset : A.OK = ⋂ i : Fin (Module.finrank F A.K + 1),
      (fun z : A.K => (LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i) ⁻¹' Metric.closedBall 0 1 := by
    ext z
    simp only [Et.OK, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro h i; exact h i
    · intro h i
      by_cases hi : i ≤ Module.finrank F A.K
      · exact h ⟨i, Nat.lt_succ_of_le hi⟩
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [LinearMap.charpoly_natDegree]; omega)]
        simp
  rw [hset]
  exact isOpen_iInter_of_finite fun i =>
    (IsUltrametricDist.isOpen_closedBall _ one_ne_zero).preimage (continuous_coeff A i)

end GlobalTheory.JR.OKOpen
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

open Polynomial

noncomputable section

namespace GlobalTheory.JR.Et

theorem charpoly_dvd_pow_of_aeval_zero {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : R[X]) (hp : aeval M p = 0) : M.charpoly ∣ p ^ Fintype.card n := by
  set a : Matrix n n R[X] := algebraMap R[X] (Matrix n n R[X]) X with ha_def
  set b : Matrix n n R[X] := (Algebra.ofId R R[X]).mapMatrix M with hb_def
  have hab : Commute a b := Algebra.commutes X b
  have key : ∀ q : R[X], ∃ H, (a - b) * H = aeval a q - aeval b q := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨H1, h1⟩ := hp
      obtain ⟨H2, h2⟩ := hq
      exact ⟨H1 + H2, by rw [mul_add, h1, h2, map_add (f := _), map_add (f := _)]; abel⟩
    | monomial k c =>
      refine ⟨algebraMap R (Matrix n n R[X]) c * ∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i), ?_⟩
      rw [aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc, hab.mul_geom_sum₂,
        mul_sub]
  obtain ⟨H, hH⟩ := key p
  have hb : aeval b p = 0 := by
    rw [hb_def, aeval_algHom_apply, hp, map_zero]
  have ha : aeval a p = algebraMap R[X] (Matrix n n R[X]) p := by
    rw [ha_def, aeval_algebraMap_apply, aeval_X_left_apply]
  have hch : (a - b).det = M.charpoly := rfl
  refine ⟨H.det, ?_⟩
  rw [← hch, ← Matrix.det_mul, hH, hb, sub_zero, ha, Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal]
  simp

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem aeval_self_charpoly_lmul (A : Et F E) (z : A.K) :
    aeval z (LinearMap.charpoly (Algebra.lmul F A.K z)) = 0 := by
  have h := LinearMap.aeval_self_charpoly (Algebra.lmul F A.K z)
  have h' : Algebra.lmul F A.K (aeval z (LinearMap.charpoly (Algebra.lmul F A.K z))) = 0 := by
    rw [← aeval_algHom_apply]; exact h
  simpa using congrArg (fun f : Module.End F A.K => f 1) h'

theorem mem_OK_iff_isIntegral [IsUltrametricDist F] (A : Et F E) (z : A.K) :
    z ∈ A.OK ↔ IsIntegral (NormedField.valuation (K := F)).integer z := by
  constructor
  · intro hz
    have hl : LinearMap.charpoly (Algebra.lmul F A.K z) ∈
        Polynomial.lifts (algebraMap (NormedField.valuation (K := F)).integer F) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro i
      refine ⟨⟨_, ?_⟩, rfl⟩
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
      exact_mod_cast hz i
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (LinearMap.charpoly_monic _)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap F, hq]
    exact aeval_self_charpoly_lmul A z
  · rintro ⟨p, hpm, hp⟩ i
    have hp' : aeval z (p.map (algebraMap (NormedField.valuation (K := F)).integer F)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]; exact hp
    have h1 : aeval (Algebra.lmul F A.K z) (p.map (algebraMap (NormedField.valuation (K := F)).integer F)) = 0 := by
      rw [aeval_algHom_apply, hp', map_zero]
    let bs := Module.finBasis F A.K
    have h2 : aeval (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul F A.K z))
        (p.map (algebraMap (NormedField.valuation (K := F)).integer F)) = 0 := by
      rw [aeval_algHom_apply, h1, map_zero]
    have h3 := charpoly_dvd_pow_of_aeval_zero _ _ h2
    have h4 : (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul F A.K z)).charpoly =
        LinearMap.charpoly (Algebra.lmul F A.K z) := LinearMap.charpoly_toMatrix _ bs
    rw [h4, ← Polynomial.map_pow] at h3
    have h5 := Polynomial.isIntegral_coeff_of_dvd _ _ (hpm.pow _) (LinearMap.charpoly_monic _) h3 i
    have h6 := (Valuation.integer.integers (NormedField.valuation (K := F))).mem_of_integral h5
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h6
    exact_mod_cast h6

theorem OK_isSubring : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), ∃ R : Subring A.K, (R : Set A.K) = A.OK := by
  intro F E _ _ _ _ hU A
  haveI : IsUltrametricDist F := hU.ultraF
  refine ⟨(integralClosure (NormedField.valuation (K := F)).integer A.K).toSubring, ?_⟩
  ext z
  exact (mem_OK_iff_isIntegral A z).symm

end GlobalTheory.JR.Et
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial Filter Topology Classical

variable {K : UQ} (B : InvAlg K) {ι : Type}

abbrev al (K : UQ) (a : K.O) : K.E := algebraMap K.O K.E a

def InDual (s : B.A) (M : Submodule K.O B.A) : Prop :=
  ∀ z ∈ M, Algebra.trace K.E B.A (s * z) ∈ (algebraMap K.O K.E).range

def indM (M : Submodule K.O B.A) (y : B.A) : ℚ := if y ∈ M then 1 else 0

def indD (M : Submodule K.O B.A) (s : B.A) : ℚ := if InDual B s M then 1 else 0

def dlt {A : Type} [CommMonoid A] (π : ι → A) (I : Finset ι) (f : A → ℚ) (y : A) : ℚ :=
  ∑ J ∈ I.powerset, (-1 : ℚ) ^ J.card * f ((∏ j ∈ J, π j) * y)

def term (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A) : ℚ :=
  dlt π I (indM B M) u * dlt π I' (indD B M) s

def HH (π : ι → B.A) (I I' : Finset ι) (u s : B.A) : ℚ :=
  ∑ᶠ M ∈ B.Lin, B.sgnLat M * term B π I I' u s M

def eS (e : ι → B.A) (I : Finset ι) : B.A := ∑ i ∈ I, e i

def Pos (a : K.O) (e : ι → B.A) (N : ℕ) (M : Submodule K.O B.A) (p : ι → ℤ) : Prop :=
  ∀ i, (∀ r : B.A, IsIntegral K.O r → (al K a ^ (p i + N)) • (e i * r) ∈ M) ∧
    ∀ m ∈ M, IsIntegral K.O ((al K a ^ (-p i)) • (e i * m))

def chi (e : ι → B.A) (I : Finset ι) (y : B.A) : ℚ :=
  K.eta (Algebra.norm K.E (y * eS B e I + (1 - eS B e I)))

def IsPre [Fintype ι] (e : ι → B.A) (S : Finset ι) : Prop :=
  CompleteOrthogonalIdempotents e ∧ ∀ i, ∃ f : B.A, IsIdempotentElem f ∧ f ≠ 0 ∧
    (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
    (i ∈ S → e i = f ∧ B.σ f = f) ∧ (i ∉ S → f * B.σ f = 0 ∧ e i = f + B.σ f)

def IsFrame [Fintype ι] (e π : ι → B.A) (S : Finset ι) : Prop :=
  IsPre B e S ∧ ∀ i ∈ S, B.Plus (π i) ∧ π i * (1 - e i) = 1 - e i ∧ K.eta (Algebra.norm K.E (π i)) = -1

def Win (I I' : Finset ι) (L k : ℕ) (p : ι → ℤ) : Prop :=
  ∀ i, -(L : ℤ) ≤ p i ∧ p i ≤ 2 * k + L ∧ (i ∈ I → 2 * (k : ℤ) - L ≤ p i) ∧ (i ∈ I' → p i ≤ L)

def Mid (S : Finset ι) (L k : ℕ) (p : ι → ℤ) : Prop :=
  ∀ i ∉ S, (L : ℤ) ≤ p i ∧ p i ≤ 2 * k - L

theorem eta_mul {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) : K.eta (x * y) = K.eta x * K.eta y := by
  unfold UQ.eta val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy), neg_add, zpow_add₀ (by norm_num)]

theorem eta_sq (x : K.E) : K.eta x * K.eta x = 1 := by
  unfold UQ.eta
  rw [← mul_zpow]; simp

theorem abs_eta (x : K.E) : |K.eta x| = 1 := by
  unfold UQ.eta; simp

theorem abs_indM (M : Submodule K.O B.A) (y : B.A) : |indM B M y| ≤ 1 := by
  unfold indM; split_ifs <;> simp

theorem abs_indD (M : Submodule K.O B.A) (y : B.A) : |indD B M y| ≤ 1 := by
  unfold indD; split_ifs <;> simp

theorem abs_dlt {A : Type} [CommMonoid A] (π : ι → A) (I : Finset ι) (f : A → ℚ) (hf : ∀ y, |f y| ≤ 1) (y : A) :
    |dlt π I f y| ≤ 2 ^ I.card := by
  unfold dlt
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ J ∈ I.powerset, |(-1 : ℚ) ^ J.card * f ((∏ j ∈ J, π j) * y)| ≤ ∑ J ∈ I.powerset, (1 : ℚ) :=
        Finset.sum_le_sum fun J _ => by rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]; exact hf _
    _ = 2 ^ I.card := by simp [Finset.card_powerset]

theorem abs_term (π : ι → B.A) (I I' : Finset ι) (u s : B.A) (M : Submodule K.O B.A) :
    |term B π I I' u s M| ≤ 2 ^ I.card * 2 ^ I'.card := by
  unfold term
  rw [abs_mul]
  exact mul_le_mul (abs_dlt _ _ _ (abs_indM B M) _) (abs_dlt _ _ _ (abs_indD B M) _) (abs_nonneg _) (by positivity)

theorem dlt_eq_zero {A : Type} [CommMonoid A] (π : ι → A) (I : Finset ι) (f : A → ℚ) (y : A) (i : ι) (hi : i ∈ I)
    (h : ∀ J ⊆ I.erase i, f (π i * ((∏ j ∈ J, π j) * y)) = f ((∏ j ∈ J, π j) * y)) : dlt π I f y = 0 := by
  unfold dlt
  rw [← Finset.insert_erase hi, Finset.sum_powerset_insert (Finset.notMem_erase i I)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun J hJ => ?_
  have hJ' : i ∉ J := fun h => Finset.notMem_erase i I (Finset.mem_powerset.1 hJ h)
  rw [Finset.prod_insert hJ', Finset.card_insert_of_notMem hJ', mul_assoc, h J (Finset.mem_powerset.1 hJ)]
  ring

end GlobalTheory.UnitLemma.Desc
end
end

section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.genEigenMultiplicityQuotient_additive_chain : ∀ {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (P Q S : Submodule k U), S ≤ Q → Q ≤ P → (∀ x ∈ P, T x ∈ P) → (∀ x ∈ Q, T x ∈ Q) → (∀ x ∈ S, T x ∈ S) → FiniteDimensional k (↥P ⧸ S.submoduleOf P) → ∀ x : k, gmult T P S x = gmult T P Q x + gmult T Q S x := by
  first | exact @GlobalTheory.PhiGam.GmultAdd.main | exact GlobalTheory.PhiGam.GmultAdd.main | (intros; apply GlobalTheory.PhiGam.GmultAdd.main <;> assumption)
end

section

namespace GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem condC_sh_and_nab_mem : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, CondC g N → ∀ a : ℤ, CondC g (sh a N) ∧ ∀ x ∈ sh a N, nab g x ∈ sh a N := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N hC a
  have h : ∀ x ∈ sh a N, nab g x ∈ sh a N := fun x hx => Window.nab_mem_sh R hg hC a hx
  exact ⟨(condC_iff_nab_mem g _).2 h, h⟩

end GlobalTheory.PhiGam
end
