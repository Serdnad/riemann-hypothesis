module

public import Formalism.RealPlaceAnalysis.Bundle001
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.RealPlaceAnalysis.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle087
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle027
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AestronglyMeasurableCompRep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle098
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace

namespace GlobalTheory

theorem uJ_col_sum {n : ℕ} (ε : Fin n → Bool) (h : Matrix (Fin n) (Fin n) ℂ) (hh : inUJ ε h)
    (j : Fin n) :
    ∑ i, (if ε i then (1 : ℝ) else -1) * ‖h i j‖ ^ 2 = if ε j then (1 : ℝ) else -1 := by
  have h1 := congrFun (congrFun hh j) j
  rw [Matrix.mul_apply] at h1
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq] at h1
  apply Complex.ofReal_injective
  push_cast
  have : ((if ε j then (1 : ℝ) else -1 : ℝ) : ℂ) = if ε j then (1 : ℂ) else -1 := by
    split_ifs <;> simp
  rw [this, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ((‖h i j‖ : ℝ) : ℂ) ^ 2 = star (h i j) * h i j := by
    rw [Complex.star_def, Complex.conj_mul']
  rw [h2]
  split_ifs <;> simp

theorem uJ_conjTranspose {n : ℕ} (ε : Fin n → Bool) (h : Matrix (Fin n) (Fin n) ℂ)
    (hh : inUJ ε h) : inUJ ε hᴴ := by
  have h1 := (uJInv n ε h hh).1
  have hJ : Jm ε * Jm ε = 1 := by
    simp only [Jm, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs <;> simp
  unfold inUJ
  rw [Matrix.conjTranspose_conjTranspose]
  calc h * Jm ε * hᴴ = h * (Jm ε * hᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Jm ε := by rw [h1, Matrix.one_mul]

theorem hs_le_of_cols (n : ℕ) (ε : Fin n → Bool) (s : Bool) (h : Matrix (Fin n) (Fin n) ℂ)
    (hh : inUJ ε h) :
    hs h ≤ n + 4 * ∑ i, ∑ j ∈ univ.filter (fun j => ε j = s), ‖h i j‖ ^ 2 := by
  set e : Fin n → ℝ := fun i => if ε i then (1 : ℝ) else -1 with he
  set σ : ℝ := if s then (1 : ℝ) else -1 with hσ
  have hc : ∀ j, ∑ i, e i * ‖h i j‖ ^ 2 = e j := uJ_col_sum ε h hh
  have hr : ∀ i, ∑ j, e j * ‖h i j‖ ^ 2 = e i := fun i => by
    have := uJ_col_sum ε hᴴ (uJ_conjTranspose ε h hh) i
    simpa only [Matrix.conjTranspose_apply, norm_star] using this
  have hee : ∀ i, e i * e i = 1 := fun i => by
    simp only [he]; split_ifs <;> simp
  have A : ∑ i, ∑ j, e i * (e j * ‖h i j‖ ^ 2) = n := by
    simp only [← Finset.mul_sum, hr, hee]
    simp
  have B : ∑ i, ∑ j, e j * ‖h i j‖ ^ 2 = ∑ i, ∑ j, e i * ‖h i j‖ ^ 2 := by
    rw [Finset.sum_comm (f := fun i j => e i * ‖h i j‖ ^ 2)]
    simp only [hr, hc]
  have C : ∑ i, ∑ j, (‖h i j‖ ^ 2 - e i * (e j * ‖h i j‖ ^ 2) + σ * (e j * ‖h i j‖ ^ 2)
      - σ * (e i * ‖h i j‖ ^ 2)) ≤ ∑ i, ∑ j, 4 * (if ε j = s then ‖h i j‖ ^ 2 else 0) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h0 : 0 ≤ ‖h i j‖ ^ 2 := by positivity
    simp only [he, hσ]
    cases ε i <;> cases ε j <;> cases s <;> simp <;> linarith
  have D : ∑ i, ∑ j, σ * (e j * ‖h i j‖ ^ 2) = ∑ i, ∑ j, σ * (e i * ‖h i j‖ ^ 2) := by
    have := congrArg (σ * ·) B
    simpa only [Finset.mul_sum] using this
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at C
  rw [A, D] at C
  simp only [Finset.sum_filter, Finset.mul_sum, hs]
  linarith

end GlobalTheory
end

section

open Formalism.REAL Finset
open scoped InnerProductSpace

namespace GlobalTheory.AlgStep

theorem sqrt_nsq_eq_norm {n : ℕ} (u : Fin n → ℝ) :
    Real.sqrt (nsq u) = ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [nsq, dot, sq]

theorem sqrt_nsq_add_le {n : ℕ} (u v : Fin n → ℝ) :
    Real.sqrt (nsq (u + v)) ≤ Real.sqrt (nsq u) + Real.sqrt (nsq v) := by
  simp only [sqrt_nsq_eq_norm, WithLp.toLp_add]
  exact norm_add_le _ _

theorem nsq_nonneg' {n : ℕ} (u : Fin n → ℝ) : 0 ≤ nsq u := by
  unfold nsq dot
  exact Finset.sum_nonneg fun a _ => mul_self_nonneg (u a)

theorem sum_range_sub_sq (c : ℝ) (n : ℕ) :
    ∑ i ∈ range n, (c - (i : ℝ)) * (c - (i : ℝ)) =
      n * c ^ 2 - c * n * (n - 1) + (n - 1) * n * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem nsq_rho_le {n : ℕ} (ε : Fin n → Bool) : nsq (rhoC ε + rhoN ε) ≤ (n : ℝ) ^ 3 / 12 := by
  have h : nsq (rhoC ε + rhoN ε) =
      ∑ i ∈ range n, (((n : ℝ) - 1) / 2 - (i : ℝ)) * (((n : ℝ) - 1) / 2 - (i : ℝ)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => (((n : ℝ) - 1) / 2 - (i : ℝ)) * (((n : ℝ) - 1) / 2 - (i : ℝ)))]
    unfold nsq dot
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.add_apply, half_sum_roots_standard n ε a]
  rw [h, sum_range_sub_sq]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem casK_form_le (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) (M : ℝ) (hfin : FiniteDimensional ℂ S)
    (hr : KRel ε F) (hu : KUnit ε F) (hS : KStable ε F S)
    (hw : ∀ (μ : Fin n → ℝ), ∀ x ∈ S, x ≠ 0 → KHighest ε F μ x → ckv ε μ ≤ M) :
    ∀ y ∈ S, (⟪y, CasK ε F y⟫_ℂ).re ≤ M * ‖y‖ ^ 2 := by
  intro y hy
  obtain ⟨m, x, μ, h1, h2, h3⟩ := kDecomp V n ε F S hfin hr hu hS
  have hy' : y ∈ ⨆ i ∈ (univ : Finset (Fin m)), kSpan ε F (x i) := by simpa [h3] using hy
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ y).1 hy'
  have hC : CasK ε F y = ∑ i, ((ckv ε (μ i) : ℝ) : ℂ) • (v i : V) := by

    rw [← hv, map_sum]
    exact Finset.sum_congr rfl fun i _ => kCasSpan V n ε F (μ i) (x i) hr (h1 i).2.2 _ (v i).2
  have key : ∀ c : Fin m → ℂ,
      ⟪y, ∑ i, c i • (v i : V)⟫_ℂ = ∑ i, c i * ⟪(v i : V), (v i : V)⟫_ℂ := by
    intro c
    rw [← hv, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum, Finset.sum_eq_single j]
    · rw [inner_smul_right]
    · intro i _ hij
      rw [inner_smul_right, h2 j i (Ne.symm hij) _ (v j).2 _ (v i).2, mul_zero]
    · simp
  have hvv : ∀ i, ⟪(v i : V), (v i : V)⟫_ℂ = ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hn : ‖y‖ ^ 2 = ∑ i, ‖(v i : V)‖ ^ 2 := by
    have h := key (fun _ => 1)
    simp only [one_smul, one_mul, hv, inner_self_eq_norm_sq_to_K] at h
    apply Complex.ofReal_injective
    push_cast
    exact h
  have key2 := key (fun i => ((ckv ε (μ i) : ℝ) : ℂ))
  rw [hC, key2]
  simp only [hvv]
  have hre : (∑ i, ((ckv ε (μ i) : ℝ) : ℂ) * ((‖(v i : V)‖ ^ 2 : ℝ) : ℂ)).re =
      ∑ i, ckv ε (μ i) * ‖(v i : V)‖ ^ 2 := by
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hre, hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact hw (μ i) (x i) (h1 i).1 (h1 i).2.1 (h1 i).2.2

theorem sqrt_nsq_le_of_abs_le {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (h : ∀ a, |lam a| ≤ b ^ 2) :
    Real.sqrt (nsq lam) ≤ (n : ℝ) ^ (1 / 2 : ℝ) * b ^ 2 := by
  have h1 : nsq lam ≤ (n : ℝ) * (b ^ 2) ^ 2 := by
    have : ∑ a : Fin n, lam a * lam a ≤ ∑ _a : Fin n, (b ^ 2) ^ 2 := by
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (h a) 2
    simpa [nsq, dot] using this
  rw [← Real.sqrt_eq_rpow]
  refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq (sq_nonneg b)]

end GlobalTheory.AlgStep

namespace GlobalTheory

open GlobalTheory.AlgStep

theorem algebraic_step_bound : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ)
    (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V) (b : ℝ),
    GlRel E → IsUnitary ε E → KindA ε E lam u → (∀ a, |lam a| ≤ b ^ 2) →
    ∀ (j : ℕ), ∀ x ∈ pfil ε E u j,
      ∑ a, ∑ c, ‖E a c x‖ ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j ^ 2 * ‖x‖ ^ 2 := by
  intro V _ _ n ε E lam u b hg hu hk hb j x hx
  obtain ⟨hhi, hcas, hfin⟩ := hk
  obtain ⟨-, -, hst, -, hcyc, -, hfd⟩ := pfilFacts V n ε E u hg
  set L := Real.sqrt (nsq lam) with hL
  set A := Real.sqrt (nsq (rhoN ε)) + Real.sqrt 2 * j with hA
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := by positivity
  have hK := casK_form_le V n ε E (pfil ε E u j) ((L + A) ^ 2) (hfd hfin j) (glRel_kRel ε E hg)
    (isUnitary_kUnit ε E hu) (hst j) (by
      intro μ y hy hy0 hyh
      have h1 := GlobalTheory.KTypeSteps.ktypes_within_steps V n ε E (LamOf ε lam) u hg hu hhi hfin j μ y hy hy0 hyh
      have h2 : μ + rhoC ε = (lam + rhoN ε) + (μ - LamOf ε lam) := by
        unfold LamOf; ring
      have h3 : Real.sqrt (nsq (μ + rhoC ε)) ≤ L + A := by
        rw [h2]
        have := sqrt_nsq_add_le (lam + rhoN ε) (μ - LamOf ε lam)
        have := sqrt_nsq_add_le lam (rhoN ε)
        linarith
      have h4 := (Real.sqrt_le_iff.mp h3).2
      have h5 := nsq_nonneg' (rhoC ε)
      unfold ckv
      linarith) x hx
  have hC : Cas E x = ((cvalR ε lam : ℝ) : ℂ) • x := casOnCyc V n E _ u hg hcas x (hcyc j hx)
  have hS := congrArg Complex.re (sumOfSquaresIdentity_holds V n ε E x hu)
  have hxx : ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [Complex.ofReal_re, LinearMap.sub_apply, two_smul, LinearMap.add_apply, hC, inner_sub_right,
    inner_add_right, inner_smul_right, hxx, ← Complex.ofReal_mul, Complex.sub_re, Complex.add_re,
    Complex.ofReal_re] at hS
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have har := rhoN_norm_le_and_casimir_arith.2 L A n hL0 hA0 hn
  have hr := rhoN_norm_le_and_casimir_arith.1 n ε
  have hp : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hn _
  have hLb := sqrt_nsq_le_of_abs_le lam b hb
  have h2 : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hj : Real.sqrt 2 * j ≤ 3 / 2 * j := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg j)
  have hle : L + 2 * A + 0.3 * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst
    linarith
  have hsq : (L + 2 * A + 0.3 * (n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j ^ 2 :=
    pow_le_pow_left₀ (by positivity) hle 2
  have hL2 : L ^ 2 = nsq lam := Real.sq_sqrt (nsq_nonneg' lam)
  have hrho := nsq_rho_le ε
  have hc : 2 * (L + A) ^ 2 - cvalR ε lam ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b j ^ 2 := by
    unfold cvalR
    linarith
  have := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖)
  rw [hS]
  linarith

end GlobalTheory
end

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory

theorem rowsAut_idem_elementary : ∀ B : RowsAut,
    (B.e 1).im = 0 ∧ 0 ≤ (B.e 1).re ∧ (∀ y, ‖B.e y‖ ≤ (B.e 1).re) ∧ Continuous B.e := by
  intro B
  obtain ⟨hlc, -, hstar, hpos, -⟩ := B.e_adm

  have him : (B.e 1).im = 0 := by
    have h := congrArg Complex.im (hstar 1)
    rw [inv_one, Complex.star_def, Complex.conj_im] at h
    linarith

  have hre : 0 ≤ (B.e 1).re := by
    have h := hpos 1 (fun _ => 1) (fun _ => 1)
    simp only [Fin.sum_univ_one, star_one, one_mul, inv_one] at h
    exact (Complex.nonneg_iff.mp h).1
  refine ⟨him, hre, ?_, hlc.continuous⟩
  intro y
  set a := (B.e 1).re with ha
  have h1 : B.e 1 = (a : ℂ) := Complex.ext (by simp [ha]) (by simp [him])
  set b := B.e y with hb
  have hyi : B.e y⁻¹ = star b := hstar y
  have key : star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    ring
  have hs : star ((‖b‖ : ℝ) : ℂ) = ((‖b‖ : ℝ) : ℂ) := Complex.conj_ofReal _

  have h := hpos 2 ![1, y] ![b, -((‖b‖ : ℝ) : ℂ)]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    inv_one, one_mul, mul_one, inv_mul_cancel, hyi, h1, star_neg, hs] at h
  have hE : star b * b * (a : ℂ) + star b * -((‖b‖ : ℝ) : ℂ) * b +
      (-((‖b‖ : ℝ) : ℂ) * b * star b + -((‖b‖ : ℝ) : ℂ) * -((‖b‖ : ℝ) : ℂ) * (a : ℂ)) =
      ((2 * ‖b‖ ^ 2 * (a - ‖b‖) : ℝ) : ℂ) := by
    push_cast at key ⊢
    linear_combination ((a : ℂ) - 2 * ((‖b‖ : ℝ) : ℂ)) * key
  rw [hE, Complex.zero_le_real] at h
  refine le_of_not_gt fun hlt => ?_
  have hb0 : 0 < ‖b‖ := lt_of_le_of_lt hre hlt
  have hneg : 2 * ‖b‖ ^ 2 * (a - ‖b‖) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
  linarith

end GlobalTheory
end

section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.RightRegProps


open GlobalTheory.RightRegFund in
theorem rightReg_unitary_mul_continuous : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R → R 1 = ContinuousLinearMap.id ℂ _ ∧ (∀ x y, R (x * y) = (R x).comp (R y)) ∧ (∀ x F, ‖R x F‖ = ‖F‖) ∧ ∀ F, Continuous fun x => R x F := by
  intro I μf _ _ fund hfund R hR
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨Γ, hΓ, hc, -, hfd⟩ := GlobalTheory.RatDiscrete.rational_points I
  obtain ⟨hl, hrt, -⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular I μf
  have hD := hfd μf fund hfund
  have : BorelSpace I.GA := inferInstance
  have : (I.muA μf).IsMulLeftInvariant := ⟨hl⟩
  have : (I.muA μf).IsMulRightInvariant := ⟨hrt⟩
  have : IsFiniteMeasureOnCompacts (I.muA μf) := by
    unfold AutInst.muA; infer_instance
  have hr : ∀ y, ∃ γ : Γ, I.rep fund y = (γ : I.GA) * y ∧ I.rep fund y ∈ fund := by
    intro y
    have h := hfund.2.1 y
    have e : I.rep fund y = h.choose * y := by
      unfold AutInst.rep; exact dif_pos h
    have hm : h.choose ∈ (Γ : Set I.GA) := by
      have k := h.choose_spec.1
      generalize h.choose = z at k ⊢
      rw [hΓ]; exact k
    exact ⟨⟨h.choose, hm⟩, e, e ▸ h.choose_spec.2⟩
  exact ⟨GlobalTheory.RightRegFund.map_one hD hfund.1 hr hR, GlobalTheory.RightRegFund.map_mul hD hfund.1 hr hR,
    GlobalTheory.RightRegFund.norm_map hD hfund.1 hr hR, GlobalTheory.RightRegFund.continuous_map hD hfund.1 hr hR⟩

end GlobalTheory.RightRegProps
end

section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory.RatDiscrete

theorem subgroup_countable_discrete : ∀ (I : AutInst), (∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset) ∧ I.GFset.Countable ∧ ∀ C : Set I.GA, IsCompact C → (I.GFset ∩ C).Finite :=
  fun I => ⟨⟨ratSub I, rfl⟩, countable_GFset I,
    fun _ hC => Set.inter_comm _ _ ▸ finite_inter I hC⟩

end GlobalTheory.RatDiscrete
end

section

open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain : ∀ I : AutInst, ∃ Γ : Subgroup I.GA, (Γ : Set I.GA) = I.GFset ∧ Countable Γ ∧ (∀ C : Set I.GA, IsCompact C → (C ∩ I.GFset).Finite) ∧ ∀ (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → IsFundamentalDomain Γ fund (I.muA μf) := by
  first | exact @GlobalTheory.RatDiscrete.rational_points | exact GlobalTheory.RatDiscrete.rational_points | (intros; apply GlobalTheory.RatDiscrete.rational_points <;> assumption)
end

section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.strong_approximation_unitaryUnipotentRadical : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)), I.IsIsot W → (∃ N : Subgroup I.GA, (N : Set I.GA) = I.NA W) ∧ IsClosed (I.NA W) ∧ (∀ m ∈ I.NA W, ((m.1, 1) : I.GA) ∈ I.NA W ∧ ((1, m.2) : I.GA) ∈ I.NA W) ∧ (∀ U : Set I.Gf, U ∈ nhds (1 : I.Gf) → ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset ∩ I.NA W, (γ⁻¹ * m).2 ∈ U) ∧ ∃ Cp : Set I.GA, IsCompact Cp ∧ Cp ⊆ I.NA W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset ∩ I.NA W, γ⁻¹ * m ∈ Cp := by
  first | exact @GlobalTheory.UnipApprox.strong_approximation | exact GlobalTheory.UnipApprox.strong_approximation | (intros; apply GlobalTheory.UnipApprox.strong_approximation <;> assumption)
end

section

namespace GlobalTheory.ProjectiveRetraction

open NumberField

theorem exists_retraction_of_projective {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [Module.Projective R (M ⧸ N)] :
    ∃ p : M →ₗ[R] M, (∀ x, p x ∈ N) ∧ ∀ x ∈ N, p x = x := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ (LinearMap.id : (M ⧸ N) →ₗ[R] (M ⧸ N))
    N.mkQ_surjective
  refine ⟨LinearMap.id - s ∘ₗ N.mkQ, fun x => ?_, fun x hx => ?_⟩
  · have h1 : N.mkQ (s (N.mkQ x)) = N.mkQ x := LinearMap.congr_fun hs (N.mkQ x)
    have h2 : N.mkQ (x - s (N.mkQ x)) = 0 := by rw [map_sub, h1, sub_self]
    exact (Submodule.Quotient.mk_eq_zero N).1 h2
  · have h0 : N.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero N).2 hx
    show x - s (N.mkQ x) = x
    rw [h0, map_zero, sub_zero]

theorem exists_retraction {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (M0 L : Submodule (𝓞 E) V) (hL : L.FG)
    (h : Formalism.MainNotions.S.Lat.IsPrimitiveSub M0 L) :
    ∃ r : L →ₗ[𝓞 E] M0, ∀ x : M0, r ⟨(x : V), h.1 x.2⟩ = x := by
  set N : Submodule (𝓞 E) L := M0.comap L.subtype with hN
  have hsat : ∀ (a : 𝓞 E), a ≠ 0 → ∀ x : L, a • x ∈ N → x ∈ N := by
    intro a ha x hx
    have hx' : a • (x : V) ∈ M0 := hx
    have ha' : (algebraMap (𝓞 E) E a) ≠ 0 := by
      intro h0
      exact ha ((IsFractionRing.injective (𝓞 E) E) (by rw [h0, map_zero]))
    have h1 : (algebraMap (𝓞 E) E a) • (x : V) ∈ Submodule.span E (M0 : Set V) := by
      rw [algebraMap_smul]
      exact Submodule.subset_span hx'
    have h2 : (x : V) ∈ Submodule.span E (M0 : Set V) :=
      (Submodule.smul_mem_iff _ ha').1 h1
    show (x : V) ∈ M0
    rw [h.2]
    exact ⟨x.2, h2⟩
  have htor : Submodule.torsion (𝓞 E) (L ⧸ N) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := N.mkQ_surjective q
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hq
    have ha2 : N.mkQ ((a : 𝓞 E) • x) = 0 := by
      rw [map_smul]
      exact ha
    have hx : x ∈ N :=
      hsat a (nonZeroDivisors.ne_zero a.2) x ((Submodule.Quotient.mk_eq_zero N).1 ha2)
    exact (Submodule.Quotient.mk_eq_zero N).2 hx
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  haveI : Module.Flat (𝓞 E) (L ⧸ N) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  haveI : Module.FinitePresentation (𝓞 E) (L ⧸ N) := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) (L ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨p, hp1, hp2⟩ := exists_retraction_of_projective N
  refine ⟨LinearMap.codRestrict M0 (L.subtype ∘ₗ p) (fun x => hp1 x), fun x => ?_⟩
  apply Subtype.ext
  have hx : (⟨(x : V), h.1 x.2⟩ : L) ∈ N := x.2
  show ((p ⟨(x : V), h.1 x.2⟩ : L) : V) = x
  rw [hp2 _ hx]

end GlobalTheory.ProjectiveRetraction
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianDatum_eq_of_same_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d d' : LocNG.Datum P) (τ τ' : Term V M r), LocNG.IsTermOver P d τ → LocNG.IsTermOver P d' τ' → τ.abelian₂ = τ'.abelian₂ → d = d' := by
  first | exact @GlobalTheory.HL.LatUniq.datum_of_lattice | exact GlobalTheory.HL.LatUniq.datum_of_lattice | (intros; apply GlobalTheory.HL.LatUniq.datum_of_lattice <;> assumption)
end
