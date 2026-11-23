module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
public import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.PeriodIntegrals.Bundle018
public import Formalism.HermitianCurvature.StatementB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.PeriodIntegrals.Bundle004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle061
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle060
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Lemma
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
public import Mathlib.Analysis.Calculus.Deriv.Slope
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.StatementQ
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.Bundle001

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompactStable

open PI.UpqRep

theorem deriv_mem {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (S : Submodule ℂ H) [FiniteDimensional ℂ S]
    {f : ℝ → H} {f' : H} (hf : HasDerivAt f f' 0) (hS : ∀ t, f t ∈ S) : f' ∈ S := by
  have hcl : IsClosed (S : Set H) := S.closed_of_finiteDimensional
  have hsl := hasDerivAt_iff_tendsto_slope_zero.mp hf
  refine hcl.mem_of_tendsto hsl (Filter.Eventually.of_forall fun t => ?_)
  exact S.smul_of_tower_mem t⁻¹ (S.sub_mem (hS _) (hS _))

variable {k r : ℕ}

private lemma real_smul_skew_and_commute {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (hc : M * X = X * M)
    (t : ℝ) : ((t : ℂ) • X)ᴴ = -((t : ℂ) • X) ∧ M * ((t : ℂ) • X) = ((t : ℂ) • X) * M := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, hX, Complex.star_def, Complex.conj_ofReal, smul_neg]
  · rw [Matrix.mul_smul, hc, Matrix.smul_mul]

private lemma exp_real_smul_mem_UJset_of_inG {n : ℕ} (M Y : Matrix (Fin n) (Fin n) ℂ) (hY : Yᴴ = -Y) (hc : M * Y = Y * M) :
    NormedSpace.exp Y ∈ UH M ∩ (Matrix.unitaryGroup (Fin n) ℂ : Set _) := by
  have hu : (NormedSpace.exp Y)ᴴ * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_conjTranspose, hY, ← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  have hcm : Commute M (NormedSpace.exp Y) := Commute.exp_right hc
  refine ⟨?_, ?_⟩
  · show (NormedSpace.exp Y)ᴴ * M * NormedSpace.exp Y = M
    rw [Matrix.mul_assoc, hcm.eq, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    exact hu

theorem dsig_mem (R : Rep k r) (S : Submodule ℂ R.H) [FiniteDimensional ℂ S]
    (hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S)
    {X : Mx k r} (hX : Xᴴ = -X) (hc : Hpk k r * X = X * Hpk k r) {v : R.H} (hv : v ∈ S) (hsm : v ∈ R.sm) :
    dsig (k := k) (r := r) R.σ X v ∈ S := by
  have hmem : ∀ t : ℝ, R.σ (NormedSpace.exp ((t : ℂ) • X)) v ∈ S := fun t =>
    hS _ (exp_real_smul_mem_UJset_of_inG _ _ (real_smul_skew_and_commute _ _ hX hc t).1 (real_smul_skew_and_commute _ _ hX hc t).2) v hv
  show deriv (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) 0 ∈ S
  by_cases hd : DifferentiableAt ℝ (fun t : ℝ => R.σ (NormedSpace.exp ((t : ℂ) • X)) v) 0
  · exact deriv_mem S hd.hasDerivAt hmem
  · rw [deriv_zero_of_not_differentiableAt hd]
    exact S.zero_mem

private lemma herm_eq_sum_star_mul_mulVec {n : ℕ} (M Y : Matrix (Fin n) (Fin n) ℂ) (h1 : Mᴴ = M) (h2 : M * M = 1)
    (hc : M * Y = Y * M) : M * Yᴴ * M = Yᴴ ∧ M * Yᴴ = Yᴴ * M := by
  have hs : Yᴴ * M = M * Yᴴ := by
    have h0 := congrArg Matrix.conjTranspose hc
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, h1] at h0
  refine ⟨?_, hs.symm⟩
  rw [← hs, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem dC_mem (R : Rep k r) (S : Submodule ℂ R.H) [FiniteDimensional ℂ S]
    (hS : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S, R.σ g x ∈ S)
    (h1 : (Hpk k r)ᴴ = Hpk k r) (h2 : Hpk k r * Hpk k r = 1)
    {Y : Mx k r} (hc : Hpk k r * Y = Y * Hpk k r) {v : R.H} (hv : v ∈ S) (hsm : v ∈ R.sm) :
    R.dC Y v ∈ S := by
  have hH : Formalism.QuantumDeterminants.Hpk k r = Hpk k r := rfl
  obtain ⟨hθ, hcs⟩ := herm_eq_sum_star_mul_mulVec _ Y h1 h2 hc
  have e1 : ((1 / 2 : ℂ) • (Y + -Yᴴ))ᴴ = -((1 / 2 : ℂ) • (Y + -Yᴴ)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_conjTranspose, ← smul_neg]
    congr 1
    · simp
    · abel
  have hI : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [Complex.star_def, map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat, mul_neg, div_neg]
  have e2 : ((1 / (2 * Complex.I)) • (Y - -Yᴴ))ᴴ = -((1 / (2 * Complex.I)) • (Y - -Yᴴ)) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_conjTranspose, hI, neg_smul]
    congr 2
    abel
  have c1 : Hpk k r * ((1 / 2 : ℂ) • (Y + -Yᴴ)) = ((1 / 2 : ℂ) • (Y + -Yᴴ)) * Hpk k r := by
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, mul_neg, neg_mul, hc, hcs]
  have c2 : Hpk k r * ((1 / (2 * Complex.I)) • (Y - -Yᴴ)) =
      ((1 / (2 * Complex.I)) • (Y - -Yᴴ)) * Hpk k r := by
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_neg, neg_mul, hc, hcs]
  unfold BranchingSupport.Rep.dC
  rw [hH, hθ]
  exact S.add_mem (dsig_mem R S hS e1 c1 hv hsm) (S.smul_mem _ (dsig_mem R S hS e2 c2 hv hsm))

theorem Jm_single {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (h : ε a = ε b) :
    Jm ε * Matrix.single a b (1 : ℂ) = Matrix.single a b 1 * Jm ε := by
  ext i j
  simp only [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  split_ifs <;> simp_all

private lemma unitary_conj_mem_and_commute_Jmat {n : ℕ} (Jmat M Q g : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hcay : Qᴴ * Jmat * Q = M)
    (hg : g ∈ UH M ∩ (Matrix.unitaryGroup (Fin n) ℂ : Set _)) :
    Q * g * Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ Q * g * Qᴴ * Jmat = Jmat * (Q * g * Qᴴ) ∧
      Qᴴ * (Q * g * Qᴴ) * Q = g := by
  obtain ⟨hgM, hgU⟩ := hg
  have hgM' : gᴴ * M * g = M := hgM
  have q1 : Qᴴ * Q = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff'.mp hQ
    rwa [Matrix.star_eq_conjTranspose] at h0
  have q2 : Q * Qᴴ = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff.mp hQ
    rwa [Matrix.star_eq_conjTranspose] at h0
  have g2 : g * gᴴ = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff.mp hgU
    rwa [Matrix.star_eq_conjTranspose] at h0
  have hJ : Jmat = Q * M * Qᴴ := by
    rw [← hcay]
    calc Jmat = (Q * Qᴴ) * Jmat * (Q * Qᴴ) := by rw [q2, Matrix.one_mul, Matrix.mul_one]
      _ = Q * (Qᴴ * Jmat * Q) * Qᴴ := by simp only [Matrix.mul_assoc]
  have hgc : M * g = g * M := by
    calc M * g = (g * gᴴ) * M * g := by rw [g2, Matrix.one_mul]
      _ = g * (gᴴ * M * g) := by simp only [Matrix.mul_assoc]
      _ = g * M := by rw [hgM']
  refine ⟨?_, ?_, ?_⟩
  · have hs : Qᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
      exact q1
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hQ hgU) hs
  · rw [hJ]
    calc Q * g * Qᴴ * (Q * M * Qᴴ) = Q * g * (Qᴴ * Q) * M * Qᴴ := by simp only [Matrix.mul_assoc]
      _ = Q * (M * g) * Qᴴ := by
          rw [q1, Matrix.mul_one, hgc]
          simp only [Matrix.mul_assoc]
      _ = Q * M * (Qᴴ * Q) * g * Qᴴ := by
          rw [q1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = Q * M * Qᴴ * (Q * g * Qᴴ) := by simp only [Matrix.mul_assoc]
  · calc Qᴴ * (Q * g * Qᴴ) * Q = (Qᴴ * Q) * g * (Qᴴ * Q) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [q1, Matrix.one_mul, Matrix.mul_one]

theorem kStable_smooth_and_stable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → ∀ S : Submodule ℂ R.H, FiniteDimensional ℂ S → PI.UpqRep.IsKStableOn ε (fun g => R.σ (Q⁻¹ * g * Q)) S → (∀ v ∈ S, R.KFin v ∧ v ∈ R.sm) ∧ ∀ a b, ε a = ε b → ∀ v ∈ S, R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v ∈ S := by
  intro hK k r ε mu R hR Q hQ S hfin hKS
  obtain ⟨⟨-, hcay⟩, hQU⟩ := hQ
  obtain ⟨-, -, -, -, hTKsm, -, hKTK, -, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR
  have q1 : Qᴴ * Q = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff'.mp hQU
    rwa [Matrix.star_eq_conjTranspose] at h0
  have q2 : Q * Qᴴ = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff.mp hQU
    rwa [Matrix.star_eq_conjTranspose] at h0
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv q1
  have hS' : ∀ g ∈ UH (Hpk k r) ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _), ∀ x ∈ S,
      R.σ g x ∈ S := by
    intro g hg x hx
    obtain ⟨hu, hc, he⟩ := unitary_conj_mem_and_commute_Jmat _ _ Q g hQU hcay hg
    have hk : Q * g * Qᴴ ∈ Kset ε := by
      simp only [Kset, Set.mem_ofPred_eq]
      exact ⟨hu, hc⟩
    have h0 := hKS (Q * g * Qᴴ) hk x hx
    simp only [hinv, he] at h0
    exact h0
  have hsm : ∀ v ∈ S, R.KFin v ∧ v ∈ R.sm := by
    intro v hv
    have hkf : R.KFin v := by
      simp only [BranchingSupport.Rep.KFin, PI.UpqRep.IsKFinHpk]
      exact ⟨S, hfin, hv, hS'⟩
    exact ⟨hkf, hTKsm v (hKTK v hkf)⟩
  refine ⟨hsm, fun a b hab v hv => ?_⟩
  have h1 : (Hpk k r)ᴴ = Hpk k r := by
    rw [← hcay, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Jm_conjTranspose]
    simp only [Matrix.mul_assoc]
  have h2 : Hpk k r * Hpk k r = 1 := by
    rw [← hcay]
    calc Qᴴ * Jm ε * Q * (Qᴴ * Jm ε * Q) = Qᴴ * Jm ε * (Q * Qᴴ) * Jm ε * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [q2, Matrix.mul_one, Matrix.mul_assoc (Qᴴ) (Jm ε), Jm_mul_self, Matrix.mul_one, q1]
  have hc : Hpk k r * (Q⁻¹ * Matrix.single a b 1 * Q) = (Q⁻¹ * Matrix.single a b 1 * Q) * Hpk k r := by
    rw [hinv, ← hcay]
    calc Qᴴ * Jm ε * Q * (Qᴴ * Matrix.single a b 1 * Q)
        = Qᴴ * Jm ε * (Q * Qᴴ) * Matrix.single a b 1 * Q := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * (Jm ε * Matrix.single a b 1) * Q := by
          rw [q2, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = Qᴴ * (Matrix.single a b 1 * Jm ε) * Q := by rw [Jm_single ε hab]
      _ = Qᴴ * Matrix.single a b 1 * (Q * Qᴴ) * Jm ε * Q := by
          rw [q2, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = Qᴴ * Matrix.single a b 1 * Q * (Qᴴ * Jm ε * Q) := by simp only [Matrix.mul_assoc]
  exact dC_mem R S hS' h1 h2 hc hv (hsm v hv).2

end GlobalTheory.CompactStable
end

section

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory.StdGrid

theorem half_le_of_lt {x y : ℝ} (m : ℤ) (h : y - x = (m : ℝ) + 1 / 2) (hlt : x < y) : x + 1 / 2 ≤ y := by
  have h1 : (-1 : ℝ) < (m : ℝ) := by linarith
  have h2 : (-1 : ℤ) < m := by exact_mod_cast h1
  have h3 : (0 : ℤ) ≤ m := by omega
  have h4 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h3
  linarith

theorem scale_bounds {Ch b ka T : ℝ} (r : ℕ) (hb : 1 ≤ b) (hka : 0 < ka) (h1 : ka ≤ b ^ Ch) (h2 : ka⁻¹ ≤ b ^ Ch)
    (h3 : 1 ≤ T * (1 / ka) ^ (2 * r)) (h4 : T * (1 / ka) ^ (2 * r) ≤ b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ))) :
    b ^ (-((2 * |Ch|) * ((2 * r + 2 : ℕ) : ℝ))) ≤ T ∧ T ≤ b ^ ((2 * |Ch|) * ((2 * r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have hC : Ch ≤ |Ch| := le_abs_self _
  have hC0 : 0 ≤ |Ch| := abs_nonneg _
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hbC : b ^ Ch ≤ b ^ |Ch| := Real.rpow_le_rpow_of_exponent_le hb hC
  have hpow : ∀ x : ℝ, 0 ≤ x → x ≤ b ^ Ch → x ^ (2 * r) ≤ b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) := by
    intro x hx hxb
    calc x ^ (2 * r) ≤ (b ^ |Ch|) ^ (2 * r) := pow_le_pow_left₀ hx (hxb.trans hbC) _
      _ = b ^ (|Ch| * ((2 * r : ℕ) : ℝ)) := by rw [Real.rpow_mul hb0.le, Real.rpow_natCast]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hb
        apply mul_le_mul_of_nonneg_left _ hC0
        push_cast; linarith
  have hm : (0 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  set m : ℝ := ((2 * r + 2 : ℕ) : ℝ) with hmdef
  have hk1 := hpow ka hka.le h1
  have hk2 := hpow (1 / ka) (by positivity) (by rwa [one_div])
  have hq : 0 < (1 / ka) ^ (2 * r) := by positivity
  have hT : 0 < T := by
    by_contra hneg
    push_neg at hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg hq.le
    linarith
  have hTe : T = T * (1 / ka) ^ (2 * r) * ka ^ (2 * r) := by
    rw [mul_assoc, ← mul_pow, one_div_mul_cancel hka.ne', one_pow, mul_one]
  have hE : 0 < b ^ (|Ch| * m) := Real.rpow_pos_of_pos hb0 _
  constructor
  · have h5 : 1 ≤ T * b ^ (|Ch| * m) := h3.trans (mul_le_mul_of_nonneg_left hk2 hT.le)
    have h6 : b ^ (|Ch| * m) ≤ b ^ ((2 * |Ch|) * m) := by
      apply Real.rpow_le_rpow_of_exponent_le hb
      nlinarith [mul_nonneg hC0 hm]
    have h7 : 1 ≤ T * b ^ ((2 * |Ch|) * m) := h5.trans (mul_le_mul_of_nonneg_left h6 hT.le)
    rw [Real.rpow_neg hb0.le, inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos hb0 _)]
    exact h7
  · have h5 : b ^ (Ch * m) ≤ b ^ (|Ch| * m) :=
      Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right hC hm)
    calc T = T * (1 / ka) ^ (2 * r) * ka ^ (2 * r) := hTe
      _ ≤ b ^ (|Ch| * m) * b ^ (|Ch| * m) := mul_le_mul (h4.trans h5) hk1 (by positivity) hE.le
      _ = _ := by rw [← Real.rpow_add hb0]; congr 1; ring

theorem cut_gap {k : ℕ} {u u' : Fin k → ℝ} {L : ℝ} (hL : 0 ≤ L) (h : HasCut u u' L) : ∃ l, L ≤ |u l - u' l| := by
  obtain ⟨a, b, ⟨l, a', b', _, hab, hI, h1, h2, _⟩, hLb⟩ := h
  have ha : a ∈ Set.Icc a' b' := hI ▸ (⟨le_rfl, by linarith⟩ : a ∈ Set.Icc a b)
  have hb : b ∈ Set.Icc a' b' := hI ▸ (⟨by linarith, le_rfl⟩ : b ∈ Set.Icc a b)
  refine ⟨l, ?_⟩
  have h3 : max (-u l) (-u' l) - min (-u l) (-u' l) = |u l - u' l| := by
    rw [max_sub_min_eq_abs]
    congr 1; ring
  linarith [ha.1, hb.2]

theorem interlace_half {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ}
    (hl : ∀ a, ∃ m : ℤ, lam a - (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 = (m : ℝ))
    (hu : ∀ i ∈ Finset.Icc 1 k, ∃ a : ℤ, u i = (a : ℝ) + ((k : ℝ) - 1) / 2)
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (s : Fin (2 * r + k + 1)) (hs : s.val + 2 ≤ k) :
    lam s + 1 / 2 ≤ u (s.val + 1) ∧ u (s.val + 2) + 1 / 2 ≤ lam s := by
  obtain ⟨h1, h2⟩ := hI.1 s.val (by omega)
  obtain ⟨m, hm⟩ := hl s
  obtain ⟨a, ha⟩ := hu (s.val + 1) (by simp; omega)
  obtain ⟨a', ha'⟩ := hu (s.val + 2) (by simp; omega)
  push_cast at hm
  refine ⟨half_le_of_lt (a - m - r - 1) ?_ h1, half_le_of_lt (m + r - a') ?_ h2⟩
  · push_cast; linarith
  · push_cast; linarith

theorem std_grid : ∃ Cg₀ : ℝ, ∀ (Ch Cg : ℝ), Cg₀ ≤ Cg → ∀ (P : M.Par) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (ka b g : ℝ), 2 ≤ P.k → StdHyp Ch Cg P.k P.r (PI.BesselPeriodGGP.eps48 P.k P.r) lam (fun i => P.u (i.val + 1)) (fun i => P.u' (i.val + 1)) (P.T * (1 / ka) ^ (2 * P.r)) (P.T' * (1 / ka) ^ (2 * P.r)) ka b → (∀ i ∈ Finset.Icc 1 P.k, (∃ a : ℤ, P.u i = (a : ℝ) + ((P.k : ℝ) - 1) / 2) ∧ ∃ a : ℤ, P.u' i = (a : ℝ) + ((P.k : ℝ) - 1) / 2) → AllGaps lam g → StdNum (2 * |Ch|) b (max (Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3) g / 2) P lam ∧ P.T ≤ b ^ ((2 * |Ch|) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ P.T' ≤ b ^ ((2 * |Ch|) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ ∀ n₀ : ℕ, ((∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) → n₀ = 30 * (P.r + 1) ^ 2 + 6) → (¬ (∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) → n₀ = 0) → Cases P n₀ := by
  refine ⟨36, ?_⟩
  intro Ch Cg hCg P lam ka b g hk hS hint hg
  obtain ⟨⟨hanti, hhalf⟩, hI, hI', hka, hka1, hka2, hT1, hT1', hT2, hT2', hlb, hub, hub', hgap, -,
    ⟨bv, hbv, hshape⟩, hcase⟩ := hS
  have hr : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _

  let s1 : Fin (2 * P.r + P.k + 1) := ⟨P.k - 1, by omega⟩
  let s2 : Fin (2 * P.r + P.k + 1) := ⟨P.k, by omega⟩
  have h12 : s1 < s2 := by simp only [s1, s2, Fin.mk_lt_mk]; omega
  have hbelow : ∀ i : Fin P.k, lam s1 < P.u (i.val + 1) := by
    intro i
    by_cases hi : i.val + 1 < P.k
    · have h1 := (hI.1 i.val hi).1
      have h2 : lam s1 ≤ lam ⟨i.val, by omega⟩ := hanti.antitone (by simp only [s1, Fin.mk_le_mk]; omega)
      exact lt_of_le_of_lt h2 h1
    · have h1 := hI.2 (by omega)
      have he : i.val = P.k - 1 := by have := i.isLt; omega
      rw [he]
      exact h1
  have hn1 := (hshape s1).2 (fun h => by
    obtain ⟨i, hi⟩ := h.2
    exact absurd (hbelow i) (not_lt.2 hi.le))
  have hn2 := (hshape s2).2 (fun h => by
    obtain ⟨i, hi⟩ := h.2
    exact absurd ((hanti h12).trans (hbelow i)) (not_lt.2 hi.le))
  have hd : |lam s1 - lam s2| ≤ bv := by
    rw [abs_le]; constructor <;> linarith [hn1.1, hn1.2, hn2.1, hn2.2]
  have hbvb : bv ≤ b := by
    have := hlb s1
    have := neg_abs_le (lam s1)
    linarith [hn1.2]
  have hmaxgap : AllGaps lam (max (Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3) g) :=
    fun s t h => max_le (hgap s t h) (hg s t h)
  have hcb := (hmaxgap s1 s2 h12.ne).trans (hd.trans hbvb)
  have hc4 : 36 ≤ max (Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3) g := by
    refine le_trans ?_ (le_max_left _ _)
    have h1 : (1 : ℝ) ≤ ((2 * P.r + 2 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by push_cast; linarith)
    nlinarith
  have hb1 : 1 ≤ b := by linarith
  have hkb : (P.k : ℝ) ≤ b := by
    have h0 : (1 : ℝ) ≤ ((2 * P.r + P.k + 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
      push_cast; linarith
    have h1 : ((2 * P.r + P.k + 1 : ℕ) : ℝ) ≤ ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 7 := le_self_pow₀ h0 (by norm_num)
    have h2 : (P.k : ℝ) ≤ ((2 * P.r + P.k + 1 : ℕ) : ℝ) := by push_cast; linarith
    nlinarith
  obtain ⟨hTl, hTu⟩ := scale_bounds P.r hb1 hka hka1 hka2 hT1 hT2
  obtain ⟨hTl', hTu'⟩ := scale_bounds P.r hb1 hka hka1 hka2 hT1' hT2'
  have hh := interlace_half hhalf (fun i hi => (hint i hi).1) hI
  have hh' := interlace_half hhalf (fun i hi => (hint i hi).2) hI'
  refine ⟨⟨fun l hl => ⟨by linarith, by linarith, hkb, ?_, ?_, hlb, ?_, ?_, ?_, hTl, hTl'⟩,
    fun s hs => ⟨(hh s hs).1, (hh s hs).2, (hh' s hs).1, (hh' s hs).2⟩⟩, hTu, hTu', ?_⟩
  · rw [Finset.mem_Icc] at hl
    have := hub ⟨l - 1, by omega⟩
    simpa [Nat.sub_add_cancel hl.1] using this
  · rw [Finset.mem_Icc] at hl
    have := hub' ⟨l - 1, by omega⟩
    simpa [Nat.sub_add_cancel hl.1] using this
  · intro s t hst
    have h1 := hmaxgap s t hst.ne
    rw [abs_of_pos (sub_pos.2 (hanti hst))] at h1
    linarith
  · exact fun s hs => ⟨fun _ => (hh s hs).1, fun _ => (hh s hs).2⟩
  · exact fun s hs => ⟨fun _ => (hh' s hs).1, fun _ => (hh' s hs).2⟩
  · intro n₀ he hne
    have hL : ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ Cg * ((P.r : ℝ) + 1) ^ 2 := by
      have h1 : (1 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
      push_cast; nlinarith
    rcases hcase with ⟨heq, l, hl, hsl, -⟩ | ⟨hneq, hcut⟩
    · have hall : ∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        have := congrFun heq ⟨i - 1, by omega⟩
        simpa [Nat.sub_add_cancel hi.1] using this
      right
      refine ⟨he hall, hall, l + 1, by omega, hl, ?_⟩
      rw [he hall, ← hall (l + 1) (by simp; omega), ← hall (l + 1 + 1) (by simp; omega)]
      simp only at hsl
      linarith
    · left
      refine ⟨hne (fun hall => hneq (funext fun i => hall _ (by simp))), ?_⟩
      obtain ⟨l, hl⟩ := cut_gap (le_trans (Nat.cast_nonneg _) hL) hcut
      exact ⟨l.val + 1, by simp, hL.trans hl⟩

end GlobalTheory.StdGrid
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q MeasureTheory

namespace GlobalTheory

theorem haarOn_UW_eq_of_mass_one {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (μ ν : Measure (Mt k r))
    (hμ : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μ) (hν : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) ν)
    (h1 : μ Set.univ = 1) (h2 : ν Set.univ = 1) : ν = μ := by
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ ν (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hμ hν.conc hν.left hν.finite_compact
  have h3 := congrArg (fun m : Measure (Mt k r) => m Set.univ) hc
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h1, h2, mul_one] at h3
  have h4 : c = 1 := by exact_mod_cast h3.symm
  rw [hc, h4, one_smul]

theorem unitaryMeasureDatum_productMeasure_eq_of_same_vectors : ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (k r : ℕ) (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (D' : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq'), D'.z = D.z → D'.z' = D.z' → D.μW Set.univ = 1 → D.μW' Set.univ = 1 → D'.μW Set.univ = 1 → D'.μW' Set.univ = 1 → D'.μN = D.μN → D'.μSS = D.μSS := by
  intro Wp _ _ _ Wq _ _ _ Wq' _ _ _ k r D D' hz hz' h1 h2 h3 h4 hN
  have e1 : D'.μW = D.μW := haarOn_UW_eq_of_mass_one D.z _ _ D.haarW (hz ▸ D'.haarW) h1 h3
  have e2 : D'.μW' = D.μW' := haarOn_UW_eq_of_mass_one D.z' _ _ D.haarW' (hz' ▸ D'.haarW') h2 h4
  unfold Formalism.FourierDecayAlt.B.RealPlaceData.μSS
  rw [e1, e2, hN]

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exists_normalised_cutoff' : ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μS : Measure (PI.MtM m)), PI.IsMatGroup G → PI.IsMatGroup S → S ⊆ G → PI.IsHaarOnM S μS → PI.IsRightInvM S μS → ∃ φ : PI.MtM m → ℝ≥0∞, Measurable φ ∧ ∀ x : PI.MtM m, Matrix.of x ∈ G → ∫⁻ s, φ (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS = 1 := by
  first | exact @GlobalTheory.exists_normalised_cutoff | exact GlobalTheory.exists_normalised_cutoff | (intros; apply GlobalTheory.exists_normalised_cutoff <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.besselColumnSteps_functional_eigen : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → 1 ≤ r → ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1))) (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1, by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) = c • l (Formalism.REAL.qminor E (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (u - (r : ℂ)) v) := by
  first | exact @GlobalTheory.qminor_column_chain | exact GlobalTheory.qminor_column_chain | (intros; apply GlobalTheory.qminor_column_chain <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.quantumMinor_rowExpansion_eigenFunctional : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (a b : Fin (t + 1) → Fin n) (a' b' : Fin t → Fin n) (a0 b0 : Fin n) (p : ℂ), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective b → Function.Injective a' → Function.Injective b' → Set.range a = insert a0 (Set.range a') → a0 ∉ Set.range a' → Set.range b = insert b0 (Set.range b') → b0 ∉ Set.range b' → a0 ∉ Set.range b → (∀ j v, l (E a0 (b j) v) = (if b j = b0 then p else 0) • l v) → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) = (e * p) • l (Formalism.REAL.qminor E a' b' u v) := by
  first | exact @GlobalTheory.qminor_row_step_under_functional | exact GlobalTheory.qminor_row_step_under_functional | (intros; apply GlobalTheory.qminor_row_step_under_functional <;> assumption)
end
