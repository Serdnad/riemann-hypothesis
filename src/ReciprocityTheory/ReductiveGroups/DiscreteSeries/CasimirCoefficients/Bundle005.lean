module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

lemma kfa_mul_Jm_apply (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Y * Jm ε) a b = Y a b * (if ε b then 1 else -1) := by
  unfold Jm
  rw [Matrix.mul_diagonal]

lemma kfa_Jm_mul_apply (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Jm ε * Y) a b = (if ε a then 1 else -1) * Y a b := by
  unfold Jm
  rw [Matrix.diagonal_mul]

lemma kfa_comm_iff_block (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Y * Jm ε = Jm ε * Y ↔ IsBlock ε Y := by
  constructor
  · intro h a b hab
    have h1 := congrFun (congrFun h a) b
    rw [kfa_mul_Jm_apply, kfa_Jm_mul_apply] at h1
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>
      simp [ha, hb] at h1 hab <;>
      first
      | exact h1
      | linear_combination h1
      | linear_combination (-1 / 2 : ℂ) * h1
      | linear_combination (1 / 2 : ℂ) * h1
  · intro h
    ext a b
    rw [kfa_mul_Jm_apply, kfa_Jm_mul_apply]
    by_cases hab : ε a = ε b
    · rw [hab]
      ring
    · rw [h a b hab]
      ring

lemma kfa_inK_iff (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    inK ε Y ↔ Yᴴ = -Y ∧ IsBlock ε Y := by
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  unfold inK inG
  rw [← kfa_comm_iff_block]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have h3 : (Yᴴ + Y) * Jm ε = 0 := by
      rw [Matrix.add_mul, h2]
      exact h1
    have h4 := congrArg (· * Jm ε) h3
    simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one, Matrix.zero_mul] at h4
    exact eq_neg_of_add_eq_zero_left h4
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h1, Matrix.neg_mul, h2, neg_add_cancel]

section ExpL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma kfa_exp_cont (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) := by
  first
  | exact NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)
  | fun_prop

lemma kfa_exp_comm {J X : Matrix (Fin n) (Fin n) ℂ} (h : X * J = J * X) :
    NormedSpace.exp X * J = J * NormedSpace.exp X := Commute.exp_left h

end ExpL

lemma kfa_exp_neg_mul (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_left, neg_add_cancel, NormedSpace.exp_zero]

lemma kfa_exp_mul_neg (A : Matrix (Fin n) (Fin n) ℂ) :
    NormedSpace.exp A * NormedSpace.exp (-A) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_right, add_neg_cancel, NormedSpace.exp_zero]

lemma kfa_exp_conjTranspose {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Yᴴ = -Y) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • Y))ᴴ = NormedSpace.exp (-((t : ℂ) • Y)) := by
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hY, smul_neg]
  simp only [Complex.star_def, Complex.conj_ofReal]

def kfaUnit (Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  ⟨NormedSpace.exp ((t : ℂ) • Y), NormedSpace.exp (-((t : ℂ) • Y)), kfa_exp_mul_neg _, kfa_exp_neg_mul _⟩

lemma kfa_mem_Kset (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • Y) ∈ Kset ε := by
  have hYJ : Y * Jm ε = Jm ε * Y := hY.2
  have hsk : Yᴴ = -Y := ((kfa_inK_iff ε Y).1 hY).1
  unfold Kset
  rw [Set.mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, kfa_exp_conjTranspose hsk,
      kfa_exp_mul_neg]
  · exact kfa_exp_comm (by rw [Matrix.smul_mul, Matrix.mul_smul, hYJ])

lemma kfa_inUJ (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) :
    inUJ ε (NormedSpace.exp ((t : ℂ) • Y)) := by
  have hYJ : Y * Jm ε = Jm ε * Y := hY.2
  have hsk : Yᴴ = -Y := ((kfa_inK_iff ε Y).1 hY).1
  have hc : NormedSpace.exp ((t : ℂ) • Y) * Jm ε = Jm ε * NormedSpace.exp ((t : ℂ) • Y) :=
    kfa_exp_comm (by rw [Matrix.smul_mul, Matrix.mul_smul, hYJ])
  unfold inUJ
  rw [kfa_exp_conjTranspose hsk, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, kfa_exp_neg_mul,
    Matrix.one_mul]

def kfaUJ (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) : UJ ε :=
  ⟨kfaUnit Y t, kfa_inUJ ε hY t⟩

def kfaKG (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) : KG ε :=
  ⟨kfaUJ ε hY t, kfa_mem_Kset ε hY t⟩

lemma kfa_toMK (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (t : ℝ) :
    toMK (kfaKG ε hY t) = NormedSpace.exp ((t : ℂ) • Y) := rfl

lemma kfa_continuous (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) :
    Continuous (kfaKG ε hY) := by
  have hu : Continuous (kfaUnit Y) := by
    refine Units.continuous_iff.2 ⟨kfa_exp_cont Y, ?_⟩
    show Continuous fun t : ℝ => NormedSpace.exp (-((t : ℂ) • Y))
    simpa only [smul_neg] using kfa_exp_cont (-Y)
  exact (hu.subtype_mk _).subtype_mk _

lemma kfa_add (ε : Fin n → Bool) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (s t : ℝ) :
    kfaKG ε hY (s + t) = kfaKG ε hY s * kfaKG ε hY t := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • Y) =
    NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y)
  rw [Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section

noncomputable section

open Matrix Filter Topology Set

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}

section PathL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma lcB_path (z Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => z * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) 0 := by
  have h1 := hasDerivAt_exp_smul_const Y ((0 : ℝ) : ℂ)
  have hof : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 (0 : ℝ) := Complex.ofRealCLM.hasDerivAt
  have h2 := HasDerivAt.scomp (h := fun y : ℝ => (y : ℂ)) (0 : ℝ) h1 hof
  have h3 := h2.const_mul z
  exact h3.congr_deriv (by simp)

end PathL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma lcB_hasDerivAt (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hUo : IsOpen U)
    (hdiff : DifferentiableOn ℂ (psM T μ) U) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hid : ∀ z ∈ U, fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z))
    (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (A : Matrix (Fin n) (Fin n) ℂ) {t : ℝ} (ht : A * NormedSpace.exp ((t : ℂ) • Y) ∈ U) :
    HasDerivAt (fun s : ℝ => T.op (γ s) * psM T μ (A * NormedSpace.exp ((s : ℂ) • Y))) 0 t := by
  set z := A * NormedSpace.exp ((t : ℂ) • Y) with hz
  have hcomm : ∀ s : ℝ, A * NormedSpace.exp ((s : ℂ) • Y) =
      z * NormedSpace.exp (((s - t : ℝ) : ℂ) • Y) := by
    intro s
    rw [hz, mul_assoc, ← Matrix.exp_add_of_commute _ _
      (((Commute.refl Y).smul_left _).smul_right _), ← add_smul]
    rw [show ((t : ℂ) + ((s - t : ℝ) : ℂ)) = (s : ℂ) by push_cast; ring]
  have h1 := lcB_path z Y
  have h2 := hasDerivAt_iff_tendsto_slope.1 h1
  have h3 : HasDerivAt (fun s : ℝ => z * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) 0 :=
    hasDerivAt_iff_tendsto_slope.2 h2
  have h4 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h3)
  have hp : HasDerivAt (fun s : ℝ => A * NormedSpace.exp ((s : ℂ) • Y)) (z * Y) t := by
    rw [show (fun s : ℝ => A * NormedSpace.exp ((s : ℂ) • Y)) =
      fun s => z * NormedSpace.exp (((s - t : ℝ) : ℂ) • Y) from funext hcomm]
    exact h4
  have hF : HasFDerivAt (psM T μ) (fderiv ℂ (psM T μ) z) z :=
    (hdiff.differentiableAt (hUo.mem_nhds ht)).hasFDerivAt
  have hF' : HasFDerivAt (psM T μ) ((fderiv ℂ (psM T μ) z).restrictScalars ℝ) z :=
    hF.restrictScalars ℝ
  have hq0 := hF'.comp_hasDerivAt t hp
  have e : ((fderiv ℂ (psM T μ) z).restrictScalars ℝ) (z * Y) = -(T.dτ Y * psM T μ z) := hid z ht
  have hq : HasDerivAt (fun s : ℝ => psM T μ (A * NormedSpace.exp ((s : ℂ) • Y)))
      (-(T.dτ Y * psM T μ z)) t := hq0.congr_deriv e
  have ho1 : HasDerivAt (fun s : ℝ => T.op (γ s)) (T.op (γ t) * T.dτ Y) t := by
    have h5 := (T.hasDeriv Y hY γ hγ).const_mul (T.op (γ t))
    have h6 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h5)
    have he : (fun s : ℝ => T.op (γ s)) =
        fun s => T.op (γ t) * ((T.τ (γ (s - t)) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) := by
      funext s
      have hs := hmul t (s - t)
      rw [show t + (s - t) = s by ring] at hs
      simp only [KType.op]
      rw [hs, map_mul]
      rfl
    rw [he]
    exact h6
  have hprod := ho1.mul hq
  have hzero : T.op (γ t) * T.dτ Y * psM T μ (A * NormedSpace.exp ((t : ℂ) • Y)) +
      T.op (γ t) * -(T.dτ Y * psM T μ z) = 0 := by
    rw [mul_neg, mul_assoc]
    exact add_neg_cancel _
  exact hzero ▸ hprod

theorem lcB_const (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hUo : IsOpen U)
    (hdiff : DifferentiableOn ℂ (psM T μ) U) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hid : ∀ z ∈ U, fderiv ℂ (psM T μ) z (z * Y) = -(T.dτ Y * psM T μ z))
    (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) (hmul : ∀ s t, γ (s + t) = γ s * γ t)
    (A : Matrix (Fin n) (Fin n) ℂ) (hpath : ∀ t ∈ Icc (0 : ℝ) 1, A * NormedSpace.exp ((t : ℂ) • Y) ∈ U) :
    T.op (γ 1) * psM T μ (A * NormedSpace.exp Y) = psM T μ A := by
  have h0 : γ 0 = 1 := by simpa using hmul 0 0
  let g : ℝ → T.V →L[ℂ] T.V := fun t => T.op (γ t) * psM T μ (A * NormedSpace.exp ((t : ℂ) • Y))
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g 0 t := fun t ht =>
    lcB_hasDerivAt T μ hUo hdiff hid hY γ hγ hmul A (hpath t ht)
  have hcont : ContinuousOn g (Icc 0 1) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hc := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt) 1 ⟨zero_le_one, le_rfl⟩
  simpa [g, h0, KType.op] using hc

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section

noncomputable section

open Finset Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiff_entry (a b : Fin n) {m : ℕ∞ω} :
    ContDiff ℂ m (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) := by
  exact (contDiff_apply ℂ (fun _ => ℂ) b).comp (contDiff_apply ℂ (fun _ => (Fin n → ℂ)) a)

theorem contDiff_lead (i : ℕ) {m : ℕ∞ω} : ContDiff ℂ m (lead (n := n) i) := by
  unfold lead
  by_cases h : i ≤ n
  · simp only [h, dif_pos]
    simp only [Matrix.det_apply, Units.smul_def]
    refine ContDiff.sum fun σ _ => ?_
    refine ContDiff.const_smul _ ?_
    refine contDiff_prod fun k _ => ?_
    simp only [Matrix.submatrix_apply]
    exact contDiff_entry _ _
  · simp only [h, dif_neg, not_false_eq_true]
    exact contDiff_const

theorem contDiffAt_zpow_lead (i : ℕ) (k : ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : lead i z ≠ 0)
    {m : ℕ∞ω} : ContDiffAt ℂ m (fun w => lead i w ^ k) z := by
  have hl : ContDiffAt ℂ m (lead (n := n) i) z := (contDiff_lead i).contDiffAt
  rcases k with k | k
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact hl.pow k
  · simp only [zpow_negSucc]
    exact (hl.pow (k + 1)).inv (pow_ne_zero _ hz)

theorem contDiffAt_phiM (μ : Fin n → ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n)
    {m : ℕ∞ω} : ContDiffAt ℂ m (PhiM μ) z := by
  unfold PhiM
  exact contDiffAt_prod fun i _ => contDiffAt_zpow_lead _ _ (hz i)

theorem differentiableAt_phiM (μ : Fin n → ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    DifferentiableAt ℂ (PhiM μ) z := by
  exact (contDiffAt_phiM μ hz (m := 1)).differentiableAt (by norm_num)

theorem hasDerivAt_line {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : DifferentiableAt ℂ F z) (v : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℂ => F (z + t • v)) (fderiv ℂ F z v) 0 := by
  have hl : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
    rw [one_smul] at h
    exact h
  have hF' : HasFDerivAt F (fderiv ℂ F z) (z + (0 : ℂ) • v) := by
    simpa using hF.hasFDerivAt
  exact hF'.comp_hasDerivAt (0 : ℂ) hl

def mulLeftCLM (Y : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ Y)

theorem lhol_lhol_eq {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : ContDiffAt ℂ 2 F z) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Lhol X (Lhol Y F) z = fderiv ℂ F z (Y * (X * z)) + fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) := by
  unfold Lhol
  have hc : DifferentiableAt ℂ (fderiv ℂ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hu : HasFDerivAt (fun y : Matrix (Fin n) (Fin n) ℂ => Y * y) (mulLeftCLM Y) z :=
    (mulLeftCLM Y).hasFDerivAt
  have h := hc.hasFDerivAt.clm_apply hu
  erw [h.fderiv]
  rfl

theorem lhol_comm {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : ContDiffAt ℂ 2 F z) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Lhol X (Lhol Y F) z = Lhol Y (Lhol X F) z + fderiv ℂ F z ((Y * X - X * Y) * z) := by
  rw [lhol_lhol_eq hF, lhol_lhol_eq hF]
  have hs := hF.isSymmSndFDerivAt (by simp)
  have h1 : fderiv ℂ (fderiv ℂ F) z (Y * z) (X * z) = fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) :=
    hs _ _
  have h2 : fderiv ℂ F z ((Y * X - X * Y) * z) =
      fderiv ℂ F z (Y * (X * z)) - fderiv ℂ F z (X * (Y * z)) := by
    rw [Matrix.sub_mul, map_sub, Matrix.mul_assoc, Matrix.mul_assoc]
  linear_combination -h1 - h2

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def PsiFormulaStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : KType ε (lowK ε lam)),
    IsHCParam lam → GapAtLeast ε lam h → 1 ≤ q0 ε →
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V),
      (∀ (k₁ k₂ : KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        Ψ (toMK k₁ * g * toMK k₂) = T.op k₁ * Ψ g * T.op k₂) ∧
      Ψ 1 = 1 ∧
      SmoothOnGV ε Ψ ∧
      (∀ g, inUJ ε g → casimirV ε Ψ g = ((casVal lam : ℝ) : ℂ) • Ψ g) ∧
      (∀ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
        ‖Ψ (toMK k * NormedSpace.exp X)‖ ≤
          Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * q0 ε)))) ∧
      (∀ μ : Measure (UJ ε), μ.IsHaarMeasure →
        (16 * (n : ℝ) * q0 ε < h → Integrable (fun g : UJ ε => Ψ (toM g)) μ) ∧
        (8 * (n : ℝ) * q0 ε < h → MemLp (fun g : UJ ε => Ψ (toM g)) 2 μ) ∧
        (∀ s : ℝ, 0 ≤ s → 8 * (n : ℝ) * q0 ε + 4 * s * Real.sqrt (2 * q0 ε) < h →
          Integrable (fun g : UJ ε => ‖Ψ (toM g)‖ ^ 2 * hs (toM g) ^ (s / 2)) μ)) ∧
      (∀ μ : Fin n → ℤ, IsMu lam μ → ∀ X : Matrix (Fin n) (Fin n) ℂ, inP ε X →
        Ψ (NormedSpace.exp X) =
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
            ∫ k, PhiM μ (toMK k⁻¹ * NormedSpace.exp X * toMK k)⁻¹ • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))

section Gelfand

variable {F : Type*} [AddCommGroup F] [Module ℂ F]

def opPow (A : Fin n → Fin n → F → F) : ℕ → Fin n → Fin n → F → F
  | 0, a, b, f => if a = b then f else 0
  | k + 1, a, b, f => ∑ c, A a c (opPow A k c b f)

def opGelfand (A : Fin n → Fin n → F → F) (k : ℕ) (f : F) : F := ∑ a, opPow A k a a f

end Gelfand

section Right

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def rightE (ε : Fin n → Bool) : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E) :=
  fun a b f => EabV ε a b f

def rightEanti (ε : Fin n → Bool) : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E) :=
  fun a b f => -EabV ε (Fin.rev b) (Fin.rev a) f

end Right

def PsiAllStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : KType ε (lowK ε lam)),
    IsHCParam lam → GapAtLeast ε lam h → 1 ≤ q0 ε →
    ∃ Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V),
      (∀ (k₁ k₂ : KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        Ψ (toMK k₁ * g * toMK k₂) = T.op k₁ * Ψ g * T.op k₂) ∧
      Ψ 1 = 1 ∧
      SmoothOnGV ε Ψ ∧
      (∀ g, inUJ ε g → casimirV ε Ψ g = ((casVal lam : ℝ) : ℂ) • Ψ g) ∧
      (∀ (k : KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
        ‖Ψ (toMK k * NormedSpace.exp X)‖ ≤
          Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * q0 ε)))) ∧
      (∀ μ : Measure (UJ ε), μ.IsHaarMeasure →
        (16 * (n : ℝ) * q0 ε < h → Integrable (fun g : UJ ε => Ψ (toM g)) μ) ∧
        (8 * (n : ℝ) * q0 ε < h → MemLp (fun g : UJ ε => Ψ (toM g)) 2 μ) ∧
        (∀ s : ℝ, 0 ≤ s → 8 * (n : ℝ) * q0 ε + 4 * s * Real.sqrt (2 * q0 ε) < h →
          Integrable (fun g : UJ ε => ‖Ψ (toM g)‖ ^ 2 * hs (toM g) ^ (s / 2)) μ)) ∧
      (∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
        opGelfand (rightE ε) k Ψ g = gval (icShift lam) k • Ψ g ∧
        opGelfand (rightEanti ε) k Ψ g = gval (icShift (-lam)) k • Ψ g) ∧
      (∀ μ : Fin n → ℤ, IsMu lam μ → ∀ X : Matrix (Fin n) (Fin n) ℂ, inP ε X →
        Ψ (NormedSpace.exp X) =
          ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
            ∫ k, PhiM μ (toMK k⁻¹ * NormedSpace.exp X * toMK k)⁻¹ • (T.op k * projW T * T.op k⁻¹) ∂(muK ε))

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
