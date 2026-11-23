module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1358
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock.CommDM
open GlobalTheory.CCRFock

private lemma unitAt_apply_eq_ite {W : Type} [DecidableEq W] {P Q R S : ℕ} (j : W × (Ix P Q × Ix R S)) (z : ℂ)
    (w : W) (a : Ix P Q) (b : Ix R S) : unitAt j z w a b = if (w, (a, b)) = j then z else 0 := by
  obtain ⟨j1, j2, j3⟩ := j
  by_cases h1 : w = j1
  · subst h1
    by_cases h2 : a = j2
    · subst h2
      by_cases h3 : b = j3
      · subst h3
        simp [unitAt]
      · simp [unitAt, h3, Ne.symm h3]
    · simp [unitAt, h2, Ne.symm h2]
  · simp [unitAt, h1]

theorem sum_unitAt {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ} (j k : W × (Ix P Q × Ix R S)) (z z' : ℂ) :
    (∑ w, ∑ a, ∑ b, lineSign a b * unitAt j z w a b * star (unitAt k z' w a b)) =
      if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0 := by
  have key : ∀ (w : W) (a : Ix P Q) (b : Ix R S), lineSign a b * unitAt j z w a b * star (unitAt k z' w a b) =
      if (w, (a, b)) = j then (if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0) else 0 := by
    intro w a b
    rw [unitAt_apply_eq_ite, unitAt_apply_eq_ite]
    by_cases hj : (w, (a, b)) = j
    · subst hj
      by_cases hk : (w, (a, b)) = k
      · subst hk
        simp
      · simp [hk]
    · simp [hj]
  simp only [key]
  rw [Fintype.sum_eq_single j.1, Fintype.sum_eq_single j.2.1, Fintype.sum_eq_single j.2.2]
  all_goals first
    | (intro x hx; simp [Prod.ext_iff, hx])
    | simp

theorem lineSign_cases {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : (lineSign a b : ℂ) = 1 ∨ (lineSign a b : ℂ) = -1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem comm_expand {V : Type} [AddCommGroup V] [Module ℂ V] (A A' B B' : Module.End ℂ V) (c u v : ℂ) :
    -(c • (A + u • A')) * (c • (B - v • B')) - (c • (B - v • B')) * -(c • (A + u • A')) =
      -((c * c) • ((A * B - B * A) - v • (A * B' - B' * A) + u • (A' * B - B * A') - (u * v) • (A' * B' - B' * A'))) := by
  simp only [neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_smul, mul_add, add_mul, mul_sub, sub_mul,
    smul_add, smul_sub, smul_neg]
  module

theorem inv_sq : (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ * (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ =
    (8 * (Real.pi : ℂ))⁻¹ := by
  rw [← mul_inv]
  congr 1
  have h : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  linear_combination 4 * h

theorem fockD_fockM_comm : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ j k : W × (Ix P Q × Ix R S), GlobalTheory.CCRFock.fockD H j * GlobalTheory.CCRFock.fockM H k - GlobalTheory.CCRFock.fockM H k * GlobalTheory.CCRFock.fockD H j =
      if j = k then 1 else 0 := by
  intro V _ _ W _ _ P Q R S H _ _ hcomm j k
  simp only [GlobalTheory.CCRFock.fockD, GlobalTheory.CCRFock.fockM]
  rw [comm_expand, hcomm, hcomm, hcomm, hcomm, sum_unitAt, sum_unitAt, sum_unitAt, sum_unitAt, inv_sq]
  by_cases hjk : j = k
  · subst hjk
    rcases lineSign_cases j.2.1 j.2.2 with h | h
    · simp only [if_true, h]
      match_scalars
      simp
      field_simp
      ring_nf
      simp [Complex.I_sq]
    · simp only [if_true, h]
      match_scalars
      simp
      field_simp
      ring_nf
      simp [Complex.I_sq]
  · simp [hjk]

end GlobalTheory.CCRFock.CommDM
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD.CCRSig

variable {W : Type} [DecidableEq W] {P Q R S : W → ℕ}

def unitAtS (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (z : ℂ) : ∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ :=
  Pi.single j.1 (Matrix.single j.2.1 j.2.2 z)

theorem sum_unitAtS [Fintype W] (j k : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (z z' : ℂ) :
    (∑ w, ∑ a, ∑ b, lineSign a b * unitAtS j z w a b * star (unitAtS k z' w a b)) =
      if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0 := by
  obtain ⟨w0, a0, b0⟩ := j
  obtain ⟨w1, a1, b1⟩ := k
  rw [Finset.sum_eq_single w0]
  · by_cases hw : w1 = w0
    · subst hw
      simp only [unitAtS, Pi.single_eq_same]
      rw [Finset.sum_eq_single a0, Finset.sum_eq_single b0]
      · by_cases ha : a0 = a1
        · subst ha
          by_cases hb : b0 = b1
          · subst hb; simp
          · have : (⟨w1, a0, b0⟩ : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) ≠ ⟨w1, a0, b1⟩ := by
              intro h; simp at h; exact hb h
            simp [this, hb, Ne.symm hb]
        · have : (⟨w1, a0, b0⟩ : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) ≠ ⟨w1, a1, b1⟩ := by
            intro h; simp at h; exact ha h.1
          simp [this, ha, Ne.symm ha]
      · intro b _ hb; simp [Ne.symm hb]
      · simp
      · intro a _ ha; simp [Ne.symm ha]
      · simp
    · have : (⟨w0, a0, b0⟩ : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) ≠ ⟨w1, a1, b1⟩ := by
        intro h; exact hw (congrArg Sigma.fst h).symm
      simp [unitAtS, hw, this]
  · intro w _ hw; simp [unitAtS, hw]
  · simp

theorem sum_unitAtS_eq [Fintype W] (c : ∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)), unitAtS j (c j.1 j.2.1 j.2.2) := by
  funext w a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Fintype.sum_sigma, unitAtS]
  rw [Finset.sum_eq_single w]
  · simp only [Pi.single_eq_same]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp
    · intro b' _ hb; simp [Matrix.single_apply, hb]
    · simp
    · intro a' _ ha; simp [Matrix.single_apply, ha]
    · simp
  · intro w' _ hw; simp [Pi.single_eq_of_ne' hw]
  · simp

end GlobalTheory.HoweD.CCRSig

namespace GlobalTheory.HoweD.CCRSig

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [DecidableEq W] {P Q R S : W → ℕ}

theorem lineSign_cases {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : (lineSign a b : ℂ) = 1 ∨ (lineSign a b : ℂ) = -1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem lineSign_mul_self {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : lineSign a b * lineSign a b = 1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem comm_expand (A A' B B' : Module.End ℂ V) (c u v : ℂ) :
    -(c • (A + u • A')) * (c • (B - v • B')) - (c • (B - v • B')) * -(c • (A + u • A')) =
      -((c * c) • ((A * B - B * A) - v • (A * B' - B' * A) + u • (A' * B - B * A') - (u * v) • (A' * B' - B' * A'))) := by
  simp only [neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul]
  module

theorem inv_sq : (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ * (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ =
    (8 * (Real.pi : ℂ))⁻¹ := by
  have h : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; ring
  rw [← mul_inv]
  congr 1
  linear_combination 4 * h

def ccrM (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) : Module.End ℂ V :=
  (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAtS j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I))

def ccrD (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) : Module.End ℂ V :=
  -((2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAtS j 1) + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I)))

theorem ccrM_comm [Fintype W] (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (hc : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1)
    (j k : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) : ccrM H j * ccrM H k = ccrM H k * ccrM H j := by
  have h11 := hc (unitAtS j 1) (unitAtS k 1)
  have h1i := hc (unitAtS j 1) (unitAtS k Complex.I)
  have hi1 := hc (unitAtS j Complex.I) (unitAtS k 1)
  have hii := hc (unitAtS j Complex.I) (unitAtS k Complex.I)
  rw [sum_unitAtS] at h11 h1i hi1 hii
  by_cases hjk : j = k
  · rw [hjk]
  · simp only [if_neg hjk, Complex.zero_im, Complex.ofReal_zero, mul_zero, zero_smul, sub_eq_zero] at h11 h1i hi1 hii
    unfold ccrM
    have c : Commute (H (unitAtS j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I))
        (H (unitAtS k 1) - (lineSign k.2.1 k.2.2 * Complex.I) • H (unitAtS k Complex.I)) :=
      Commute.sub_left (Commute.sub_right h11 (Commute.smul_right h1i _))
        (Commute.smul_left (Commute.sub_right hi1 (Commute.smul_right hii _)) _)
    exact ((c.smul_left _).smul_right _).eq

theorem ccrD_ccrM_comm [Fintype W] (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (hc : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1)
    (j k : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) :
    ccrD H j * ccrM H k - ccrM H k * ccrD H j = if j = k then 1 else 0 := by
  unfold ccrD ccrM
  rw [comm_expand, hc, hc, hc, hc, sum_unitAtS, sum_unitAtS, sum_unitAtS, sum_unitAtS,
    inv_sq]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases h : j = k
  · subst h
    simp only [if_true, smul_smul, ← sub_smul, ← add_smul, ← neg_smul]
    conv_rhs => rw [← one_smul ℂ (1 : Module.End ℂ V)]
    congr 1
    rcases lineSign_cases j.2.1 j.2.2 with h | h
    · rw [h]; simp; field_simp; linear_combination (-8 : ℂ) * Complex.I_sq
    · rw [h]; simp; field_simp; linear_combination (-8 : ℂ) * Complex.I_sq
  · simp [h]

theorem unitAtS_re_im (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (z : ℂ) :
    unitAtS j z = ((z.re : ℝ) : ℂ) • unitAtS j 1 + ((z.im : ℝ) : ℂ) • unitAtS j Complex.I := by
  funext w
  by_cases hw : w = j.1
  · subst hw
    simp only [unitAtS, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_single, ← Matrix.single_add, smul_eq_mul,
      mul_one, Complex.re_add_im]
  · simp [unitAtS, Pi.single_eq_of_ne hw]

theorem heis_expanccrD [Fintype W] (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (hadd : ∀ c c', H (c + c') = H c + H c') (hsmul : ∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c)
    (c : ∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    H c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)),
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • ccrM H j +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • ccrD H j) := by
  have h0 : H 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  let H' : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →+ Module.End ℂ V := ⟨⟨H, h0⟩, hadd⟩
  have hsum : H c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)), H (unitAtS j (c j.1 j.2.1 j.2.2)) := by
    conv_lhs => rw [sum_unitAtS_eq c]
    exact map_sum H' _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [unitAtS_re_im, hadd, hsmul, hsmul]
  have hs : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  have he := lineSign_mul_self j.2.1 j.2.2
  unfold ccrM ccrD GlobalTheory.CCRFock.coefM GlobalTheory.CCRFock.coefD
  generalize ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = s at hs ⊢
  generalize lineSign j.2.1 j.2.2 = e at he ⊢
  generalize H (unitAtS j 1) = A
  generalize H (unitAtS j Complex.I) = B
  generalize ((c j.1 j.2.1 j.2.2).re : ℂ) = x
  generalize ((c j.1 j.2.1 j.2.2).im : ℂ) = y
  have hI := Complex.I_mul_I
  match_scalars
  · field_simp
    ring
  · field_simp
    linear_combination (2 * y * e * e) * hI - 2 * y * he

end GlobalTheory.HoweD.CCRSig

namespace GlobalTheory.HoweD


open GlobalTheory.HoweD.CCRSig in
theorem ccr_fock_ops_sig : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : W → ℕ} (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V), (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) → (∀ c c', H c * H c' - H c' * H c = ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) → ∃ m D : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) → Module.End ℂ V, (∀ i j, m i * m j = m j * m i) ∧ (∀ i j, D i * m j - m j * D i = if i = j then 1 else 0) ∧ (∀ (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (f₀ : V), H (Pi.single j.1 (Matrix.single j.2.1 j.2.2 1)) f₀ + (lineSign j.2.1 j.2.2 * Complex.I) • H (Pi.single j.1 (Matrix.single j.2.1 j.2.2 Complex.I)) f₀ = 0 → D j f₀ = 0) ∧ ∀ c, H c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)), ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • m j + (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • D j) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul hc
  refine ⟨ccrM H, ccrD H, ccrM_comm H hc, ccrD_ccrM_comm H hc, fun j f₀ h => ?_, heis_expanccrD H hadd hsmul⟩
  have h' : H (unitAtS j 1) f₀ + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I) f₀ = 0 := h
  simp only [GlobalTheory.HoweD.CCRSig.ccrD, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.add_apply, h', smul_zero, neg_zero]

end GlobalTheory.HoweD
end
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem lineSign_mul_self {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : lineSign a b * lineSign a b = 1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem sum_unitAt {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ} (c : W → Matrix (Ix P Q) (Ix R S) ℂ) :
    c = ∑ j : W × (Ix P Q × Ix R S), unitAt j (c j.1 j.2.1 j.2.2) := by
  rw [Fintype.sum_prod_type]
  conv_lhs => rw [← Finset.univ_sum_single c]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fintype.sum_prod_type]
  conv_lhs => rw [Matrix.matrix_eq_sum_single (c w)]
  funext v
  simp only [unitAt, Finset.sum_apply]
  by_cases h : v = w
  · subst h
    simp
  · simp [h]

theorem unitAt_re_im {W : Type} [DecidableEq W] {P Q R S : ℕ} (j : W × (Ix P Q × Ix R S)) (z : ℂ) :
    unitAt j z = ((z.re : ℝ) : ℂ) • unitAt j 1 + ((z.im : ℝ) : ℂ) • unitAt j Complex.I := by
  simp only [unitAt, ← Pi.single_smul', ← Pi.single_add, Matrix.smul_single, ← Matrix.single_add, smul_eq_mul, mul_one,
    Complex.re_add_im]

theorem heis_expand : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    ∀ c : W → Matrix (Ix P Q) (Ix R S) ℂ, H c = ∑ j : W × (Ix P Q × Ix R S),
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • GlobalTheory.CCRFock.fockM H j +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • GlobalTheory.CCRFock.fockD H j) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul c
  have h0 : H 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  let H' : (W → Matrix (Ix P Q) (Ix R S) ℂ) →+ Module.End ℂ V := ⟨⟨H, h0⟩, hadd⟩
  have hsum : H c = ∑ j : W × (Ix P Q × Ix R S), H (unitAt j (c j.1 j.2.1 j.2.2)) := by
    conv_lhs => rw [sum_unitAt c]
    exact map_sum H' _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [unitAt_re_im, hadd, hsmul, hsmul]
  have hs : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  have he := lineSign_mul_self j.2.1 j.2.2
  unfold fockM fockD coefM coefD
  generalize ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = s at hs ⊢
  generalize lineSign j.2.1 j.2.2 = e at he ⊢
  generalize H (unitAt j 1) = A
  generalize H (unitAt j Complex.I) = B
  generalize ((c j.1 j.2.1 j.2.2).re : ℂ) = x
  generalize ((c j.1 j.2.1 j.2.2).im : ℂ) = y
  have hI := Complex.I_mul_I
  match_scalars
  · field_simp
    ring
  · field_simp
    linear_combination (2 * y * e * e) * hI - 2 * y * he

end GlobalTheory.CCRFock
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace GlobalTheory.EvAdm

theorem isCompact_scaledInt_of_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Finite κ] {a : F} (ha : a ≠ 0) :
    IsCompact (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have hO : IsCompact {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F} := by
    haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
      fun v => isCompact_iff_compactSpace.1 (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)
    have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (𝓕 := Filter.cofinite)).continuous
    rw [RestrictedProduct.range_structureMap] at h
    exact h
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → FiniteAdeleRing (𝓞 F) F) :=
    fun z i => algebraMap F (FiniteAdeleRing (𝓞 F) F) a * z i
  have hg : Continuous g := continuous_pi fun i => continuous_const.mul (continuous_apply i)
  have hP : IsCompact (Set.pi Set.univ fun _ : κ =>
      {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F}) := isCompact_univ_pi fun _ => hO
  refine (hP.image hg).of_isClosed_subset ((scaledInt F κ a).isClosed_of_isOpen (isOpen_scaledInt a)) ?_
  intro z hz
  refine ⟨fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i, fun i _ v => ?_, ?_⟩
  · have h : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v =
        (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v := by
      have h1 := map_mul (evalV F v) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) (z i)
      rw [AlgHom.commutes, map_inv₀ (algebraMap F (v.adicCompletion F))] at h1
      exact h1
    show (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v ∈ _
    rw [h]
    exact hz i v
  · funext i
    simp only [g]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]

theorem indicator_coset_scaledInt_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun _ => (1 : ℂ)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _ κ _ a ha r
  have hf : Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F => y - r := continuous_id.sub continuous_const
  have hcl : IsClopen {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} :=
    ⟨((scaledInt F κ a).isClosed_of_isOpen (isOpen_scaledInt a)).preimage hf, (isOpen_scaledInt a).preimage hf⟩
  have hco : IsCompact {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} :=
    (Homeomorph.subRight r).isCompact_preimage.2 (isCompact_scaledInt_of_ne_zero (κ := κ) ha)
  generalize {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} = S at hcl hco ⊢
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)

end GlobalTheory.EvAdm
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

theorem _root_.GlobalTheory.T.adelicLinearCoordinates_continuous_finite_real_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT N : ℕ)
    (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
    Continuous e ∧ Continuous e.symm ∧
      (∀ x : Formalism.IndefR.DatumF.WOF F E nS nT, x.map (Formalism.IndefR.DatumF.finPartF F E) = 0 ↔ GlobalTheory.SWQ.fin (e x).1 = 0 ∧ GlobalTheory.SWQ.fin (e x).2 = 0) ∧
      (∀ x : Formalism.IndefR.DatumF.WOF F E nS nT, x.map (Formalism.IndefR.DatumF.infPartF F E) = 0 ↔ GlobalTheory.SWQ.inf (e x).1 = 0 ∧ GlobalTheory.SWQ.inf (e x).2 = 0) := by
  first | exact @GlobalTheory.AdelicCoordF.coord | exact GlobalTheory.AdelicCoordF.coord | (intros; apply GlobalTheory.AdelicCoordF.coord <;> assumption)
end
