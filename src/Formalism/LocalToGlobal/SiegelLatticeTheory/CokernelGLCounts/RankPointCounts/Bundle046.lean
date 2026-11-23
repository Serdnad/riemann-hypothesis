module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle020
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DensitySumsAndDomination
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTiePl
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbCut
import Formalism.DoubleCosetMeasures.LatticeCoset
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstKernelPropertiesOfHypotheses
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
public import Mathlib.Algebra.Order.Field.GeomSum
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumGlue
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle043
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut

@[expose] public section

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol
  Formalism.L2.SG.DataInst Formalism.L2.SG.Pf.ProdConvCut Formalism.L2.SG.Pf.AlTie

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)

theorem etaV_pm (v : PlX X) :
    ((etaV (E := X.B.I.E) v : ℤ) : ℝ) = 1 ∨ ((etaV (E := X.B.I.E) v : ℤ) : ℝ) = -1 := by
  unfold etaV
  split_ifs <;> simp

theorem absNorm_ge_two (v : PlX X) : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast h2

private theorem exp_bounds_prod_one_sub_pow_div (q η : ℝ) (hq : 2 ≤ q) (hη : η = 1 ∨ η = -1) (k a N : ℕ) (hk : 1 ≤ k)
    (ha : k ≤ a) :
    Real.exp (-(4 * q⁻¹ ^ k)) ≤ ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i) ∧
      ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i) ≤ Real.exp (2 * q⁻¹ ^ k) := by
  have hq0 : 0 < q := by linarith
  have hx0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hxq : q⁻¹ * q = 1 := inv_mul_cancel₀ hq0.ne'
  have hx2 : q⁻¹ ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_left hq hx0]
  have hterm : ∀ i : ℕ, |η ^ i / q ^ i| = q⁻¹ ^ i := by
    intro i
    rw [abs_div, abs_pow, abs_pow, abs_of_pos hq0, inv_pow]
    rcases hη with rfl | rfl <;> simp
  have hsum : ∑ i ∈ Finset.Icc a N, q⁻¹ ^ i ≤ 2 * q⁻¹ ^ k := by
    have h1 : ∑ i ∈ Finset.Icc a N, q⁻¹ ^ i ≤ q⁻¹ ^ a / (1 - q⁻¹) := by
      have hI : Finset.Icc a N = Finset.Ico a (N + 1) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hI]
      exact geom_sum_Ico_le_of_lt_one hx0 (by linarith)
    have h2 : q⁻¹ ^ a / (1 - q⁻¹) ≤ 2 * q⁻¹ ^ a := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (pow_nonneg hx0 a) (by linarith : (0 : ℝ) ≤ 1 / 2 - q⁻¹)]
    have h3 : q⁻¹ ^ a ≤ q⁻¹ ^ k := pow_le_pow_of_le_one hx0 (by linarith) ha
    linarith
  constructor
  · have hfac : ∀ i ∈ Finset.Icc a N, Real.exp (-(2 * q⁻¹ ^ i)) ≤ 1 - η ^ i / q ^ i := by
      intro i hi
      have hi1 : i ≠ 0 := by
        have := (Finset.mem_Icc.mp hi).1
        omega
      have hy0 : 0 ≤ q⁻¹ ^ i := pow_nonneg hx0 i
      have hy : q⁻¹ ^ i ≤ 1 / 2 := le_trans (pow_le_of_le_one hx0 (by linarith) hi1) hx2
      have hle : η ^ i / q ^ i ≤ q⁻¹ ^ i := (abs_le.mp (le_of_eq (hterm i))).2
      have he : 1 + 2 * q⁻¹ ^ i ≤ Real.exp (2 * q⁻¹ ^ i) := by
        linarith [Real.add_one_le_exp (2 * q⁻¹ ^ i)]
      have hEF : Real.exp (-(2 * q⁻¹ ^ i)) * Real.exp (2 * q⁻¹ ^ i) = 1 := by
        rw [← Real.exp_add]
        simp
      have hE0 : 0 < Real.exp (-(2 * q⁻¹ ^ i)) := Real.exp_pos _
      have hE12 : Real.exp (-(2 * q⁻¹ ^ i)) * (1 + 2 * q⁻¹ ^ i) ≤ 1 := by
        calc Real.exp (-(2 * q⁻¹ ^ i)) * (1 + 2 * q⁻¹ ^ i)
            ≤ Real.exp (-(2 * q⁻¹ ^ i)) * Real.exp (2 * q⁻¹ ^ i) := mul_le_mul_of_nonneg_left he hE0.le
          _ = 1 := hEF
      have hc : 1 ≤ (1 + 2 * q⁻¹ ^ i) * (1 - q⁻¹ ^ i) := by nlinarith
      calc Real.exp (-(2 * q⁻¹ ^ i))
          ≤ Real.exp (-(2 * q⁻¹ ^ i)) * ((1 + 2 * q⁻¹ ^ i) * (1 - q⁻¹ ^ i)) := le_mul_of_one_le_right hE0.le hc
        _ = (Real.exp (-(2 * q⁻¹ ^ i)) * (1 + 2 * q⁻¹ ^ i)) * (1 - q⁻¹ ^ i) := by ring
        _ ≤ 1 * (1 - q⁻¹ ^ i) := mul_le_mul_of_nonneg_right hE12 (by linarith)
        _ ≤ 1 - η ^ i / q ^ i := by linarith
    calc Real.exp (-(4 * q⁻¹ ^ k))
        ≤ Real.exp (∑ i ∈ Finset.Icc a N, -(2 * q⁻¹ ^ i)) := by
          apply Real.exp_le_exp.mpr
          rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
          linarith
      _ = ∏ i ∈ Finset.Icc a N, Real.exp (-(2 * q⁻¹ ^ i)) := Real.exp_sum _ _
      _ ≤ ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i) :=
          Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) hfac
  · have hfac : ∀ i ∈ Finset.Icc a N, 1 - η ^ i / q ^ i ≤ Real.exp (q⁻¹ ^ i) := by
      intro i _
      have := (abs_le.mp (le_of_eq (hterm i))).1
      linarith [Real.add_one_le_exp (q⁻¹ ^ i)]
    have hnn : ∀ i ∈ Finset.Icc a N, 0 ≤ 1 - η ^ i / q ^ i := by
      intro i _
      have := (abs_le.mp (le_of_eq (hterm i))).2
      have hy : q⁻¹ ^ i ≤ 1 := pow_le_one₀ hx0 (by linarith)
      linarith
    calc ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i)
        ≤ ∏ i ∈ Finset.Icc a N, Real.exp (q⁻¹ ^ i) := Finset.prod_le_prod₀ hnn hfac
      _ = Real.exp (∑ i ∈ Finset.Icc a N, q⁻¹ ^ i) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (2 * q⁻¹ ^ k) := Real.exp_le_exp.mpr hsum

theorem aP_bounds (hk : 1 ≤ D.R.k) (v : PlX X) (T : ℕ) :
    Real.exp (-(4 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k)) ≤ aP (E := X.B.I.E) v D.R.k X.B.I.n T ∧
      aP (E := X.B.I.E) v D.R.k X.B.I.n T ≤ Real.exp (2 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k) := by
  unfold aP
  exact exp_bounds_prod_one_sub_pow_div _ _ (absNorm_ge_two X v) (etaV_pm X v) _ _ _ hk (by split_ifs <;> omega)

private theorem exp_bounds_mul_of_exp_bounds (a b y : ℝ) (hy : 0 ≤ y)
    (ha : Real.exp (-(4 * y)) ≤ a ∧ a ≤ Real.exp (2 * y)) (hb : Real.exp (-(4 * y)) ≤ b ∧ b ≤ Real.exp (2 * y)) :
    (Real.exp (-(8 * y)) ≤ a ∧ a ≤ Real.exp (4 * y)) ∧
      (Real.exp (-(8 * y)) ≤ a * b ∧ a * b ≤ Real.exp (4 * y)) := by
  have ha0 : 0 ≤ a := le_trans (Real.exp_pos _).le ha.1
  have hb0 : 0 ≤ b := le_trans (Real.exp_pos _).le hb.1
  refine ⟨⟨le_trans (Real.exp_le_exp.mpr (by linarith)) ha.1, le_trans ha.2 (Real.exp_le_exp.mpr (by linarith))⟩, ?_, ?_⟩
  · calc Real.exp (-(8 * y)) = Real.exp (-(4 * y)) * Real.exp (-(4 * y)) := by
          rw [← Real.exp_add]
          ring_nf
      _ ≤ a * b := mul_le_mul ha.1 hb.1 (Real.exp_pos _).le ha0
  · calc a * b ≤ Real.exp (2 * y) * Real.exp (2 * y) := mul_le_mul ha.2 hb.2 hb0 (Real.exp_pos _).le
      _ = Real.exp (4 * y) := by
          rw [← Real.exp_add]
          ring_nf

theorem alX_bounds (hk : 1 ≤ D.R.k) (v : PlX X) :
    Real.exp (-(8 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k)) ≤ alX X u u' v ∧
      alX X u u' v ≤ Real.exp (4 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k) := by
  have h := exp_bounds_mul_of_exp_bounds _ _ ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k) (by positivity)
    (aP_bounds X hk v (Tw u)) (aP_bounds X hk v (Tw u'))
  unfold alX
  split_ifs
  · exact h.1
  · exact h.2

theorem summable_qk (hk2 : 2 ≤ D.R.k) :
    Summable fun v : PlX X => (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k := by
  have hP := Formalism.L2.SG.Pf.placesOver_holds D
  set s := D.R.k with hs
  set a : PlF D → ℝ := fun p => (Formalism.L2.SG.DataCut.qP p ^ s)⁻¹ with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => inv_nonneg.2 (pow_nonneg (Formalism.L2.SG.DataCut.qP_nonneg p) _)
  have hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, a p ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    intro S
    exact Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S Formalism.L2.SG.DataCut.qP Loc.resChar D.R.f s hk2
      (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩)
      (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))
  have haS : Summable a := summable_of_sum_le ha0 hsum
  have h1 : Summable fun v : PlX X => a (plEquiv X v) := (plEquiv X).summable_iff.2 haS
  refine h1.congr fun v => ?_
  show (Formalism.L2.SG.DataCut.qP (plEquiv X v) ^ s)⁻¹ = _
  have hq : Formalism.L2.SG.DataCut.qP (plEquiv X v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    rw [← absNorm_plEquiv X v]
    exact Formalism.L2.SG.Pf.LocModel.qPl_eq _
  rw [hq, inv_pow]

theorem AlConvC_holds : AlConvC X u u' := by
  have hk2 : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk1 : 1 ≤ D.R.k := by omega
  have hpos : ∀ v, 0 < alX X u u' v := fun v => lt_of_lt_of_le (Real.exp_pos _) (alX_bounds X u u' hk1 v).1
  have hlog : Summable fun v : PlX X => Real.log (alX X u u' v) := by
    refine Summable.of_norm_bounded ((summable_qk X hk2).mul_left 8) fun v => ?_
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨b1, b2⟩ := alX_bounds X u u' hk1 v
    have h1 := Real.log_le_log (Real.exp_pos _) b1
    have h2 := Real.log_le_log (hpos v) b2
    rw [Real.log_exp] at h1 h2
    have hy0 : 0 ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k :=
      pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _
    constructor <;> linarith
  have hlogO : Summable fun v : OrdX X => Real.log (alX X u u' v.1) :=
    hlog.comp_injective (i := fun v : OrdX X => v.1) Subtype.val_injective
  have hposO : ∀ v : OrdX X, 0 < alX X u u' v.1 := fun v => hpos v.1
  refine ⟨Real.multipliable_of_summable_log hposO hlogO, ?_⟩
  rw [← Real.rexp_tsum_eq_tprod hposO hlogO]
  exact Real.exp_pos _

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbCut

open MeasureTheory Formalism.MainNotions.S Formalism.L2.SG.Pf.LocOrbSumPf
open Classical

section Cast

variable {K : Type} [CommRing K]

theorem sLow_cast {n n' : ℕ} (h : n' = n) (A : Matrix (Fin n) (Fin n) K) :
    Formalism.DoubleCosetMeasures.sLow (A.submatrix (finCongr h) (finCongr h)) = Formalism.DoubleCosetMeasures.sLow A := by
  subst h
  rfl

theorem sUp_cast {n n' : ℕ} (h : n' = n) (A : Matrix (Fin n) (Fin n) K) :
    Formalism.DoubleCosetMeasures.sUp (A.submatrix (finCongr h) (finCongr h)) = Formalism.DoubleCosetMeasures.sUp A := by
  subst h
  rfl

theorem lowUni_cast {n n' : ℕ} (h : n' = n) {A : Matrix (Fin n) (Fin n) K} (hA : Formalism.DoubleCosetMeasures.IsLowUni A) :
    Formalism.DoubleCosetMeasures.IsLowUni (A.submatrix (finCongr h) (finCongr h)) := by
  subst h
  exact hA

theorem upUni_cast {n n' : ℕ} (h : n' = n) {A : Matrix (Fin n) (Fin n) K} (hA : Formalism.DoubleCosetMeasures.IsUpUni A) :
    Formalism.DoubleCosetMeasures.IsUpUni (A.submatrix (finCongr h) (finCongr h)) := by
  subst h
  exact hA

theorem sLow_one {n : ℕ} : Formalism.DoubleCosetMeasures.sLow (1 : Matrix (Fin n) (Fin n) K) = 0 := by
  simp [Formalism.DoubleCosetMeasures.sLow, Matrix.one_apply, Fin.ext_iff]

theorem sUp_one {n : ℕ} : Formalism.DoubleCosetMeasures.sUp (1 : Matrix (Fin n) (Fin n) K) = 0 := by
  simp [Formalism.DoubleCosetMeasures.sUp, Matrix.one_apply, Fin.ext_iff]

theorem sLow_mem (R : Subring K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, A i j ∈ R) :
    Formalism.DoubleCosetMeasures.sLow A ∈ R := by
  unfold Formalism.DoubleCosetMeasures.sLow
  refine Subring.sum_mem R (fun j _ => ?_)
  split_ifs
  · exact hA _ _
  · exact R.zero_mem

theorem sUp_mem (R : Subring K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, A i j ∈ R) :
    Formalism.DoubleCosetMeasures.sUp A ∈ R := by
  unfold Formalism.DoubleCosetMeasures.sUp
  refine Subring.sum_mem R (fun j _ => ?_)
  split_ifs
  · exact hA _ _
  · exact R.zero_mem

end Cast

section Val

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] [IsTopologicalRing E]

theorem uLow_lowUni {n : ℕ} (x : Loc.IL n → E) : Formalism.DoubleCosetMeasures.IsLowUni (Loc.uLow x) := by
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · have h' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp only [Loc.uLow]
    rw [if_neg (ne_of_lt h'), dite_eq_right (not_lt.mpr h'.le)]
  · simp [Loc.uLow]

theorem uUp_upUni {n : ℕ} (w : Loc.Pt E n) (y : Loc.IN w → E) : Formalism.DoubleCosetMeasures.IsUpUni (Loc.uUp w y) := by
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · have h' : j < i := hij
    simp only [Loc.uUp]
    rw [if_neg (ne_of_gt h'), dite_eq_right (fun h => absurd h.1 (not_lt.mpr h'.le))]
  · simp [Loc.uUp]

def rI {m : ℕ} (a : Loc.Pt E (m + 1)) (B : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E :=
  B.submatrix (finCongr (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a)) (finCongr (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a))

theorem rI_mul {m : ℕ} (a : Loc.Pt E (m + 1)) (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    rI a (A * B) = rI a A * rI a B := by
  unfold rI
  rw [Matrix.submatrix_mul_equiv]

theorem rI_mat {m : ℕ} (a : Loc.Pt E (m + 1)) :
    rI a a.mat = Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 := by
  unfold rI
  rw [Formalism.MainNotions.LocalModelPeriodLattices.mat_eq]
  ext i j
  simp

theorem rI_zQ {m : ℕ} (R : Subring E) (a : Loc.Pt E (m + 1)) (q : Formalism.FourierDecayAlt.A5.Cos R (Formalism.MainNotions.LocalModelPeriodLattices.tr a)) :
    rI a (zQ R a q) = Formalism.FourierDecayAlt.A5.orbZ (Formalism.MainNotions.LocalModelPeriodLattices.tr a) (Formalism.FourierDecayAlt.A5.rep R q) := by
  unfold rI zQ
  ext i j
  simp

theorem lowUni_rI {m : ℕ} (a : Loc.Pt E (m + 1)) {A : Matrix (Fin (m + 1)) (Fin (m + 1)) E}
    (hA : Formalism.DoubleCosetMeasures.IsLowUni A) : Formalism.DoubleCosetMeasures.IsLowUni (rI a A) := lowUni_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) hA

theorem upUni_rI {m : ℕ} (a : Loc.Pt E (m + 1)) {A : Matrix (Fin (m + 1)) (Fin (m + 1)) E}
    (hA : Formalism.DoubleCosetMeasures.IsUpUni A) : Formalism.DoubleCosetMeasures.IsUpUni (rI a A) := upUni_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) hA

theorem sLow_rI {m : ℕ} (a : Loc.Pt E (m + 1)) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    Formalism.DoubleCosetMeasures.sLow (rI a A) = Formalism.DoubleCosetMeasures.sLow A := sLow_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) A

theorem sUp_rI {m : ℕ} (a : Loc.Pt E (m + 1)) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    Formalism.DoubleCosetMeasures.sUp (rI a A) = Formalism.DoubleCosetMeasures.sUp A := sUp_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) A

theorem phase_eq (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1))
    (q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a)) (xy : (Loc.IL (m + 1) → E) × (Loc.IN a → E))
    (l ρ : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (hl : Formalism.MainNotions.S.TieN.IntLow M l) (hρ : Formalism.MainNotions.S.TieN.IntUp M ρ)
    (hq : zQ M.R a q = l * zAt a xy * ρ) :
    M.psiR (phQ M.R a q) = M.psiR (Loc.simpleLow (Loc.uLow xy.1) + Loc.simpleUp (Loc.uUp a xy.2)) := by
  have hψ : ∀ x ∈ M.R, M.psiR x = 1 := fun r hr => by
    simpa using (Formalism.MainNotions.LocalModelPeriodLattices.selfDual_of_core M hOK 1).2 M.R.one_mem r hr
  have hLo : Formalism.DoubleCosetMeasures.IsLowUni (rI a l * rI a (Loc.uLow xy.1)) :=
    Formalism.DoubleCosetMeasures.isLowUni_mul E (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))
  have hUp : Formalism.DoubleCosetMeasures.IsUpUni (rI a (Loc.uUp a xy.2) * rI a ρ) :=
    Formalism.DoubleCosetMeasures.isUpUni_mul E (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))
  have hv : Formalism.DoubleCosetMeasures.IsLowUni (((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) := (Formalism.FourierDecayAlt.A5.rep M.R q).1.2.1
  have hu : Formalism.DoubleCosetMeasures.IsUpUni (((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) := (Formalism.FourierDecayAlt.A5.rep M.R q).2.2
  have hvPu : (((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) *
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 * (((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) =
      (rI a l * rI a (Loc.uLow xy.1)) * Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
        (rI a (Loc.uUp a xy.2) * rI a ρ) := by
    have h := congrArg (rI a) hq
    rw [rI_zQ] at h
    unfold zAt at h
    rw [rI_mul, rI_mul, rI_mul, rI_mul, rI_mat] at h
    unfold Formalism.FourierDecayAlt.A5.orbZ at h
    rw [h]
    simp only [Matrix.mul_assoc]
  have hLd : IsUnit (rI a l * rI a (Loc.uLow xy.1)).det := by rw [Formalism.DoubleCosetMeasures.isLowUni_det E hLo]; exact isUnit_one
  have hUd : IsUnit (rI a (Loc.uUp a xy.2) * rI a ρ).det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det E hUp]; exact isUnit_one
  have hfix : ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * (((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)) *
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
      ((((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹) =
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 := by
    calc _ = (rI a l * rI a (Loc.uLow xy.1))⁻¹ * ((((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) *
          Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
          (((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * (rI a l * rI a (Loc.uLow xy.1))) *
          Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
          ((rI a (Loc.uUp a xy.2) * rI a ρ) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹) := by
          rw [hvPu]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hLd, Matrix.mul_nonsing_inv _ hUd, Matrix.one_mul, Matrix.mul_one]
  have h0 := Formalism.DoubleCosetMeasures.Final.phaseWellDef E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 _ _
    (Formalism.DoubleCosetMeasures.isLowUni_mul E (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv) (Formalism.DoubleCosetMeasures.isUpUni_mul E hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)) hfix
  have sa := Formalism.DoubleCosetMeasures.Final.simpleAdd E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum
  rw [(sa _ _).1 (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv, (sa _ _).2 hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)] at h0
  have hLi := (sa (rI a l * rI a (Loc.uLow xy.1))⁻¹ (rI a l * rI a (Loc.uLow xy.1))).1
    (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hLo
  rw [Matrix.nonsing_inv_mul _ hLd, sLow_one] at hLi
  have hUi := (sa (rI a (Loc.uUp a xy.2) * rI a ρ) (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹).2
    hUp (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)
  rw [Matrix.mul_nonsing_inv _ hUd, sUp_one] at hUi
  rw [(sa _ _).1 (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))] at hLi
  rw [(sa _ _).2 (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))] at hUi
  have hph : phQ M.R a q = Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) +
      (Formalism.DoubleCosetMeasures.sLow (rI a (Loc.uLow xy.1)) + Formalism.DoubleCosetMeasures.sUp (rI a (Loc.uUp a xy.2))) := by
    unfold phQ
    linear_combination h0 + hLi + hUi
  have h1 : Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) ∈ M.R :=
    add_mem (by rw [sLow_rI]; exact sLow_mem M.R _ hl.2.2) (by rw [sUp_rI]; exact sUp_mem M.R _ hρ.2.2)
  rw [hph, AddChar.map_add_eq_mul, hψ _ h1, one_mul]
  rw [sLow_rI, sUp_rI, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleLow_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleUp_eq]

theorem nIso_orb (M : Loc.Model F E) {n : ℕ} {Z Z' : Matrix (Fin (n + 1)) (Fin (n + 1)) E}
    (l ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hl : Formalism.MainNotions.S.TieN.IntLow M l) (hρ : Formalism.MainNotions.S.TieN.IntUp M ρ)
    (hZ : Z' = l * Z * ρ) (h1 : ∀ i j, Z' i j ∈ M.R) (h2 : IsUnit Z'.det) (h1' : ∀ i j, Z i j ∈ M.R)
    (h2' : IsUnit Z.det) (Z0 : M.Mat (n + 1)) :
    M.nIso (Formalism.MainNotions.LocalOrbitGerms.Cls.toMat M Z' h1 h2) Z0 = M.nIso (Formalism.MainNotions.LocalOrbitGerms.Cls.toMat M Z h1' h2') Z0 := by
  subst hZ
  unfold Loc.Model.nIso
  rw [Nat.card_congr (Formalism.MainNotions.LocalOrbitGerms.Cls.isoEquiv M _ Z0), Nat.card_congr (Formalism.MainNotions.LocalOrbitGerms.Cls.isoEquiv M _ Z0),
    Formalism.MainNotions.LocalOrbitGerms.Cls.toMat_map, Formalism.MainNotions.LocalOrbitGerms.Cls.toMat_map]
  exact Formalism.DoubleCosetMeasures.Final.isoInv E M.R (n + 1) l ρ Z (lowUni_of M hl) (upUni_of M hρ) hl.2.2 hρ.2.2 _ _ _

theorem val (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) : IntegrandConstantOnOrbit M a c := by
  intro q xy hI hmem
  obtain ⟨l, ρ, hl, hρ, hq⟩ := hmem
  have hIq : ∀ i j, zQ M.R a q i j ∈ M.R := int_of_mem M hI ⟨l, ρ, hl, hρ, hq⟩
  have hdq : IsUnit (zQ M.R a q).det := Formalism.MainNotions.LocalOrbitGerms.Cls.isUnit_det_sub a _
  have hI' : ∀ i j, (Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2) i j ∈ M.R := hI
  have hdz : IsUnit (Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Formalism.L2.SG.Pf.LocModel.uLow_det, Formalism.L2.SG.Pf.LocModel.uUp_det, one_mul,
      mul_one, Formalism.MainNotions.LocalModelPeriodLattices.det_eq]
    exact Formalism.FourierDecayAlt.P.A5x6.pt_det_isUnit _
  rw [Formalism.MainNotions.LocalOrbitGerms.Cls.bbIntegrand_eq]
  unfold valQ Formalism.MainNotions.LocalOrbitGerms.Cls.GG
  rw [dite_eq_left ⟨hIq, hdq⟩, dite_eq_left ⟨hI', hdz⟩, phase_eq M hOK a q xy l ρ hl hρ hq,
    nIso_orb M l ρ hl hρ hq hIq hdq hI' hdz]
  rfl

end Val

end Formalism.L2.SG.Pf.LocOrbCut
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.LocOrbSumPf MeasureTheory
open Classical

variable {D : Formalism.BasicNotions.D7}

theorem wtL_eq_wtZ (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)}
    (ha : modPt δ T T' p w = some a) (Y : MatP D p) :
    wtL M δ T T' p w Y = wtZ (M p) a (orbR (M p) (Y + shM δ T T' p w)) := by
  have hmat : a.mat = modMat δ T T' p w + shM δ T T' p w := modShift_holds δ T T' p w a ha
  have hset : {xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN a → (D.s.atP p).Ep) |
      Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp a xy.2 ∈ kkOrb M p Y} =
      {xy | zAt a xy ∈ orbR (M p) (Y + shM δ T T' p w)} := by
    ext xy
    simp only [Set.mem_ofPred_eq]
    rw [mem_orbR_iff M δ T T' p w Y (zAt a xy), zAt_eq hmat xy, add_sub_cancel_right]
  unfold wtL wtZ muA
  simp only [ha]
  rw [hset]

theorem wtL_count (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)}
    (hOK : (M p).OK) (ha : modPt δ T T' p w = some a) {Y : MatP D p} (hY : ∀ i j, Y i j ∈ (M p).R) :
    {q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) |
      LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w)}.Finite ∧
    wtL M δ T T' p w Y = ({q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) |
      LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w)}.ncard : ℝ) := by
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
  have hZ0 : ∀ i j, (Y + shM δ T T' p w) i j ∈ (M p).R := fun i j =>
    add_mem (hY i j) (shM_mem M δ T T' p w i j)
  obtain ⟨hfin, hsum⟩ := LocOrbCut.wt_gen (M p) hOK a (Y + shM δ T T' p w) hZ0
  set S := {q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) |
      LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w)} with hSdef
  have hsupp : (Function.support (fun q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) =>
      if LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w) then (1 : ℂ) else 0)) = S := by
    ext q
    simp [hSdef]
  rw [hsupp] at hfin
  refine ⟨hfin, ?_⟩
  rw [wtL_eq_wtZ M δ ha Y]
  have hc : (wtZ (M p) a (orbR (M p) (Y + shM δ T T' p w)) : ℂ) = (S.ncard : ℂ) := by
    rw [hsum, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by rw [hsupp]; simp)]
    rw [Finset.sum_boole, Set.ncard_eq_toFinset_card S hfin]
    congr 2
    exact Finset.filter_true_of_mem (fun q hq => hfin.mem_toFinset.1 hq)
  exact_mod_cast hc

end Formalism.L2.SG.Pf.Coef
end
end
