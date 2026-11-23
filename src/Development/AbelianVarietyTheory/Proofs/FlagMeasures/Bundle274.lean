module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle255
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle090
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle267
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle261
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle265
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle266
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Std.Tactic.BVDecide.Normalize.Bool
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction

@[expose] public section

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.GapDegreeTie

open Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

theorem deg_eq_mul_fdegH : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS), cdScaleTie D → GoodW D τ w w' θ W → ∃ κ : ℝ, 0 < κ ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → (∃ h : ℝ, GapAtLeast (epsSH D.R) lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) → ∀ v : A.H, v ≠ 0 → A.deg = κ * PI.BesselPeriodGGP.fdegH W.μG A.σ v ∧ 0 < A.deg := by
  intro _ D τ w w' θ W _ hW
  have hμ : PI.BesselPeriodGGP.IsHaarOn (GG D.R.k D.R.rS) W.μG := hW.2.2.2.2.2.2.1
  by_cases hQ : ∃ Q, IsCayley D.R.k D.R.rS (epsSH D.R) Q
  swap
  · refine ⟨1, one_pos, fun lam A hA _ => absurd ?_ hQ⟩
    obtain ⟨P, hP, -⟩ := hA.2.2.2.2.2.2.2.2.2.2
    exact ⟨P, hP⟩
  obtain ⟨Q, hQ⟩ := hQ
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1
  obtain ⟨a, ha0, hat, ha⟩ := GlobalTheory.BesselDegree.haar_eq_smul hQd hQ.2 W.μG hμ
  set s : ℝ≥0∞ := ((D.s.cdScale _ (epsSH D.R) : NNReal) : ℝ≥0∞) with hs
  have hs0 : s ≠ 0 := ENNReal.coe_ne_zero.2 (D.s.cdScale_pos _ _).ne'
  have hst : s ≠ ∞ := ENNReal.coe_ne_top
  have hb0 : a / s ≠ 0 := (ENNReal.div_pos ha0 hst).ne'
  have hbt : a / s ≠ ∞ := (ENNReal.div_lt_top hat hs0).ne
  have hκ : 0 < (a / s).toReal := ENNReal.toReal_pos hb0 hbt
  refine ⟨(a / s).toReal, hκ, fun lam A hA _ v hv => ?_⟩
  obtain ⟨P, hP, hd, hS⟩ := hA.2.2.2.2.2.2.2.2.2.2
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hme : MeasurableEmbedding (phi (epsSH D.R) P) :=
    (phi_closedEmbedding (ε := epsSH D.R) Formalism.REAL.isClosedEmbeddingMatrix hPd).measurableEmbedding
  have hb : W.μG = (a / s) • (s • Formalism.REAL.muG (epsSH D.R)).map (phi (epsSH D.R) P) := by
    rw [Measure.map_smul, smul_smul, ENNReal.div_mul_cancel hs0 hst, GlobalTheory.DegreeTie.map_phi_eq hP hQ]
    · exact ha
    · exact hme.measurable.aemeasurable
  have hf : PI.BesselPeriodGGP.fdegH W.μG A.σ v = A.deg / (a / s).toReal := by
    refine Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq (div_pos hd hκ) (fun v w v' w' => ?_) hv
    obtain ⟨h1, h2⟩ := hS v w v' w'
    rw [hb]
    constructor
    · refine Integrable.smul_measure ?_ hbt
      rw [hme.integrable_map_iff]
      exact h1
    · rw [integral_smul_measure, hme.integral_map]
      have h3 : ∫ g, ⟪w, A.σ (Matrix.of (phi (epsSH D.R) P g)) v⟫_ℂ *
          star ⟪w', A.σ (Matrix.of (phi (epsSH D.R) P g)) v'⟫_ℂ
          ∂(s • Formalism.REAL.muG (epsSH D.R)) = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((A.deg : ℝ) : ℂ) := h2
      rw [h3, Complex.ofReal_div, div_div_eq_mul_div, Complex.real_smul]
      ring
  refine ⟨?_, hd⟩
  rw [hf]
  field_simp

end GlobalTheory.GapDegreeTie

end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.RealFibre

private lemma eq_zero_of_sum_star_mul_const_mul_eq_zero {n : ℕ} (x : Fin n → ℂ) (c : ℂ) (hc : c ≠ 0)
    (h : ∑ i, star (x i) * (c * x i) = 0) : x = 0 := by
  have h1 : c * ((∑ i, Complex.normSq (x i) : ℝ) : ℂ) = 0 := by
    rw [← h, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (Complex.normSq (x i) : ℂ) = star (x i) * x i := Complex.normSq_eq_conj_mul_self
    rw [e]; ring
  have h2 : ∑ i, Complex.normSq (x i) = 0 := by
    have h3 := (mul_eq_zero.mp h1).resolve_left hc
    exact_mod_cast h3
  funext i
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (x j))).mp h2 i
    (Finset.mem_univ i)
  simpa using h4

theorem one_le_rkR_of_isIsoC {n : ℕ} {ε : Fin n → Bool} {W : Submodule ℂ (Fin n → ℂ)} (hW : IsIsoC ε W) :
    1 ≤ rkR ε := by
  unfold IsIsoC herm Jm at hW
  obtain ⟨hne, hiso⟩ := hW
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hq := hiso x hxW x hxW

  have hall : ∀ b : Bool, ∃ i, ε i = b := by
    intro b
    by_contra hno
    push_neg at hno
    have hb : ∀ i, ε i = !b := fun i => by
      have h' := hno i
      cases hε : ε i <;> cases b <;> simp_all
    apply hx0
    apply eq_zero_of_sum_star_mul_const_mul_eq_zero x (if (!b) = true then (1 : ℂ) else -1) (by split_ifs <;> norm_num)
    rw [← hq]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, hb]
  obtain ⟨i, hi⟩ := hall true
  obtain ⟨j, hj⟩ := hall false
  unfold rkR
  apply le_min
  · exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  · exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩

theorem decE_le_exp {q : ℕ} (hq : 1 ≤ q) {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    decE q h t ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt q) * t)) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hs1 : 1 ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hq)
  unfold decE
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  obtain ⟨s, hsd⟩ : ∃ s, s = Real.sqrt q := ⟨_, rfl⟩
  rw [← hsd] at hs hs1 ⊢
  have hs0 : s ≠ 0 := hs.ne'

  have key : t / s - min (2 * t ^ 2) (t / s) ≤ 1 := by
    rcases le_total (2 * t ^ 2) (t / s) with h' | h'
    · rw [min_eq_left h']
      obtain ⟨u, hu⟩ : ∃ u, u = t / s := ⟨_, rfl⟩
      rw [← hu]
      have ht : t = u * s := by rw [hu]; field_simp
      have h2 : t ^ 2 = u ^ 2 * s ^ 2 := by rw [ht]; ring
      have h1 : 0 ≤ u ^ 2 * (s ^ 2 - 1) := mul_nonneg (sq_nonneg u) (by nlinarith)
      nlinarith [sq_nonneg (u - 1 / 4)]
    · rw [min_eq_right h']; norm_num
  have e : h / (8 * s) * t = h / 8 * (t / s) := by ring
  rw [e]
  nlinarith [mul_nonneg hh (sub_nonneg.mpr key)]

theorem rate_lt {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q) {h : ℝ}
    (hh : 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    0 ≤ h ∧ 12 * (n : ℝ) * q < h / (8 * Real.sqrt q) := by
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hpow : (q : ℝ) ^ ((3 : ℝ) / 2) = q * Real.sqrt q := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hq0, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [hpow] at hh
  have hP : 0 < (n : ℝ) * q * Real.sqrt q := by positivity
  refine ⟨by nlinarith, ?_⟩
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

private lemma list_prod_eq_take_mul_pair_mul_drop {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → ℂ) (v : ι) :
    ∏ u, F u = F v * ∏ u ∈ Finset.univ.erase v, F u :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ v)).symm

private lemma rkR_le' {n : ℕ} (ε : Fin n → Bool) : rkR ε ≤ n := by
  unfold rkR
  calc min (Finset.univ.filter fun a => ε a = true).card (Finset.univ.filter fun a => ε a = false).card
      ≤ (Finset.univ.filter fun a => ε a = true).card := min_le_left _ _
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

theorem integral_phe_eq_zero : StrictLow → ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → LocDec B h → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → ∀ (v : InfinitePlace B.I.F) (Wv : Submodule ℂ (Fin B.I.n → ℂ)), IsIsoC (B.I.ε v) Wv → ∀ ν : Measure (UJ (B.I.ε v)), IsHaarSub (NW (B.I.ε v) Wv) ν → ∀ x y : B.I.GA, ∫ m, phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) ∂ν = 0 := by
  classical
  intro hS B d h hD hL hh v Wv hW ν hν x y
  obtain ⟨hHC, hDS, hLow, hFd⟩ := hD v
  have hDS' := hDS
  obtain ⟨_, _, hU, _⟩ := hDS'
  obtain ⟨hw1, hwS⟩ := hLow
  have hq1 : 1 ≤ rkR (B.I.ε v) := one_le_rkR_of_isIsoC hW
  have hn1 : 1 ≤ B.I.n := le_trans hq1 (rkR_le' _)
  obtain ⟨h0, hc⟩ := rate_lt hn1 hq1 (hh v)

  obtain ⟨α, hαs, hαc, hαfix⟩ := exists_smooth_fix_lowKSub B.I.n (B.I.ε v) (B.lam v) (B.H v) (B.σ v) hU
    (hS B.I.n (B.I.ε v) (B.lam v) hHC (B.H v) (B.σ v) hDS).1

  have hT := GlobalTheory.T.unitary_rep_matrixCoeff_integral_eq_zero B.I.n (B.I.ε v) Wv ν hW hν (B.H v) (B.σ v) (d v)
    (h / (8 * Real.sqrt (rkR (B.I.ε v) : ℝ))) α (B.w v) hU hFd hc hw1 hαs hαc
    (fun u => hαfix (B.w v) hwS u)
    ⟨Real.exp (h / 8), fun g => (hL v g).trans (decE_le_exp hq1 h0 _)⟩ (x.1 v) (y.1 v)
  have hstar : ∫ m, star ⟪B.w v, B.σ v (uMat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ ∂ν = 0 := by
    refine (integral_conj (μ := ν)
      (f := fun m => ⟪B.w v, B.σ v (uMat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ)).trans ?_
    rw [hT]; simp

  have hfun : ∀ m : UJ (B.I.ε v),
      phe B d (x * (open Classical in ((Pi.mulSingle v m, 1) : B.I.GA)) * y) =
        ((((∏ u, d u : ℝ) : ℂ) * star (∏ u ∈ Finset.univ.erase v,
          ⟪B.w u, B.σ u (uMat (x.1 u * y.1 u)) (B.w u)⟫_ℂ)) * B.e (x.2 * y.2)) *
        star ⟪B.w v, B.σ v (uMat (x.1 v * m * y.1 v)) (B.w v)⟫_ℂ := by
    intro m
    have hrest : ∏ u ∈ Finset.univ.erase v,
        ⟪B.w u, B.σ u (uMat (x.1 u * (open Classical in (Pi.mulSingle v m : B.I.Ginf)) u * y.1 u)) (B.w u)⟫_ℂ =
        ∏ u ∈ Finset.univ.erase v, ⟪B.w u, B.σ u (uMat (x.1 u * y.1 u)) (B.w u)⟫_ℂ :=
      Finset.prod_congr rfl fun u hu => by
        rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hu), mul_one]
    simp only [GlobalTheory.Count.phe, GlobalTheory.Count.ph, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, mul_one]
    rw [list_prod_eq_take_mul_pair_mul_drop _ v, hrest, Pi.mulSingle_eq_same, star_mul']
    ring
  refine (integral_congr_ae (ae_of_all ν hfun)).trans ?_
  rw [integral_const_mul, hstar, mul_zero]

end GlobalTheory.RealFibre
end

section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.BigConvLevi

open Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.BigCellHermitian

variable {k r : ℕ}

theorem hb_mul_self : Hb k * Hb k = 1 := by
  unfold Hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

theorem isUnit_det_of_hb {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : μᴴ * Hb k * μ = Hb k) :
    IsUnit μ.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hb k * μᴴ * Hb k)
  calc Hb k * μᴴ * Hb k * μ = Hb k * (μᴴ * Hb k * μ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, hb_mul_self]

theorem conj_mem_of_levi (A B n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hAB : A * B = 1) (hA : A ∈ UH (Hpk k r)) (hB : B ∈ UH (Hpk k r))
    (hA1 : ∀ i j, ¬ mid k r j → A i j = if i = j then 1 else 0)
    (hB1 : ∀ i j, ¬ mid k r j → B i j = if i = j then 1 else 0)
    (hB3 : ∀ m j, mid k r j → ¬ mid k r m → B m j = 0)
    (hn : n ∈ Nset k r) : A * n * B ∈ Nset k r := by
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hA hn.1) hB, ?_, ?_⟩
  · intro a i hai
    have hea : ¬ mid k r (eI k r a) := by
      have := a.isLt; simp only [mid, eI]; omega
    rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
    · rw [hB1 _ _ hea, if_pos rfl, mul_one, Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
      · rw [hn.2.1 a (eI k r a) (by simp [eI]), if_pos rfl, mul_one, hA1 _ _ hea]
      · intro l _ hl
        by_cases hla : a.val ≤ l.val
        · rw [hn.2.1 a l hla, if_neg hl, mul_zero]
        · have hlm : ¬ mid k r l := by have := a.isLt; simp only [mid]; omega
          rw [hA1 i l hlm, if_neg (by rw [Fin.ext_iff]; omega), zero_mul]
      · simp
    · intro l _ hl
      rw [hB1 _ _ hea, if_neg hl, mul_zero]
    · simp
  · intro i j hj1 hj2 hi
    have hjm : mid k r j := ⟨hj1, hj2⟩
    rw [Matrix.mul_apply]
    have key : ∀ m, (A * n) i m * B m j = A i m * B m j := by
      intro m
      by_cases hm : mid k r m
      · congr 1
        rw [Matrix.mul_apply, Finset.sum_eq_single m]
        · rw [hn.2.2 m m hm.1 hm.2 hm.1, if_pos rfl, mul_one]
        · intro l _ hl
          by_cases hlr : r ≤ l.val
          · rw [hn.2.2 l m hm.1 hm.2 hlr, if_neg hl, mul_zero]
          · have hlm : ¬ mid k r l := by simp only [mid]; omega
            rw [hA1 i l hlm, if_neg (by rw [Fin.ext_iff]; omega), zero_mul]
        · simp
      · rw [hB3 m j hjm hm, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl (fun m _ => key m), ← Matrix.mul_apply, hAB, Matrix.one_apply]

theorem cellQuot_props (c : Fin r → ℂ) (μ₁ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hc : ∀ a, c a ≠ 0) (h₁ : μ₁ᴴ * Hb k * μ₁ = Hb k) (h : μᴴ * Hb k * μ = Hb k) :
    (bigCell k r c μ₁)⁻¹ * bigCell k r c μ ∈ UH (Hpk k r) ∧
    (∀ i j, ¬ mid k r j → ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) i j = if i = j then 1 else 0) ∧
    (∀ m j, mid k r j → ¬ mid k r m → ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) m j = 0) := by
  have hg₁ := big_cell_mem_holds k r c μ₁ hc h₁
  have hg := big_cell_mem_holds k r c μ hc h
  have u₁ := WeylGroupFacts.isUnit_of_uh hg₁
  have hμ₁ := isUnit_det_of_hb h₁
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hg₁) hg, ?_, ?_⟩
  · intro i j hj
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun l _ => by rw [bc_out_col c μ μ₁ l j hj]),
      ← Matrix.mul_apply, Matrix.nonsing_inv_mul _ u₁, Matrix.one_apply]
  · intro m j hj hm
    obtain ⟨t, rfl⟩ := mid_exists hj
    have e1 : (Pi.single (wI k r t) 1 : Fin (2 * r + k + 1) → ℂ) = jV k r (Pi.single t 1) := by
      funext i
      by_cases hi : mid k r i
      · obtain ⟨s, rfl⟩ := mid_exists hi
        rw [jV_wI]
        simp only [Pi.single_apply, wI_inj.eq_iff]
      · rw [jV_out _ hi, Pi.single_apply, if_neg (fun he : i = wI k r t => hi (he ▸ mid_wI t))]
    have col : ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) m (wI k r t) =
        (((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) *ᵥ Pi.single (wI k r t) 1) m := by
      rw [Matrix.mulVec_single_one]; rfl
    have back : ∀ v : Fin (k + 1) → ℂ,
        jV k r v = bigCell k r c μ₁ *ᵥ jV k r (μ₁⁻¹ *ᵥ v) := by
      intro v
      rw [bigCell_mulVec_jV, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hμ₁, Matrix.one_mulVec]
    rw [col, ← Matrix.mulVec_mulVec, e1, bigCell_mulVec_jV, back, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ u₁, Matrix.one_mulVec, jV_out _ hm]

theorem levi_conj_mem_iff : ∀ (k r : ℕ) (c : Fin r → ℂ) (μ₁ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    (∀ a, c a ≠ 0) → μ₁ᴴ * Formalism.QuantumDeterminants.Hb k * μ₁ = Formalism.QuantumDeterminants.Hb k →
    μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k →
    ∀ n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, n ∈ Formalism.QuantumDeterminants.Nset k r ↔
      (Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ * n *
        ((Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ)⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r := by
  intro k r c μ₁ μ hc h₁ h n
  have u₁ := WeylGroupFacts.isUnit_of_uh (big_cell_mem_holds k r c μ₁ hc h₁)
  have u := WeylGroupFacts.isUnit_of_uh (big_cell_mem_holds k r c μ hc h)
  obtain ⟨hA, hA1, hA3⟩ := cellQuot_props c μ₁ μ hc h₁ h
  obtain ⟨hB, hB1, hB3⟩ := cellQuot_props c μ μ₁ hc h h₁
  have hinv : ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ)⁻¹ = (bigCell k r c μ)⁻¹ * bigCell k r c μ₁ := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ u₁]
  have hAB : (bigCell k r c μ₁)⁻¹ * bigCell k r c μ * ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ u, Matrix.nonsing_inv_mul _ u₁]
  have hBA : (bigCell k r c μ)⁻¹ * bigCell k r c μ₁ * ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ u₁, Matrix.nonsing_inv_mul _ u]
  rw [hinv]
  constructor
  · exact conj_mem_of_levi _ _ n hAB hA hB hA1 hB1 hB3
  · intro hn'
    have := conj_mem_of_levi _ _ _ hBA hB hA hB1 hA1 hA3 hn'
    have e : (bigCell k r c μ)⁻¹ * bigCell k r c μ₁ *
        ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ * n * ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁)) *
        ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) = n := by
      calc _ = ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁ * ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ)) * n *
            ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁ * ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ)) := by
            simp only [Matrix.mul_assoc]
        _ = n := by rw [hBA, Matrix.one_mul, Matrix.mul_one]
    rwa [e] at this

end GlobalTheory.BigConvLevi
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.classNumber_rootDisc_factor_le_HHZ : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ Z : GramM D, (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f * 9 ^ D.R.f ≤ HHZ D large₂.sc.b C Z := by
  first | exact @GlobalTheory.LoopC.SizeQ.main | exact GlobalTheory.LoopC.SizeQ.main | (intros; apply GlobalTheory.LoopC.SizeQ.main <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.orth_transversal_flags_inf_isotropic_eq_bot : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' : LFlag S r T'), Submodule.IsFullLattice E Λ → IsLift Λ F → IsLift Λ F' → Gval F F' ≠ 0 → Hp Λ F F' ≤ orth S (Xplus F) ∧ Hp Λ F F' ≤ orth S (Xplus F') ∧ Hp Λ F F' ⊓ Xsp F = ⊥ := by
  first | exact @GlobalTheory.LoopC.PerpFlags.main | exact GlobalTheory.LoopC.PerpFlags.main | (intros; apply GlobalTheory.LoopC.PerpFlags.main <;> first | assumption | exact (by assumption : Submodule.IsFullLattice _ _).toIsLattice)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.hermitianData_with_term_single_orbit_primeTo : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → P.PrimeTo → ∀ (d d' : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d' t' → Datum.Rel d d' := by
  first | exact @GlobalTheory.HL.PrimeToOrbit.main | exact GlobalTheory.HL.PrimeToOrbit.main | (intros; apply GlobalTheory.HL.PrimeToOrbit.main <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.isHaarOn_besselSubgroup_prod_map : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (UWset k r z) μW → IsHaarOn (Nset k r) μN → IsHaarOn (Sset k r z) ((μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) := by
  first | exact @GlobalTheory.SgInf.ProdHaarS.isHaarOn_prod_map | exact GlobalTheory.SgInf.ProdHaarS.isHaarOn_prod_map | (intros; apply GlobalTheory.SgInf.ProdHaarS.isHaarOn_prod_map <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.two_le_rootDiscriminant_and_split_arithmetic_conditions : ∀ D : D7, 2 ≤ D.host.rdE ∧ ArithmeticConditionsOfDatum D := by
  first | exact @GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 | exact GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 | (intros; apply GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 <;> assumption)
end
