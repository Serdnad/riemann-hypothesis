module

public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.Bundle008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.FrameExists2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle072
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliTwoByTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle065
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle086
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle026
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.UniformSpace.Matrix

@[expose] public section

section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem bcWeight_nonneg (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (sub_nonneg.2 h) _)
  · exact le_rfl

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem adj_local (Θ : DiffOp k r Wp Wq) {f₁ f₂ : Mat k r → (Wq →L[ℂ] Wp)} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) : ∀ x ∈ V, x ∈ GV k r → opAdj Θ f₁ x = opAdj Θ f₂ x := by
  intro x hx hxG
  unfold opAdj
  congr 1
  refine List.map_congr_left fun T _ => ?_
  rw [PositiveOrbitOpen.rw_local (f₁ := fun y => T.coefAdj y (f₁ y)) (f₂ := fun y => T.coefAdj y (f₂ y)) hV
    (fun y hy hyG => by simp only [h y hy hyG]) T.word.reverse
    (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) x hx hxG]

theorem betaBig_congr (D : RealPlaceData k r Wp Wq)
    {J₁ J₁' J₂ J₂' : Mat k r → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)}
    (h : ∀ g ∈ Om k r D.z D.z', J₁ g = J₂ g) (h' : ∀ g ∈ Om k r D.z D.z', J₁' g = J₂' g) :
    betaBig k r (Tz k r D.z) (Tz k r D.z') D.μsec J₁ J₁' = betaBig k r (Tz k r D.z) (Tz k r D.z') D.μsec J₂ J₂' := by
  unfold betaBig
  apply integral_congr_ae
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ Om k r D.z D.z' := hq hQ
    simp only [h _ hg, h' _ hg]
  · have h0 : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (bcWeight_nonneg _ _ q)
    simp only [h0, Complex.ofReal_zero, zero_mul]

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

section

namespace Formalism.FourierDecayAlt.P.TBBx3

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate ENNReal

noncomputable section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem vecCutAt_of_one (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hχ : ∀ x, 1 ≤ x → χ x = 1) : TBB.VecCutAt p χ F := by
  intro ε hε γ hγ hle
  have hle0 : ε ≤ D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r γ := hle
  unfold KB.Pl.V D.vecV
  split_ifs with h h'
  · rw [Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_cutF]
    have hG := Formalism.FourierDecayAlt.P.ptG_spec P.k P.r p.T.base.z p.T.base.z' γ h'.choose hγ h'.choose_spec.2.1
    have hle' : ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' h'.choose := hG ▸ hle0
    rw [hχ _ ((one_le_div hε).mpr hle'), Complex.ofReal_one, one_smul]
  · rfl
  · rfl

theorem hsInner_self_re_nonneg (A : Wq →L[ℂ] Wp) : 0 ≤ (B.hsInner A A).re := by
  unfold B.hsInner
  have h := inner_self_nonneg (𝕜 := ℂ) (x := B.hsVec A)
  simpa using h

theorem rr_top_re_nonneg (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ) (w : List C.Letter)
    (h : C.LPt) (hi : P.r < i) : 0 ≤ (p.RR F i w h h).re := by
  unfold KB.Pl.RR D.RRplace
  by_cases h1 : D.IsLocPt h i ∧ D.IsLocPt h i
  · rw [dite_eq_left h1, dite_eq_right (by omega)]
    by_cases h2 : i = P.r + 1
    · rw [if_pos h2]
      by_cases h3 : w = []
      · rw [if_pos h3]
        exact hsInner_self_re_nonneg _
      · rw [if_neg h3]
        unfold Top.topOf
        rw [Complex.re_sum]
        refine Finset.sum_nonneg fun e _ => ?_
        rw [Complex.re_sum]
        refine Finset.sum_nonneg fun ρ _ => ?_
        rw [Complex.re_ofReal_mul]
        exact mul_nonneg (mul_self_nonneg _) (hsInner_self_re_nonneg _)
    · rw [if_neg h2]
      simp
  · rw [dite_eq_right h1]
    simp

theorem posAt_of_forms (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ)
    (hnn : ∀ y, 0 ≤ nn y)
    (hform : ∀ (j : ℕ) (w : List C.Letter) (h : C.LPt), j ≤ P.r → TBB.AdmW P p.l0 Y w → w.length ≤ N →
      0 ≤ (p.RR F j w h h).re) : TBB.PosAt p nn F Y N := by
  intro i w h hw hN
  unfold TBB.Ew TBB.NP
  rw [Complex.re_ofReal_mul]
  apply mul_nonneg
  · apply div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    unfold TBB.normC
    apply List.prod_nonneg
    intro a ha
    rw [List.mem_map] at ha
    obtain ⟨l, _, rfl⟩ := ha
    exact hnn _
  · by_cases hi : i ≤ P.r
    · exact hform i w h hi hw hN
    · exact rr_top_re_nonneg p F i w h (by omega)

theorem ew_zero_nil (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) :
    TBB.Ew p nn G 0 w [] = (p.RR G 0 w [] []).re / TBB.normC nn w := by
  have h1 : ∀ TT : ℝ, TBB.nPt P.k P.r TT [] = 1 := fun TT => by simp [TBB.nPt, C.nAux]
  unfold TBB.Ew TBB.NP
  simp only [h1, Real.sqrt_one, one_mul]
  rw [Complex.re_ofReal_mul, one_div, inv_mul_eq_div]

theorem limZeroAt_of_limits (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (N : ℕ) (κ₀ : ℝ)
    (hE : ∀ w, TBB.AdmW P p.l0 Y w → w.length ≤ N → ∃ sz : ℝ, 0 ≤ sz ∧ sz ≤ TBB.normC nn w ∧
      Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0)
        (𝓝 (sz * (B.beta p.T.base F F).re)))
    (hB : ENNReal.ofReal (B.beta p.T.base F F).re ≤ ENNReal.ofReal κ₀ * TBB.jN2 p F) :
    TBB.LimZeroAt p nn χ F Y N κ₀ := by
  intro w hw hN
  obtain ⟨sz, hsz0, hszn, hlim⟩ := hE w hw hN
  have hEw : ∀ ε, TBB.Ew p nn (D.cutF p.T.base χ F ε) 0 w [] =
      (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re / TBB.normC nn w := fun ε => ew_zero_nil p nn _ w
  have hlim2 : Tendsto (fun ε => ENNReal.ofReal (TBB.Ew p nn (D.cutF p.T.base χ F ε) 0 w [])) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (sz * (B.beta p.T.base F F).re / TBB.normC nn w))) := by
    simp only [hEw]
    exact ENNReal.tendsto_ofReal (hlim.div_const _)
  rw [hlim2.limsup_eq]
  refine le_trans ?_ hB
  rw [ENNReal.ofReal_le_ofReal_iff']
  have hn0 : 0 ≤ TBB.normC nn w := le_trans hsz0 hszn
  by_cases hb : 0 ≤ (B.beta p.T.base F F).re
  · left
    rcases hn0.lt_or_eq with hpos | hzero
    · rw [div_le_iff₀ hpos]
      calc sz * (B.beta p.T.base F F).re ≤ TBB.normC nn w * (B.beta p.T.base F F).re :=
            mul_le_mul_of_nonneg_right hszn hb
        _ = (B.beta p.T.base F F).re * TBB.normC nn w := mul_comm _ _
    · rw [← hzero, div_zero]
      exact hb
  · right
    push_neg at hb
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hsz0 hb.le) hn0

end

end Formalism.FourierDecayAlt.P.TBBx3

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

theorem vector_truncation_at_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hχ : ∀ x, 1 ≤ x → χ x = 1) : Formalism.FourierDecayAlt.TBB.VecCutAt p χ F := by
  exact TBBx3.vecCutAt_of_one p χ F hχ

theorem limit_zero_at_place {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (nn : ℝ → ℝ) (χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Y : Finset ℝ) (N : ℕ) (κ₀ : ℝ)
    (hE : ∀ w, Formalism.FourierDecayAlt.TBB.AdmW P p.l0 Y w → w.length ≤ N → ∃ sz : ℝ, 0 ≤ sz ∧ sz ≤ Formalism.FourierDecayAlt.TBB.normC nn w ∧
      Tendsto (fun ε : ℝ => (p.RR (D.cutF p.T.base χ F ε) 0 w [] []).re) (𝓝[>] 0)
        (𝓝 (sz * (B.beta p.T.base F F).re)))
    (hB : ENNReal.ofReal (B.beta p.T.base F F).re ≤ ENNReal.ofReal κ₀ * Formalism.FourierDecayAlt.TBB.jN2 p F) :
    Formalism.FourierDecayAlt.TBB.LimZeroAt p nn χ F Y N κ₀ := by
  exact TBBx3.limZeroAt_of_limits p nn χ F Y N κ₀ hE hB

end Formalism.FourierDecayAlt.P
end

section

open Matrix Finset Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

namespace GroupGeneratedByExp

section Banach

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem norm_pow_mul_le (x u : 𝔸) (n : ℕ) : ‖x ^ n * u‖ ≤ ‖x‖ ^ n * ‖u‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, pow_succ', mul_assoc]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

theorem norm_exp_mul_le (x u : 𝔸) : ‖NormedSpace.exp x * u‖ ≤ Real.exp ‖x‖ * ‖u‖ := by
  have h1 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • x ^ n) * u) (NormedSpace.exp x * u) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x).mul_right u
  have h2 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • ‖x‖ ^ n) * ‖u‖) (Real.exp ‖x‖ * ‖u‖) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖).mul_right ‖u‖
  refine h1.norm_le_of_bounded h2 fun n => ?_
  rw [smul_mul_assoc, norm_smul, smul_eq_mul, mul_assoc, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_pow_mul_le x u n) (by positivity)

theorem norm_pow_mul_le' {a : 𝔸} {q : ℝ} (hq : 0 ≤ q) (ha : ∀ u, ‖a * u‖ ≤ q * ‖u‖) (m : ℕ) (u : 𝔸) :
    ‖a ^ m * u‖ ≤ q ^ m * ‖u‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, pow_succ', mul_assoc]
    exact (ha _).trans (mul_le_mul_of_nonneg_left ih hq)

theorem norm_pow_sub_pow_le {a b : 𝔸} {q : ℝ} (hq : 1 ≤ q) (ha : ∀ u, ‖a * u‖ ≤ q * ‖u‖)
    (hb : ∀ u, ‖b * u‖ ≤ q * ‖u‖) (m : ℕ) :
    ‖a ^ m - b ^ m‖ ≤ (m : ℝ) * q ^ m * (‖a - b‖ * ‖(1 : 𝔸)‖) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  induction m with
  | zero => simp
  | succ m ih =>
    have e : a ^ (m + 1) - b ^ (m + 1) = a * (a ^ m - b ^ m) + (a - b) * b ^ m := by
      rw [pow_succ', pow_succ']; noncomm_ring
    have h1 : ‖a * (a ^ m - b ^ m)‖ ≤ q * ((m : ℝ) * q ^ m * (‖a - b‖ * ‖(1 : 𝔸)‖)) :=
      (ha _).trans (mul_le_mul_of_nonneg_left ih hq0)
    have h2 : ‖b ^ m‖ ≤ q ^ (m + 1) * ‖(1 : 𝔸)‖ := by
      have := norm_pow_mul_le' hq0 hb m 1
      rw [mul_one] at this
      refine this.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact pow_le_pow_right₀ hq (Nat.le_succ m)
    have h3 : ‖(a - b) * b ^ m‖ ≤ ‖a - b‖ * (q ^ (m + 1) * ‖(1 : 𝔸)‖) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    rw [e]
    refine (norm_add_le _ _).trans ((add_le_add h1 h3).trans (le_of_eq ?_))
    push_cast
    ring

theorem diff_hasDerivAt (X Y : 𝔸) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * NormedSpace.exp (t • Y) - NormedSpace.exp (t • (X + Y))) 0 0 := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
  have h3 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (X + Y) 0
  have h := (h1.mul h2).sub h3
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, mul_one, sub_self] at h
  exact h

theorem trotter (X Y : 𝔸) :
    Tendsto (fun n : ℕ => (NormedSpace.exp (((n : ℝ)⁻¹) • X) * NormedSpace.exp (((n : ℝ)⁻¹) • Y)) ^ n) atTop
      (𝓝 (NormedSpace.exp (X + Y))) := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  set s : ℝ := ‖X‖ + ‖Y‖ with hs
  set F : ℝ → 𝔸 := fun t : ℝ =>
    NormedSpace.exp (t • X) * NormedSpace.exp (t • Y) - NormedSpace.exp (t • (X + Y)) with hF
  have hF0 : F 0 = 0 := by simp [hF, NormedSpace.exp_zero]
  have hsl := (diff_hasDerivAt X Y).tendsto_slope_zero
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_inv_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact (inv_pos.2 this).ne'
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) • F ((n : ℝ)⁻¹)) atTop (𝓝 0) := by
    have := hsl.comp hinv
    refine this.congr fun n => ?_
    simp only [Function.comp, zero_add, inv_inv]
    rw [show NormedSpace.exp ((0 : ℝ) • X) * NormedSpace.exp ((0 : ℝ) • Y) - NormedSpace.exp ((0 : ℝ) • (X + Y)) = 0
      from hF0, sub_zero]
  have h2 : Tendsto (fun n : ℕ => Real.exp s * ‖(1 : 𝔸)‖ * ‖(n : ℝ) • F ((n : ℝ)⁻¹)‖) atTop (𝓝 0) := by
    have := (h1.norm).const_mul (Real.exp s * ‖(1 : 𝔸)‖)
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ h2
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hni : (0 : ℝ) ≤ (n : ℝ)⁻¹ := (inv_pos.2 hn0).le
  have hb : NormedSpace.exp (X + Y) = NormedSpace.exp (((n : ℝ)⁻¹) • (X + Y)) ^ n := by
    rw [← NormedSpace.exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
  have hq : (1 : ℝ) ≤ Real.exp ((n : ℝ)⁻¹ * s) := Real.one_le_exp (by positivity)
  have ha : ∀ u : 𝔸, ‖NormedSpace.exp (((n : ℝ)⁻¹) • X) * NormedSpace.exp (((n : ℝ)⁻¹) • Y) * u‖ ≤
      Real.exp ((n : ℝ)⁻¹ * s) * ‖u‖ := by
    intro u
    rw [mul_assoc]
    refine (norm_exp_mul_le _ _).trans ?_
    refine (mul_le_mul_of_nonneg_left (norm_exp_mul_le _ _) (Real.exp_pos _).le).trans (le_of_eq ?_)
    rw [← mul_assoc, ← Real.exp_add, norm_smul, norm_smul, Real.norm_of_nonneg hni, hs, mul_add]
  have hb' : ∀ u : 𝔸, ‖NormedSpace.exp (((n : ℝ)⁻¹) • (X + Y)) * u‖ ≤ Real.exp ((n : ℝ)⁻¹ * s) * ‖u‖ := by
    intro u
    refine (norm_exp_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [Real.exp_le_exp, norm_smul, Real.norm_of_nonneg hni]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hni
  rw [hb]
  refine (norm_pow_sub_pow_le hq ha hb' n).trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul, show (n : ℝ) * ((n : ℝ)⁻¹ * s) = s by field_simp, norm_smul, Real.norm_of_nonneg hn0.le]
  ring

end Banach

theorem trotterMx (N : ℕ) (X Y : Matrix (Fin N) (Fin N) ℂ) :
    Tendsto (fun n : ℕ => (NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • X) * NormedSpace.exp ((((n : ℝ)⁻¹ : ℝ) : ℂ) • Y)) ^ n) atTop
      (𝓝 (NormedSpace.exp (X + Y))) := by
  let _ := Matrix.linftyOpNormedRing (n := Fin N) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℂ)
  have h := trotter X Y
  simp only [Complex.coe_smul]
  exact h

section Rep

variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem group_eq_exp (φ : ℝ → (W →L[ℂ] W)) (A : W →L[ℂ] W) (h0 : φ 0 = 1)
    (hA : ∀ t, HasDerivAt φ ((φ t).comp A) t) (t : ℝ) : φ t = NormedSpace.exp (t • A) := by
  have hcW : CompleteSpace W := FiniteDimensional.complete ℂ W
  let _ : NormedAlgebra ℚ (W →L[ℂ] W) := NormedAlgebra.restrictScalars ℚ ℂ (W →L[ℂ] W)
  have hE : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-A)))
      ((-A) * NormedSpace.exp (s • (-A))) s := fun s => hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-A) s
  have hψ : ∀ s : ℝ, HasDerivAt (fun u : ℝ => φ u * NormedSpace.exp (u • (-A))) 0 s := by
    intro s
    have h := (hA s).mul (hE s)
    have e : (φ s).comp A * NormedSpace.exp (s • (-A)) + φ s * ((-A) * NormedSpace.exp (s • (-A))) = 0 := by
      show φ s * A * _ + _ = 0
      noncomm_ring
    rwa [e] at h
  have hconst := is_const_of_deriv_eq_zero (𝕜 := ℝ) (fun s => (hψ s).differentiableAt) (fun s => (hψ s).deriv) t 0
  simp only [zero_smul, NormedSpace.exp_zero, h0, mul_one] at hconst
  have hinv : NormedSpace.exp (t • (-A)) * NormedSpace.exp (t • A) = 1 := by
    rw [← NormedSpace.exp_add_of_commute, smul_neg, neg_add_cancel, NormedSpace.exp_zero]
    exact (((Commute.refl A).neg_left).smul_left _).smul_right _
  calc φ t = φ t * (NormedSpace.exp (t • (-A)) * NormedSpace.exp (t • A)) := by rw [hinv, mul_one]
    _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hconst, one_mul]

end Rep

end GroupGeneratedByExp

theorem trotter_product_formula : Qr.Trotter := by
  intro 𝔸 _ _ _ X Y
  exact GroupGeneratedByExp.trotter X Y

theorem trotter_product_matrices : Qr.TrotterMx := by
  intro N X Y
  exact GroupGeneratedByExp.trotterMx N X Y

theorem representation_exp : Qr.PiExp := by
  intro W _ _ _ k r z π hπ X hX t
  have hcont : Continuous fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) := by
    have h1 := Qx8.lcurve_cont X (1 : Mx k r)
    simp only [Matrix.mul_one] at h1
    exact hπ.2.comp_continuous h1 (QrD.exp_uw hX)
  have h0 : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) 0 = 1 := by
    simp [NormedSpace.exp_zero, hπ.1.1]
  obtain ⟨A, hA⟩ := one_parameter_differentiable W (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) h0
    (fun s t => by
      show π (NormedSpace.exp (((s + t : ℝ) : ℂ) • X)) = _
      rw [B5.exp_add', hπ.1.2 _ (QrD.exp_uw hX s) _ (QrD.exp_uw hX t)]) hcont
  have hAd : QrD.dOp π X = A := by
    have h := (QrD.dOp_hasDeriv hπ.1 hπ.2 hX).unique (hA 0)
    have h0' : π (NormedSpace.exp (((0 : ℝ) : ℂ) • X)) = 1 := h0
    rw [h, h0']
    exact ContinuousLinearMap.id_comp A
  have h := GroupGeneratedByExp.group_eq_exp _ A h0 hA t
  rw [hAd]
  exact h

end Formalism.FourierDecayAlt.P
end
end

section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem radialDecompositionSpectral_of_branching : Branching → RadialDecompositionSpectral := fun hB =>
  q_radial_decomposition_of_pieces second_contraction_adapted contractions_covariant capelli_two_by_two
    right_type_action hB qnTPres

end Formalism.FourierDecayAlt.P
end
