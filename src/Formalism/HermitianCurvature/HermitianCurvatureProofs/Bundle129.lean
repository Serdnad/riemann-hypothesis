module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormPositivity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle020
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairOperatorCommute
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
public import Formalism.HermitianCurvature.Bundle006
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftDerivativeCurves
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP

theorem thr_of_budget (k r : ℕ) (N A₀ : ℝ) (hk : 2 ≤ k) (hN : 0 ≤ N)
    (hA : 100 * ((r : ℝ) + 1) ^ 4 * (N * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀) :
    JF.TransportedAlt k r A₀ (2 * r + k + 1) := by
  unfold JF.TransportedAlt
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have hcast : ((2 * r + k + 1 : ℕ) : ℝ) = n := by rw [hn]; push_cast; ring
  rw [hcast, lt_div_iff₀ (by positivity)]
  have hn1 : (1 : ℝ) ≤ n := by rw [hn]; linarith
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
  have h4 : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ 4 := by
    have : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
    calc (r : ℝ) + 1 = ((r : ℝ) + 1) * 1 := by ring
      _ ≤ ((r : ℝ) + 1) * ((r : ℝ) + 1) ^ 3 := by gcongr
      _ = ((r : ℝ) + 1) ^ 4 := by ring
  have h3 : n ^ 2 ≤ n ^ 3 := by
    calc n ^ 2 = n ^ 2 * 1 := by ring
      _ ≤ n ^ 2 * n := by gcongr
      _ = n ^ 3 := by ring
  have hNn : 0 ≤ N * n ^ 2 := by positivity
  have hstep : 100 * ((r : ℝ) + 1) * n ^ 2 ≤ A₀ := by
    calc 100 * ((r : ℝ) + 1) * n ^ 2 ≤ 100 * ((r : ℝ) + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by
          have : ((r : ℝ) + 1) * n ^ 2 ≤ ((r : ℝ) + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by
            calc ((r : ℝ) + 1) * n ^ 2 ≤ ((r : ℝ) + 1) ^ 4 * n ^ 2 := by gcongr
              _ ≤ ((r : ℝ) + 1) ^ 4 * (N * n ^ 2 + n ^ 3) := by gcongr; linarith
          linarith
      _ ≤ A₀ := hA
  have hrn : (r : ℝ) * n ≤ ((r : ℝ) + 1) * n ^ 2 := by
    have : (r : ℝ) ≤ (r : ℝ) + 1 := by linarith
    calc (r : ℝ) * n ≤ ((r : ℝ) + 1) * n := by gcongr
      _ = ((r : ℝ) + 1) * n * 1 := by ring
      _ ≤ ((r : ℝ) + 1) * n * n := by gcongr
      _ = ((r : ℝ) + 1) * n ^ 2 := by ring
  have hpos : 0 < ((r : ℝ) + 1) * n ^ 2 := by positivity
  nlinarith

theorem bessel_eigenvalue_equation_holds : BesselEigen := by
  refine ⟨100, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Y x hx
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, hCk, hk2, hA, _⟩, _, _, _⟩ := hB
  obtain ⟨_, hv⟩ := hbuilt
  obtain ⟨_, _, _, hplace, hCC, heig⟩ := hv v
  have hThr : JF.TransportedAlt S.G.k S.G.r A₀ (2 * S.G.r + S.G.k + 1) :=
    thr_of_budget S.G.k S.G.r (S.Ntop : ℝ) A₀ hk2 (Nat.cast_nonneg _) hA
  have hT : Tz S.G.k S.G.r (T v).base.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r (T v).base.z' = S.T' := hplace.2.2.2.2.1
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := by
    refine ⟨hx.1, ?_⟩
    have h3 : S.T * S.T' < Complex.normSq x.2 := hx.2
    rw [hT, hT']; exact h3
  have hg : B.gq (T v).base x ∈ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' :=
    Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base x hq
  have hgG : B.gq (T v).base x ∈ B.GV S.G.k S.G.r := hg.1
  have hCkn : B.CkOn ((2 * S.G.r + S.G.k + 1 : ℕ) : ℕ∞) (B.GV S.G.k S.G.r) (f v) :=
    Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top (hCk v)
  rw [Formalism.FourierDecayAlt.P.casimir_under_jacquet_integral S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A₀
    (2 * S.G.r + S.G.k + 1) (f v) (Y : ℂ) le_rfl hThr (hCC _) _ hg]
  have hint : ∀ᵐ p ∂(T v).base.μSS,
      JF.xiP (T v).base p • Q.CV S.G.k S.G.r (Y : ℂ) (B.rho (T v).base p (f v)) (B.gq (T v).base x) =
        ((S.P v Y : ℝ) : ℂ) • (JF.xiP (T v).base p • B.rho (T v).base p (f v) (B.gq (T v).base x)) := by
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_inSS (T v).base] with p hp
    rw [Formalism.FourierDecayAlt.P.capelli_rho_commute S.G.k S.G.r _ _ (T v).base (Y : ℂ) (f v) p hp hCkn _ hgG]
    have hs := Formalism.FourierDecayAlt.P.B7.sgs_mem (T v).base hp hgG
    simp only [B.rho]
    rw [heig Y _ hs, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]
  rw [integral_congr_ae hint, integral_smul]
  rfl

end Formalism.FourierDecayAlt.P.CutMP
end

section

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section Lev

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem tprod_succ (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) (l : Fin r) :
    P5.tprod L Y l.val = P5.tprod L Y (l.val + 1) * Ts (site L l) Y := by
  rw [P5.tprod, dite_eq_left l.isLt]

theorem tprod_top (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) : P5.tprod L Y r = 1 := by
  rw [P5.tprod, dite_eq_right (lt_irrefl r)]

theorem QQi_step (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (l : Fin r) : QQi L st l.castSucc = fun Y => Matrix.conjTranspose (Ts (site L l) (star Y)) * QQi L st l.succ Y * Ts (site L l) Y := by
  funext Y
  simp only [QQi, Fin.coe_castSucc, Fin.val_succ]
  rw [tprod_succ L (star Y) l, tprod_succ L Y l, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem QQi_top (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π'))) :
    QQi L st (Fin.last r) = st.QQ := by
  funext Y
  simp only [QQi, Fin.val_last, tprod_top, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

def bet (μ : MeasureTheory.Measure (Mt k r)) (Φ Ψ : RadSp k r z z' π π') : ℂ := pairLev μ 0 Φ Ψ (fun _ => 1)

theorem pairAt_zero_left (μ : MeasureTheory.Measure (Mt k r)) (Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ 0 Ψ c = 0 := by
  have h0 : ∀ A : Wq →L[ℂ] Wp, B.hsInner 0 A = 0 := fun A => by
    simp only [B.hsInner, B.hsVec, ContinuousLinearMap.zero_apply]
    rw [show (fun _ : Fin (Module.finrank ℂ Wq) => (0 : Wp)) = 0 from rfl, WithLp.toLp_zero,
      inner_zero_right]
  simp [P5.pairAt, h0]

theorem pairAt_zero_right (μ : MeasureTheory.Measure (Mt k r)) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ Φ 0 c = 0 := by
  have h0 : ∀ A : Wq →L[ℂ] Wp, B.hsInner A 0 = 0 := fun A => by
    simp only [B.hsInner, B.hsVec, ContinuousLinearMap.zero_apply]
    rw [show (fun _ : Fin (Module.finrank ℂ Wq) => (0 : Wp)) = 0 from rfl, WithLp.toLp_zero,
      inner_zero_left]
  simp [P5.pairAt, h0]

variable {S : Type} [Fintype S] [DecidableEq S]

theorem form_single_left (μ : MeasureTheory.Measure (Mt k r)) (a : Ix S) (Φ : RadSp k r z z' π π')
    (y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ 0 (Pi.single a Φ) y c = pairLev μ 0 Φ (y a) c := by
  simp only [P5.form, pairLev]
  congr 1
  funext c'
  congr 1
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, pairAt_zero_left]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem form_eq_pairS (μ : MeasureTheory.Measure (Mt k r)) (K0 : Submodule ℂ (RadSp k r z z' π π'))
    (c : Fin r → ℂ) (hS : SesqOn (Submodule.pi Set.univ fun _ : Ix S => K0) (fun x y => form μ 0 x y c))
    (x y : Ix S → RadSp k r z z' π π') (hx : ∀ a, x a ∈ K0) (hy : ∀ a, y a ∈ K0) :
    form μ 0 x y c = pairS (fun Φ Ψ => pairLev μ 0 Φ Ψ c) x y := by
  classical
  have hyU : y ∈ Submodule.pi Set.univ (fun _ : Ix S => K0) := Submodule.mem_pi.mpr (fun a _ => hy a)
  have hsingle : ∀ a, Pi.single a (x a) ∈ Submodule.pi Set.univ (fun _ : Ix S => K0) := by
    intro a
    refine Submodule.mem_pi.mpr (fun b _ => ?_)
    by_cases h : b = a
    · subst h
      simpa using hx b
    · rw [Pi.single_eq_of_ne h]
      exact K0.zero_mem
  have hzero : form μ 0 0 y c = 0 := by
    have h := (hS 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) y hyU 1).1
    simp only [one_smul, add_zero, one_mul] at h
    linear_combination -h
  have key : ∀ s : Finset (Ix S), form μ 0 (∑ a ∈ s, Pi.single a (x a)) y c =
      ∑ a ∈ s, pairLev μ 0 (x a) (y a) c := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert b s hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb]
      have hmem : (∑ a ∈ s, Pi.single a (x a)) ∈ Submodule.pi Set.univ (fun _ : Ix S => K0) :=
        Submodule.sum_mem _ (fun a _ => hsingle a)
      have h := (hS _ (hsingle b) _ hmem y hyU 1).1
      dsimp only at h
      rw [one_smul, one_mul] at h
      rw [h, ih, form_single_left]
  have h2 := key Finset.univ
  rw [Finset.univ_sum_single] at h2
  rw [h2]
  rfl

end Lev

section Data

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
  (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : MeasureTheory.Measure (Mt P.k P.r))
  (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)

theorem isStart_QQi (hD : IsData P z z' π π' X μ L st l0) (i : Fin (P.r + 1)) :
    IsStart (QQi L st i) (M.qC P) := by
  have h0 : IsStart st.QQ (M.qC P) := by
    have hX := (Formalism.FourierDecayAlt.P.actual_start Wp Wq P z z' π π' hD.1 X).1
    have h := Formalism.FourierDecayAlt.P.Mx8.isStart_smul X.QQ (M.qC P) (M.sgn P l0) (Formalism.FourierDecayAlt.P.Mx8.sgn_sq P l0)
      (Formalism.FourierDecayAlt.P.Mx8.sgn_star P l0) hX
    have e : st.QQ = fun Y => M.sgn P l0 • X.QQ Y := funext hD.2.2.2.1
    rw [e]; exact h
  have key : ∀ d i : ℕ, ∀ hi : i + d = P.r, IsStart (QQi L st ⟨i, by omega⟩) (M.qC P) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have e : (⟨i, by omega⟩ : Fin (P.r + 1)) = Fin.last P.r := Fin.ext (by simp; omega)
      rw [e, QQi_top]; exact h0
    | succ d ih =>
      intro i hi
      have hlt : i < P.r := by omega
      let l : Fin P.r := ⟨i, hlt⟩
      have e : (⟨i, by omega⟩ : Fin (P.r + 1)) = l.castSucc := rfl
      rw [e, QQi_step]
      have ih' := ih (i + 1) (by omega)
      have e' : (⟨i + 1, by omega⟩ : Fin (P.r + 1)) = l.succ := rfl
      rw [e'] at ih'
      exact Formalism.FourierDecayAlt.P.Mx8.isStart_step _ _ _ (isSite_actual hD.2.2.1 l)
        (qqCommutes_actual P z z' π π' X μ L st l0 hD l) ih'
  exact key (P.r - i.val) i.val (by omega)

theorem form_single_right (μ : MeasureTheory.Measure (Mt P.k P.r)) (a : Ix S)
    (x : Ix S → RadSp P.k P.r z z' π π') (Ψ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) :
    form μ 0 x (Pi.single a Ψ) c = pairLev μ 0 (x a) Ψ c := by
  simp only [P5.form, pairLev]
  congr 1
  funext c'
  congr 1
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, pairAt_zero_right]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem herm_on {W : Type} [AddCommGroup W] [Module ℂ W] (U' : Submodule ℂ W) (f : W → W → ℂ) (hS : SesqOn U' f)
    (hN : NonnegOn U' f) (x : W) (hx : x ∈ U') (y : W) (hy : y ∈ U') : f y x = conj (f x y) := by
  have key : ∀ a : ℂ, (f (x + a • y) (x + a • y)).im = 0 := fun a =>
    (Complex.nonneg_iff.mp (hN _ (U'.add_mem hx (U'.smul_mem a hy)))).2.symm
  have hxx : (f x x).im = 0 := (Complex.nonneg_iff.mp (hN x hx)).2.symm
  have hyy : (f y y).im = 0 := (Complex.nonneg_iff.mp (hN y hy)).2.symm
  have expand : ∀ a : ℂ, f (x + a • y) (x + a • y) =
      f x x + conj a * f x y + a * (f y x + conj a * f y y) := by
    intro a
    rw [(hS x hx y hy (x + a • y) (U'.add_mem hx (U'.smul_mem a hy)) a).1,
      (hS x hx y hy x hx a).2, (hS x hx y hy y hy a).2]
  have h1 := key 1
  have hI := key Complex.I
  rw [expand] at h1 hI
  simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im, Complex.add_re, Complex.mul_re, map_one, hxx, hyy] at h1 hI
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith

end Data

end

end Formalism.FourierDecayAlt.P.PBF
end

section

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Topx1

namespace Formalism.FourierDecayAlt.P.PBI

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def GrpInt (S : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (V : Wq →L[ℂ] Wp) : Prop :=
  ∀ hB ∈ UWset k r S.z', hB *ᵥ ν' = ν' → (S.π (m₀ * hB * m₀⁻¹)).comp (V.comp (S.π' hB⁻¹)) = V

theorem gen_dOp_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) {X : B.Mat k r}
    (hX : QrD.InLieW k r S.z' X) (hXν : X *ᵥ ν' = 0) (hY : QrD.InLieW k r S.z (m₀ * X * m₀⁻¹)) :
    (QrD.dOp S.π (m₀ * X * m₀⁻¹)).comp V = V.comp (QrD.dOp S.π' X) := by
  obtain ⟨hmU, -, hiU, -, um, -, -⟩ := vecw_base_parts S hbase
  have key : ∀ t : ℝ, (S.π (NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹)))).comp V =
      V.comp (S.π' (NormedSpace.exp ((t : ℂ) • X))) := by
    intro t
    have hhB := QrD.exp_uw hX t
    have hBν := Qx8.exp_fix hXν t
    set hB := NormedSpace.exp ((t : ℂ) • X) with hhBdef
    have hconj : NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹)) = m₀ * hB * m₀⁻¹ := by
      have h := LeftDerivativeCurves.exp_swap hiU X t
      rw [Matrix.nonsing_inv_nonsing_inv _ um] at h
      calc NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹))
          = m₀ * (m₀⁻¹ * NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹))) := by
            rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ um, Matrix.one_mul]
        _ = m₀ * hB * m₀⁻¹ := by rw [h, Matrix.mul_assoc]
    have h := hV hB hhB hBν
    have hinv := WeylGroupFacts.uw_inv hhB
    have uB := WeylGroupFacts.isUnit_of_uh hhB.1
    rw [hconj]
    calc (S.π (m₀ * hB * m₀⁻¹)).comp V
        = ((S.π (m₀ * hB * m₀⁻¹)).comp (V.comp (S.π' hB⁻¹))).comp (S.π' hB) := by
          rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, ← S.π'_rep.2 _ hinv _ hhB,
            Matrix.nonsing_inv_mul _ uB, S.π'_rep.1]
          rfl
      _ = V.comp (S.π' hB) := by rw [h]
  have hd1 := QrD.dOp_hasDeriv S.π'_rep S.π'_cont hX
  have hd2 := QrD.dOp_hasDeriv S.π_rep S.π_cont hY
  let L1 : (Wq →L[ℂ] Wq) →L[ℂ] (Wq →L[ℂ] Wp) := ContinuousLinearMap.compL ℂ Wq Wq Wp V
  let L2 : (Wp →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq Wp Wp).flip V
  have h1 := (L1.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd1
  have h2 := (L2.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd2
  have hfun : ((L2.restrictScalars ℝ) ∘ fun t : ℝ => S.π (NormedSpace.exp ((t : ℂ) • (m₀ * X * m₀⁻¹)))) =
      ((L1.restrictScalars ℝ) ∘ fun t : ℝ => S.π' (NormedSpace.exp ((t : ℂ) • X))) := by
    funext t
    exact key t
  rw [hfun] at h2
  exact h2.unique h1

theorem gen_ecOp_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) {m : ℕ}
    {Bs' : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [S.z', ν'] Bs') (a b : Fin m) :
    (QrD.ecOp S.π (Q.unitB (Hpk k r) (fun a => m₀ *ᵥ Bs' a) a b)).comp V =
      V.comp (QrD.ecOp S.π' (Q.unitB (Hpk k r) Bs' a b)) := by
  obtain ⟨hmU, -, -, -, um, -, -⟩ := vecw_base_parts S hbase
  have hBz : Q.IsFrameOf k r [S.z] (fun a => m₀ *ᵥ Bs' a) :=
    vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) (vecw_frame_fwd S hbase hB)
  have hBz' : Q.IsFrameOf k r [S.z'] Bs' := vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  have hBν : Q.IsFrameOf k r [ν'] Bs' := vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  obtain ⟨e1, e2, e3⟩ := vecw_conj_eq hmU um Bs' a b
  have lY := QrD.frame_lie hBz a b
  have lX := QrD.frame_lie hBz' a b
  have lν := QrD.frame_lie hBν a b
  rw [e1, e2, e3] at lY
  unfold QrD.ecOp
  rw [e1, e2, e3, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, gen_dOp_intertwine S hbase V hV lX.1 lν.1.2 lY.1,
    gen_dOp_intertwine S hbase V hV lX.2 lν.2.2 lY.2]

theorem gen_capRep_intertwine (S : B.RealPlaceData k r Wp Wq) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) {m : ℕ}
    {Bs' : Fin m → Fin (2 * r + k + 1) → ℂ} (hB : Q.IsFrameOf k r [S.z', ν'] Bs') (w : ℂ) (v : Wq) :
    Q.capRep k r S.π (fun a => m₀ *ᵥ Bs' a) w (V v) = V (Q.capRep k r S.π' Bs' w v) := by
  have hBz : Q.IsFrameOf k r [S.z] (fun a => m₀ *ᵥ Bs' a) :=
    vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) (vecw_frame_fwd S hbase hB)
  have hBz' : Q.IsFrameOf k r [S.z'] Bs' := vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  unfold Q.capRep
  refine vecw_qmF V.toLinearMap _ _ (fun i j y => ?_) id id w v
  have lY := QrD.frame_lie hBz i j
  have lX := QrD.frame_lie hBz' i j
  simp only [ContinuousLinearMap.coe_coe]
  rw [QrD.ecRep_eq S.π_rep S.π_cont lY.1 lY.2, QrD.ecRep_eq S.π'_rep S.π'_cont lX.1 lX.2]
  have h := congrArg (fun L : Wq →L[ℂ] Wp => L y) (gen_ecOp_intertwine S hbase V hV hB i j)
  simpa using h

end gen

open Finset

theorem types_of_grpInt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (S : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (TP : Formalism.FourierDecayAlt.Top.TypeProj P S.π S.z (m₀ *ᵥ ν')) (hPl : Q.IsPlace P S.z S.z' S.π S.π')
    (hbase : D.IsBaseFrame S ν' m₀) (V : Wq →L[ℂ] Wp) (hV : GrpInt S ν' m₀ V) :
    ∑ ρ : M.Ty P, (TP.E ρ).comp V = V := by
  obtain ⟨hOK, hz, hz', -, -, hty, hty'⟩ := hPl
  obtain ⟨hmU, hmW, -, -, -, hzeq, -⟩ := vecw_base_parts S hbase
  obtain ⟨hν, hνz, hνν, -, -⟩ := id hbase
  have he : inWb P.k P.r (m₀ *ᵥ ν') := hmW ν' hν
  have hee : herm (Hpk P.k P.r) (m₀ *ᵥ ν') (m₀ *ᵥ ν') = 1 := by rw [Dx2.DF.herm_m0_mulVec_invariant m₀ hmU]; exact hνν
  have hez : herm (Hpk P.k P.r) (m₀ *ᵥ ν') S.z = 0 := by
    rw [hzeq, Qx8.herm_smul_right', Dx2.DF.herm_m0_mulVec_invariant m₀ hmU, hνz, mul_zero]
  obtain ⟨Bs₀', hB₀'⟩ := vecw_frame_exists P.k P.r hOK.k_pos S.z' ν' hz' S.T'_pos hν hνz hνν
  have hB₀ := vecw_frame_fwd S hbase hB₀'
  obtain ⟨S', hInt', -, heig⟩ := branching_proof Wq (parametersUPrimeForU P) (parameters_u_prime_for_u_ok hOK) rfl S.z' ν' S.π' hz'
    S.T'_pos hty' hν hνz hνν
  have heig' : ∀ (σ : M.Ty (parametersUPrimeForU P)) (w : ℂ), ∀ v ∈ S' σ,
      Q.capRep P.k P.r S.π' Bs₀' w v = M.xC (parametersUPrimeForU P) σ (w - ((P.k : ℂ) - 2) / 2) • v :=
    fun σ w v hv => heig Bs₀' hB₀' σ w v hv
  refine ContinuousLinearMap.ext fun f => ?_
  rw [_root_.sum_apply]
  simp only [ContinuousLinearMap.comp_apply]
  have hf : f ∈ ⨆ σ, S' σ := by rw [hInt'.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction S' (motive := fun f => ∑ ρ, TP.E ρ (V f) = V f) hf ?_ ?_ ?_
  · intro σ v hv
    refine vecw_good_of_eig hOK hz S.T_pos hty he hez hee TP hB₀ σ _ fun w => ?_
    rw [gen_capRep_intertwine S hbase V hV hB₀' w v, heig' σ w v hv, map_smul]
  · simp
  · intro a b ha hb
    simp only [map_add (f := _), Finset.sum_add_distrib, ha, hb]

end Formalism.FourierDecayAlt.P.PBI
end
end
