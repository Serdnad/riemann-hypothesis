module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle200
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle165
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle202
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjFrom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle065
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle072
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMK

def HB {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ)
    (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)) : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp) :=
  PBI.chartCoefficient b b' (fun Z' y' => ((β Z' : ℝ) : ℂ) • Φ Z' y')

def kapL {k p ρ : ℕ} (z : Fin (2 * ρ + k + 1) → ℂ) (b : U.RC k p ρ → ℝ) : ℂ :=
  ∫ x, (b x : ℂ) * psi k (p + ρ) (liftVec k p ρ z) cStd (U.Rn k p ρ x) ∂(U.muRC k p ρ)

def kapR {k p ρ : ℕ} (z' : Fin (2 * ρ + k + 1) → ℂ) (b' : U.RC k p ρ → ℝ) : ℂ :=
  ∫ x, (b' x : ℂ) * star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)) ∂(U.muRC k p ρ)

def RightAvg : Prop :=
  ∀ (k p ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq], ρ = 0 →
    ∀ (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq),
    B0.z' = liftVec k p ρ Bj.z' → (∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y)) →
    Bj.μW' Set.univ = 1 → B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl) →
    Bj.μN = D.muN k ρ → B0.μN = D.muN k (p + ρ) →
    ∀ (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)),
    Continuous b' → HasCompactSupport b' →
    ∀ Z : Fin p → Fin p → ℂ, (Matrix.of Z).det ≠ 0 →
    Integrable (fun v : G.UT p → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))) →
    ∫ v : G.UT p → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1 →
    ∀ y : Mt k ρ, (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ →
    (∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2))) →
    (∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y') →
    ∀ h ∈ UWset k ρ Bj.z, ∀ a : U.RC k p ρ,
      PBG.Kr B0 (HB b b' β Φ) (U.Rn k p ρ (-a) * U.embG k p ρ h⁻¹ * U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) =
        (((b a : ℝ) : ℂ) * kapR Bj.z' b') • (Bj.π h⁻¹).comp (Φ Z y)

def LeftAvg : Prop :=
  ∀ (k p ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq], ρ = 0 →
    ∀ (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq),
    Bj.μW Set.univ = 1 → Bj.μN = D.muN k ρ →
    ∀ (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (g : B.Mat k (p + ρ)) (b : U.RC k p ρ → ℝ) (c : ℂ)
      (A : Wq →L[ℂ] Wp), Continuous b → HasCompactSupport b →
    (∀ h ∈ UWset k ρ Bj.z, ∀ a : U.RC k p ρ,
      PBG.Kr B0 H (U.Rn k p ρ (-a) * U.embG k p ρ h⁻¹ * g) = (((b a : ℝ) : ℂ) * c) • (Bj.π h⁻¹).comp A) →
    PBQ.pbF Bj B0 rfl H g = (kapL Bj.z b * c) • A

def CoreN : Prop :=
  ∀ (k p ρ n : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (e : p + ρ = n), ρ = 0 →
    ∀ (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq),
    D.castV e (liftVec k p ρ Bj.z') = B0.z' → (∀ y : B.Mat k ρ, Bj.π' y = B0.π' (D.castM e (ιLev k p ρ y))) →
    Bj.μW Set.univ = 1 → Bj.μW' Set.univ = 1 → B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ e) →
    Bj.μN = D.muN k ρ → B0.μN = D.muN k n →
    ∀ (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp)),
    Continuous b → HasCompactSupport b → Continuous b' → HasCompactSupport b' →
    ∀ Z : Fin p → Fin p → ℂ, (Matrix.of Z).det ≠ 0 →
    Integrable (fun v : G.UT p → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))) →
    ∫ v : G.UT p → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1 →
    ∀ y : Mt k ρ, (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ →
    (∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2))) →
    (∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y') →
    PBQ.pbF Bj B0 e (D.castF e.symm (HB b b' β Φ)) (D.castM e (U.mMap k p ρ (Matrix.of Z) (Matrix.of y))) =
      (kapL Bj.z b * kapR Bj.z' b') • Φ Z y

def TopMk : Prop := CoreN → CutEX.MkTop

section assembly

theorem coreRfl (hR : RightAvg) (hL : LeftAvg) (k p ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    [FiniteDimensional ℂ Wq] (hρ : ρ = 0) (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq)
    (hz' : B0.z' = liftVec k p ρ Bj.z') (hπ' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y))
    (hW : Bj.μW Set.univ = 1) (hW' : Bj.μW' Set.univ = 1)
    (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k (p + ρ))
    (b b' : U.RC k p ρ → ℝ) (β : (Fin p → Fin p → ℂ) → ℝ) (Φ : (Fin p → Fin p → ℂ) → Mt k ρ → (Wq →L[ℂ] Wp))
    (hb : Continuous b) (hbc : HasCompactSupport b) (hb' : Continuous b') (hbc' : HasCompactSupport b')
    (Z : Fin p → Fin p → ℂ) (hZ : (Matrix.of Z).det ≠ 0)
    (hβi : Integrable (fun v : G.UT p → ℂ => β (Matrix.of.symm (Matrix.of Z * G.upper v))))
    (hβ1 : ∫ v : G.UT p → ℂ, β (Matrix.of.symm (Matrix.of Z * G.upper v)) = 1)
    (y : Mt k ρ) (hy : (Matrix.of y : B.Mat k ρ) ∈ B.GV k ρ)
    (hΦL : ∀ h1 ∈ UWset k ρ Bj.z, ∀ h2 ∈ UWset k ρ Bj.z',
      Φ Z (Matrix.of.symm (h1 * Matrix.of y * h2)) = (Bj.π h1).comp ((Φ Z y).comp (Bj.π' h2)))
    (hΦU : ∀ (u : G.UT p → ℂ) (y' : Mt k ρ), (Matrix.of y' : B.Mat k ρ) ∈ B.GV k ρ →
      Φ (Matrix.of.symm (Matrix.of Z * G.upper u)) y' =
        psi k (p + ρ) (liftVec k p ρ Bj.z') cStd (U.muP k p ρ (G.upper u)) • Φ Z y') :
    PBQ.pbF Bj B0 rfl (HB b b' β Φ) (U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) =
      (kapL Bj.z b * kapR Bj.z' b') • Φ Z y := hL k p ρ Wp Wq hρ Bj B0 hW hNj (HB b b' β Φ) (U.mMap k p ρ (Matrix.of Z) (Matrix.of y)) b
    (kapR Bj.z' b') (Φ Z y) hb hbc
    (fun h hh a => hR k p ρ Wp Wq hρ Bj B0 hz' hπ' hW' hW0' hNj hN0 b b' β Φ hb' hbc' Z hZ hβi hβ1 y hy
      hΦL hΦU h hh a)

theorem coreN_of (hR : RightAvg) (hL : LeftAvg) : CoreN := by
  intro k p ρ n Wp Wq _ _ _ _ _ _ e hρ Bj B0 hz' hπ' hW hW' hW0' hNj hN0 b b' β Φ hb hbc hb' hbc' Z hZ hβi hβ1 y hy
    hΦL hΦU
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl] at hz'
  have hπ'' : ∀ y : B.Mat k ρ, Bj.π' y = B0.π' (U.embG k p ρ y) := fun y => by
    rw [hπ' y, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]
  have hF : D.castF (rfl : p + ρ = p + ρ).symm (HB b b' β Φ) = HB b b' β Φ := funext fun x => by
    simp only [D.castF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rw [hF, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  exact coreRfl hR hL k p ρ Wp Wq hρ Bj B0 hz'.symm hπ'' hW hW' hW0' hNj hN0 b b' β Φ hb hbc hb' hbc' Z hZ hβi hβ1
    y hy hΦL hΦU

theorem mkTop_of_leaves (hR : RightAvg) (hL : LeftAvg) (hT : TopMk) : CutEX.MkTop := hT (coreN_of hR hL)

end assembly

end Formalism.FourierDecayAlt.P.CutMK
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

theorem lphi_log_deriv (m : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖iteratedDeriv (m + 1) Real.log x‖ = (m.factorial : ℝ) * (x ^ (m + 1))⁻¹ := by
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_natCast]
  congr 1
  have e : (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, zpow_neg, zpow_natCast, norm_inv, norm_pow, Real.norm_of_nonneg hx.le]

theorem lphi_deriv_bdd {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (hld : ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C)
    {a : ℝ} (ha : 0 < a) (j : ℕ) : ∃ D : ℝ, ∀ x, a < x → ‖iteratedDeriv j φ x‖ ≤ D := by
  choose C hC using hld
  set Φ : ℝ → ℝ := fun u => φ (Real.exp u) with hΦdef
  have hΦ : ContDiff ℝ ∞ Φ := hφ
  set s : Set ℝ := Set.Ioi a with hs
  have hso : IsOpen s := isOpen_Ioi
  set K : ℝ := ∑ i ∈ Finset.range (j + 1), |C i| with hK
  have hKi : ∀ i ≤ j, |C i| ≤ K := fun i hi =>
    Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  set M : ℝ := max 1 a⁻¹ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  set Dd : ℝ := (j.factorial : ℝ) * M with hDd
  refine ⟨(j.factorial : ℝ) * K * Dd ^ j, fun x hx => ?_⟩
  have hx0 : 0 < x := ha.trans hx
  have hxs : x ∈ s := hx
  have hlogc : ContDiffOn ℝ ∞ Real.log s :=
    Real.contDiffOn_log.mono fun y hy => ne_of_gt (ha.trans (show a < y from hy))
  have hFdB := norm_iteratedFDerivWithin_comp_le (n := j) (N := ∞) (g := Φ) (f := Real.log) (t := Set.univ)
    hΦ.contDiffOn hlogc (by exact_mod_cast le_top) uniqueDiffOn_univ hso.uniqueDiffOn (Set.mapsTo_univ _ _) hxs
    (C := K) (D := Dd) (fun i hi => by
      rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have := hC i x hx0
      unfold LE.ld at this
      rw [Real.norm_eq_abs]
      exact this.trans ((le_abs_self _).trans (hKi i hi)))
    (fun i hi1 hij => by
      rw [iteratedFDerivWithin_of_isOpen i hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      rw [lphi_log_deriv m hx0]
      have hxi : (x ^ (m + 1))⁻¹ ≤ M ^ (m + 1) := by
        rw [← inv_pow]
        exact pow_le_pow_left₀ (inv_nonneg.2 hx0.le)
          ((inv_anti₀ ha hx.le).trans (le_max_right _ _)) _
      have hf1 : (m.factorial : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_le (by omega)
      have hj1 : (1 : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero j)
      have hjp : (j.factorial : ℝ) ≤ (j.factorial : ℝ) ^ (m + 1) := le_self_pow₀ hj1 (by omega)
      rw [hDd, mul_pow]
      exact mul_le_mul (hf1.trans hjp) hxi (by positivity) (by positivity))
  rw [iteratedFDerivWithin_of_isOpen j hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hFdB
  have heq : (Φ ∘ Real.log) =ᶠ[nhds x] φ := by
    filter_upwards [isOpen_Ioi.mem_nhds hx0] with y hy
    simp [hΦdef, Real.exp_log (show (0 : ℝ) < y from hy)]
  rw [← heq.iteratedDeriv_eq]
  exact hFdB

theorem lphi_cut {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (hld : ∀ p, ∃ C, ∀ x, 0 < x → |LE.ld p φ x| ≤ C)
    {δ : ℝ} (hδ : 0 < δ) : ∃ (h : ℝ → ℝ) (ε' : ℝ), U.IsCutG ε' h ∧ ∀ x, δ ≤ x → h x = φ x := by
  set χ₀ : ℝ → ℝ := fun y => Real.smoothTransition (2 * y - 1) with hχ₀
  have hχ : C6.IsCut0 χ₀ := by
    refine ⟨Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const),
      ⟨1 / 2, by norm_num, fun y hy => Real.smoothTransition.zero_of_nonpos (by linarith)⟩,
      fun y hy => Real.smoothTransition.one_of_one_le (by linarith)⟩
  obtain ⟨δ₀, hδ₀, hcut, -⟩ := Formalism.FourierDecayAlt.P.JCTx6.Lev0.isCutG_div hχ hδ
  set ψ : ℝ → ℝ := fun x => χ₀ (x / δ) with hψ
  have hε : 0 < δ₀ * δ := mul_pos hδ₀ hδ
  have hψ1 : ∀ x, δ ≤ x → ψ x = 1 := fun x hx =>
    hχ.2.2 _ (by rw [le_div_iff₀ hδ]; linarith)
  have hψ0 : ∀ x, x < δ₀ * δ → ψ x = 0 := hcut.2.2
  have hφc := smoothLog_contDiffOn hφ
  refine ⟨fun x => ψ x * φ x, δ₀ * δ, ⟨?_, ?_, fun x hx => by simp [hψ0 x hx]⟩,
    fun x hx => by simp [hψ1 x hx]⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x < δ₀ * δ
    · refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      simp [hψ0 y hy]
    · have hx0 : 0 < x := lt_of_lt_of_le hε (not_lt.1 hx)
      exact hcut.1.contDiffAt.mul (hφc.contDiffAt (isOpen_Ioi.mem_nhds hx0))
  · intro q
    set a : ℝ := δ₀ * δ / 2 with ha
    have ha0 : 0 < a := by positivity
    choose cψ hcψ using hcut.2.1
    choose D hD using fun j => lphi_deriv_bdd hφ hld ha0 j
    refine ⟨∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |cψ i| * |D (q - i)|, fun x => ?_⟩
    have hS0 : 0 ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * |cψ i| * |D (q - i)| :=
      Finset.sum_nonneg fun i _ => by positivity
    by_cases hx : x < δ₀ * δ
    · have e : (fun x => ψ x * φ x) =ᶠ[nhds x] fun _ => (0 : ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
        simp [hψ0 y hy]
      rw [e.iteratedDeriv_eq]
      simp only [iteratedDeriv_const]
      split_ifs <;> simpa using hS0
    · have hxa : a < x := by linarith [not_lt.1 hx]
      set s : Set ℝ := Set.Ioi a with hs
      have hso : IsOpen s := isOpen_Ioi
      have hxs : x ∈ s := hxa
      have hφs : ContDiffOn ℝ ∞ φ s := hφc.mono fun y hy => ha0.trans (show a < y from hy)
      have hL := norm_iteratedFDerivWithin_mul_le (N := ∞) (hcut.1.contDiffOn (s := s)) hφs hso.uniqueDiffOn
        hxs (n := q) (by exact_mod_cast le_top)
      rw [iteratedFDerivWithin_of_isOpen q hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hL
      refine hL.trans (Finset.sum_le_sum fun i hi => ?_)
      rw [iteratedFDerivWithin_of_isOpen i hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        iteratedFDerivWithin_of_isOpen (q - i) hso hxs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      have h1 : ‖iteratedDeriv i ψ x‖ ≤ |cψ i| := (hcψ i x).trans (le_abs_self _)
      have h2 : ‖iteratedDeriv (q - i) φ x‖ ≤ |D (q - i)| := (hD (q - i) x hxa).trans (le_abs_self _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _) (by positivity)

theorem local_phi_transfer_holds : JALocPhi := by
  refine ⟨2, by norm_num, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v φ Bg A J hφ hld hBg hJ hFF
  refine ⟨hFF, fun δ hδ => ?_⟩
  obtain ⟨F, hF1, hF2, hF3⟩ := hJ.2 δ hδ
  obtain ⟨h, ε', hcut, hhφ⟩ := lphi_cut hφ hld hδ
  obtain ⟨hck, hcc⟩ := gcut_graded (T v).base.z (T v).base.z' h ε' hcut (A := A) hBg hF1 hF2
  refine ⟨fun g => ((h (GfP S T v g) : ℝ) : ℂ) • F g, hck, hcc, fun x hx hG => ?_⟩
  have e1 : (fun g => ((h (GfP S T v g) : ℝ) : ℂ) • F g) = D.cutF (T v).base h F 1 := by
    funext g; simp [D.cutF, GfP]
  rw [e1, Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, div_one, ← hF3 x hx hG]
  simp only [mulG]
  unfold GfP at hG
  rw [hhφ _ hG]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.JA

end
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.ER

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace CAS

variable {k r : ℕ}

def TF (a : B.Mat k r → ℂ) : Prop := ContDiff ℝ ∞ a ∧ HasCompactSupport a

theorem tsupport_rdV {ψ : B.Mat k r → ℂ} (hψ : ContDiff ℝ ∞ ψ) (X : B.Mat k r) :
    tsupport (RdV X ψ) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro g hg
  by_contra hgs
  apply hg
  have hopen : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport ψ).isOpen_compl
  have hcont : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    continuous_const.mul (Formalism.REAL.continuous_exp_real_smul X)
  have hmem : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) ⁻¹' (tsupport ψ)ᶜ ∈ 𝓝 (0 : ℝ) := by
    apply hcont.continuousAt.preimage_mem_nhds
    apply hopen.mem_nhds
    simpa using hgs
  have hev : (fun t : ℝ => ψ (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hmem] with t ht
    exact image_eq_zero_of_notMem_tsupport ht
  show deriv _ 0 = 0
  rw [hev.deriv_eq]
  simp

theorem tf_rdV {a : B.Mat k r → ℂ} (ha : TF a) (X : B.Mat k r) : TF (RdV X a) := by
  exact ⟨rdV_contDiff ha.1 X, ha.2.mono' ((subset_tsupport _).trans (tsupport_rdV ha.1 X))⟩

theorem tf_rw {a : B.Mat k r → ℂ} (ha : TF a) : ∀ w : List (B.Mat k r), TF (B.Rw w a)
  | [] => ha
  | X :: w => tf_rdV (tf_rw ha w) X

theorem level_zero_set_eq_group : Q.Glev k r 0 = B.GV k r := by
  ext g
  simp only [Q.Glev, Set.mem_setOf_eq, B.GV, Fin.val_zero, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true,
    and_true]

theorem haar0 {μ : Measure (Mt k r)} (h : B.IsHaarOn (B.GV k r) μ) : B.IsHaarOn (Q.Glev k r 0) μ := by
  rw [level_zero_set_eq_group]
  exact h

theorem lie0 {X : B.Mat k r} (hX : B.inLie k r X) : Q.inLieLev k r 0 X := by
  exact ⟨hX, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem smooth0 {a : B.Mat k r → ℂ} (ha : ContDiff ℝ ∞ a) : Q.SmoothLev k r 0 Set.univ a := by
  exact fun g₀ _ => ⟨Set.univ, a, isOpen_univ, trivial, ha.contDiffOn, fun _ _ _ => rfl⟩

theorem cpt0 {a : B.Mat k r → ℂ} (ha : HasCompactSupport a) : Q.CptOn k r 0 a := by
  exact ⟨tsupport a, ha, fun g _ hg => image_eq_zero_of_notMem_tsupport hg⟩

theorem word_adj_scalar {μ : Measure (Mt k r)} (h : B.IsHaarOn (B.GV k r) μ) :
    ∀ (w : List (B.Mat k r)), (∀ X ∈ w, B.inLie k r X) → ∀ {a b : B.Mat k r → ℂ}, TF a → TF b →
      (∫ x : Mt k r, B.Rw w a (Matrix.of x) * star (b (Matrix.of x)) ∂μ) =
        (-1 : ℂ) ^ w.length * ∫ x : Mt k r, a (Matrix.of x) * star (B.Rw w.reverse b (Matrix.of x)) ∂μ
  | [], _, a, b, _, _ => by simp [B.Rw]
  | X :: w, hw, a, b, ha, hb => by
    have hX : B.inLie k r X := hw X (by simp)
    have hw' : ∀ Z ∈ w, B.inLie k r Z := fun Z hZ => hw Z (by simp [hZ])
    have e1 : B.Rw (X :: w) a = RdV X (B.Rw w a) := rfl
    have e2 : B.Rw (X :: w).reverse b = B.Rw w.reverse (RdV X b) := by
      simp only [B.Rw, List.reverse_cons, List.foldr_append, List.foldr_cons, List.foldr_nil]
    have hra := tf_rw ha w
    have sk := Formalism.FourierDecayAlt.P.right_differential_skew k r 0 μ (haar0 h) X (B.Rw w a) b (lie0 hX) (smooth0 hra.1)
      (smooth0 hb.1) (cpt0 hra.2) (cpt0 hb.2)
    rw [e1, sk, word_adj_scalar h w hw' ha (tf_rdV hb X), e2, List.length_cons, pow_succ]
    ring

end CAS

open CAS in
theorem capacity_adjoint_scalar : CapAdjScalar := by
  intro k r Y μ h a b ha hac hb hbc
  have ta : TF a := ⟨ha, hac⟩
  have tb : TF b := ⟨hb, hbc⟩
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  obtain ⟨hLw, hCV⟩ := Classical.choose_spec (Formalism.FourierDecayAlt.P.capelli_word_sum k r Y)
  have hLie : ∀ cw ∈ capLw k r Y, ∀ X ∈ cw.2, B.inLie k r X := fun cw hc X hX => ((hLw cw hc).1 X hX).1

  have hintA : ∀ v : B.Mat k r → ℂ, Continuous v →
      Integrable (fun x : Mt k r => a (Matrix.of x) * star (v (Matrix.of x))) μ := by
    intro v hv
    have hc : Continuous (fun x : Mt k r => a (Matrix.of x) * star (v (Matrix.of x))) :=
      ha.continuous.mul (continuous_star.comp hv)
    have hs : HasCompactSupport (fun x : Mt k r => a (Matrix.of x) * star (v (Matrix.of x))) :=
      hac.mono fun x hx h0 => hx (by show a x * _ = 0; rw [h0, zero_mul])
    exact hc.integrable_of_hasCompactSupport hs
  have hintB : ∀ v : B.Mat k r → ℂ, Continuous v →
      Integrable (fun x : Mt k r => v (Matrix.of x) * star (b (Matrix.of x))) μ := by
    intro v hv
    have hc : Continuous (fun x : Mt k r => v (Matrix.of x) * star (b (Matrix.of x))) :=
      hv.mul (continuous_star.comp hb.continuous)
    have hs : HasCompactSupport (fun x : Mt k r => v (Matrix.of x) * star (b (Matrix.of x))) :=
      hbc.mono fun x hx h0 => hx (by show _ * star (b x) = 0; rw [h0, star_zero, mul_zero])
    exact hc.integrable_of_hasCompactSupport hs

  have hH := Formalism.FourierDecayAlt.P.hermitian_haar_invariance k r 0 0 0 μ (haar0 h) (fun _ _ => rfl) (fun _ _ => rfl) a b
    (smooth0 ha) (smooth0 hb) (cpt0 hac) (cpt0 hbc) Y 0 0
  have eT : ∀ (Y' : ℂ), Q.tL k r (E := ℂ) 0 0 0 Y' 0 0 = Q.CV k r Y' := fun _ => rfl
  have eS : star Y = conj Y := rfl
  rw [eT, eT, eS] at hH
  rw [← hH]

  have e2 : (∫ x : Mt k r, Q.CV k r Y a (Matrix.of x) * star (b (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, ((capLw k r Y).map fun cw =>
        cw.1 * (B.Rw cw.2 a (Matrix.of x) * star (b (Matrix.of x)))).sum ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [Formalism.FourierDecayAlt.P.B5.haar_ae h] with x hx
    have := hCV ℂ (B.GV k r) a (ckOn_of_contDiff ha _ _) (Matrix.of x) hx hx
    rw [this, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun cw _ => ?_)
    rw [smul_eq_mul, mul_assoc]

  have e1 : (∫ x : Mt k r, a (Matrix.of x) * star (wsAdj (capLw k r Y) b (Matrix.of x)) ∂μ) =
      ∫ x : Mt k r, ((capLw k r Y).map fun cw =>
        cw.1 * ((-1 : ℂ) ^ cw.2.length * (a (Matrix.of x) * star (B.Rw cw.2.reverse b (Matrix.of x))))).sum ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [wsAdj, Complex.star_def, map_list_sum, List.map_map, ← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun cw _ => ?_)
    simp only [Function.comp_apply, map_mul, map_pow, map_neg, map_one, Complex.conj_conj]
    ring
  rw [e1, e2,
    (Formalism.FourierDecayAlt.P.B5.integral_listSum μ _ _ fun cw _ =>
      ((hintA _ (tf_rw tb _).1.continuous).const_mul _).const_mul _).2,
    (Formalism.FourierDecayAlt.P.B5.integral_listSum μ _ _ fun cw _ => (hintB _ (tf_rw ta _).1.continuous).const_mul _).2]
  refine congrArg List.sum (List.map_congr_left fun cw hcw => ?_)
  rw [integral_const_mul, integral_const_mul, integral_const_mul,
    word_adj_scalar h cw.2 (hLie cw hcw) ta tb]

end

end Formalism.FourierDecayAlt.P.CutMP.ER
end
