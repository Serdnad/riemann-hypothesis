module

public import Formalism.SharpRestriction.AdmissibleParameterJoins.SumLogPrimeFactorsLe
public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Formalism.SharpRestriction.ParamsHeightRankConstant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

abbrev WithTw (𝒞 : FamClass) : FamClass := fun Fm => 𝒞 Fm ∧ TwGood Fm

theorem muTu_of_tuSize {eps : ℝ} (Fm : FamP eps) (h0 : 0 < eps) (h : TuSize Fm) : J.MuTu Fm := by
  obtain ⟨x0, hx0⟩ := h
  let C := max Fm.CTu 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨2 * C, x0, fun x hx i u => ?_⟩
  let s := (Fm.L x i).sc
  let R := (Fm.D x i).R
  have hL : s.L ≤ s.x := by
    exact J.scale_rpow_le_self_of_le_one s (by linarith [s.eps_lt])
  have hL0 : 0 ≤ s.L := zero_le_one.trans (Real.one_le_rpow s.one_lt_alt.le (by
    change 0 ≤ (Fm.L x i).sc.eps
    simpa only [Fm.L_eps] using h0.le))
  have hm : (R.m : ℝ) ≤ 2 * R.n := by exact_mod_cast R.m_le_f
  calc
    Real.log (((Fm.D x i).mem u).A.T : ℝ) ≤ Fm.CTu * R.m * s.L := (hx0 x hx i).2 u
    _ ≤ C * R.m * s.L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)) hL0
    _ ≤ C * (2 * R.n) * s.x :=
      mul_le_mul (mul_le_mul_of_nonneg_left hm hC) hL hL0 (by positivity)
    _ = (2 * C) * (s.x * R.n) := by ring
    _ ≤ (2 * C) * s.X'' R.n := mul_le_mul_of_nonneg_left (J.xn_le_Xpp s R) (by positivity)

end Formalism.MainNotions

end
