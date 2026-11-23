module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle091
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle092
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle093
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle094
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

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_node_bounds_le_h0 : SzRow (fun C D L => (12 * L.sc.b / lStar L + 2 * D.R.t + 8 ≤ h0 L ∧ (D.R.k : ℝ) * D.R.t * L.sc.L ≤ h0 L ∧ C.P.Ch0r * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L ≤ h0 L ∧ ((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ C.P.CCount ≤ h0 L ∧ 4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6 ≤ h0 L ∧ C.P.Ch0k * D.R.k * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) ≤ h0 L ∧ 2 * (Mrt D : ℝ) ^ 3 + D.R.t + 3 ≤ h0 L ∧ 120 * (D.R.r : ℝ) * (qSig D : ℝ) ^ ((3 : ℝ) / 2) ≤ h0 L ∧ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ h0 L ∧ 16 * (qSig D : ℝ) * D.R.N D.R.m ≤ h0 L)) := by
  first | exact @GlobalTheory.EX.szRow_nodeGap | exact GlobalTheory.EX.szRow_nodeGap | (intros; apply GlobalTheory.EX.szRow_nodeGap <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_sizeDel : SzRow (fun _ _ L => SizeDel L) := by
  first | exact @GlobalTheory.EX.szRow_sizeDel | exact GlobalTheory.EX.szRow_sizeDel | (intros; apply GlobalTheory.EX.szRow_sizeDel <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_PP_pow_mul_dim_pow_div_le_TOv : SzRow (fun C D L => ((C.T.CP * zBase L ^ C.T.eP) ^ 4 * ((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ C.T.Cp / ((D.R.m : ℝ) * L.de2) ≤ ((TOv L.sc : ℕ) : ℝ)) ∧ (((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) * D.R.k / D.R.m ≤ ((TOv L.sc : ℕ) : ℝ))) := by
  first | exact @GlobalTheory.EX.szRow_TO_lower | exact GlobalTheory.EX.szRow_TO_lower | (intros; apply GlobalTheory.EX.szRow_TO_lower <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_del_ge_cloudUnit_and_count_bounds : SzRow (fun C D L => ((D.R.k : ℝ) ^ C.P.CDel * (C.P.CDel * D.R.m) ^ 3 / D.div.etaF ^ C.P.CDel ≤ (D.s.Del : ℝ) ∧ C.P.CDel * D.R.m * D.R.N D.R.m ≤ (D.s.Del : ℝ) ∧ (D.R.k : ℝ) ^ C.P.CDel * (C.P.CDel * (D.R.m : ℝ) ^ 4 * L.sc.L) ^ 4 ≤ (D.s.Del : ℝ) ∧ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ)) ∧ (((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ C.P.CCount ≤ (D.s.Del : ℝ))) := by
  first | exact @GlobalTheory.EX.szRow_cloudUnit_lower | exact GlobalTheory.EX.szRow_cloudUnit_lower | (intros; apply GlobalTheory.EX.szRow_cloudUnit_lower <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_etaSz_le_b_div_and_log_etaSz_le_and_t_le : SzRow (fun C D L => (L.etaSz ≤ L.sc.b / ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3)) ∧ (Real.log L.etaSz ≤ L.sc.x ^ (L.sc.eps / 4)) ∧ ((D.R.t : ℝ) ≤ L.etaSz) ∧ ((D.R.t : ℝ) * L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x) ∧ ((D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n)) := by
  first | exact @GlobalTheory.EX.szRow_eta_bounds | exact GlobalTheory.EX.szRow_eta_bounds | (intros; apply GlobalTheory.EX.szRow_eta_bounds <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_t_add_cube_le_h0_and_f_mul_N_pow_le_h0 : SzRow (fun C D L => ((D.R.t : ℝ) + 2 * ((D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1)) ^ 3 + 1 ≤ h0 L) ∧ ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ C.P.Ch0N ≤ h0 L)) := by
  first | exact @GlobalTheory.EX.szRow_gap_fun_fN | exact GlobalTheory.EX.szRow_gap_fun_fN | (intros; apply GlobalTheory.EX.szRow_gap_fun_fN <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_PP_and_dim_and_TOv_le_x_rpow_Ct : SzRow (fun C D L => ((C.T.CP * zBase L ^ C.T.eP) ≤ L.sc.x ^ L.Ct) ∧ (((D.R.f * D.R.r.choose 2 : ℕ) : ℝ) ≤ L.sc.x ^ L.Ct) ∧ (((TOv L.sc : ℕ) : ℝ) ≤ L.sc.x ^ L.Ct)) := by
  first | exact @GlobalTheory.EX.szRow_pp_dim_to_le_rpow | exact GlobalTheory.EX.szRow_pp_dim_to_le_rpow | (intros; apply GlobalTheory.EX.szRow_pp_dim_to_le_rpow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_sizeLstar : SzRow (fun _ _ L => SizeLstar L) := szRow_lStar

end GlobalTheory.EX
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_m_mul_Sc_add_etaSz_le_w_mul_L_and_bounds : SzRow (fun C D L => ((D.R.m : ℝ) * (L.Sc + L.etaSz) ≤ L.sc.w'' D.R.n * L.sc.L) ∧ ((D.R.N D.R.m : ℝ) * L.etaSz ≤ L.de2 * D.R.m * L.sc.w'' D.R.n) ∧ (L.etaSz ^ 2 * D.R.r * L.sc.L ≤ L.de2 * D.R.m * L.sc.w'' D.R.n ^ 2) ∧ ((D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n)) := by
  first | exact @GlobalTheory.EX.szRow_eta_le_w | exact GlobalTheory.EX.szRow_eta_le_w | (intros; apply GlobalTheory.EX.szRow_eta_le_w <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_b_add_Sc_add_etaSz_add_div_lt_lStar : SzRow (fun C D L => (L.sc.b' + L.Sc + L.etaSz + L.sc.b / lStar L < lStar L) ∧ (2 * L.etaSz + D.R.t + 8 * L.sc.b / lStar L + 7 < lStar L)) := by
  first | exact @GlobalTheory.EX.szRow_lStar | exact GlobalTheory.EX.szRow_lStar | (intros; apply GlobalTheory.EX.szRow_lStar <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_sizeKRel : SzRow (fun _ _ L => SizeKRel L) := by
  first | exact @GlobalTheory.EX.szRow_sizeKRel | exact GlobalTheory.EX.szRow_sizeKRel | (intros; apply GlobalTheory.EX.szRow_sizeKRel <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.sizes_host_degree_and_log_q_and_conductor_bounds : SzRow (fun C D L => (L.sc.x ^ (2 * L.Ct + 5) < (D.host.q : ℝ) ∧ L.sc.x ^ (2 * L.Ct + 5) < (D.host.d : ℝ)) ∧ (L.sc.x ^ (L.sc.ez / 6) ≤ Real.log D.host.q) ∧ (|L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps) ∧ ((condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 ≤ L.sc.b ^ ((1 : ℝ) / 2)) ∧ (Real.log D.host.pde ≤ L.sc.L ∧ Real.log D.host.pde' ≤ L.sc.L)) := by
  first | exact @GlobalTheory.EX.szRow_primes_conductor | exact GlobalTheory.EX.szRow_primes_conductor | (intros; apply GlobalTheory.EX.szRow_primes_conductor <;> assumption)
end
