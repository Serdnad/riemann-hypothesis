module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor

@[expose] public section

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

abbrev FDSec (X : Comp → Data E r) : Type := ∀ c, Frame (X c).Ψ r → ℂ

abbrev FPt (X : Comp → Data E r) : Type := Σ c, ((X c).dom : Set (Frame (X c).Ψ r))

def IsHolCusp (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : Prop :=
  ∀ c, P c ∈ (X c).SS (la c)

def supE (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : ENNReal :=
  ⨆ p : FPt X, ENNReal.ofReal ((X p.1).pnorm (la p.1) (P p.1) p.2)

def supN (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) : ℝ := (supE X la P).toReal

theorem pnorm_fac_nonneg (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) :
    0 ≤ ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _

theorem pnorm_smul (X : Data E r) (la : Wt X.Ψ r) (a : ℂ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la (a • P) x = ‖a‖ * X.pnorm la P x := by
  simp only [Data.pnorm, Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

def holSub (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) : Submodule ℂ (FDSec X) :=
  Submodule.span ℂ {P | IsHolCusp X la P}

theorem holCusp_mem_holSub (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) {P : FDSec X}
    (h : IsHolCusp X la P) : P ∈ holSub X la :=
  Submodule.subset_span h

end Formalism.L2.PjFree
end
end

section

noncomputable section

namespace Formalism.L2.Pj.I2FramePointLemmas

open ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.PullbackSections NumberField
open scoped ContDiff

section Deriv

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end Deriv

section Pi

variable {E : Type} [Field E] [NumberField E]

end Pi

section Log

variable {E : Type} [Field E] [NumberField E]

theorem dstar_pos (X : PT E) {dg : ℕ} (P : Par X dg) : 0 < dstar (E := E) P.m := by
  unfold dstar
  have h1 := P.hfr
  have h2 := P.hm1
  have hf : 0 < PT.f E := by
    rcases Nat.eq_zero_or_pos (PT.f E) with h | h
    · rw [h] at h1; simp at h1
    · exact h
  exact Nat.mul_pos (Nat.mul_pos two_pos hf) h2

theorem jbound_pos (X : PT E) {dg : ℕ} (P : Par X dg) (n : ℕ) : 0 < P.Jbound n := by
  have hd0 : (0 : ℝ) < (dstar (E := E) P.m : ℝ) := by exact_mod_cast dstar_pos X P
  have hd : (0 : ℝ) < 2 * (dstar (E := E) P.m : ℝ) := by linarith
  have hB := Real.rpow_pos_of_pos hd ((dstar (E := E) P.m : ℝ) / 2)
  have h6 : (0 : ℝ) < 6 * (2 * (dstar (E := E) P.m : ℝ)) ^ ((dstar (E := E) P.m : ℝ) / 2) :=
    mul_pos (by norm_num) hB
  unfold Par.Jbound
  exact mul_pos (mul_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos (inv_pos.2 h6) _))
    (pow_pos (by norm_num) _)) (Real.exp_pos _)

end Log

end Formalism.L2.Pj.I2FramePointLemmas
end
end
