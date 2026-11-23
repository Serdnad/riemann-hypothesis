module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.CurveHyp
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.IsTransSys
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Series
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle082
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace Two

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem fExp_zero : Formalism.L2.Th1.B.fExp (0 : PowerSeries K) = 1 := by
  have h := Formalism.L2.Th1.B.fExp_add (K := K) (ι := Unit) (f := 0) (g := 0) (map_zero _) (map_zero _)
  rw [add_zero] at h
  have hc : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.fExp (0 : MvPowerSeries Unit K)) = 1 :=
    Formalism.L2.Th1.B.constantCoeff_fExp (map_zero _)
  have hne : Formalism.L2.Th1.B.fExp (0 : MvPowerSeries Unit K) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hc; exact zero_ne_one hc
  exact (mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm))

theorem oneUnit_fExp_neg {f : PowerSeries K} (h : Formalism.InvariantFactorPaths.G7.Simeq (ι := Unit) f 0) :
    OneUnit (Formalism.L2.Th1.B.fExp (-f)) := by
  obtain ⟨h0, hI⟩ := h
  rw [sub_zero] at h0 hI
  have h0n : MvPowerSeries.constantCoeff (-f : MvPowerSeries Unit K) = 0 := by
    rw [map_neg, h0, neg_zero]
  have hf : OneUnit (Formalism.L2.Th1.B.fExp f) :=
    ⟨Formalism.L2.Th1.B.constantCoeff_fExp h0, (Ser.intS_iff_integral _).2 hI⟩
  refine Ser.oneUnit_of_mul_eq_one hf ?_
  rw [← Formalism.L2.Th1.B.fExp_add h0 h0n, add_neg_cancel]
  exact fExp_zero

end Two

end Formalism.L2.Th1.E
end
end

section

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace Shape

section Alg

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (xP yP : R)

end Alg

section Pts

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K)

theorem px_neg (Q : W.toAffine.Point) : px W (-Q) = px W Q := by
  cases Q <;> rfl

end Pts

section Nrm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

end Nrm

end Shape

open Shape

theorem XTShape_holds : XTShape := UpperTheory.Reformulated.B.SeriesSubgroup.XTShape_holds

theorem FacShape_of (hR : IntRules) (hA : UnitAtRules) (hK : UnitKap) (hP : UnitPsi2)
    (hD : UnitDiff) (hX : XTShape) : FacShape := by
  intro K _ _ _ W hW P Q hP0 hQ0 hPx hPy hQx hQy hs hd
  obtain ⟨hI, hc0, hc1, hc2⟩ := hX K W hW P hP0 hPx hPy
  obtain ⟨rC, -, rAdd, rNeg, -⟩ := hR K
  obtain ⟨-, -, rU, -⟩ := hA K
  have hf : IntS (C (px W Q) - xT W P) := by
    rw [sub_eq_add_neg]; exact rAdd _ _ (rC _ hQx) (rNeg _ hI)
  have e0 : coeff 0 (C (px W Q) - xT W P) = px W Q - px W P := by
    rw [map_sub, hc0, coeff_zero_C]
  have e1 : coeff 1 (C (px W Q) - xT W P) = -psi2 W P := by
    rw [map_sub, hc1, coeff_C]; simp
  have hxeq : (P + Q = 0 ∨ P - Q = 0) → px W Q = px W P := by
    rintro (h | h)
    · rw [eq_neg_of_add_eq_zero_left h, px_neg]
    · rw [sub_eq_zero.mp h]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · refine rU 0 _ hf (fun i hi => absurd hi (Nat.not_lt_zero i)) ?_
    rw [e0, norm_sub_rev]
    exact hD K W hW P Q hP0 hQ0 h1 h2 hPx hPy hQx hQy (hs h1) (hd h2)
  · refine rU 1 _ hf (fun i hi => ?_) ?_
    · obtain rfl : i = 0 := by omega
      rw [e0, hxeq h1, sub_self]
    · rw [e1, norm_neg]
      rcases h1 with h | h
      · have hPQ : P = -Q := eq_neg_of_add_eq_zero_left h
        have hPP : P + P = P - Q := by rw [hPQ, sub_eq_add_neg]
        have hne : P + P ≠ 0 := by
          rw [hPQ, ← neg_add]; exact neg_ne_zero.mpr h2
        refine hP K W hW P hP0 hne hPx hPy ?_
        rw [hPP]; exact hd (hPP ▸ hne)
      · have hPQ : P = Q := sub_eq_zero.mp h
        have hne : P + Q ≠ 0 := by rw [hPQ]; exact h2
        have hne' : P + P ≠ 0 := by rw [hPQ]; exact h2
        refine hP K W hW P hP0 hne' hPx hPy ?_
        have := hs hne
        rwa [← hPQ] at this
  · have hPQ : P = Q := sub_eq_zero.mp h1
    obtain ⟨k0, k1⟩ := hK K W hW P hP0 (by rw [hPQ]; exact h2) hPx hPy
    refine rU 2 _ hf (fun i hi => ?_) ?_
    · have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl
      · rw [e0, hPQ, sub_self]
      · rw [e1, k0, neg_zero]
    · rw [map_sub, hc2 k0, coeff_C]
      simpa using k1

end Formalism.L2.Th1.E
end
end
