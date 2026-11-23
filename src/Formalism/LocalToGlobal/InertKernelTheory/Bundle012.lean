module

public import Formalism.LocalToGlobal.InertKernelTheory.Bundle011
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRep
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalToGlobal.InertKernelTheory.FirstKernelGeneratorOfOrthogonal
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle001
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.IsHypPair

@[expose] public section

section

noncomputable section

open scoped Matrix

namespace Formalism.L2.KerInert.RepFrame

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.L2.G.Pend (Frm)
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)

def TwInt : Prop :=
  ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)) (w : X.G.P.W v), ‖twE X E v s (algebraMap (X.G.P.W v) (X.G.P.Qq v) w)‖ ≤ 1

variable (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

end Formalism.L2.KerInert.RepFrame
end
end

section

noncomputable section

namespace Formalism.L2.KerInert.Rep

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def CurveDict : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ) (l : ℕ) [Fact l.Prime]
    (g : Formalism.MainNotions.GL3Theta.G1 l) (hLT : Formalism.L2.G.Pend.LTIso g),
    Formalism.MainNotions.GL3Theta.At D cc δ g → 5 ≤ l → Formalism.MainNotions.GL3Theta.InertK D l → Formalism.MainNotions.GL3Theta.ModelOverW g.lam g.abelian₂ g.C →
    ∃ g2 g3 ε s2 : MaximalUnramifiedExtension l, (g2 : ℂ_[l]) = Formalism.L2.Th1.A.g₂ g.W ∧ (g3 : ℂ_[l]) = Formalism.L2.Th1.A.g₃ g.W ∧
      (ε : ℂ_[l]) = (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹ ∧
      PowerSeries.rescale ((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) (Formalism.MainNotions.TaylorLogMetric.sgSer g.lam g.abelian₂) =
        PowerSeries.C ((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) * Formalism.L2.Th1.B.sgW g.W (s2 : ℂ_[l]) ∧
      ‖((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹‖ = 1 ∧
      CurveAt l (Formalism.L2.G.Pend.beLT hLT) g2 g3 ε s2 ∧
      ∀ D' : Formalism.BasicNotions.D7, DictInt D' g.lam g.abelian₂
        (((g.C.u⁻¹ : ℂ_[l]ˣ) : ℂ_[l]) * (Formalism.L2.KerInert.BeCob.eLT hLT)⁻¹) g2 g3 s2 ε

end Formalism.L2.KerInert.Rep
end
end
