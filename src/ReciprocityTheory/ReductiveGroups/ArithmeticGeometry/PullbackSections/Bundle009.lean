module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle006
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
import Formalism.SharpRestriction.Divisibility.WeightAlgebra

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj

def PPSemicharSt : Prop :=
  ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U →
    ∀ (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x) (Wu : UnitAt W),
      (∀ τ' i', ‖dmin (U.X k).Gm x.1 τ' i'‖ = 1) →
      ∀ a, Wu.χl (W.Pm a) = (-1 : ℂ) ^ ((W.F.Di (W.ik k)).EF a (H.w0 • a))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

section FrRd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def IsFrRd {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) (Wu : UnitAt W) (kk : ℤ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L kk (Over.mk (U.un k x).x))) (θF : (Fin W.g → ℂ) → ℂ) : Prop :=
  ∀ j z (pt : Sp ℂ ⟶ Gx (U.un k x).x),
    pt ≫ gxFst (U.un k x).x = (W.F.ex (W.ik k) W.Pm z).left →
    pt ≫ gxSnd (U.un k x).x = 𝟙 (Sp ℂ) →
    ⊤ ≤ (W.F.ex (W.ik k) W.Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' pt ((LPow Xo.univ.t.G Xo.univ.t.PP.L kk (Over.mk (U.un k x).x)).U (fun _ => j))
      (F.f (fun _ => j)) = θF z * Wu.fr j z ^ kk

end FrRd

section BC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

end BC

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

def TorusPins {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom} (W : UnfAt U k x) (Wu : UnitAt W)
    (A : ReciprocityTheory.ChartRestriction.G.I2.TorusAt (U.X k) x.1) (L : (Fin W.g → ℂ) →ₗ[ℂ] ReciprocityTheory.ChartRestriction.G.I2.Vsp A.T.dim) : Prop :=
  (∀ a, A.φ ((W.φ k a : (U.X k).Λ) : Fin r → E) = L (star (W.Pm a))) ∧
  (∀ z z', ReciprocityTheory.ChartRestriction.G.I2.Hf (L z) (L z') = star (hermForm Wu.Hm (star z) (star z'))) ∧
  (∀ z, A.s (fun _ => L z) = star (Wu.θ (star z))) ∧
  (∀ a, ((A.T.eps (A.φ ((W.φ k a : (U.X k).Λ) : Fin r → E)) : ℤ) : ℂ) = Wu.χl (W.Pm a))

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
