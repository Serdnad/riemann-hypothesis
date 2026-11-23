module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle009
public import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

@[expose] public section

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits NumberField IsDedekindDomain GlobalTheory.HTW

variable (D : D7)

def Splits (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  ∃ e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i]
      ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i)),
    ∀ g u, e ((mapM (toK D.nd i) (rO D.nd i r π) g).mulVec u) =
      ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec (e u).1,
        fun c : Fin D.R.t =>
          toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c)

section Place

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

variable {D} (L : SizeData₂ D) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

end Place

variable {D}

end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

def IntAt {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : ℂ) : Prop :=
  a ∈ Qbar ∧ ‖lamC lam a‖ ≤ 1

variable {D : D7}

theorem exp_le (D : D7) (i : ℕ) (hi : i < D.R.m) :
    D.R.f * D.R.N i * D.R.N (i + 1) ≤ D.R.f * D.R.N D.R.m * (D.R.N D.R.m + D.R.t) := by
  have h1 : D.R.N i ≤ D.R.N D.R.m := by
    unfold Ranks.N; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _
  have h2 : D.R.N (i + 1) ≤ D.R.N D.R.m + D.R.t := by
    unfold Ranks.N
    exact le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _) (Nat.le_add_right _ _)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2

end GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

end
end
