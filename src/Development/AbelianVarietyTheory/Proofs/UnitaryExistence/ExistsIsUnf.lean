module

import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAnFibAllPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Formalism.LocalToGlobal.ProjectiveLattices.IntegrableOnIntegrand
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameUniformisationPrescribedSpace
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.IsUnfEx

theorem exists_xi {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    ∃ ξ₀ : E, cc ξ₀ = -ξ₀ ∧ ξ₀ ≠ 0 ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ₀).im < 0 := by
  first | exact _root_.GlobalTheory.SpanInhab.exists_imag_neg | exact @_root_.GlobalTheory.SpanInhab.exists_imag_neg | apply _root_.GlobalTheory.SpanInhab.exists_imag_neg <;> assumption

theorem exists_isUnf : N1c → GlobalTheory.Published.HasseNormSt → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), 1 ≤ Dw.p + Dw.q → GoodEmb c σ → ∃ U : Unf Xo c σ (Dw.p + Dw.q), IsUnf U := by
  intro h1 h2 h3 h4 E _ _ _ H Dw l Xo c σ hpq hσ
  obtain ⟨ξ₀, hcc, hne, him⟩ := exists_xi H
  have hcc' : cc (-ξ₀) = -(-ξ₀) := by
    unfold cc at hcc ⊢
    rw [map_neg, hcc]
  obtain ⟨Gm, φ, hφ⟩ :=
    GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ₀) hcc' (neg_ne_zero.2 hne) (Dw.p + Dw.q) rfl
  obtain ⟨U, hU, -⟩ :=
    _root_.GlobalTheory.FrameUnif.exists_unf_of_space h1 h2 h3 h4 E H Dw l Xo c σ (Dw.p + Dw.q) ξ₀ Gm φ hpq hσ hcc him hφ
  exact ⟨U, hU⟩

end GlobalTheory.IsUnfEx
