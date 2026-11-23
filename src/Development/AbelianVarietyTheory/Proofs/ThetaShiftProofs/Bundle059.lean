module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle003
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArchimedeanUniqueness.MetricDef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AbelianPartSectionNormSqEqThetaData
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDataDescendsPrincipalIdealSubring
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLinearLiftAdditiveHolomorphicAbelian
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle014
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle003
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.abelianPart_sectionNormSq_eq_thetaData : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (w : ℂ) (v : ℝ), Ha.T < w.im → Arch.IsThNormAt a.D₀.P a.D₀.rig th (RingHom.id ℂ) v → v = ‖Θ.κ‖ ^ 2 * (Real.sqrt (2 ^ (g - Θ.S.card) * ((((Θ.τ w).map Complex.im).submatrix (fun k : {k // k ∉ Θ.S} => k.1) (fun k : {k // k ∉ Θ.S} => k.1)).det)))⁻¹ := by
  first | exact @GlobalTheory.AbelianPartNorm.norm_eq | exact GlobalTheory.AbelianPartNorm.norm_eq | (intros; apply GlobalTheory.AbelianPartNorm.norm_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.arcData_descends_principalIdealSubring : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (R R' : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [Field R'] (f : R →+* R') (b : O →+* R) (b' : O →+* R') (a' : ArcIn Dw l β R' b') (D₀ : Out.DegPre R) (p : Out.IsPullDeg f D₀ a'.D₀) (n : ℕ), letI := H.starRing; ∀ oB : D₀.P.OAct (𝓞 E), Function.Injective f → b' = f.comp b → 0 < n → TauCan a'.D₀ n → (∀ x, (a'.oa.onB.act x).left ≫ prj p = prj p ≫ (oB.act x).left) → (∀ v, ∃ q, GlobalTheory.ArcPull.IsPullQk p q (a'.eta v)) → (∀ v, ∃ q, GlobalTheory.ArcPull.IsPullQk p q (a'.etaA v)) → ∃ (a : ArcIn Dw l β R b) (p' : Out.IsPullDeg f a.D₀ a'.D₀), a.D₀ = D₀ ∧ HEq p' p ∧ InBC f a a' p' ∧ TauCan a.D₀ n := by
  first | exact @GlobalTheory.ArcDescent.exists_arcIn_down | exact GlobalTheory.ArcDescent.exists_arcIn_down | (intros; apply GlobalTheory.ArcDescent.exists_arcIn_down <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_linearLift_additiveHolomorphic_abelian : ∀ (P P' : Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap (RingHom.id ℂ)) φ → ∀ (u : HolUnif P'.A P'.L P'.g) (g : ℕ) (T : Over (Sp ℂ)) (i : Sp ℂ ⟶ T.left), i ≫ T.hom = 𝟙 _ → ∀ G : (Fin g → ℂ) → (T ⟶ P.A), (∀ z z', G (z + z') = G z * G z') → IsHolTo Set.univ (fun z => i ≫ (G z).left) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ), (∀ z, (u.ex (F z)).left ≫ φ = i ≫ (G z).left) ∧ (∀ z, G z = 1 → F z ∈ u.Λ) ∧ ∀ (z : Fin g → ℂ) (z' : Fin P'.g → ℂ) (η' : epsR ℂ ⟶ P'.A), IsDerivAt0 (fun z => i ≫ (G z).left) z (η'.left ≫ φ) → u.IsDiff z' η' → z' = F z := by
  first | exact @GlobalTheory.AbelianLetters.exists_linear_lift_of_isGrpPullback | exact GlobalTheory.AbelianLetters.exists_linear_lift_of_isGrpPullback | (intros; apply GlobalTheory.AbelianLetters.exists_linear_lift_of_isGrpPullback <;> assumption)
end
