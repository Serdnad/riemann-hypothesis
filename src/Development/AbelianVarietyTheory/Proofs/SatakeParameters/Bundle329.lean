module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle318
public import Formalism.LocalToGlobal.HermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle317
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle319
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle012
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG


theorem _root_.GlobalTheory.T.tameLocalCharacter_det_congruent_one_eq_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok → ∀ (i n : ℕ) (P : rowSG Pr sel mu) (k : GLint X.E n P.1),
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E n) l))) →
    rhoS Ch sel mu i P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1 := by
  first | exact @GlobalTheory.TwV.AwayCpl.RhoOne.rhoS_det_one | exact GlobalTheory.TwV.AwayCpl.RhoOne.rhoS_det_one | (intros; apply GlobalTheory.TwV.AwayCpl.RhoOne.rhoS_det_one <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG


theorem _root_.GlobalTheory.T.exists_vector_prescribed_residues_in_frames : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E))) (f : SB → (Sp E n ≃ₗ[E] Sp E n)) (y0 : SB → Sp E n) (e : SB → ℕ),
    ∃ y : Sp E n, ∀ P l, IntAt P.1 ((((qOf P.1 : ℕ) : E) ^ (e P))⁻¹ * ((f P).symm y - y0 P) l) := by
  first | exact @GlobalTheory.CRTFrame.approx_frames_target | exact GlobalTheory.CRTFrame.approx_frames_target | (intros; apply GlobalTheory.CRTFrame.approx_frames_target <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.orthonormalCoords_conj_unitary_standard_form : ∀ (D : D7) {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (crd γ : GL (Fin n) D.host.E), cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E) = J → γ ∈ UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) J → cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  first | exact @GlobalTheory.unitary_conj_orthonormal | exact GlobalTheory.unitary_conj_orthonormal | (intros; apply GlobalTheory.unitary_conj_orthonormal <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

theorem _root_.GlobalTheory.T.companionHermitianLattice_fg : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), IsUnit J.det → ∀ (a : 𝓞 E) (Lb : Submodule (𝓞 E) (Fin N → E)), Lb.FG → Submodule.span E (Lb : Set (Fin N → E)) = ⊤ → (compan (sp := sp) J a Lb).FG := by
  first | exact @GlobalTheory.compan_fg | exact GlobalTheory.compan_fg | (intros; apply GlobalTheory.compan_fg <;> assumption)
end
