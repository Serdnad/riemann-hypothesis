module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2418
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUnipotentModIdealModConjIdeal
import Formalism.LocalRingCardinality.DataHost
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
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotent_mod_ideal_of_trivial_mod_half : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (L' : Submodule (𝓞 E) (Fin r → E)) (Mb P : Ideal (𝓞 E)), Mb ≤ P →
    ∀ {A : Type} [AddCommGroup A] [Module (𝓞 E) A] (φ : A ≃ₗ[𝓞 E] (L' ⧸ (Mb • (⊤ : Submodule (𝓞 E) L'))))
      (ℓ : A ≃ₗ[𝓞 E] A) (n : ℤ),
    (∀ x : A, ((ℓ.toLinearMap - LinearMap.id : Module.End (𝓞 E) A) ^ r) x ∈ P • (⊤ : Submodule (𝓞 E) A)) →
    ∀ γ t : Matrix (Fin r) (Fin r) E, (∀ w ∈ L', Matrix.mulVec γ w ∈ L') → (∀ w ∈ L', Matrix.mulVec γ w - w ∈ Mb • L') →
    (∀ w : L', ∃ hw : Matrix.mulVec t w ∈ L',
      Submodule.Quotient.mk (p := Mb • (⊤ : Submodule (𝓞 E) L')) ⟨_, hw⟩ = φ ((ℓ ^ n) (φ.symm (Submodule.Quotient.mk w)))) →
    ∀ w ∈ L', Matrix.mulVec ((γ * t - 1) ^ r) w ∈ P • L' := by
  first | exact @GlobalTheory.UnipModHalf.unip_mod_half | exact GlobalTheory.UnipModHalf.unip_mod_half | (intros; apply GlobalTheory.UnipModHalf.unip_mod_half <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

theorem _root_.GlobalTheory.T.log_ordFrac_comap_formallyUnramified_dvr : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (V : ValuationSubring L) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap φ)], (letI := (φ.restrict (V.comap φ) V fun _ hx => hx).toAlgebra; Algebra.FormallyUnramified (V.comap φ) V ∧ Algebra.EssFiniteType (V.comap φ) V) → ∀ g : K, g ≠ 0 → WithZero.log (Ring.ordFrac V (φ g)) = WithZero.log (Ring.ordFrac (V.comap φ) g) := by
  first | exact @GlobalTheory.RestrictOrd.log_ordFrac_comap | exact GlobalTheory.RestrictOrd.log_ordFrac_comap | (intros; apply GlobalTheory.RestrictOrd.log_ordFrac_comap <;> assumption)
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitary_unipotent_mod_ideal_mod_conjIdeal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r) (β : GL (Fin r) E),
    (∀ v w, herm X.Gm (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v) (Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) w) =
      herm X.Gm v w) →
    (∀ v, v ∈ X.L' ↔ Matrix.mulVec (β : Matrix (Fin r) (Fin r) E) v ∈ X.L') →
    ∀ P : Ideal (𝓞 E), (∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈ P • X.L') →
    ∀ v ∈ X.L', Matrix.mulVec (((β : Matrix (Fin r) (Fin r) E) - 1) ^ r) v ∈
      P.map ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E ≃+* 𝓞 E) : 𝓞 E →+* 𝓞 E) • X.L' := by
  first | exact @GlobalTheory.UnipConjIdeal.pow_sub_one_mem_conj_ideal_smul | exact GlobalTheory.UnipConjIdeal.pow_sub_one_mem_conj_ideal_smul | (intros; apply GlobalTheory.UnipConjIdeal.pow_sub_one_mem_conj_ideal_smul <;> assumption)
end
