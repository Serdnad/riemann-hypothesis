module

public import Formalism.SatakeDualWeyl.Bundle001
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Order.Filter.Cofinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.Bundle003
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.exists_commute_mul_cT_eq_of_integral_hermitian_polynomial : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (σ : L →+* L) (ϖ : L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (y : Matrix (Fin n) (Fin n) L) (Q₀ : (intL L)[X]), (∀ i j, y i j ∈ intL L) → cT σ y * y = 1 → y.charpoly = Q₀.map (intL L).subtype → Q₀.Separable → ∀ t : GL (Fin n) L, (∀ i j, t.val i j ∈ intL L) → (∀ i j, (t⁻¹ : GL (Fin n) L).val i j ∈ intL L) → cT σ t.val = t.val → (∃ p : (intL L)[X], t.val = aeval y (p.map (intL L).subtype)) → ∃ s : GL (Fin n) L, s.val * y = y * s.val ∧ s.val * cT σ s.val = t.val := by
  first | exact @GlobalTheory.NormEq.hermUnit_eq_norm | (intros; apply GlobalTheory.NormEq.hermUnit_eq_norm <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.adelic_class_count_product : ∀ (ι : Type) (S : Set ι) (Cl : ι → Type) [∀ w, Finite (Cl w)] (D R : Type) [Finite D] (loc : R → ∀ w, Cl w) (O : ∀ w, Cl w → ℂ) (s : D → ∀ w, Cl w → ℂ) (good : ∀ w, Cl w → Prop) (N : ℂ), (∀ᶠ w in (cofinite : Filter ι), (∃! c, good w c) ∧ ∀ c, (O w c = if good w c then 1 else 0) ∧ (good w c → ∀ d, s d w c = 1)) → (∀ w, w ∉ S → Nonempty (Cl w)) → (∀ r, ∀ᶠ w in (cofinite : Filter ι), good w (loc r w)) → (∀ r r', (∀ w ∈ S, loc r w = loc r' w) → r = r') → (∀ x : ∀ w, Cl w, (∀ᶠ w in (cofinite : Filter ι), good w (x w)) → ∑ᶠ d : D, ∏ᶠ w ∈ S, s d w (x w) = if ∃ r, ∀ w ∈ S, loc r w = x w then N else 0) → (Function.support fun r : R => ∏ᶠ w ∈ S, O w (loc r w)).Finite ∧ (∑ᶠ r : R, ∏ᶠ w ∈ S, O w (loc r w)) * N = ∑ᶠ d : D, ∏ᶠ w ∈ S, ∑ᶠ c : Cl w, s d w c * O w c := by
  first | exact @GlobalTheory.finsum_finprod_local_sums_expand | exact GlobalTheory.finsum_finprod_local_sums_expand | (intros; apply GlobalTheory.finsum_finprod_local_sums_expand <;> assumption)
end
