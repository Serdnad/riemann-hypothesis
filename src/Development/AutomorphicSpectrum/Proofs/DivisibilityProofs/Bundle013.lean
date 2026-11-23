module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle008
public import Development.WeilBound.CoreStatements.IdealCycleValues.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle007
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.uniformizer_divisor_cycle_number : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (u : Oˣ) (e : ℕ) (σ : Type) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum (divCycle P (C ((u : O) * ϖ ^ e))) cls H Q = (e : ℝ) * genNum (FractionRing O) (genFib P) cls H Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const | exact GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

theorem _root_.GlobalTheory.T.local_number_permutation_invariant : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (r : ℕ) (e : Equiv.Perm (Fin r)) (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)), (∀ (a : O) (x : Fin r → K → ℤ), laNum P a (x ∘ e) k Q = laNum P a x k Q) ∧ ∀ T : LocPair ι O (Fin r), (T.comp e).ck P k Q = T.ck P k Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.RootPerm.root_perm | exact GlobalTheory.CompanionTheory.Ar.Num.RootPerm.root_perm | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.RootPerm.root_perm <;> assumption)
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem cycNum_linear : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ H H' : MvPolynomial σ ℝ, cycNum Z cls (H + H') Q = cycNum Z cls H Q + cycNum Z cls H' Q) ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), cycNum Z cls (C c * H) Q = c * cycNum Z cls H Q) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), cycNum Z cls (∑ a ∈ s, H a) Q = ∑ a ∈ s, cycNum Z cls (H a) Q) ∧ ∀ (μ : σ →₀ ℕ) (c : ℝ), cycNum Z cls (monomial μ c) Q = c * (cycList Z (classList cls μ ++ Q) : ℝ) :=
  @BaseChangeColon.cycNum_linear_in_polynomial

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem numbers_rename : (∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (Z : Ideal (MRing ι O) → ℤ) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), cycNum Z cls (rename e H) Q = cycNum Z (cls ∘ e) H Q) ∧ (∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ σ' : Type) (e : σ → σ') (V : Ideal (MRing ι F)) (cls : σ' → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (rename e H) Q = genNum F V (cls ∘ e) H Q) :=
  BaseChangeColon.cycNum_rename_variables

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem genNum_linear : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ H H' : MvPolynomial σ ℝ, genNum F V cls (H + H') Q = genNum F V cls H Q + genNum F V cls H' Q) ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), genNum F V cls (C c * H) Q = c * genNum F V cls H Q) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), genNum F V cls (∑ a ∈ s, H a) Q = ∑ a ∈ s, genNum F V cls (H a) Q) ∧ ∀ (μ : σ →₀ ℕ) (c : ℝ), genNum F V cls (monomial μ c) Q = c * (intNumL F V (classList cls μ ++ Q) : ℝ) := by
  exact @BaseChangeColon.genNum_linear_in_polynomial

end GlobalTheory.CompanionTheory.Ar.Num
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.arith_intersection_constant_metric : ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (c : ℝ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → II K ι P (e + 1) (Fin.snoc L (HermLine.ofWeight (fun _ => c) (fun _ _ _ => rfl))) = -c * ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.intersection_snoc_constWeight | exact GlobalTheory.CompanionTheory.Ar.Top.intersection_snoc_constWeight | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.intersection_snoc_constWeight <;> assumption)
end
