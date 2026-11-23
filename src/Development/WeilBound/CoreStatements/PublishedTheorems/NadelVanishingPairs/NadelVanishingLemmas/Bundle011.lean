module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle999
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.relative_snc_same_divisor : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (L' : Fin s → LB X) (σ' : ∀ i, (L' i).Sec), RelSnc f d L σ → (∀ i, (L' i).IsLB) → (∀ i, SameDiv (σ i) (σ' i)) → RelSnc f d L' σ' := by
  first | exact @_root_.GlobalTheory.LogPair.relSnc_of_sameDiv | exact _root_.GlobalTheory.LogPair.relSnc_of_sameDiv | (intros; apply _root_.GlobalTheory.LogPair.relSnc_of_sameDiv <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.etale_coordinates_stalk_flat : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (g : Y ⟶ Sp R) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ (y : Y) (hy : y ∈ U), ((Y.presheaf.germ U y hy).hom.comp (cstOn g U)).Flat := by
  first | exact @_root_.GlobalTheory.LogPair.flat_germ_comp_cstOn_of_isEtCoord | exact _root_.GlobalTheory.LogPair.flat_germ_comp_cstOn_of_isEtCoord | (intros; apply _root_.GlobalTheory.LogPair.flat_germ_comp_cstOn_of_isEtCoord <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.snc_chart_equations_differ_unit : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (g : Y ⟶ Sp R) {n s : ℕ} (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec), (∀ i, (L i).IsLB) → ∀ (C C' : SncChart g n L σ) (y : Y) (hy : y ∈ C.U) (hy' : y ∈ C'.U) (c : Fin s), ∃ v : (Y.presheaf.stalk y)ˣ, (Y.presheaf.germ C.U y hy).hom ((C.e c).elim 1 C.t) = v * (Y.presheaf.germ C'.U y hy').hom ((C'.e c).elim 1 C'.t) := by
  first | exact @_root_.GlobalTheory.LogPair.sncChart_germ_eqn_unit | exact _root_.GlobalTheory.LogPair.sncChart_germ_eqn_unit | (intros; apply _root_.GlobalTheory.LogPair.sncChart_germ_eqn_unit <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.finrank_kaehler_affine_chart : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Smooth f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (U : X.Opens) (c : ∀ i, (L i).ι) (hc : ∀ i, U ≤ (L i).U (c i)) (x : X) (K : Type) [Field K] [Algebra Γ(X, U) K], IsAffineOpen U → x ∈ U → (∀ a : Γ(X, U), algebraMap Γ(X, U) K a ≠ 0 ↔ x ∈ X.basicOpen a) → (letI : Algebra R Γ(X, U) := (cstOn f U).toAlgebra; Module.finrank K (K ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]) = d ∧ LinearIndependent K (fun i : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0} => (1 : K) ⊗ₜ[Γ(X, U)] KaehlerDifferential.D R Γ(X, U) (resG X (hc i) ((σ i).f (c i))))) → ∃ C : SncChart f d L σ, x ∈ C.U := by
  first | exact @_root_.GlobalTheory.LogPair.ChartPt.exists_chart | exact _root_.GlobalTheory.LogPair.ChartPt.exists_chart | (intros; apply _root_.GlobalTheory.LogPair.ChartPt.exists_chart <;> assumption)
end
