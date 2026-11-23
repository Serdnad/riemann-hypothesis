module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsDerivationNonPthPower
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.TopLogFormsCanonicalGenerator
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.exterior_derivative_is_differential : ∀ (K : Type) [Field K], IsExtD ℤ K (extD K) := by
  first | exact @_root_.GlobalTheory.LogDR.isExtD_extD | exact _root_.GlobalTheory.LogDR.isExtD_extD | (intros; apply _root_.GlobalTheory.LogDR.isExtD_extD <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.log_forms_generated_dlog : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (y : X), (∀ w ∈ locRing y, ExteriorAlgebra.ι X.functionField (dK w) ∈ forms (locRing y : Set X.functionField) (dlog '' {g | LogUnit Z y g}) 1) ∧ ∀ g, LogUnit Z y g → ExteriorAlgebra.ι X.functionField (dlog g) ∈ forms (locRing y : Set X.functionField) (dlog '' {g | LogUnit Z y g}) 1 := by
  first | exact @_root_.GlobalTheory.DI.dK_dlog_mem_forms_one | exact _root_.GlobalTheory.DI.dK_dlog_mem_forms_one | (intros; apply _root_.GlobalTheory.DI.dK_dlog_mem_forms_one <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.lattice_model_finite_quasicoherent : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V) (F : X.Modules), LatModel M F → (∀ y : X, ∃ (U : X.Opens) (m : ℕ) (v : Fin m → V), y ∈ U ∧ IsAffineOpen U ∧ LinearIndependent X.functionField v ∧ ∀ z ∈ U, ∀ w, w ∈ M z ↔ ∃ c : Fin m → X.functionField, (∀ i, RegAt z (c i)) ∧ w = ∑ i, c i • v i) → GlobalTheory.QCoh.IsFiniteQC F := by
  first | exact @_root_.GlobalTheory.LogDR.LatFinite.isFiniteQC_of_latModel | exact _root_.GlobalTheory.LogDR.LatFinite.isFiniteQC_of_latModel | (intros; apply _root_.GlobalTheory.LogDR.LatFinite.isFiniteQC_of_latModel <;> assumption)
end

section

open GlobalTheory GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.euler_contraction_chart_forms : ∀ (K : Type) [Field K] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (i : Fin n) (θ : abelian₂ K →ₗ[K] abelian₂ K), (∀ j, (x j : K) ∈ A) → IsEulerContraction x i θ → (∀ q, ∀ η ∈ chartForms A x J t (q + 1), θ η ∈ chartForms A x J t q) ∧ ∀ η ∈ chartForms A x J t 0, θ η = 0 := by
  first | exact @_root_.GlobalTheory.LogDR.chartForms_stable_euler | exact _root_.GlobalTheory.LogDR.chartForms_stable_euler | (intros; apply _root_.GlobalTheory.LogDR.chartForms_stable_euler <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.lattice_model_unique_injective : ∀ (X : Scheme.{0}) [IsIntegral X] {V V' : Type} [AddCommGroup V] [Module X.functionField V] [AddCommGroup V'] [Module X.functionField V'] (M : X → AddSubgroup V) (F F' : X.Modules) (φ : V →ₗ[X.functionField] V'), Function.Injective φ → LatModel M F → (Nonempty (LatModel (fun y => (M y).map φ.toAddMonoidHom) F)) ∧ (LatModel M F' → Nonempty (F ≅ F')) := by
  first | exact @_root_.GlobalTheory.LogDR.latModel_map_and_unique | exact _root_.GlobalTheory.LogDR.latModel_map_and_unique | (intros; apply _root_.GlobalTheory.LogDR.latModel_map_and_unique <;> assumption)
end

section

open GlobalTheory GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.chart_forms_differential_closed : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ), AlgChart A x → ∀ q, ∀ η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) q, extD K η ∈ chartForms A x J (t ^ p * ∏ j ∈ J, x j ^ r j) (q + 1) := by
  first | exact @_root_.GlobalTheory.LogDR.extD_mem_chartForms_twist | exact _root_.GlobalTheory.LogDR.extD_mem_chartForms_twist | (intros; apply _root_.GlobalTheory.LogDR.extD_mem_chartForms_twist <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.exists_lattice_model : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V] (M : X → AddSubgroup V), (∀ y (f : X.functionField) (v : V), RegAt y f → v ∈ M y → f • v ∈ M y) → ∃ F : X.Modules, Nonempty (LatModel M F) := by
  first | exact @_root_.GlobalTheory.LogDR.exists_latModel | exact _root_.GlobalTheory.LogDR.exists_latModel | (intros; apply _root_.GlobalTheory.LogDR.exists_latModel <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.fraction_field_coordinates_dlog : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsDomain A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ (L : Type) [Field L] [Algebra A L] [IsFractionRing A L] (ht : ∀ j, algebraMap A L (t j) ≠ 0), IsCoord (fun j => Units.mk0 (algebraMap A L (t j)) (ht j)) ∧ ∀ f : A, ∃ c : Fin n → A, KaehlerDifferential.D ℤ L (algebraMap A L f) = ∑ j, algebraMap A L (c j) • KaehlerDifferential.D ℤ L (algebraMap A L (t j)) := by
  first | exact @_root_.GlobalTheory.EtCoordBasis.etale_coords_basis | exact _root_.GlobalTheory.EtCoordBasis.etale_coords_basis | (intros; apply _root_.GlobalTheory.EtCoordBasis.etale_coords_basis <;> assumption)
end

section

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem dK_eq_zero_imp_pow : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (f : K),
    dK f = 0 → ∃ g : K, f = g ^ p := by
  intro K _ p _ _ f hf
  by_contra hne
  push_neg at hne
  obtain ⟨D, hD⟩ := DerivExt.exists_derivation p f hne
  have h := D.liftKaehlerDifferential_comp_D f
  have h0 : (KaehlerDifferential.D ℤ K) f = 0 := hf
  rw [h0, map_zero, hD] at h
  exact zero_ne_one h

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.LogDR GlobalTheory.LogPair

theorem _root_.GlobalTheory.T.top_log_forms_canonical_generator : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp (ZMod p)) (d : ℕ) [SmoothOfRelativeDimension d f] {C : Type} [Fintype C] (E : C → CartierDiv X) {ι : Type} (𝒜 : SncAtlas E d ι), ∃ ω₀ : abelian₂ X.functionField, ω₀ ≠ 0 ∧ ∀ (G : CartierDiv X) (y : X) (η : abelian₂ X.functionField), η ∈ logAt (suppAll E) G d y ↔ ∃ c : X.functionField, (canonical f d + ∑ c, E c + G).RegularAt y c ∧ η = c • ω₀ := by
  first | exact @_root_.GlobalTheory.LogDR.logAt_top_eq_canonical | exact _root_.GlobalTheory.LogDR.logAt_top_eq_canonical | (intros; apply _root_.GlobalTheory.LogDR.logAt_top_eq_canonical <;> assumption)
end
