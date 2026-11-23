module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.isIntegral_quotientRing_sectionTuple_locus : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∀ (l : Fin (D + 1)) (w : X.functionField), x l ≠ 0 → (∀ z ∈ NV P e 0 (x l), RegAt z w) → IsIntegral (ratR x l) w := by
  first | exact @GlobalTheory.FnInt.main | exact GlobalTheory.FnInt.main | (intros; apply GlobalTheory.FnInt.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.exists_common_denominator_rational_sections : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (N : HermLB q) (r r' : N.B.ι → Y.functionFieldˣ), IsRatSec N.B r → IsRatSec N.B r' → ∃ (A : HermLB q) (u : A.B.Sec) (t t' : (N.tens A).B.Sec) (hu : genericPoint Y ∈ nonzeroLocus u) (ht : genericPoint Y ∈ nonzeroLocus t) (ht' : genericPoint Y ∈ nonzeroLocus t'), ∀ (i : N.B.ι) (j : A.B.ι), genericPoint Y ∈ N.B.U i → genericPoint Y ∈ A.B.U j → ratOfSec t ht (i, j) = r i * ratOfSec u hu j ∧ ratOfSec t' ht' (i, j) = r' i * ratOfSec u hu j := by
  first | exact @GlobalTheory.MixHt.exists_common_denom | exact GlobalTheory.MixHt.exists_common_denom | (intros; apply GlobalTheory.MixHt.exists_common_denom <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → (∃ m : ℕ, ∀ x : X, ∃ d ≤ m, HasDim x d) ∧ (∀ (x : X) (d d' : ℕ), HasDim x d → HasDim x d' → d = d') ∧ (∀ x : X, HasDim x 0 ↔ IsClosed ({x} : Set X)) ∧ (∀ x : X, IsClosed ({x} : Set X) → Finite (X.residueField x)) ∧ (∀ (Y : Scheme.{0}) (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) (d : ℕ), HasDim (i y) d ↔ HasDim y d) ∧ ∀ (Y : Scheme.{0}) [IsIntegral Y] (d : ℕ), HasDim (genericPoint Y) d ↔ topologicalKrullDim Y = d := by
  first | exact @GlobalTheory.MixHt.hasDim_basic | exact GlobalTheory.MixHt.hasDim_basic | (intros; apply GlobalTheory.MixHt.hasDim_basic <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.mixedArch_restricted_eq_zero_of_no_complexPoints : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), (∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) → ∀ (e : ℕ) (L : Fin e → HermLB q) (M : HermLB q), (∀ (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), mixArch L M hr = 0) ∧ ∀ (t : M.B.Sec) (z : Y), resArch L M t z = 0 := by
  first | exact @GlobalTheory.MixHt.mixArch_resArch_eq_zero_of_noCxPts | exact GlobalTheory.MixHt.mixArch_resArch_eq_zero_of_noCxPts | (intros; apply GlobalTheory.MixHt.mixArch_resArch_eq_zero_of_noCxPts <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.blockDiagonalFibreCasimir_commute_sameBlock_unit : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), IsGl F → ∀ a b, s a = s b → cas s F * F a b = F a b * cas s F := by
  first | exact @GlobalTheory.HoweR.cas_mul_comm_of_block | exact GlobalTheory.HoweR.cas_mul_comm_of_block | (intros; apply GlobalTheory.HoweR.cas_mul_comm_of_block <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.isBlockUnitaryFiniteSubspace_map_intertwiner : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M') (f : M →ₗ[ℂ] M') (U : Submodule ℂ M), (∀ a b, s a = s b → ∀ x ∈ U, f (F a b x) = F' a b (f x)) → UnitOn s F U → UnitOn s F' (U.map f) := by
  first | exact @GlobalTheory.HoweR.unitOn_map | exact GlobalTheory.HoweR.unitOn_map | (intros; apply GlobalTheory.HoweR.unitOn_map <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.piTensorSpanAllFactors_sup_finite_singleton : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ U C : ∀ w, Submodule ℂ (V w), tensAll (fun w => U w ⊔ C w) ≤ tensAll U ⊔ tensAny C ∧ ((∀ w, FiniteDimensional ℂ (U w)) → FiniteDimensional ℂ (tensAll U)) ∧ ∀ v : ∀ w, V w, tensAll (fun w => Submodule.span ℂ {v w}) ≤ Submodule.span ℂ {PiTensorProduct.tprod ℂ v} := by
  first | exact @GlobalTheory.HoweR.TensSup.main | exact GlobalTheory.HoweR.TensSup.main | (intros; apply GlobalTheory.HoweR.TensSup.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.coheight_add_pointClosureDim_eq_dim : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ d : ℕ, topologicalKrullDim Y = d → ∀ (z : Y) (e : ℕ), HasDim z e → Order.coheight z + (e : ℕ∞) = d := by
  first | exact @GlobalTheory.DimCoheight.coheight_add_eq | exact GlobalTheory.DimCoheight.coheight_add_eq | (intros; apply GlobalTheory.DimCoheight.coheight_add_eq <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.blockCasimir_eigenvalue_drops_offBlock : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (α β x ω : ℂ) (y : ι → M), IsGl F → (∀ a b, qop F α β a b = 0) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ a, cas s F (y a) = ω • y a) → ∀ j, s j = false → cas s F (∑ b, F j b (y b)) = (ω - 4 * x + 2 * α + ((Finset.univ.filter fun a => s a = true).card : ℂ) - ((Finset.univ.filter fun a => s a = false).card : ℂ)) • ∑ b, F j b (y b) := by
  first | exact @GlobalTheory.HoweR.cas_drop | exact GlobalTheory.HoweR.cas_drop | (intros; apply GlobalTheory.HoweR.cas_drop <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.tprod_cyclic_modulo_spanSomeFactor : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (R S : T → ℕ) (a : ∀ w, Mat (R w) (S w) →ₗ[ℂ] Module.End ℂ (V w)) (C : ∀ w, Submodule ℂ (V w)) (v : ∀ w, V w), (∀ w, genSub (a w) {v w} ⊔ C w = ⊤) → ∀ N : Submodule ℂ (PiTensorProduct ℂ V), (∀ w, Stab (actAt w (a w)) N) → tensAny C ≤ N → PiTensorProduct.tprod ℂ v ∈ N → N = ⊤ := by
  first | exact @GlobalTheory.HoweR.tprod_cyclic_top | exact GlobalTheory.HoweR.tprod_cyclic_top | (intros; apply GlobalTheory.HoweR.tprod_cyclic_top <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.blockUnitary_diagonal_le_of_eigenvalue_bound : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (U : Submodule ℂ M) (R : ℝ), UnitOn s F U → (∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, y a ∈ U) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → x ≤ R) → ∀ a, s a = true → ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → m.re ≤ R := by
  first | exact @GlobalTheory.HoweR.re_diag_le_of_eigen_bound | exact GlobalTheory.HoweR.re_diag_le_of_eigen_bound | (intros; apply GlobalTheory.HoweR.re_diag_le_of_eigen_bound <;> assumption)
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.glActionQuadraticRelationModulo_piTensorAtFactor : ∀ (T : Type) [Fintype T] [DecidableEq T] (V : T → Type) [∀ w, AddCommGroup (V w)] [∀ w, Module ℂ (V w)], ∀ (C : ∀ w, Submodule ℂ (V w)) (w : T) (p q : ℕ) (a : Mat p q →ₗ[ℂ] Module.End ℂ (V w)) (α β α' β' : ℂ), QuadMod a α β α' β' (C w) ⊤ → QuadMod (actAt w a) α β α' β' (tensAny C) ⊤ := by
  first | exact @GlobalTheory.HoweR.quadMod_actAt | exact GlobalTheory.HoweR.quadMod_actAt | (intros; apply GlobalTheory.HoweR.quadMod_actAt <;> assumption)
end
