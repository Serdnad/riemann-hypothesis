module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle070
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGramDetEqIndex
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle309
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle294
public import Mathlib.RingTheory.RingHom.Flat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle300
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointWeightSpaceEqOfCharpoly
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle296
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle310
public import ReciprocityTheory.DualLattices.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle311
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
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle001
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtOrderProdSub

@[expose] public section

section

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem _root_.GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime : ∀ (V : ValuationSubring ℂ) (a b : ℕ), Nat.Coprime a b → V.valuation (a : ℂ) = 1 ∨ V.valuation (b : ℂ) = 1 := by
  first | exact @GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime | exact GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime | (intros; apply GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.norm_gram_det_eq_index : ∀ (F : Type) [Field F] [NumberField F] (V : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (n : ℕ) (b : Module.Basis (Fin n) F V) (B : LinearMap.BilinForm F V) (L : AddSubgroup V), B.IsSymm → B.Nondegenerate → (∀ i, b i ∈ L) → (∀ (a : 𝓞 F) x, x ∈ L → a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (B x y)) → |((Algebra.norm ℚ (Matrix.of fun i j => B (b i) (b j)).det : ℚ) : ℝ)| = (L.relIndex (AddSubgroup.closure {y | ∀ x ∈ L, IsIntegral ℤ (B x y)}) : ℝ) * ((Submodule.span (𝓞 F) (Set.range b)).toAddSubgroup.relIndex L : ℝ) ^ 2 := by
  first | exact @GlobalTheory.abs_norm_det_gram_eq_relIndex | exact GlobalTheory.abs_norm_det_gram_eq_relIndex | (intros; apply GlobalTheory.abs_norm_det_gram_eq_relIndex <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.finsupp_mapDomain_eq_zero_at_filtered_stage : ∀ (Λ : Type 1) [AddCommGroup Λ] (J : Type) [SmallCategory J] [IsFiltered J] (P : J ⥤ Type) (Q : Type) (ι : ∀ j, P.obj j → Q), (∀ (j k : J) (f : j ⟶ k) (x : P.obj j), ι k (P.map f x) = ι j x) → (∀ j (x y : P.obj j), ι j x = ι j y → ∃ (k : J) (f : j ⟶ k), P.map f x = P.map f y) → ∀ j (x : P.obj j →₀ Λ), Finsupp.mapDomain (ι j) x = 0 → ∃ (k : J) (f : j ⟶ k), Finsupp.mapDomain (P.map f) x = 0 := by
  first | (exact @GlobalTheory.finsupp_mapDomain_eq_zero_at_stage) | (exact GlobalTheory.finsupp_mapDomain_eq_zero_at_stage) | (intros; apply GlobalTheory.finsupp_mapDomain_eq_zero_at_stage  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.grpObj_eq_one_of_pow_eq_one_of_sqZero_trivial : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (G : Over (Sp C)) [GrpObj G] (n : ℕ), IsUnit (n : C) → ∀ (T : Over (Sp C)) (z : T ⟶ G), (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ z = 1) → z ^ n = 1 → z = 1 := by
  first | (exact @GlobalTheory.MulUnramified.eq_one_of_pow_eq_one_thick) | (exact GlobalTheory.MulUnramified.eq_one_of_pow_eq_one_thick) | (intros; apply GlobalTheory.MulUnramified.eq_one_of_pow_eq_one_thick  <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.locally_trivial_unit_cocycle_faithfully_flat : ∀ (R B C D : CommRingCat.{0}) (f : R ⟶ B) (j₁ j₂ : B ⟶ C) (d₁₂ d₂₃ d₁₃ : C ⟶ D), IsPushout f f j₁ j₂ → IsPushout j₂ j₁ d₁₂ d₂₃ → j₁ ≫ d₁₃ = j₁ ≫ d₁₂ → j₂ ≫ d₁₃ = j₂ ≫ d₂₃ → f.hom.FaithfullyFlat → ∀ c : Cˣ, d₁₃.hom (c : C) = d₁₂.hom (c : C) * d₂₃.hom (c : C) → ∀ P : Ideal R, P.IsPrime → ∃ s : R, s ∉ P ∧ ∃ x y : B, x * y = f.hom s ∧ j₂.hom x = (c : C) * j₁.hom x := by
  first | exact @GlobalTheory.UnitCocycle.exists_local | exact GlobalTheory.UnitCocycle.exists_local | (intros; apply GlobalTheory.UnitCocycle.exists_local <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.schlessinger_flat_fibreProduct : ∀ (P R₁ R₂ R₀ B₁ B₂ B₀ B : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀) (a₁ : R₁ ⟶ B₁) (a₂ : R₂ ⟶ B₂) (a₀ : R₀ ⟶ B₀) (b₁ : B₁ ⟶ B₀) (b₂ : B₂ ⟶ B₀) (c₁ : B ⟶ B₁) (c₂ : B ⟶ B₂) (a : P ⟶ B), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → IsPushout a₁ g₁ b₁ a₀ → IsPushout a₂ g₂ b₂ a₀ → a₁.hom.Flat → a₂.hom.Flat → IsPullback c₁ c₂ b₁ b₂ → a ≫ c₁ = f₁ ≫ a₁ → a ≫ c₂ = f₂ ≫ a₂ → a.hom.Flat ∧ IsPushout a f₁ c₁ a₁ ∧ IsPushout a f₂ c₂ a₂ := by
  first | exact @GlobalTheory.SchlessingerFlat.schlessinger_flat | exact GlobalTheory.SchlessingerFlat.schlessinger_flat | (intros; apply GlobalTheory.SchlessingerFlat.schlessinger_flat <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.splitting_absence_spreads_alt : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (D : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = MvPolynomial.map φ f ∧ ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P (MvPolynomial.map φ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q (MvPolynomial.map φ g) ≠ 0) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → ¬ (∃ u v : MvPolynomial σ k, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = MvPolynomial.map ψ f ∧ ∃ P Q : σ → k, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P (MvPolynomial.map ψ g) ≠ 0 ∧ MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0) := by
  first | exact @GlobalTheory.splitting_absence_spreads | exact GlobalTheory.splitting_absence_spreads | (intros; apply GlobalTheory.splitting_absence_spreads <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.finrank_jointWeightSpace_eq_of_charpoly : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H] [FiniteDimensional k H] (σ : C →+* Module.End k H) (r : ℕ), (∀ c : C, LinearMap.charpoly (σ c) = ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ r).map (Int.castRingHom k)) → ∀ χ : C →+* k, Module.finrank k ↥(⨅ c : C, (σ c).maxGenEigenspace (χ c)) = r * Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  first | (exact @GlobalTheory.WeightCount.finrank_weight_eq) | (exact GlobalTheory.WeightCount.finrank_weight_eq) | (intros; apply GlobalTheory.WeightCount.finrank_weight_eq <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_separable_normalization_reduced_fibers : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A], ¬ IsField A → ∃ y : A, (Polynomial.aeval (R := k) y).Finite ∧ ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → y - algebraMap k A α ∉ Q ^ 2 := by
  first | (exact @GlobalTheory.exists_separable_normalisation_reduced_fibres) | (exact GlobalTheory.exists_separable_normalisation_reduced_fibres) | (intros; apply GlobalTheory.exists_separable_normalisation_reduced_fibres  <;> assumption)
end

section

open GlobalTheory.EtC

theorem _root_.GlobalTheory.T.isAlgClosed_fractionRing_atPrime_of_etale' : ∀ (T E : Type) [CommRing T] [IsDomain T] [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime] [IsDomain (Localization.AtPrime P)], IsAlgClosed (FractionRing T) → IsAlgClosed (FractionRing (Localization.AtPrime P)) := by
  first | (exact @GlobalTheory.isAlgClosed_fractionRing_atPrime_of_etale) | (exact GlobalTheory.isAlgClosed_fractionRing_atPrime_of_etale) | (intros; apply GlobalTheory.isAlgClosed_fractionRing_atPrime_of_etale  <;> assumption)
end

section

open TensorProduct

theorem _root_.GlobalTheory.T.exists_pow_eq_of_kaehler_D_eq_zero' : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (K : Type) [Field K] [Algebra k K] (f : K), KaehlerDifferential.D k K f = 0 → ∃ h : K, h ^ p = f := by
  first | exact @GlobalTheory.exists_pow_eq_of_kaehler_D_eq_zero | exact GlobalTheory.exists_pow_eq_of_kaehler_D_eq_zero | (intros; apply GlobalTheory.exists_pow_eq_of_kaehler_D_eq_zero <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.exists_integral_unimodular_matrix_for_depth : ∀ (C : Type) [Field C] [IsAlgClosed C] (v : AddValuation C (WithTop ℝ)) (V : Type) [AddCommGroup V] [Module C V] (N : ℕ), 0 < N → ∀ (j m : ℕ) (z : Fin m → V), Module.finrank C (Submodule.span C (Set.range z)) ≤ j → ∃ x : Matrix (Fin m) (Fin m) C, (∀ w u, IsIntV v (x w u)) ∧ v x.det = 0 ∧ ∀ w : Fin m, j ≤ w.val → ∑ u, (x w u) ^ N • z u = 0 := by
  first | exact @GlobalTheory.powRow_matrix | exact GlobalTheory.powRow_matrix | (intros; apply GlobalTheory.powRow_matrix <;> assumption)
end
