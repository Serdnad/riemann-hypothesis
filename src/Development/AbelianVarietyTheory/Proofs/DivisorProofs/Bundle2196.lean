module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2167
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.sepClosure_exists_pow_mem_range_of_finiteDimensional : ∀ (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K L] [FiniteDimensional K L] [Algebra K Ω] [IsSepClosure K Ω] [Algebra L Ω'] [IsSepClosure L Ω'] [Algebra K Ω'] [IsScalarTower K L Ω'] (j : Ω →ₐ[K] Ω') (y : Ω'), ∃ (m : ℕ) (x : Ω), 0 < m ∧ y ^ m = j x ∧ ∀ a b : Ω', (a - b) ^ m = a ^ m - b ^ m := by
  first | exact @GlobalTheory.Published.AbVarRed.sepClosure_finiteExt_pow_mem_range | exact GlobalTheory.Published.AbVarRed.sepClosure_finiteExt_pow_mem_range | (intros; apply GlobalTheory.Published.AbVarRed.sepClosure_finiteExt_pow_mem_range <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finiteIndex_subgroup_aut_extend_sepClosure : ∀ (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K L] [FiniteDimensional K L] [Algebra K Ω] [IsSepClosure K Ω] [Algebra L Ω'] [IsSepClosure L Ω'] [Algebra K Ω'] [IsScalarTower K L Ω'] (j : Ω →ₐ[K] Ω'), ∃ H : Subgroup (Ω ≃ₐ[K] Ω), H.FiniteIndex ∧ ∀ σ ∈ H, ∃ σ' : Ω' ≃ₐ[L] Ω', ∀ x, σ' (j x) = j (σ x) := by
  first | exact @GlobalTheory.SepExt.exists_finiteIndex_extend | exact GlobalTheory.SepExt.exists_finiteIndex_extend | (intros; apply GlobalTheory.SepExt.exists_finiteIndex_extend <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finite_image_of_map_eq_one_on_inf_finiteIndex' : ∀ (G M : Type) [Group G] [Monoid M] (ρ : G →* M) (I H : Subgroup G), H.FiniteIndex → (∀ σ ∈ I, σ ∈ H → ρ σ = 1) → (ρ '' (I : Set G)).Finite := by
  first | exact @GlobalTheory.finite_image_of_map_eq_one_on_inf_finiteIndex | exact GlobalTheory.finite_image_of_map_eq_one_on_inf_finiteIndex | (intros; apply GlobalTheory.finite_image_of_map_eq_one_on_inf_finiteIndex <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_smul_mem_span_orbit_of_numberField_lattice : ∀ (l : ℕ) [Fact l.Prime] (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (O F : Type) [CommRing O] [Field F] [NumberField F] [Algebra O F] [IsFractionRing O F] (ρ : O →+* Module.End ℤ_[l] T), Module.finrank ℤ_[l] T = Module.finrank ℚ F → (∀ (n : ℕ) (a : Fin n → O), LinearIndependent ℚ (fun i => algebraMap O F (a i)) → LinearIndependent ℤ_[l] (fun i => ρ (a i))) → ∃ (v : T) (c : ℤ_[l]), c ≠ 0 ∧ ∀ t : T, c • t ∈ Submodule.span ℤ_[l] (Set.range fun a => ρ a v) := by
  first | exact @GlobalTheory.CyclicLattice.exists_smul_mem_span_orbit | exact GlobalTheory.CyclicLattice.exists_smul_mem_span_orbit | (intros; apply GlobalTheory.CyclicLattice.exists_smul_mem_span_orbit <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.dvr_fractionField_ringEquiv_eq_unit_mul : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (σ : K' ≃+* K'), (∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → ∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l := by
  first | exact @GlobalTheory.dvr_fractionField_ringEquiv_eq_mul | exact GlobalTheory.dvr_fractionField_ringEquiv_eq_mul | (intros; apply GlobalTheory.dvr_fractionField_ringEquiv_eq_mul <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mem_range_spMap_mapRingHom_of_fibre_closedPoint : ∀ (R K : Type) [CommRing R] [Field K] (χ : R →+* K), Function.Surjective χ → ∀ (x : Sp (Polynomial R)), spMap (algebraMap R (Polynomial R)) x = spMap χ (IsLocalRing.closedPoint K) → x ∈ Set.range (spMap (Polynomial.mapRingHom χ)) := by
  first | exact @GlobalTheory.fibre_line_over_surjection | exact GlobalTheory.fibre_line_over_surjection | (intros; apply GlobalTheory.fibre_line_over_surjection <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finite_compl_punctured_line_open : ∀ (k : Type) [Field k] (V : Set (Sp (Localization.Away (Polynomial.X : Polynomial k)))), IsOpen V → ∀ (χ₁ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k), spMap χ₁.toRingHom (IsLocalRing.closedPoint k) ∈ V → Set.Finite {c : k | c ≠ 0 ∧ ∀ χ : Localization.Away (Polynomial.X : Polynomial k) →ₐ[k] k, χ (algebraMap (Polynomial k) _ Polynomial.X) = c → spMap χ.toRingHom (IsLocalRing.closedPoint k) ∉ V} := by
  first | exact @GlobalTheory.punctured_line_open_cofinite | exact GlobalTheory.punctured_line_open_cofinite | (intros; apply GlobalTheory.punctured_line_open_cofinite <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.semilinear_symm_fixes_unit_section_genericFibre : ∀ (K W K' : Type) [Field K] [CommRing W] [Field K'] [Algebra W K'] [Algebra K K'] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G] (e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A), IsMonHom e.hom → ∀ (σ : K' ≃ₐ[K] K') (x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ η[G].left → x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ → x ≫ (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) ≫ e.inv.left) = spMap (σ : K' →+* K') ≫ x := by
  first | exact @GlobalTheory.semilinear_symm_fixes_unit | exact GlobalTheory.semilinear_symm_fixes_unit | (intros; apply GlobalTheory.semilinear_symm_fixes_unit <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eq_spMap_comp_eval_zero_of_chart_comp_eq : ∀ (K : Type) [CommRing K] (Y : Scheme.{0}) (W : Y.Opens), IsAffineOpen W → ∀ (g₀ g₁ : Sp (Polynomial K) ⟶ Y), (∀ x, g₀ x ∈ W) → (∀ x, g₁ x ∈ W) → spMap (algebraMap (Polynomial K) (Localization.Away (Polynomial.X : Polynomial K))) ≫ g₀ = spMap (Polynomial.aeval (IsLocalization.Away.invSelf (Polynomial.X : Polynomial K) : Localization.Away (Polynomial.X : Polynomial K))).toRingHom ≫ g₁ → g₀ = spMap (algebraMap K (Polynomial K)) ≫ spMap (Polynomial.evalRingHom 0) ≫ g₀ := by
  first | exact @GlobalTheory.chart_map_into_affine_const | exact GlobalTheory.chart_map_into_affine_const | (intros; apply GlobalTheory.chart_map_into_affine_const <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.equalizer_sections_closed_ideal : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom → ∀ (x y : Sp R ⟶ X.left), x ≫ X.hom = 𝟙 _ → y ≫ X.hom = 𝟙 _ → ∃ I : Ideal R, ∀ (T : Type) [CommRing T] (ψ : R →+* T), (spMap ψ ≫ x = spMap ψ ≫ y ↔ ∀ r ∈ I, ψ r = 0) := by
  first | exact @GlobalTheory.sections_eqLocus_ideal | exact GlobalTheory.sections_eqLocus_ideal | (intros; apply GlobalTheory.sections_eqLocus_ideal <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isAbelianScheme_and_comm_baseChange_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsAbelianScheme ((Over.pullback (spMap (algebraMap K L))).obj A) ∧ IsCommMonObj ((Over.pullback (spMap (algebraMap K L))).obj A) := by
  first | exact @GlobalTheory.Published.AbVarRed.isAbelianScheme_baseChange_field_and_comm | exact GlobalTheory.Published.AbVarRed.isAbelianScheme_baseChange_field_and_comm | (intros; apply GlobalTheory.Published.AbVarRed.isAbelianScheme_baseChange_field_and_comm <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.semilinearModel_fixes_unit_section_abelian : ∀ (W K' : Type) [CommRing W] [IsDomain W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (σ : K' →+* K') (τ : W →+* W) (φ : G.left ⟶ G.left) (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) → φ ≫ G.hom = G.hom ≫ spMap τ → pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = ρ ≫ pullback.fst G.hom (spMap (algebraMap W K')) → ∀ (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → ∀ x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K')), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ ρ = spMap σ ≫ x → e₀ ≫ φ = spMap τ ≫ e₀ := by
  first | exact @GlobalTheory.SemilinearModel.unit_section_semilinear | exact GlobalTheory.SemilinearModel.unit_section_semilinear | (intros; apply GlobalTheory.SemilinearModel.unit_section_semilinear <;> assumption)
end
