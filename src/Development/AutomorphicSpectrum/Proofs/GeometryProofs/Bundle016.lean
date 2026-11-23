module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle001
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle003
public import Mathlib.RingTheory.Ideal.Span
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle002
public import Mathlib.RingTheory.OreLocalization.Ring
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle001
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle004
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor MonoidalCategory CartesianMonoidalCategory MonObj Limits

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

def regIso (h : IsCptGen ξ) (p : Cpt ξ) : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
  RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun a b hab => h.inj p (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩

def regPt (h : IsCptGen ξ) (p : Cpt ξ) : Sp (regAt ξ p) ⟶ X :=
  spMap (regIso h p).toRingHom ≫ X.fromSpecStalk p.1

theorem genMap_regIso_symm (h : IsCptGen ξ) (p : Cpt ξ) (a : regAt ξ p) :
    genMap ξ p ((regIso h p).symm a) = a := by
  exact congrArg Subtype.val ((regIso h p).apply_symm_apply a)

set_option backward.isDefEq.respectTransparency false in
theorem genMap_specializes {p q : Cpt ξ} (hs : q.1 ⤳ p.1) (s : X.presheaf.stalk p.1) :
    genMap ξ q ((X.presheaf.stalkSpecializes hs).hom s) = genMap ξ p s := by
  simp only [genMap]
  rw [← CommRingCat.comp_apply, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]

theorem regAt_le {p q : Cpt ξ} (hs : q.1 ⤳ p.1) : regAt ξ p ≤ regAt ξ q := by
  rintro _ ⟨s, rfl⟩
  exact ⟨_, genMap_specializes hs s⟩

theorem spMap_genMap_fromSpecStalk (p : Cpt ξ) : spMap (genMap ξ p) ≫ X.fromSpecStalk p.1 = ξ := by
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (x := ξ (IsLocalRing.closedPoint Ω)) (y := p.1) p.2,
    ← Category.assoc, ← Spec.map_comp] at h2
  exact h2

theorem spMap_algebraMap_regPt (h : IsCptGen ξ) (p : Cpt ξ) : spMap (algebraMap (regAt ξ p) Ω) ≫ regPt h p = ξ := by
  have e : (algebraMap (regAt ξ p) Ω).comp (regIso h p).toRingHom = genMap ξ p :=
    RingHom.ext fun x => rfl
  dsimp only [regPt, spMap]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
  exact spMap_genMap_fromSpecStalk p

abbrev regIncl {p q : Cpt ξ} (hs : q.1 ⤳ p.1) : regAt ξ p →+* regAt ξ q := Subring.inclusion (regAt_le hs)

theorem spMap_regIncl_regPt (h : IsCptGen ξ) {p q : Cpt ξ} (hs : q.1 ⤳ p.1) :
    spMap (regIncl hs) ≫ regPt h p = regPt h q := by
  have e : (regIncl hs).comp (regIso h p).toRingHom =
      (regIso h q).toRingHom.comp (X.presheaf.stalkSpecializes hs).hom :=
    RingHom.ext fun s => Subtype.ext (genMap_specializes hs s).symm
  dsimp only [regPt, spMap]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_comp,
    CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

def castPt {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x y : Sp R ⟶ S} (e : x = y) {E : Type}
    [AddCommGroup E] [Module R E] (M : LieModel G x E) : LieModel G y E := e ▸ M

theorem castPt_pt_left {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x y : Sp R ⟶ S} (e : x = y)
    {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) (a : E) :
    ((castPt e M).pt a).left = (M.pt a).left := by
  subst e
  rfl

end GlobalTheory.CompanionTheory.Ar.LieStalk
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorBC

private theorem mul_left_congr_of_base_eq {S W : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : W ⟶ S} (h : f = f')
    (y₀ z₀ : Over.mk f ⟶ G) (y₁ z₁ : Over.mk f' ⟶ G) (hy : y₁.left = y₀.left) (hz : z₁.left = z₀.left) :
    (y₁ * z₁).left = (y₀ * z₀).left := by
  subst h
  have e1 : y₁ = y₀ := Over.OverMorphism.ext hy
  have e2 : z₁ = z₀ := Over.OverMorphism.ext hz
  rw [e1, e2]

private theorem pow_eq_one_congr_of_left_eq {S W : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : W ⟶ S} (h : f = f')
    (g₀ : Over.mk f ⟶ G) (g₁ : Over.mk f' ⟶ G) (hg : g₁.left = g₀.left) (N : ℕ) :
    g₁ ^ N = 1 ↔ g₀ ^ N = 1 := by
  subst h
  have e : g₁ = g₀ := Over.OverMorphism.ext hg
  rw [e]

theorem isTorsionAlong_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (Γ' : BT.QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom φ) ≫ x) N (F ≫ i) := by
  intro R _ _ T _ Γ S G _ x N i hT R' _ _ φ Γ' F hB
  have hw : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ) := hB.cart.w
  have hassoc : ∀ {Y : Scheme.{0}} (h : Y ⟶ Spec (CommRingCat.of R')),
      h ≫ (Spec.map (CommRingCat.ofHom φ) ≫ x) = (h ≫ Spec.map (CommRingCat.ofHom φ)) ≫ x :=
    fun _ => (Category.assoc _ _ _).symm
  have lift1 : ∀ (Y : Over (Spec (CommRingCat.of R'))) (y : Y ⟶ Γ'.G),
      (y.left ≫ F) ≫ Γ.G.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ) := by
    intro Y y
    rw [Category.assoc, hw, ← Category.assoc, Over.w y]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, hT.isOver, ← Category.assoc, hw, Category.assoc]
  · intro Y y z y₀ z₀ hy hz
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    let y' : Y' ⟶ Γ.G := Over.homMk (y.left ≫ F) (lift1 Y y)
    let z' : Y' ⟶ Γ.G := Over.homMk (z.left ≫ F) (lift1 Y z)
    let y₁ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk y₀.left ((Over.w y₀).trans (hassoc Y.hom))
    let z₁ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk z₀.left ((Over.w z₀).trans (hassoc Y.hom))
    have hm := hT.mul Y' y' z' y₁ z₁
      (by show y₀.left = (y.left ≫ F) ≫ i; rw [Category.assoc]; exact hy)
      (by show z₀.left = (z.left ≫ F) ≫ i; rw [Category.assoc]; exact hz)
    have hF := hB.mul Y y z y' z' rfl rfl
    rw [← mul_left_congr_of_base_eq (hassoc Y.hom) y₀ z₀ y₁ z₁ rfl rfl, hm, hF, Category.assoc]
  · intro Y y z h
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    have e := hT.inj Y' (Over.homMk (y.left ≫ F) (lift1 Y y) : Y' ⟶ Γ.G)
      (Over.homMk (z.left ≫ F) (lift1 Y z) : Y' ⟶ Γ.G)
      (by show (y.left ≫ F) ≫ i = (z.left ≫ F) ≫ i; rw [Category.assoc, Category.assoc]; exact h)
    have e2 : y.left ≫ F = z.left ≫ F := congrArg (fun m => m.left) e
    apply Over.OverMorphism.ext
    exact hB.cart.hom_ext e2 ((Over.w y).trans (Over.w z).symm)
  · intro Y g
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    let g₁ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk g.left ((Over.w g).trans (hassoc Y.hom))
    rw [← pow_eq_one_congr_of_left_eq (hassoc Y.hom) g g₁ rfl N, hT.kernel Y' g₁]
    constructor
    · rintro ⟨y', hy'⟩
      refine ⟨Over.homMk (hB.cart.lift y'.left Y.hom (Over.w y')) (hB.cart.lift_snd _ _ _), ?_⟩
      show hB.cart.lift y'.left Y.hom (Over.w y') ≫ F ≫ i = g.left
      rw [← Category.assoc, hB.cart.lift_fst]
      exact hy'
    · rintro ⟨y, hy⟩
      refine ⟨(Over.homMk (y.left ≫ F) (lift1 Y y) : Y' ⟶ Γ.G), ?_⟩
      show (y.left ≫ F) ≫ i = g.left
      rw [Category.assoc]
      exact hy

end GlobalTheory.CompanionTheory.Ar.TorBC
end
end

section


theorem _root_.GlobalTheory.T.integral_over_localization_scaled : ∀ {o K : Type} [CommRing o] [Field K] [Algebra o K] (A : Subalgebra o K) (R : Subring K), (∀ a ∈ A, a ∈ R) → (∀ r ∈ R, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ r = u / v) → ∀ (t : K), IsIntegral R t → ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ IsIntegral A (v * t) := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral | exact GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral | (intros; apply GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral <;> assumption)
end

section


theorem _root_.GlobalTheory.T.abel_summation_bound : ∀ (N : ℕ) (a D : Fin N → ℝ) (Up Lo Cc : ℝ), 0 ≤ Up → 0 ≤ Lo → 0 ≤ Cc → (∀ p q, p ≤ q → a q ≤ a p) → (∀ p, |a p| ≤ 2) → (∀ p : Fin N, (p : ℕ) + 1 < N → -Lo ≤ -∑ k ∈ Finset.Iic p, D k ∧ -∑ k ∈ Finset.Iic p, D k ≤ Up) → (∀ p : Fin N, (p : ℕ) + 1 = N → |∑ k ∈ Finset.Iic p, D k| ≤ Cc) → -(4 * Lo + 2 * Cc) ≤ ∑ p, -a p * D p ∧ ∑ p, -a p * D p ≤ 4 * Up + 2 * Cc := by
  first | exact @GlobalTheory.CompanionTheory.AbelBounds.abel_bound | exact GlobalTheory.CompanionTheory.AbelBounds.abel_bound | (intros; apply GlobalTheory.CompanionTheory.AbelBounds.abel_bound <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.primitive_element_powers_indep : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A] (f : A),
    Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f → f ≠ 0 →
    ∀ c : ℕ → k, ∑ i ∈ Finset.range p, c i • f ^ i = 0 → ∀ i < p, c i = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HopfPrim.powers_indep_of_primitive | exact GlobalTheory.CompanionTheory.HopfPrim.powers_indep_of_primitive | (intros; apply GlobalTheory.CompanionTheory.HopfPrim.powers_indep_of_primitive <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem epi_subfield_closure_range_eq_top : ∀ (O F : Type) [CommRing O] [Field F] (β : O →+* F),
    (∀ (T : Type) [CommRing T] (g₁ g₂ : F →+* T), g₁.comp β = g₂.comp β → g₁ = g₂) →
    Subfield.closure (Set.range β) = ⊤ :=
  PositivityTheory.UnitarySelfGeneration.subfield_closure_eq_top_of_epi

end GlobalTheory.CompanionTheory.Ggeo
end

section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem extend_to_fraction_field_relay : ∀ (O F L : Type) [CommRing O] [Field F] [CommRing L] (β : O →+* F) (θ : O →+* L), Subfield.closure (Set.range β) = ⊤ → (∀ b, β b ≠ 0 → IsUnit (θ b)) → (∀ a, β a = 0 → θ a = 0) → ∃ χ : F →+* L, χ.comp β = θ :=
  PositivityTheory.UnitarySelfGeneration.extends_to_fraction_field

end GlobalTheory.CompanionTheory.Ggeo
end

section


theorem _root_.GlobalTheory.T.localized_module_base_change : ∀ (R P C C' : Type) [CommRing R] [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C'] (f t : R) [AddCommGroup P] [Module R P]
  [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P] [Module.Finite (Localization.Away f) P]
  [Module.Projective (Localization.Away f) P], IsUnit (algebraMap R C f) → ∀ c : C →ₐ[R] C',
  IsLocalizedModule (Submonoid.powers t) c.toLinearMap →
  IsLocalizedModule (Submonoid.powers t) (LinearMap.compRight R c.toLinearMap : (P →ₗ[R] C) →ₗ[R] (P →ₗ[R] C')) := by
  first | exact @GlobalTheory.CompanionTheory.LocHom.isLocalizedModule_compRight_away | exact GlobalTheory.CompanionTheory.LocHom.isLocalizedModule_compRight_away | (intros; apply GlobalTheory.CompanionTheory.LocHom.isLocalizedModule_compRight_away <;> assumption)
end

section


theorem _root_.GlobalTheory.T.projective_modules_glue_cover : ∀ (R E : Type) [CommRing R] [AddCommGroup E] [Module R E] (J : Type) [Finite J] (f : J → R), Ideal.span (Set.range f) = ⊤ →
  ∀ (F : J → Type) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [∀ i, Module (Localization.Away (f i)) (F i)]
    [∀ i, IsScalarTower R (Localization.Away (f i)) (F i)] [∀ i, Module.Finite (Localization.Away (f i)) (F i)]
    [∀ i, Module.Projective (Localization.Away (f i)) (F i)] (φ : ∀ i, E →ₗ[R] F i),
    (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (φ i)) → Module.Finite R E ∧ Module.Projective R E := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.finite_projective_of_isLocalizedModule_cover | exact GlobalTheory.CompanionTheory.Ggeo.finite_projective_of_isLocalizedModule_cover | (intros; apply GlobalTheory.CompanionTheory.Ggeo.finite_projective_of_isLocalizedModule_cover <;> assumption)
end

section


theorem _root_.GlobalTheory.T.localization_sheaf_glue_modules : ∀ (R E : Type) [CommRing R] [AddCommGroup E] [Module R E] (J : Type) [Finite J] (f : J → R), Ideal.span (Set.range f) = ⊤ →
  ∀ (F : {g : R // ∃ i, f i ∣ g} → Type) [∀ g, AddCommGroup (F g)] [∀ g, Module R (F g)]
    (res : ∀ g g' : {g : R // ∃ i, f i ∣ g}, g.1 ∣ g'.1 → (F g →ₗ[R] F g'))
    (ρ : ∀ g, E →ₗ[R] F g),
    (∀ g (h : g.1 ∣ g.1) y, res g g h y = y) →
    (∀ g g' g'' (h : g.1 ∣ g'.1) (h' : g'.1 ∣ g''.1) (h'' : g.1 ∣ g''.1) y, res g' g'' h' (res g g' h y) = res g g'' h'' y) →
    (∀ g g' (h : g.1 ∣ g'.1) e, res g g' h (ρ g e) = ρ g' e) →
    (∀ g (a : R), a ∣ g.1 → IsUnit (algebraMap R (Module.End R (F g)) a)) →
    (∀ g g' (h : g.1 ∣ g'.1) (t : R), g'.1 = g.1 * t → IsLocalizedModule (Submonoid.powers t) (res g g' h)) →
    (∀ e, (∀ i, ρ ⟨f i, i, dvd_rfl⟩ e = 0) → e = 0) →
    (∀ w : ∀ i, F ⟨f i, i, dvd_rfl⟩,
      (∀ i j, res ⟨f i, i, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_right _ _) (w i) =
        res ⟨f j, j, dvd_rfl⟩ ⟨f i * f j, i, dvd_mul_right _ _⟩ (dvd_mul_left _ _) (w j)) →
      ∃ e, ∀ i, ρ ⟨f i, i, dvd_rfl⟩ e = w i) →
    ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (ρ ⟨f i, i, dvd_rfl⟩) := by
  first | exact @GlobalTheory.CompanionTheory.BasicCover.isLocalizedModule_of_basic_cover | exact GlobalTheory.CompanionTheory.BasicCover.isLocalizedModule_of_basic_cover | (intros; apply GlobalTheory.CompanionTheory.BasicCover.isLocalizedModule_of_basic_cover <;> assumption)
end

section


theorem _root_.GlobalTheory.T.dual_module_finite_projective : ∀ (R P : Type) [CommRing R] (f : R) [AddCommGroup P] [Module R P]
  [Module (Localization.Away f) P] [IsScalarTower R (Localization.Away f) P] [Module.Finite (Localization.Away f) P]
  [Module.Projective (Localization.Away f) P],
  Module.Finite (Localization.Away f) (P →ₗ[R] Localization.Away f) ∧ Module.Projective (Localization.Away f) (P →ₗ[R] Localization.Away f) := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.HomDual.finite_projective_hom | exact GlobalTheory.CompanionTheory.Ggeo.HomDual.finite_projective_hom | (intros; apply GlobalTheory.CompanionTheory.Ggeo.HomDual.finite_projective_hom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.section_extends_from_stalk_pullback : ∀ {X Y Z : Scheme.{0}} (π : Y ⟶ X) (p : X) (y₀ : Y), π y₀ = p → ∀ (c : Z ⟶ pullback π (X.fromSpecStalk p)) [IsClosedImmersion c] (s : Γ(Z, ⊤)), ∃ (W : Y.Opens) (f : Γ(Y, W)), y₀ ∈ W ∧ ((c ≫ pullback.fst π (X.fromSpecStalk p)).app W).hom f = Z.presheaf.map (homOfLE (le_top : (c ≫ pullback.fst π (X.fromSpecStalk p)) ⁻¹ᵁ W ≤ ⊤)).op s := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_open_extension | exact GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_open_extension | (intros; apply GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_open_extension <;> assumption)
end
