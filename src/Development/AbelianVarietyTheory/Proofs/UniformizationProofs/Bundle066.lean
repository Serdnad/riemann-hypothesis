module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEquivPow
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingAutOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle058
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle016
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
public import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Free
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finrank_eq_card_kernel_points_of_etale :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ φ : B ⟶ B, ∀ [IsFinite φ.left] [Etale φ.left], ∀ x : B.left, φ.left.finrank x = Nat.card {y : 𝟙_ _ ⟶ B // y ≫ φ = 1} := by
  intro K _ _ B _ _ hB φ _ _ x
  have := hB.geomConnected
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace_of_subsingleton B.hom
  let o : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B := 1
  let t : Spec (CommRingCat.of K) ⟶ B.left := o.left
  obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  have ht : t ≫ B.hom = 𝟙 _ := Over.w o
  rw [(Scheme.Hom.isLocallyConstant_finrank φ.left).apply_eq_of_preconnectedSpace x (t z),
    ← (GlobalTheory.FinEt.card_points_eq_finrank φ.left t z).2]
  refine Nat.card_congr
    { toFun := fun y ↦ ⟨Over.homMk y.1 ?_, Over.OverMorphism.ext y.2⟩
      invFun := fun y ↦ ⟨y.1.left, congrArg CommaMorphism.left y.2⟩
      left_inv := fun y ↦ rfl
      right_inv := fun y ↦ Subtype.ext (Over.OverMorphism.ext rfl) }
  change y.1 ≫ B.hom = 𝟙 _
  rw [← Over.w φ, ← Category.assoc, y.2, ht]

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct

namespace GlobalTheory.Unif

theorem finFlatChart_of_openImmersion {X Y Z S B : Scheme.{0}} (f : X ⟶ B) (s : S ⟶ B)
    (j : Y ⟶ X) [IsOpenImmersion j] (i : Z ⟶ S) [IsOpenImmersion i] (p : Y ⟶ Z)
    [IsFinite p] [Flat p] [Surjective p] [Nonempty Z] (h : p ≫ i ≫ s = j ≫ f) :
    ∃ (W : X.Opens) (V : S.Opens) (π : W.toScheme ⟶ V.toScheme), (W : Set X).Nonempty ∧
      IsFinite π ∧ Flat π ∧ Surjective π ∧ π ≫ V.ι ≫ s = W.ι ≫ f := by
  obtain ⟨y, -⟩ := p.surjective (Classical.arbitrary Z)
  refine ⟨j.opensRange, i.opensRange, j.isoOpensRange.inv ≫ p ≫ i.isoOpensRange.hom,
    ⟨j y, y, rfl⟩, inferInstance, inferInstance, inferInstance, ?_⟩
  simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, h]
  rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι_assoc]

theorem exists_finFlat_away (R A : Type) [CommRing R] [CommRing A] [IsDomain R]
    [IsNoetherianRing R] (φ : R →+* A) (hφ : φ.Finite) (hi : Function.Injective φ) :
    ∃ (Y Z : Scheme.{0}) (j : Y ⟶ Spec (CommRingCat.of A)) (i : Z ⟶ Spec (CommRingCat.of R))
      (p : Y ⟶ Z), IsOpenImmersion j ∧ IsOpenImmersion i ∧ IsFinite p ∧ Flat p ∧ Surjective p ∧
      Nonempty Z ∧ p ≫ i = j ≫ Spec.map (CommRingCat.ofHom φ) := by
  algebraize [φ]
  have : Module.FinitePresentation R A := Module.finitePresentation_of_finite R A
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors R) (LocalizedModule.mkLinearMap (nonZeroDivisors R) A) (FractionRing R)
  have hfree' : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] A) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) A)
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R (Localization.Away r) A)
  have h1 : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    rw [IsFinite.SpecMap_iff]; exact hφ
  have h2 : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    ⟨hφ.to_isIntegral.comap_surjective hi⟩
  have h3 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) :=
    inferInstance
  have hd : IsDomain (Localization.Away r) :=
    IsLocalization.isDomain_localization (Submonoid.powers_le.mpr hr)
  refine ⟨_, _, _, _, _, MorphismProperty.of_isPullback hpb h3, h3,
    MorphismProperty.of_isPullback hpb.flip h1, ?_, MorphismProperty.of_isPullback hpb.flip h2,
    inferInstanceAs (Nonempty (PrimeSpectrum (Localization.Away r))), hpb.w⟩
  rw [Flat.SpecMap_iff]
  exact (RingHom.flat_algebraMap_iff (R := Localization.Away r)
    (S := Localization.Away r ⊗[R] A)).mpr inferInstance

theorem exists_finite_flat_chart : ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f], ∃ (g : ℕ) (W : X.Opens) (V : (Spec (CommRingCat.of (MvPolynomial (Fin g) K))).Opens) (π : W.toScheme ⟶ V.toScheme), (W : Set X).Nonempty ∧ IsFinite π ∧ Flat π ∧ Surjective π ∧ π ≫ V.ι ≫ (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K)))) = W.ι ≫ f := by
  intro K _ X _ f _
  obtain ⟨_, ⟨U, hU, rfl⟩, hξ, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  replace hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨_, hξ⟩⟩
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (hU.fromSpec ≫ f)
  have hft : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  have hft' : ψ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft
  letI : Algebra K Γ(X, U) := ψ.hom.toAlgebra
  have : Algebra.FiniteType K Γ(X, U) := hft'
  obtain ⟨g, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K Γ(X, U)
  obtain ⟨Y, Z, j, i, p, _, _, _, _, _, _, h⟩ :=
    exists_finFlat_away _ _ φ.toRingHom hfin hinj
  refine ⟨g, finFlatChart_of_openImmersion f _ (j ≫ hU.fromSpec) i p ?_⟩
  rw [reassoc_of% h, Category.assoc, ← hψ, ← Spec.map_comp]
  congr 2
  ext x
  exact φ.commutes x

end GlobalTheory.Unif
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SectionAut

abbrev PP {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (a : ℤ) : LB Y :=
  LB.LinComb L (K := Fin 1) (fun _ => p) (fun _ => a)

theorem mem_one {X Y : Scheme.{0}} {L : LB X} {p : Y ⟶ X} {j : Fin 1 → L.ι} {y : Y} :
    y ∈ LB.wchart L (fun _ : Fin 1 => p) j ↔ p y ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem exists_equiv {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N n : ℕ) :
    ∃ E : H0 (PP L p N) n ≃ LB.Sec (PP L p ((N * n : ℕ) : ℤ)),
      ∀ a (j : Fin 1 → L.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ LB.wchart L (fun _ : Fin 1 => p) j →
        gs r z (LB.wchart L (fun _ : Fin 1 => p) j) ((E a).f j) =
          gs r z (LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j)) (a.f (fun _ => j)) := by
  obtain ⟨E, hE⟩ := PowSections.exists_equiv L p N n
  refine ⟨E, fun a j Z r z hz => ?_⟩
  have le : LB.wchart L (fun _ : Fin 1 => p) j ≤ LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j) :=
    fun y hy => Set.mem_iInter.2 fun _ => hy
  have e : (E a).f j = (Y.presheaf.map (homOfLE le).op).hom (a.f (fun _ => j)) :=
    fn_ext fun y hy => (hE a j y (mem_one.1 hy)).trans (gs_res (𝟙 Y) y le hy _).symm
  exact (congrArg (gs r z _) e).trans (gs_res r z le hz _)

theorem exists_gen_of_iso {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N n : ℕ) (F ψ : Y ⟶ Y) (hψ : ψ ≫ F = 𝟙 Y)
    (m : Y ⟶ X) (hm : ψ ≫ p = m) (w : LB.Iso (PP L p N) ((PP L p N).pull F)) (hw : w.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![p, m] ![((N * n : ℕ) : ℤ), -((N * n : ℕ) : ℤ)]), α.IsGen ∧
      ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, m] j →
        gm (𝟙 Y) y (LB.wchart L ![p, m] j) (α.s j) = Geo.Tor.gw w ψ y (fun _ => j 0) (fun _ => j 1) ^ (n : ℤ) := by
  subst hm
  have hF : ∀ y, F (ψ y) = y := fun y => by
    rw [← Scheme.Hom.comp_apply, hψ]; rfl
  have h0 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, ψ ≫ p] j →
      F (ψ y) ∈ (PP L p N).U (fun _ => j 0) := fun j y hy => by
    rw [hF]; exact mem_one.2 (Set.mem_iInter.1 hy 0)
  have h1 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, ψ ≫ p] j →
      ψ y ∈ (PP L p N).U (fun _ => j 1) := fun j y hy => mem_one.2 (Set.mem_iInter.1 hy 1)
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L ![p, ψ ≫ p] j ≤
      ψ ⁻¹ᵁ (((PP L p N).pull F).U (fun _ _ => j 0) ⊓ (PP L p N).U (fun _ => j 1)) := fun j y hy =>
    ⟨mem_pull.2 (h0 j y hy), h1 j y hy⟩
  let α : LB.Gen (LB.LinComb L (K := Fin 2) ![p, ψ ≫ p] ![((N * n : ℕ) : ℤ), -((N * n : ℕ) : ℤ)]) :=
    ⟨fun j => res (le j) (pullU ψ _ (w.s (fun _ _ => j 0, fun _ => j 1))) ^ (n : ℤ)⟩
  have hα : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![p, ψ ≫ p] j →
      gm (𝟙 Y) y (LB.wchart L ![p, ψ ≫ p] j) (α.s j) =
        Geo.Tor.gw w ψ y (fun _ => j 0) (fun _ => j 1) ^ (n : ℤ) := fun j y hy =>
    (map_zpow _ _ _).trans (congrArg (· ^ (n : ℤ))
      ((gm_res (𝟙 Y) y (le j) hy _).trans (gm_pull (𝟙 Y) ψ y (((PP L p N).pull F).U (fun _ _ => j 0) ⊓ (PP L p N).U (fun _ => j 1)) (le j hy) _)))
  refine ⟨α, isGen_of_gm α fun y j j' hj hj' => ?_, hα⟩
  have e := (isGen_iff w).1 hw Y ψ y _ _ _ _ (h0 j y hj) (h0 j' y hj') (h1 j y hj) (h1 j' y hj')
  have e0 := gm_linComb L (fun _ : Fin 1 => p) (fun _ => (N : ℤ)) (ψ ≫ F) y (fun _ => j 0) (fun _ => j' 0)
    (h0 j y hj) (h0 j' y hj')
  have e1 := gm_linComb L (fun _ : Fin 1 => p) (fun _ => (N : ℤ)) ψ y (fun _ => j 1) (fun _ => j' 1)
    (h1 j y hj) (h1 j' y hj')
  rw [Fin.prod_univ_one] at e0 e1
  have e' := e.trans (congrArg₂ (fun a b => a * b⁻¹ * _) e0 e1)
  rw [hα j y hj, hα j' y hj', e', trF, Fin.prod_univ_two, hψ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Category.id_comp, mul_zpow, inv_zpow, ← zpow_mul,
    Nat.cast_mul, zpow_neg]

theorem chart_le {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => p) j ≤ LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy

def rho {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) :
    Γ(Y, LB.wchart (PP L p N) (fun _ : Fin 1 => 𝟙 Y) (fun _ => j)) →+* Γ(Y, LB.wchart L (fun _ : Fin 1 => p) j) :=
  (Y.presheaf.map (homOfLE (chart_le L p N j)).op).hom

theorem rho_injective {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) :
    Function.Injective (rho L p N j) := fun a b h => fn_ext fun y hy => by
  have hy' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : Fin 1 => p) j := Set.mem_iInter.1 hy 0
  exact (gs_res (𝟙 Y) y (chart_le L p N j) hy' a).symm.trans ((congrArg (gs (𝟙 Y) y _) h).trans
    (gs_res (𝟙 Y) y (chart_le L p N j) hy' b))

theorem rho_resTop {X Y : Scheme.{0}} (L : LB X) (p : Y ⟶ X) (N : ℤ) (j : Fin 1 → L.ι) (c : Γ(Y, ⊤)) :
    rho L p N j (resTop _ c) = resTop _ c := fn_ext fun y hy =>
  (gs_res (𝟙 Y) y (chart_le L p N j) hy _).trans ((gs_res (𝟙 Y) y le_top (chart_le L p N j hy) c).trans
    (gs_res (𝟙 Y) y le_top hy c).symm)

theorem exists_iso {K : Type} [CommRing K] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    (Y : Over (Spec (CommRingCat.of K))) [IsProper Y.hom] (p : Y.left ⟶ X) (N : ℕ) (hA : RelAmple Y (PP L p N))
    (Φ : ∀ n : ℕ, 1 ≤ n → LB.Sec (PP L p ((N * n : ℕ) : ℤ)) ≃ LB.Sec (PP L p ((N * n : ℕ) : ℤ)))
    (hlin : ∀ n hn (c : K) (s s' s'' : LB.Sec (PP L p ((N * n : ℕ) : ℤ))),
      (∀ j, s''.f j = resTop _ (scal Y.hom c) * s.f j + s'.f j) →
      ∀ j, (Φ n hn s'').f j = resTop _ (scal Y.hom c) * (Φ n hn s).f j + (Φ n hn s').f j)
    (hmul : ∀ n m hn hm hnm (s : LB.Sec (PP L p ((N * n : ℕ) : ℤ))) (s' : LB.Sec (PP L p ((N * m : ℕ) : ℤ)))
      (s'' : LB.Sec (PP L p ((N * (n + m) : ℕ) : ℤ))),
      (∀ j, @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) (s''.f j) =
        @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) (s.f j) *
          @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) (s'.f j)) →
      ∀ j, @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ (n + m) hnm s'').f j) =
        @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ n hn s).f j) *
          @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ m hm s').f j)) :
    ∃ ψ : Y ≅ Y, ∀ (m : Y.left ⟶ X), ψ.hom.left ≫ p = m → ∀ n hn,
      ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![p, m] ![((N * n : ℕ) : ℤ), -((N * n : ℕ) : ℤ)]), α.IsGen ∧
        ∀ s (j : Fin 2 → L.ι) (y : Y.left), y ∈ LB.wchart L ![p, m] j →
          gs (𝟙 _) y (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 0)) ((Φ n hn s).f (fun _ => j 0)) =
            (gm (𝟙 _) y (LB.wchart L ![p, m] j) (α.s j)).val *
              gs ψ.hom.left y (LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 1)) (s.f (fun _ => j 1)) := by
  choose E hE using fun n => exists_equiv L p N n
  have hE' : ∀ n a j, @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((E n a).f j) =
      rho L p N j (a.f (fun _ => j)) := fun n a j =>
    fn_ext fun y hy => (hE n a j _ (𝟙 _) y hy).trans (gs_res (𝟙 _) y (chart_le L p N j) hy _).symm
  let θ : ∀ n : ℕ, 1 ≤ n → (H0 (PP L p N) n ≃ H0 (PP L p N) n) := fun n hn => (E n).trans ((Φ n hn).trans (E n).symm)
  have hθE : ∀ n hn a, E n (θ n hn a) = Φ n hn (E n a) := fun n hn a => (E n).apply_symm_apply _
  have hθ : ∀ n hn a j, rho L p N j ((θ n hn a).f (fun _ => j)) =
      @id Γ(Y.left, LB.wchart L (fun _ : Fin 1 => p) j) ((Φ n hn (E n a)).f j) := fun n hn a j => by
    rw [← hE', hθE]
  have one : ∀ j : Fin 1 → (PP L p N).ι, ∃ i, j = fun _ => i := fun j =>
    ⟨j 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
  obtain ⟨Φ₀, w, hw, H⟩ := exists_iso_of_sectionRing_aut_of_relAmple K Y (PP L p N) (LB.isLB_linComb hL _ _) hA θ
    (fun n hn c a b d h j => by
      obtain ⟨i, rfl⟩ := one j
      apply rho_injective L p N i
      have e := hlin n hn c (E n b) (E n a) (E n d) (fun j => (hE' n d j).trans ((congrArg (rho L p N j) (h _)).trans
        ((map_add _ _ _).trans ((add_comm _ _).trans (congrArg₂ (· + ·) ((map_mul _ _ _).trans
          (congrArg₂ (· * ·) (rho_resTop L p N j _) (hE' n b j).symm)) (hE' n a j).symm))))) i
      exact (hθ n hn d i).trans (e.trans ((map_add _ _ _).trans ((add_comm _ _).trans (congrArg₂ (· + ·)
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) (rho_resTop L p N i _) (hθ n hn b i))) (hθ n hn a i)))).symm))
    (fun n m hn hm a b d h j => by
      obtain ⟨i, rfl⟩ := one j
      apply rho_injective L p N i
      have e := hmul n m hn hm (hn.trans (Nat.le_add_right n m)) (E n a) (E m b) (E (n + m) d)
        (fun j => (hE' _ d j).trans ((congrArg (rho L p N j) (h _)).trans
          ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hE' n a j).symm (hE' m b j).symm)))) i
      exact (hθ _ _ d i).trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hθ n hn a i) (hθ m hm b i))).symm))
  have hψ : Φ₀.inv.left ≫ Φ₀.hom.left = 𝟙 _ := by rw [← Over.comp_left, Φ₀.inv_hom_id, Over.id_left]
  refine ⟨Φ₀.symm, fun m hm n hn => ?_⟩
  obtain ⟨α, hα, hv⟩ := exists_gen_of_iso L p N n Φ₀.hom.left Φ₀.inv.left hψ m hm w hw
  refine ⟨α, hα, fun s j y hy => ?_⟩
  obtain ⟨a, rfl⟩ := (E n).surjective s
  have hF : Φ₀.hom.left (Φ₀.inv.left y) = y := by
    rw [← Scheme.Hom.comp_apply, hψ]; rfl
  have h0 : y ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 0) := mem_one.2 (Set.mem_iInter.1 hy 0)
  have h1 : Φ₀.inv.left y ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 1) := by
    subst hm; exact mem_one.2 (Set.mem_iInter.1 hy 1)
  have e := H n hn a _ Φ₀.inv.left y (fun _ _ => j 0) (fun _ _ => j 1)
    (fun _ => (congrArg (· ∈ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j 0)) hF).mpr h0) (fun _ => h1)
  rw [hψ, Fin.prod_univ_one, Category.comp_id] at e
  rw [← hθE, hE n _ _ _ (𝟙 _) y h0, hv j y hy]
  exact e.trans (congrArg _ (hE n a _ _ Φ₀.inv.left y h1).symm)

end SectionAut

theorem exists_iso_of_multiplicative_section_family : ∀ (F : Type) [Field F] (S : Scheme.{0}) (P : PolAV S) (t : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), 1 ≤ N → ∀ Φ : ∀ k : ℕ, LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)) ≃ LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)), (∀ k (s s' s'' : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (c : Γ((Over.mk t).left, ⊤)), (∀ j, s''.f j = liftFun P.A _ c * s.f j + s'.f j) → ∀ j, (Φ k s'').f j = liftFun P.A _ c * (Φ k s).f j + (Φ k s').f j) → (∀ k l (s : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t))) (s' : LB.Sec (LPow P.A P.L ((N * (l + 1) : ℕ) : ℤ) (Over.mk t))) (s'' : LB.Sec (LPow P.A P.L ((N * (k + l + 1 + 1) : ℕ) : ℤ) (Over.mk t))), (∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s''.f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s.f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s'.f j)) → ∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ (k + l + 1) s'').f j) = @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ k s).f j) * @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ l s').f j)) → ∃ (ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P.A) (_ : ψ.hom ≫ fst _ _ = fst _ _), ∀ k, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (Over.mk t) P.A).left, (ψ.hom ≫ snd _ _).left] ![((N * (k + 1) : ℕ) : ℤ), -((N * (k + 1) : ℕ) : ℤ)]), α.IsGen ∧ ∀ s, IsTwistPull P.A P.L ψ.hom (ψ.hom ≫ snd _ _) rfl _ _ α s (Φ k s) := by
  intro F _ S P t N hN Φ hlin hmul
  obtain ⟨hp, hA⟩ := isProper_and_relAmple_lPow F S P t N hN
  have hp' : IsProper (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left).hom := hp
  have hmul' : ∀ k l m (_ : m = k + l + 1) (s : LB.Sec (LPow P.A P.L ((N * (k + 1) : ℕ) : ℤ) (Over.mk t)))
      (s' : LB.Sec (LPow P.A P.L ((N * (l + 1) : ℕ) : ℤ) (Over.mk t)))
      (s'' : LB.Sec (LPow P.A P.L ((N * (m + 1) : ℕ) : ℤ) (Over.mk t))),
      (∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s''.f j) =
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s.f j) *
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) (s'.f j)) →
      ∀ j, @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ m s'').f j) =
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ k s).f j) *
        @id Γ((Over.mk t ⊗ P.A).left, LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) j) ((Φ l s').f j) := by
    rintro k l _ rfl
    exact hmul k l
  obtain ⟨ψ₀, H⟩ := SectionAut.exists_iso P.L P.isLB
    (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left) (snd (Over.mk t) P.A).left N hA
    (fun n hn => match n, hn with | k + 1, _ => Φ k)
    (fun n hn c => match n, hn with
      | k + 1, _ => fun s s' s'' => hlin k s s' s'' ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c))
    (fun n m hn hm _ => match n, m, hn, hm with
      | k + 1, l + 1, _, _ => hmul' k l (k + 1 + l) (by omega))
  have w₀ : ψ₀.hom.left ≫ (fst (Over.mk t) P.A).left = (fst (Over.mk t) P.A).left := Over.w ψ₀.hom
  let ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P.A := Over.isoMk ((Over.forget _).mapIso ψ₀) (by
    have e : (fst (Over.mk t) P.A).left ≫ t = (Over.mk t ⊗ P.A).hom := Over.w (fst (Over.mk t) P.A)
    show ψ₀.hom.left ≫ (Over.mk t ⊗ P.A).hom = (Over.mk t ⊗ P.A).hom
    rw [← e, ← Category.assoc, w₀])
  refine ⟨ψ, Over.OverMorphism.ext w₀, fun k => ?_⟩
  obtain ⟨α, hα, hv⟩ := H (ψ.hom ≫ snd _ _).left rfl (k + 1) (Nat.succ_pos k)
  refine ⟨α, hα, fun s j => fn_ext fun y hy => ?_⟩
  have l₀ := chart_le_zero P.A P.L (ψ.hom ≫ snd _ _) j
  have l₁ := chart_le_pull P.A P.L ψ.hom (ψ.hom ≫ snd _ _) rfl j
  exact (gs_res (𝟙 _) y l₀ hy _).trans ((hv s j y hy).trans ((gs_mul (𝟙 _) y _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) ((gs_res (𝟙 _) y l₁ hy _).trans
      (gs_pull (𝟙 _) ψ.hom.left y
        (LB.wchart P.L (fun _ : Fin 1 => (snd (Over.mk t) P.A).left) (fun _ => j 1)) (l₁ hy) _)))).symm)

end GlobalTheory
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ThetaRep

theorem finrank_secM (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {n : ℕ}
    (hn : 1 ≤ n) {F : Type} [Field F] (q : Spec (CommRingCat.of F) ⟶ S) :
    Module.finrank Γ((Over.mk q).left, ⊤) (SecM P.A P.L n (Over.mk q)) = n ^ P.g := by
  obtain ⟨U, hU, b, hb⟩ := hS S P n hn (q (IsLocalRing.closedPoint F))
  have hr : Set.range q ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    obtain rfl : y = IsLocalRing.closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
    exact ⟨⟨_, hU⟩, rfl⟩
  let t : Spec (CommRingCat.of F) ⟶ (overRes (T := baseOver S) U).left := IsOpenImmersion.lift U.ι q hr
  have ht : t ≫ (overRes (T := baseOver S) U).hom = q := by
    show IsOpenImmersion.lift U.ι q hr ≫ (U.ι ≫ 𝟙 _) = q
    rw [Category.comp_id, IsOpenImmersion.lift_fac]
  have pull : ∀ i, ∃ b' : LB.Sec (LPow P.A P.L n (baseAt t)),
      IsPullSec P.A P.L n (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i) b' := fun i => by
    obtain ⟨s', hs'⟩ := IndivisibleSection.exists_pull_chart (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
    exact ⟨s', fun j => hs' j _⟩
  choose b' hb' using pull
  obtain ⟨h₁, h₂⟩ := hb F t b' hb'
  rw [← ht]
  haveI : Nontrivial Γ((baseAt t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  exact (Module.finrank_eq_card_basis (Module.Basis.mk h₁ h₂.ge)).trans (Fintype.card_fin _)

theorem eq_one_of_weilIs (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {F : Type} [Field F]
    [IsAlgClosed F] (q : Spec (CommRingCat.of F) ⟶ S) {n : ℕ} (hn : (n : F) ≠ 0) (x : Over.mk q ⟶ P.A)
    (hx : x ^ n = 1) (h : ∀ y : Over.mk q ⟶ P.A, y ^ n = 1 → WeilIs P.A P.L n x y 1) : x = 1 := by
  obtain ⟨P', g, hg, -, hm, t, ht⟩ := hL.polBaseChange S _ q P
  have hp : IsGrpPullback P'.A P.A q g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hm]
    rfl⟩
  obtain ⟨w, hw⟩ := LBIso.symm (⟨t, ht⟩ : LBIso _ _)
  let ρ : Over.mk q ⟶ Over.mk (𝟙 _ ≫ q) := Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  let Φ : (baseOver (Spec (CommRingCat.of F)) ⟶ P'.A) →* (Over.mk q ⟶ P.A) :=
    MonoidHom.mk' (fun y => ρ ≫ toBase hg.w y) (fun a b => by rw [hm, MonObj.comp_mul])
  have hΦ : ∀ y, (Φ y).left = y.left ≫ g := fun y => Category.id_comp _
  have inj : Function.Injective Φ := fun a b e => Over.OverMorphism.ext (hg.hom_ext
    ((hΦ a).symm.trans ((congrArg CommaMorphism.left e).trans (hΦ b))) ((Over.w a).trans (Over.w b).symm))
  let x' : baseOver (Spec (CommRingCat.of F)) ⟶ P'.A :=
    Over.homMk (hg.lift x.left (𝟙 _) ((Over.w x).trans (Category.id_comp q).symm)) (hg.lift_snd _ _ _)
  have ex : Φ x' = x := Over.OverMorphism.ext ((hΦ x').trans (hg.lift_fst _ _ _))
  have hx' : x' ^ n = 1 := inj (by rw [map_pow, ex, hx, map_one])
  have := hL.weilNondeg F P' n hn x' hx' fun y hy =>
    (GlobalTheory.weilIs_grpPullback_iff hL.globalFns hL.cube P P' hp w hw (t := q) (t' := 𝟙 _) (Category.id_comp q).symm n x' y hx' hy x (Φ y)
      ((congrArg CommaMorphism.left ex).symm.trans (hΦ x')) (hΦ y) 1).1 (h _ (by rw [← map_pow, hy, map_one]))
  rw [← ex, this, map_one]

theorem exists_projective_rep : Laws → Laws2 → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), (N : F) ≠ 0 → ∃ (Φ : {x : Over.mk p ⟶ P.A // x ^ N = 1} → (SecM P.A P.L N (Over.mk p) ≃ₗ[Γ((Over.mk p).left, ⊤)] SecM P.A P.L N (Over.mk p))) (e : {x : Over.mk p ⟶ P.A // x ^ N = 1} → {x : Over.mk p ⟶ P.A // x ^ N = 1} → Γ((Over.mk p).left, ⊤)ˣ), Module.finrank Γ((Over.mk p).left, ⊤) (SecM P.A P.L N (Over.mk p)) = N ^ P.g ∧ (∀ a, ∃ θ : ThetaGrp P.A P.L N (Over.mk p), θ.pt = a.1 ∧ ∀ v, IsActOf P.A P.L N θ (SecM.toSec P.A v) (SecM.toSec P.A (Φ a v))) ∧ (∀ a b c, c.1 = a.1 * b.1 → ∃ r : Γ((Over.mk p).left, ⊤)ˣ, ∀ v, Φ c v = r.val • Φ a (Φ b v)) ∧ (∀ a b, WeilIs P.A P.L N a.1 b.1 (e a b) ∧ ∀ v, Φ a (Φ b v) = (e a b).val • Φ b (Φ a v)) ∧ ∀ a, (∀ b, e a b = 1) → a.1 = 1) := by
  intro hL _ S _ P F _ _ p N hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 fun e => hN (by rw [e, Nat.cast_zero])
  haveI : Subsingleton (Over.mk p).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  haveI : Nonempty (Over.mk p).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of F)))
  obtain ⟨ρ, hact, hcomm, hrat, hmul⟩ := thetaGrp_acts_linearly hL.globalFns S P N (Over.mk p)
  choose θ hθ using fun a : {x : Over.mk p ⟶ P.A // x ^ N = 1} =>
    BoxTheta.exists_theta hL.kerPow P hN1 (T := Over.mk p) a.1 a.2
  choose e he using fun a b : {x : Over.mk p ⟶ P.A // x ^ N = 1} =>
    ((hL.weil S P N (Over.mk p)).1 a.1 b.1 a.2 b.2).exists
  refine ⟨fun a => ρ (θ a), e, finrank_secM hL.secBaseChange P hN1 p,
    fun a => ⟨θ a, hθ a, fun v => (hact _ _ _).2 rfl⟩, fun a b c hc => ?_, fun a b => ⟨he a b, ?_⟩, fun a ha => ?_⟩
  · obtain ⟨θ', h₁, h₂⟩ := hmul (θ a) (θ b)
    obtain ⟨r, hr⟩ := hrat θ' (θ c) (by rw [h₁, hθ, hθ, hθ, hc])
    exact ⟨r, fun v => by rw [← h₂]; exact hr v⟩
  · refine hcomm _ _ _ ((GlobalLift.weilIs_iff_commIsOf hL.globalFns P.isAb P.isLB _ _ _).1 ?_)
    rw [hθ, hθ]
    exact he a b
  · exact eq_one_of_weilIs hL P p hN a.1 a.2 fun y hy => ha ⟨y, hy⟩ ▸ he a ⟨y, hy⟩

end GlobalTheory.ThetaRep
end
