module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle004
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle177
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2873
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.smooth_iSup_opens_comp_of_forall_smooth : ∀ (P' T : Scheme.{0}) (q : P' ⟶ T) (I : Type) (V : I → P'.Opens), (∀ i, Smooth ((V i).ι ≫ q)) → Smooth ((⨆ i, V i).ι ≫ q) := by
  first | exact @GlobalTheory.Mum.smooth_iSup_comp | exact GlobalTheory.Mum.smooth_iSup_comp | (intros; apply GlobalTheory.Mum.smooth_iSup_comp <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BdLocalExt

theorem exists_extension_of_smooth {A : CommRingCat.{0}} [IsRegularRing A] {X Y : Scheme.{0}} (p : X ⟶ Spec A) [Smooth p]
    [QuasiCompact p] (u : Y ⟶ X) [IsOpenImmersion u] (L : LB Y) (hL : L.IsLB) :
    ∃ M : LB X, M.IsLB ∧ LBIso (M.pull u) L := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have h : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ UniqueFactorizationMonoid (X.presheaf.stalk x) := fun x => by
    haveI : Smooth (show X ⟶ Spec (CommRingCat.of A) from p) := ‹Smooth p›
    haveI : IsRegularRing (X.presheaf.stalk x) :=
      GlobalTheory.ExtendRig.isRegularRing_stalk GlobalTheory.isRegularRing_of_smooth A p x
    haveI : IsRegularLocalRing (X.presheaf.stalk x) := IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
    haveI : IsDomain (X.presheaf.stalk x) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
    exact ⟨inferInstance, GlobalTheory.uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
      GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      GlobalTheory.isPrincipal_map_away_of_hasProjectiveDimensionLE _⟩
  exact GlobalTheory.exists_lineBundle_extension_of_isDomain X Y u inferInstance (fun x => (h x).1) (fun x => (h x).2) L hL

theorem exists_extension_stalk {S X Y : Scheme.{0}} (g : X ⟶ S) [Smooth g] [QuasiCompact g] (e : Y ⟶ X)
    [IsOpenImmersion e] (x : S) [IsRegularLocalRing (S.presheaf.stalk x)] (L : LB Y) (hL : L.IsLB) :
    ∃ M : LB (pullback g (S.fromSpecStalk x)), M.IsLB ∧
      LBIso (M.pull (pullback.map (e ≫ g) (S.fromSpecStalk x) g (S.fromSpecStalk x) e (𝟙 _) (𝟙 _) (by simp) (by simp)))
        (L.pull (pullback.fst (e ≫ g) (S.fromSpecStalk x))) := by
  haveI : IsRegularRing (S.presheaf.stalk x) := GlobalTheory.isRegularRing_of_isRegularLocalRing _
  exact exists_extension_of_smooth (pullback.snd g (S.fromSpecStalk x)) _ _ (pull_isLB hL _)

end GlobalTheory.BdLocalExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.affineOpen_smoothScheme_isSpec_smoothAlgebra : ∀ (R : Type) [CommRing R] (Y : Over (Sp R)), Smooth Y.hom → ∀ (W : Y.left.Opens), IsAffineOpen W → ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O) (k : Sp O ⟶ Y.left) (_ : IsOpenImmersion k), k.opensRange = W ∧ k ≫ Y.hom = spMap (algebraMap R O) ∧ Algebra.Smooth R O := by
  first | exact @GlobalTheory.Mum.affineChart_smooth | exact GlobalTheory.Mum.affineChart_smooth | (intros; apply GlobalTheory.Mum.affineChart_smooth <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.surjective_open_containing_closedFibre_smooth_square : ∀ {R : Type} [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom → Surjective U.hom → ∀ (V : (U ⊗ U).left.Opens), (∀ z : (U ⊗ U).left, (U ⊗ U).hom z = closedPoint R → z ∈ V) → Surjective (V.ι ≫ (U ⊗ U).hom) := by
  first | exact @GlobalTheory.Mum.NearSurj.surjective_of_open_closedFibre | exact GlobalTheory.Mum.NearSurj.surjective_of_open_closedFibre | (intros; apply GlobalTheory.Mum.NearSurj.surjective_of_open_closedFibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_lift_residueFieldPoint_smooth_completeLocal : ∀ (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'], IsAdicComplete (maximalIdeal R') R' → ∀ (ρ : R →+* R') (U : Over (Sp R)), Smooth U.hom → ∀ (x₀ : Sp (ResidueField R') ⟶ U.left), x₀ ≫ U.hom = spMap ((residue R').comp ρ) → ∀ O : U.left.Opens, Set.range x₀ ⊆ O → ∃ a : Sp R' ⟶ U.left, a ≫ U.hom = spMap ρ ∧ Set.range a ⊆ O := by
  first | exact @GlobalTheory.HenselLift.exists_lift_mem_open | exact GlobalTheory.HenselLift.exists_lift_mem_open | (intros; apply GlobalTheory.HenselLift.exists_lift_mem_open <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_separable_point_smooth_localRing_open : ∀ (R : Type) [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom → ∀ O : U.left.Opens, (∃ u ∈ O, U.hom u = closedPoint R) → ∃ (k' : Type) (_ : Field k') (_ : Algebra (ResidueField R) k') (_ : Module.Finite (ResidueField R) k') (_ : Algebra.IsSeparable (ResidueField R) k') (x : Sp k' ⟶ U.left), x ≫ U.hom = spMap ((algebraMap (ResidueField R) k').comp (residue R)) ∧ Set.range x ⊆ O := by
  first | exact @GlobalTheory.Mum.exists_separable_point_of_smooth | exact GlobalTheory.Mum.exists_separable_point_of_smooth | (intros; apply GlobalTheory.Mum.exists_separable_point_of_smooth <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isIso_baseChange_over_basicOpen_of_tensor_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X : Over (Sp R)) (Z : Scheme.{0}) (π : Z ⟶ X.left) (s : Z ⟶ Sp R') (hX : π ≫ X.hom = s ≫ spMap (algebraMap R R')) (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (C : Subalgebra R C') (j : Sp C' ⟶ Z) (l : Sp C ⟶ X.left) [IsOpenImmersion l], IsPullback j (spMap (algebraMap C C')) π l → j ≫ s = spMap (algebraMap R' C') → l ≫ X.hom = spMap (algebraMap R C) → ∀ f g : C, (∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _)) → (∀ t : TensorProduct R C R', (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) → Algebra.Smooth R (Localization.Away g) → ∀ q : Sp C, f ∉ q.asIdeal → g ∉ q.asIdeal → ∃ V : X.left.Opens, l q ∈ V ∧ IsAffineOpen V ∧ Smooth (V.ι ≫ X.hom) ∧ IsIso (pullback.lift (π.resLE V (π ⁻¹ᵁ V) le_rfl) ((π ⁻¹ᵁ V).ι ≫ s) (by rw [Scheme.Hom.resLE_comp_ι_assoc, hX]; simp only [Category.assoc]) : (π ⁻¹ᵁ V).toScheme ⟶ pullback (V.ι ≫ X.hom) (spMap (algebraMap R R'))) := by
  first | exact @GlobalTheory.Mum.LocIso.exists_smooth_basicOpen_iso | exact GlobalTheory.Mum.LocIso.exists_smooth_basicOpen_iso | (intros; apply GlobalTheory.Mum.LocIso.exists_smooth_basicOpen_iso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.connectedSpace_pullback_of_comp_of_surjective : ∀ (X P Q Z : Scheme.{0}) (a : X ⟶ P) (b : P ⟶ Q) (g : X ⟶ Q) (ν : Z ⟶ Q), a ≫ b = g → Surjective a → ConnectedSpace (pullback g ν : Scheme.{0}) → ConnectedSpace (pullback b ν : Scheme.{0}) := by
  first | exact @GlobalTheory.connectedSpace_pullback_of_comp_surjective | exact GlobalTheory.connectedSpace_pullback_of_comp_surjective | (intros; apply GlobalTheory.connectedSpace_pullback_of_comp_surjective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.surjective_openPart_productMap_irreducible_fibres : ∀ (T : Scheme.{0}) (H V : Over T) [GrpObj H] (e : V ⟶ H), IsOpenImmersion e.left → Surjective V.hom → (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ T), IrreducibleSpace (pullback H.hom t : Scheme.{0})) → Surjective ((fst V V ≫ e) * (snd V V ≫ e)).left := by
  first | exact @GlobalTheory.Mum.surjective_mul_of_open_of_irreducible_fibres | exact GlobalTheory.Mum.surjective_mul_of_open_of_irreducible_fibres | (intros; apply GlobalTheory.Mum.surjective_mul_of_open_of_irreducible_fibres <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.glue_overlap_diagonal_top_and_cocycle : ∀ (B S X : Scheme.{0}) (π : S ⟶ B), Surjective π → ∀ (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → (∀ i, V i i = ⊤) ∧ (∀ (i j k : J) (x : (V i j).toScheme), (V i j).ι x ∈ V i k → τ i j x ∈ V j k) := by
  first | exact @GlobalTheory.Mum.glue_overlap_cocycle | exact GlobalTheory.Mum.glue_overlap_cocycle | (intros; apply GlobalTheory.Mum.glue_overlap_cocycle <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isSeparated_of_isPullback_universallyClosed_surjective' : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), UniversallyClosed π → Surjective π → ∀ (G' : Over S) (G : Over (Sp R)) (β : G'.left ⟶ G.left), IsPullback β G'.hom G.hom π → IsSeparated G'.hom → IsSeparated G.hom := by
  first | exact @GlobalTheory.isSeparated_of_isPullback_universallyClosed_surjective | exact GlobalTheory.isSeparated_of_isPullback_universallyClosed_surjective | (intros; apply GlobalTheory.isSeparated_of_isPullback_universallyClosed_surjective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.existsUnique_glue_maps_openCover_same_source : ∀ (X Y P : Scheme.{0}) (J : Type) (e : J → (P ⟶ X)) (g : J → (P ⟶ Y)), (∀ j, IsOpenImmersion (e j)) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ P), a ≫ e i = b ≫ e j → a ≫ g i = b ≫ g j) → ∃ β : X ⟶ Y, (∀ j, e j ≫ β = g j) ∧ ∀ β' : X ⟶ Y, (∀ j, e j ≫ β' = g j) → β' = β := by
  first | exact @GlobalTheory.GlueDesc.exists_unique_glue | exact GlobalTheory.GlueDesc.exists_unique_glue | (intros; apply GlobalTheory.GlueDesc.exists_unique_glue <;> assumption)
end
