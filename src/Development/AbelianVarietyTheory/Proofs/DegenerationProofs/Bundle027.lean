module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGlueFinitelyManyCompatibleSmoothModels
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfDefectZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrder
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnramifiedIdealLocusCharacterization
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle016
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle021
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle009
public import Mathlib.RingTheory.Smooth.Locus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_glue_finitely_many_compatible_smoothModels : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (n : ℕ) (M : Fin (n + 1) → Model R A), (∀ i j, Compat (M i) (M j)) → ∃ G : Model R A, (∀ i, (M i).Le G) ∧ (∀ y : G.Y.left, ∃ (i : Fin (n + 1)) (g : (M i).Y ⟶ G.Y), IsOpenImmersion g.left ∧ (M i).j ≫ g.left = G.j ∧ y ∈ Set.range g.left) ∧ ∀ N : Model R A, (∀ i, Compat N (M i)) → Compat N G := by
  first | exact @GlobalTheory.SS.GlueCompat.glue_compat | exact GlobalTheory.SS.GlueCompat.glue_compat | (intros; apply GlobalTheory.SS.GlueCompat.glue_compat <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.exists_smooth_of_defect_zero' : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), Unr π R' → Defect a π 0 → ∃ f : B, IsUnit (a f) ∧ Algebra.Smooth R (Localization.Away f) := by
  first | exact @GlobalTheory.SS.exists_smooth_of_defect_zero | exact GlobalTheory.SS.exists_smooth_of_defect_zero | (intros; apply GlobalTheory.SS.exists_smooth_of_defect_zero <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.existsUnique_modelHasJacobianOrder : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (π : R), Irreducible π → ∀ (A : Over (Sp K)) (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A), IsFrame D → ∀ M : Model R A, M.Irr → ∃! n : ℤ, HasOrd M D π n := by
  first | exact @GlobalTheory.SS.Ord.existsUnique_hasOrd | exact GlobalTheory.SS.Ord.existsUnique_hasOrd | (intros; apply GlobalTheory.SS.Ord.existsUnique_hasOrd <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelMapGenericallyOpenImmersion_calculus : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → (∀ (A : Over (Sp K)) (M N : Model R A), M.Irr → M.Le N → GenIso M N (𝟙 A)) ∧ (∀ (A A' A'' : Over (Sp K)) (M : Model R A) (N : Model R A') (P : Model R A'') (f : A ⟶ A') (g : A' ⟶ A''), N.Irr → GenIso M N f → GenIso N P g → GenIso M P (f ≫ g)) ∧ (∀ (A A' : Over (Sp K)) (M : Model R A) (N : Model R A') (f : A ≅ A'), (GenIso M N f.hom → GenIso N M f.inv) ∧ (GenIso M N f.hom ↔ GenIso (M.twist f) N (𝟙 A')) ∧ (M.Irr → (M.twist f).Irr)) ∧ (∀ (A A' B B' : Over (Sp K)) (M : Model R A) (N : Model R A') (P : Model R B) (Q : Model R B') (f : A ⟶ B) (g : A' ⟶ B'), GenIso M P f → GenIso N Q g → GenIso (M.prod N) (P.prod Q) (f ⊗ₘ g)) ∧ (∀ (A A' A'' : Over (Sp K)) (M : Model R A) (N : Model R A') (P : Model R A''), M.Irr → N.Irr → P.Irr → GenIso ((M.prod N).prod P) (M.prod (N.prod P)) (α_ A A' A'').hom ∧ GenIso (M.prod N) (N.prod M) (β_ A A').hom) := by
  first | exact @GlobalTheory.SS.GI.genIso_calculus | exact GlobalTheory.SS.GI.genIso_calculus | (intros; apply GlobalTheory.SS.GI.genIso_calculus <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

theorem _root_.GlobalTheory.T.unramified_ideal_locus_characterization : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B] (E : ∀ (R' : Type) [CommRing R'] [Algebra R R'], (B →ₐ[R] R') → Prop), (∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → Unr π R') → ∀ (I : Ideal B), (∀ b, b ∈ I ↔ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), E R' a → algebraMap R R' π ∣ a b) → ∀ (k : Type) [Field k] [Algebra R k] [Algebra k (B ⧸ I)] [IsScalarTower R k (B ⧸ I)], Function.Surjective (algebraMap R k) → Algebra.Smooth k (B ⧸ I) → Module.Free (B ⧸ I) (TensorProduct B (B ⧸ I) (KaehlerDifferential R B)) → ∃ (B' : Type) (_ : CommRing B') (_ : Algebra R B') (φ : B →ₐ[R] B'), Algebra.FiniteType R B' ∧ Module.Flat R B' ∧ Function.Injective φ ∧ (∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R') (c : ℕ), E R' a → Defect a π (c + 1) → ∃ a' : B' →ₐ[R] R', a'.comp φ = a ∧ Defect a' π c := by
  first | exact @GlobalTheory.SS.dilatation_lowers_defect | exact GlobalTheory.SS.dilatation_lowers_defect | (intros; apply GlobalTheory.SS.dilatation_lowers_defect <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.RedPts

variable {S : Scheme.{0}}

def precomp (G : Over S) [GrpObj G] {T T' : Over S} (u : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) where
  toFun x := u ≫ x
  map_one' := MonObj.comp_one u
  map_mul' x y := MonObj.comp_mul u x y

def diagSec {T : Scheme.{0}} (p : T ⟶ S) : 𝟙_ (Over T) ⟶ (Over.pullback p).obj (Over.mk p) :=
  Over.homMk (pullback.lift (𝟙 T) (𝟙 T) rfl) (pullback.lift_snd _ _ _)

def toSec (G : Over S) [GrpObj G] {T : Scheme.{0}} (p : T ⟶ S) :
    (Over.mk p ⟶ G) →* (𝟙_ (Over T) ⟶ (Over.pullback p).obj G) :=
  (precomp _ (diagSec p)).comp (Over.pullback p).homMonoidHom

theorem toSec_left_fst (G : Over S) [GrpObj G] {T : Scheme.{0}} (p : T ⟶ S) (x : Over.mk p ⟶ G) :
    (toSec G p x).left ≫ pullback.fst G.hom p = x.left := by
  have h₁ : ((Over.pullback p).map x).left ≫ pullback.fst G.hom p = pullback.fst p p ≫ x.left :=
    pullback.lift_fst _ _ _
  have h₂ : (diagSec p).left ≫ pullback.fst p p = 𝟙 T := pullback.lift_fst _ _ _
  change ((diagSec p).left ≫ ((Over.pullback p).map x).left) ≫ _ = _
  rw [Category.assoc, h₁]
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ x.left) h₂)).trans (Category.id_comp _)

theorem toSec_injective (G : Over S) [GrpObj G] {T : Scheme.{0}} (p : T ⟶ S) :
    Function.Injective (toSec G p) := fun x y h =>
  Over.OverMorphism.ext (by rw [← toSec_left_fst, h, toSec_left_fst])

theorem eq_one_of_pow_of_closedPoint (G : Over S) [GrpObj G] [IsCommMonObj G]
    [LocallyOfFiniteType G.hom] {R : Type} [CommRing R] [IsLocalRing R] (p : Sp R ⟶ S) {n : ℕ}
    (hn : IsUnit (n : R)) (x : Over.mk p ⟶ G) (hx : x ^ n = 1) {Z : Over S} (j : Z ⟶ Over.mk p)
    (hj : IsLocalRing.closedPoint R ∈ Set.range (show Z.left ⟶ Sp R from j.left)) (h : j ≫ x = 1) :
    x = 1 := by
  apply toSec_injective G p
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by simpa using hn.map (Scheme.ΓSpecIso (.of R)).inv.hom
  let G' := (Over.pullback p).obj G
  have : LocallyOfFiniteType G'.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom p))
  have := GlobalTheory.GrpTangent.formallyUnramified_mulN G' hn'
  have : LocallyOfFiniteType ((mulN G' n).left ≫ G'.hom) := by rw [Over.w]; infer_instance
  have := locallyOfFiniteType_of_comp (mulN G' n).left G'.hom
  refine Over.OverMorphism.ext (GlobalTheory.eq_of_isLocalRing_of_unramified (R := .of R) (mulN G' n).left
    (a := (toSec G p x).left) (b := (toSec G p 1).left) ?_ (show Z.left ⟶ Sp R from j.left) hj ?_)
  · have e : toSec G p x ≫ mulN G' n = toSec G p 1 ≫ mulN G' n := by
      rw [GlobalTheory.GrpTangent.comp_mulN, GlobalTheory.GrpTangent.comp_mulN, ← map_pow, ← map_pow, hx, one_pow]
    exact congrArg Over.Hom.left e
  · refine pullback.hom_ext ?_ ?_
    · have e : j ≫ x = j ≫ 1 := by rw [h, MonObj.comp_one]
      exact ((Category.assoc _ _ _).trans (congrArg (j.left ≫ ·) (toSec_left_fst G p x))).trans
        ((congrArg Over.Hom.left e).trans
          ((Category.assoc _ _ _).trans (congrArg (j.left ≫ ·) (toSec_left_fst G p 1))).symm)
    · exact ((Category.assoc _ _ _).trans (congrArg (j.left ≫ ·)
        ((Over.w (toSec G p x)).trans (Over.w (toSec G p 1)).symm))).trans (Category.assoc _ _ _).symm

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_reduction : ∀ (W R Ω : Type) [CommRing W] [CommRing R] [IsDomain R] [IsLocalRing R] [Field Ω] [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω], Function.Injective (algebraMap R Ω) → ∀ (G : Over (Sp W)) [GrpObj G], SmConn G → ∃ (H : Subgroup (Over.mk (spMap (algebraMap W Ω)) ⟶ G)) (r : H →* (𝟙_ (Over (Sp (IsLocalRing.ResidueField R))) ⟶ (Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G)), (∀ x, x ∈ H ↔ ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R Ω) ≫ s = x.left) ∧ (∀ (x : H) (s : Sp R ⟶ G.left), s ≫ G.hom = spMap (algebraMap W R) → spMap (algebraMap R Ω) ≫ s = x.1.left → (r x).left ≫ pullback.fst G.hom _ = spMap (IsLocalRing.residue R) ≫ s) ∧ ∀ (n : ℕ) (x : H), IsUnit (n : R) → x ^ n = 1 → r x = 1 → x = 1 := by
  intro W R Ω _ _ _ _ _ _ _ _ _ hj G _ hG
  obtain ⟨hc, hsm, hsep, -, -⟩ := hG
  let u : Over.mk (spMap (algebraMap W Ω)) ⟶ Over.mk (spMap (algebraMap W R)) :=
    Over.homMk (spMap (algebraMap R Ω))
      ((spMap_comp _ _).trans (congrArg spMap (IsScalarTower.algebraMap_eq W R Ω).symm))
  let v : Over.mk (spMap ((IsLocalRing.residue R).comp (algebraMap W R))) ⟶
      Over.mk (spMap (algebraMap W R)) :=
    Over.homMk (spMap (IsLocalRing.residue R)) (spMap_comp _ _)
  have hdom : IsDominant (spMap (algebraMap R Ω)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap R Ω) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hj]; exact bot_le)⟩
  have hu : Function.Injective (precomp G u) := fun a b h => Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp R) G.hom ((Over.w a).trans (Over.w b).symm)
      (spMap (algebraMap R Ω)) (congrArg Over.Hom.left h))
  let e := MonoidHom.ofInjective hu
  refine ⟨(precomp G u).range, ((toSec G _).comp (precomp G v)).comp e.symm.toMonoidHom,
    fun x => ⟨?_, ?_⟩, fun x s hs hx => ?_, fun n x hn hx hr => ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.left, Over.w s, rfl⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨Over.homMk s hs, Over.OverMorphism.ext hx⟩
  · obtain ⟨y, rfl⟩ := e.surjective x
    obtain rfl : y = Over.homMk s hs := hu (Over.OverMorphism.ext hx.symm)
    change (toSec G _ (precomp G v (e.symm (e _)))).left ≫ _ = _
    rw [e.symm_apply_apply, toSec_left_fst]
    rfl
  · obtain ⟨y, rfl⟩ := e.surjective x
    change toSec G _ (precomp G v (e.symm (e _))) = _ at hr
    rw [e.symm_apply_apply, map_eq_one_iff _ (toSec_injective G _)] at hr
    rw [← map_pow, map_eq_one_iff _ e.injective] at hx
    rw [eq_one_of_pow_of_closedPoint G _ hn y hx v
      ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩ hr, map_one]

end GlobalTheory.RedPts
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem isIrreducible_fibre_pullback {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType f]
    {k : Type} [Field k] [IsAlgClosed k] (i : Spec (.of k) ⟶ S) [IsClosedImmersion i]
    (hf : IsIrreducible (f ⁻¹' Set.range i)) (hg : IsIrreducible (g ⁻¹' Set.range i)) :
    IsIrreducible ((pullback.fst f g ≫ f) ⁻¹' Set.range i) := by
  have irr : ∀ {X : Scheme.{0}} (f : X ⟶ S), IsIrreducible (f ⁻¹' Set.range i) →
      IrreducibleSpace ↥(pullback f i) := by
    intro X f h
    rw [← Scheme.Pullback.range_fst] at h
    have e := (pullback.fst f i).isClosedEmbedding.isEmbedding
    have := Subtype.irreducibleSpace h
    exact e.toHomeomorph.irreducibleSpace_iff.2 this
  have h1 := irr f hf
  have h2 := irr g hg
  have h3 : GeometricallyIrreducible (pullback.snd f i) := geometricallyIrreducible_of_isAlgClosed _
  have h4 : IrreducibleSpace ↥(pullback (pullback.snd f i) (pullback.snd g i)) := inferInstance
  let m := pullback.map (pullback.snd f i) (pullback.snd g i) f g (pullback.fst f i) (pullback.fst g i) i
    pullback.condition.symm pullback.condition.symm
  have hm : Set.range m = (pullback.fst f g ≫ f) ⁻¹' Set.range i := by
    rw [Scheme.Pullback.range_map, Scheme.Pullback.range_fst, Scheme.Pullback.range_fst]
    ext z
    have hz : g (pullback.snd f g z) = f (pullback.fst f g z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Scheme.Hom.comp_apply, hz, and_self]
  rw [← hm, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ m.continuous.continuousOn

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem Model.j_comp_of_comm (M : Model R A) (N : Model R A') (f : A ⟶ A') (g : M.Y ⟶ N.Y)
    (h : M.e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map g = f ≫ N.e.inv) :
    M.j ≫ g.left = f.left ≫ N.j := by
  have h2 := congrArg (fun q => q.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h
  have h4 : ((Over.pullback (spMap (algebraMap R K))).map g).left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))
      = pullback.fst M.Y.hom (spMap (algebraMap R K)) ≫ g.left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc] at h2
  unfold Model.j
  rw [Category.assoc]
  exact (congrArg (fun q => M.e.inv.left ≫ q) h4).symm.trans h2

theorem Model.prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j :=
  Model.j_comp_of_comm (M.prod N) M (fst A A') (fst M.Y N.Y) (by simp [Model.prod])

theorem Model.prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j :=
  Model.j_comp_of_comm (M.prod N) N (snd A A') (snd M.Y N.Y) (by simp [Model.prod])

theorem Model.sp_eq_preimage [IsLocalRing R] (M : Model R A) :
    M.sp = M.Y.hom ⁻¹' Set.range (spMap (IsLocalRing.residue R)) := by
  have : Set.range (spMap (IsLocalRing.residue R)) = {IsLocalRing.closedPoint R} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint _)]
      exact IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩
  rw [this]; rfl

theorem Model.Irr.prod [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] {M : Model R A} {N : Model R A'}
    (hM : M.Irr) (hN : N.Irr) : (M.prod N).Irr := by
  have := M.smooth
  have : IsClosedImmersion (spMap (IsLocalRing.residue R)) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  unfold Model.Irr at *
  rw [Model.sp_eq_preimage] at *
  exact isIrreducible_fibre_pullback M.Y.hom N.Y.hom (spMap (IsLocalRing.residue R)) hM hN

theorem WeakNeron.prod [IsLocalRing R] {I I' : Type} {M : I → Model R A} {N : I' → Model R A'}
    (hM : WeakNeron M) (hN : WeakNeron N) : WeakNeron (fun p : I × I' => (M p.1).prod (N p.2)) := by
  intro R' K' _ _ _ _ _ _ _ hm a ha
  obtain ⟨i, b, hb, hb'⟩ := hM R' K' hm (a ≫ (fst A A').left) (by
    rw [Category.assoc, ← ha, ← Over.w (fst A A'), Category.assoc])
  obtain ⟨i', c, hc, hc'⟩ := hN R' K' hm (a ≫ (snd A A').left) (by
    rw [Category.assoc, ← ha, ← Over.w (snd A A'), Category.assoc])
  have e1 := Model.prod_j_fst (M i) (N i')
  have e2 := Model.prod_j_snd (M i) (N i')
  refine ⟨(i, i'), pullback.lift (f := (M i).Y.hom) (g := (N i').Y.hom) b c (hb.trans hc.symm), ?_, ?_⟩
  · exact (pullback.lift_fst_assoc _ _ _ _).trans hb
  · refine pullback.hom_ext (f := (M i).Y.hom) (g := (N i').Y.hom) ?_ ?_
    · refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
      refine (congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans (hb'.trans ?_)
      exact (Category.assoc _ _ _).trans (congrArg (a ≫ ·) e1.symm)
    · refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
      refine (congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans (hc'.trans ?_)
      exact (Category.assoc _ _ _).trans (congrArg (a ≫ ·) e2.symm)

theorem prod_irr_and_weakNeron : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' : Over (Sp K)), (∀ (M : Model R A) (N : Model R A'), M.Irr → N.Irr → (M.prod N).Irr) ∧ ∀ (I I' : Type) (M : I → Model R A) (N : I' → Model R A'), WeakNeron M → WeakNeron N → WeakNeron (fun p : I × I' => (M p.1).prod (N p.2)) := by
  intro R K _ _ _ _ _ h A A'
  have := h.2.2.1
  exact ⟨fun _ _ hM hN => hM.prod hN, fun _ _ _ _ hM hN => hM.prod hN⟩

end GlobalTheory.SS
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.quasiFiniteAt_affineSpace_homOfVector_of_coord : ∀ (C : Core) (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), IsClosed ({w} : Set C.G.toScheme) → C.Coord w W hw u → (AffineSpace.homOfVector (W.ι ≫ C.GG.hom) (fun i => W.topIso.inv.hom (u i))).QuasiFiniteAt ⟨w, hw⟩ := by
  first | exact @GlobalTheory.quasiFiniteAt_homOfVector_of_coord | exact GlobalTheory.quasiFiniteAt_homOfVector_of_coord | (intros; apply GlobalTheory.quasiFiniteAt_homOfVector_of_coord <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem appTop_pow_mul {S : Scheme.{0}} {G : Over S} (F : End G) (q m : ℕ) (f : Γ(G.left, ⊤))
    (h : (F ^ m).asHom.left.appTop.hom f = f ^ (q ^ m)) (j : ℕ) :
    (F ^ (m * j)).asHom.left.appTop.hom f = f ^ (q ^ (m * j)) := by
  induction j with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, pow_one]
    change (Scheme.Hom.appTop (𝟙 G.left)).hom f = f
    simp
  | succ j ih =>
    have e : (F ^ (m * (j + 1))).asHom.left =
        (F ^ m).asHom.left ≫ (F ^ (m * j)).asHom.left := by
      rw [Nat.mul_succ, pow_add]; rfl
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ih, map_pow, h,
      ← pow_mul, ← pow_add, Nat.mul_succ, add_comm]

theorem isAffine_splitTorus (k : Type) [Field k] (X : Type) [AddCommGroup X] :
    IsAffine (splitTorus (Sp k) X).left := by
  have : IsAffine (splitTorusAff ZU X).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Spec ZU.{0}) := inferInstance
  exact inferInstanceAs (IsAffine (pullback (splitTorusAff ZU X).hom (toZ (Sp k))))

theorem frobG_splitTorus_pow :
    ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
      (F : End (splitTorus (Sp k) X)) (q : ℕ), FrobG (splitTorus (Sp k) X) F q →
        ∃ m, 1 ≤ m ∧ ∀ l, (F ^ (m * l)).asHom = (𝟙 (splitTorus (Sp k) X)) ^ (q ^ (m * l)) := by
  intro k _ X _ _ _ F q hF
  classical
  have := isAffine_splitTorus k X
  have key : ∀ χ : X, ∃ m : ℕ, 1 ≤ m ∧
      (F ^ m).asHom.left.appTop.hom
        (charUnit (Sp k) X χ).val = (charUnit (Sp k) X χ).val ^ (q ^ m) := by
    intro χ
    obtain ⟨m, hm, h, hh⟩ := hF.2 ⊤ (isAffineOpen_top _) (charUnit (Sp k) X χ).val
    refine ⟨m, hm, ?_⟩
    rw [← hh, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  choose n0 hn1 hn using key
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  refine ⟨∏ x ∈ s, n0 x, Nat.succ_le_of_lt (Finset.prod_pos fun x _ => hn1 x), fun l => ?_⟩
  let e := splitTorusPointsEquiv (Sp k) X (splitTorus (Sp k) X)
  apply e.injective
  rw [map_pow]
  have hgen : ∀ χ ∈ s, e (F ^ ((∏ x ∈ s, n0 x) * l)).asHom (Multiplicative.ofAdd χ) =
      (e (𝟙 _) ^ (q ^ ((∏ x ∈ s, n0 x) * l))) (Multiplicative.ofAdd χ) := by
    intro χ hχ
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n0 hχ
    apply Units.ext
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, splitTorusPointsEquiv_val,
      splitTorusPointsEquiv_val, hc, Nat.mul_assoc, appTop_pow_mul F q _ _ (hn χ)]
    congr 1
  refine MonoidHom.ext fun x => ?_
  have hx : x.toAdd ∈ Submodule.span ℤ (s : Set X) := by rw [hs]; trivial
  generalize e (F ^ ((∏ x ∈ s, n0 x) * l)).asHom = a at hgen ⊢
  generalize (e (𝟙 _) ^ (q ^ ((∏ x ∈ s, n0 x) * l))) = b at hgen ⊢
  change a (Multiplicative.ofAdd x.toAdd) = b (Multiplicative.ofAdd x.toAdd)
  generalize x.toAdd = w at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add y z _ _ h1 h2 => rw [ofAdd_add, map_mul, map_mul, h1, h2]
  | smul n y _ h => rw [ofAdd_zsmul, map_zpow, map_zpow, h]

end GlobalTheory.SS
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isSmoothAt_of_smooth_mod_ideal_powers : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → ∀ (C : Type) [CommRing C] [Algebra R C] [Algebra.FiniteType R C], (∀ e : ℕ, Algebra.Smooth (R ⧸ I ^ (e + 1)) (TensorProduct R (R ⧸ I ^ (e + 1)) C)) → ∀ (q : Ideal C) [q.IsPrime], q.comap (algebraMap R C) = IsLocalRing.maximalIdeal R → Algebra.IsSmoothAt R q := by
  first | exact @GlobalTheory.SmoothAdic.isSmoothAt_of_smooth_quotient_pow | exact GlobalTheory.SmoothAdic.isSmoothAt_of_smooth_quotient_pow | (intros; apply GlobalTheory.SmoothAdic.isSmoothAt_of_smooth_quotient_pow <;> assumption)
end
