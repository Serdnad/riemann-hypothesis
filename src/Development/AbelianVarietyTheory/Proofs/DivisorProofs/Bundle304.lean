module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Scheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle196
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle194
public import Mathlib.RingTheory.RingHom.Etale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle010
public import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Shapes.Countable
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
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.AlgebraicTopology.SimplexCategory.Defs
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.NumberTheory.ModularForms.SlashActions

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_dominant_natCast_isUnit_of_nonZeroDivisor : ∀ (T : Scheme.{0}) (c : ℕ), (∀ (U : T.Opens) (f : Γ(T, U)), (c : Γ(T, U)) * f = 0 → f = 0) → ∃ (U : Scheme.{0}) (j : U ⟶ T), IsSchemeTheoreticallyDominant j ∧ IsUnit (c : Γ(U, ⊤)) := by
  first | (exact @GlobalTheory.exists_schemeTheoreticallyDominant_isUnit_natCast) | (exact GlobalTheory.exists_schemeTheoreticallyDominant_isUnit_natCast) | (intros; apply GlobalTheory.exists_schemeTheoreticallyDominant_isUnit_natCast  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.finite_coheight_one_notMem_open_genericPoint : ∀ (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (S : Set X), IsOpen S → genericPoint X ∈ S → {x : X | Order.coheight x = 1 ∧ x ∉ S}.Finite := by
  first | exact @GlobalTheory.VerticalUnit.finite_coheight_one_notMem | exact GlobalTheory.VerticalUnit.finite_coheight_one_notMem | (intros; apply GlobalTheory.VerticalUnit.finite_coheight_one_notMem <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

theorem _root_.GlobalTheory.T.ker_ne_bot_and_not_effCartier_of_two_le_dim : ∀ {W Y : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian Y] (i : W ⟶ Y) [IsClosedImmersion i], 2 ≤ ringKrullDim (Y.presheaf.stalk (i (genericPoint W))) → i.ker ≠ ⊥ ∧ ∀ U : Y.Opens, i (genericPoint W) ∈ U → ¬ FinalTheorems.EffCartier (i.ker.comap U.ι) := by
  first | exact @GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier | exact GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier | (intros; apply GlobalTheory.NotCartier.ker_ne_bot_and_not_effCartier <;> assumption)
end

section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_gluedQuotientMap_of_local_quotients : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j) (b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left)
    (G : Scheme.{0}) (F : G ⟶ S) (ψ : ∀ j, (B j).left ⟶ G),
    (∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left) →
    (∀ j k, pullback.fst _ _ ≫ ψ j = b j k ≫ ψ k) → (∀ j, ψ j ≫ F = (B j).hom ≫ 𝒰.f j) →
    ∃ Qm : A.left ⟶ G, Qm ≫ F = A.hom ∧ ∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Qm := by
  first | (exact @GlobalTheory.QuotGlue.exists_glueMap) | (exact GlobalTheory.QuotGlue.exists_glueMap) | (intros; apply GlobalTheory.QuotGlue.exists_glueMap  <;> assumption)
end

section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isPullback_gluedQuotient_kernelPair_of_cover : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H G : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A) (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) (ψ : ∀ j, (B j).left ⟶ G.left) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j),
    (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) → (∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Q.left) → (∀ j, IsPullback ((fst ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A) ≫ (Over.pullback (𝒰.f j)).map i) * snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (q j) (q j)) → IsPullback ((fst H A ≫ i) * snd H A) (snd H A) Q Q := by
  first | exact @GlobalTheory.GlueQuotPB.isPullback_translation_of_cover | exact GlobalTheory.GlueQuotPB.isPullback_translation_of_cover | (intros; apply GlobalTheory.GlueQuotPB.isPullback_translation_of_cover <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem spec_pi_cofan_isColimit : ∀ (ι : Type) [Finite ι] (T : ι → Type) [∀ i, CommRing (T i)] (B : Type) [CommRing B] (e : B ≃+* (∀ i, T i)), Nonempty (IsColimit (Cofan.mk (Spec (CommRingCat.of B)) (fun i => Spec.map (CommRingCat.ofHom ((Pi.evalRingHom T i).comp e.toRingHom))))) := by
  intro ι _ T _ B _ e
  let R : ι → CommRingCat := fun i => CommRingCat.of (T i)
  let eB : CommRingCat.of B ≅ CommRingCat.of (∀ i, T i) := e.toCommRingCatIso
  let φ : (∐ fun i => Spec (R i)) ≅ Spec (CommRingCat.of B) :=
    asIso (sigmaSpec R) ≪≫ Scheme.Spec.mapIso eB.op
  refine ⟨IsColimit.ofIsoColimit (coproductIsCoproduct _) (Cofan.ext φ ?_)⟩
  intro i
  simp only [φ, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.op_hom, Cofan.inj, Cofan.mk_ι_app]
  erw [ι_sigmaSpec_assoc]
  simp only [Scheme.Spec_map, Quiver.Hom.unop_op, ← Spec.map_comp]
  rfl

end GlobalTheory.EtC
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_local_pieces : ∀ (X : Scheme.{0}) (Z : Set X), StableUnderGeneralization Z → (∀ x ∈ Z, ∃ (W W' : X.Opens) (J : Finset Γ(X, W')), W ≤ W' ∧ x ∈ W ∧ (∀ c ∈ J, x ∉ X.basicOpen c) ∧ ∀ y ∈ W, (∀ c ∈ J, y ∉ X.basicOpen c) → y ∈ Z) → IsOpen Z := by
  first | exact @GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces | exact GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces | (intros; apply GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtaleCoverDescent


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout {R S T P : CommRingCat.{0}} {f : R ⟶ S} {g : R ⟶ T}
    {inl : S ⟶ P} {inr : T ⟶ P} (H : IsPushout f g inl inr) (x : Spec S) (y : Spec T)
    (hxy : Spec.map f x = Spec.map g y) : ∃ z : Spec P, Spec.map inl z = x := by
  have hP := isPullback_SpecMap_of_isPushout f g inl inr H
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨hP.isoPullback.inv w, ?_⟩
  rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_fst]
  exact hw

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
private lemma exists_etale_pushout_of_filtered_colimit (J : Type) [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (hc : IsColimit c) {B : CommRingCat.{0}}
    (g : c.pt ⟶ B) (hg : g.hom.Etale) :
    ∃ (j : J) (B' : CommRingCat.{0}) (a : D.obj j ⟶ B') (h : B' ⟶ B),
      a.hom.Etale ∧ IsPushout a (c.ι.app j) h g := by
  letI := g.hom.toAlgebra
  haveI : Algebra.Etale c.pt B := hg
  obtain ⟨j, A, _, _, hA, ⟨e⟩⟩ := _root_.GlobalTheory.EtaleDescent.exists_etale_model_of_isColimit J D c hc B
  letI : Algebra (D.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  refine ⟨j, CommRingCat.of A, CommRingCat.ofHom (algebraMap (D.obj j) A),
    CommRingCat.ofHom ((e : TensorProduct (D.obj j) c.pt A →+* B).comp
      Algebra.TensorProduct.includeRight.toRingHom), ?_, ?_⟩
  · exact RingHom.etale_algebraMap.mpr hA
  · refine (CommRingCat.isPushout_tensorProduct (D.obj j) c.pt A).flip.of_iso (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (RingEquiv.toCommRingCatIso e.toRingEquiv) ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · ext x
      rfl
    · ext x
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      exact e.commutes x

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
private lemma exists_etale_pushout_at_later_index_of_range {J : Type} [SmallCategory J]
    {D : J ⥤ CommRingCat.{0}} (c : Cocone D) {k k' : J} (f : k ⟶ k') {B B' : CommRingCat.{0}}
    {g : c.pt ⟶ B} {a : D.obj k ⟶ B'} {h : B' ⟶ B} (ha : a.hom.Etale)
    (H : IsPushout a (c.ι.app k) h g) :
    ∃ (B'' : CommRingCat.{0}) (a' : D.obj k' ⟶ B'') (h' : B'' ⟶ B),
      a'.hom.Etale ∧ IsPushout a' (c.ι.app k') h' g ∧
      ∀ p : Spec (D.obj k'), Spec.map (D.map f) p ∈ Set.range (Spec.map a) →
        p ∈ Set.range (Spec.map a') := by
  have hw : D.map f ≫ c.ι.app k' ≫ g = a ≫ h := by
    rw [H.w, ← c.w f, Category.assoc]
  refine ⟨pushout (D.map f) a, pushout.inl (D.map f) a,
    pushout.desc (c.ι.app k' ≫ g) h hw, ?_, ?_, ?_⟩
  · exact RingHom.Etale.isStableUnderBaseChange.pushout_inl RingHom.Etale.respectsIso _ _ ha
  · have top : IsPushout a (D.map f) (pushout.inr (D.map f) a) (pushout.inl (D.map f) a) :=
      (IsPushout.of_hasPushout (D.map f) a).flip
    have big : IsPushout a (D.map f ≫ c.ι.app k')
        (pushout.inr (D.map f) a ≫ pushout.desc (c.ι.app k' ≫ g) h hw) g := by
      rw [c.w f, pushout.inr_desc]
      exact H
    exact big.of_top (pushout.inl_desc _ _ _) top
  · rintro p ⟨v, hv⟩
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.EtaleCoverDescent.exists_point_of_isPushout (IsPushout.of_hasPushout (D.map f) a) p v hv.symm
    exact ⟨z, hz⟩


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct in
theorem _root_.GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (ι : Type) [Finite ι] (B : ι → CommRingCat.{0}) (g : ∀ i, c.pt ⟶ B i), (∀ i, (g i).hom.Etale) → (∀ p : Spec c.pt, ∃ i v, Spec.map (g i) v = p) → ∀ j₀ : J, ∃ (j : J) (_ : j₀ ⟶ j) (B' : ι → CommRingCat.{0}) (g' : ∀ i, D.obj j ⟶ B' i) (h : ∀ i, B' i ⟶ B i), (∀ i, (g' i).hom.Etale ∧ IsPushout (g' i) (c.ι.app j) (h i) (g i)) ∧ ∀ p : Spec (D.obj j), ∃ i v, Spec.map (g' i) v = p := by
  intro J _ _ D c hc ι _ B g hg hsurj j₀
  classical
  have := Fintype.ofFinite ι
  choose jm Bm am hm ham hHm using fun i => exists_etale_pushout_of_filtered_colimit J D c hc (g i) (hg i)
  let O : Finset J := insert j₀ (Finset.univ.image jm)
  let j1 := IsFiltered.sup O ∅
  have f0 : j₀ ⟶ j1 := IsFiltered.toSup O ∅ (Finset.mem_insert_self _ _)
  have fm : ∀ i, jm i ⟶ j1 := fun i =>
    IsFiltered.toSup O ∅ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  choose B1 a1 h1 ha1 hH1 _ using fun i => exists_etale_pushout_at_later_index_of_range c (fm i) (ham i) (hHm i)
  let W : Set (Spec (D.obj j1)) := {q | ∀ i, q ∉ Set.range (Spec.map (a1 i))}
  have hW : IsClosed W := by
    have hWe : W = (⋃ i, Set.range (Spec.map (a1 i)))ᶜ := by
      ext q
      simp [W]
    rw [hWe, isClosed_compl_iff]
    refine isOpen_iUnion fun i => ?_
    have : Etale (Spec.map (a1 i)) := by
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      exact ha1 i
    exact (Spec.map (a1 i)).isOpenMap.isOpen_range
  have claim : ∃ (k : J) (f : j1 ⟶ k), ∀ p : Spec (D.obj k), Spec.map (D.map f) p ∉ W := by
    by_contra hcon
    push_neg at hcon
    haveI : ∀ {i i' : Jᵒᵖ} (f : i ⟶ i'), IsAffineHom ((D.op ⋙ Scheme.Spec).map f) :=
      fun f => inferInstanceAs (IsAffineHom (Spec.map (D.map f.unop)))
    obtain ⟨s, hs⟩ := exists_mem_of_isClosed_of_nonempty' (D.op ⋙ Scheme.Spec)
      (Scheme.Spec.mapCone c.op) (isLimitOfPreserves Scheme.Spec hc.op) (j := op j1)
      (fun i hij => (Spec.map (D.map hij.unop)) ⁻¹' W)
      (fun i hij => hW.preimage (Spec.map _).continuous)
      (fun i hij => hcon _ hij.unop)
      (fun i hij => (hW.preimage (Spec.map _).continuous).isCompact)
      (fun i i' hi'i hij x hx => by
        change Spec.map (D.map hij.unop) (Spec.map (D.map hi'i.unop) x) ∈ W
        rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, ← D.map_comp]
        exact hx)
    have hs1 : Spec.map (c.ι.app j1) s ∈ W := by
      have := hs (op j1) (𝟙 _)
      change Spec.map (D.map (𝟙 j1)) (Spec.map (c.ι.app j1) s) ∈ W at this
      simpa [D.map_id, Spec.map_id] using this
    obtain ⟨i, v, rfl⟩ := hsurj s
    refine hs1 i ⟨Spec.map (h1 i) v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, (hH1 i).w, Spec.map_comp, Scheme.Hom.comp_apply]
  obtain ⟨k, f, hk⟩ := claim
  choose B2 a2 h2 ha2 hH2 hpt using fun i => exists_etale_pushout_at_later_index_of_range c f (ha1 i) (hH1 i)
  refine ⟨k, f0 ≫ f, B2, a2, h2, fun i => ⟨ha2 i, hH2 i⟩, fun p => ?_⟩
  have hp := hk p
  simp only [W, Set.mem_setOf_eq, not_forall, not_not] at hp
  obtain ⟨i, hi⟩ := hp
  obtain ⟨v, hv⟩ := hpt i p hi
  exact ⟨i, v, hv⟩

end GlobalTheory.EtaleCoverDescent
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem locallyConstant_spec_local_eq_closedPoint {R A : Type} [CommRing A] [IsLocalRing A]
    (f : LocallyConstant (Spec (CommRingCat.of A)) R) (x : Spec (CommRingCat.of A)) :
    f x = f (IsLocalRing.closedPoint A : PrimeSpectrum A) := by
  have hx : (x : PrimeSpectrum A) ⤳ IsLocalRing.closedPoint A :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (x : PrimeSpectrum A).isPrime.ne_top)
  have ho : IsOpen (f ⁻¹' {f (IsLocalRing.closedPoint A : PrimeSpectrum A)}) := f.isLocallyConstant _
  exact hx.mem_open ho rfl

theorem locallyConstant_spec_local_bijective :
    ∀ (R : Type) (A : Type) [CommRing A] [IsLocalRing A],
      Function.Bijective (fun c : R => LocallyConstant.const (Spec (CommRingCat.of A)) c) := by
  intro R A _ _
  refine ⟨fun c d h => ?_, fun f => ⟨f (IsLocalRing.closedPoint A : PrimeSpectrum A), ?_⟩⟩
  · have := congrArg (fun g : LocallyConstant (Spec (CommRingCat.of A)) R =>
      g (IsLocalRing.closedPoint A : PrimeSpectrum A)) h
    exact this
  · ext x
    simp only [LocallyConstant.coe_const, Function.const_apply]
    exact (locallyConstant_spec_local_eq_closedPoint f x).symm

end GlobalTheory
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem etale_mem_iff_points : ∀ (U : Scheme.{0}) (S : Sieve U), S ∈ Scheme.etaleTopology.{0} U ↔
    ∀ u : U, ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), Etale j ∧ j v = u ∧ S.arrows j := by
  intro U S
  constructor
  · intro hS u
    obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
    obtain ⟨i, v, hv⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 u
    exact ⟨𝒰.X i, 𝒰.f i, v, 𝒰.map_prop i, hv, hle _ _ (Presieve.ofArrows.mk i)⟩
  · intro h
    choose V j v hj hv hS using h
    refine (Scheme.mem_grothendieckTopology_iff (P := @Etale)).2
      ⟨Scheme.Cover.mkOfCovers U V j (fun u => ⟨u, v u, hv u⟩) hj, ?_⟩
    intro W f hf
    obtain ⟨u⟩ := hf
    exact hS u

end GlobalTheory
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory

theorem isCompact_pi_upperHalfPlane_im_bounds :
    ∀ (ι : Type) [Fintype ι] (L : Set (ι → ℂ)), IsCompact L → (∀ z ∈ L, ∀ i, 0 < (z i).im) →
    ∃ c c' : ℝ, 0 < c ∧ ∀ z ∈ L, ∀ i, c ≤ (z i).im ∧ (z i).im ≤ c' := by
  intro ι _ L hL hpos
  obtain ⟨C, hC⟩ := hL.isBounded.exists_norm_le
  have hup : ∀ z ∈ L, ∀ i, (z i).im ≤ C := fun z hz i =>
    (Complex.im_le_norm (z i)).trans ((norm_le_pi_norm z i).trans (hC z hz))
  rcases L.eq_empty_or_nonempty with hE | hne
  · exact ⟨1, 0, one_pos, by simp [hE]⟩
  have hm : ∀ i, ∃ m : ℝ, 0 < m ∧ ∀ z ∈ L, m ≤ (z i).im := by
    intro i
    have hc : Continuous fun z : ι → ℂ => (z i).im :=
      Complex.continuous_im.comp (continuous_apply i)
    obtain ⟨x, hx, hmin⟩ := hL.exists_isMinOn hne hc.continuousOn
    exact ⟨(x i).im, hpos x hx i, fun z hz => hmin hz⟩
  choose m hm0 hmle using hm
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, C, one_pos, fun z _ i => isEmptyElim i⟩
  refine ⟨Finset.univ.inf' Finset.univ_nonempty m, C, ?_, fun z hz i => ⟨?_, hup z hz i⟩⟩
  · exact (Finset.lt_inf'_iff _).2 fun i _ => hm0 i
  · exact (Finset.inf'_le _ (Finset.mem_univ i)).trans (hmle i z hz)

end GlobalTheory
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem summable_lambert_prod (e : ℕ) (Q : ℂ) (c : ℕ → ℕ → ℂ) (hQ : ‖Q‖ < 1)
    (hc : ∀ d m, ‖c d m‖ ≤ 1) :
    Summable fun x : ℕ+ × ℕ+ =>
      ((x.2 : ℕ) : ℂ) ^ e * c x.1 x.2 * Q ^ ((x.1 : ℕ) * (x.2 : ℕ)) := by
  have h := summable_prod_mul_pow (𝕜 := ℝ) e (r := ‖Q‖) (by simpa using hQ)
  refine Summable.of_norm_bounded h fun x => ?_
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  gcongr
  calc ((x.2 : ℕ) : ℝ) ^ e * ‖c x.1 x.2‖ ≤ ((x.2 : ℕ) : ℝ) ^ e * 1 := by
        gcongr; exact hc _ _
    _ = _ := mul_one _

theorem hasSum_lambert : ∀ (e : ℕ) (Q : ℂ) (c : ℕ → ℕ → ℂ), ‖Q‖ < 1 → (∀ d m, ‖c d m‖ ≤ 1) → HasSum (fun k : ℕ => (∑ m ∈ k.divisors, (m : ℂ) ^ e * c (k / m) m) * Q ^ k) (∑' d : ℕ+, ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c d m * Q ^ ((d : ℕ) * (m : ℕ))) := by
  intro e Q c hQ hc
  have hs := summable_lambert_prod e Q c hQ hc
  rw [← hs.tsum_prod]
  have h1 := sigmaAntidiagonalEquivProd.hasSum_iff.mpr hs.hasSum
  have h2 := h1.sigma (fun n => hasSum_fintype _)
  refine (Function.Injective.hasSum_iff (g := PNat.val) PNat.coe_injective ?_).mp ?_
  · intro k hk
    have : k = 0 := by
      by_contra h
      exact hk ⟨⟨k, Nat.pos_of_ne_zero h⟩, rfl⟩
    simp [this]
  · refine HasSum.congr_fun h2 fun n => ?_
    symm
    have h3 : ∀ x : Nat.divisorsAntidiagonal (n : ℕ),
        ((fun x : ℕ+ × ℕ+ => ((x.2 : ℕ) : ℂ) ^ e * c x.1 x.2 * Q ^ ((x.1 : ℕ) * (x.2 : ℕ))) ∘
          sigmaAntidiagonalEquivProd) ⟨n, x⟩ =
        (fun y : ℕ × ℕ => (y.2 : ℂ) ^ e * c y.1 y.2 * Q ^ (y.1 * y.2)) x.1 := fun x => rfl
    rw [Finset.sum_congr rfl (fun x _ => h3 x),
      Finset.sum_coe_sort (Nat.divisorsAntidiagonal (n : ℕ))
        (fun y : ℕ × ℕ => (y.2 : ℂ) ^ e * c y.1 y.2 * Q ^ (y.1 * y.2)),
      Nat.sum_divisorsAntidiagonal' (fun a b : ℕ => (b : ℂ) ^ e * c a b * Q ^ (a * b))]
    simp only [Function.comp_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m hm => by
      rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hm)]

end GlobalTheory.WpFam
end
