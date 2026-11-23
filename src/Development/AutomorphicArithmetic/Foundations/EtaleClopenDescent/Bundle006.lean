module

public import Development.EtaleCohomology.EtaleSheaves.Bundle069
public import Development.EtaleCohomology.EtaleSheaves.ZeroSheafMaps.EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.EtaleSheaves.Bundle074
import Development.EtaleCohomology.EtaleSheaves.Bundle004
public import Development.EtaleCohomology.EtaleSheaves.Bundle076
public import Development.EtaleCohomology.EtaleSheaves.Bundle047
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Sites.EpiMono
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits

namespace UpperTheory.Cb.HomologyEvaluation

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private theorem comp_reassoc_six {D : Type*} [Category D] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : D} (f₁ : A₀ ⟶ A₁)
    (f₂ : A₁ ⟶ A₂) (f₃ : A₂ ⟶ A₃) (f₄ : A₃ ⟶ A₄) (f₅ : A₄ ⟶ A₅) (f₆ : A₅ ⟶ A₆) :
    ((f₁ ≫ f₂ ≫ f₃ ≫ f₄) ≫ f₅) ≫ f₆ = (f₁ ≫ f₂) ≫ f₃ ≫ f₄ ≫ f₅ ≫ f₆ := by
  simp

private theorem single_homologyMap (L : CochainComplex C ℤ) (X : C) (c : X ⟶ L.cycles 0) :
    ∃ φ : (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X ⟶ L,
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).inv ≫
        HomologicalComplex.homologyMap φ 0 = c ≫ L.homologyπ 0 := by
  refine ⟨HomologicalComplex.mkHomFromSingle (c ≫ L.iCycles 0) (fun k _ => by simp), ?_⟩
  have h1 : (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).inv =
      (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 X).inv ≫
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X).homologyπ 0 := by
    rw [← cancel_mono (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom]
    simp
  rw [h1, Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  congr 1
  rw [← cancel_mono (L.iCycles 0)]
  simp

private theorem exists_cycles (K : DerivedCategory C) :
    ∃ (Z : C) (π : Z ⟶ (DerivedCategory.homologyFunctor C 0).obj K), Epi π ∧
      ∀ (X : C) (c : X ⟶ Z), ∃ x : (DerivedCategory.singleFunctor C 0).obj X ⟶ K,
        (DerivedCategory.homologyFunctor C 0).map x =
          (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app X ≫ c ≫ π := by
  obtain ⟨L, ⟨e⟩⟩ : ∃ L, Nonempty (DerivedCategory.Q.obj L ≅ K) :=
    ⟨_, ⟨(DerivedCategory.Q (C := C)).objObjPreimageIso K⟩⟩
  refine ⟨L.cycles 0, L.homologyπ 0 ≫ (DerivedCategory.homologyFunctorFactors C 0).inv.app L ≫
    (DerivedCategory.homologyFunctor C 0).map e.hom, ?_, fun X c => ?_⟩
  · have i0 : Epi (L.homologyπ 0) := inferInstance
    have i1 : IsIso ((DerivedCategory.homologyFunctorFactors C 0).inv.app L) :=
      inferInstanceAs (IsIso ((DerivedCategory.homologyFunctorFactors C 0).app L).inv)
    have i2 : Epi ((DerivedCategory.homologyFunctorFactors C 0).inv.app L ≫
        (DerivedCategory.homologyFunctor C 0).map e.hom) := epi_comp _ _
    exact @epi_comp _ _ _ _ _ _ i0 _ i2
  obtain ⟨φ, hφ⟩ := single_homologyMap L X c
  refine ⟨(DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫ DerivedCategory.Q.map φ ≫ e.hom, ?_⟩
  have h2 : (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app X =
      (DerivedCategory.homologyFunctor C 0).map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X) ≫
      (DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom := by
    have h3 : (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app X =
        (DerivedCategory.homologyFunctor C 0).map (((DerivedCategory.singleFunctorsPostcompQIso C).hom.hom 0).app X) ≫
        𝟙 _ ≫ (DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom := rfl
    have hm : (DerivedCategory.homologyFunctor C 0).map (NatTrans.app (𝟙 ((DerivedCategory.singleFunctors C).functor 0)) X) =
        (DerivedCategory.homologyFunctor C 0).map ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X) := rfl
    rw [h3, DerivedCategory.singleFunctorsPostcompQIso_hom_hom]
    erw [Category.id_comp]
    exact congrArg (fun t => t ≫ (DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom) hm
  rw [h2, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  have hφ' : HomologicalComplex.homologyMap φ 0 =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom ≫ c ≫ L.homologyπ 0 := by
    rw [← hφ, Iso.hom_inv_id_assoc]
  have n' : (DerivedCategory.homologyFunctor C 0).map (DerivedCategory.Q.map φ) =
      ((DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫ HomologicalComplex.homologyMap φ 0) ≫
        (DerivedCategory.homologyFunctorFactors C 0).inv.app L :=
    (Iso.eq_comp_inv ((DerivedCategory.homologyFunctorFactors C 0).app L)).2
      (DerivedCategory.homologyFunctorFactors_hom_naturality φ 0)
  have key : (DerivedCategory.homologyFunctor C 0).map (DerivedCategory.Q.map φ) ≫
      (DerivedCategory.homologyFunctor C 0).map e.hom =
      ((DerivedCategory.homologyFunctorFactors C 0).hom.app _ ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).hom) ≫ c ≫
        L.homologyπ 0 ≫ (DerivedCategory.homologyFunctorFactors C 0).inv.app L ≫
          (DerivedCategory.homologyFunctor C 0).map e.hom := by
    rw [n', hφ']
    exact comp_reassoc_six _ _ _ _ _ _
  simpa only [Category.assoc] using key

end UpperTheory.Cb.HomologyEvaluation

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Cb.HomologyEvaluation
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafShMapZeroPf LateralTheory.E.LeafShMapZeroPf.Gen

variable {B : Scheme.{0}} {q : ℕ}

private def ev (H : SShv B q) (U : B.Etale) :
    ((F0 B q).obj U ⟶ H) ≃ ToType (H.obj.obj (op U)) :=
  ((sheafificationAdjunction (EtTop B) (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv _ H).trans
    ((((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight B.Etaleᵒᵖ).homEquiv
      (uliftYoneda.{1}.obj U) H.obj).trans uliftYonedaEquiv)

private theorem ev_comp {H H' : SShv B q} (g : H ⟶ H') (U : B.Etale) (t : (F0 B q).obj U ⟶ H) :
    ev H' U (t ≫ g) = g.hom.app (op U) (ev H U t) := by
  have h1 := (sheafificationAdjunction (EtTop B)
    (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv_naturality_right t g
  have h2 := ((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight B.Etaleᵒᵖ).homEquiv_naturality_right
    (X := uliftYoneda.{1}.obj U) ((sheafificationAdjunction (EtTop B)
      (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv _ H t) ((sheafToPresheaf _ _).map g)
  exact (congrArg uliftYonedaEquiv ((congrArg (((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight
    B.Etaleᵒᵖ).homEquiv (uliftYoneda.{1}.obj U) H'.obj) h1).trans h2)).trans
      (uliftYonedaEquiv_comp _ _)

private theorem ev_map (H : SShv B q) {U U' : B.Etale} (a : U' ⟶ U) (t : (F0 B q).obj U ⟶ H) :
    ev H U' ((F0 B q).map a ≫ t) = H.obj.map a.op (ev H U t) := by
  have h1 := (sheafificationAdjunction (EtTop B)
    (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv_naturality_left
      (X' := ((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} (ZMod q)))).obj (uliftYoneda.{1}.obj U'))
      (X := ((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} (ZMod q)))).obj (uliftYoneda.{1}.obj U))
      (((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} (ZMod q)))).map
        (uliftYoneda.{1}.map a)) t
  have h2 := ((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight B.Etaleᵒᵖ).homEquiv_naturality_left
    (uliftYoneda.{1}.map a) ((sheafificationAdjunction (EtTop B)
      (ModuleCat.{1} (ULift.{1} (ZMod q)))).homEquiv _ H t)
  exact (congrArg uliftYonedaEquiv ((congrArg (((ModuleCat.adj (ULift.{1} (ZMod q))).whiskerRight
    B.Etaleᵒᵖ).homEquiv (uliftYoneda.{1}.obj U') H.obj) h1).trans h2)).trans
      (uliftYonedaEquiv_naturality _ a.op).symm

private theorem lift_local {Z H : SShv B q} (π : Z ⟶ H) [Epi π] (U : B.Etale) (t : (F0 B q).obj U ⟶ H) :
    Cov U (fun U' a => ∃ c : (F0 B q).obj U' ⟶ Z, c ≫ π = (F0 B q).map a ≫ t) := by
  haveI : EssentiallySmall.{1} B.Etale := inferInstance
  haveI : (EtTop B).HasSheafCompose (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) := inferInstance
  have hls : Sheaf.IsLocallySurjective π :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{1} (ULift.{1} (ZMod q))) π).2 inferInstance
  refine ⟨Presheaf.imageSieve π.hom (ev H U t),
    Presheaf.imageSieve_mem (EtTop B) π.hom (U := op U) (ev H U t), fun U' a ha => ?_⟩
  obtain ⟨z, hz⟩ := ha
  refine ⟨(ev Z U').symm z, (ev H U').injective ?_⟩
  rw [ev_comp, ev_map, Equiv.apply_symm_apply]
  exact hz

end UpperTheory.Cb.HomologyEvaluation

open UpperTheory.Cb.HomologyEvaluation LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShMapZeroPf.Gen in
theorem UpperTheory.Cb.free_etale_sheaf_lift_exists :
    LateralTheory.E.LeafShMapZeroPf.EtaleLift' := by
  intro B q K U s
  obtain ⟨Z, π, hπ, hlift⟩ := exists_cycles (C := SShv B q) K
  refine (lift_local π U ((e0 B q).inv.app U ≫ s)).mono fun U' a hc => ?_
  obtain ⟨c, hc⟩ := hc
  obtain ⟨x, hx⟩ := hlift _ c
  refine ⟨x, ?_⟩
  have he : (e0 B q).hom.app U' =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0).hom.app ((F0 B q).obj U') :=
    Category.comp_id _
  have n : (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ (e0 B q).hom.app U =
      (e0 B q).hom.app U' ≫ (F0 B q).map a := (e0 B q).hom.naturality a
  have s1 : s = (e0 B q).hom.app U ≫ (e0 B q).inv.app U ≫ s := by
    rw [Iso.hom_inv_id_app_assoc]
  have h1 : (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫ s =
      (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫
        (e0 B q).hom.app U ≫ (e0 B q).inv.app U ≫ s := by rw [← s1]
  have h2 : (DerivedCategory.homologyFunctor (SShv B q) 0).map ((OU B q).map a) ≫
      (e0 B q).hom.app U ≫ (e0 B q).inv.app U ≫ s =
      (e0 B q).hom.app U' ≫ (F0 B q).map a ≫ (e0 B q).inv.app U ≫ s := by
    rw [reassoc_of% n]
    rfl
  have h3 : (e0 B q).hom.app U' ≫ (F0 B q).map a ≫ (e0 B q).inv.app U ≫ s =
      (e0 B q).hom.app U' ≫ c ≫ π := by rw [hc]
  have h4 : (e0 B q).hom.app U' ≫ c ≫ π =
      (DerivedCategory.homologyFunctor (SShv B q) 0).map x := by
    rw [he]; exact hx.symm
  exact h1.trans (h2.trans (h3.trans h4))
end
end

section

noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace UpperTheory.Cb.ConeApexLifts

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

private def top (K : CochainComplex C ℤ) (k : ℤ) (hK : IsZero (K.X (k + 1))) :
    (singleFunctor C k).obj (K.X k) ⟶ K :=
  HomologicalComplex.mkHomFromSingle (𝟙 _) (fun j hj => by
    obtain rfl : j = k + 1 := by simpa using hj.symm
    exact hK.eq_of_tgt _ _)

private lemma top_f (K : CochainComplex C ℤ) (k : ℤ) (hK : IsZero (K.X (k + 1))) :
    (top K k hK).f k = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) k (K.X k)).hom := by
  simp only [top, HomologicalComplex.mkHomFromSingle_f, Category.comp_id]

private lemma top_comm {K L : CochainComplex C ℤ} (φ : K ⟶ L) (k : ℤ) (hK : IsZero (K.X (k + 1)))
    (hL : IsZero (L.X (k + 1))) :
    (singleFunctor C k).map (φ.f k) ≫ top L k hL = top K k hK ≫ φ := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, top_f, top_f]
  change ((HomologicalComplex.single C (ComplexShape.up ℤ) k).map (φ.f k)).f k ≫ _ = _
  simp only [HomologicalComplex.single_map_f_self, Category.assoc, Iso.cancel_iso_hom_left]
  simp

private lemma ofHom_top_comp {K I : CochainComplex C ℤ} (k : ℤ) (hK : IsZero (K.X (k + 1))) {m q : ℤ}
    (hq : k + m = q) (x : Cochain K I m) :
    (Cochain.ofHom (top K k hK)).comp x (zero_add m) = Cochain.fromSingleMk (x.v k q hq) hq := by
  ext p q' hpq
  by_cases hp : p = k
  · subst hp
    obtain rfl : q' = q := by omega
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.fromSingleMk_v, top_f]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _

private def coneTop {K L : CochainComplex C ℤ} (φ : K ⟶ L) (k : ℤ) (hK : IsZero (K.X (k + 1)))
    (hL : IsZero (L.X (k + 1))) :
    mappingCone ((singleFunctor C k).map (φ.f k)) ⟶ mappingCone φ :=
  mappingCone.map _ _ (top K k hK) (top L k hL) (top_comm φ k hK hL)

private lemma inl_coneTop {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k : ℤ) (hK : IsZero (K.X (k + 1)))
    (hL : IsZero (L.X (k + 1))) {n : ℤ} (z : Cochain (mappingCone φ) I n) :
    (mappingCone.inl ((singleFunctor C k).map (φ.f k))).comp
        ((Cochain.ofHom (coneTop φ k hK hL)).comp z (zero_add n)) (show -1 + n = n - 1 by omega) =
      Cochain.fromSingleMk (((mappingCone.inl φ).comp z (show -1 + n = n - 1 by omega)).v k (k + (n - 1)) rfl) rfl := by
  rw [← Cochain.comp_assoc_of_second_is_zero_cochain, coneTop, mappingCone.map, mappingCone.inl_desc,
    Cochain.comp_assoc_of_first_is_zero_cochain, ofHom_top_comp k hK rfl]

private lemma inr_coneTop {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k : ℤ) (hK : IsZero (K.X (k + 1)))
    (hL : IsZero (L.X (k + 1))) {n : ℤ} (z : Cochain (mappingCone φ) I n) :
    (Cochain.ofHom (mappingCone.inr ((singleFunctor C k).map (φ.f k)))).comp
        ((Cochain.ofHom (coneTop φ k hK hL)).comp z (zero_add n)) (zero_add n) =
      Cochain.fromSingleMk (((Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)).v k (k + n) rfl) rfl := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, coneTop, mappingCone.map,
    mappingCone.inr_desc, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    ofHom_top_comp k hL rfl]

open LateralTheory.E.FiltGenPf in
private lemma lift_of_top {K L I : CochainComplex C ℤ} (φ : K ⟶ L) (k n : ℤ)
    (hK : ∀ p, k < p → IsZero (K.X p)) (hL : ∀ p, k < p → IsZero (L.X p))
    (z : Cochain (mappingCone φ) I n)
    (c₀ : Cochain (mappingCone ((singleFunctor C k).map (φ.f k))) I (n - 1))
    (h : (Cochain.ofHom (coneTop φ k (hK _ (by omega)) (hL _ (by omega)))).comp z (zero_add n) =
      δ (n - 1) n c₀) :
    ∃ c : Cochain (mappingCone φ) I (n - 1), V φ (k - 1) n (z - δ (n - 1) n c) := by
  obtain ⟨a, ha⟩ := Cochain.fromSingleMk_surjective
    ((mappingCone.inl ((singleFunctor C k).map (φ.f k))).comp c₀ (show -1 + (n - 1) = n - 1 - 1 by omega))
    (k + (n - 1 - 1)) rfl
  obtain ⟨b, hb⟩ := Cochain.fromSingleMk_surjective
    ((Cochain.ofHom (mappingCone.inr ((singleFunctor C k).map (φ.f k)))).comp c₀ (zero_add (n - 1)))
    (k + (n - 1)) rfl
  have hc : δ (n - 1) n c₀ = mappingCone.descCochain ((singleFunctor C k).map (φ.f k))
      (Cochain.fromSingleMk (a ≫ I.d (k + (n - 1 - 1)) (k + (n - 1)) + n.negOnePow • (φ.f k ≫ b))
        (show k + (n - 1) = k + (n - 1) from rfl))
      (Cochain.fromSingleMk (b ≫ I.d (k + (n - 1)) (k + n)) (show k + n = k + n from rfl)) (by omega) := by
    rw [desc_eta ((singleFunctor C k).map (φ.f k)) (show n - 1 - 1 + 1 = n - 1 by omega) c₀, ← ha, ← hb]
    exact δ_desc_fromSingle k (φ.f k) (show n - 1 + 1 = n by omega) a b (by omega) rfl rfl
  have e1 := inl_coneTop φ k (hK _ (by omega)) (hL _ (by omega)) z
  rw [h, hc, mappingCone.inl_descCochain] at e1
  have e2 := inr_coneTop φ k (hK _ (by omega)) (hL _ (by omega)) z
  rw [h, hc, mappingCone.inr_descCochain] at e2
  have f1 := congrArg (Cochain.fromSingleEquiv (show k + (n - 1) = k + (n - 1) from rfl)) e1
  have f2 := congrArg (Cochain.fromSingleEquiv (show k + n = k + n from rfl)) e2
  simp only [Cochain.fromSingleEquiv_fromSingleMk] at f1 f2
  refine ⟨mappingCone.descCochain φ (Cochain.single a (n - 1 - 1)) (Cochain.single b (n - 1)) (by omega), ?_, ?_⟩
  · intro p q hpq hp
    rcases eq_or_lt_of_le (show k ≤ p by omega) with rfl | hkp
    · obtain rfl : q = k + (n - 1) := by omega
      rw [Cochain.comp_sub, δ_desc φ (by omega) (by omega), mappingCone.inl_descCochain,
        Cochain.sub_v, Cochain.add_v, Cochain.units_smul_v,
        δ_v (n - 1 - 1) (n - 1) (by omega) _ k (k + (n - 1)) hpq (k + (n - 1 - 1)) (k + 1) (by omega) rfl,
        Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
        Cochain.single_v_eq_zero a _ (k + 1) _ _ (by omega), Cochain.single_v, Cochain.single_v, ← f1]
      simp
    · exact (hK p hkp).eq_of_src _ _
  · intro p q hpq hp
    rcases eq_or_lt_of_le (show k ≤ p by omega) with rfl | hkp
    · obtain rfl : q = k + n := by omega
      rw [Cochain.comp_sub, δ_desc φ (by omega) (by omega), mappingCone.inr_descCochain,
        Cochain.sub_v,
        δ_v (n - 1) n (by omega) _ k (k + n) hpq (k + (n - 1)) (k + 1) (by omega) rfl,
        Cochain.single_v_eq_zero b _ (k + 1) _ _ (by omega), Cochain.single_v, ← f2]
      simp
    · exact (hL p hkp).eq_of_src _ _

section Host

open AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC LateralTheory.E.DiscLvlPf

variable (R : Type) [CommRing R]

private lemma pull_cone_injective {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (u : K₁ ⟶ K₂) (v : L₁ ⟶ L₂)
    [IsIso u] [IsIso v] (c : φ₁ ≫ v = u ≫ φ₂) (F : Shv R) (n : ℤ) :
    Function.Injective (HK.pull R (mappingCone.map φ₁ φ₂ u v c) F n) := by
  have c' : φ₂ ≫ inv v = inv u ≫ φ₁ := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← c, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hT : mappingCone.map φ₂ φ₁ (inv u) (inv v) c' ≫ mappingCone.map φ₁ φ₂ u v c = 𝟙 _ := by
    rw [← mappingCone.map_comp, cone_map_congr R φ₂ φ₂ _ (by rw [Category.id_comp, Category.comp_id])
      (IsIso.inv_hom_id u) (IsIso.inv_hom_id v)]
    exact mappingCone.map_id φ₂
  intro x y hxy
  have := congrArg (HK.pull R (mappingCone.map φ₂ φ₁ (inv u) (inv v) c') F n) hxy
  rwa [← pull_comp', ← pull_comp', hT, pull_id', pull_id'] at this

private def lvl {Z : PSh} {X : Spc} (a : disc.obj Z ⟶ X) : (free R).obj Z ⟶ ((chains R).obj X).X 0 :=
  (e0d R Z).inv ≫ ((chains R).map a).f 0

private lemma lvl_isIso {Z : PSh} {X : Spc} (a : disc.obj Z ⟶ X) (ha : IsIso (a.app (op ⦋0⦌))) :
    IsIso (lvl R a) := by
  have e : lvl R a ≫ (e0 R X).hom = (free R).map (a.app (op ⦋0⦌)) := by
    have := etale_discrete_chains_degree_zero_iso_free_naturality R a
    simp only [lvl, Category.assoc, this]
    exact Iso.inv_hom_id_assoc (e0d R Z) _
  have : IsIso (lvl R a ≫ (e0 R X).hom) := by rw [e]; infer_instance
  exact IsIso.of_isIso_comp_right _ (e0 R X).hom

private lemma lvl_comm {Z' Z : PSh} {X' X : Spc} (g : X' ⟶ X) (h : Z' ⟶ Z) (a : disc.obj Z ⟶ X)
    (b : disc.obj Z' ⟶ X') (comm : disc.map h ≫ a = b ≫ g) :
    (free R).map h ≫ lvl R a = lvl R b ≫ ((chains R).map g).f 0 := by
  have e : (free R).map h ≫ (e0d R Z).inv = (e0d R Z').inv ≫ ((chains R).map (disc.map h)).f 0 := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← etale_discrete_simplicial_chains_degree_zero_iso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [lvl, Category.assoc]
  rw [← Category.assoc, e, Category.assoc, ← HomologicalComplex.comp_f, ← Functor.map_comp, comm,
    Functor.map_comp, HomologicalComplex.comp_f]

private lemma sec_chains {Z : PSh} {X : Spc} (a : disc.obj Z ⟶ X) (hX : IsZero (((chains R).obj X).X (0 + 1))) :
    sec R Z ≫ (chains R).map a =
      (singleFunctor (Shv R) 0).map (lvl R a) ≫ top ((chains R).obj X) 0 hX := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, top_f]
  change _ = ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map (lvl R a)).f 0 ≫ _
  simp only [sec, HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

end Host

end UpperTheory.Cb.ConeApexLifts

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
  LateralTheory.E.LeafGhostCut LateralTheory.E.DiscLvlPf UpperTheory.Cb.ConeApexLifts in
theorem UpperTheory.Cb.simplicial_chains_degree_zero_injective :
    LateralTheory.E.t_E3Cut.Coprod → LateralTheory.E.FiltrationLevelBase.Step0 := by
  intro _ R _ F n Z' Z X' X g h a b comm ha hb z hz
  have hK : ∀ p : ℤ, 0 < p → IsZero (((chains R).obj X').X p) := LateralTheory.E.CechFiltPf.chains_isZero R X'
  have hL : ∀ p : ℤ, 0 < p → IsZero (((chains R).obj X).X p) := LateralTheory.E.CechFiltPf.chains_isZero R X
  have hK1 := hK (0 + 1) (by omega)
  have hL1 := hL (0 + 1) (by omega)
  have := lvl_isIso R a ha
  have := lvl_isIso R b hb
  have cT : (singleFunctor (Shv R) 0).map ((free R).map h) ≫ (singleFunctor (Shv R) 0).map (lvl R a) =
      (singleFunctor (Shv R) 0).map (lvl R b) ≫ (singleFunctor (Shv R) 0).map (((chains R).map g).f 0) := by
    rw [← Functor.map_comp, ← Functor.map_comp, lvl_comm R g h a b comm]
  have hsq : mappingCone.map _ _ (sec R Z') (sec R Z) (sec_comm R h) ≫ rmap R g (disc.map h) b a comm =
      mappingCone.map _ _ _ _ cT ≫ coneTop ((chains R).map g) 0 hK1 hL1 := by
    rw [rmap, coneTop, ← mappingCone.map_comp, ← mappingCone.map_comp]
    exact cone_map_congr R _ _ _ _ (sec_chains R b hK1) (sec_chains R a hL1)
  have hz' : HK.pull R (rmap R g (disc.map h) b a comm) F n (CohomologyClass.mk z) = 0 := hz
  have h1 : HK.pull R (coneTop ((chains R).map g) 0 hK1 hL1) F n (CohomologyClass.mk z) = 0 := by
    have h2 := (pull_comp' R (mappingCone.map _ _ (sec R Z') (sec R Z) (sec_comm R h))
      (rmap R g (disc.map h) b a comm) F n (CohomologyClass.mk z)).trans
        ((congrArg _ hz').trans (map_zero _))
    apply pull_cone_injective R _ _ _ _ cT F n
    rw [map_zero]
    exact (pull_comp' R _ _ F n _).symm.trans
      ((congrArg (fun t => HK.pull R t F n (CohomologyClass.mk z)) hsq.symm).trans h2)
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (coneTop ((chains R).map g) 0 hK1 hL1)) z (zero_add n)) = 0 at h1
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at h1
  obtain ⟨c₀, hc₀⟩ := h1
  obtain ⟨c, hc⟩ := lift_of_top ((chains R).map g) 0 n hK hL
    (z : Cochain (mappingCone ((chains R).map g)) (res R F) n) c₀ hc₀.symm
  have e : (0 : ℤ) - 1 = -1 := by norm_num
  rw [e] at hc
  exact ⟨c, hc⟩
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut
  LateralTheory.E.LeafDescendFPPf

namespace UpperTheory.Cb.DescentMapFactorization

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
variable {E : Scheme.{0}} (p : E ⟶ Sp R)

private def tR : LateralTheory.E.LeafDescendMapPf.D R p ⟶ (Functor.const _).obj (Sp R) where
  app S := pullback.snd _ _ ≫ incl S.unop.2.1
  naturality S T h := by
    simp only [Functor.const_obj_map, Category.comp_id]
    erw [pullback.lift_snd_assoc]
    rw [Category.assoc, LateralTheory.E.LeafDescendMapPf.incl_incl]
    exact (Category.comp_id _).symm

private lemma tR_app (S : (LateralTheory.E.LeafDescendMapPf.J R)ᵒᵖ) : (tR R p).app S =
    pullback.snd p (incl S.unop.2.1) ≫ incl S.unop.2.1 := rfl

end UpperTheory.Cb.DescentMapFactorization

open UpperTheory.Cb.DescentMapFactorization in
theorem UpperTheory.Cb.descent_map_factors_through_stage :
    LateralTheory.E.LeafPairRelPf.LeafFactorStage := by
  intro k _ Ω _ _ R hR C E Y c p w hp hs f hf a ha
  obtain ⟨h1, h2, h3⟩ := hp
  haveI : Nonempty (LateralTheory.E.LeafDescendMapPf.J R) := ⟨⟨R, le_rfl, hR⟩⟩
  haveI : ∀ S : (LateralTheory.E.LeafDescendMapPf.J R)ᵒᵖ, CompactSpace ((LateralTheory.E.LeafDescendMapPf.D R p).obj S) := by
    intro S
    dsimp only [LateralTheory.E.LeafDescendMapPf.D]
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p _)
  haveI : ∀ S : (LateralTheory.E.LeafDescendMapPf.J R)ᵒᵖ, QuasiSeparatedSpace ((LateralTheory.E.LeafDescendMapPf.D R p).obj S) := by
    intro S
    dsimp only [LateralTheory.E.LeafDescendMapPf.D]
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd p _)
  have hcomm : (LateralTheory.E.LeafDescendMapPf.cone R p c w hs).π ≫ tR R p = (Functor.const _).map (a ≫ f) := by
    ext S
    simp only [NatTrans.comp_app, Functor.const_map_app]
    rw [tR_app]
    simp only [pullback.lift_snd_assoc, Category.assoc, LateralTheory.E.LeafDescendMapPf.toR_incl]
    exact ha.symm
  obtain ⟨S, g, hg1, hg2⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (LateralTheory.E.LeafDescendMapPf.D R p) (tR R p) f (LateralTheory.E.LeafDescendMapPf.cone R p c w hs)
    (LateralTheory.E.LeafDescendMapPf.coneIsLimit R p c w hs hR) a hcomm
  exact ⟨S.unop.1, S.unop.2.1, S.unop.2.2, g, hg2, hg1⟩

end
end
