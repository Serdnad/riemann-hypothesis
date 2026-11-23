module

public import Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.EtSpreadsOf
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Development.EtaleCohomology.EtaleSheaves.LeafSpreadSmoothPf
public import Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism.LeafSheafIsoOf
public import Development.EtaleCohomology.EtaleSheaves.ZeroSheafMaps.EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.EtaleCohomology.EtaleSheaves.Bundle046
import Development.EtaleCohomology.EtaleSheaves.PropertyDescent.BaseChange

@[expose] public section

section

noncomputable section
open CategoryTheory Limits TensorProduct

namespace LateralTheory.E.EtStagePf

theorem exists_model {A T : CommRingCat.{0}} (f : A ⟶ T) (hf : f.hom.Etale) :
    ∃ (A₀ B₀ : CommRingCat.{0}) (a : A₀ ⟶ A) (f₀ : A₀ ⟶ B₀) (b : B₀ ⟶ T),
      (Int.castRingHom A₀).FinitePresentation ∧ f₀.hom.Etale ∧ IsPushout a f₀ f b := by
  let _ := f.hom.toAlgebra
  have h : Algebra.Etale A T := hf
  obtain ⟨A₀, B₀, _, _, hfg, het, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg ℤ A T
  have hft : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hfg
  have hfp : Algebra.FinitePresentation ℤ A₀ := Algebra.FinitePresentation.of_finiteType.mp hft
  refine ⟨CommRingCat.of A₀, CommRingCat.of B₀, CommRingCat.ofHom (algebraMap A₀ A),
    CommRingCat.ofHom (algebraMap A₀ B₀),
    CommRingCat.ofHom (e.symm.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom), ?_, ?_, ?_⟩
  · have := RingHom.finitePresentation_algebraMap.mpr hfp
    rwa [RingHom.ext_int (algebraMap ℤ A₀) (Int.castRingHom A₀)] at this
  · exact RingHom.etale_algebraMap.mpr het
  · refine (CommRingCat.isPushout_tensorProduct A₀ A B₀).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      e.symm.toRingEquiv.toCommRingCatIso (by simp) (by simp) ?_ ?_
    · ext x
      exact e.symm.commutes x
    · ext x
      rfl

theorem EtStage_of : LateralTheory.E.SpreadPf.Cut.EtStage := by
  intro J _ _ D c hc _ _ T _ f _ _ _ hf
  obtain ⟨A₀, B₀, a, f₀, b, hfp, het, hP⟩ := exists_model f hf
  let α : (Functor.const J).obj (CommRingCat.of ℤ) ⟶ D :=
    { app := fun i => CommRingCat.ofHom (Int.castRingHom _)
      naturality := fun _ _ _ => CommRingCat.hom_ext (RingHom.ext_int _ _) }
  obtain ⟨k, a', -, ha⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit (CommRingCat.of ℤ) D α
    (CommRingCat.ofHom (Int.castRingHom A₀)) c hc hfp a
    (fun _ => CommRingCat.hom_ext (RingHom.ext_int _ _))
  subst ha
  have hQ := IsPushout.of_hasPushout a' f₀
  have hw : a' ≫ c.ι.app k ≫ f = f₀ ≫ b := by rw [← hP.w, Category.assoc]
  refine ⟨k, pushout a' f₀, pushout.inl a' f₀, pushout.desc (c.ι.app k ≫ f) b hw, ?_, ?_⟩
  · refine IsPushout.of_left ?_ (pushout.inl_desc _ _ _).symm hQ
    rw [pushout.inr_desc]
    exact hP
  · have := (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff (P := @RingHom.Etale)).mpr
      RingHom.Etale.isStableUnderBaseChange
    exact this.of_isPushout hQ het

end LateralTheory.E.EtStagePf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendChainPf
  LateralTheory.E.LeafPropsDescendPf LateralTheory.E.LeafPropsDescendPf.Split LateralTheory.E.LeafSpreadSmoothPf

namespace LateralTheory.E.LeafSpreadRelDimPf

def LeafRelDimAtImage : Prop := ∀ (k : Type) [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω),
    R.FG → ∀ {C D : Scheme.{0}} (c : C ⟶ Sp Ω) (q : D ⟶ Sp R) (v : C ⟶ D), IsAffine D →
    LocallyOfFinitePresentation q → Smooth q → SmoothOfRelativeDimension 1 c →
    IsPullback v c q (toR R) →
    ∀ y : C, ∃ V : D.Opens, v y ∈ V ∧ SmoothOfRelativeDimension 1 (V.ι ≫ q)

def LeafGenericOpenSpread : Prop := ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] (D : Scheme.{0}) (q : D ⟶ Sp A),
    IsAffine D → LocallyOfFinitePresentation q → ∀ U : D.Opens,
    (∀ x : D, (show PrimeSpectrum A from q x).asIdeal = ⊥ → x ∈ U) →
    ∃ f : A, f ≠ 0 ∧ ∀ x : D, f ∉ (show PrimeSpectrum A from q x).asIdeal → x ∈ U

theorem generic_pt {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω) (ω : Sp Ω) :
    (show PrimeSpectrum R from toR R ω).asIdeal = ⊥ := by
  have h0 : (show PrimeSpectrum Ω from ω).asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  change Ideal.comap (algebraMap R Ω) (show PrimeSpectrum Ω from ω).asIdeal = ⊥
  rw [h0]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R Ω)

theorem LeafSpreadRelDim_of_sub (hA : LeafRelDimAtImage) (hB : LeafGenericOpenSpread) : LeafSpreadRelDim := by
  intro k _ Ω _ _ R hR C D c q v hD hlfp hsm hs hv
  let U : D.Opens := sSup {V : D.Opens | SmoothOfRelativeDimension 1 (V.ι ≫ q)}
  have hU : ∀ x : D, (show PrimeSpectrum R from q x).asIdeal = ⊥ → x ∈ U := by
    intro x hx
    let ω : Sp Ω := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)
    have he : q x = toR R ω := PrimeSpectrum.ext (hx.trans (generic_pt R ω).symm)
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x ω he
    obtain ⟨V, hV, hVs⟩ := hA k Ω R hR c q v hD hlfp hsm hs hv (hv.isoPullback.inv z)
    have : v (hv.isoPullback.inv z) = x := by
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz1]
    rw [this] at hV
    exact TopologicalSpace.Opens.mem_sSup.mpr ⟨V, hVs, hV⟩
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).mp hR
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  obtain ⟨f, hf0, hf⟩ := hB R D q hD hlfp U hU
  have hf0' : (f : Ω) ≠ 0 := fun h => hf0 (Subtype.ext h)
  let T : Subalgebra k Ω := Algebra.adjoin k ((({((f : Ω))⁻¹} : Finset Ω)) : Set Ω)
  refine ⟨R ⊔ T, le_sup_left, hR.sup (Subalgebra.fg_adjoin_finset _), ?_⟩
  intro R' hR' hRR E q' r hE
  have hinv : ((f : Ω))⁻¹ ∈ R' :=
    hR' (le_sup_right (a := R) (Algebra.subset_adjoin (by simp)))
  have hunit : IsUnit (Subalgebra.inclusion hRR f) := by
    have h1 : Subalgebra.inclusion hRR f * (⟨_, hinv⟩ : R') = 1 := Subtype.ext (mul_inv_cancel₀ hf0')
    exact isUnit_iff_exists_inv.mpr ⟨_, h1⟩
  have hL : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} 1) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1))
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)
    (fun V : {V : D.Opens // SmoothOfRelativeDimension 1 (V.ι ≫ q)} => r ⁻¹ᵁ V.1) ?_ ?_
  · refine top_le_iff.mp fun e _ => ?_
    have hq : q (r e) = incl hRR (q' e) := by
      rw [← Scheme.Hom.comp_apply, hE.w, Scheme.Hom.comp_apply]
    have hx : f ∉ (show PrimeSpectrum R from q (r e)).asIdeal := by
      rw [hq]
      change Subalgebra.inclusion hRR f ∉ (show PrimeSpectrum R' from q' e).asIdeal
      exact fun h => (show PrimeSpectrum R' from q' e).isPrime.ne_top
        (Ideal.eq_top_of_isUnit_mem _ h hunit)
    obtain ⟨V, hVs, hV⟩ := TopologicalSpace.Opens.mem_sSup.mp (hf (r e) hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVs⟩, hV⟩
  · intro V
    have h2 := (isPullback_morphismRestrict r V.1).paste_vert hE
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback h2 V.2

end LateralTheory.E.LeafSpreadRelDimPf

namespace LateralTheory.E.LeafSpreadRelDimPf.Spread
open Topology TopologicalSpace

theorem exists_ne_zero_of_constructible {A : Type} [CommRing A] [IsDomain A] (T : Set (PrimeSpectrum A))
    (hT : IsConstructible T) (h : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∉ T) :
    ∃ f : A, f ≠ 0 ∧ ∀ p ∈ T, f ∈ p.asIdeal := by
  revert h
  induction T, hT using IsConstructible.induction_of_isTopologicalBasis
    (fun f : A => (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)))
    PrimeSpectrum.isTopologicalBasis_basic_opens (fun f => PrimeSpectrum.isCompact_basicOpen f) with
  | sdiff g s hs =>
    intro h
    by_cases hg : g = 0
    · refine ⟨1, one_ne_zero, fun p hp => ?_⟩
      have := hp.1
      simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, hg] at this
      exact absurd p.asIdeal.zero_mem this
    · have hη : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) := by
        simpa [PrimeSpectrum.mem_basicOpen] using hg
      have : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ ⋃ j ∈ s, (PrimeSpectrum.basicOpen j : Set (PrimeSpectrum A)) := by
        by_contra hn; exact h ⟨hη, hn⟩
      obtain ⟨j, hj, hηj⟩ := Set.mem_iUnion₂.mp this
      have hj0 : j ≠ 0 := by simpa [PrimeSpectrum.mem_basicOpen] using hηj
      refine ⟨j, hj0, fun p hp => ?_⟩
      have h2 := hp.2
      by_contra hn
      exact h2 (Set.mem_iUnion₂.mpr ⟨j, hj, by simpa [PrimeSpectrum.mem_basicOpen] using hn⟩)
  | union s hs t ht ihs iht =>
    intro h
    obtain ⟨f1, h1, hf1⟩ := ihs (fun hh => h (Or.inl hh))
    obtain ⟨f2, h2, hf2⟩ := iht (fun hh => h (Or.inr hh))
    refine ⟨f1 * f2, mul_ne_zero h1 h2, fun p hp => ?_⟩
    rcases hp with hp | hp
    · exact Ideal.mul_mem_right _ _ (hf1 p hp)
    · exact Ideal.mul_mem_left _ _ (hf2 p hp)

theorem LeafGenericOpenSpread_pf : LeafGenericOpenSpread := by
  intro A _ _ _ D q hD hlfp U hU
  have : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian D := {}
  have hZ : IsConstructible ((U : Set D)ᶜ) :=
    ((NoetherianSpace.isCompact (U : Set D)).isConstructible U.isOpen).compl
  have : QuasiCompact q := inferInstance
  have hI := q.isConstructible_image hZ
  obtain ⟨f, hf0, hf⟩ := exists_ne_zero_of_constructible (A := A) (q '' ((U : Set D)ᶜ)) hI (by
    rintro ⟨x, hx, hqx⟩
    exact hx (hU x (by rw [hqx])))
  refine ⟨f, hf0, fun x hx => ?_⟩
  by_contra hxU
  exact hx (hf (q x) ⟨x, hxU, rfl⟩)

end LateralTheory.E.LeafSpreadRelDimPf.Spread

namespace LateralTheory.E.LeafSpreadRelDimPf

theorem LeafRelDimAtImage_pf : LeafRelDimAtImage := by
  intro k _ Ω _ _ R hR C D c q v hD hlfp hsm hs hv y
  obtain ⟨n, W, hW, hWs⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim q (v y)
  have := ReciprocityTheory.ChartRestriction.G.H1.dim_base hv hWs hs y hW
  subst this
  exact ⟨W, hW, hWs⟩

theorem LeafSpreadRelDim_of : LeafSpreadRelDim :=
  LeafSpreadRelDim_of_sub LeafRelDimAtImage_pf Spread.LeafGenericOpenSpread_pf

end LateralTheory.E.LeafSpreadRelDimPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LeafSecRepPf
open LateralTheory.E.LeafDegCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafShIsoPf LateralTheory.E.LeafShIsoPf.Sh

section General
universe u
variable {C : Type u} [Category.{0} C] (R : Type 1) [Ring R]

def FP : C ⥤ (Cᵒᵖ ⥤ ModuleCat.{1} R) :=
  yoneda ⋙ (Functor.whiskeringRight Cᵒᵖ (Type 0) (ModuleCat.{1} R)).obj
    (uliftFunctor.{1, 0} ⋙ ModuleCat.free R)

def gen {U V : C} (a : V ⟶ U) : ((FP R).obj U).obj (op V) :=
  ModuleCat.freeMk (R := R) (X := ULift.{1} (V ⟶ U)) (ULift.up a)

theorem map_gen {U V W : C} (a : V ⟶ U) (b : W ⟶ V) :
    ((FP R).obj U).map b.op (gen R a) = gen R (b ≫ a) :=
  ModuleCat.free_map_apply (R := R) _ _

theorem app_gen {U U' V : C} (a : V ⟶ U') (b : U' ⟶ U) :
    ((FP R).map b).app (op V) (gen R a) = gen R (a ≫ b) :=
  ModuleCat.free_map_apply (R := R) _ _

theorem freePresheaf_hom_ext {U V : C} {M : ModuleCat.{1} R} {f g : ((FP R).obj U).obj (op V) ⟶ M}
    (h : ∀ a : V ⟶ U, f (gen R a) = g (gen R a)) : f = g :=
  ModuleCat.free_hom_ext (R := R) (X := ULift.{1} (V ⟶ U)) (fun x => h x.down)

def desc (G : Cᵒᵖ ⥤ ModuleCat.{1} R) (U : C) (s : G.obj (op U)) (V : C) :
    ((FP R).obj U).obj (op V) ⟶ G.obj (op V) :=
  ModuleCat.freeDesc (R := R) (X := ULift.{1} (V ⟶ U)) (↾fun x => G.map x.down.op s)

theorem desc_gen (G : Cᵒᵖ ⥤ ModuleCat.{1} R) (U : C) (s : G.obj (op U)) {V : C} (a : V ⟶ U) :
    desc R G U s V (gen R a) = G.map a.op s :=
  ModuleCat.freeDesc_apply (R := R) _ _

theorem nat_gen {G : Cᵒᵖ ⥤ ModuleCat.{1} R} {U V : C} (η : (FP R).obj U ⟶ G) (a : V ⟶ U) :
    η.app (op V) (gen R a) = G.map a.op (η.app (op U) (gen R (𝟙 U))) := by
  have h := ConcreteCategory.congr_hom (η.naturality a.op) (gen R (𝟙 U))
  simp only [ConcreteCategory.comp_apply] at h
  rw [map_gen, Category.comp_id] at h
  exact h

def yE (G : Cᵒᵖ ⥤ ModuleCat.{1} R) (U : C) : ((FP R).obj U ⟶ G) ≃ G.obj (op U) where
  toFun η := η.app (op U) (gen R (𝟙 U))
  invFun s :=
    { app := fun V => desc R G U s V.unop
      naturality := by
        rintro ⟨V⟩ ⟨W⟩ ⟨b⟩
        apply freePresheaf_hom_ext
        intro a
        simp only [ConcreteCategory.comp_apply]
        have h := map_gen R a b
        erw [h, desc_gen, desc_gen]
        rw [op_comp, G.map_comp, ConcreteCategory.comp_apply]
        rfl }
  left_inv η := by
    ext1
    funext ⟨V⟩
    apply freePresheaf_hom_ext
    intro a
    exact (desc_gen R G U _ a).trans (nat_gen R η a).symm
  right_inv s := by
    refine (desc_gen R G U s (𝟙 U)).trans ?_
    simp

theorem yE_res {G : Cᵒᵖ ⥤ ModuleCat.{1} R} {U U' : C} (a : U' ⟶ U) (η : (FP R).obj U ⟶ G) :
    yE R G U' ((FP R).map a ≫ η) = G.map a.op (yE R G U η) := by
  change η.app (op U') (((FP R).map a).app (op U') (gen R (𝟙 U'))) = _
  rw [app_gen, Category.id_comp]
  exact nat_gen R η a

theorem yE_sub {G : Cᵒᵖ ⥤ ModuleCat.{1} R} (U : C) (η η' : (FP R).obj U ⟶ G) :
    yE R G U (η - η') = yE R G U η - yE R G U η' := rfl

variable (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{1} R)]

theorem general (T : C ⥤ Sheaf J (ModuleCat.{1} R)) (i : FP R ⋙ presheafToSheaf J _ ≅ T) :
    ∃ e : ∀ (F : Sheaf J (ModuleCat.{1} R)) (U : C), (T.obj U ⟶ F) ≃ F.obj.obj (op U),
  (∀ (F G : Sheaf J (ModuleCat.{1} R)) (g : F ⟶ G) (U : C) (t : T.obj U ⟶ F),
    e G U (t ≫ g) = g.hom.app (op U) (e F U t)) ∧
  (∀ (F : Sheaf J (ModuleCat.{1} R)) (U U' : C) (a : U' ⟶ U) (t : T.obj U ⟶ F),
    e F U' (T.map a ≫ t) = F.obj.map a.op (e F U t)) ∧
  (∀ (F : Sheaf J (ModuleCat.{1} R)) (U : C) (t t' : T.obj U ⟶ F), e F U (t - t') = e F U t - e F U t') := by
  let adj := sheafificationAdjunction J (ModuleCat.{1} R)
  refine ⟨fun F U => ((Iso.homCongr (i.app U).symm (Iso.refl F)).trans
    (adj.homEquiv ((FP R).obj U) F)).trans (yE R F.obj U), ?_, ?_, ?_⟩
  · intro F G g U t
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
    rfl
  · intro F U U' a t
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    have h : (i.app U').hom ≫ T.map a ≫ t =
        (presheafToSheaf J _).map ((FP R).map a) ≫ (i.app U).hom ≫ t := by
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      exact (i.hom.naturality a).symm
    rw [h]
    erw [Adjunction.homEquiv_naturality_left]
    exact yE_res R a _
  · intro F U t t'
    simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [Preadditive.comp_sub, ← yE_sub]
    congr 1

end General

theorem LeafSecRep_of : LeafSecRep := by
  intro B q
  let i : FP (C := B.Etale) (ULift.{1} (ZMod q)) ⋙ presheafToSheaf (EtTop B) _ ≅ OU B q ⋙ H0 B q :=
    (Functor.isoWhiskerLeft (FP (C := B.Etale) (ULift.{1} (ZMod q)) ⋙ presheafToSheaf (EtTop B) _)
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (SShv B q) 0)).symm
  exact general (ULift.{1} (ZMod q)) (EtTop B) (OU B q ⋙ H0 B q) i

end LateralTheory.E.LeafSecRepPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.DegreeZeroGenerators
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafShMapZeroPf LateralTheory.E.LeafShMapZeroPf.Gen

abbrev Rq (q : ℕ) := ULift.{1} (ZMod q)

abbrev Gq (q : ℕ) : Type 0 ⥤ ModuleCat.{1} (Rq q) := uliftFunctor.{1, 0} ⋙ ModuleCat.free (Rq q)

abbrev P0 (B : Scheme.{0}) (q : ℕ) (U : B.Etale) : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (Rq q) :=
  ((Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (Rq q))).obj (Gq q)).obj (yoneda.obj U)

def gen {B : Scheme.{0}} {q : ℕ} (U : B.Etale) : ((F0 B q).obj U).obj.obj (op U) :=
  (toSheafify (EtTop B) (P0 B q U)).app (op U) (ModuleCat.freeMk (ULift.up (𝟙 U)))

theorem gen_nat {B : Scheme.{0}} {q : ℕ} {U U' : B.Etale} (a : U' ⟶ U) :
    ((F0 B q).map a).hom.app (op U') (gen U') = ((F0 B q).obj U).obj.map a.op (gen U) := by
  have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality (EtTop B)
    (((Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (Rq q))).obj (Gq q)).map (yoneda.map a))) (op U'))
    (ModuleCat.freeMk (ULift.up (𝟙 U')))
  have h2 := ConcreteCategory.congr_hom ((toSheafify (EtTop B) (P0 B q U)).naturality a.op)
    (ModuleCat.freeMk (ULift.up (𝟙 U)))
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h1 h2
  unfold gen
  refine Eq.trans ?_ (h1.symm.trans ?_)
  · rfl
  · refine Eq.trans ?_ h2
    congr 1
    simp only [Gq, Functor.comp_map]
    erw [ModuleCat.free_map_apply, ModuleCat.free_map_apply]
    show ModuleCat.freeMk (ULift.up (𝟙 U' ≫ a)) = ModuleCat.freeMk (ULift.up (a ≫ 𝟙 U))
    simp

theorem free_etale_sheaf_zmod_exists_hom_sending_generator {B : Scheme.{0}} {q : ℕ} (H : SShv B q) (U : B.Etale) (x : H.obj.obj (op U)) :
    ∃ t : (F0 B q).obj U ⟶ H, t.hom.app (op U) (gen U) = x := by
  let φ : P0 B q U ⟶ H.obj :=
    { app := fun W => ModuleCat.freeDesc (TypeCat.ofHom (fun f : ULift.{1} (W.unop ⟶ U) => H.obj.map f.down.op x))
      naturality := by
        intro W W' f
        apply ModuleCat.free_hom_ext
        intro y
        simp only [Gq, ConcreteCategory.comp_apply, Functor.comp_map]
        erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        show H.obj.map (f.unop ≫ y.down).op x = H.obj.map f (H.obj.map y.down.op x)
        simp }
  refine ⟨((sheafificationAdjunction (EtTop B) _).homEquiv (P0 B q U) H).symm φ, ?_⟩
  have e := ((sheafificationAdjunction (EtTop B) _).homEquiv (P0 B q U) H).apply_symm_apply φ
  rw [Adjunction.homEquiv_unit] at e
  have e2 := ConcreteCategory.congr_hom (NatTrans.congr_app e (op U)) (ModuleCat.freeMk (ULift.up (𝟙 U)))
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at e2
  unfold gen
  refine Eq.trans ?_ (e2.trans ?_)
  · rfl
  · simp only [φ]
    erw [ModuleCat.freeDesc_apply]
    show H.obj.map (𝟙 U).op x = x
    simp

theorem free_etale_sheaf_zmod_representable_generates : EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerators := by
  intro B q H H' g h
  apply (sheafToPresheaf (EtTop B) (ModuleCat.{1} (Rq q))).map_injective
  rw [Functor.map_zero]
  apply NatTrans.ext
  funext U
  induction U with | op U => ?_
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨t, ht⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator H U x
  obtain ⟨S, hS, hP⟩ := h U t
  have key : ∀ (U' : B.Etale) (a : U' ⟶ U), S a →
      H'.obj.map a.op (g.hom.app (op U) x) = H'.obj.map a.op 0 := by
    intro U' a ha
    have h3 := congrArg (fun m : (F0 B q).obj U' ⟶ H' =>
      ((sheafToPresheaf (EtTop B) (ModuleCat.{1} (Rq q))).map m).app (op U') (gen U')) (hP U' a ha)
    simp only [Functor.map_comp, Functor.map_zero, NatTrans.comp_app, NatTrans.app_zero,
      ConcreteCategory.comp_apply] at h3
    rw [map_zero, ← ht]
    have n := ConcreteCategory.congr_hom (g.hom.naturality a.op) (t.hom.app (op U) (gen U))
    simp only [ConcreteCategory.comp_apply] at n
    rw [← n]
    have n2 := ConcreteCategory.congr_hom (t.hom.naturality a.op) (gen U)
    simp only [ConcreteCategory.comp_apply] at n2
    rw [← n2, ← gen_nat a]
    exact h3
  have := Sheaf.isSeparated H' U S hS _ 0 key
  simp only [NatTrans.app_zero]
  exact this

end LateralTheory.E.DegreeZeroGenerators
end
end
