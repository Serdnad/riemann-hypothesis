module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle012
public import Development.EtaleCohomology.CohomologicalPurity.Bundle021
public import Development.EtaleCohomology.CohomologicalPurity.Bundle025
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
public import Development.EtaleCohomology.CohomologicalPurity.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Presentable.Type
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
import Mathlib.Tactic.TypeStar
public import Development.EtaleCohomology.CohomologicalPurity.Bundle014

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ThomClassRestriction

theorem LeafTau_of (hBd : LeafBd) (hG : LeafGeo) (hPB : LeafPB) (hTl : LeafTail)
    (hU : LeafTauU) (hT : LeafTauTop) : LeafTau :=
  LeafTau_ofU hBd hG hPB hTl hU hT

end LateralTheory.CohomologicalPurity.Thom.ThomClassRestriction
end
end

section

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem fin_pb {α β γ δ M : Type*} [AddCommMonoid M] (t : α → β) (l : α → γ) (r : β → δ) (b : γ → δ)
    (w : ∀ a, r (t a) = b (l a)) (hpb : ∀ x y, r x = b y → ∃ a, t a = x ∧ l a = y)
    (ht : Function.Injective t) (hr : Function.Injective r) (hb : Function.Injective b)
    (x : β →₀ M) (y : γ →₀ M) (h : Finsupp.mapDomain r x = Finsupp.mapDomain b y) :
    ∃ z : α →₀ M, Finsupp.mapDomain t z = x ∧ Finsupp.mapDomain l z = y := by
  classical
  have hsupp : ∀ s ∈ x.support, s ∈ Set.range t := by
    intro s hs
    have h1 : (Finsupp.mapDomain r x) (r s) ≠ 0 := by
      rw [Finsupp.mapDomain_apply_of_injective hr]; exact Finsupp.mem_support_iff.1 hs
    rw [h] at h1
    have h2 : r s ∈ (Finsupp.mapDomain b y).support := Finsupp.mem_support_iff.2 h1
    have h3 := Finsupp.mapDomain_support h2
    obtain ⟨c, -, hc⟩ := Finset.mem_image.1 h3
    obtain ⟨a, ha, -⟩ := hpb s c hc.symm
    exact ⟨a, ha⟩
  refine ⟨x.comapDomain t ht.injOn, ?_, ?_⟩
  · exact Finsupp.mapDomain_comapDomain t ht x hsupp
  · apply Finsupp.mapDomain_injective hb
    rw [← Finsupp.mapDomain_comp]
    have : b ∘ l = r ∘ t := funext fun a => (w a).symm
    rw [this, Finsupp.mapDomain_comp, Finsupp.mapDomain_comapDomain t ht x hsupp, h]

theorem isPullback_of_app {J C : Type*} [Category J] [Category C] {A B X Y : J ⥤ C}
    {t : A ⟶ B} {l : A ⟶ X} {r : B ⟶ Y} {b : X ⟶ Y} (w : t ≫ r = l ≫ b)
    (h : ∀ j, IsPullback (t.app j) (l.app j) (r.app j) (b.app j)) : IsPullback t l r b :=
  IsPullback.of_isLimit' ⟨w⟩ (evaluationJointlyReflectsLimits _ fun j =>
    (isLimitMapConePullbackConeEquiv ((evaluation J C).obj j) w).symm (h j).isLimit)

theorem modfree_pb (R : Type) [CommRing R] {A' A B' B : Type} (t : A' ⟶ B') (l : A' ⟶ A) (r : B' ⟶ B)
    (b : A ⟶ B) (hpb : IsPullback t l r b) (hr : Function.Injective r) (hb : Function.Injective b) :
    IsPullback ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map t))
      ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map l))
      ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map r))
      ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map b)) := by
  obtain ⟨w, hinj, hex⟩ := (Types.isPullback_iff _ _ _ _).1 hpb
  have ht : Function.Injective t := fun x y h => hinj x y ⟨h, hb (by
    have := ConcreteCategory.congr_hom w x; have h2 := ConcreteCategory.congr_hom w y; simp only [ConcreteCategory.comp_apply, types_comp_apply] at this h2
    rw [← this, ← h2, h])⟩
  have hw : ∀ a : ULift.{1} A', ULift.up (r (t a.down)) = ULift.up (b (l a.down)) := fun a => by
    have := ConcreteCategory.congr_hom w a.down; simp only [ConcreteCategory.comp_apply, types_comp_apply] at this; rw [this]
  have sq : (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map t) ≫
      (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map r) =
      (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map l) ≫
      (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map b) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, w]
  refine IsPullback.of_map (forget (ModuleCat (ULift.{1} R))) sq ?_
  rw [Types.isPullback_iff]
  refine ⟨congrArg (forget _).map sq, ?_, ?_⟩
  · rintro x y ⟨h1, -⟩
    have hu : Function.Injective (uliftFunctor.{1}.map t) := fun a c h =>
      ULift.ext (ht (congrArg ULift.down h))
    exact Finsupp.mapDomain_injective hu h1
  · intro x y h
    exact fin_pb (uliftFunctor.{1}.map t) (uliftFunctor.{1}.map l) (uliftFunctor.{1}.map r)
      (uliftFunctor.{1}.map b) hw
      (fun x y h => by
        obtain ⟨a, ha1, ha2⟩ := hex x.down y.down (congrArg ULift.down h)
        exact ⟨ULift.up a, ULift.ext ha1, ULift.ext ha2⟩)
      (fun a c h => ULift.ext (ht (congrArg ULift.down h)))
      (fun a c h => ULift.ext (hr (congrArg ULift.down h)))
      (fun a c h => ULift.ext (hb (congrArg ULift.down h))) x y h

theorem leafFreePb : LeafFreePb := by
  intro R _ A' A B' B t l r b hpb hr hb
  have hP : IsPullback ((freeP R).map t) ((freeP R).map l) ((freeP R).map r) ((freeP R).map b) := by
    refine isPullback_of_app (by rw [← Functor.map_comp, ← Functor.map_comp, hpb.w]) fun U => ?_
    have hrU : Mono (r.app U) := by rw [NatTrans.mono_iff_mono_app] at hr; exact hr U
    have hbU : Mono (b.app U) := by rw [NatTrans.mono_iff_mono_app] at hb; exact hb U
    exact modfree_pb R _ _ _ _ (hpb.map ((evaluation _ _).obj U))
      ((mono_iff_injective _).1 hrU) ((mono_iff_injective _).1 hbU)
  exact hP.map (presheafToSheaf _ _)

theorem LeafCokIso_of : LeafCokIso := leafCokIso_of leafFreePb

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.FreeCovPf

variable {X : Scheme.{0}} (U V : X.Opens)

def pieces : Bool → Scheme.{0}
  | true => U.toScheme
  | false => V.toScheme

def incl : (b : Bool) → pieces U V b ⟶ (U ⊔ V : X.Opens).toScheme
  | true => X.homOfLE le_sup_left
  | false => X.homOfLE le_sup_right

theorem cover_mem :
    Sieve.ofArrows (pieces U V) (incl U V) ∈ Scheme.etaleTopology.{0} (U ⊔ V : X.Opens).toScheme := by
  apply Precoverage.generate_mem_toGrothendieck
  refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun x => ?_, fun b => ?_⟩
  · have hx : x.1 ∈ U ⊔ V := x.2
    rcases (TopologicalSpace.Opens.mem_sup.1 hx) with h | h
    · exact ⟨true, ⟨⟨x.1, h⟩, Subtype.ext (Scheme.homOfLE_apply (le_sup_left : U ≤ U ⊔ V) _)⟩⟩
    · exact ⟨false, ⟨⟨x.1, h⟩, Subtype.ext (Scheme.homOfLE_apply (le_sup_right : V ≤ U ⊔ V) _)⟩⟩
  · cases b
    · exact (inferInstance : Etale (X.homOfLE (le_sup_right : V ≤ U ⊔ V)))
    · exact (inferInstance : Etale (X.homOfLE (le_sup_left : U ≤ U ⊔ V)))

theorem sec_zero (R : Type) [CommRing R] (Zs : Shv R) (z : Zs.obj.obj (op (U ⊔ V : X.Opens).toScheme))
    (h : ∀ b, Zs.obj.map (incl U V b).op z = 0) : z = 0 := by
  have e := Presheaf.IsSheaf.hom_ext_ofArrows Zs.property (incl U V) (cover_mem U V)
    (E := ModuleCat.of (ULift.{1} R) (ULift.{1} R))
    (x := ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ z)) (y := 0) (fun b => by
      ext1
      apply LinearMap.ext_ring
      simp [h b])
  have := congrArg (fun φ => φ.hom (1 : ULift.{1} R)) e
  simpa using this

theorem main (R : Type) [CommRing R] :
    Epi (biprod.desc ((free R).map (yoneda.map (X.homOfLE (le_sup_left : U ≤ U ⊔ V))))
      ((free R).map (yoneda.map (X.homOfLE (le_sup_right : V ≤ U ⊔ V))))) := by
  apply Preadditive.epi_of_cancel_zero
  intro Zs g hg
  have ha := congrArg (fun k => biprod.inl ≫ k) hg
  have hb := congrArg (fun k => biprod.inr ≫ k) hg
  simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, comp_zero] at ha hb
  let adj := sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  let W := (U ⊔ V : X.Opens).toScheme
  let g' := adj.homEquiv _ _ g
  let z := g'.app (op W) (ModuleCat.freeMk (ULift.up (𝟙 W)))
  have hval : ∀ (T : Scheme.{0}) (t : T ⟶ W),
      g'.app (op T) (ModuleCat.freeMk (ULift.up t : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op T)))) = Zs.obj.map t.op z := by
    intro T t
    have := congrArg (fun φ => φ.hom (ModuleCat.freeMk (ULift.up (𝟙 W) : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op W))))) (g'.naturality t.op)
    have key : ((freeP R).obj (yoneda.obj W)).map t.op (ModuleCat.freeMk (ULift.up (𝟙 W) : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op W)))) = ModuleCat.freeMk (ULift.up t : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op T))) := by
      simp [freeP, ModuleCat.freeMk, ModuleCat.free]
      erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rfl
    exact (congrArg (fun v => (g'.app (op T)) v) key).symm.trans this
  have h0 : ∀ (P : PSh), adj.homEquiv _ _ (0 : (presheafToSheaf _ _).obj ((freeP R).obj P) ⟶ Zs) = 0 := by
    intro P
    rw [Adjunction.homEquiv_unit]
    simp
  have hres : ∀ {Y : Scheme.{0}} (i : Y ⟶ W), (free R).map (yoneda.map i) ≫ g = 0 → Zs.obj.map i.op z = 0 := by
    intro Y i hi
    have h1 : adj.homEquiv _ _ ((presheafToSheaf _ _).map ((freeP R).map (yoneda.map i)) ≫ g) =
        (freeP R).map (yoneda.map i) ≫ g' :=
      adj.homEquiv_naturality_left _ _
    have hi' : (presheafToSheaf _ _).map ((freeP R).map (yoneda.map i)) ≫ g = 0 := hi
    rw [hi', h0] at h1
    have h2 := congrArg (fun φ => (φ.app (op Y)).hom (ModuleCat.freeMk (ULift.up (𝟙 Y) : uliftFunctor.{1, 0}.obj ((yoneda.obj Y).obj (op Y))))) h1
    have key : ((freeP R).map (yoneda.map i)).app (op Y) (ModuleCat.freeMk (ULift.up (𝟙 Y) : uliftFunctor.{1, 0}.obj ((yoneda.obj Y).obj (op Y)))) = ModuleCat.freeMk (ULift.up i : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op Y))) := by
      simp [freeP, ModuleCat.freeMk, ModuleCat.free]
      erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rfl
    rw [← hval]
    exact ((congrArg (fun v => (g'.app (op Y)) v) key).symm.trans h2.symm)
  have hz : z = 0 := sec_zero U V R Zs z (fun b => by
    cases b
    · exact hres _ hb
    · exact hres _ ha)
  have hg' : g' = 0 := by
    apply NatTrans.ext
    funext T
    induction T using Opposite.rec with | op T => ?_
    apply ModuleCat.free_hom_ext
    rintro ⟨t⟩
    erw [hval T t]
    rw [hz, map_zero]
    rfl
  exact (adj.homEquiv _ _).injective (hg'.trans (h0 _).symm)

theorem LeafFreeCov_of : LateralTheory.CohomologicalPurity.Thom.LeafFreeCov := fun R _ _ U V => main U V R

end LateralTheory.CohomologicalPurity.FreeCovPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.QisLocalPf

variable (R : Type) [CommRing R]

abbrev Fsh := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))

instance wlb : Scheme.etaleTopology.{0}.WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

instance ph : (Fsh R).PreservesHomology := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  infer_instance

theorem chainsN_eq : chainsN R = TubeCut.chainsP R ⋙ (Fsh R).mapHomologicalComplex _ := by
  unfold chainsN TubeCut.chainsP
  rw [Functor.assoc, AlgebraicTopology.map_alternatingFaceMapComplex]
  rfl

theorem isIso_F_map {P Q : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (g : P ⟶ Q)
    (hi : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} g)
    (hs : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} g) : IsIso ((Fsh R).map g) := by
  exact (GrothendieckTopology.W_iff _ g).1 ((GrothendieckTopology.W_iff_isLocallyBijective _ g).2 ⟨hi, hs⟩)

theorem sc_iso {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology] {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
    [S₁.HasHomology] [S₂.HasHomology] [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [IsIso (F.map (ShortComplex.homologyMap φ))] :
    IsIso (@ShortComplex.homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _) := by
  have e := ShortComplex.mapHomologyIso_hom_naturality φ F
  rw [(Iso.eq_comp_inv _).2 e]
  infer_instance

theorem quasiIso_chainsN {E E' : Spc} (f : E ⟶ E')
    (hi : ∀ n, Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((TubeCut.chainsP R).map f) n))
    (hs : ∀ n, Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((TubeCut.chainsP R).map f) n)) :
    QuasiIso ((chainsN R).map f) := by
  have key : ∀ {K L : ChainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℕ} (φ : K ⟶ L),
      (∀ n, IsIso ((Fsh R).map (HomologicalComplex.homologyMap φ n))) →
      QuasiIso (((Fsh R).mapHomologicalComplex _).map φ) := by
    intro K L φ h
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
    have e := ShortComplex.mapHomologyIso_hom_naturality ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) (Fsh R)
    have : IsIso ((Fsh R).map (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor _ _ n).map φ))) := h n
    exact sc_iso (Fsh R) ((HomologicalComplex.shortComplexFunctor _ _ n).map φ)
  have hf := key ((TubeCut.chainsP R).map f) (fun n => isIso_F_map R _ (hi n) (hs n))
  rw [chainsN_eq]
  exact hf

theorem LeafQisLocal_of : TubeCut.LeafQisLocal := by
  intro R _ E E' f hi hs
  have h := quasiIso_chainsN R f hi hs
  show QuasiIso (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat)
  exact (HomologicalComplex.quasiIso_extendMap_iff _ _).2 h

end LateralTheory.CohomologicalPurity.QisLocalPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

@[reassoc] theorem dinl_map {A B : Arrow Spc} (ψ : A ⟶ B) : dbl.inl A ≫ dbl.map ψ = ψ.right ≫ dbl.inl B :=
  pushout.inl_desc (f := A.hom) (g := A.hom) _ _ _

variable {P' P : Arrow Spc} (φ : P' ⟶ P)

def ii : P'.right ⟶ MM φ := pushout.inl P'.hom (P'.hom ≫ φ.right)
def jj : P.right ⟶ MM φ := pushout.inr P'.hom (P'.hom ≫ φ.right)
theorem ij_cond : P'.hom ≫ ii φ = (P'.hom ≫ φ.right) ≫ jj φ :=
  pushout.condition (f := P'.hom) (g := P'.hom ≫ φ.right)

def rr : MM φ ⟶ P.right :=
  pushout.desc (f := P'.hom) (g := P'.hom ≫ φ.right) φ.right (𝟙 _) (by simp)

def QQ : Arrow Spc := Arrow.mk (jj φ)

def chi : P' ⟶ QQ φ := Arrow.homMk (P'.hom ≫ φ.right) (ii φ) (ij_cond φ).symm

def sig : dbl (QQ φ) ⟶ MM φ :=
  pushout.desc (f := jj φ) (g := jj φ) (𝟙 _) (rr φ ≫ jj φ) (by
    have h : jj φ ≫ rr φ = 𝟙 _ :=
      pushout.inr_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
    rw [← Category.assoc, h, Category.id_comp, Category.comp_id])

theorem inr_sig_gM : dbl.inr (QQ φ) ≫ sig φ ≫ gM φ = rr φ ≫ dbl.inr P := by
  have hs : dbl.inr (QQ φ) ≫ sig φ = rr φ ≫ jj φ :=
    pushout.inr_desc (f := jj φ) (g := jj φ) _ _ _
  have hg : jj φ ≫ gM φ = dbl.inr P :=
    pushout.inr_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
  rw [← Category.assoc, hs]
  change (rr φ ≫ jj φ) ≫ gM φ = rr φ ≫ dbl.inr P
  rw [Category.assoc, hg]

theorem hgM : dbl.map (chi φ) ≫ sig φ ≫ gM φ = dbl.map φ := by
  have hs : dbl.inl (QQ φ) ≫ sig φ = 𝟙 _ :=
    pushout.inl_desc (f := jj φ) (g := jj φ) _ _ _
  have hg : ii φ ≫ gM φ = φ.right ≫ dbl.inl P :=
    pushout.inl_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
  have hr : ii φ ≫ rr φ = φ.right :=
    pushout.inl_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
  apply pushout.hom_ext
  · show dbl.inl P' ≫ _ = dbl.inl P' ≫ _
    rw [dinl_map_assoc, dinl_map, ← Category.assoc (dbl.inl (QQ φ)), hs]
    change ii φ ≫ 𝟙 (MM φ) ≫ gM φ = _
    rw [Category.id_comp]
    exact hg
  · show dbl.inr P' ≫ _ = dbl.inr P' ≫ _
    rw [← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, inr_sig_gM]
    change ii φ ≫ rr φ ≫ dbl.inr P = _
    rw [← Category.assoc, hr]

end LateralTheory.CohomologicalPurity.TubeCut

namespace LateralTheory.CohomologicalPurity.TubeCut
variable {P' P : Arrow Spc} (φ : P' ⟶ P)
theorem jj_inl : jj φ ≫ dbl.inl (QQ φ) = jj φ ≫ dbl.inr (QQ φ) :=
  pushout.condition (f := jj φ) (g := jj φ)

def LeafFix : Prop := ∀ (q : ℕ) (n i : ℤ) {P' P : Arrow Spc} (φ : P' ⟶ P) (z : Ht q (dbl (QQ φ)) n i),
  z ∈ Hs q (QQ φ) n i → pull _ (sig φ ≫ dbl.inl (QQ φ)) (tw q i) n z = z

def LeafChiExc : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), Exc q (chi φ)

theorem pull_sig_inl (q : ℕ) (n i : ℤ) (z : Ht q (dbl (QQ φ)) n i) :
    pull _ (sig φ) (tw q i) n (pull _ (dbl.inl (QQ φ)) (tw q i) n z) = pull _ (sig φ ≫ dbl.inl (QQ φ)) (tw q i) n z :=
  (pull_comp _ (sig φ) (dbl.inl (QQ φ)) _ n z).symm

theorem pull_jj_inl (q : ℕ) (n i : ℤ) (z : Ht q (dbl (QQ φ)) n i) (hz : z ∈ Hs q (QQ φ) n i) :
    pull _ (jj φ) (tw q i) n (pull _ (dbl.inl (QQ φ)) (tw q i) n z) = 0 := by
  have hzz : pull _ (dbl.inr (QQ φ)) (tw q i) n z = 0 := hz
  exact (pull_comp _ (jj φ) (dbl.inl (QQ φ)) _ n z).symm.trans
    ((congrArg (fun f => pull _ f (tw q i) n z) (jj_inl φ)).trans
      ((pull_comp _ (jj φ) (dbl.inr (QQ φ)) _ n z).trans ((congrArg (pull _ (jj φ) (tw q i) n) hzz).trans (map_zero _))))

theorem LeafExcOfEqv_of (hF : LeafFix) (hX : LeafChiExc) : LeafExcOfEqv := by
  intro q P' P φ hE n i
  have jj_gM : jj φ ≫ gM φ = dbl.inr P :=
    pushout.inr_desc (f := P'.hom) (g := P'.hom ≫ φ.right) _ _ _
  have inr_sig : dbl.inr (QQ φ) ≫ sig φ = rr φ ≫ jj φ :=
    pushout.inr_desc (f := jj φ) (g := jj φ) _ _ _
  have inl_sig : dbl.inl (QQ φ) ≫ sig φ = 𝟙 _ :=
    pushout.inl_desc (f := jj φ) (g := jj φ) _ _ _
  have hB : Function.Bijective (pull _ (gM φ) (tw q i) n) := hE i n
  have hC := hX q φ n i
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    have hw' : pull _ (dbl.map φ) (tw q i) n w.1 = 0 := congrArg Subtype.val hw
    have hj : pull _ (jj φ) (tw q i) n (pull _ (gM φ) (tw q i) n w.1) = 0 := by
      rw [← pull_comp, jj_gM]; exact w.2
    have hz : pull _ (sig φ) (tw q i) n (pull _ (gM φ) (tw q i) n w.1) ∈ Hs q (QQ φ) n i := by
      change pull _ (dbl.inr (QQ φ)) _ n (pull _ (sig φ) _ n _) = 0
      exact (pull_comp _ (dbl.inr (QQ φ)) (sig φ) _ n _).symm.trans
        ((congrArg (fun f => pull _ f (tw q i) n (pull _ (gM φ) (tw q i) n w.1)) inr_sig).trans
          ((pull_comp _ (rr φ) (jj φ) _ n _).trans ((congrArg (pull _ (rr φ) (tw q i) n) hj).trans (map_zero _))))
    have h0 : Hs.pull q (chi φ) n i ⟨_, hz⟩ = Hs.pull q (chi φ) n i 0 := by
      rw [map_zero]
      apply Subtype.ext
      change pull _ (dbl.map (chi φ)) _ n (pull _ (sig φ) _ n (pull _ (gM φ) _ n w.1)) = 0
      rw [← pull_comp, ← pull_comp, Category.assoc, hgM]; exact hw'
    have h1 := congrArg Subtype.val (hC.1 h0)
    change pull _ (sig φ) _ n (pull _ (gM φ) _ n w.1) = 0 at h1
    have h2 : pull _ (gM φ) (tw q i) n w.1 = 0 := by
      have e := congrArg (pull _ (dbl.inl (QQ φ)) (tw q i) n) h1
      have e2 : pull _ (dbl.inl (QQ φ)) (tw q i) n (pull _ (sig φ) (tw q i) n (pull _ (gM φ) (tw q i) n w.1)) =
          pull _ (gM φ) (tw q i) n w.1 :=
        (pull_comp _ (dbl.inl (QQ φ)) (sig φ) _ n _).symm.trans
          ((congrArg (fun f => pull _ f (tw q i) n (pull _ (gM φ) (tw q i) n w.1)) inl_sig).trans (pull_id _ _ _ n _))
      rw [e2, map_zero] at e
      exact e
    apply Subtype.ext
    exact hB.1 (h2.trans (map_zero _).symm)
  · intro z'
    obtain ⟨z, hz⟩ := hC.2 z'
    obtain ⟨y', hy'⟩ := hB.2 (pull _ (dbl.inl (QQ φ)) (tw q i) n z.1)
    have hm : y' ∈ Hs q P n i := by
      change pull _ (dbl.inr P) _ n y' = 0
      rw [← jj_gM, pull_comp, hy']
      exact pull_jj_inl φ q n i z.1 z.2
    refine ⟨⟨y', hm⟩, ?_⟩
    rw [← hz]
    apply Subtype.ext
    change pull _ (dbl.map φ) _ n y' = pull _ (dbl.map (chi φ)) _ n z.1
    rw [← hgM, pull_comp, pull_comp, hy', pull_sig_inl, hF q n i φ z.1 z.2]

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

abbrev levF (n : SimplexCategoryᵒᵖ) : Spc ⥤ Spc := (evaluation SimplexCategoryᵒᵖ PSh).obj n ⋙ disc

theorem LeafMLev_of : LeafMLev := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro P' P φ n
  let F := levF n
  have hc : F.map (P'.hom ≫ φ.right) = F.map P'.hom ≫ F.map φ.right := F.map_comp _ _
  let a : disc.obj ((MM φ).obj n) ≅ MM ((lev n).map φ) :=
    (PreservesPushout.iso F P'.hom (P'.hom ≫ φ.right)).symm ≪≫ pushout.congrHom rfl hc
  let b : disc.obj ((dbl P).obj n) ≅ dbl ((lev n).obj P) :=
    (PreservesPushout.iso F P.hom P.hom).symm
  refine ⟨a, b, ?_⟩
  rw [← Iso.inv_comp_eq]
  change (pushout.congrHom rfl hc).inv ≫ (PreservesPushout.iso F P'.hom (P'.hom ≫ φ.right)).hom ≫ F.map (gM φ) ≫
    (PreservesPushout.iso F P.hom P.hom).inv = gM ((lev n).map φ)
  apply pushout.hom_ext
  · rw [pushout.congrHom_inv, pushout.inl_desc_assoc, Category.id_comp]
    erw [PreservesPushout.inl_iso_hom_assoc, ← F.map_comp_assoc, pushout.inl_desc, pushout.inl_desc, F.map_comp_assoc]
    erw [PreservesPushout.inl_iso_inv]
    rfl
  · rw [pushout.congrHom_inv, pushout.inr_desc_assoc, Category.id_comp]
    erw [PreservesPushout.inr_iso_hom_assoc, ← F.map_comp_assoc, pushout.inr_desc, pushout.inr_desc]
    erw [PreservesPushout.inr_iso_inv]
    rfl

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

namespace LateralTheory.CohomologicalPurity.Cl

theorem LeafCmp_of_Mat (hMat : LeafMat) : LeafCmp := LeafCmp_of hMat LeafCmpNb_pf LeafCmpId_pf

end LateralTheory.CohomologicalPurity.Cl
end
