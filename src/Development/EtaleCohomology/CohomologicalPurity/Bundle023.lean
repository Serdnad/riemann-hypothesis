module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle013
public import Development.EtaleCohomology.CohomologicalPurity.Bundle014
public import Development.EtaleCohomology.CohomologicalPurity.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def LeafFreeCov : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (U V : X.Opens),
  Epi (biprod.desc ((free R).map (yoneda.map (X.homOfLE (le_sup_left : U ≤ U ⊔ V))))
    ((free R).map (yoneda.map (X.homOfLE (le_sup_right : V ≤ U ⊔ V)))))

namespace HtpyMVPf

theorem bij_pull_iso (R : Type) [CommRing R] (F : Shv R) {A B : Spc} (e : A ≅ B) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine ⟨fun x y h => ?_, fun y => ⟨pull R e.inv F n y, ?_⟩⟩
  · have hx := pull_comp R e.inv e.hom F n x
    have hy := pull_comp R e.inv e.hom F n y
    rw [e.inv_hom_id, pull_id] at hx hy
    rw [hx, hy, h]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem eqv_of_sq (R : Type) [CommRing R] (F : Shv R) {A B A' B' : Spc} (f : A ⟶ B) (g : A' ⟶ B')
    (α : A ≅ A') (β : B ≅ B') (w : α.hom ≫ g = f ≫ β.hom) (hf : Eqv R f F) : Eqv R g F := by
  intro n
  have h1 : (pull R α.hom F n) ∘ (pull R g F n) = (pull R f F n) ∘ (pull R β.hom F n) := by
    funext x; simp only [Function.comp_apply, ← pull_comp, w]
  have h2 : Function.Bijective ((pull R α.hom F n) ∘ (pull R g F n)) := by
    rw [h1]; exact (hf n).comp (bij_pull_iso R F β n)
  exact (Function.Bijective.of_comp_iff' (bij_pull_iso R F α n) _).1 h2

theorem mono_sch {Y Z : Scheme.{0}} (f : Y ⟶ Z) [Mono f] : Mono (sch.map f) := by
  have hy : Mono (yoneda.map f) := by
    have : ∀ T, Mono ((yoneda.map f).app T) := fun T => by
      rw [mono_iff_injective]
      intro a b h
      exact (cancel_mono f).1 h
    exact NatTrans.mono_of_mono_app _
  have : ∀ n, Mono ((sch.map f).app n) := fun _ => hy
  exact NatTrans.mono_of_mono_app _

theorem sch_pres : PreservesLimitsOfShape WalkingCospan sch := by
  unfold sch; infer_instance

end HtpyMVPf

theorem LeafHtpyMV_of (hF : LeafFreeCov) : LeafHtpyMV := by
  intro a4 R _ F X' X p U V U' V' hU hV hI hS hu hv hi
  have cov : ∀ (Y : Scheme.{0}) (A B : Y.Opens),
      Cover2 R (sch.map (Y.homOfLE (le_sup_left : A ≤ A ⊔ B))) (sch.map (Y.homOfLE (le_sup_right : B ≤ A ⊔ B))) :=
    fun Y A B => ⟨HtpyMVPf.mono_sch _, HtpyMVPf.mono_sch _, fun _ => hF R Y A B⟩
  have eu : X'.homOfLE (le_sup_left : U' ≤ U' ⊔ V') ≫ p.resLE (U ⊔ V) (U' ⊔ V') hS =
      p.resLE U U' hU ≫ X.homOfLE (le_sup_left : U ≤ U ⊔ V) := by
    simp
  have ev : X'.homOfLE (le_sup_right : V' ≤ U' ⊔ V') ≫ p.resLE (U ⊔ V) (U' ⊔ V') hS =
      p.resLE V V' hV ≫ X.homOfLE (le_sup_right : V ≤ U ⊔ V) := by
    simp
  have hu' := congrArg sch.map eu
  have hv' := congrArg sch.map ev
  rw [sch.map_comp, sch.map_comp] at hu' hv'
  refine a4 R _ _ _ _ _ _ _ hu' hv' F (cov X' U' V') (cov X U V) hu hv ?_
  have := HtpyMVPf.sch_pres
  have P' := (isPullback_opens_inf_le (X := X') (le_sup_left : U' ≤ U' ⊔ V') (le_sup_right : V' ≤ U' ⊔ V')).map sch
  have P := (isPullback_opens_inf_le (X := X) (le_sup_left : U ≤ U ⊔ V) (le_sup_right : V ≤ U ⊔ V)).map sch
  refine HtpyMVPf.eqv_of_sq R F _ _ P'.isoPullback P.isoPullback ?_ hi
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc, Category.assoc,
      IsPullback.isoPullback_hom_fst, ← sch.map_comp, ← sch.map_comp]
    congr 1
    simp
  · rw [Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc, Category.assoc,
      IsPullback.isoPullback_hom_snd, ← sch.map_comp, ← sch.map_comp]
    congr 1
    simp

end LateralTheory.CohomologicalPurity.Thom
end
end

section

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

theorem le_map_of {d : ℕ} {P : SP d} (F F₀ : Frame P) (C : Type) [CommRing C] (φ : F.B →+* C) (ψ : F₀.B →+* C)
    (e : Spec.map (CommRingCat.ofHom φ) ≫ F.w = Spec.map (CommRingCat.ofHom ψ) ≫ F₀.w) : F.I.map φ ≤ F₀.I.map ψ := by
  let J := F₀.I.map ψ
  let π : C →+* C ⧸ J := Ideal.Quotient.mk J
  let ψ' : F₀.B ⧸ F₀.I →+* C ⧸ J := Ideal.Quotient.lift F₀.I (π.comp ψ)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem ψ ha))
  have hψ : ψ'.comp (Ideal.Quotient.mk F₀.I) = π.comp ψ := RingHom.ext fun a => rfl
  have hw : (Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom φ)) ≫ F.w =
      (Spec.map (CommRingCat.ofHom ψ') ≫ F₀.z) ≫ P.ι := by
    rw [Category.assoc, e, Category.assoc, ← F₀.cart.w, ← Category.assoc, ← Category.assoc,
      ← spec_comp_ofHom, ← spec_comp_ofHom, hψ]
  let t := F.cart.lift _ _ hw
  have ht : t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I)) =
      Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom φ) := F.cart.lift_fst _ _ _
  let τ : F.B ⧸ F.I →+* C ⧸ J := (Spec.preimage t).hom
  have h1 : Spec.map (CommRingCat.ofHom (τ.comp (Ideal.Quotient.mk F.I))) =
      Spec.map (CommRingCat.ofHom (π.comp φ)) := by
    rw [spec_comp_ofHom, spec_comp_ofHom, ← ht]
    congr 1
    exact Spec.map_preimage t
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  change (π.comp φ) a = 0
  rw [← show (τ.comp (Ideal.Quotient.mk F.I)) = π.comp φ from h2, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

theorem LeafCmpId_pf : LeafCmpId := fun _ _ F F₀ C _ φ ψ e =>
  le_antisymm (le_map_of F F₀ C φ ψ e) (le_map_of F₀ F C ψ φ e.symm)

end LateralTheory.CohomologicalPurity.Cl
end
end

section

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

theorem LeafCmpNb_pf : LeafCmpNb := by
  intro X B B₀ _ _ w w₀ h₀ y hy
  let W : (Spec (CommRingCat.of B)).Opens := w ⁻¹ᵁ w₀.opensRange
  have hs : IsOpen (X := PrimeSpectrum B) (W : Set (Spec (CommRingCat.of B))) := W.2
  have hyW : (y : PrimeSpectrum B) ∈ (W : Set (Spec (CommRingCat.of B))) := hy
  obtain ⟨_, ⟨g, rfl⟩, hyg, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := B)).exists_subset_of_mem_open hyW hs
  let l : B →+* Localization.Away g := algebraMap B (Localization.Away g)
  have hr : Set.range (PrimeSpectrum.comap l) = PrimeSpectrum.basicOpen g :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away g) g
  have H : Set.range (Spec.map (CommRingCat.ofHom l) ≫ w) ⊆ Set.range w₀ := by
    rintro _ ⟨t, rfl⟩
    have : (Spec.map (CommRingCat.ofHom l)) t ∈ W :=
      hsub (by
        have h1 : PrimeSpectrum.comap l t ∈ Set.range (PrimeSpectrum.comap l) := ⟨t, rfl⟩
        rw [hr] at h1; exact h1)
    exact this
  let u := IsOpenImmersion.lift w₀ _ H
  refine ⟨Localization.Away g, inferInstance, l, (Spec.preimage u).hom, ?_, ?_, ?_⟩
  · exact Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of B) g
  · have h2 : (y : PrimeSpectrum B) ∈ Set.range (PrimeSpectrum.comap l) := by rw [hr]; exact hyg
    obtain ⟨t, ht⟩ := h2
    exact ⟨show Spec (CommRingCat.of (Localization.Away g)) from t, ht⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    exact (IsOpenImmersion.lift_fac w₀ _ H).symm

end LateralTheory.CohomologicalPurity.Cl
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

theorem sres_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res f (Sec.res g x) = Sec.res (f ≫ g) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem sres_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (f : V ⟶ U) :
    Sec.res (F := F) f 0 = 0 := map_zero ((F.obj.map f.op).hom)

theorem smap_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero ((φ.hom.app (op U)).hom)

theorem smap_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (f : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res f x) = Sec.res f (Sec.map φ x) := by
  have := congrArg (fun h => h.hom x) (φ.hom.naturality f.op)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this

theorem le_comp' {Y Z X : Scheme.{0}} {W : Y.Opens} (f : Y ⟶ Z) (g : Z ⟶ X) (U : X.Opens) (k : Y ⟶ X)
    (hk : f ≫ g = k) (hW : W ≤ k ⁻¹ᵁ U) : W ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  subst hk; intro w hw; exact hW hw

theorem zc_res {R : Type} [CommRing R] {K : Cx R} {n : ℤ} {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens)
    (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U) (a : Sec (K.X n) X) (ha : a ∈ Zc K U n) : Sec.res f a ∈ Zc K U' n := by
  rw [mem_Zc] at ha ⊢
  refine ⟨?_, ?_⟩
  · rw [sres_comp, ← Scheme.Hom.resLE_comp_ι f h, ← sres_comp, ha.1, sres_zero]
  · rw [smap_res, ha.2, sres_zero]

theorem res_inj (q : ℕ) (i : ℤ) : ∀ s, Injective ((res _ (tw q i)).X s) := fun s => by
  unfold res; infer_instance

theorem res_neg (q : ℕ) (i : ℤ) : ∀ s < 0, IsZero ((res _ (tw q i)).X s) := fun s hs => by
  unfold res; exact CochainComplex.isZero_of_isStrictlyGE _ 0 s hs

theorem LeafDescOSep_of : LeafDescOSep := by
  intro hD hF q X U m i hL s hs
  have h1 : ∀ n < m, ∀ (W : X.Opens), ∀ a ∈ Zc (res _ (tw q i)) (W.ι ⁻¹ᵁ U) n, ∀ x ∈ W,
      ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ Bd (res _ (tw q i)) (V.ι ⁻¹ᵁ U) n (rs h a) := by
    intro n hn W a ha x hx
    obtain ⟨V, hVW, hxV, hV⟩ := hL x W hx
    obtain ⟨cls, -, hker, -⟩ := hD q n i
    have hz : rs hVW a ∈ Zc (res _ (tw q i)) (V.ι ⁻¹ᵁ U) n :=
      zc_res _ _ _ (le_comp' _ _ U _ (Scheme.homOfLE_ι _ _) le_rfl) a ha
    refine ⟨V, hVW, hxV, (hker _ ⟨_, hz⟩).1 ?_⟩
    have := hV n hn
    exact Subsingleton.elim _ _
  obtain ⟨cls, hsurj, hker, hnat⟩ := hD q m i
  obtain ⟨a, rfl⟩ := hsurj U s
  have hFl := (hF _ (res _ (tw q i)) (res_inj q i) (res_neg q i) X U m h1).1
  have hza' : Sec.res (⊤ : X.Opens).ι a.1 ∈ Zc (res _ (tw q i)) ((⊤ : X.Opens).ι ⁻¹ᵁ U) m :=
    zc_res _ _ _ le_rfl a.1 a.2
  have hB : Bd (res _ (tw q i)) ((⊤ : X.Opens).ι ⁻¹ᵁ U) m (Sec.res (⊤ : X.Opens).ι a.1) := by
    apply hFl ⊤
    intro x _
    by_cases hxU : x ∈ U
    · refine ⟨U, le_top, hxU, ⟨0, sres_zero _, ?_⟩⟩
      have e : rs (le_top : U ≤ ⊤) (Sec.res (⊤ : X.Opens).ι a.1) = 0 := by
        unfold rs; rw [sres_comp, Scheme.homOfLE_ι]; exact a.2.1
      rw [e]; exact smap_zero _
    · obtain ⟨V, hxV, hV0⟩ := hs x hxU
      refine ⟨V, le_top, hxV, ?_⟩
      have e : rs (le_top : V ≤ ⊤) (Sec.res (⊤ : X.Opens).ι a.1) = Sec.res V.ι a.1 := by
        unfold rs; rw [sres_comp, Scheme.homOfLE_ι]
      have hz : Sec.res V.ι a.1 ∈ Zc (res _ (tw q i)) (V.ι ⁻¹ᵁ U) m := zc_res _ _ _ le_rfl a.1 a.2
      rw [e]
      refine (hker _ (⟨_, hz⟩ : Zc _ _ _)).1 ?_
      rw [← hnat V.ι (V.ι ⁻¹ᵁ U) U le_rfl a ⟨_, hz⟩ rfl]
      exact hV0
  have h0 := (hker _ (⟨_, hza'⟩ : Zc _ _ _)).2 hB
  rw [← hnat (⊤ : X.Opens).ι _ U le_rfl a ⟨_, hza'⟩ rfl] at h0
  have hle : U ≤ X.topIso.inv ⁻¹ᵁ ((⊤ : X.Opens).ι ⁻¹ᵁ U) :=
    le_comp' _ _ U (𝟙 X) (Scheme.toIso_inv_ι X) (fun x hx => hx)
  have hid : U ≤ (𝟙 X) ⁻¹ᵁ U := fun x hx => hx
  have key := pull_pull X.topIso.inv (⊤ : X.Opens).ι (Scheme.toIso_inv_ι X) U _ U hle le_rfl hid m i (cls U a)
  rw [h0, map_zero, Hs_pull_id] at key
  exact key.symm

end LateralTheory.CohomologicalPurity.Cl
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Cl

theorem ker_specMap_mk_appTop {R : CommRingCat.{0}} (I : Ideal R) :
    RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom =
      I.comap (Scheme.ΓSpecIso R).hom.hom := by
  have h := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))
  calc RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom
      = RingHom.ker ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I))).hom).hom := by
        rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv]; rfl
    _ = RingHom.ker ((Scheme.ΓSpecIso R).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)).hom := by rw [h]; rfl
    _ = _ := by rw [CommRingCat.hom_comp, ← RingHom.comap_ker, CommRingCat.hom_ofHom, Ideal.mk_ker]

theorem comap_iso_inv {A B : CommRingCat.{0}} (e : A ≅ B) (J : Ideal A) :
    J.comap e.inv.hom = J.map e.hom.hom := by
  have h := Ideal.comap_symm (I := J) e.commRingCatIsoToRingEquiv
  exact h

theorem ker_specMap_mk_top {B : CommRingCat.{0}} (IB : Ideal B) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk IB))).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      IB.comap (Scheme.ΓSpecIso B).hom.hom := by
  rw [Scheme.ker_of_isAffine, Scheme.IdealSheafData.ofIdealTop_ideal, ← ker_specMap_mk_appTop]
  convert Ideal.map_id _
  rw [show (homOfLE (X := (Spec (CommRingCat.of B)).Opens) (le_top (a := ⊤))).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id]
  rfl

theorem comap_ideal_top {X : Scheme.{0}} {B : CommRingCat.{0}} (I : X.IdealSheafData) (w : Spec B ⟶ X)
    [IsOpenImmersion w] (V : X.affineOpens) (ψ : Γ(X, V.1) ⟶ B) (hle : w ''ᵁ ⊤ ≤ V.1)
    (key : X.presheaf.map (homOfLE hle).op ≫ (w.appIso ⊤).hom = ψ ≫ (Scheme.ΓSpecIso B).inv) :
    (I.comap w).ideal ⟨⊤, isAffineOpen_top _⟩ = (I.ideal V).map (ψ ≫ (Scheme.ΓSpecIso B).inv).hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  rw [← Scheme.IdealSheafData.map_ideal I (U := ⟨w ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion w⟩) (V := V) hle]
  rw [comap_iso_inv, Ideal.map_map, ← CommRingCat.hom_comp]
  exact congrArg (fun f => Ideal.map (CommRingCat.Hom.hom f) (I.ideal V)) key

theorem key_gen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U))
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec)]
    (hle : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) ''ᵁ ⊤ ≤ U) :
    X.presheaf.map (homOfLE hle).op ≫
      (Scheme.Hom.appIso (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) ⊤).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)) ≫ (Scheme.ΓSpecIso _).inv := by
  have e : (⊤ : (Spec (CommRingCat.of (Localization.Away r))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) ⁻¹ᵁ U := by
    intro x _
    exact hle ⟨x, trivial, rfl⟩
  have e1 := Scheme.Hom.appLE_appIso_inv
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec) e
  have h1 : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have h2 : (⊤ : (Spec (CommRingCat.of (Localization.Away r))).Opens) ≤
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ⁻¹ᵁ ⊤ := le_top
  have a1 : hU.fromSpec.appLE U ⊤ h1 = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    rw [show ((eqToHom hU.fromSpec_preimage_self).op ≫ (homOfLE h1).op : Opposite.op (⊤ : (Spec Γ(X, U)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ from Subsingleton.elim _ _]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have a2 : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))).appLE ⊤ ⊤ h2 =
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r)))).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  calc _ = (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) (Localization.Away r))) ≫ hU.fromSpec).appLE U ⊤ e := by
        rw [← e1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := by
      rw [← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ h1 h2, a1, a2, Scheme.ΓSpecIso_inv_naturality]
      rfl

theorem hle_loc {X : Scheme.{0}} (V : X.affineOpens) (r : Γ(X, V.1))
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec)] :
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec) ''ᵁ ⊤ ≤ V.1 := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  rintro _ ⟨y, rfl⟩
  show V.2.fromSpec _ ∈ (V.1 : Set X)
  rw [← V.2.range_fromSpec]; exact ⟨_, rfl⟩

theorem LeafGenKer_of : LeafGenKer := by
  intro X Z ι _ V r
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec) := by
    have h1 := Scheme.isOpenImmersion_SpecMap_localizationAway (R := Γ(X, V.1)) r
    have h2 := V.2.isOpenImmersion_fromSpec
    infer_instance
  have hle := hle_loc V r
  apply Scheme.IdealSheafData.ext_of_isAffine
  have hL := ker_specMap_mk_top (B := CommRingCat.of (Localization.Away r))
    ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))
  have hR := comap_ideal_top ι.ker _ V _ hle (key_gen V.2 r hle)
  refine hL.trans (Eq.trans ?_ hR.symm)
  have hc := comap_iso_inv (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away r))).symm
    ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))
  simp only [Iso.symm_inv, Iso.symm_hom] at hc
  rw [hc, Ideal.map_map]
  rfl

end LateralTheory.CohomologicalPurity.Cl
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut.HKSumPf

variable {R : Type} [CommRing R] {A : Type} {K : A → Cx R} {c : Cofan K}

instance hasColShv : HasColimitsOfShape (Discrete A) (Shv R) := by
  have : IsGrothendieckAbelian.{1} (Shv R) := inferInstance
  have : HasColimitsOfSize.{1, 1} (Shv R) := IsGrothendieckAbelian.hasColimits (Shv R)
  have : HasColimitsOfSize.{0, 0} (Shv R) := hasColimitsOfSizeShrink.{0, 0, 1, 1} _
  infer_instance

def hcp (hc : IsColimit c) (p : ℤ) : IsColimit ((HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) p).mapCocone c) :=
  haveI : PreservesColimitsOfShape (Discrete A) (HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) p) := inferInstance
  isColimitOfPreserves _ hc

variable {L : Cx R} {n : ℤ}

def glue (hc : IsColimit c) (y : ∀ a, Cochain (K a) L n) : Cochain c.pt L n :=
  Cochain.mk fun p q hpq => (hcp hc p).desc
    ⟨L.X q, Discrete.natTrans fun j => (y j.as).v p q hpq⟩

theorem glue_v (hc : IsColimit c) (y : ∀ a, Cochain (K a) L n) (a : A) (p q : ℤ) (hpq : p + n = q) :
    (c.inj a).f p ≫ (glue hc y).v p q hpq = (y a).v p q hpq := by
  simp only [glue]
  exact (hcp hc p).fac _ ⟨a⟩

theorem comp_glue (hc : IsColimit c) (y : ∀ a, Cochain (K a) L n) (a : A) :
    (Cochain.ofHom (c.inj a)).comp (glue hc y) (zero_add n) = y a := by
  ext p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, glue_v]

theorem ext_cochain (hc : IsColimit c) {z₁ z₂ : Cochain c.pt L n}
    (h : ∀ a, (Cochain.ofHom (c.inj a)).comp z₁ (zero_add n) = (Cochain.ofHom (c.inj a)).comp z₂ (zero_add n)) :
    z₁ = z₂ := by
  refine Cochain.ext _ _ fun p q hpq => ?_
  refine (hcp hc p).hom_ext fun ⟨a⟩ => ?_
  have := congrArg (fun z => z.v p q hpq) (h a)
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] at this
  exact this

end LateralTheory.CohomologicalPurity.TubeCut.SumCut.HKSumPf

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut
open HKSumPf

theorem LeafHKSum_of : LeafHKSum := by
  intro R _ F A K c hc' n
  obtain ⟨hc⟩ := hc'
  have key : ∀ (a : A) (z : Cocycle c.pt (res R F) n),
      HK.pull R (c.inj a) F n (CohomologyClass.mk z) =
        CohomologyClass.mk (zcomp (Cocycle.ofHom (c.inj a)) z (zero_add n)) := fun _ _ => rfl
  constructor
  · let Φ : HK R c.pt F n →+ (∀ a, HK R (K a) F n) := AddMonoidHom.pi fun a => HK.pull R (c.inj a) F n
    change Function.Injective Φ
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := x.mk_surjective
    have h1 : ∀ a, ∃ β : Cochain (K a) (res R F) (n - 1),
        δ (n - 1) n β = (Cochain.ofHom (c.inj a)).comp z.1 (zero_add n) := by
      intro a
      have := congrFun hx a
      change HK.pull R (c.inj a) F n (CohomologyClass.mk z) = 0 at this
      rw [key, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at this
      exact this
    choose β hβ using h1
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨glue hc β, ext_cochain hc fun a => ?_⟩
    rw [← δ_ofHom_comp, comp_glue, hβ]
  · intro f
    have h1 : ∀ a, ∃ z : Cocycle (K a) (res R F) n, CohomologyClass.mk z = f a := fun a => (f a).mk_surjective
    choose z hz using h1
    have hcoc : δ n (n + 1) (glue hc fun a => (z a).1) = 0 := by
      refine ext_cochain hc fun a => ?_
      rw [← δ_ofHom_comp, comp_glue, Cochain.comp_zero]
      exact Cocycle.δ_eq_zero _ _
    refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl hcoc), funext fun a => ?_⟩
    show HK.pull R (c.inj a) F n _ = _
    rw [key, ← hz a]
    congr 1
    exact Cocycle.ext (comp_glue hc _ a)

end LateralTheory.CohomologicalPurity.TubeCut.SumCut
end
end
