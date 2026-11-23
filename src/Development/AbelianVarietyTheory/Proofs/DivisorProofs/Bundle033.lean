module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace GlobalTheory.IdealGlue

lemma res_bijective {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) (e : U = V) :
    Function.Bijective (X.presheaf.map (homOfLE h).op).hom := by
  subst e
  have : homOfLE h = 𝟙 U := Subsingleton.elim _ _
  rw [this, op_id, X.presheaf.map_id]
  exact Function.bijective_id

lemma app_bijective {Q X : Scheme.{u}} (f : Q ⟶ X) [IsOpenImmersion f] (W : X.Opens)
    (hW : W ≤ f.opensRange) : Function.Bijective (f.app W).hom := by
  have h2 : f.app W = X.presheaf.map (homOfLE (f.image_preimage_le W)).op ≫
      (f.appIso (f ⁻¹ᵁ W)).hom := by
    rw [← Category.comp_id (f.app W), ← Iso.inv_hom_id (f.appIso (f ⁻¹ᵁ W)), ← Category.assoc,
      f.app_appIso_inv]
    rfl
  rw [h2, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Bijective.comp (f.appIso (f ⁻¹ᵁ W)).commRingCatIsoToRingEquiv.bijective
    (res_bijective _ ?_)
  rw [f.image_preimage_eq_opensRange_inf]
  exact inf_eq_right.mpr hW

noncomputable def loc {P X : Scheme.{u}} (f : P ⟶ X) (J : P.IdealSheafData) (W : X.affineOpens)
    (h : IsAffineOpen (f ⁻¹ᵁ W.1)) : Ideal Γ(X, W) :=
  (J.ideal ⟨f ⁻¹ᵁ W.1, h⟩).comap (f.app W.1).hom

lemma loc_congr {P X : Scheme.{u}} {f f' : P ⟶ X} (hf : f = f') {J J' : P.IdealSheafData}
    (hJ : J = J') (W : X.affineOpens) (h : IsAffineOpen (f ⁻¹ᵁ W.1))
    (h' : IsAffineOpen (f' ⁻¹ᵁ W.1)) : loc f J W h = loc f' J' W h' := by
  subst hf hJ; rfl

lemma loc_comap {Q X : Scheme.{u}} (f : Q ⟶ X) [IsOpenImmersion f] (I : X.IdealSheafData)
    (W : X.affineOpens) (hW : W.1 ≤ f.opensRange) (h : IsAffineOpen (f ⁻¹ᵁ W.1)) :
    loc f (I.comap f) W h = I.ideal W := by
  unfold loc
  have hle : (⟨f ''ᵁ f ⁻¹ᵁ W.1, h.image_of_isOpenImmersion f⟩ : X.affineOpens) ≤ W :=
    f.image_preimage_le W.1
  have e1 := I.ideal_comap_of_isOpenImmersion f ⟨f ⁻¹ᵁ W.1, h⟩
  have e2 := I.map_ideal hle
  rw [e1, Ideal.comap_comap, ← CommRingCat.hom_comp, f.app_appIso_inv]
  refine Eq.trans ?_ (Ideal.comap_map_of_bijective _ (res_bijective (f.image_preimage_le W.1) (by
    rw [f.image_preimage_eq_opensRange_inf]; exact inf_eq_right.mpr hW)) (I := I.ideal W))
  exact congrArg _ e2.symm

lemma loc_comp {Q' Q X : Scheme.{u}} (g : Q' ⟶ Q) (f : Q ⟶ X) [IsOpenImmersion g]
    [IsOpenImmersion f] (J : Q.IdealSheafData) (W : X.affineOpens)
    (hW : W.1 ≤ (g ≫ f).opensRange) (h1 : IsAffineOpen ((g ≫ f) ⁻¹ᵁ W.1))
    (h2 : IsAffineOpen (f ⁻¹ᵁ W.1)) :
    loc (g ≫ f) (J.comap g) W h1 = loc f J W h2 := by
  have hle : f ⁻¹ᵁ W.1 ≤ g.opensRange := by
    intro y hy
    obtain ⟨z, hz⟩ := hW hy
    refine ⟨z, f.isOpenEmbedding.injective ?_⟩
    simpa using hz
  have := loc_comap g J ⟨f ⁻¹ᵁ W.1, h2⟩ hle
    (by simpa [Scheme.Hom.comp_preimage] using h1)
  unfold loc at this ⊢
  calc _ = (((J.comap g).ideal ⟨(g ≫ f) ⁻¹ᵁ W.1, h1⟩).comap
        (g.app (f ⁻¹ᵁ W.1)).hom).comap (f.app W.1).hom := by
          exact (congrArg (fun φ => Ideal.comap (CommRingCat.Hom.hom φ)
            ((J.comap g).ideal ⟨(g ≫ f) ⁻¹ᵁ W.1, h1⟩)) (Scheme.Hom.comp_app g f W.1)).trans rfl
    _ = _ := congrArg (Ideal.comap (f.app W.1).hom) this

end GlobalTheory.IdealGlue

namespace GlobalTheory.IdealGlue

lemma ideal_transfer {A A' B B' : CommRingCat.{u}} (φ : A ⟶ B) (φ' : A' ⟶ B') (ρ : A ⟶ A')
    (ρ' : B ⟶ B') (hc : ρ ≫ φ' = φ ≫ ρ') (hb : Function.Bijective φ.hom)
    (hb' : Function.Bijective φ'.hom) (𝔞 : Ideal B) :
    (𝔞.comap φ.hom).map ρ.hom = (𝔞.map ρ'.hom).comap φ'.hom := by
  calc (𝔞.comap φ.hom).map ρ.hom
      = (((𝔞.comap φ.hom).map ρ.hom).map φ'.hom).comap φ'.hom :=
        (Ideal.comap_map_of_bijective _ hb').symm
    _ = (((𝔞.comap φ.hom).map φ.hom).map ρ'.hom).comap φ'.hom := by
        rw [Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hc]
    _ = (𝔞.map ρ'.hom).comap φ'.hom := by rw [Ideal.map_comap_of_surjective _ hb.2]

lemma loc_map {P X : Scheme.{u}} (f : P ⟶ X) [IsOpenImmersion f] (J : P.IdealSheafData)
    (W W' : X.affineOpens) (hle : W' ≤ W) (hW : W.1 ≤ f.opensRange)
    (h : IsAffineOpen (f ⁻¹ᵁ W.1)) (h' : IsAffineOpen (f ⁻¹ᵁ W'.1)) :
    (loc f J W h).map (X.presheaf.map (homOfLE hle).op).hom = loc f J W' h' := by
  have hW' : W'.1 ≤ f.opensRange := (show W'.1 ≤ W.1 from hle).trans hW
  have hJ := J.map_ideal' (U := ⟨f ⁻¹ᵁ W'.1, h'⟩) (V := ⟨f ⁻¹ᵁ W.1, h⟩)
    ((TopologicalSpace.Opens.map f.base).map (homOfLE hle).op.unop).op
  exact (ideal_transfer _ _ _ _ (f.naturality (homOfLE hle).op) (app_bijective f W.1 hW)
    (app_bijective f W'.1 hW') _).trans (congrArg _ hJ)

lemma loc_indep {X : Scheme.{u}} {ι : Type*} (P : ι → Scheme.{u}) (e : ∀ i, P i ⟶ X)
    [∀ i, IsOpenImmersion (e i)] (K : ∀ i, (P i).IdealSheafData)
    (hK : ∀ i j (Q : Scheme.{u}) (a : Q ⟶ P i) (b : Q ⟶ P j), a ≫ e i = b ≫ e j →
      (K i).comap a = (K j).comap b)
    (i j : ι) (W : X.affineOpens) (hi : W.1 ≤ (e i).opensRange) (hj : W.1 ≤ (e j).opensRange)
    (h : IsAffineOpen ((e i) ⁻¹ᵁ W.1)) (h' : IsAffineOpen ((e j) ⁻¹ᵁ W.1)) :
    loc (e i) (K i) W h = loc (e j) (K j) W h' := by
  have hc := pullback.condition (f := e i) (g := e j)
  have hr : W.1 ≤ (pullback.fst (e i) (e j) ≫ e i).opensRange := by
    intro x hx
    have : x ∈ Set.range (pullback.fst (e i) (e j) ≫ e i) := by
      rw [IsOpenImmersion.range_pullback_to_base_of_left]
      exact ⟨hi hx, hj hx⟩
    exact this
  have hr' : W.1 ≤ (pullback.snd (e i) (e j) ≫ e j).opensRange := by
    intro x hx
    have : x ∈ Set.range (pullback.snd (e i) (e j) ≫ e j) := by
      rw [← hc]
      exact hr hx
    exact this
  rw [← loc_comp (pullback.fst (e i) (e j)) (e i) (K i) W hr
      (W.2.preimage_of_isOpenImmersion _ hr) h,
    ← loc_comp (pullback.snd (e i) (e j)) (e j) (K j) W hr'
      (W.2.preimage_of_isOpenImmersion _ hr') h']
  exact loc_congr hc (hK i j _ _ _ hc) _ _ _

theorem idealSheaf_glue_of_openImmersions :
    (∀ {X : Scheme.{0}} (𝒜 : Set X.affineOpens), (∀ W ∈ 𝒜, ∀ W' : X.affineOpens, W' ≤ W → W' ∈ 𝒜) →
      (∀ x : X, ∃ W ∈ 𝒜, x ∈ W.1) → ∀ (k : ∀ W : X.affineOpens, Ideal Γ(X, W)),
      (∀ W ∈ 𝒜, ∀ (W' : X.affineOpens) (h : W' ≤ W),
        (k W).map (X.presheaf.map (homOfLE h).op).hom = k W') →
      ∃ I : X.IdealSheafData, ∀ W ∈ 𝒜, I.ideal W = k W) →
    ∀ {X : Scheme.{0}} {ι : Type*} (P : ι → Scheme.{0}) (e : ∀ i, P i ⟶ X),
      (∀ i, IsOpenImmersion (e i)) → (∀ x : X, ∃ i, x ∈ Set.range (e i)) →
      ∀ (K : ∀ i, (P i).IdealSheafData),
      (∀ i j (Q : Scheme.{0}) (a : Q ⟶ P i) (b : Q ⟶ P j), a ≫ e i = b ≫ e j →
        (K i).comap a = (K j).comap b) →
      ∃ I : X.IdealSheafData, ∀ i, I.comap (e i) = K i := by
  intro hA X ι P e he hcov K hK
  classical
  have haff : ∀ i (W : X.affineOpens), W.1 ≤ (e i).opensRange → IsAffineOpen ((e i) ⁻¹ᵁ W.1) :=
    fun i W hW => W.2.preimage_of_isOpenImmersion (e i) hW
  let k : ∀ W : X.affineOpens, Ideal Γ(X, W) := fun W =>
    if hex : ∃ i, W.1 ≤ (e i).opensRange then
      loc (e hex.choose) (K hex.choose) W (haff _ W hex.choose_spec) else ⊤
  have hk : ∀ i (W : X.affineOpens) (hW : W.1 ≤ (e i).opensRange),
      k W = loc (e i) (K i) W (haff i W hW) := by
    intro i W hW
    have hex : ∃ i, W.1 ≤ (e i).opensRange := ⟨i, hW⟩
    simp only [k, dif_pos hex]
    exact loc_indep P e K hK _ _ W hex.choose_spec hW _ _
  have hcov' : ∀ x : X, ∃ W : X.affineOpens, ∃ i, W.1 ≤ (e i).opensRange ∧ x ∈ W.1 := by
    intro x
    obtain ⟨i, y, rfl⟩ := hcov x
    obtain ⟨W, hW, hxW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show e i y ∈ (e i).opensRange from ⟨y, rfl⟩)
    exact ⟨⟨W, hW⟩, i, hWle, hxW⟩
  obtain ⟨I, hI⟩ := hA {W | ∃ i, W.1 ≤ (e i).opensRange}
    (fun W ⟨i, hi⟩ W' hW' => ⟨i, (show W'.1 ≤ W.1 from hW').trans hi⟩)
    (fun x => by
      obtain ⟨W, i, hi, hx⟩ := hcov' x
      exact ⟨W, ⟨i, hi⟩, hx⟩)
    k
    (fun W ⟨i, hi⟩ W' hW' => by
      have hi' : W'.1 ≤ (e i).opensRange := (show W'.1 ≤ W.1 from hW').trans hi
      rw [hk i W hi, hk i W' hi']
      exact loc_map (e i) (K i) W W' hW' hi _ _)
  refine ⟨I, fun i => ?_⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := {W : X.affineOpens // W.1 ≤ (e i).opensRange})
    (fun W => ⟨(e i) ⁻¹ᵁ W.1.1, haff i W.1 W.2⟩) ?_ ?_
  · rw [eq_top_iff]
    intro y _
    obtain ⟨W, hW, hyW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show e i y ∈ (e i).opensRange from ⟨y, rfl⟩)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWle⟩, hyW⟩
  · intro W
    apply Ideal.comap_injective_of_surjective _ (app_bijective (e i) W.1.1 W.2).2
    have h1 := loc_comap (e i) I W.1 W.2 (haff i W.1 W.2)
    have h2 := hk i W.1 W.2
    have h3 := hI W.1 ⟨i, W.2⟩
    exact h1.trans (h3.trans h2)

end GlobalTheory.IdealGlue
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

namespace GlobalTheory.SubschemeIntegral

theorem isPreirreducible_univ_of_cover {X : Type*} [TopologicalSpace X] {ι : Type*} (U : ι → Set X)
    (hU : ∀ a, IsOpen (U a)) (hcov : ∀ x, ∃ a, x ∈ U a) (hirr : ∀ a, IsPreirreducible (U a))
    (hmeet : ∀ a b, (U a).Nonempty → (U b).Nonempty → (U a ∩ U b).Nonempty) :
    IsPreirreducible (Set.univ : Set X) := by
  intro u v hu hv ⟨x, _, hxu⟩ ⟨y, _, hyv⟩
  obtain ⟨a, hxa⟩ := hcov x
  obtain ⟨b, hyb⟩ := hcov y
  obtain ⟨z, hza, hzu, hzb⟩ := hirr a u (U b) hu (hU b) ⟨x, hxa, hxu⟩
    (by obtain ⟨w, h1, h2⟩ := hmeet a b ⟨x, hxa⟩ ⟨y, hyb⟩; exact ⟨w, h1, h2⟩)
  obtain ⟨w, _, hw⟩ := hirr b u v hu hv ⟨z, hzb, hzu⟩ ⟨y, hyb, hyv⟩
  exact ⟨w, trivial, hw⟩

theorem fromSpec_mem_support {Y : Scheme.{0}} (I : Y.IdealSheafData) (U : Y.affineOpens)
    (hU : IsAffineOpen U.1) (P : PrimeSpectrum Γ(Y, U.1)) (h : I.ideal U ≤ P.asIdeal) :
    hU.fromSpec P ∈ (I.support : Set Y) := by
  have hmem : hU.fromSpec P ∈ U.1 := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨P, rfl⟩
  change hU.fromSpec P ∈ I.support
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hmem]
  have : hU.fromSpec P ∈ hU.fromSpec '' PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(Y, U.1)) :=
    ⟨P, (PrimeSpectrum.mem_zeroLocus _ _).mpr h, rfl⟩
  rw [hU.fromSpec_image_zeroLocus] at this
  exact this.1

theorem exists_cover {Y : Scheme.{0}} (I : Y.IdealSheafData) {ι : Type} (W : ι → Y.affineOpens)
    (hW : ⨆ a, (W a).1 = ⊤) (x : I.subscheme) :
    ∃ a y, (I.subschemeCover.f (W a)) y = x := by
  have hx : I.subschemeι x ∈ (⨆ a, (W a).1) := by rw [hW]; trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  haveI := I.subschemeCover.map_prop (W a)
  have : x ∈ (I.subschemeCover.f (W a)).opensRange := by
    rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]; exact ha
  obtain ⟨y, hy⟩ := this
  exact ⟨a, y, hy⟩

theorem isEmpty_spec_top {Y : Scheme.{0}} (I : Y.IdealSheafData) (U : Y.affineOpens)
    (h : I.ideal U = ⊤) : IsEmpty (Spec (I.subschemeCover.X U)) := by
  haveI : Subsingleton (Γ(Y, U) ⧸ I.ideal U) := Ideal.Quotient.subsingleton_iff.mpr h
  refine ⟨fun y => ?_⟩
  have : Subsingleton (I.subschemeCover.X U) := this
  exact y.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr (by rw [Subsingleton.elim (1 : I.subschemeCover.X U) 0]; exact zero_mem _))

theorem isIntegral_or_isEmpty_subscheme : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData) (ι : Type) (W : ι → Y.affineOpens), (⨆ a, (W a).1 = ⊤) → (∀ a, I.ideal (W a) = ⊤ ∨ (I.ideal (W a)).IsPrime) → (∀ a b (ha : (I.ideal (W a)).IsPrime), I.ideal (W b) ≠ ⊤ → (W a).2.fromSpec ⟨I.ideal (W a), ha⟩ ∈ (W b).1) → IsIntegral I.subscheme ∨ IsEmpty I.subscheme := by
  intro Y I ι W hW hI hm
  by_cases hex : ∃ a, (I.ideal (W a)).IsPrime
  · left
    obtain ⟨a₀, ha₀⟩ := hex
    haveI hred : ∀ a, _root_.IsReduced (I.subschemeCover.X (W a)) := by
      intro a
      rcases hI a with h | h
      · haveI : Subsingleton (Γ(Y, W a) ⧸ I.ideal (W a)) := Ideal.Quotient.subsingleton_iff.mpr h
        change _root_.IsReduced (Γ(Y, W a) ⧸ I.ideal (W a)); infer_instance
      · haveI := h
        change _root_.IsReduced (Γ(Y, W a) ⧸ I.ideal (W a)); infer_instance
    let 𝒰 : I.subscheme.OpenCover := Scheme.Cover.mkOfCovers ι (fun a => Spec (I.subschemeCover.X (W a)))
      (fun a => I.subschemeCover.f (W a)) (exists_cover I W hW) (fun a => I.subschemeCover.map_prop (W a))
    haveI : ∀ a : 𝒰.I₀, AlgebraicGeometry.IsReduced (𝒰.X a) := fun a => by
      change AlgebraicGeometry.IsReduced (Spec (I.subschemeCover.X (W a))); haveI := hred a; infer_instance
    haveI : AlgebraicGeometry.IsReduced I.subscheme := IsReduced.of_openCover I.subscheme 𝒰
    have hpt : ∀ a (ha : (I.ideal (W a)).IsPrime), ∃ x : I.subscheme,
        I.subschemeι x = (W a).2.fromSpec ⟨I.ideal (W a), ha⟩ := by
      intro a ha
      have := fromSpec_mem_support I (W a) (W a).2 ⟨I.ideal (W a), ha⟩ le_rfl
      rw [← I.range_subschemeι] at this
      exact this
    have hrange : ∀ a (x : I.subscheme), I.subschemeι x ∈ (W a).1 → x ∈ Set.range (I.subschemeCover.f (W a)) := by
      intro a x hx
      haveI := I.subschemeCover.map_prop (W a)
      have : x ∈ (I.subschemeCover.f (W a)).opensRange := by
        rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]; exact hx
      exact this
    have hp : ∀ a, (Set.range (I.subschemeCover.f (W a))).Nonempty → (I.ideal (W a)).IsPrime := by
      rintro a ⟨_, y, _⟩
      rcases hI a with h | h
      · exact ((isEmpty_spec_top I (W a) h).false y).elim
      · exact h
    haveI : IrreducibleSpace I.subscheme := by
      obtain ⟨x₀, -⟩ := hpt a₀ ha₀
      have hpre : IsPreirreducible (Set.univ : Set I.subscheme) := by
        refine isPreirreducible_univ_of_cover (fun a => Set.range (I.subschemeCover.f (W a))) (fun a => ?_)
          (fun x => ?_) (fun a => ?_) (fun a b ha hb => ?_)
        · haveI := I.subschemeCover.map_prop (W a); exact (I.subschemeCover.f (W a)).isOpenEmbedding.isOpenMap.isOpen_range
        · obtain ⟨a, y, hy⟩ := exists_cover I W hW x; exact ⟨a, y, hy⟩
        · rcases hI a with h | h
          · haveI := isEmpty_spec_top I (W a) h
            rw [Set.range_eq_empty]; exact isPreirreducible_empty
          · haveI : IsDomain (I.subschemeCover.X (W a)) := by
              change IsDomain (Γ(Y, W a) ⧸ I.ideal (W a)); haveI := h; infer_instance
            rw [← Set.image_univ]
            exact ((IrreducibleSpace.isIrreducible_univ _).image _
              (I.subschemeCover.f (W a)).continuous.continuousOn).isPreirreducible
        · obtain ⟨x, hx⟩ := hpt a (hp a ha)
          refine ⟨x, hrange a x ?_, hrange b x ?_⟩
          · rw [hx, ← SetLike.mem_coe, ← (W a).2.range_fromSpec]; exact ⟨_, rfl⟩
          · rw [hx]; exact hm a b (hp a ha) (hp b hb).ne_top
      haveI : PreirreducibleSpace I.subscheme := ⟨hpre⟩
      exact { toNonempty := ⟨x₀⟩ }
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  · right
    refine ⟨fun x => ?_⟩
    obtain ⟨a, y, -⟩ := exists_cover I W hW x
    have h : I.ideal (W a) = ⊤ := (hI a).resolve_right (fun h => hex ⟨a, h⟩)
    exact (isEmpty_spec_top I (W a) h).false y

end GlobalTheory.SubschemeIntegral
end

section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

private theorem app_comp_ι_eq_zero_iff {T S : Scheme.{0}} (U : S.Opens) (g : T ⟶ U) (V : U.toScheme.Opens) (x : Γ(S, U.ι ''ᵁ V)) :
    ((g ≫ U.ι).app (U.ι ''ᵁ V)).hom x = 0 ↔ (g.app V).hom x = 0 := by
  have e : (g ≫ U.ι).app (U.ι ''ᵁ V) = g.app V ≫ T.presheaf.map (eqToHom (by simp)).op := by
    simp only [Scheme.Hom.comp_app, Scheme.Opens.ι_app]
    refine (g.naturality (homOfLE (U.ι.preimage_image_eq V).le).op).trans ?_
    congr 2
  rw [e]
  exact map_eq_zero_iff (T.presheaf.map _).hom (ConcreteCategory.bijective_of_isIso _).1

private theorem restrict_app_eq_zero_iff {T S : Scheme.{0}} (f : T ⟶ S) (U : S.Opens) (V : U.toScheme.Opens) (a : Γ(S, U.ι ''ᵁ V)) :
    ((f ∣_ U).app V).hom a = 0 ↔ (f.app (U.ι ''ᵁ V)).hom a = 0 := by
  rw [morphismRestrict_app]
  exact map_eq_zero_iff (T.presheaf.map _).hom (ConcreteCategory.bijective_of_isIso _).1

private theorem app_res_eq_zero {S T : Scheme.{0}} (t : T ⟶ S) {V W : S.Opens} (h : V ≤ W) (b : Γ(S, W))
    (hb : (t.app W).hom b = 0) : (t.app V).hom ((S.presheaf.map (homOfLE h).op).hom b) = 0 := by
  have e := congrArg (fun φ => φ.hom b) (t.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e, hb, map_zero]

theorem exists_pow_mul_app_eq_zero_near_of_represented : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop), (∀ (T T' : Scheme.{0}) (t : T ⟶ S) (u : T' ⟶ T), Φ T t → Φ T' (u ≫ t)) → ∀ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), IsClosedImmersion i → (∀ (T : Scheme.{0}) (t : T ⟶ U), Φ T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t) → ∀ (W : S.Opens) (s c : Γ(S, W)), (∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app (S.basicOpen s)).hom ((S.presheaf.map (homOfLE (S.basicOpen_le s)).op).hom c) = 0) → ∀ y : S, y ∈ U → y ∈ W → ∃ (V : S.Opens) (hV : V ≤ W), y ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0 := by
  intro S Φ hstab U Z i hi hrep W s c hc y hyU hyW
  have hm : (⟨y, hyU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ W := hyW
  obtain ⟨V', hV'aff, hyV', hV'le⟩ := (Opens.isBasis_iff_nbhd.mp U.toScheme.isBasis_affineOpens) hm
  have hV : U.ι ''ᵁ V' ≤ W := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := hx
    exact hV'le hx'
  refine ⟨U.ι ''ᵁ V', hV, ⟨⟨y, hyU⟩, hyV', rfl⟩, ?_⟩
  set V : S.Opens := U.ι ''ᵁ V' with hVdef
  set p : Z ⟶ S := i ≫ U.ι with hpdef
  let cV : Γ(S, V) := (S.presheaf.map (homOfLE hV).op).hom c
  let sV : Γ(S, V) := (S.presheaf.map (homOfLE hV).op).hom s
  have hpre : p ⁻¹ᵁ V = i ⁻¹ᵁ V' := by
    rw [hpdef, Scheme.Hom.comp_preimage, hVdef, U.ι.preimage_image_eq V']
  have hcpt : IsCompact ((p ⁻¹ᵁ V : Z.Opens) : Set Z) := by
    rw [hpre]
    exact QuasiCompact.isCompact_preimage (f := i) _ V'.2 hV'aff.isCompact
  have hΦi : Φ Z p := (hrep Z i).2 ⟨𝟙 _, Category.id_comp _⟩
  have h0 := hc Z p hΦi
  have h1 := app_res_eq_zero p (inf_le_right : V ⊓ S.basicOpen s ≤ S.basicOpen s) _ h0
  have hres : (S.presheaf.map (homOfLE (inf_le_left : V ⊓ S.basicOpen s ≤ V)).op).hom cV =
      (S.presheaf.map (homOfLE (inf_le_right : V ⊓ S.basicOpen s ≤ S.basicOpen s)).op).hom
        ((S.presheaf.map (homOfLE (S.basicOpen_le s)).op).hom c) := by
    simp only [cV, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have key : ∀ (O : Z.Opens) (_ : O = p ⁻¹ᵁ (V ⊓ S.basicOpen s)) (h : O ≤ p ⁻¹ᵁ V),
      (Z.presheaf.map (homOfLE h).op).hom ((p.app V).hom cV) = 0 := by
    rintro O rfl h
    have e := congrArg (fun φ => φ.hom cV) (p.naturality (homOfLE (inf_le_left : V ⊓ S.basicOpen s ≤ V)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    refine e.symm.trans ?_
    rw [hres]
    exact h1
  have hO : Z.basicOpen ((p.app V).hom sV) = p ⁻¹ᵁ (V ⊓ S.basicOpen s) := by
    rw [← Scheme.preimage_basicOpen, Scheme.basicOpen_res]
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact Z hcpt
    ((p.app V).hom cV) ((p.app V).hom sV) (key _ hO _)
  have hpa : (p.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0 := by
    rw [map_mul, map_pow, map_mul, map_pow]
    exact hn
  have hia := (app_comp_ι_eq_zero_iff U i V' _).1 hpa
  refine ⟨n, fun T t ht => ?_⟩
  have ht' : Φ _ ((t ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι]
    exact hstab _ _ t _ ht
  obtain ⟨z, hz⟩ := (hrep _ (t ∣_ U)).1 ht'
  refine (restrict_app_eq_zero_iff t U V' _).1 ?_
  rw [← hz, Scheme.Hom.comp_app]
  exact (congrArg (fun x => (z.app (i ⁻¹ᵁ V')).hom x) hia).trans (map_zero _)
end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_factor_closedImmersion_of_locally :
    ∀ (Z A Y : Scheme.{0}) (a : A ⟶ Z), IsClosedImmersion a → ∀ (g : Y ⟶ Z),
      (∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ ∃ z : W.toScheme ⟶ A, z ≫ a = W.ι ≫ g) →
      ∃ z : Y ⟶ A, z ≫ a = g := by
  intro Z A Y a ha g h
  choose W hW z hz using h
  have hc : TopologicalSpace.IsOpenCover W := by
    refine TopologicalSpace.IsOpenCover.mk ?_
    rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩
  let 𝒰 := Y.openCoverOfIsOpenCover W hc
  obtain ⟨u, hu⟩ : ∃ u : ∀ i, 𝒰.X i ⟶ A, ∀ i, u i ≫ a = 𝒰.f i ≫ g := ⟨z, hz⟩
  have hglue : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ u i =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ u j := by
    intro i j
    rw [← cancel_mono a, Category.assoc, Category.assoc, hu, hu, pullback.condition_assoc]
  refine ⟨𝒰.glueMorphisms u hglue, ?_⟩
  refine 𝒰.hom_ext _ _ fun i => ?_
  rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
  exact hu i

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory

theorem faithfullyFlat_app_of_isAffineHom_flat_surjective :
    ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (V : Y.Opens), IsAffineHom p → Flat p → Surjective p →
      IsAffineOpen V → (p.app V).hom.FaithfullyFlat := by
  intro X Y p V _ _ _ hV
  have hpre : IsAffineOpen (p ⁻¹ᵁ V) := hV.preimage p
  have : IsAffine V := hV
  have : IsAffine (p ⁻¹ᵁ V) := hpre
  have : Flat (p ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p V).flip ‹Flat p›
  have : Surjective (p ∣_ V) := IsZariskiLocalAtTarget.restrict ‹Surjective p› V
  have hff := (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (p ∣_ V)).mp
    ⟨inferInstance, inferInstance⟩
  rw [morphismRestrict_appTop] at hff
  have hff' := (RingHom.FaithfullyFlat.respectsIso.cancel_right_isIso
    (p.app (V.ι ''ᵁ ⊤)) (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p V ⊤)).op)).mp hff
  rwa [Scheme.Opens.ι_image_top] at hff'

end GlobalTheory
end
