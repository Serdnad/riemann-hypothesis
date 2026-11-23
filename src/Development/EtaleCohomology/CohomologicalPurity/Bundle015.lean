module

public import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Order.CompletePartialOrder
public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

theorem LeafOff_of : LeafOff := by
  intro d P F
  apply le_antisymm F.h
  intro y hy
  change y ∉ PrimeSpectrum.zeroLocus (F.I : Set F.B)
  intro hz
  have hk : RingHom.ker (Ideal.Quotient.mk F.I) = F.I := Ideal.mk_ker
  have hr : y ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk F.I)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, hk]; exact hz
  obtain ⟨y0, rfl⟩ := hr
  have hw := congrArg (fun g => g.base y0) F.cart.w
  simp only [Scheme.Hom.comp_base] at hw
  have hU : F.w.base ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I))).base y0) ∈ (P.U : Set P.X) := hy
  rw [P.hU] at hU
  exact hU ⟨F.z.base y0, hw.symm⟩

end LateralTheory.CohomologicalPurity.Cl
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Cl

theorem range_frame_ι {d : ℕ} {P : SP d} (F : Frame P) :
    ((off F.B F.I : (Spec (CommRingCat.of F.B)).Opens) : Set (Spec (CommRingCat.of F.B))) =
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I))))ᶜ := by
  have h := range_comap_of_surjective (f := Ideal.Quotient.mk F.I) (hf :=
    Ideal.Quotient.mk_surjective)
  rw [Ideal.mk_ker] at h
  change (PrimeSpectrum.zeroLocus (F.I : Set F.B))ᶜ = _
  rw [← h]
  rfl

def Frame.sp {d : ℕ} {P : SP d} (F : Frame P) (hw : Etale F.w) : SP d where
  X := Spec (CommRingCat.of F.B)
  Z := Spec (CommRingCat.of (F.B ⧸ F.I))
  S := P.S
  p := F.w ≫ P.p
  ι := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I))
  e := P.e
  U := off F.B F.I
  cl := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  smX := by
    have := P.smX
    have : SmoothOfRelativeDimension 0 F.w := inferInstance
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + (P.e + d)) (F.w ≫ P.p))
  smZ := by
    have hz : Etale F.z := MorphismProperty.of_isPullback F.cart hw
    have := P.smZ
    have : SmoothOfRelativeDimension 0 F.z := inferInstance
    have e : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I)) ≫ F.w ≫ P.p = F.z ≫ P.ι ≫ P.p := by
      rw [← Category.assoc, F.cart.w, Category.assoc]
    rw [e]
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + P.e) (F.z ≫ P.ι ≫ P.p))
  hU := range_frame_ι F

theorem LeafVanF_of (hV : LeafVan) : LeafVanF := by
  intro hH d q _ P hq F hw i
  refine hV hH d q (F.sp hw) ?_ i
  have h := hq.map F.w.appTop.hom
  rw [map_natCast] at h
  exact h

end LateralTheory.CohomologicalPurity.Cl
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Cl

theorem sub_C_mem_X {σ R : Type} [CommRing R] (f : MvPolynomial σ R) :
    f - MvPolynomial.C (MvPolynomial.constantCoeff f) ∈ Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ R)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr =>
    have : p + r - MvPolynomial.C (MvPolynomial.constantCoeff (p + r)) =
      (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) + (r - MvPolynomial.C (MvPolynomial.constantCoeff r)) := by
      simp only [map_add (f := _)]; ring
    rw [this]; exact add_mem hp hr
  | mul_X p n _ =>
    simp only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨n, rfl⟩)

theorem chart_nbhd {d : ℕ} {A B : Type} [CommRing A] [CommRing B] (I : Ideal A) (φ : A →+* B)
    (ψ : MvPolynomial (Fin d) (A ⧸ I) →+* B) (hφ : Nbhd φ I) (hψ : ψ.Etale)
    (hJ : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ = I.map φ)
    (hc : ∀ a : A, φ a - ψ (MvPolynomial.C (Ideal.Quotient.mk I a)) ∈ I.map φ) :
    Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) := by
  refine ⟨hψ, ?_, ?_⟩
  · set_option synthInstance.maxHeartbeats 200000 in
    apply (injective_iff_map_eq_zero _).2
    intro f hf
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, hJ] at hf
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (MvPolynomial.constantCoeff f)
    have h1 : ψ (f - MvPolynomial.C (MvPolynomial.constantCoeff f)) ∈ I.map φ := by
      rw [← hJ]; exact Ideal.mem_map_of_mem _ (sub_C_mem_X f)
    have h2 : φ a ∈ I.map φ := by
      have := sub_mem (add_mem (hc a) (sub_mem hf h1)) (0 : I.map φ).2
      rw [map_sub, ← ha] at this
      simpa using this
    have h3 : Ideal.Quotient.mk I a = 0 := by
      apply hφ.2.1
      rw [Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]
      exact h2
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have := sub_C_mem_X f
    rwa [← ha, h3, map_zero, sub_zero] at this
  · intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨a', ha'⟩ := hφ.2.2 (Ideal.Quotient.mk _ b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
    refine ⟨Ideal.Quotient.mk _ (MvPolynomial.C (Ideal.Quotient.mk I a)), ?_⟩
    rw [Ideal.quotientMap_mk] at ha' ⊢
    rw [Ideal.Quotient.eq] at ha' ⊢
    rw [hJ]
    have := sub_mem ha' (hc a)
    simpa using this

theorem LeafVanRing_of (hNb : LeafNb) (hTh : LeafThom) : LeafVanRing := by
  intro hH d q _ A _ I hC hq n i hn
  have hA1 : A1 := hH.1
  have hA9 : A9 := hH.2.2.2.2.2.2.1
  obtain ⟨B, _, φ, ψ, hφ, hψ, hI, hc⟩ := hC
  have hJ : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ = I.map φ := by
    rw [Ideal.map_span, hI, ← Set.range_comp]; rfl
  have hN := chart_nbhd I φ ψ hφ hψ hJ hc
  have e1 := hNb hA1 q φ I (I.map φ) hφ rfl (off_map φ I).le n i
  have e2 := hNb hA1 q ψ _ _ hN rfl (off_map ψ _).le n i
  obtain ⟨th, hth⟩ := hTh hH d
  have hqR : IsUnit (q : A ⧸ I) := by simpa using hq.map (Ideal.Quotient.mk I)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 * d := ⟨n - 2 * d, by ring⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + d := ⟨i - d, by ring⟩
  have hm : m < 0 := by omega
  have hsub : Subsingleton (Ht q (sp (A ⧸ I)) m j) := (hA9 (ZMod q) (tw q j)).1 _ m hm
  have h3 := ((hth q).2.2.1 (A ⧸ I) _ rfl hqR m j).2
  have hR : Subsingleton (Hs q (opn (off (MvPolynomial (Fin d) (A ⧸ I))
      (Ideal.span (Set.range MvPolynomial.X)))) (m + 2 * d) (j + d)) := by
    constructor; intro x y
    obtain ⟨a, rfl⟩ := h3 x; obtain ⟨b, rfl⟩ := h3 y; rw [Subsingleton.elim a b]
  have hB : ∀ x y : Hs q (opn (off B ((Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ))) (m + 2 * d) (j + d), x = y := by
    intro x y
    obtain ⟨a, rfl⟩ := e2.2 x; obtain ⟨b, rfl⟩ := e2.2 y; rw [Subsingleton.elim a b]
  rw [hJ] at hB
  exact ⟨fun x y => e1.1 (hB _ _)⟩

end LateralTheory.CohomologicalPurity.Cl
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Cl

def LeafGenCart : Prop := ∀ {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.affineOpens) (r : Γ(X, V.1)),
  ∃ z : Spec (CommRingCat.of (Localization.Away r ⧸ (ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))) ⟶ Z,
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))) z
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec) ι

def LeafGenKer : Prop := ∀ {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.affineOpens) (r : Γ(X, V.1)),
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))))).ker =
    ι.ker.comap (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec)

theorem LeafGenCart_of (hK : LeafGenKer) : LeafGenCart := by
  intro X Z ι _ V r
  have hK' := hK ι V r
  have hm : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of (Localization.Away r)) _
  have hfst := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion ι
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec)
  let e := IsClosedImmersion.lift (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1)
    (Localization.Away r))) ≫ V.2.fromSpec) ι) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))))) (by rw [hfst, hK'])
  refine ⟨e ≫ pullback.snd _ _, isPullback_of_isClosedImmersion _ ι _ _ ?_ hK'.symm⟩
  rw [Category.assoc, ← pullback.condition, IsClosedImmersion.lift_fac_assoc]

theorem span_loc {d : ℕ} {A : Type} [CommRing A] (I : Ideal A) (a : Fin d → A) (r : A) (ha : ∀ j, a j ∈ I)
    (hra : ∀ y ∈ I, r * y ∈ Ideal.span (Set.range a)) :
    Ideal.span (Set.range (algebraMap A (Localization.Away r) ∘ a)) = I.map (algebraMap A (Localization.Away r)) := by
  rw [Set.range_comp, ← Ideal.map_span]
  apply le_antisymm
  · exact Ideal.map_mono (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact ha j))
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap]
    have hu : IsUnit (algebraMap A (Localization.Away r) r) := IsLocalization.Away.algebraMap_isUnit r
    have h1 : algebraMap A (Localization.Away r) (r * y) ∈ (Ideal.span (Set.range a)).map (algebraMap A (Localization.Away r)) :=
      Ideal.mem_map_of_mem _ (hra y hy)
    rw [map_mul] at h1
    obtain ⟨u, hu'⟩ := hu
    have := Ideal.mul_mem_left _ (↑u⁻¹ : Localization.Away r) h1
    rwa [← hu', ← mul_assoc, Units.inv_mul, one_mul] at this

theorem LeafGen_of (hC : LeafChart) (hGR : LeafGenRing) (hKer : LeafGenKer) : LeafGen := by
  have hCart : LeafGenCart := LeafGenCart_of @hKer
  intro d P x hx
  obtain ⟨V, hxV, -, hfg, hch⟩ := hC d P x ⊤ trivial
  obtain ⟨a, r, hr1, ha, hra⟩ := hGR d Γ(P.X, V.1) (P.ι.ker.ideal V) hfg hch
  have := P.cl
  obtain ⟨z, hz⟩ := hCart P.ι V r
  have hxr : x ∈ Set.range P.ι := by
    by_contra h; exact hx (by rw [← SetLike.mem_coe, P.hU]; exact h)
  refine ⟨⟨Localization.Away r, (P.ι.ker.ideal V).map (algebraMap _ _), algebraMap _ _ ∘ a,
    span_loc _ a r ha hra, Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ V.2.fromSpec, z, ?_, hz⟩, ?_, ?_⟩
  · intro y hy
    change (_ ≫ V.2.fromSpec) y ∈ P.U
    rw [← SetLike.mem_coe, P.hU]
    rintro ⟨t, ht⟩
    obtain ⟨s, hs, -⟩ := Scheme.exists_preimage_of_isPullback hz y t ht.symm
    apply hy
    rw [← hs]
    intro g hg
    change Ideal.Quotient.mk _ g ∈ s.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg]; exact zero_mem _
  · change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ V.2.fromSpec)
    have h1 := Scheme.isOpenImmersion_SpecMap_localizationAway (R := Γ(P.X, V.1)) r
    have h2 := V.2.isOpenImmersion_fromSpec
    infer_instance
  · have hxV' : x ∈ (V.1 : Set P.X) := hxV
    rw [← V.2.range_fromSpec] at hxV'
    obtain ⟨p, hp⟩ := hxV'
    have hz0 : x ∈ P.X.zeroLocus (U := V.1) (P.ι.ker.ideal V) := by
      rw [← Scheme.IdealSheafData.mem_support_iff_of_mem hxV, ← SetLike.mem_coe, Scheme.Hom.support_ker]; exact subset_closure hxr
    have hIp : ∀ g ∈ P.ι.ker.ideal V, g ∈ p.asIdeal := by
      intro g hg
      have h1 := (Scheme.mem_zeroLocus_iff _ _ _).1 hz0 g hg
      by_contra h2
      apply h1
      rw [← hp]
      change p ∈ V.2.fromSpec ⁻¹ᵁ P.X.basicOpen g
      rw [V.2.fromSpec_preimage_basicOpen]; exact h2
    have hr : p ∈ PrimeSpectrum.basicOpen r := by
      intro h; apply p.2.ne_top; rw [Ideal.eq_top_iff_one]
      have := p.asIdeal.sub_mem h (hIp _ hr1); simpa using this
    have hr' : p ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(P.X, V.1) (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]; exact hr
    obtain ⟨q, hq⟩ := hr'
    refine ⟨q, ?_⟩
    show V.2.fromSpec ((Spec.map (CommRingCat.ofHom (algebraMap Γ(P.X, V.1) (Localization.Away r)))) q) = x
    rw [← hp]
    exact congrArg V.2.fromSpec hq

end LateralTheory.CohomologicalPurity.Cl
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.ZornPf
open LateralTheory.CohomologicalPurity.Cl

theorem rs_rs {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} {U V W : X.Opens} (h1 : U ≤ V) (h2 : V ≤ W)
    (a : Sec G W.toScheme) : rs h1 (rs h2 a) = rs (h1.trans h2) a := by
  change (G.obj.map (X.homOfLE h1).op).hom ((G.obj.map (X.homOfLE h2).op).hom a) = (G.obj.map (X.homOfLE _).op).hom a
  rw [← Scheme.homOfLE_homOfLE X h1 h2, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem rs_refl {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U)
    (a : Sec G U.toScheme) : rs h a = a := by
  change (G.obj.map (X.homOfLE h).op).hom a = a
  rw [Scheme.homOfLE_rfl X U]
  simp

theorem rs_sub {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V)
    (a b : Sec G V.toScheme) : rs h (a - b) = rs h a - rs h b := map_sub _ _ _

theorem rs_add {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V)
    (a b : Sec G V.toScheme) : rs h (a + b) = rs h a + rs h b := map_add _ _ _

theorem glue {R : Type} [CommRing R] (G : Shv R) {X : Scheme.{0}} {A : Type*} (V : A → X.Opens)
    (s : ∀ k, Sec G (V k).toScheme) (hc : ∀ k l, rs inf_le_left (s k) = rs inf_le_right (s l)) :
    ∃ c : Sec G (⨆ k, V k).toScheme, ∀ k, rs (le_iSup V k) c = s k := by
  have hG : Presheaf.IsSheaf (Scheme.etaleTopology) (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.property
  have hmem : Sieve.generate (Presieve.ofArrows (fun k => (V k).toScheme) (fun k => X.homOfLE (le_iSup V k)))
      ∈ Scheme.etaleTopology (⨆ k, V k).toScheme := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff (P := (@Etale : MorphismProperty Scheme.{0}))).2 ⟨fun x => ?_, fun i => ?_⟩
    · have hx : (x.1 : X) ∈ ⨆ k, V k := x.2
      rw [TopologicalSpace.Opens.mem_iSup] at hx
      obtain ⟨k, hk⟩ := hx
      refine ⟨k, ⟨⟨x.1, hk⟩, ?_⟩⟩
      apply Subtype.ext
      exact Scheme.homOfLE_apply (le_iSup V k) ⟨x.1, hk⟩
    · infer_instance
  have hS := hG.isSheafFor _ hmem
  rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hS
  obtain ⟨c, hc', -⟩ := hS s (by
    intro i j Z gi gj e
    have e' : gi ≫ (V i).ι = gj ≫ (V j).ι := by
      have := congrArg (· ≫ (⨆ k, V k).ι) e
      simpa using this
    have hr : Set.range (gi ≫ (V i).ι) ⊆ Set.range (V i ⊓ V j).ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      refine ⟨?_, ?_⟩
      · have : (gi ≫ (V i).ι) z ∈ Set.range (V i).ι := ⟨gi z, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
      · rw [e']
        have : (gj ≫ (V j).ι) z ∈ Set.range (V j).ι := ⟨gj z, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
    let l := IsOpenImmersion.lift (V i ⊓ V j).ι (gi ≫ (V i).ι) hr
    have hl : l ≫ (V i ⊓ V j).ι = gi ≫ (V i).ι := IsOpenImmersion.lift_fac _ _ _
    have li : gi = l ≫ X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) := by
      rw [← cancel_mono (V i).ι, Category.assoc, Scheme.homOfLE_ι, hl]
    have lj : gj = l ≫ X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) := by
      rw [← cancel_mono (V j).ι, Category.assoc, Scheme.homOfLE_ι, hl, e']
    change (G.obj.map gi.op).hom (s i) = (G.obj.map gj.op).hom (s j)
    rw [li, lj, op_comp, op_comp, Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply, LinearMap.comp_apply]
    exact congrArg (G.obj.map l.op).hom (hc i j))
  exact ⟨c, hc'⟩

theorem LeafZorn_of : LeafZorn := by
  intro R _ G X N hres hloc hfl W A V h a hcov hcomp
  let P : (Σ T : X.Opens, Sec G T.toScheme) → Prop :=
    fun p => ∀ k, rs inf_le_left p.2 - rs inf_le_right (a k) ∈ N (p.1 ⊓ V k)
  let r : {p // P p} → {p // P p} → Prop := fun p q => ∃ hh : p.1.1 ≤ q.1.1, rs hh q.1.2 = p.1.2
  have htrans : ∀ {p q s : {p // P p}}, r p q → r q s → r p s := by
    rintro p q s ⟨h1, e1⟩ ⟨h2, e2⟩
    exact ⟨h1.trans h2, by rw [← e1, ← e2, rs_rs]⟩
  have hchain : ∀ C : Set {p // P p}, IsChain r C → ∃ ub, ∀ p ∈ C, r p ub := by
    intro C hC
    let Vc : C → X.Opens := fun p => p.1.1.1
    obtain ⟨c, hc⟩ := glue G Vc (fun p : C => p.1.1.2) (by
      intro p q
      by_cases hpq : p.1 = q.1
      · obtain rfl : p = q := Subtype.ext hpq
        rfl
      · rcases hC p.2 q.2 hpq with ⟨hh, e⟩ | ⟨hh, e⟩
        · show rs inf_le_left p.1.1.2 = rs inf_le_right q.1.1.2
          rw [← e, rs_rs]
        · show rs inf_le_left p.1.1.2 = rs inf_le_right q.1.1.2
          rw [← e, rs_rs])
    refine ⟨⟨⟨⨆ p, Vc p, c⟩, fun k => ?_⟩, fun p hp => ⟨le_iSup Vc ⟨p, hp⟩, hc ⟨p, hp⟩⟩⟩
    apply hloc
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    change x ∈ (⨆ p, Vc p) at hx1
    rw [TopologicalSpace.Opens.mem_iSup] at hx1
    obtain ⟨p, hp⟩ := hx1
    have h' : Vc p ⊓ V k ≤ (⨆ p, Vc p) ⊓ V k := inf_le_inf_right _ (le_iSup Vc p)
    refine ⟨Vc p ⊓ V k, h', ⟨hp, hx2⟩, ?_⟩
    have key : rs h' (rs inf_le_left c - rs inf_le_right (a k)) =
        rs inf_le_left p.1.1.2 - rs inf_le_right (a k) := by
      rw [rs_sub, rs_rs, rs_rs, show rs (h'.trans inf_le_left) c = rs inf_le_left (rs (le_iSup Vc p) c) by
        rw [rs_rs], hc p]
    rw [key]
    exact p.1.2 k
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded hchain htrans
  have hVT : ∀ k, V k ≤ m.1.1 := by
    intro k
    have hd := m.2 k
    obtain ⟨n, hn, hnd⟩ := hfl _ _ inf_le_right _ hd
    let Vb : Bool → X.Opens := fun b => Bool.rec (V k) m.1.1 b
    have hn' := congrArg (rs (inf_comm (V k) m.1.1).le) hnd
    rw [rs_rs, rs_sub, rs_rs, rs_rs] at hn'
    obtain ⟨e, he⟩ := glue G Vb (fun b => Bool.rec (motive := fun b => Sec G (Vb b).toScheme) (a k + n) m.1.2 b) (by
      intro i j
      cases i <;> cases j
      · rfl
      · show rs inf_le_left (a k + n) = rs inf_le_right m.1.2
        rw [rs_add, hn']
        abel
      · show rs inf_le_left m.1.2 = rs inf_le_right (a k + n)
        rw [rs_add, hnd]
        abel
      · rfl)
    have hP : P ⟨⨆ b, Vb b, e⟩ := by
      intro l
      apply hloc
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      change x ∈ (⨆ b, Vb b) at hx1
      rw [TopologicalSpace.Opens.mem_iSup] at hx1
      obtain ⟨b, hb⟩ := hx1
      have h' : Vb b ⊓ V l ≤ (⨆ b, Vb b) ⊓ V l := inf_le_inf_right _ (le_iSup Vb b)
      refine ⟨Vb b ⊓ V l, h', ⟨hb, hx2⟩, ?_⟩
      have key : rs h' (rs inf_le_left e - rs inf_le_right (a l)) =
          rs inf_le_left (rs (le_iSup Vb b) e) - rs inf_le_right (a l) := by
        rw [rs_sub, rs_rs, rs_rs, rs_rs]
      rw [key, he b]
      cases b
      · show rs inf_le_left (a k + n) - rs inf_le_right (a l) ∈ N (V k ⊓ V l)
        rw [rs_add, show rs inf_le_left (a k) + rs inf_le_left n - rs inf_le_right (a l) =
          (rs inf_le_left (a k) - rs inf_le_right (a l)) + rs inf_le_left n by abel]
        exact add_mem (hcomp k l) (hres _ _ _ n hn)
      · exact m.2 l
    obtain ⟨hh, -⟩ := hm ⟨_, hP⟩ ⟨le_iSup Vb true, he true⟩
    exact (le_iSup Vb false).trans hh
  have hWT : W ≤ m.1.1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hcov x hx
    exact hVT k hk
  refine ⟨rs hWT m.1.2, fun k => ?_⟩
  have hk : V k ≤ m.1.1 ⊓ V k := le_inf (hVT k) le_rfl
  have key : rs hk (rs inf_le_left m.1.2 - rs inf_le_right (a k)) = rs (h k) (rs hWT m.1.2) - a k := by
    rw [rs_sub, rs_rs, rs_rs, rs_rs, rs_refl]
  rw [← key]
  exact hres _ _ hk _ (m.2 k)

end LateralTheory.CohomologicalPurity.ZornPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut.SumCut

def LeafChainsSum : Prop := ∀ (R : Type) [CommRing R] (A : Type) (E : A → Spc) (c : Cofan E), Nonempty (IsColimit c) →
  Nonempty (IsColimit (Cofan.mk ((chains R).obj c.pt) fun a => (chains R).map (c.inj a)))

def LeafHKSum : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) (K : A → Cx R) (c : Cofan K),
  Nonempty (IsColimit c) → ∀ n : ℤ, Function.Bijective fun (x : HK R c.pt F n) (a : A) => HK.pull R (c.inj a) F n x

end LateralTheory.CohomologicalPurity.TubeCut.SumCut

namespace LateralTheory.CohomologicalPurity.TubeCut
open SumCut

theorem LeafSum_of (hc : LeafChainsSum) (hk : LeafHKSum) : LeafSum := by
  intro R _ F A E c hc' n
  exact hk R F A (fun a => (chains R).obj (E a)) _ (hc R A E c hc') n

end LateralTheory.CohomologicalPurity.TubeCut
end
end
