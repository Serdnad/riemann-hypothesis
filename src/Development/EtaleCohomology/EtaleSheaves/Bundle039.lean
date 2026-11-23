module

public import Development.EtaleCohomology.EtaleSheaves.Bundle025
public import Development.EtaleCohomology.EtaleSheaves.Bundle026
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.CovPf

theorem aic_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (h : AIC A) : AIC B := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map (e.symm : B →+* A)) (hp.map _) (by
    rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  rw [Polynomial.eval_map] at ha
  have h2 := congrArg (e : A →+* B) ha
  rw [Polynomial.hom_eval₂, map_zero] at h2
  have h3 : ((e : A →+* B).comp (e.symm : B →+* A)) = RingHom.id B := by ext x; simp
  rw [h3] at h2
  exact h2

theorem aicsch_of_imm {W Z : Scheme.{0}} (i : W ⟶ Z) [IsOpenImmersion i] [Nonempty W] (hZ : AICSch Z) :
    AICSch W := by
  have : IsIntegral Z := hZ.1
  refine ⟨isIntegral_of_isOpenImmersion i, fun V hV hne => ?_⟩
  have h1 := hZ.2 (i ''ᵁ V) (hV.image_of_isOpenImmersion i) (by
    obtain ⟨x, hx⟩ := hne; exact ⟨i.base x, x, hx, rfl⟩)
  exact aic_equiv (i.appIso V).commRingCatIsoToRingEquiv h1

theorem unit_of_hom {W Z : Scheme.{0}} (i : W ⟶ Z) (q : ℕ) (hq : IsUnit (q : Γ(Z, ⊤))) :
    IsUnit (q : Γ(W, ⊤)) := by
  have := hq.map (i.appTop).hom
  simpa using this

def R (P : Scheme.{0} → Prop) {Z : Scheme.{0}} (s : Set Z) : Prop :=
  ∀ (W : Scheme.{0}) (i : W ⟶ Z) [IsOpenImmersion i], Set.range i = s → Nonempty W → P W

def StepP (q : ℕ) (P : Scheme.{0} → Prop) : Prop :=
  ∀ {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g],
    Set.range f ∪ Set.range g = Set.univ → AICSch X → AICSch U → AICSch V → IsUnit (q : Γ(X, ⊤)) →
    P U → P V → (Nonempty ↥(pullback f g : Scheme.{0}) → P (pullback f g)) → P X

theorem R_empty (P : Scheme.{0} → Prop) {Z : Scheme.{0}} : R P (∅ : Set Z) := by
  intro W i _ hr hW
  obtain ⟨w⟩ := hW
  have : i.base w ∈ Set.range i := ⟨w, rfl⟩
  rw [hr] at this; exact this.elim

theorem R_aff (q : ℕ) (P : Scheme.{0} → Prop) (haff : ∀ Z : Scheme.{0}, IsAffine Z → AICSch Z → IsUnit (q : Γ(Z, ⊤)) → P Z)
    {Z : Scheme.{0}} (hZ : AICSch Z) (hq : IsUnit (q : Γ(Z, ⊤))) (A : Z.Opens) (hA : IsAffineOpen A) :
    R P (A : Set Z) := by
  intro W i _ hr hW
  have e : Set.range i = Set.range A.ι := by rw [hr]; simp
  have hWa : IsAffine W := (IsAffine.iff_of_isIso (IsOpenImmersion.isoOfRangeEq i A.ι e).hom).mpr hA
  exact haff W hWa (aicsch_of_imm i hZ) (unit_of_hom i q hq)

theorem R_step (q : ℕ) (P : Scheme.{0} → Prop) (hstep : StepP q P) {Z : Scheme.{0}} (hZ : AICSch Z)
    (hq : IsUnit (q : Γ(Z, ⊤))) {s t : Set Z} (hs : IsOpen s) (ht : IsOpen t)
    (Rs : R P s) (Rt : R P t) (Rst : R P (s ∩ t)) : R P (s ∪ t) := by
  intro W i _ hr hW
  rcases s.eq_empty_or_nonempty with hs0 | ⟨x, hx⟩
  · subst hs0; exact Rt W i (by simpa using hr) hW
  rcases t.eq_empty_or_nonempty with ht0 | ⟨y, hy⟩
  · subst ht0; exact Rs W i (by simpa using hr) hW
  have subs : s ⊆ Set.range i := hr ▸ Set.subset_union_left
  have subt : t ⊆ Set.range i := hr ▸ Set.subset_union_right
  let U' : W.Opens := i ⁻¹ᵁ ⟨s, hs⟩
  let V' : W.Opens := i ⁻¹ᵁ ⟨t, ht⟩
  have rU : Set.range (U'.ι ≫ i) = s := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    exact Set.image_preimage_eq_of_subset subs
  have rV : Set.range (V'.ι ≫ i) = t := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    exact Set.image_preimage_eq_of_subset subt
  obtain ⟨w, hw⟩ := subs hx
  obtain ⟨v, hv⟩ := subt hy
  have neU : Nonempty U'.toScheme := ⟨⟨w, show i.base w ∈ s from hw ▸ hx⟩⟩
  have neV : Nonempty V'.toScheme := ⟨⟨v, show i.base v ∈ t from hv ▸ hy⟩⟩
  have hZW : AICSch W := aicsch_of_imm i hZ
  refine hstep U'.ι V'.ι ?_ hZW (aicsch_of_imm U'.ι hZW) (aicsch_of_imm V'.ι hZW) (unit_of_hom i q hq)
    (Rs _ (U'.ι ≫ i) rU neU) (Rt _ (V'.ι ≫ i) rV neV) (fun hne => Rst _ (pullback.fst U'.ι V'.ι ≫ U'.ι ≫ i) ?_ hne)
  · ext w'
    simp only [Scheme.Opens.range_ι, Set.mem_union, Set.mem_univ, iff_true]
    have : i.base w' ∈ s ∪ t := hr ▸ ⟨w', rfl⟩
    exact this
  · rw [← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact Set.image_preimage_eq_of_subset (Set.inter_subset_left.trans subs)

section Topo
variable {Z : Scheme.{0}} (Q : Set Z → Prop) (hE : Q ∅) (hB : ∀ A : Z.Opens, IsAffineOpen A → Q A)
  (hS : ∀ {s t : Set Z}, IsOpen s → IsOpen t → Q s → Q t → Q (s ∩ t) → Q (s ∪ t))
include hE hB hS

theorem stage1 (A : Z.Opens) (hA : IsAffineOpen A) {ι : Type} (t : Finset ι) :
    ∀ f : ι → Γ(Z, A), Q (⋃ i ∈ t, (Z.basicOpen (f i) : Set Z)) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro f; simpa using hE
  | insert a t ha ih =>
    intro f
    rw [Finset.set_biUnion_insert]
    have hI : (Z.basicOpen (f a) : Set Z) ∩ ⋃ i ∈ t, (Z.basicOpen (f i) : Set Z)
        = ⋃ i ∈ t, (Z.basicOpen (f a * f i) : Set Z) := by
      simp [Scheme.basicOpen_mul, Set.inter_iUnion₂]
    refine hS (Z.basicOpen (f a)).isOpen (isOpen_biUnion fun i _ => (Z.basicOpen (f i)).isOpen)
      (hB _ (hA.basicOpen _)) (ih f) ?_
    rw [hI]; exact ih _

theorem stage1' (A : Z.Opens) (hA : IsAffineOpen A) (S : Set Z) (hSo : IsOpen S) (hSc : IsCompact S)
    (hSA : S ⊆ A) : Q S := by
  have hch : ∀ x : S, ∃ f : Γ(Z, A), Z.basicOpen f ≤ ⟨S, hSo⟩ ∧ (x : Z) ∈ Z.basicOpen f :=
    fun x => hA.exists_basicOpen_le (V := ⟨S, hSo⟩) ⟨x.1, x.2⟩ (hSA x.2)
  choose f hf1 hf2 using hch
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover (fun x : S => (Z.basicOpen (f x) : Set Z))
    (fun x => (Z.basicOpen _).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hf2 _⟩)
  have : S = ⋃ i ∈ t, (Z.basicOpen (f i) : Set Z) :=
    subset_antisymm ht (Set.iUnion₂_subset fun i _ => hf1 i)
  rw [this]; exact stage1 Q hE hB hS A hA t f

theorem stage2 [QuasiSeparatedSpace Z] (t : Finset Z.affineOpens) :
    Q (⋃ i ∈ t, ((i : Z.Opens) : Set Z)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hE
  | insert a t ha ih =>
    rw [Finset.set_biUnion_insert]
    have hTo : IsOpen (⋃ i ∈ t, ((i : Z.Opens) : Set Z)) := isOpen_biUnion fun i _ => (i : Z.Opens).isOpen
    have hTc : IsCompact (⋃ i ∈ t, ((i : Z.Opens) : Set Z)) := t.isCompact_biUnion fun i _ => i.2.isCompact
    refine hS (a : Z.Opens).isOpen hTo (hB _ a.2) ih ?_
    exact stage1' Q hE hB hS a a.2 _ ((a : Z.Opens).isOpen.inter hTo)
      (QuasiSeparatedSpace.inter_isCompact _ _ (a : Z.Opens).isOpen a.2.isCompact hTo hTc) Set.inter_subset_left

theorem stage3 [CompactSpace Z] [QuasiSeparatedSpace Z] : Q Set.univ := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : Z.affineOpens => ((U : Z.Opens) : Set Z))
    (fun U => (U : Z.Opens).isOpen) (fun x _ => by
      have : x ∈ (⨆ i : Z.affineOpens, (i : Z.Opens)) := by rw [iSup_affineOpens_eq_top]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using this)
  have : (Set.univ : Set Z) = ⋃ i ∈ t, ((i : Z.Opens) : Set Z) := subset_antisymm ht (Set.subset_univ _)
  rw [this]; exact stage2 Q hE hB hS t

end Topo

theorem Cov_of : LateralTheory.E.AICAcycPf.Cov := by
  intro q P hiso haff hstep Z _ _ hZ hq
  have h := stage3 (R P (Z := Z)) (R_empty P) (fun A hA => R_aff q P haff hZ hq A hA)
    (fun hs ht Rs Rt Rst => R_step q P hstep hZ hq hs ht Rs Rt Rst)
  have : IsIntegral Z := hZ.1
  exact h Z (𝟙 Z) (by simp) inferInstance

end LateralTheory.E.CovPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.AICAcycPf

namespace LateralTheory.E.StepPf

theorem empty_case {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g]
    (hc : Set.range f ∪ Set.range g = Set.univ) [IrreducibleSpace X] (hW : ¬ Nonempty ↥(pullback f g : Scheme.{0})) :
    Set.range f = Set.univ ∨ Set.range g = Set.univ := by
  by_contra hne
  push Not at hne
  have hfne : (Set.range f).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hne.2 (by simpa [h] using hc)
  have hgne : (Set.range g).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hne.1 (by simpa [h] using hc)
  have hirr : IsPreirreducible (Set.univ : Set X) := (IrreducibleSpace.isIrreducible_univ X).isPreirreducible
  obtain ⟨x, -, hxf, hxg⟩ := hirr _ _ f.isOpenEmbedding.isOpen_range g.isOpenEmbedding.isOpen_range
    (by simpa using hfne) (by simpa using hgne)
  obtain ⟨u, rfl⟩ := hxf
  obtain ⟨v, hv⟩ := hxg
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) u v hv.symm
  exact hW ⟨z⟩

theorem acyc_of_surj (q : ℕ) {V X : Scheme.{0}} (g : V ⟶ X) [IsOpenImmersion g] (hg : Set.range g = Set.univ)
    (h : Acyc q (sch.obj V)) : Acyc q (sch.obj X) := by
  have : Surjective g := ⟨Set.range_eq_univ.mp hg⟩
  have : IsIso g := (isIso_iff_isOpenImmersion_and_surjective g).mpr ⟨inferInstance, inferInstance⟩
  exact acyc_of_iso q (asIso g).symm h

theorem Step_of : Step := by
  intro hyp hMV hZ q U V X f g _ _ hc hX hU hV hq hAU hAV hAW
  have hXi : IsIntegral X := hX.1
  by_cases hW : Nonempty ↥(pullback f g : Scheme.{0})
  · have hAW' := hAW hW
    have : IsIntegral U := hU.1
    have := hW
    have : IsIntegral (pullback f g : Scheme.{0}) := isIntegral_of_isOpenImmersion (pullback.fst f g ≫ f)
    have hqU : IsUnit (q : Γ(U, ⊤)) := by
      have := hq.map f.appTop.hom
      simpa using this
    intro n i hn
    obtain ⟨δ, hex, -⟩ := hMV hyp (ZMod q) (tw q i)
    obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by ring⟩
    have hsU := hAU (m + 1) i hn
    have hsV := hAV (m + 1) i hn
    obtain ⟨-, h2, h3⟩ := hex f g hc m
    constructor
    suffices h0 : ∀ x : Ht q (sch.obj X) (m + 1) i, x = 0 by
      intro a b; rw [h0 a, h0 b]
    intro x
    obtain ⟨w, hw⟩ := (h3 x).mp ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw]
    rcases lt_or_eq_of_le (show (0 : ℤ) ≤ m by omega) with hm | hm
    · have hsW := hAW' m i hm
      rw [Subsingleton.elim w 0, map_zero]
    · subst hm
      rw [h2]
      obtain ⟨a, ha⟩ := (hZ hyp q (pullback.fst f g) hU inferInstance hqU i).2 w
      exact ⟨a, 0, by rw [map_zero, sub_zero]; exact ha.symm⟩
  · rcases empty_case f g hc hW with h | h
    · exact acyc_of_surj q f h hAU
    · exact acyc_of_surj q g h hAV

end LateralTheory.E.StepPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechSigmaProof

abbrev cov {X : Scheme.{0}} (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    (∐ fun j => (V j).toScheme) ⟶ O.toScheme :=
  Sigma.desc fun j => X.homOfLE (hV j)

theorem pre_le {Y X : Scheme.{0}} (g : Y ⟶ X) {A B : X.Opens} (h : A ≤ B) : g ⁻¹ᵁ A ≤ g ⁻¹ᵁ B :=
  fun _ hx => h hx

theorem sq_cov {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    Limits.Sigma.map (fun j => g ∣_ V j) ≫ cov O V hV = cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j)) ≫ g ∣_ O := by
  refine Sigma.hom_ext _ _ fun j => ?_
  rw [← cancel_mono O.ι]
  simp [cov, morphismRestrict_ι]

theorem cov_surj {X : Scheme.{0}} (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O)
    (hc : O ≤ ⨆ j, V j) : Surjective (cov O V hV) := by
  apply Surjective.sigmaDesc_of_union_range_eq_univ
  refine Set.eq_univ_iff_forall.2 fun x => ?_
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc x.2)
  refine Set.mem_iUnion.2 ⟨j, ⟨⟨x.1, hj⟩, ?_⟩⟩
  apply Subtype.ext
  exact congr($(X.homOfLE_ι (hV j)) ⟨x.1, hj⟩)

instance cov_smooth {X : Scheme.{0}} (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    Smooth (cov O V hV) :=
  haveI : IsZariskiLocalAtSource @Smooth.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{0}) (Q := RingHom.Smooth)
  IsZariskiLocalAtSource.sigmaDesc (P := @Smooth.{0}) fun _ => inferInstance

def arr {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    Arrow.mk (yoneda.map (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j)))) ⟶
      Arrow.mk (yoneda.map (cov O V hV)) :=
  Arrow.homMk (yoneda.map (Limits.Sigma.map fun j => g ∣_ V j)) (yoneda.map (g ∣_ O))
    (by simp only [Arrow.mk_hom]; rw [← Functor.map_comp, ← Functor.map_comp, sq_cov g O V hV])

def LevelIso : Prop := ∀ {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O)
  (n : ℕ), Nonempty (Arrow.mk ((Arrow.mapCechNerve (arr g O V hV)).app (op (SimplexCategory.mk n))) ≅
    Arrow.mk (yoneda.map (Limits.Sigma.map fun j : Fin (n + 1) → ι => g ∣_ (⨅ k, V (j k)))))

section
variable {R : Type} [CommRing R] {F : Shv R}

theorem eqv_of_arrowIso {E E' E₁ E₁' : Spc} {f : E ⟶ E'} {f' : E₁ ⟶ E₁'} (e : Arrow.mk f ≅ Arrow.mk f')
    (h : Eqv R f' F) : Eqv R f F := by
  have w : f = e.hom.left ≫ f' ≫ e.inv.right := by
    have := Arrow.w e.hom
    simp only [Arrow.mk_hom] at this
    rw [← Category.assoc, this, Category.assoc, ← Arrow.comp_right, e.hom_inv_id, Arrow.id_right]
    simp
  rw [w]
  exact ZariskiLocalCech.eqv_comp (ZariskiLocalCech.eqv_iso _) (ZariskiLocalCech.eqv_comp h (ZariskiLocalCech.eqv_iso _))

theorem eqv_of_comp_left {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hfg : Eqv R (f ≫ g) F) :
    Eqv R g F := fun n => by
  have h : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  have := hfg n
  rw [h] at this
  exact (Function.Bijective.of_comp_iff' (hf n) _).1 this

end

theorem CechSigma_of (hL : LevelIso) : ZariskiLocalCech.CechSigma := by
  unfold LevelIso at hL
  intro hH R _ F Y X g O ι V hV hc hn
  obtain ⟨_, hA2, hA3, -⟩ := hH
  have hc' : g ⁻¹ᵁ O ≤ ⨆ j, g ⁻¹ᵁ V j := by
    rw [← Scheme.Hom.preimage_iSup]; exact pre_le g hc
  have := cov_surj O V hV hc
  have := cov_surj (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j)) hc'
  have e1 : Eqv R (cechAug (cov O V hV)) F := hA2 R _ F
  have e2 : Eqv R (cechAug (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j)))) F := hA2 R _ F
  have e3 : Eqv R (Arrow.mapCechNerve (arr g O V hV)) F := by
    refine hA3 R _ F fun m => ?_
    obtain ⟨e⟩ := hL g O V hV m.unop.len
    have e' : Arrow.mk (disc.map ((Arrow.mapCechNerve (arr g O V hV)).app m)) ≅
        Arrow.mk (sch.map (Limits.Sigma.map fun j : Fin (m.unop.len + 1) → ι => g ∣_ (⨅ k, V (j k)))) :=
      (disc.mapArrow).mapIso e
    exact eqv_of_arrowIso e' (hn _)
  have w : Arrow.mapCechNerve (arr g O V hV) ≫ cechAug (cov O V hV) =
      cechAug (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j))) ≫ sch.map (g ∣_ O) := by
    have h := (Arrow.mapAugmentedCechNerve (arr g O V hV)).w
    exact h
  have h4 : Eqv R (cechAug (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j))) ≫ sch.map (g ∣_ O)) F := by
    rw [← w]; exact ZariskiLocalCech.eqv_comp e3 e1
  exact eqv_of_comp_left e2 h4

end LateralTheory.E.CechSigmaProof
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf

namespace LateralTheory.E.ZarIndPf

def Bij (q : ℕ) (i n : ℤ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) : Prop :=
  Function.Bijective (pull _ (sch.map (fO f p U)) (tw q i) n)

def InjStep : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ, (∀ s : S, Germ q i n f p s) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  ∀ U : S.Opens, IsCompact (U : Set S) → Function.Injective (pull _ (sch.map (fO f p U)) (tw q i) n)

def SurjStep : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ, (∀ s : S, Germ q i n f p s) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Function.Injective (pull _ (sch.map (fO f p U)) (tw q i) n)) →
  ∀ U : S.Opens, IsCompact (U : Set S) → Function.Surjective (pull _ (sch.map (fO f p U)) (tw q i) n)

def Step : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ, (∀ s : S, Germ q i n f p s) →
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i n f p U

theorem Step_of (h1 : InjStep) (h2 : SurjStep) : Step := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i n hg hb U hU
  exact ⟨h1 hM hH q f p hq i n hg hb U hU, h2 hM hH q f p hq i n hg hb (h1 hM hH q f p hq i n hg hb) U hU⟩

theorem pull_bij_of_iso {E E' : Spc} (g : E ⟶ E') [IsIso g] {q' : ℕ} (F : Shv (ZMod q')) (n : ℤ) :
    Function.Bijective (pull _ g F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull _ (inv g) F n, fun x => ?_, fun x => ?_⟩
  · simp [← pull_comp, pull_id]
  · simp [← pull_comp, pull_id]

theorem bij_top {q : ℕ} {i n : ℤ} {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [IsIso (⊤ : S.Opens).ι] (h : Bij q i n f p ⊤) :
    Function.Bijective (pull _ (sch.map f) (tw q i) n) := by
  have e : fO f p ⊤ ≫ pullback.fst p (⊤ : S.Opens).ι = pullback.fst (f ≫ p) (⊤ : S.Opens).ι ≫ f := by
    exact pullback.lift_fst _ _ _
  have e2 : ∀ x, pull _ (sch.map (fO f p ⊤)) (tw q i) n (pull _ (sch.map (pullback.fst p (⊤ : S.Opens).ι)) _ n x) =
      pull _ (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) _ n (pull _ (sch.map f) _ n x) := by
    intro x
    rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, e]
  have b1 := pull_bij_of_iso (sch.map (pullback.fst p (⊤ : S.Opens).ι)) (tw q i) n
  have b2 := pull_bij_of_iso (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n
  have hc : Function.Bijective ((pull (ZMod q) (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n) ∘ (pull (ZMod q) (sch.map f) (tw q i) n)) := by
    have : (pull (ZMod q) (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n) ∘ (pull (ZMod q) (sch.map f) (tw q i) n) =
        (pull (ZMod q) (sch.map (fO f p ⊤)) (tw q i) n) ∘ (pull (ZMod q) (sch.map (pullback.fst p (⊤ : S.Opens).ι)) (tw q i) n) :=
      funext fun x => (e2 x).symm
    rw [this]; exact h.comp b1
  refine ⟨hc.1.of_comp, fun y => ?_⟩
  obtain ⟨x, hx⟩ := hc.2 (pull (ZMod q) (sch.map (pullback.fst (f ≫ p) (⊤ : S.Opens).ι)) (tw q i) n y)
  exact ⟨x, b2.1 hx⟩

theorem bij_neg (hH : Hyp) {q : ℕ} {i n : ℤ} (hn : n < 0) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    Bij q i n f p U := by
  have h1 := (hH.a9 (ZMod q) (tw q i)).1 (sch.obj (overO p U)) n hn
  have h2 := (hH.a9 (ZMod q) (tw q i)).1 (sch.obj (overO (f ≫ p) U)) n hn
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

theorem ZarInd_of_step (hS : Step) : ZarInd := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i hg
  have P : ∀ n : ℤ, ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i n f p U := by
    intro n
    induction n using Int.induction_on with
    | zero => exact hS hM hH q f p hq i 0 (fun s => hg s 0) (fun U _ => bij_neg hH (by norm_num) f p U)
    | succ m ih =>
      exact hS hM hH q f p hq i (m + 1) (fun s => hg s (m + 1)) (by simpa using ih)
    | pred m ih =>
      exact fun U _ => bij_neg hH (by omega) f p U
  intro n
  have : IsIso (⊤ : S.Opens).ι := (Scheme.topIso S).isIso_hom
  exact bij_top f p (P n ⊤ (by simpa using isCompact_univ))

end LateralTheory.E.ZarIndPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChowLCut

inductive IterLine {S : Scheme.{0}} : ∀ {Y : Scheme.{0}}, (Y ⟶ S) → Prop
  | iso {Y : Scheme.{0}} (e : Y ⟶ S) : IsIso e → IterLine e
  | comp {Y T : Scheme.{0}} (l : Y ⟶ T) (k : T ⟶ S) : IsLine l → IterLine k → IterLine (l ≫ k)

theorem IT_of_iterLine {S Y : Scheme.{0}} {k : Y ⟶ S} (hk : IterLine k) :
    ∀ {X : Scheme.{0}} (u : X ⟶ Y), IsIntegralHom u → IT (u ≫ k) := by
  induction hk with
  | iso e he => intro X u hu; exact IT.int _ (by infer_instance)
  | comp l k hl _ ih =>
    intro X u hu
    refine IT.step (u ≫ l) k _ ?_ ⟨_, u, l, hu, hl, rfl⟩ (Category.assoc _ _ _)
    simpa using ih (𝟙 _) inferInstance

def LineEx : Prop := ∀ S : Scheme.{0}, ∃ (L : Scheme.{0}) (l : L ⟶ S), IsLine l

def IterBC : Prop := ∀ {P S X : Scheme.{0}} (q : P ⟶ S) (g : X ⟶ S), IterLine q → IterLine (pullback.fst g q)

def ChowGraph : Prop := ∀ (A : Type) [CommRing A] {X₁ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of A)) [IsProper p₁],
  IsIntegral X₁ → ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of A)) (X' : Scheme.{0}) (i : X' ⟶ pullback p₁ q)
    (U : X₁.Opens) (s : U.toScheme ⟶ X'), IterLine q ∧ IsClosedImmersion i ∧ IsClosedImmersion (i ≫ pullback.snd p₁ q) ∧
    (U : Set X₁).Nonempty ∧ s ≫ i ≫ pullback.fst p₁ q = U.ι

theorem goal_of (hB : IterBC) (hG : ChowGraph) : LateralTheory.E.ChowCut.ChowL := by
  intro A _ X₁ p₁ _ hX₁
  obtain ⟨P, q, X', i, U, s, hq, hi, his, hU, hs⟩ := hG A p₁ hX₁
  refine ⟨X', i ≫ pullback.fst p₁ q, U, s, hU, hs, IT_of_iterLine (hB q p₁ hq) i inferInstance, ?_⟩
  have e : (i ≫ pullback.fst p₁ q) ≫ p₁ = (i ≫ pullback.snd p₁ q) ≫ q := by
    rw [Category.assoc, pullback.condition, Category.assoc]
  rw [e]
  exact IT_of_iterLine hq _ inferInstance

end LateralTheory.E.ChowLCut

end
end
