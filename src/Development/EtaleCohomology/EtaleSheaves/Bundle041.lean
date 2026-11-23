module

public import Development.EtaleCohomology.EtaleSheaves.Bundle026
public import Development.EtaleCohomology.EtaleSheaves.Bundle006
public import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.Algebra.Category.ModuleCat.AB
public import Development.EtaleCohomology.EtaleSheaves.Bundle027
public import Mathlib.AlgebraicGeometry.Normalization
public import Development.EtaleCohomology.EtaleSheaves.Bundle028
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Polynomial

namespace LateralTheory.E.AICOpenPf
open LateralTheory.E.t_E2Cut LateralTheory.E.SteinPf

theorem roots_in {A K : Type} [CommRing A] [IsDomain A] [CommRing K] [IsDomain K] (φ : A →+* K) (hA : AIC A) :
    ∀ n (p : A[X]), p.natDegree = n → p.Monic → ∀ β : K, (p.map φ).eval β = 0 → ∃ a, φ a = β := by
  intro n
  induction n with
  | zero =>
    intro p hd hm β hβ
    have : p = 1 := hm.natDegree_eq_zero.mp hd
    subst this; simp at hβ
  | succ n ih =>
    intro p hd hm β hβ
    obtain ⟨a, ha⟩ := hA p hm (by omega)
    have hfac : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hqm : (p /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [hfac]; exact hm)
    have hqd : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    rw [← hfac, Polynomial.map_mul, eval_mul, mul_eq_zero] at hβ
    rcases hβ with h | h
    · refine ⟨a, ?_⟩
      simp at h; rw [sub_eq_zero] at h; exact h.symm
    · exact ih _ hqd hqm β h

theorem gtf_res {Z : Scheme.{0}} [IsIntegral Z] {U W : Z.Opens} (i : U ⟶ W) [Nonempty U] [Nonempty W] (s : Γ(Z, W)) :
    Z.germToFunctionField U (Z.presheaf.map i.op s) = Z.germToFunctionField W s := by
  simp only [Scheme.germToFunctionField]
  rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_res]

theorem gtf_res_hom {Z : Scheme.{0}} [IsIntegral Z] {U W : Z.Opens} (i : U ⟶ W) [Nonempty U] [Nonempty W] :
    (Z.germToFunctionField U).hom.comp (Z.presheaf.map i.op).hom = (Z.germToFunctionField W).hom := by
  ext s; exact gtf_res i s

theorem AICOpen_of : AICOpen := by
  intro Z hZ W hW p hm hd
  have : IsIntegral Z := hZ.1
  have : Nonempty W := ⟨⟨_, hW.some_mem⟩⟩
  have hcov : ∀ x : W, ∃ U : Z.Opens, IsAffineOpen U ∧ (x : Z) ∈ U ∧ U ≤ W := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open x.2 W.isOpen
    exact ⟨U, hU, hxU, hUW⟩
  choose U hUa hxU hUW using hcov
  have hne : ∀ x : W, Nonempty (U x) := fun x => ⟨⟨_, hxU x⟩⟩
  let ψ := Z.germToFunctionField W

  have hroot : ∀ x : W, ∃ β : Z.functionField, (p.map ψ.hom).eval β = 0 := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hZ.2 _ (hUa x) ⟨_, hxU x⟩
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    obtain ⟨r, hr⟩ := hA (p.map ρ) (hm.map ρ) (by rw [hm.natDegree_map]; exact hd)
    refine ⟨Z.germToFunctionField (U x) r, ?_⟩
    rw [← gtf_res_hom (homOfLE (hUW x)), ← Polynomial.map_map, Polynomial.eval_map_apply, hr, map_zero]
  obtain ⟨β, hβ⟩ := hroot ⟨_, hW.some_mem⟩
  have hsec : ∀ x : W, ∃ t : Γ(Z, U x), Z.germToFunctionField (U x) t = β := by
    intro x
    have := hne x
    have hA : AIC Γ(Z, U x) := hZ.2 _ (hUa x) ⟨_, hxU x⟩
    let ρ := (Z.presheaf.map (homOfLE (hUW x)).op).hom
    exact roots_in (Z.germToFunctionField (U x)).hom hA _ (p.map ρ) rfl (hm.map ρ) β
      (by rw [Polynomial.map_map, gtf_res_hom]; exact hβ)
  choose sf hsf using hsec
  have hcompat : TopCat.Presheaf.IsCompatible Z.sheaf.1 U sf := by
    intro i j
    have := hne i; have := hne j
    have hij : ((U i ⊓ U j : Z.Opens) : Set Z).Nonempty :=
      nonempty_preirreducible_inter (U i).isOpen (U j).isOpen ⟨_, hxU i⟩ ⟨_, hxU j⟩
    have : Nonempty (U i ⊓ U j : Z.Opens) := ⟨⟨_, hij.some_mem⟩⟩
    apply Z.germToFunctionField_injective (U i ⊓ U j)
    change Z.germToFunctionField _ (Z.presheaf.map _ (sf i)) = Z.germToFunctionField _ (Z.presheaf.map _ (sf j))
    rw [gtf_res, gtf_res, hsf, hsf]
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (U := U) (V := W) (iUV := fun x => homOfLE (hUW x))
    (hcover := fun y hy => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxU _⟩) (sf := sf) (h := hcompat)
  have hsβ : ψ s = β := by
    have h0 := hs ⟨_, hW.some_mem⟩
    have := hne ⟨_, hW.some_mem⟩
    rw [← hsf ⟨_, hW.some_mem⟩, ← gtf_res (homOfLE (hUW ⟨_, hW.some_mem⟩)) s]
    exact congrArg _ h0
  obtain ⟨t, ht⟩ : ∃ t : Γ(Z, W), ψ t = β := ⟨s, hsβ⟩
  refine ⟨t, Z.germToFunctionField_injective W ?_⟩
  rw [map_zero]
  have key : ψ.hom (p.eval t) = (p.map ψ.hom).eval (ψ.hom t) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  change ψ.hom (p.eval t) = 0
  rw [key]; change (p.map ψ.hom).eval (ψ t) = 0
  rw [ht]; exact hβ

end LateralTheory.E.AICOpenPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafCochainVanishPf

variable {R : Type} [CommRing R]

theorem free_ext_zero (P : PSh) (G : Shv R) (φ : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.hom.app (op U)).hom (freeGen R P U x) = 0) : φ = 0 := by
  have h0 : (0 : (free R).obj P ⟶ G).hom = 0 := rfl
  refine Sheaf.hom_ext ?_
  rw [h0]
  refine sheafify_hom_ext _ _ _ G.property ?_
  ext U : 2
  refine ModuleCat.free_hom_ext (fun x => ?_)
  exact (h U.unop x.down).trans (by erw [Limits.comp_zero]; rfl)

theorem chains_isZero (E : Spc) (p : ℤ) (hp : 0 < p) : Limits.IsZero (((chains R).obj E).X p) := by
  refine HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => ?_)
  have : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
  omega

theorem cochain_zero_of (E : Spc) {U V : Spc} (f : U ⟶ E) (g : V ⟶ E) (hc : Cover2 R f g) (K : Cx R) (k : ℤ)
    (γ : Cochain ((chains R).obj E) K k)
    (hU : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx U N Y), ev γ N w h Y ((f.app _).app _ y) = 0)
    (hV : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (Y : Scheme.{0}) (y : Sx V N Y), ev γ N w h Y ((g.app _).app _ y) = 0) :
    γ = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hp : 0 < p
  · exact (chains_isZero (R := R) E p hp).eq_of_src _ _
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨(-p).toNat, by omega⟩
  have hφ : (chainsXIso R E N).inv ≫ γ.v (-(N : ℤ)) q hpq = 0 := by
    have := hc.2.2 (op (SimplexCategory.mk N))
    rw [← cancel_epi (biprod.desc ((free R).map (f.app (op (SimplexCategory.mk N))))
      ((free R).map (g.app (op (SimplexCategory.mk N))))), Limits.comp_zero]
    apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Limits.comp_zero]
      refine free_ext_zero _ _ _ (fun Y y => ?_)
      have e := hU N q hpq Y y
      unfold ev at e
      rw [← LateralTheory.E.FirstChernNaturality.freeGen_nat (R := R)] at e
      exact e
    · rw [biprod.inr_desc_assoc, Limits.comp_zero]
      refine free_ext_zero _ _ _ (fun Y y => ?_)
      have e := hV N q hpq Y y
      unfold ev at e
      rw [← LateralTheory.E.FirstChernNaturality.freeGen_nat (R := R)] at e
      exact e
  rw [← Iso.hom_inv_id_assoc (chainsXIso R E N) (γ.v _ _ hpq), hφ, Limits.comp_zero]

end LateralTheory.E.LeafCochainVanishPf

theorem LateralTheory.E.LeafA6suppPf.LeafCochainVanish_of : LateralTheory.E.LeafA6suppPf.LeafCochainVanish := by
  intro R _ U V E f g hc K k γ hU hV
  exact LateralTheory.E.LeafCochainVanishPf.cochain_zero_of E f g hc K k γ hU hV
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.NormPf

def OpenNbhdIC : Prop := ∀ {Z : Scheme.{0}} (U : Z.Opens), AICSch Z → (U : Set Z).Nonempty → AICSch U.toScheme

def FFAlg : Prop := ∀ {Z : Scheme.{0}} [IsIntegral Z], AICSch Z → IsAlgClosed Z.functionField

def NormAIC : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] {W : Scheme.{0}} (g : Spec (CommRingCat.of K) ⟶ W)
  [QuasiCompact g] [QuasiSeparated g], AICSch g.normalization

theorem spec_field_qc (K : Type) [Field K] {W : Scheme.{0}} (g : Spec (CommRingCat.of K) ⟶ W) : QuasiCompact g := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro U _
  exact (Set.toFinite _).isCompact

theorem Norm_of (h0 : OpenNbhdIC) (h1 : FFAlg) (h2 : NormAIC) : LateralTheory.E.ChowCut.Norm := by
  intro Z W f _ hZ ⟨U, s, hU, hs⟩
  have : IsIntegral Z := hZ.1
  have hUa := h0 U hZ hU
  have := hUa.1
  have := h1 hUa
  let g0 : Spec (CommRingCat.of U.toScheme.functionField) ⟶ U.toScheme := U.toScheme.fromSpecStalk _
  let g := g0 ≫ s
  have := spec_field_qc _ g
  refine ⟨g.normalization, g.fromNormalization, inferInstance, h2 _ g, ?_⟩
  have hg0 : IsDominant g0 := by
    constructor
    rw [denseRange_iff_closure_range, Scheme.range_fromSpecStalk]
    exact Set.eq_univ_of_univ_subset ((genericPoint_spec U.toScheme).def ▸ closure_mono (Set.singleton_subset_iff.mpr (specializes_refl _)))
  have hU' : IsDominant U.ι := by
    constructor
    rw [denseRange_iff_closure_range, Scheme.Opens.range_ι]
    exact (U.isOpen.dense hU).closure_eq
  have e : g.toNormalization ≫ g.fromNormalization ≫ f = g0 ≫ U.ι := by
    rw [reassoc_of% g.toNormalization_fromNormalization, Category.assoc, hs]
  have : IsDominant (g.toNormalization ≫ g.fromNormalization ≫ f) := by rw [e]; infer_instance
  exact IsDominant.of_comp g.toNormalization _

end LateralTheory.E.NormPf

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.InjectiveSections

abbrev MC (q : ℕ) := ModuleCat.{1} (ULift.{1} (ZMod q))

theorem sigma_const_mono (q : ℕ) {α : Type} {d d' : MC q} (f : d ⟶ d') [Mono f] :
    Mono (Limits.Sigma.map (fun _ : α => f)) := by
  have : Mono (Discrete.natTrans (fun (_ : Discrete α) => f) : Discrete.functor (fun _ : α => d) ⟶ Discrete.functor (fun _ : α => d')) :=
    @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ (fun _ => inferInstanceAs (Mono f))
  have : AB4OfSize.{0} (MC q) := AB4OfSize_shrink.{0, 1} (MC q)
  have : HasExactColimitsOfShape (Discrete α) (MC q) := AB4OfSize.ofShape α
  have : PreservesFiniteLimits (colim : (Discrete α ⥤ MC q) ⥤ MC q) := inferInstance
  exact (Functor.map_mono colim (Discrete.natTrans (fun (_ : Discrete α) => f) : Discrete.functor (fun _ : α => d) ⟶ Discrete.functor (fun _ : α => d')) : _)

instance evalLA_mono (q : ℕ) (U : Scheme.{0}) :
    (evaluationLeftAdjoint (MC q) (op U)).PreservesMonomorphisms where
  preserves {d d'} f _ := by
    refine @NatTrans.mono_of_mono_app _ _ _ _ _ _ _ (fun t => ?_)
    change Mono (Limits.Sigma.desc (fun h : op U ⟶ t => f ≫ Sigma.ι (fun _ => d') h))
    have h : Limits.Sigma.desc (fun h : op U ⟶ t => f ≫ Sigma.ι (fun _ => d') h) = Limits.Sigma.map (fun _ => f) := by
      apply Limits.Sigma.hom_ext; intro j; rw [Limits.Sigma.ι_desc, Limits.Sigma.ι_map]
    rw [h]
    exact sigma_const_mono q f

theorem eval_injective (q : ℕ) (M : Shv (ZMod q)) [Injective M] (U : Scheme.{0}) :
    Injective (M.obj.obj (op U)) := by
  have h1 : Injective ((sheafToPresheaf Scheme.etaleTopology.{0} (MC q)).obj M) :=
    Injective.injective_of_adjoint (sheafificationAdjunction Scheme.etaleTopology.{0} (MC q)) M
  have h2 : Injective M.obj := h1
  exact Injective.injective_of_adjoint (evaluationAdjunctionRight (MC q) (op U)) M.obj

end LateralTheory.E.InjectiveSections

open LateralTheory.E.InjectiveSections in
theorem LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj_of : LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj := by
  intro q _ M _ U
  have h := eval_injective q M U
  exact Module.injective_module_of_injective_object (ULift.{1} (ZMod q)) (Sec M U)
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut

namespace LateralTheory.E.ProEqvPf

def fm {A : Type} [CommRing A] [IsLocalRing A] {U Y : Scheme.{0}} (u : U ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of A)) :
    pullback (u ≫ g) (cpt A) ⟶ pullback g (cpt A) :=
  pullback.map _ _ _ _ u (𝟙 _) (𝟙 _) (by simp) (by simp)

def Hit (q : ℕ) (i n : ℤ) {A : Type} [CommRing A] [IsLocalRing A] {U Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A))
    (z : Ht q (sch.obj (pullback g (cpt A))) n i) (u : U ⟶ Y) : Prop :=
  ∃ w : Ht q (sch.obj U) n i, pull _ (sch.map (pullback.fst (u ≫ g) (cpt A))) _ _ w = pull _ (sch.map (fm u g)) _ _ z

def PiLocalization₂ : Prop := LateralTheory.E.t_E2Cut.Cont → Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (y : Y) {J : Type}
  [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
  ClopenSys y D c ι → (∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) → ∀ n : ℤ,
  (∀ x : Ht q (sch.obj Y) n i, pull _ (sch.map (pullback.fst g (cpt A))) _ _ x = 0 → ∃ j, pull _ (sch.map (ι j)) _ _ x = 0) ∧
  ∀ z : Ht q (sch.obj (pullback g (cpt A))) n i, ∃ j, Hit q i n g z (ι j)

def Glue : Prop := MV → Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)) (n : ℤ),
  (∀ x : Ht q (sch.obj Y) n i, pull _ (sch.map (pullback.fst g (cpt A))) _ _ x = 0 → ∀ y : Y,
    ∃ (U : Scheme.{0}) (u : U ⟶ Y), IsOpenImmersion u ∧ IsClosedImmersion u ∧ y ∈ Set.range u ∧ pull _ (sch.map u) _ _ x = 0) →
  (∀ z : Ht q (sch.obj (pullback g (cpt A))) n i, ∀ y : Y,
    ∃ (U : Scheme.{0}) (u : U ⟶ Y), IsOpenImmersion u ∧ IsClosedImmersion u ∧ y ∈ Set.range u ∧ Hit q i n g z u) →
  Function.Bijective (pull _ (sch.map (pullback.fst g (cpt A))) (tw q i) n)

theorem ProEqv_of (hC : LateralTheory.E.t_E2Cut.Cont) (hM : MV) (hS : PiLocalization₂) (hG : Glue) : ProEqv := by
  intro H q i A _ _ hq Y _ _ g hY n
  refine hG hM H q i A hq g n (fun x hx y => ?_) (fun z y => ?_)
  · obtain ⟨J, _, _, D, c, ι, hc, hp⟩ := hY y
    obtain ⟨j, hj⟩ := (hS hC H q i A hq g y D c ι hc hp n).1 x hx
    exact ⟨_, ι j, (hc.2.1 j).1, (hc.2.1 j).2.1, (hc.2.1 j).2.2, hj⟩
  · obtain ⟨J, _, _, D, c, ι, hc, hp⟩ := hY y
    obtain ⟨j, hj⟩ := (hS hC H q i A hq g y D c ι hc hp n).2 z
    exact ⟨_, ι j, (hc.2.1 j).1, (hc.2.1 j).2.1, (hc.2.1 j).2.2, hj⟩

end LateralTheory.E.ProEqvPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut

namespace LateralTheory.E.BuildCut

def ProdACF (W : Type) [CommRing W] : Prop :=
  AIC W ∧ ∀ a : W, ∃ e u : W, IsIdempotentElem e ∧ IsUnit u ∧ a = e * u

def Pts : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P],
  ∃ (W : Type) (_ : CommRing W) (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W ∧ Surjective w

def LimInt : Prop := ∀ {Y : Scheme.{0}} (y : Y) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D)
  (ι : ∀ j, D.obj j ⟶ Y), ClopenSys y D c ι → ∀ j, IsIntegralHom (c.π.app j ≫ ι j)

def Comp : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ w.normalization),
      ClopenSys y D c ι ∧ AICSch c.pt

theorem goal_of (hP : Pts) (hL : LimInt) (hC : Comp) : Build := by
  intro P _ _
  obtain ⟨W, _, w, hW, hs⟩ := hP (P := P)
  refine ⟨w.normalization, w.fromNormalization, inferInstance, ?_, fun y => ?_⟩
  · have h := hs
    rw [← w.toNormalization_fromNormalization] at h
    exact ⟨Function.Surjective.of_comp h.surj⟩
  · obtain ⟨J, _, _, D, c, ι, hc, hA⟩ := hC W w hW y
    refine ⟨J, inferInstance, inferInstance, D, c, ι, hc, hA, fun j => ?_⟩
    have := hL y D c ι hc j
    infer_instance

end LateralTheory.E.BuildCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.FibPf

namespace LateralTheory.E.FibClosedPf

abbrev fm {A : Type} [CommRing A] [IsLocalRing A] {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) :
    pullback (c ≫ p) (cpt A) ⟶ pullback p (cpt A) :=
  pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp)

def FibQCQS : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A))
  [QuasiCompact c] [QuasiSeparated c], QuasiCompact (fm c p) ∧ QuasiSeparated (fm c p)

def FibStalk : Prop := Hyp → HZero → AICAcyc → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c]
  [QuasiSeparated c] [IsDominant c], AICSch Z → AICSch S →
  (∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t)) →
  ∀ s : (pullback p (cpt A) : Scheme.{0}),
    Eqv _ (sch.map (pullback.map (fm c p ≫ 𝟙 _) ((pullback p (cpt A)).fromSpecStalk s) (𝟙 _)
      ((pullback p (cpt A)).fromSpecStalk s) (fm c p) (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i)

theorem FibClosed_of (hZ : ZLG) (h0 : HZero) (hA : AICAcyc) (hQ : FibQCQS) (hS : FibStalk) : FibClosed := by
  intro H q i A _ _ hq Z S c p _ _ _ _ _ hZs hSs hB
  obtain ⟨_, _⟩ := hQ A c p
  obtain ⟨_, _⟩ := qcqs_of (pullback.snd p (cpt A))
  have hu : IsUnit (q : Γ(pullback p (cpt A), ⊤)) := unit_of hq (pullback.fst p (cpt A) ≫ p)
  exact hZ H q (fm c p) (𝟙 _) hu i (hS H h0 hA q i A hq c p hZs hSs hB)

theorem fm_isPullback {A : Type} [CommRing A] [IsLocalRing A] {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) :
    IsPullback (fm c p) (pullback.fst (c ≫ p) (cpt A)) (pullback.fst p (cpt A)) c := by
  refine IsPullback.of_right (h₁₂ := pullback.snd p (cpt A)) (h₂₂ := p) ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback p (cpt A)).flip
  have e : fm c p ≫ pullback.snd p (cpt A) = pullback.snd (c ≫ p) (cpt A) := by
    unfold fm; rw [pullback.map]; erw [pullback.lift_snd]; simp
  rw [e]
  exact (IsPullback.of_hasPullback (c ≫ p) (cpt A)).flip

theorem fibQCQS : FibQCQS := by
  intro A _ _ Z S c p _ _
  exact ⟨MorphismProperty.of_isPullback (P := @QuasiCompact) (fm_isPullback c p).flip ‹_›,
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (fm_isPullback c p).flip ‹_›⟩

end LateralTheory.E.FibClosedPf
end
end

section

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.E.HensCut

def LocAIC : Prop := ∀ (B : Type) [CommRing B] [IsDomain B] (M : Submonoid B), (0 : B) ∉ M → AIC B →
  IsDomain (Localization M) ∧ AIC (Localization M)

def MonicSplits : Prop := ∀ (R : Type) [CommRing R] [IsDomain R], AIC R → ∀ p : Polynomial R, p.Monic →
  ∃ s : Multiset R, p = (s.map fun a => Polynomial.X - Polynomial.C a).prod

def IdemPart : Prop := ∀ (A : Type) [CommRing A] (n : ℕ) (y : Fin n → A), ∏ l, y l = 0 →
  IsUnit (∑ l, ∏ m ∈ Finset.univ.erase l, y m) →
  ∃ e : Fin n → A, (∀ l, IsIdempotentElem (e l)) ∧ (∀ l m, l ≠ m → e l * e m = 0) ∧ ∑ l, e l = 1 ∧ ∀ l, e l * y l = 0

def ColimHens : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (β : (Functor.const J).obj (CommRingCat.of B) ⟶ D) (c : Cocone D), IsColimit c →
  (∀ j, Function.Bijective (Ideal.quotientMap (I.map (β.app j).hom) (β.app j).hom Ideal.le_comap_map)) →
  (∀ j, ∀ x ∈ I.map (β.app j).hom, ∃ (j' : J) (f : j ⟶ j'), IsUnit ((D.map f).hom (1 + x))) →
  (∀ j (p : Polynomial (D.obj j)) (a₀ : D.obj j), p.Monic → p.eval a₀ ∈ I.map (β.app j).hom →
    IsUnit (Ideal.Quotient.mk (I.map (β.app j).hom) (p.derivative.eval a₀)) →
    ∃ (j' : J) (f : j ⟶ j') (a : D.obj j'), (p.map (D.map f).hom).IsRoot a ∧ a - (D.map f).hom a₀ ∈ I.map (β.app j').hom) →
  ∃ K : Ideal c.pt, HenselianRing c.pt K ∧ Nonempty (B ⧸ I ≃+* c.pt ⧸ K)

def PartDiag : Prop := ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B → IsUnit (q : B) →
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
    (β : (Functor.const J).obj (CommRingCat.of B) ⟶ D),
    (∀ j, ∃ (m : ℕ) (R : Fin m → Type) (_ : ∀ k, CommRing (R k)),
      (∀ k, IsDomain (R k) ∧ AIC (R k) ∧ IsUnit (q : R k)) ∧ Nonempty (D.obj j ≃+* ∀ k, R k)) ∧
    (∀ j, Function.Bijective (Ideal.quotientMap (I.map (β.app j).hom) (β.app j).hom Ideal.le_comap_map)) ∧
    (∀ j, ∀ x ∈ I.map (β.app j).hom, ∃ (j' : J) (f : j ⟶ j'), IsUnit ((D.map f).hom (1 + x))) ∧
    (∀ j (p : Polynomial (D.obj j)) (a₀ : D.obj j), p.Monic → p.eval a₀ ∈ I.map (β.app j).hom →
      IsUnit (Ideal.Quotient.mk (I.map (β.app j).hom) (p.derivative.eval a₀)) →
      ∃ (j' : J) (f : j ⟶ j') (a : D.obj j'), (p.map (D.map f).hom).IsRoot a ∧
        a - (D.map f).hom a₀ ∈ I.map (β.app j').hom)

theorem goal_of (_hL : LocAIC) (_hM : MonicSplits) (_hI : IdemPart) (hC : ColimHens) (hD : PartDiag) :
    LateralTheory.E.QuotAcycCut.Hens := by
  intro q B _ _ I hB hq
  obtain ⟨J, _, _, D, β, hst, ha, hb, hc⟩ := hD q B I hB hq
  obtain ⟨K, hK, he⟩ := hC B I J D β (colimit.cocone D) (colimit.isColimit D) ha hb hc
  refine ⟨J, inferInstance, inferInstance, D, colimit.cocone D, colimit.isColimit D, hst, ?_, K, hK, he⟩
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  have h1 : IsUnit ((q : B)) := hq
  have h2 := h1.map ((β.app j) ≫ (colimit.cocone D).ι.app j).hom
  simpa using h2

end LateralTheory.E.HensCut
end
end
