module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCutHoc
public import Development.EtaleCohomology.CohomologicalPurity.Bundle016
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem zpf_pushout {R B : Type} [CommRing R] [CommRing B] (φ : R →+* B) (I : Ideal R) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map φ)))
      (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) := by
  letI := φ.toAlgebra
  let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I
  refine (CommRingCat.isPushout_tensorProduct R B (R ⧸ I)).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) e.toRingEquiv.toCommRingCatIso.symm ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · ext x
    simp [e]
    rw [← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, AlgEquiv.symm_apply_apply]; rfl
  · ext x
    simp [e]
    rw [Algebra.smul_def, mul_one]; rfl

theorem zpf_sqA (X Z : Scheme.{0}) (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.affineOpens) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ι.ker.ideal V))))
      (ι.ker.subschemeCover.f V ≫ inv ι.toImage) V.2.fromSpec ι := by
  have h0 : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (ι.ker.ideal V))))
      (ι.ker.subschemeCover.f V) V.2.fromSpec ι.ker.subschemeι := by
    have hf := V.2.isOpenImmersion_fromSpec
    have hc : IsOpenImmersion (ι.ker.subschemeCover.f V) := ι.ker.subschemeCover.map_prop V
    refine @IsOpenImmersion.isPullback _ _ _ _ _ _ _ _ hc hf ?_ ?_
    · exact (Scheme.IdealSheafData.subschemeCover_map_subschemeι _ V).trans
        (Scheme.IdealSheafData.glueDataObjι_ι _ V)
    · exact (congrArg (ι.ker.subschemeι ⁻¹ᵁ ·) V.2.opensRange_fromSpec).trans
        (Scheme.IdealSheafData.opensRange_subschemeCover_map _ V).symm
  refine h0.of_iso (Iso.refl _) (Iso.refl _) (asIso ι.toImage).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
    exact ι.toImage_imageι

theorem zpf_range_mk {A : Type} [CommRing A] (J : Ideal A) :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
      PrimeSpectrum.zeroLocus (J : Set A) := by
  have := _root_.range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective (I := J))
  rw [Ideal.mk_ker] at this
  exact this

theorem LeafZ_of : LeafZ := by
  intro X Z ι _ V B _ φ
  have hP := (isPullback_SpecMap_of_isPushout _ _ _ _
    (zpf_pushout φ (ι.ker.ideal V))).paste_vert (zpf_sqA X Z ι V)
  refine ⟨⟨_, hP⟩, ?_⟩
  intro U hU
  have hr : ∀ x, (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) x ∈ Set.range ι ↔
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((ι.ker.ideal V).map φ)))) := by
    intro x; constructor
    · rintro ⟨y, hy⟩
      obtain ⟨a, ha, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
      refine ⟨hP.isoPullback.inv a, ?_⟩
      rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_fst]; exact ha
    · rintro ⟨a, rfl⟩
      exact ⟨_, (Scheme.Hom.comp_apply _ _ a).symm.trans
        ((congrArg (fun k => k a) hP.w.symm).trans (Scheme.Hom.comp_apply _ _ a))⟩
  ext x
  have h1 : x ∈ off B ((ι.ker.ideal V).map φ) ↔ x ∉ PrimeSpectrum.zeroLocus (((ι.ker.ideal V).map φ : Ideal B) : Set B) :=
    Iff.rfl
  have h2 : x ∈ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ U ↔
      (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) x ∈ (U : Set X) := Iff.rfl
  simp only [SetLike.mem_coe]
  rw [h1, h2, hU, Set.mem_compl_iff, hr, zpf_range_mk]
  exact Iff.rfl
end TubeCut
end CohomologicalPurity
end LateralTheory
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

instance sch_preservesLimits : PreservesLimitsOfSize.{0, 0} sch := by
  unfold sch
  infer_instance

theorem sch_isPullback {P X Y Z : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) : IsPullback (sch.map fst) (sch.map snd) (sch.map f) (sch.map g) :=
  h.map sch

theorem isPullback_resLE {Y X : Scheme.{0}} (w : Y ⟶ X) (U : X.Opens) :
    IsPullback (w ⁻¹ᵁ U).ι (w.resLE U (w ⁻¹ᵁ U) le_rfl) w U.ι := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact (isPullback_morphismRestrict w U).flip

theorem LeafAbv_of : LeafAbv := by
  intro Y X w U' U h
  subst h
  have hP := sch_isPullback (isPullback_resLE w U)
  refine ⟨Arrow.isoMk hP.isoPullback (Iso.refl _) ?_, rfl, ?_⟩
  · simp [opn, abv]
  · apply Arrow.hom_ext
    · rw [Arrow.comp_left]
      exact hP.isoPullback_hom_snd
    · rw [Arrow.comp_right]
      exact Category.id_comp _

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def chainsP (R : Type) [CommRing R] : Spc ⥤ ChainComplex (Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) ℕ :=
  (SimplicialObject.whiskering _ _).obj (freeP R) ⋙ AlgebraicTopology.alternatingFaceMapComplex _

def LeafQisLocal : Prop := ∀ (R : Type) [CommRing R] (E E' : Spc) (f : E ⟶ E'),
  (∀ n, Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map f) n)) →
  (∀ n, Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map f) n)) →
  QuasiIso ((chains R).map f)

def LeafAugLocal : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ),
    Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map (aug _ hc)) n) ∧
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (HomologicalComplex.homologyMap ((chainsP R).map (aug _ hc)) n)

theorem LeafLocCutAug.goal_of (hq : LeafQisLocal) (hl : LeafAugLocal) : EtaleLocAug := by
  intro J _ D X c ho hcov hdir hc R _
  exact hq R _ _ (aug _ hc) (fun n => (hl J D X c ho hcov hdir hc R n).1) (fun n => (hl J D X c ho hcov hdir hc R n).2)

theorem LeafLocCutAll.goal_of (hb : EtaleLocBase) (hq : LeafQisLocal) (hl : LeafAugLocal) : LeafLoc :=
  LeafLocCut.goal_of hb (LeafLocCutAug.goal_of hq hl)

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafHensH : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (C : Type) [CommRing C] (K : Ideal C), HenselianRing C K →
  IsUnit (q : C) → ∀ i : ℤ, Eqv (ZMod q) (spMap (Ideal.Quotient.mk K)) (tw q i)

def LeafAffQuot : Prop := LeafQuot → ∀ (d : ℕ) (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
  (ψ : MvPolynomial (Fin d) R →+* B) (η : B →+* C), Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) →
  ∀ (I : Ideal B) (K : Ideal C), IndNbhd η I → K = I.map η →
  Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) = I →
  Function.Bijective ((Ideal.Quotient.mk K).comp (η.comp (ψ.comp MvPolynomial.C)))

def LeafExcAff : Prop := Hyp → LeafIndExc → ∀ (d q : ℕ) [NeZero q] (R B C : Type) [CommRing R] [CommRing B] [CommRing C]
  (ψ : MvPolynomial (Fin d) R →+* B) (η : B →+* C), IsUnit (q : R) →
  Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) → ∀ (I : Ideal B) (K : Ideal C), IndNbhd η I → K = I.map η →
  Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) = I → ∃ h,
  Exc q (opnMap (Spec.map (CommRingCat.ofHom (η.comp ψ))) (off C K) (off _ (Ideal.span (Set.range MvPolynomial.X))) h)

theorem spMap_comp' {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  change sch.map _ = sch.map _ ≫ sch.map _
  rw [← Functor.map_comp, ← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  change sch.map (Spec.map (𝟙 _)) = _
  rw [Spec.map_id, CategoryTheory.Functor.map_id]

theorem eqv_spMap_bij {A B : Type} [CommRing A] [CommRing B] (e : A →+* B) (he : Function.Bijective e)
    {S : Type} [CommRing S] (F : Shv S) : Eqv S (spMap e) F := by
  let E := RingEquiv.ofBijective e he
  have h1 : (E.symm : B →+* A).comp e = RingHom.id A := by ext x; exact E.symm_apply_apply x
  have h2 : e.comp (E.symm : B →+* A) = RingHom.id B := by ext x; exact E.apply_symm_apply x
  have : IsIso (spMap e) := ⟨⟨spMap (E.symm : B →+* A), by rw [← spMap_comp', h2, spMap_id'],
    by rw [← spMap_comp', h1, spMap_id']⟩⟩
  exact eqv_iso _ F

theorem LeafPrdAff_of (hT : LeafThom) (hA : LeafActNat) (h1 : LeafHensH) (h2 : LeafAffQuot) (h3 : LeafExcAff)
    (hQ : LeafQuot) (hI : LeafIndExc) : LeafPrdAff := by
  intro hyp d q _ R B C _ _ _ ψ η hq hψ I K hη hK hH hI' hy n i
  have hth : IsThom d (thom d) := @pick_spec _ ⟨fun _ _ _ _ _ _ => 0⟩ _ (hT hyp d)
  have hqP : IsUnit (q : MvPolynomial (Fin d) R) := by simpa using hq.map (MvPolynomial.C : R →+* MvPolynomial (Fin d) R)
  have hqC : IsUnit (q : C) := by simpa using hq.map ((η.comp ψ).comp MvPolynomial.C)
  obtain ⟨h, hE⟩ := h3 hyp hI d q R B C ψ η hq hψ I K hη hK hI'
  have hnat := (hth q).1 (MvPolynomial (Fin d) R) C (η.comp ψ) (Ideal.span (Set.range MvPolynomial.X)) K MvPolynomial.X rfl
    hy h hqP
  have hg := (hth q).2.2.1 R (Ideal.span (Set.range MvPolynomial.X)) rfl hq n i
  let p := pull (ZMod q) (spMap ((η.comp ψ).comp (MvPolynomial.C : R →+* MvPolynomial (Fin d) R))) (tw q i) n
  have hmk := h1 hyp q C K hH hqC i n
  have he := eqv_spMap_bij _ (h2 hQ d R B C ψ η hψ I K hη hK hI') (tw q i) n
  have hp : Function.Bijective p := by
    rw [spMap_comp'] at he
    have e2 : (pull (ZMod q) (spMap (Ideal.Quotient.mk K) ≫ spMap (η.comp (ψ.comp MvPolynomial.C))) (tw q i) n : _ → _) =
        (pull (ZMod q) (spMap (Ideal.Quotient.mk K)) (tw q i) n) ∘ p := funext fun x => pull_comp _ _ _ _ _ x
    rw [e2] at he
    exact (Function.Bijective.of_comp_iff' hmk p).1 he
  have hpb : ∀ b, p b = pull (ZMod q) (spMap (η.comp ψ)) (tw q i) n (pull (ZMod q) (spMap MvPolynomial.C) (tw q i) n b) :=
    fun b => by
      change pull _ _ _ _ b = _
      rw [← pull_comp, ← spMap_comp']
  refine (Function.Bijective.of_comp_iff _ hp).1 ?_
  have key := (hE (n + 2 * d) (i + d)).comp hg
  convert key using 1
  funext b
  refine Eq.trans ?_ (hA hyp.2.2.2.2.1 q _ _ _ n (2 * d) i d _ _).symm
  rw [hnat, Function.comp_apply, hpb]
  rfl

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem LeafQuot_of : LeafQuot := by
  intro A B _ _ φ I h
  obtain ⟨J, _, _, D, s, t, ⟨hc⟩, hj⟩ := h
  have hst : ∀ j (a : A), (t.app j).hom ((s.app j).hom a) = φ a := fun j a =>
    congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of B => f.hom a) (hj j).2
  have sn : ∀ {j k : J} (f : j ⟶ k), (D.map f).hom.comp (s.app j).hom = (s.app k).hom := by
    intro j k f
    have := s.naturality f
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
    rw [this]; rfl
  have tn : ∀ {j k : J} (f : j ⟶ k) (y : D.obj j), (t.app k).hom ((D.map f).hom y) = (t.app j).hom y := by
    intro j k f y
    have := t.naturality f
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
    exact congrArg (fun g : D.obj j ⟶ CommRingCat.of B => g.hom y) this
  have mv : ∀ {j k : J} (f : j ⟶ k) (y : D.obj j), y ∈ I.map (s.app j).hom →
      (D.map f).hom y ∈ I.map (s.app k).hom := by
    intro j k f y hy
    have := Ideal.mem_map_of_mem (D.map f).hom hy
    rwa [Ideal.map_map, sn f] at this
  have rep : ∀ b : B, ∃ j, ∃ y : D.obj j, (t.app j).hom y = b := fun b =>
    Concrete.isColimit_exists_rep D hc b
  have mem : ∀ x ∈ I.map φ, ∃ j, ∃ y : D.obj j, y ∈ I.map (s.app j).hom ∧ (t.app j).hom y = x := by
    intro x hx
    obtain ⟨j0⟩ := IsFiltered.nonempty (C := J)
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, ha, rfl⟩ := h
      exact ⟨j0, (s.app j0).hom a, Ideal.mem_map_of_mem _ ha, hst j0 a⟩
    | zero => exact ⟨j0, 0, zero_mem _, map_zero _⟩
    | add x x' _ _ h h' =>
      obtain ⟨j, y, hy, rfl⟩ := h
      obtain ⟨k, y', hy', rfl⟩ := h'
      refine ⟨IsFiltered.max j k, (D.map (IsFiltered.leftToMax j k)).hom y + (D.map (IsFiltered.rightToMax j k)).hom y',
        add_mem (mv _ _ hy) (mv _ _ hy'), ?_⟩
      rw [map_add (f := _), tn, tn]
    | smul b x _ h =>
      obtain ⟨j, y, hy, rfl⟩ := h
      obtain ⟨k, c, rfl⟩ := rep b
      refine ⟨IsFiltered.max k j, (D.map (IsFiltered.leftToMax k j)).hom c * (D.map (IsFiltered.rightToMax k j)).hom y,
        Ideal.mul_mem_left _ _ (mv _ _ hy), ?_⟩
      rw [map_mul, tn, tn]; rfl
  constructor
  · intro u v huv
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.Quotient.eq] at huv
    rw [Ideal.Quotient.eq]
    rw [← map_sub] at huv
    obtain ⟨j, y, hy, hy'⟩ := mem _ huv
    rw [← hst j] at hy'
    obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc y ((s.app j).hom (a - a')) hy'
    have h1 : (s.app k).hom (a - a') ∈ I.map (s.app k).hom := by
      have e : (D.map g).hom ((s.app j).hom (a - a')) = (D.map f).hom y := hfg.symm
      have e2 : ((D.map g).hom.comp (s.app j).hom) (a - a') = (s.app k).hom (a - a') :=
        congrArg (fun r : A →+* D.obj k => r (a - a')) (sn g)
      rw [← e2]
      have := mv f y hy
      rw [← e] at this
      exact this
    have h2 := (hj k).1.2.1 (a₁ := Ideal.Quotient.mk I (a - a')) (a₂ := 0) (by
      rw [Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]; exact h1)
    exact (Ideal.Quotient.eq_zero_iff_mem).1 h2
  · intro w
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨j, y, rfl⟩ := rep b
    obtain ⟨u, hu⟩ := (hj j).1.2.2 (Ideal.Quotient.mk _ y)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
    refine ⟨Ideal.Quotient.mk I a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hu
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    have hc' : (t.app j).hom.comp (s.app j).hom = φ :=
      congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of B => f.hom) (hj j).2
    have := Ideal.mem_map_of_mem (t.app j).hom hu
    rw [Ideal.map_map, hc', map_sub, hst] at this
    exact this

end LateralTheory.CohomologicalPurity.TubeCut
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex
namespace LateralTheory.CohomologicalPurity.TubeCut

variable {d : ℕ}

theorem hmap_congr (H : Hens) {A B : Type} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B} {φ ψ : A →+* B}
    (e : φ = ψ) (h : I ≤ J.comap φ) (h' : I ≤ J.comap ψ) : H.map φ h = H.map ψ h' := by subst e; rfl

theorem hmap_sq (H : Hens) {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    {I : Ideal A} {J : Ideal B} {K : Ideal C} {L : Ideal D} (a : A →+* B) (b : B →+* D) (c : A →+* C) (e : C →+* D)
    (ha : I ≤ J.comap a) (hb : J ≤ L.comap b) (hc : I ≤ K.comap c) (he : K ≤ L.comap e) (e0 : b.comp a = e.comp c) :
    (H.map b hb).comp (H.map a ha) = (H.map e he).comp (H.map c hc) := by
  rw [← H.map_comp a b ha hb (fun x hx => hb (ha hx)), ← H.map_comp c e hc he (fun x hx => he (hc hx))]
  exact hmap_congr H e0 _ _

theorem appLE_congr {X Y : Scheme.{0}} {u v : X ⟶ Y} (e : u = v) (U : Y.Opens) (W : X.Opens) (h : W ≤ u ⁻¹ᵁ U) :
    u.appLE U W h = v.appLE U W (e ▸ h) := by subst e; rfl

theorem idl {P' P : SP d} (φ : P'.Hom P) (V : P.X.affineOpens) (V' : P'.X.affineOpens) (h : V'.1 ≤ φ.f ⁻¹ᵁ V.1) :
    P.ι.ker.ideal V ≤ (P'.ι.ker.ideal V').comap (φ.f.appLE V.1 V'.1 h).hom := by
  have := P.cl; have := P'.cl
  intro a ha
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at ha
  rw [Ideal.mem_comap, Scheme.Hom.ker_apply, RingHom.mem_ker]
  rw [← CommRingCat.comp_apply, P'.ι.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr φ.cart.w,
    Scheme.Hom.comp_appLE, CommRingCat.comp_apply, ha, map_zero]

theorem cotangentAtUnit_tangentBijection_naturality (H : Hens) {P' P : SP d} (φ : P'.Hom P) (V1 V2 : P.X.affineOpens) (V1' V2' : P'.X.affineOpens)
    (h1 : V1'.1 ≤ φ.f ⁻¹ᵁ V1.1) (h2 : V2'.1 ≤ φ.f ⁻¹ᵁ V2.1) (hV : V1 ≤ V2) (hV' : V1' ≤ V2') :
    Spec.map (CommRingCat.ofHom (H.map _ (P'.ι.ker.ideal_le_comap_ideal hV'))) ≫
      Spec.map (CommRingCat.ofHom (H.map (φ.f.appLE V2.1 V2'.1 h2).hom (idl φ V2 V2' h2))) =
    Spec.map (CommRingCat.ofHom (H.map (φ.f.appLE V1.1 V1'.1 h1).hom (idl φ V1 V1' h1))) ≫
      Spec.map (CommRingCat.ofHom (H.map _ (P.ι.ker.ideal_le_comap_ideal hV))) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact hmap_sq H _ _ _ _ _ _ _ _ (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE])

theorem henselization_spec_map_commutes_with_smooth_pair_hom (H : Hens) {P' P : SP d} (φ : P'.Hom P) (V : P.X.affineOpens) (V' : P'.X.affineOpens)
    (h : V'.1 ≤ φ.f ⁻¹ᵁ V.1) :
    Spec.map (CommRingCat.ofHom (H.map (φ.f.appLE V.1 V'.1 h).hom (idl φ V V' h))) ≫ hensTo H P V =
      hensTo H P' V' ≫ φ.f := by
  dsimp only [hensTo, eta]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, H.map_η, CommRingCat.ofHom_comp, Spec.map_comp_assoc]
  exact (congrArg (_ ≫ ·) (IsAffineOpen.SpecMap_appLE_fromSpec φ.f V.2 V'.2 h)).trans (Category.assoc _ _ _).symm

abbrev RJ {P' P : SP d} (φ : P'.Hom P) : Type :=
  {p : P'.X.affineOpens × P.X.affineOpens // Good P' p.1 ∧ Good P p.2 ∧ p.1.1 ≤ φ.f ⁻¹ᵁ p.2.1}

def Sys.ref (hC : LateralTheory.CohomologicalPurity.LeafChart) {P' P : SP d} (φ : P'.Hom P) : Sys P' where
  J := RJ φ
  V j := j.1.1
  mono h := (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1
  good j := j.2.1
  cov x := by
    obtain ⟨V, hV, -, g⟩ := hC d P (φ.f x) ⊤ trivial
    obtain ⟨V', hV', l, g'⟩ := hC d P' x (φ.f ⁻¹ᵁ V.1) hV
    exact ⟨⟨(V', V), g', g, l⟩, hV'⟩
  dir x j k hj hk := by
    have hj2 : φ.f x ∈ j.1.2.1 := j.2.2.2 hj
    have hk2 : φ.f x ∈ k.1.2.1 := k.2.2.2 hk
    obtain ⟨V, hV, l, g⟩ := hC d P (φ.f x) (j.1.2.1 ⊓ k.1.2.1) ⟨hj2, hk2⟩
    obtain ⟨V', hV', l', g'⟩ := hC d P' x (j.1.1.1 ⊓ k.1.1.1 ⊓ φ.f ⁻¹ᵁ V.1) ⟨⟨hj, hk⟩, hV⟩
    exact ⟨⟨(V', V), g', g, l'.trans inf_le_right⟩, ⟨l'.trans (inf_le_left.trans inf_le_left), l.trans inf_le_left⟩,
      ⟨l'.trans (inf_le_left.trans inf_le_right), l.trans inf_le_right⟩, hV'⟩

theorem EtaleRefine_of_push (hP : LeafPush) : LeafRefine := by
  intro hC H d P' P φ
  let S' := Sys.ref hC φ
  let G1 : S'.J ⥤ (Sys.all hC P').J := Monotone.functor (f := fun j => (⟨j.1.1, j.2.1⟩ : {V : P'.X.affineOpens // Good P' V}))
    (fun _ _ h => (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1)
  let G2 : S'.J ⥤ (Sys.all hC P).J := Monotone.functor (f := fun j => (⟨j.1.2, j.2.2.1⟩ : {V : P.X.affineOpens // Good P V}))
    (fun _ _ h => (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2)
  let α1 : S'.hen H ⋙ yoneda ⟶ G1 ⋙ (Sys.all hC P').hen H ⋙ yoneda :=
    { app := fun j => (𝟙 ((S'.hen H ⋙ yoneda).obj j) : _ ⟶ (G1 ⋙ (Sys.all hC P').hen H ⋙ yoneda).obj j)
      naturality := fun j k f => (Category.comp_id _).trans (Category.id_comp ((G1 ⋙ (Sys.all hC P').hen H ⋙ yoneda).map f)).symm }
  obtain ⟨a, ha⟩ := hP _ _ _ _ G1 α1 _ _ (𝟙 (yoneda.obj P'.X)) _ _ (S'.cocHen H) ((Sys.all hC P').cocHen H)
    (fun j => (Category.id_comp _).trans (Category.comp_id _).symm)
  have ea : a ≫ (Sys.all hC P').π H = S'.π H := by
    have := ha; rw [disc.map_id, Category.comp_id] at this; exact this
  let α2 : S'.hen H ⋙ yoneda ⟶ G2 ⋙ (Sys.all hC P).hen H ⋙ yoneda :=
    { app := fun j => yoneda.map (Spec.map (CommRingCat.ofHom
        (H.map (φ.f.appLE (j.1.2).1 (j.1.1).1 j.2.2.2).hom (idl φ j.1.2 j.1.1 j.2.2.2))))
      naturality := fun j k f => (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map
        (cotangentAtUnit_tangentBijection_naturality H φ j.1.2 k.1.2 j.1.1 k.1.1 j.2.2.2 k.2.2.2 (Prod.le_def.1 (Subtype.coe_le_coe.2 f.le)).2
          (Prod.le_def.1 (Subtype.coe_le_coe.2 f.le)).1)).trans (yoneda.map_comp _ _)) }
  obtain ⟨b, hb⟩ := hP _ _ _ _ G2 α2 _ _ (yoneda.map φ.f) _ _ (S'.cocHen H) ((Sys.all hC P).cocHen H)
    (fun j => (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map (henselization_spec_map_commutes_with_smooth_pair_hom H φ j.1.2 j.1.1 j.2.2.2)).trans
      (yoneda.map_comp _ _)))
  exact ⟨S', a, b, ea, hb⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def MM {P' P : Arrow Spc} (φ : P' ⟶ P) : Spc := pushout P'.hom (P'.hom ≫ φ.right)

def gM {P' P : Arrow Spc} (φ : P' ⟶ P) : MM φ ⟶ dbl P :=
  pushout.desc (φ.right ≫ dbl.inl P) (dbl.inr P) (by
    rw [← Category.assoc, ← Arrow.w φ, Category.assoc, Category.assoc]
    exact congrArg (φ.left ≫ ·) (pushout.condition (f := P.hom) (g := P.hom)))

def LeafExcOfEqv : Prop := ∀ (q : ℕ) (P' P : Arrow Spc) (φ : P' ⟶ P), (∀ i, Eqv (ZMod q) (gM φ) (tw q i)) → Exc q φ

def LeafEqvOfExc : Prop := ∀ (q : ℕ) (P' P : Arrow Spc) (φ : P' ⟶ P), Exc q φ → ∀ i, Eqv (ZMod q) (gM φ) (tw q i)

def LeafMLev : Prop := ∀ (P' P : Arrow Spc) (φ : P' ⟶ P) (n : SimplexCategoryᵒᵖ),
  ∃ (a : disc.obj ((MM φ).obj n) ≅ MM ((lev n).map φ)) (b : disc.obj ((dbl P).obj n) ≅ dbl ((lev n).obj P)),
    disc.map ((gM φ).app n) ≫ b.hom = a.hom ≫ gM ((lev n).map φ)

theorem LeafExcLevel_of (h1 : LeafExcOfEqv) (h2 : LeafEqvOfExc) (h3 : LeafMLev) : LeafExcLevel := by
  intro a3 q P' P φ hl
  apply h1 q P' P φ
  intro i
  apply a3
  intro n
  obtain ⟨a, b, w⟩ := h3 P' P φ n
  have e : disc.map ((gM φ).app n) = a.hom ≫ gM ((lev n).map φ) ≫ b.inv := by
    rw [← Category.assoc, ← w, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]
  exact eqv_comp (eqv_iso _ _) (eqv_comp (h2 q _ _ _ (hl n) i) (eqv_iso _ _))

end LateralTheory.CohomologicalPurity.TubeCut
end
end
