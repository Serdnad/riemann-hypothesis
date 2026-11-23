module

public import Development.EtaleCohomology.EtaleSheaves.Bundle051
public import Development.EtaleCohomology.EtaleSheaves.Bundle053
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.EmbedPf

def AffClosed : Prop := ∀ (A : Type) [CommRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A))
  [LocallyOfFiniteType p] (V : X.Opens), IsAffineOpen V →
    ∃ (n : ℕ) (e : V.toScheme ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) A))), IsClosedImmersion e ∧
      e ≫ Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A))) = V.ι ≫ p

def Chart : Prop := ∀ (A : Type) [CommRing A] (n : ℕ), ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of A))
  (j : Spec (CommRingCat.of (MvPolynomial (Fin n) A)) ⟶ P), IterLine q ∧ IsOpenImmersion j ∧
    j ≫ q = Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)))

theorem affClosed : AffClosed := by
  intro A _ X p _ V hV
  haveI : IsAffine V.toScheme := hV
  have hfT : LocallyOfFiniteType (V.ι ≫ p) := inferInstance
  have happ := HasRingHomProperty.appTop @LocallyOfFiniteType (V.ι ≫ p) hfT
  let g : CommRingCat.of A ⟶ Γ(V.toScheme, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (V.ι ≫ p).appTop
  have hg : g.hom.FiniteType := by
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact RingHom.FiniteType.comp happ h1
  letI : Algebra A Γ(V.toScheme, ⊤) := g.hom.toAlgebra
  have hft : Algebra.FiniteType A Γ(V.toScheme, ⊤) := hg
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hft
  refine ⟨n, V.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom), ?_, ?_⟩
  · have hs := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ.toRingHom) hφ
    have hi : IsClosedImmersion V.toScheme.toSpecΓ := inferInstance
    exact @IsClosedImmersion.comp _ _ _ _ _ hi hs
  · have hcomp : CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A)) ≫ CommRingCat.ofHom φ.toRingHom = g := by
      ext a
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
      exact φ.commutes a
    have h2 : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin n) A))) =
        Spec.map g := by rw [← Spec.map_comp, hcomp]
    have h3 : V.toScheme.toSpecΓ ≫ Spec.map g = V.ι ≫ p := by
      have hn := Scheme.toSpecΓ_naturality (V.ι ≫ p)
      have h4 : Spec.map g = Spec.map (V.ι ≫ p).appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv :=
        Spec.map_comp _ _
      rw [h4, ← Category.assoc, ← hn, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    refine Eq.trans ?_ h3
    rw [Category.assoc]
    exact congrArg (fun t => V.toScheme.toSpecΓ ≫ t) h2

theorem Embed_of (hA : AffClosed) (hC : Chart) : LateralTheory.E.ChowGraphCut.Embed := by
  intro A _ X p _ V hV
  obtain ⟨n, e, he, hep⟩ := hA A p V hV
  obtain ⟨P, q, j, hq, hj, hjq⟩ := hC A n
  haveI := hj
  haveI := he
  refine ⟨P, q, j.opensRange, e ≫ j.isoOpensRange.hom, hq, inferInstance, ?_⟩
  rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, hjq, hep]

end LateralTheory.E.EmbedPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.IterCompPf

theorem isLine_iso_comp {L L' S : Scheme.{0}} (e : L' ⟶ L) [IsIso e] {l : L ⟶ S} (h : IsLine l) :
    IsLine (e ≫ l) :=
  h.bc (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback e (e ≫ l) l (𝟙 S))

theorem iterLine_iso_comp {T S Y : Scheme.{0}} {k : T ⟶ S} (hk : IterLine k) (e : Y ⟶ T) [IsIso e] :
    IterLine (e ≫ k) := by
  cases hk with
  | iso k' hk' => exact IterLine.iso _ inferInstance
  | comp l k' hl hk' =>
    rw [← Category.assoc]
    exact IterLine.comp _ _ (isLine_iso_comp e hl) hk'

theorem IterComp_of : LateralTheory.E.ChowGraphCut.IterComp := by
  intro P T S l k hl hk
  induction hl with
  | iso e he => exact iterLine_iso_comp hk e
  | comp l₁ k₁ hl₁ _ ih =>
    rw [Category.assoc]
    exact IterLine.comp _ _ hl₁ ih

end LateralTheory.E.IterCompPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf LateralTheory.E.ZarIndPf LateralTheory.E.InjStepPf

namespace LateralTheory.E.OverMVPf

variable {X S : Scheme.{0}}

@[reassoc]
theorem resO_fst (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO p h ≫ pullback.fst p U.ι = pullback.fst p V.ι := by
  simp only [resO, pullback.map, pullback.lift_fst, Category.comp_id]

theorem resO_snd (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO p h ≫ pullback.snd p U.ι ≫ U.ι = pullback.snd p V.ι ≫ V.ι := by
  simp only [resO, pullback.map, pullback.lift_snd_assoc, Category.assoc, Scheme.homOfLE_ι]

instance resO_open (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) : IsOpenImmersion (resO p h) := by
  have : IsOpenImmersion (resO p h ≫ pullback.fst p U.ι) := by rw [resO_fst]; infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst p U.ι)

theorem range_sub {T : Scheme.{0}} (U : S.Opens) (a : T ⟶ U) :
    Set.range (a ≫ U.ι) ⊆ (U : Set S) := by
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι]
  exact ⟨_, rfl⟩

theorem cover (p : X ⟶ S) (V W : S.Opens) :
    Set.range (resO p (le_sup_left : V ≤ V ⊔ W)) ∪ Set.range (resO p (le_sup_right : W ≤ V ⊔ W)) = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  have hy : p (pullback.fst p (V ⊔ W).ι y) ∈ ((V ⊔ W : S.Opens) : Set S) := by
    have := range_sub (V ⊔ W) (pullback.snd p (V ⊔ W).ι) ⟨y, rfl⟩
    rwa [← pullback.condition, Scheme.Hom.comp_apply] at this
  have inj := (pullback.fst p (V ⊔ W).ι).isOpenEmbedding.injective
  rcases hy with hV | hW
  · obtain ⟨s, hs⟩ : p (pullback.fst p (V ⊔ W).ι y) ∈ Set.range V.ι := by rwa [Scheme.Opens.range_ι]
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := V.ι) _ s hs.symm
    left; refine ⟨z, inj ?_⟩
    rw [← Scheme.Hom.comp_apply, resO_fst, hz]
  · obtain ⟨s, hs⟩ : p (pullback.fst p (V ⊔ W).ι y) ∈ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := W.ι) _ s hs.symm
    right; refine ⟨z, inj ?_⟩
    rw [← Scheme.Hom.comp_apply, resO_fst, hz]

abbrev PP (p : X ⟶ S) (V W : S.Opens) : Scheme.{0} :=
  pullback (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W))

abbrev g0 (p : X ⟶ S) (V W : S.Opens) : PP p V W ⟶ S := pullback.fst _ _ ≫ pullback.fst p V.ι ≫ p

theorem overOpenPullbackStructureMap_eq_via_left_open (p : X ⟶ S) (V W : S.Opens) : g0 p V W = pullback.fst _ _ ≫ pullback.snd p V.ι ≫ V.ι := by
  rw [g0, pullback.condition]

theorem overOpenPullbackStructureMap_eq_via_right_open (p : X ⟶ S) (V W : S.Opens) : g0 p V W = pullback.snd _ _ ≫ pullback.snd p W.ι ≫ W.ι := by
  rw [g0, ← pullback.condition, ← resO_fst_assoc p (le_sup_left : V ≤ V ⊔ W), pullback.condition_assoc, resO_fst_assoc]

theorem overOpenPullbackStructureMap_range_subset_inter (p : X ⟶ S) (V W : S.Opens) :
    Set.range (g0 p V W) ⊆ Set.range (V ⊓ W).ι := by
  rw [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_inf]
  intro s hs
  refine ⟨?_, ?_⟩
  · rw [overOpenPullbackStructureMap_eq_via_left_open, ← Category.assoc] at hs; exact range_sub V _ hs
  · rw [overOpenPullbackStructureMap_eq_via_right_open, ← Category.assoc] at hs; exact range_sub W _ hs

def kk (p : X ⟶ S) (V W : S.Opens) : PP p V W ⟶ overO p (V ⊓ W) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst p V.ι) (IsOpenImmersion.lift (V ⊓ W).ι (g0 p V W) (overOpenPullbackStructureMap_range_subset_inter p V W))
    (by rw [IsOpenImmersion.lift_fac, Category.assoc])

def ee (p : X ⟶ S) (V W : S.Opens) : overO p (V ⊓ W) ⟶ PP p V W :=
  pullback.lift (resO p (inf_le_left : V ⊓ W ≤ V)) (resO p (inf_le_right : V ⊓ W ≤ W))
    (by rw [resO_comp, resO_comp])

@[reassoc]
theorem kk_fst' (p : X ⟶ S) (V W : S.Opens) : kk p V W ≫ pullback.fst p (V ⊓ W).ι = pullback.fst _ _ ≫ pullback.fst p V.ι := by
  simp only [kk, pullback.lift_fst]

theorem kk_snd' (p : X ⟶ S) (V W : S.Opens) : kk p V W ≫ pullback.snd p (V ⊓ W).ι ≫ (V ⊓ W).ι = g0 p V W := by
  simp only [kk, pullback.lift_snd_assoc, IsOpenImmersion.lift_fac]

theorem kk_l (p : X ⟶ S) (V W : S.Opens) : kk p V W ≫ resO p (inf_le_left : V ⊓ W ≤ V) = pullback.fst _ _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, resO_fst, kk_fst']
  · rw [← cancel_mono V.ι, Category.assoc, Category.assoc, resO_snd, kk_snd', overOpenPullbackStructureMap_eq_via_left_open, Category.assoc]

theorem kk_r (p : X ⟶ S) (V W : S.Opens) : kk p V W ≫ resO p (inf_le_right : V ⊓ W ≤ W) = pullback.snd _ _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, resO_fst, kk_fst', ← resO_fst p (le_sup_left : V ≤ V ⊔ W), pullback.condition_assoc, resO_fst]
  · rw [← cancel_mono W.ι, Category.assoc, Category.assoc, resO_snd, kk_snd', overOpenPullbackStructureMap_eq_via_right_open, Category.assoc]

theorem kk_ee (p : X ⟶ S) (V W : S.Opens) : kk p V W ≫ ee p V W = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, ee, pullback.lift_fst, kk_l, Category.id_comp]
  · rw [Category.assoc, ee, pullback.lift_snd, kk_r, Category.id_comp]

theorem ee_kk (p : X ⟶ S) (V W : S.Opens) : ee p V W ≫ kk p V W = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, kk_fst', ee, pullback.lift_fst_assoc, resO_fst, Category.id_comp]
  · rw [← cancel_mono (V ⊓ W).ι, Category.assoc, Category.assoc, kk_snd', g0, ee, pullback.lift_fst_assoc,
      resO_fst_assoc, pullback.condition, Category.id_comp]

theorem ee_fst (p : X ⟶ S) (V W : S.Opens) : ee p V W ≫ pullback.fst _ _ = resO p (inf_le_left : V ⊓ W ≤ V) := by
  simp only [ee, pullback.lift_fst]

theorem ee_snd (p : X ⟶ S) (V W : S.Opens) : ee p V W ≫ pullback.snd _ _ = resO p (inf_le_right : V ⊓ W ≤ W) := by
  simp only [ee, pullback.lift_snd]

@[reassoc]
theorem fO_fst {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    fO f p U ≫ pullback.fst p U.ι = pullback.fst (f ≫ p) U.ι ≫ f := by
  simp only [fO, pullback.map, pullback.lift_fst]

@[reassoc]
theorem fO_snd {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    fO f p U ≫ pullback.snd p U.ι = pullback.snd (f ≫ p) U.ι := by
  simp only [fO, pullback.map, pullback.lift_snd, Category.comp_id]

theorem kk_nat {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (V W : S.Opens) :
    kk (f ≫ p) V W ≫ fO f p (V ⊓ W) = pullback.map _ _ _ _ (fO f p V) (fO f p W) (fO f p (V ⊔ W))
      (fO_res f p le_sup_left) (fO_res f p le_sup_right) ≫ kk p V W := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, fO_fst, kk_fst'_assoc, kk_fst', pullback.lift_fst_assoc, Category.assoc, fO_fst]
  · rw [← cancel_mono (V ⊓ W).ι, Category.assoc, Category.assoc, Category.assoc, Category.assoc, fO_snd_assoc, kk_snd',
      kk_snd', g0, g0, pullback.lift_fst_assoc, Category.assoc, fO_fst_assoc]

theorem OverMV_of : OverMV := by
  intro hM hH q Y X S f p i m V W
  obtain ⟨δ, hex, hnat⟩ := hM hH (ZMod q) (tw q i)
  have cX := cover p V W
  have cY := cover (f ≫ p) V W
  refine ⟨(δ (resO p le_sup_left) (resO p le_sup_right) m).comp (pull _ (sch.map (kk p V W)) _ m),
    (δ (resO (f ≫ p) le_sup_left) (resO (f ≫ p) le_sup_right) m).comp (pull _ (sch.map (kk (f ≫ p) V W)) _ m),
    ?_, ?_, ?_, ?_⟩
  · intro x h1 h2
    obtain ⟨w', hw'⟩ := ((hex _ _ cX m).2.2 x).1 ⟨h1, h2⟩
    refine ⟨pull _ (sch.map (ee p V W)) _ _ w', ?_⟩
    rw [AddMonoidHom.comp_apply, ← pull_comp, ← Functor.map_comp, kk_ee, CategoryTheory.Functor.map_id, pull_id, hw']
  · intro a b
    rw [AddMonoidHom.comp_apply, map_sub, ← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, kk_l, kk_r]
    exact ((hex _ _ cX m).2.1 _).2 ⟨a, b, rfl⟩
  · intro w hw
    obtain ⟨a, b, hab⟩ := ((hex _ _ cY m).2.1 _).1 hw
    refine ⟨a, b, ?_⟩
    have e : w = pull _ (sch.map (ee (f ≫ p) V W)) _ _ (pull _ (sch.map (kk (f ≫ p) V W)) _ _ w) := by
      rw [← pull_comp, ← Functor.map_comp, ee_kk, CategoryTheory.Functor.map_id, pull_id]
    rw [e, hab, map_sub, ← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, ee_fst, ee_snd]
  · intro w
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← pull_comp, ← Functor.map_comp, kk_nat, Functor.map_comp,
      pull_comp, hnat _ _ _ _ cY cX]

end LateralTheory.E.OverMVPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut LateralTheory.E.ChowGraphCut

namespace LateralTheory.E.ProdPf

theorem iterLine_of_isPullback {S P : Scheme.{0}} {q : P ⟶ S} (hq : IterLine q) :
    ∀ {X P' : Scheme.{0}} (g : X ⟶ S) (a : P' ⟶ P) (q' : P' ⟶ X), IsPullback a q' q g → IterLine q' := by
  induction hq with
  | iso e he =>
    intro X P' g a q' h
    have : IsIso (pullback.snd e g) := inferInstance
    have hq' : q' = h.isoPullback.hom ≫ pullback.snd e g := (IsPullback.isoPullback_hom_snd h).symm
    rw [hq']
    exact IterLine.iso _ inferInstance
  | comp l k hl _ ih =>
    intro X P' g a q' h
    have w : q' ≫ g = (a ≫ l) ≫ k := by rw [Category.assoc, ← h.w]
    let m := pullback.lift q' (a ≫ l) w
    have hb : IsPullback (pullback.snd g k) (pullback.fst g k) k g := (IsPullback.of_hasPullback g k).flip
    have e1 : m ≫ pullback.fst g k = q' := pullback.lift_fst _ _ _
    have e2 : m ≫ pullback.snd g k = a ≫ l := pullback.lift_snd _ _ _
    have hs : IsPullback a (m ≫ pullback.fst g k) (l ≫ k) g := by
      rw [e1]; exact h
    have ht : IsPullback a m l (pullback.snd g k) := IsPullback.of_bot hs e2.symm hb
    have hm : IsLine m := hl.bc ht
    have e : q' = m ≫ pullback.fst g k := e1.symm
    rw [e]
    exact IterLine.comp _ _ hm (ih g (pullback.snd g k) (pullback.fst g k) hb)

theorem exists_widePullback_of_iteratedLine (hI : IterComp) {S : Scheme.{0}} : ∀ (n : ℕ) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S),
    (∀ j, IterLine (qj j)) →
    ∃ (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j), IterLine q ∧ (∀ j, π j ≫ qj j = q) ∧
      ∀ {T : Scheme.{0}} (t : T ⟶ S) (f : ∀ j, T ⟶ Pj j), (∀ j, f j ≫ qj j = t) →
        ∃! g : T ⟶ P, g ≫ q = t ∧ ∀ j, g ≫ π j = f j := by
  intro n
  induction n with
  | zero =>
    intro Pj qj _
    refine ⟨S, 𝟙 S, fun j => j.elim0, IterLine.iso _ inferInstance, fun j => j.elim0, ?_⟩
    intro T t f _
    refine ⟨t, ⟨by simp, fun j => j.elim0⟩, ?_⟩
    rintro g ⟨hg, -⟩
    simpa using hg
  | succ n ih =>
    intro Pj qj hqj
    obtain ⟨P0, q0, π0, hq0, hπ0, hU0⟩ := ih (fun j => Pj j.succ) (fun j => qj j.succ) (fun j => hqj j.succ)
    have hfst : IterLine (pullback.fst q0 (qj 0)) :=
      iterLine_of_isPullback (hqj 0) q0 (pullback.snd q0 (qj 0)) (pullback.fst q0 (qj 0))
        (IsPullback.of_hasPullback q0 (qj 0)).flip
    let π : ∀ j, pullback q0 (qj 0) ⟶ Pj j :=
      Fin.cases (motive := fun j => pullback q0 (qj 0) ⟶ Pj j) (pullback.snd q0 (qj 0))
        (fun j => pullback.fst q0 (qj 0) ≫ π0 j)
    have hπ0' : π 0 = pullback.snd q0 (qj 0) := rfl
    have hπs : ∀ j : Fin n, π j.succ = pullback.fst q0 (qj 0) ≫ π0 j := fun j => rfl
    refine ⟨pullback q0 (qj 0), pullback.fst q0 (qj 0) ≫ q0, π, hI _ _ hfst hq0, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · rw [hπ0', ← pullback.condition]
      · rw [hπs, Category.assoc, hπ0]
    · intro T t f hf
      obtain ⟨g0, ⟨hg0q, hg0π⟩, hu⟩ := hU0 t (fun j => f j.succ) (fun j => hf j.succ)
      have w : g0 ≫ q0 = f 0 ≫ qj 0 := by rw [hg0q, hf 0]
      refine ⟨pullback.lift g0 (f 0) w, ⟨?_, ?_⟩, ?_⟩
      · rw [← Category.assoc, pullback.lift_fst, hg0q]
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · rw [hπ0', pullback.lift_snd]
        · rw [hπs, ← Category.assoc, pullback.lift_fst, hg0π]
      · rintro g' ⟨hg'q, hg'π⟩
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
          apply hu
          refine ⟨by rw [Category.assoc, hg'q], fun j => ?_⟩
          rw [Category.assoc, ← hπs, hg'π]
        · rw [pullback.lift_snd, ← hπ0', hg'π]

theorem Prod_of (hI : IterComp) : LateralTheory.E.ChowGraphCut.Prod := by
  intro S n Pj qj hq
  exact exists_widePullback_of_iteratedLine hI n Pj qj hq

end LateralTheory.E.ProdPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.FibPf LateralTheory.E.FibClosedPf LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibreEqvPf

theorem eqv_snd_snd {q : ℕ} {i : ℤ} {Z S K L : Scheme.{0}} (c : Z ⟶ S) (t : L ⟶ S) (k : K ⟶ L) :
    Eqv _ (sch.map (pullback.snd (pullback.snd c t) k)) (tw q i) ↔ Eqv _ (sch.map (pullback.snd c (k ≫ t))) (tw q i) := by
  have e := pullbackLeftPullbackSndIso_hom_snd c t k
  rw [← e, Functor.map_comp]
  exact ⟨fun h => eqv_right h (eqv_iso (pullbackLeftPullbackSndIso c t k) q i), fun h => eqv_comp (eqv_iso _ q i) h⟩

theorem eqv_snd_iso {q : ℕ} {i : ℤ} {Z S K K' : Scheme.{0}} (c : Z ⟶ S) (T : K ⟶ S) (ρ : K' ⟶ K) [IsIso ρ]
    (h : Eqv _ (sch.map (pullback.snd c T)) (tw q i)) : Eqv _ (sch.map (pullback.snd c (ρ ≫ T))) (tw q i) := by
  rw [← eqv_snd_snd]
  have w : sch.map (pullback.snd (pullback.snd c T) ρ) ≫ sch.map ρ = sch.map (pullback.fst (pullback.snd c T) ρ) ≫ sch.map (pullback.snd c T) := by
    rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  refine eqv_left (g := sch.map ρ) ?_ (eqv_iso (asIso ρ) q i)
  rw [w]
  exact eqv_comp (eqv_iso (asIso (pullback.fst (pullback.snd c T) ρ)) q i) h

def StalkFib : Prop := Hyp → HZero → AICAcyc → ∀ (q : ℕ) (i : ℤ) {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c]
  [QuasiSeparated c] [IsDominant c], AICSch Z → AICSch S → ∀ x : S, IsUnit (q : S.presheaf.stalk x) →
  Eqv _ (sch.map (pullback.snd c (S.fromSpecStalk x))) (tw q i)

theorem residue_bij {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (f : R →+* R') [IsLocalHom f]
    (hf : Function.Surjective f) : Function.Bijective (IsLocalRing.ResidueField.map f) := by
  refine ⟨(IsLocalRing.ResidueField.map f).injective, fun y => ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨IsLocalRing.residue R x, IsLocalRing.ResidueField.map_residue f x⟩

theorem geom (H : Hyp) (h0 : HZero) (hA : AICAcyc) (hS : StalkSHS) (hF : StalkFib) (q : ℕ) (i : ℤ) {Z S : Scheme.{0}}
    (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c] (hZs : AICSch Z) (hSs : AICSch S)
    (hB : ∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t))
    (x : S) (hu : IsUnit (q : S.presheaf.stalk x)) :
    Eqv _ (sch.map (pullback.snd c (cpt (S.presheaf.stalk x) ≫ S.fromSpecStalk x))) (tw q i) := by
  have hsh := hS S hSs x
  obtain ⟨_, _⟩ := id hsh
  have hx := hF H h0 hA q i c hZs hSs x hu
  have hpb : Eqv _ (sch.map (pullback.fst (pullback.snd c (S.fromSpecStalk x)) (cpt (S.presheaf.stalk x)))) (tw q i) :=
    hB _ hsh hu (S.fromSpecStalk x)
  have hE1 : Eqv _ (sch.map (cpt (S.presheaf.stalk x))) (tw q i) := H.e1 q _ (IsLocalRing.maximalIdeal _) hu i
  rw [← eqv_snd_snd]
  refine eqv_left (g := sch.map (cpt (S.presheaf.stalk x))) ?_ hE1
  rw [← Functor.map_comp, ← pullback.condition, Functor.map_comp]
  exact eqv_comp hpb hx

theorem FibreEqv_of (hS : StalkSHS) (hF : StalkFib) : FibreEqv := by
  intro H h0 hA q i A _ _ hq Z S c p _ _ _ _ _ hZs hSs hB s
  set j := pullback.fst p (cpt A)
  have h1 : SurjectiveOnStalks (cpt A) :=
    SurjectiveOnStalks.Spec_iff.2 (RingHom.surjectiveOnStalks_of_surjective IsLocalRing.residue_surjective)
  have h2 : SurjectiveOnStalks j := MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback p (cpt A)).flip h1
  have hsurj : Function.Surjective (j.stalkMap s).hom := j.stalkMap_surjective s
  have hu0 : IsUnit (q : Γ(S, ⊤)) := unit_of hq p
  have hu : IsUnit (q : S.presheaf.stalk (j s)) := by
    simpa using hu0.map (S.presheaf.germ ⊤ (j s) trivial).hom
  have hbij := residue_bij (j.stalkMap s).hom hsurj
  let ρ : Spec (CommRingCat.of (IsLocalRing.ResidueField ((pullback p (cpt A)).presheaf.stalk s))) ⟶
      Spec (CommRingCat.of (IsLocalRing.ResidueField (S.presheaf.stalk (j s)))) :=
    Spec.map (RingEquiv.ofBijective _ hbij).toCommRingCatIso.hom
  have sq : cpt ((pullback p (cpt A)).presheaf.stalk s) ≫ (pullback p (cpt A)).fromSpecStalk s ≫ j =
      ρ ≫ cpt (S.presheaf.stalk (j s)) ≫ S.fromSpecStalk (j s) := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk j, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [ρ, cpt, ← Spec.map_comp]
    congr 1
  rw [eqv_snd_snd, sq]
  exact eqv_snd_iso c _ ρ (geom H h0 hA hS hF q i c hZs hSs hB (j s) hu)

end LateralTheory.E.FibreEqvPf

namespace LateralTheory.E.FibreEqvPf

def BaseAIC : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, AICSch (pullback c (S.fromSpecStalk x))

def StalkAIC : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, AICSch (Spec (S.presheaf.stalk x))

theorem StalkFib_of (hZB : BaseAIC) (hSA : StalkAIC) : StalkFib := by
  intro H h0 hA q i Z S c _ _ _ hZs hSs x hu
  have hB := hZB c hZs hSs x
  have hK := hSA S hSs x
  have : IsIntegral (pullback c (S.fromSpecStalk x) : Scheme.{0}) := hB.1
  have : ConnectedSpace (pullback c (S.fromSpecStalk x) : Scheme.{0}) := inferInstance
  have : CompactSpace (pullback c (S.fromSpecStalk x) : Scheme.{0}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd c (S.fromSpecStalk x))
  have : QuasiSeparatedSpace (pullback c (S.fromSpecStalk x) : Scheme.{0}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd c (S.fromSpecStalk x))
  have hu1 : IsUnit (q : Γ(Spec (S.presheaf.stalk x), ⊤)) := unit_of (A := S.presheaf.stalk x) hu (𝟙 _)
  have hu2 : IsUnit (q : Γ(pullback c (S.fromSpecStalk x), ⊤)) :=
    unit_of (A := S.presheaf.stalk x) hu (pullback.snd c (S.fromSpecStalk x))
  exact eqv_of H.a9 _ (h0 H q (pullback.snd c (S.fromSpecStalk x)) hK inferInstance hu1 i) (fun n hn => hA H q _ hB hu2 n i hn)
    (fun n hn => hA H q _ hK hu1 n i hn)

end LateralTheory.E.FibreEqvPf

namespace LateralTheory.E.FibreEqvPf

def StalkAICRing : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, AIC (S.presheaf.stalk x)

def SpecAIC : Prop := ∀ (B : CommRingCat.{0}), IsDomain B → AIC B → AICSch (Spec B)

theorem StalkAIC_of (h1 : StalkAICRing) (h2 : SpecAIC) : StalkAIC := by
  intro S hS x
  have : IsIntegral S := hS.1
  exact h2 _ inferInstance (h1 S hS x)

end LateralTheory.E.FibreEqvPf
end
end
