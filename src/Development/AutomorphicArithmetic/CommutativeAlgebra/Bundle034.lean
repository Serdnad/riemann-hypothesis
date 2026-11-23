module

import Development.AutomorphicArithmetic.WhittakerHecke.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle560
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle731
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle023
public import Development.EtaleCohomology.EtaleSheaves.Bundle077
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
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
import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.simplices_pullback_existsUnique_of_map_eq :
    ∀ {A B C : Spc} (r : A ⟶ C) (u : B ⟶ C) (k : ℕ) (T : Scheme.{0}) (x : Sx A k T) (y : Sx B k T), x.map r = y.map u →
        ∃! z : Sx (pullback r u) k T, z.map (pullback.fst r u) = x ∧ z.map (pullback.snd r u) = y := by
  apply UpperTheory.existsUnique_simplex_pullback_of_map_eq <;> assumption
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Deg2

abbrev T (q : ℕ) : Shv ℤ := (restr (Int.castRingHom (ZMod q))).obj (tw q 1)

def kap (q : ℕ) [NeZero q] : T q ⟶ Gm := (GlobalTheory.T.kummer_sequence_etale_tateTwist q).choose

theorem kap_spec (q : ℕ) [NeZero q] : Mono (kap q) ∧ kap q ≫ ((q : ℤ) • 𝟙 Gm) = 0 ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map (kap q) (show Sec (T q) U from twGen 1 ζ) = unitSec u) ∧ (∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Sec.map ((q : ℤ) • 𝟙 Gm) b = 0 → ∃ a, Sec.map (kap q) a = b) ∧ ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ b : Sec Gm U, Loc U fun V g => ∃ c : Sec Gm V, Sec.map ((q : ℤ) • 𝟙 Gm) c = Sec.res g b :=
  (GlobalTheory.T.kummer_sequence_etale_tateTwist q).choose_spec

section MV
variable (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A)

end MV

section Shrink
variable (R : Type) [CommRing R] (B A' : Type) [CommRing B] [CommRing A'] [Algebra B A'] (f s : B)

end Shrink

end UpperTheory.Deg2
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish :
    ∀ (Q : Scheme.{0} → Prop) (G : Shv ℤ), (∀ U : Scheme.{0}, Q U → Subsingleton (Sec G U)) → ∀ P : PSh, Supp Q P → ∀ n : ℤ, Subsingleton (HK ℤ (sgl ((free ℤ).obj P)) G n) := by
  intro Q G hG P hP n
  apply UpperTheory.subsingleton_hypercohomology_free_of_subsingleton_cohomology
  haveI : (res ℤ G).IsKInjective := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ G).1
  refine GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support ℤ (disc.obj P) (res ℤ G) ?_ n
  intro U hU m b hb
  have hQ : Q U := hP U hU
  haveI : Subsingleton (Sec G U) := hG U hQ
  obtain ⟨h0, -, h3, hneg⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ G U
  have hz : ∀ (c : Sec ((res ℤ G).X m) U), b = c → c = 0 →
      Loc U fun V g => ∃ a : Sec ((res ℤ G).X (m - 1)) V,
        Sec.map ((res ℤ G).d (m - 1) m) a = Sec.res g b := by
    rintro c rfl rfl
    refine ⟨⊤, (Scheme.etaleTopology.{0}).top_mem U, fun V g _ => ⟨0, ?_⟩⟩
    simp
  rcases lt_trichotomy m 0 with h | h | h
  · haveI := hneg m h
    exact hz b rfl (Subsingleton.elim _ _)
  · subst h
    obtain ⟨a, rfl⟩ := (h0 b).1 hb
    refine hz _ rfl ?_
    rw [Subsingleton.elim a 0]
    simp
  · exact h3 (m - 1) m (m + 1) h (by omega) b rfl hb
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

private lemma sec_comp {A B C : Shv ℤ} (p : A ⟶ B) (q : B ⟶ C) {V : Scheme.{0}} (x : Sec A V) :
    Sec.map (p ≫ q) x = Sec.map q (Sec.map p x) := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma exists_lift {M F : Shv ℤ} (g : M ⟶ (res ℤ F).X 0) (hg : g ≫ (res ℤ F).d 0 1 = 0) :
    ∃ f : M ⟶ F, f ≫ resι ℤ F = g := by
  classical
  have hinj : ∀ U : Scheme, Function.Injective (Sec.map (resι ℤ F) (U := U)) :=
    fun U => (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ F U).2.1
  have hex : ∀ (U : Scheme) (x : Sec M U), ∃ a : Sec F U, Sec.map (resι ℤ F) a = Sec.map g x := by
    intro U x
    refine ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness ℤ F U).1 _).1 ?_
    rw [← sec_comp, hg]
    rfl
  let φ : ∀ U : Scheme, Sec M U → Sec F U := fun U x => (hex U x).choose
  have hφ : ∀ U x, Sec.map (resι ℤ F) (φ U x) = Sec.map g x := fun U x => (hex U x).choose_spec
  let η : M.obj ⟶ F.obj :=
    { app := fun U => ModuleCat.ofHom
        { toFun := φ U.unop
          map_add' := fun x y => hinj _ (by
            rw [hφ]
            show (ModuleCat.Hom.hom _) (x + y) = (ModuleCat.Hom.hom _) (φ _ x + φ _ y)
            rw [map_add (f := _), map_add (f := _)]
            exact congrArg₂ (· + ·) (hφ _ x).symm (hφ _ y).symm)
          map_smul' := fun r x => hinj _ (by
            rw [hφ, RingHom.id_apply]
            have e1 := (ModuleCat.Hom.hom (g.hom.app U)).map_smul r x
            have e2 := (ModuleCat.Hom.hom ((resι ℤ F).hom.app U)).map_smul r (φ _ x)
            exact e1.trans ((congrArg _ (hφ _ x).symm).trans e2.symm)) }
      naturality := by
        intro U V h
        ext x
        apply hinj
        have n1 := congrArg (fun k => ModuleCat.Hom.hom k x) (g.hom.naturality h)
        have n2 := congrArg (fun k => ModuleCat.Hom.hom k (φ _ x)) ((resι ℤ F).hom.naturality h)
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at n1 n2
        show Sec.map (resι ℤ F) (φ _ ((ModuleCat.Hom.hom (M.obj.map h)) x)) =
          Sec.map (resι ℤ F) ((ModuleCat.Hom.hom (F.obj.map h)) (φ _ x))
        rw [hφ]
        refine n1.trans ?_
        refine Eq.trans ?_ n2.symm
        exact congrArg _ (hφ _ x).symm }
  refine ⟨⟨η⟩, (GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections ℤ (⟨η⟩ ≫ resι ℤ F)).2.2.2 g (fun U a => ?_)⟩
  rw [sec_comp]
  exact hφ U a

set_option backward.isDefEq.respectTransparency false in
private lemma sgl_f {M F : Shv ℤ} (f : M ⟶ F) :
    sglι M ≫ ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F).f 0 = f ≫ resι ℤ F := by
  rw [HomologicalComplex.comp_f, ← Category.assoc]
  have h : sglι M ≫ ((CochainComplex.singleFunctor (Shv ℤ) 0).map f).f 0 = f ≫ sglι F := by
    simp [sglι, CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self]
  rw [h, Category.assoc, (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.2.2.1]

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.bijective_cl_hypercohomology_singleton_zero :
    ∀ (M F : Shv ℤ), Function.Bijective (cl : (M ⟶ F) → HK ℤ (sgl M) F 0) := by
  intro M F
  have hz : ∀ p : ℤ, p ≠ 0 → IsZero ((sgl M).X p) := fun p hp =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hp
  have hL : IsZero ((res ℤ F).X (-1)) := by
    haveI := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.1
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 (-1) (by norm_num)
  have hβ0 : ∀ β : Cochain (sgl M) (res ℤ F) (-1), β = 0 := by
    intro β
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = -1 := by omega
      exact hL.eq_of_tgt _ _
    · exact (hz p hp).eq_of_src _ _
  have hcob : ∀ x : Cocycle (sgl M) (res ℤ F) 0, x ∈ coboundaries (sgl M) (res ℤ F) 0 → x = 0 := by
    intro x hx
    obtain ⟨β, hβ⟩ := (mem_coboundaries_iff x (-1) (by norm_num)).1 hx
    apply Cocycle.ext
    rw [← hβ, hβ0 β, δ_zero]
    rfl
  have hmono : Mono (resι ℤ F) := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).2.2.2.2.2.1
  have hsg : IsIso (sglι M) := by
    dsimp [sglι]
    infer_instance
  constructor
  · intro f f' h
    have h1 : Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f ≫ resAug F)
        = Cocycle.ofHom ((CochainComplex.singleFunctor (Shv ℤ) 0).map f' ≫ resAug F) := by
      have := hcob _ ((CohomologyClass.mk_eq_zero_iff _).1
        (by rw [CohomologyClass.mk_sub]; exact sub_eq_zero.2 h))
      exact sub_eq_zero.1 this
    have h2 := congrArg (fun x : Cocycle (sgl M) (res ℤ F) 0 =>
      (x : Cochain (sgl M) (res ℤ F) 0).v 0 0 (add_zero 0)) h1
    simp only [Cocycle.ofHom_coe, Cochain.ofHom_v] at h2
    apply (cancel_mono (resι ℤ F)).1
    rw [← sgl_f, ← sgl_f, h2]
  · intro c
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective c
    have hz1 : (z : Cochain (sgl M) (res ℤ F) 0).v 0 0 (add_zero 0) ≫ (res ℤ F).d 0 1 = 0 := by
      have e := congrArg (fun w : Cochain (sgl M) (res ℤ F) 1 => w.v 0 1 (zero_add 1))
        ((Cocycle.mem_iff 0 1 (zero_add 1) _).1 z.2)
      simp only [δ_zero_cochain_v, Cochain.zero_v] at e
      rwa [(hz 1 one_ne_zero).eq_of_tgt ((sgl M).d 0 1) 0, zero_comp, sub_zero] at e
    obtain ⟨f, hf⟩ := exists_lift (sglι M ≫ (z : Cochain (sgl M) (res ℤ F) 0).v 0 0 (add_zero 0))
      (by rw [Category.assoc, hz1, comp_zero])
    refine ⟨f, ?_⟩
    show CohomologyClass.mk _ = CohomologyClass.mk z
    congr 1
    apply Cocycle.ext
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [add_zero] at hpq
    subst hpq
    by_cases hp : p = 0
    · subst hp
      rw [Cocycle.ofHom_coe, Cochain.ofHom_v, ← cancel_epi (sglι M), sgl_f, hf]
    · exact (hz p hp).eq_of_src _ _
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafVanBPf LateralTheory.E.LeafVanBStalkPf

namespace UpperTheory.PushoutColimitSpec

private theorem epi_of_closed {R S : CommRingCat.{0}} (q : R ⟶ S) [IsClosedImmersion (Spec.map q)] : Epi q :=
  ⟨fun a b h => Spec.map_injective ((cancel_mono (Spec.map q)).1 (by
    rw [← Spec.map_comp, ← Spec.map_comp, h]))⟩

private theorem isPushout_of_Spec {A B C P : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (inl : B ⟶ P) (inr : C ⟶ P)
    (h : IsPullback (Spec.map inl) (Spec.map inr) (Spec.map f) (Spec.map g)) : IsPushout f g inl inr := by
  have hw : f ≫ inl = g ≫ inr := Spec.map_injective (by simpa using h.w)
  have h' : IsPullback inl.op inr.op f.op g.op :=
    IsPullback.of_map Scheme.Spec (by rw [← op_comp, ← op_comp, hw]) h
  exact h'.unop.flip

private def colimOfPushout {J : Type} [SmallCategory J] {D D' : J ⥤ CommRingCat.{0}} {c : Cocone D} (hc : IsColimit c)
    (c' : Cocone D') (q : ∀ j, D.obj j ⟶ D'.obj j)
    (hq : ∀ {j j' : J} (g : j ⟶ j'), D.map g ≫ q j' = q j ≫ D'.map g) (hepi : ∀ j, Epi (q j))
    (qi : c.pt ⟶ c'.pt) (hqi : ∀ j, c.ι.app j ≫ qi = q j ≫ c'.ι.app j) (j0 : J)
    (hp : IsPushout (c.ι.app j0) (q j0) qi (c'.ι.app j0)) : IsColimit c' :=
  let f (s : Cocone D') : c.pt ⟶ s.pt := hc.desc
    ⟨s.pt, { app := fun j => q j ≫ s.ι.app j
             naturality := fun j j' g => by
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
               rw [← Category.assoc, hq, Category.assoc, s.w] }⟩
  have hf (s : Cocone D') (j : J) : c.ι.app j ≫ f s = q j ≫ s.ι.app j := hc.fac _ j
  { desc := fun s => hp.desc (f s) (s.ι.app j0) (hf s j0)
    fac := fun s j => by
      have := hepi j
      rw [← cancel_epi (q j), ← Category.assoc, ← hqi, Category.assoc, hp.inl_desc, hf]
    uniq := fun s m hm => by
      apply hp.hom_ext
      · rw [hp.inl_desc]
        apply hc.hom_ext
        intro j
        rw [← Category.assoc, hqi, Category.assoc, hm, hf]
      · rw [hp.inr_desc, hm] }

private theorem ring_system {J : Type} [SmallCategory J] (Z : J → Scheme.{0}) [∀ j, IsAffine (Z j)]
    (r : ∀ {j j' : J} (_ : j ⟶ j'), Z j' ⟶ Z j) (hid : ∀ j, r (𝟙 j) = 𝟙 _)
    (hcomp : ∀ {j j' j'' : J} (g : j ⟶ j') (g' : j' ⟶ j''), r (g ≫ g') = r g' ≫ r g) :
    ∃ (D' : J ⥤ CommRingCat.{0}) (ez : ∀ j, Z j ≅ Spec (D'.obj j)),
      ∀ {j j' : J} (g : j ⟶ j'), (ez j').inv ≫ r g ≫ (ez j).hom = Spec.map (D'.map g) := by
  refine ⟨{ obj := fun j => Γ(Z j, ⊤)
            map := fun {j j'} g => Spec.preimage ((Z j').isoSpec.inv ≫ r g ≫ (Z j).isoSpec.hom)
            map_id := fun j => Spec.map_injective (by simp [hid])
            map_comp := fun {j j' j''} g g' => Spec.map_injective (by simp [hcomp]) },
    fun j => (Z j).isoSpec, fun {j j'} g => ?_⟩
  simp

private theorem cocone_system {J : Type} [SmallCategory J] [Nonempty J] (Z : J → Scheme.{0})
    (r : ∀ {j j' : J} (_ : j ⟶ j'), Z j' ⟶ Z j) (D D' : J ⥤ CommRingCat.{0})
    (ez : ∀ j, Z j ≅ Spec (D'.obj j))
    (hr : ∀ {j j' : J} (g : j ⟶ j'), (ez j').inv ≫ r g ≫ (ez j).hom = Spec.map (D'.map g))
    (c : Cocone D) (hc : IsColimit c) (φ : ∀ j, Z j ⟶ Spec (D.obj j)) [∀ j, IsClosedImmersion (φ j)]
    (hφ : ∀ {j j' : J} (g : j ⟶ j'), r g ≫ φ j = φ j' ≫ Spec.map (D.map g))
    (Zi : Scheme.{0}) [IsAffine Zi] (φi : Zi ⟶ Spec c.pt) (l : ∀ j, Zi ⟶ Z j)
    (hl : ∀ {j j' : J} (g : j ⟶ j'), l j' ≫ r g = l j)
    (hlφ : ∀ j, l j ≫ φ j = φi ≫ Spec.map (c.ι.app j))
    (hpb : ∀ j, IsPullback (l j) φi (φ j) (Spec.map (c.ι.app j))) :
    ∃ (c' : Cocone D') (_ : IsColimit c') (ei : Zi ≅ Spec c'.pt),
      ∀ j, ei.inv ≫ l j ≫ (ez j).hom = Spec.map (c'.ι.app j) := by
  let q : ∀ j, D.obj j ⟶ D'.obj j := fun j => Spec.preimage ((ez j).inv ≫ φ j)
  have hqs : ∀ j, Spec.map (q j) = (ez j).inv ≫ φ j := fun j => Spec.map_preimage _
  let c' : Cocone D' :=
    { pt := Γ(Zi, ⊤)
      ι := { app := fun j => Spec.preimage (Zi.isoSpec.inv ≫ l j ≫ (ez j).hom)
             naturality := fun j j' g => Spec.map_injective (by
               simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, Spec.map_comp,
                 Spec.map_preimage, ← hr g, Category.assoc, Iso.hom_inv_id_assoc]
               rw [← Category.assoc (l j'), hl g, ← Category.assoc]) } }
  have hcs : ∀ j, Spec.map (c'.ι.app j) = Zi.isoSpec.inv ≫ l j ≫ (ez j).hom := fun j => Spec.map_preimage _
  let qi : c.pt ⟶ c'.pt := Spec.preimage (Zi.isoSpec.inv ≫ φi)
  have hqis : Spec.map qi = Zi.isoSpec.inv ≫ φi := Spec.map_preimage _
  have hepi : ∀ j, Epi (q j) := fun j => by
    have : IsClosedImmersion (Spec.map (q j)) := by rw [hqs]; infer_instance
    exact epi_of_closed _
  have hq : ∀ {j j' : J} (g : j ⟶ j'), D.map g ≫ q j' = q j ≫ D'.map g := fun {j j'} g =>
    Spec.map_injective (by
      simp only [Spec.map_comp, hqs, ← hr g, Category.assoc, Iso.hom_inv_id_assoc, hφ g])
  have hqi : ∀ j, c.ι.app j ≫ qi = q j ≫ c'.ι.app j := fun j => Spec.map_injective (by
    simp only [Spec.map_comp, hqs, hcs, hqis, Category.assoc, Iso.hom_inv_id_assoc, hlφ])
  obtain ⟨j0⟩ := ‹Nonempty J›
  have hp : IsPushout (c.ι.app j0) (q j0) qi (c'.ι.app j0) := by
    apply isPushout_of_Spec
    refine IsPullback.of_iso (hpb j0).flip Zi.isoSpec (Iso.refl _) (ez j0) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hqis]
    · simp [hcs]
    · simp
    · simp [hqs]
  exact ⟨c', colimOfPushout hc c' q hq hepi qi hqi j0 hp, Zi.isoSpec, fun j => (hcs j).symm⟩

end UpperTheory.PushoutColimitSpec

open UpperTheory.PushoutColimitSpec in
theorem UpperTheory.exists_closedFiber_colimit_presentation :
    ∀ {B W : Scheme.{0}} (ι : W ⟶ B) [IsClosedImmersion ι] (U : B.Etale) (x : U.left) (S : SHSys U x)
        (zl : ∀ j, pullback (S.t ≫ U.hom) ι ⟶ pullback (S.V j).hom ι),
        (∀ j, zl j ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Spec.map (S.c.ι.app j) ≫ (S.e j).inv) →
        (∀ j, zl j ≫ pullback.snd _ _ = pullback.snd _ _) →
        ∃ (D' : S.J ⥤ CommRingCat.{0}) (c' : Cocone D') (_ : IsColimit c')
          (ez : ∀ j, pullback (S.V j).hom ι ≅ Spec (D'.obj j)) (ei : pullback (S.t ≫ U.hom) ι ≅ Spec c'.pt),
          (∀ {j j' : S.J} (g : j ⟶ j'), (ez j').inv ≫ resBW ι (S.tr g) ≫ (ez j).hom = Spec.map (D'.map g)) ∧
          (∀ j, ei.inv ≫ zl j ≫ (ez j).hom = Spec.map (c'.ι.app j)) := by
  intro B W ι _ U x S zl h1 h2
  have rfst : ∀ {j j' : S.J} (g : j ⟶ j'),
      resBW ι (S.tr g) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (S.tr g).left := fun g => pullback.lift_fst _ _ _
  have rsnd : ∀ {j j' : S.J} (g : j ⟶ j'),
      resBW ι (S.tr g) ≫ pullback.snd _ _ = pullback.snd _ _ := fun g =>
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have htr : ∀ {j j' : S.J} (g : j ⟶ j'),
      (S.tr g).left = (S.e j').hom ≫ Spec.map (S.D.map g) ≫ (S.e j).inv := fun g => by
    rw [← S.tr_spec g]; simp
  have hid : ∀ j, resBW ι (S.tr (𝟙 j)) = 𝟙 _ := fun j => by
    apply pullback.hom_ext
    · rw [rfst, htr]; simp
    · rw [rsnd]; simp
  have hcomp : ∀ {j j' j'' : S.J} (g : j ⟶ j') (g' : j' ⟶ j''),
      resBW ι (S.tr (g ≫ g')) = resBW ι (S.tr g') ≫ resBW ι (S.tr g) := fun g g' => by
    apply pullback.hom_ext
    · rw [Category.assoc, rfst, rfst, reassoc_of% (rfst g'), htr, htr, htr]; simp
    · rw [Category.assoc, rsnd, rsnd, rsnd]
  have hVa : ∀ j, IsAffine (S.V j).left := fun j => .of_isIso (S.e j).hom
  let φ : ∀ j, pullback (S.V j).hom ι ⟶ Spec (S.D.obj j) := fun j => pullback.fst _ _ ≫ (S.e j).hom
  have hφc : ∀ j, IsClosedImmersion (φ j) := fun j => inferInstance
  have hZa : ∀ j, IsAffine (pullback (S.V j).hom ι) := fun j => by
    have h := (IsClosedImmersion.isAffine_surjective_of_isAffine (φ j)).1
    exact h
  have hZi : IsAffine (pullback (S.t ≫ U.hom) ι) :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (pullback.fst (S.t ≫ U.hom) ι)).1
  obtain ⟨D', ez, hr⟩ := ring_system (fun j => pullback (S.V j).hom ι) (fun g => resBW ι (S.tr g)) hid hcomp
  have hφ : ∀ {j j' : S.J} (g : j ⟶ j'),
      resBW ι (S.tr g) ≫ φ j = φ j' ≫ Spec.map (S.D.map g) := fun {j j'} g => by
    simp only [φ]
    rw [reassoc_of% (rfst g), htr]; simp
  have hl : ∀ {j j' : S.J} (g : j ⟶ j'), zl j' ≫ resBW ι (S.tr g) = zl j := fun {j j'} g => by
    apply pullback.hom_ext
    · rw [Category.assoc, rfst, reassoc_of% (h1 j'), h1, htr]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Spec.map_comp_assoc, S.c.w]
    · rw [Category.assoc, rsnd, h2, h2]
  have hlφ : ∀ j, zl j ≫ φ j = pullback.fst _ _ ≫ Spec.map (S.c.ι.app j) := fun j => by
    simp only [φ]
    rw [reassoc_of% (h1 j)]; simp
  have hpb : ∀ j, IsPullback (zl j) (pullback.fst (S.t ≫ U.hom) ι) (φ j) (Spec.map (S.c.ι.app j)) := fun j => by
    have hw : (S.a j).left ≫ U.hom = (S.V j).hom := by simpa using (S.a j).w
    have hb : (Spec.map (S.c.ι.app j) ≫ (S.e j).inv) ≫ (S.V j).hom = S.t ≫ U.hom := by
      rw [S.ht j, ← hw]; simp
    have big : IsPullback (zl j ≫ pullback.snd _ _) (pullback.fst (S.t ≫ U.hom) ι) ι
        ((Spec.map (S.c.ι.app j) ≫ (S.e j).inv) ≫ (S.V j).hom) := by
      rw [h2, hb]; exact (IsPullback.of_hasPullback _ _).flip
    have sq := IsPullback.of_right big (h1 j) (IsPullback.of_hasPullback (S.V j).hom ι).flip
    exact IsPullback.of_iso sq (Iso.refl _) (Iso.refl _) (Iso.refl _) (S.e j) (by simp) (by simp) (by simp [φ]) (by simp)
  have : Nonempty S.J := IsFiltered.nonempty
  obtain ⟨c', hc', ei, he⟩ := cocone_system (fun j => pullback (S.V j).hom ι) (fun g => resBW ι (S.tr g)) S.D D' ez hr
    S.c S.hc φ hφ (pullback (S.t ≫ U.hom) ι) (pullback.fst _ _) zl hl hlφ hpb
  exact ⟨D', c', hc', ez, ei, hr, he⟩
end
end
