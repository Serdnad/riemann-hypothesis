module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StrictlyHenselianIsColimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle479
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle575
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1076
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
import Mathlib.Data.Finset.Functor
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section
namespace GlobalTheory.EtC.GmStep.KillColim

theorem laurentMap_coeff_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (p : LaurentPolynomial A) (m : ℤ) : (laurentMap f p).coeff m = f (p.coeff m) := by
  rw [laurentMap_coeff, Finsupp.mapRange_apply]

theorem laurentMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (laurentMap g).comp (laurentMap f) = laurentMap (g.comp f) := by
  refine RingHom.ext fun p => ?_
  · apply AddMonoidAlgebra.coeff_injective
    ext m
    simp [laurentMap_coeff_apply]

theorem laurentMap_id (A : Type) [CommRing A] : laurentMap (RingHom.id A) = RingHom.id _ := by
  refine RingHom.ext fun p => ?_
  · apply AddMonoidAlgebra.coeff_injective
    ext m
    simp [laurentMap_coeff_apply]

theorem laurentMap_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : Function.Injective (laurentMap f) := by
  intro p r h
  apply AddMonoidAlgebra.coeff_injective
  ext m
  apply hf
  rw [← laurentMap_coeff_apply, ← laurentMap_coeff_apply, h]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Functor.map_comp, ← Spec.map_comp]; rfl

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]

def diag : Finset S ⥤ CommRingCat.{0} where
  obj t := CommRingCat.of (LaurentPolynomial (Algebra.adjoin A (t : Set S)))
  map {t u} h := CommRingCat.ofHom
    (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.2 h.le))).toRingHom)
  map_id t := by
    ext1
    refine (Eq.trans ?_ (laurentMap_id _)).trans rfl
    congr 1
  map_comp f g := by
    ext1
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    rw [laurentMap_comp]
    rfl

def cocone : Cocone (diag A S) where
  pt := CommRingCat.of (LaurentPolynomial S)
  ι := { app := fun t => CommRingCat.ofHom (laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom)
         naturality := fun t u h => by
           ext1
           simp only [diag, Functor.const_obj_map, Category.comp_id, CommRingCat.hom_comp,
             CommRingCat.hom_ofHom]
           rw [laurentMap_comp]
           rfl }

theorem val_CT (t : Finset S) (a : Algebra.adjoin A (t : Set S)) (n : ℤ) :
    laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom (LaurentPolynomial.C a * LaurentPolynomial.T n) =
      LaurentPolynomial.C (a : S) * LaurentPolynomial.T n := by
  rw [map_mul, laurentMap_C, laurentMap_T]
  rfl

theorem lm_val_incl {t u : Finset S} (h : (t : Set S) ⊆ u) (p : LaurentPolynomial (Algebra.adjoin A (t : Set S))) :
    laurentMap (Algebra.adjoin A (u : Set S)).val.toRingHom
        (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom p) =
      laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom p := by
  apply AddMonoidAlgebra.coeff_injective
  ext m
  simp only [laurentMap_coeff_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_val,
    Subalgebra.coe_inclusion]

theorem exists_finset_adjoin_laurent_preimage (x : LaurentPolynomial S) : ∃ (t : Finset S) (y : LaurentPolynomial (Algebra.adjoin A (t : Set S))),
    x = laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom y := by
  classical
  induction x using LaurentPolynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨t, y, rfl⟩ := hp
    obtain ⟨t', y', rfl⟩ := hr
    have h1 : (t : Set S) ⊆ ((t ⊔ t' : Finset S) : Set S) := Finset.coe_subset.2 le_sup_left
    have h2 : (t' : Set S) ⊆ ((t ⊔ t' : Finset S) : Set S) := Finset.coe_subset.2 le_sup_right
    refine ⟨t ⊔ t', laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono h1)).toRingHom y +
      laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono h2)).toRingHom y', ?_⟩
    rw [map_add (f := _), lm_val_incl A S h1, lm_val_incl A S h2]
  | C_mul_T n a =>
    have hmem : a ∈ Algebra.adjoin A (({a} : Finset S) : Set S) :=
      Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self a))
    refine ⟨{a}, LaurentPolynomial.C (⟨a, hmem⟩ : Algebra.adjoin A (({a} : Finset S) : Set S)) *
      LaurentPolynomial.T n, ?_⟩
    rw [val_CT]

theorem laurent_adjoin_eq_of_image_eq [DecidableEq S] {i j : Finset S} (xi : LaurentPolynomial (Algebra.adjoin A (i : Set S)))
    (xj : LaurentPolynomial (Algebra.adjoin A (j : Set S)))
    (h : laurentMap (Algebra.adjoin A (i : Set S)).val.toRingHom xi =
      laurentMap (Algebra.adjoin A (j : Set S)).val.toRingHom xj) :
    laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono
        (Finset.coe_subset.2 (le_sup_left : i ≤ i ⊔ j)))).toRingHom xi =
      laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono
        (Finset.coe_subset.2 (le_sup_right : j ≤ i ⊔ j)))).toRingHom xj := by
  refine laurentMap_injective (Algebra.adjoin A ((i ⊔ j : Finset S) : Set S)).val.toRingHom
    Subtype.val_injective ?_
  exact (lm_val_incl A S (Finset.coe_subset.2 (le_sup_left : i ≤ i ⊔ j)) xi).trans
    (h.trans (lm_val_incl A S (Finset.coe_subset.2 (le_sup_right : j ≤ i ⊔ j)) xj).symm)

def coconeIsColimit : IsColimit (cocone A S) := by
  classical
  haveI : ReflectsColimitsOfShape (Finset S) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (cocone A S)) ?_ ?_)
  · intro x
    exact exists_finset_adjoin_laurent_preimage A S x
  · intro i j xi xj h
    exact ⟨i ⊔ j, homOfLE le_sup_left, homOfLE le_sup_right, laurent_adjoin_eq_of_image_eq A S xi xj h⟩

end GlobalTheory.EtC.GmStep.KillColim
end

namespace GlobalTheory.EtC.GmStep.KillColim

theorem val_laurent (A S : Type) [CommRing A] [CommRing S] [Algebra A S] (t : Finset S) :
    (laurentMap (Algebra.adjoin A (t : Set S)).val.toRingHom).comp
        (laurentMap (algebraMap A (Algebra.adjoin A (t : Set S)))) = laurentMap (algebraMap A S) := by
  rw [laurentMap_comp]
  congr 1

theorem incl_laurent (A S : Type) [CommRing A] [CommRing S] [Algebra A S] {t u : Finset S}
    (h : (t : Set S) ⊆ u) :
    (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono (R := A) h)).toRingHom).comp
        (laurentMap (algebraMap A (Algebra.adjoin A (t : Set S)))) =
      laurentMap (algebraMap A (Algebra.adjoin A (u : Set S))) := by
  rw [laurentMap_comp]
  congr 1

theorem kill_colim : ∀ (q : ℕ) (A S : Type) [CommRing A] [CommRing S] [Algebra A S], IsUnit (q : A) →
    ∀ (n i : ℤ) (x : Ht q (sp (LaurentPolynomial A)) n i),
    pull _ (spMap (laurentMap (algebraMap A S))) _ _ x = 0 →
    ∃ t : Finset S, pull _ (spMap (laurentMap (algebraMap A (Algebra.adjoin A (t : Set S))))) _ _ x = 0 := by
  intro q A S _ _ _ hq n i x hx
  classical
  have hu : IsUnit (q : (diag A S).obj ∅) := by
    have := hq.map ((LaurentPolynomial.C : Algebra.adjoin A ((∅ : Finset S) : Set S) →+* _).comp
      (algebraMap A _))
    rw [map_natCast] at this
    exact this
  have e1 : spMap ((cocone A S).ι.app ∅).hom ≫
      spMap (laurentMap (algebraMap A (Algebra.adjoin A ((∅ : Finset S) : Set S)))) =
      spMap (laurentMap (algebraMap A S)) :=
    (spMap_comp' _ (laurentMap (Algebra.adjoin A ((∅ : Finset S) : Set S)).val.toRingHom)).trans
      (congrArg spMap (val_laurent A S ∅))
  have hy0 : pull _ (spMap ((cocone A S).ι.app ∅).hom) _ _
      (pull _ (spMap (laurentMap (algebraMap A (Algebra.adjoin A ((∅ : Finset S) : Set S))))) _ _ x) = 0 :=
    (pull_comp _ _ _ _ _ x).symm.trans ((congrArg (fun g => pull _ g (tw q i) n x) e1).trans hx)
  obtain ⟨k, f, hk⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (diag A S) (cocone A S) (coconeIsColimit A S) n i).2 ∅ _ hu hy0
  have e2 : spMap ((diag A S).map f).hom ≫
      spMap (laurentMap (algebraMap A (Algebra.adjoin A ((∅ : Finset S) : Set S)))) =
      spMap (laurentMap (algebraMap A (Algebra.adjoin A (k : Set S)))) :=
    (spMap_comp' _ (laurentMap (Subalgebra.inclusion (Algebra.adjoin_mono (R := A)
      (Finset.coe_subset.2 f.le))).toRingHom)).trans
      (congrArg spMap (incl_laurent A S (Finset.coe_subset.2 f.le)))
  exact ⟨k, (congrArg (fun g => pull _ g (tw q i) n x) e2).symm.trans ((pull_comp _ _ _ _ _ x).trans hk)⟩

end GlobalTheory.EtC.GmStep.KillColim
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC.GmPhiNoeth

theorem coeff_laurentMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : LaurentPolynomial R) (n : ℤ) :
    (laurentMap f p).coeff n = f (p.coeff n) := by
  simp [laurentMap]

theorem laurentMap_id (R : Type) [CommRing R] : laurentMap (RingHom.id R) = RingHom.id _ :=
  RingHom.ext fun p => AddMonoidAlgebra.ext (Finsupp.ext fun n => by rw [coeff_laurentMap]; rfl)

def laurentFunctor : CommRingCat.{0} ⥤ CommRingCat.{0} where
  obj R := CommRingCat.of (LaurentPolynomial R)
  map f := CommRingCat.ofHom (laurentMap f.hom)
  map_id R := by
    change CommRingCat.ofHom (laurentMap (RingHom.id R)) = _
    rw [laurentMap_id]; rfl
  map_comp f g := by
    change CommRingCat.ofHom (laurentMap (g.hom.comp f.hom)) = _
    rw [GmPhiNat.laurentMap_comp]; rfl

def isColimit_laurent {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}
    (hc : IsColimit c) : IsColimit (laurentFunctor.mapCocone c) := by
  haveI : ReflectsColimitsOfShape J (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have hc' : IsColimit ((forget CommRingCat.{0}).mapCocone c) := isColimitOfPreserves _ hc

  have hsurj : ∀ a : c.pt, ∃ j, ∃ b : D.obj j, (c.ι.app j).hom b = a := fun a =>
    Types.jointly_surjective_of_isColimit hc' a

  have hker : ∀ j (b : D.obj j), (c.ι.app j).hom b = 0 → ∃ k, ∃ f : j ⟶ k, (D.map f).hom b = 0 := by
    intro j b hb
    have h := (Types.FilteredColimit.isColimit_eq_iff' hc' b 0).1 (by
      change (c.ι.app j).hom b = (c.ι.app j).hom 0
      rw [hb, map_zero])
    obtain ⟨k, f, hf⟩ := h
    refine ⟨k, f, ?_⟩
    change (D.map f).hom b = (D.map f).hom 0 at hf
    rw [hf, map_zero]
  have hw : ∀ {j k : J} (f : j ⟶ k) (y : LaurentPolynomial (D.obj j)),
      laurentMap (c.ι.app k).hom (laurentMap (D.map f).hom y) = laurentMap (c.ι.app j).hom y := by
    intro j k f y
    rw [← RingHom.comp_apply, ← GmPhiNat.laurentMap_comp, ← CommRingCat.hom_comp, c.w f]
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (laurentFunctor.mapCocone c)) ?_ ?_)
  · intro (x : LaurentPolynomial c.pt)
    suffices h : ∃ j, ∃ y : LaurentPolynomial (D.obj j), laurentMap (c.ι.app j).hom y = x by
      obtain ⟨j, y, hy⟩ := h
      exact ⟨j, y, hy.symm⟩
    induction x using LaurentPolynomial.induction_on' with
    | add p p' hp hp' =>
      obtain ⟨j, y, rfl⟩ := hp
      obtain ⟨j', y', rfl⟩ := hp'
      refine ⟨IsFiltered.max j j', laurentMap (D.map (IsFiltered.leftToMax j j')).hom y +
        laurentMap (D.map (IsFiltered.rightToMax j j')).hom y', ?_⟩
      rw [map_add (f := _), hw, hw]
    | C_mul_T n a =>
      obtain ⟨j, b, rfl⟩ := hsurj a
      refine ⟨j, LaurentPolynomial.C b * LaurentPolynomial.T n, ?_⟩
      rw [map_mul, GmPhiNat.laurentMap_T, ← RingHom.comp_apply, GmPhiNat.laurentMap_C, RingHom.comp_apply]
  · intro i j (xi : LaurentPolynomial (D.obj i)) (xj : LaurentPolynomial (D.obj j)) h
    change laurentMap (c.ι.app i).hom xi = laurentMap (c.ι.app j).hom xj at h
    let m := IsFiltered.max i j
    let fi := IsFiltered.leftToMax i j
    let fj := IsFiltered.rightToMax i j
    let z : LaurentPolynomial (D.obj m) := laurentMap (D.map fi).hom xi - laurentMap (D.map fj).hom xj
    have hz : laurentMap (c.ι.app m).hom z = 0 := by
      simp only [z, map_sub, hw, h, sub_self]

    have hfin : ∀ s : Finset ℤ, ∃ k, ∃ h : m ⟶ k, ∀ n ∈ s, (D.map h).hom (z.coeff n) = 0 := by
      intro s
      classical
      induction s using Finset.induction_on with
      | empty => exact ⟨m, 𝟙 m, fun n hn => absurd hn (Finset.notMem_empty n)⟩
      | insert n s _ ih =>
        obtain ⟨k₁, h₁, hk₁⟩ := ih
        have hn : (c.ι.app m).hom (z.coeff n) = 0 := by
          rw [← coeff_laurentMap, hz]; rfl
        obtain ⟨k₂, h₂, hk₂⟩ := hker m _ hn
        obtain ⟨k, g₁, g₂, hg⟩ := IsFiltered.span h₁ h₂
        refine ⟨k, h₁ ≫ g₁, fun n' hn' => ?_⟩
        rcases Finset.mem_insert.1 hn' with rfl | hn'
        · rw [hg, D.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, hk₂, map_zero]
        · rw [D.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, hk₁ n' hn', map_zero]
    obtain ⟨k, hmk, hk⟩ := hfin z.coeff.support
    have hz0 : laurentMap (D.map hmk).hom z = 0 := by
      refine AddMonoidAlgebra.ext (Finsupp.ext fun n => ?_)
      rw [coeff_laurentMap]
      by_cases hn : n ∈ z.coeff.support
      · exact hk n hn
      · rw [Finsupp.notMem_support_iff.1 hn, map_zero]; rfl
    refine ⟨k, fi ≫ hmk, fj ≫ hmk, ?_⟩
    change laurentMap (D.map (fi ≫ hmk)).hom xi = laurentMap (D.map (fj ≫ hmk)).hom xj
    rw [D.map_comp, D.map_comp, CommRingCat.hom_comp, CommRingCat.hom_comp, GmPhiNat.laurentMap_comp,
      GmPhiNat.laurentMap_comp, RingHom.comp_apply, RingHom.comp_apply, ← sub_eq_zero, ← map_sub]
    exact hz0

end GlobalTheory.EtC.GmPhiNoeth


open GlobalTheory.EtC.GmPhiNoeth in
theorem GlobalTheory.EtC.gmPhi_surjective_of_noetherian : ∀ (q : ℕ) [NeZero q],
    (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
      Function.Surjective (gmPhi q A i)) →
    ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Surjective (gmPhi q A i) := by
  intro q _ hN A _ hSH hq i x
  obtain ⟨hH, hsep⟩ := hSH
  obtain ⟨J, _, _, D, ι, hc, hl, hst, hqj, -, -⟩ :=
    GlobalTheory.SHColim.strictlyHenselian_isColimit q A ⟨hH, hsep⟩ hq
  have hqL : IsUnit (q : LaurentPolynomial A) := by
    simpa using hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)
  obtain ⟨j, y, hy⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (D ⋙ laurentFunctor) _ (isColimit_laurent hc) 1 i).1 x hqL
  obtain ⟨B, _, _, s, hs⟩ := hst j
  haveI := hl j
  haveI : IsNoetherianRing (D.obj j) := GlobalTheory.StalkNoeth.isNoetherianRing_of_isStalk B (D.obj j) s hs
  obtain ⟨b, hb⟩ := hN (D.obj j) hs.1 (hqj j) i y
  have hn := gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q (A := D.obj j) (B := A) (ι.app j).hom (hqj j) i b
  rw [hb] at hn
  exact ⟨_, hn.symm.trans hy⟩
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.CutTransfer

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem proj_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (finGL E n (locGL E n w g)) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 := congrArg (fun z => (GeneralLinearGroup.map (pLoc E w) z).val i j) (pFin_finGL (E := E) (locGL E n w g))
  simp only [pLoc_locGL] at h1
  exact h1

theorem gl_ext_pLoc {x y : GL (Fin n) (Af E)}
    (h : ∀ v, GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) : x = y :=
  Units.ext (Matrix.ext fun i k => IsDedekindDomain.FiniteAdeleRing.ext _ fun v =>
    congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i k) (h v))

variable [_root_.NumberField.IsTotallyComplex E]

theorem comm_of_proj_eq_one (w : HeightOneSpectrum (𝓞 E)) {x : GA E n}
    (hx : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x = 1) (g : GL (Fin n) (w.adicCompletion E)) :
    x * finGL E n (locGL E n w g) = finGL E n (locGL E n w g) * x := by
  have hxw : GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x) = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrArg (fun z : GL (Fin n) (w.adicCompletion E) => z.val i j) hx
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_finGL, mul_one, one_mul]
  · simp only [map_mul, pFin_finGL]
    refine gl_ext_pLoc fun v => ?_
    simp only [map_mul]
    by_cases hv : v = w
    · subst hv
      rw [hxw, one_mul, mul_one]
    · rw [pLoc_locGL_of_ne hv, one_mul, mul_one]

theorem superDiag_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin n) (w.adicCompletion E)) :
    GlobalTheory.Whittaker.superDiag (finGL E n (locGL E n w u)) = sFin E (sLoc E w (GlobalTheory.Whittaker.superDiag u)) := by
  unfold GlobalTheory.Whittaker.superDiag

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := by
    intro h
    subst h
    simp at hj
  change (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
    sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j - sLoc E w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) +
      sLoc E w ((u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) = _
  simp [Matrix.one_apply_ne hij]

theorem psiN_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin n) (w.adicCompletion E)) :
    psiN (finGL E n (locGL E n w u)) = psiLoc w (GlobalTheory.Whittaker.superDiag u) := by
  unfold psiN psiLoc
  rw [superDiag_finGL_locGL]

theorem finGL_locGL_mem_NA' (w : HeightOneSpectrum (𝓞 E)) {u : GL (Fin n) (w.adicCompletion E)}
    (hu : u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n)) : finGL E n (locGL E n w u) ∈ NA (E := E) (a := n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
      sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j - sLoc E w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) +
        sLoc E w ((u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) = 0
    simp [Matrix.one_apply_ne hij.ne', h1 i j hij]
  · change (1 : Matrix (Fin n) (Fin n) (Ad E)) i i - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i i) +
      sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i i - sLoc E w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i i) +
        sLoc E w ((u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i i)) = 1
    simp [h2 i]

end GlobalTheory.JSW.CutTransfer

namespace GlobalTheory.JSW.CutTransfer

theorem transfer : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x, ψ x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))), (∀ u ∈ U, locGL E (m + 1) w u ∈ K) → ∀ X A : Set (GL (Fin (m + 1)) (w.adicCompletion E)), GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))) X A → ∃ T : GA E (m + 1) →₀ ℂ, (∀ k ∈ T.support, ∃ g, k = finGL E (m + 1) (locGL E (m + 1) w g)) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ y : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈ A → GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ X}.indicator W y := by
  intro E _ _ _ m w ψ hψ K U hU X A hcut
  classical
  obtain ⟨T₀, hT₀⟩ := hcut
  let Φ : GL (Fin (m + 1)) (w.adicCompletion E) →* GA E (m + 1) := (finGL E (m + 1)).comp (locGL E (m + 1) w)
  have hΦ : ∀ g, Φ g = finGL E (m + 1) (locGL E (m + 1) w g) := fun _ => rfl
  refine ⟨T₀.mapDomain Φ, ?_, ?_⟩
  · intro k hk
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hk)
    exact ⟨g, rfl⟩
  · intro W hN hK y hy
    set yw := GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y with hyw
    set x := y * (Φ yw)⁻¹ with hxdef
    have hx : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x = 1 := by
      rw [hxdef, map_mul, map_inv, hΦ, proj_finGL_locGL, ← hyw, mul_inv_cancel]
    have hcomm : ∀ g, x * Φ g = Φ g * x := fun g => comm_of_proj_eq_one w hx g
    have hxy : ∀ g, x * Φ (yw * g) = y * Φ g := by
      intro g
      rw [map_mul, hxdef, mul_assoc, ← mul_assoc (Φ yw)⁻¹, inv_mul_cancel, one_mul]
    let f : GL (Fin (m + 1)) (w.adicCompletion E) → ℂ := fun g => W (x * Φ g)
    have hf1 : GlobalTheory.JSW.KirFin.Eqv ψ f := by
      intro u hu g
      show W (x * Φ (u * g)) = ψ (GlobalTheory.Whittaker.superDiag u) * W (x * Φ g)
      rw [map_mul, ← mul_assoc, hcomm u, mul_assoc, hΦ u, hN _ (finGL_locGL_mem_NA' w hu), psiN_finGL_locGL, hψ]
      rfl
    have hf2 : ∀ u ∈ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))), ∀ g, f (g * u) = f g := by
      intro u hu g
      show W (x * Φ (g * u)) = W (x * Φ g)
      rw [map_mul, ← mul_assoc, hΦ u, hK _ (hU u hu)]
    have key := hT₀ f hf1 hf2 yw hy
    have hact : GlobalTheory.JSW.Cut.act (T₀.mapDomain Φ) W y = GlobalTheory.JSW.Cut.act T₀ f yw := by
      unfold GlobalTheory.JSW.Cut.act
      rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
      refine Finset.sum_congr rfl fun k _ => ?_
      show _ * W (y * Φ k) = _ * W (x * Φ (yw * k))
      rw [hxy]
    rw [hact, key]
    by_cases h : yw ∈ X
    · have h' : y ∈ {z : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) z ∈ X} := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
      show W (x * Φ yw) = W y
      rw [hxdef, mul_assoc, inv_mul_cancel, mul_one]
    · have h' : y ∉ {z : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) z ∈ X} := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

end GlobalTheory.JSW.CutTransfer
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

theorem _root_.GlobalTheory.T.normalised_isoPowerBundle_ratio_unit_eq_one : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), IsAbelianScheme A → L.IsLB → M.IsLB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (α α₂ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)) (v : Γ(A'.left, ⊤)ˣ), IsTest A B L M t A' B' φA' φB' Φ' → ψA ≫ (snd (topS Rg) A).left = φA' → ψB ≫ (snd (topS Rg) B).left = φB' → (∀ p, α.s p = res (le_top : (isoLB (L := L) (M := M) k Φ' ψA ψB).U p ≤ ⊤) v * α₂.s p) → RigEq L M k eA eB t Φ' ψA ψB α → RigEq L M k eA eB t Φ' ψA ψB α₂ → v = 1 := by
  first | (exact @GlobalTheory.HomFixUnit.ratio_unit_eq_one) | (exact GlobalTheory.HomFixUnit.ratio_unit_eq_one) | (intros; apply GlobalTheory.HomFixUnit.ratio_unit_eq_one  <;> assumption)
end
