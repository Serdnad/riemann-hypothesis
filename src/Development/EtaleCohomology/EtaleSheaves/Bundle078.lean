module

public import Development.EtaleCohomology.EtaleSheaves.Bundle068
public import Development.EtaleCohomology.EtaleSheaves.Bundle004
public import Development.EtaleCohomology.EtaleSheaves.Bundle003
public import Development.EtaleCohomology.EtaleSheaves.Bundle005
public import Development.EtaleCohomology.EtaleSheaves.Bundle006
public import Development.EtaleCohomology.EtaleSheaves.Bundle007
public import Development.EtaleCohomology.EtaleSheaves.Bundle015
public import Development.EtaleCohomology.EtaleSheaves.Bundle069
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafVanWPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafVan0Pf

section Cone
variable {C : Type*} [Category C] [Preadditive C] {K L M : CochainComplex C ℤ} (φ : K ⟶ L) [HomologicalComplex.HasHomotopyCofiber φ]

theorem desc_δ {n m : ℤ} (α : Cochain K M m) (β : Cochain L M n) (h : m + 1 = n) (n' : ℤ) (hn' : n + 1 = n') :
    δ n n' (mappingCone.descCochain φ α β h) =
      mappingCone.descCochain φ (δ m n α + n'.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (δ n n' β) hn' := by
  rw [mappingCone.δ_descCochain φ α β h n' hn']; rfl

theorem desc_eq_zero {n m : ℤ} {α : Cochain K M m} {β : Cochain L M n} {h : m + 1 = n}
    (H : mappingCone.descCochain φ α β h = 0) : α = 0 ∧ β = 0 := by
  constructor
  · have := mappingCone.inl_descCochain φ α β h
    rw [H, Cochain.comp_zero] at this; exact this.symm
  · have := mappingCone.inr_descCochain φ α β h
    rw [H, Cochain.comp_zero] at this; exact this.symm

theorem units_mul_self' (u : ℤˣ) : u * u = 1 := Int.units_mul_self u

theorem cone_zero
    (hinj : ∀ (n : ℤ) (x : Cocycle L M n),
      CohomologyClass.mk (zcomp (Cocycle.ofHom φ) x (zero_add n)) = 0 → CohomologyClass.mk x = 0)
    (hsurj : ∀ (n : ℤ) (y : Cocycle K M n), ∃ x : Cocycle L M n,
      CohomologyClass.mk (zcomp (Cocycle.ofHom φ) x (zero_add n)) = CohomologyClass.mk y)
    (n : ℤ) (z : Cocycle (mappingCone φ) M n) : CohomologyClass.mk z = 0 := by
  set a : Cochain K M (n - 1) := (mappingCone.inl φ).comp z.1 (by omega) with ha
  set b : Cochain L M n := (Cochain.ofHom (mappingCone.inr φ)).comp z.1 (zero_add n) with hb
  have hz : z.1 = mappingCone.descCochain φ a b (by omega) := by
    rw [mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
    simp [ha, hb]
  have h0 := Cocycle.δ_eq_zero z (n + 1)
  rw [hz, desc_δ φ a b _ (n + 1) rfl] at h0
  obtain ⟨h1, h2⟩ := desc_eq_zero φ h0
  have hda : δ (n - 1) n a = -((n + 1).negOnePow • (Cochain.ofHom φ).comp b (zero_add n)) := eq_neg_of_add_eq_zero_left h1
  let bc : Cocycle L M n := Cocycle.mk b (n + 1) rfl h2
  have hb0 : CohomologyClass.mk bc = 0 := by
    apply hinj
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨-((n + 1).negOnePow • a), ?_⟩
    rw [δ_neg, δ_units_smul, hda, smul_neg, neg_neg, smul_smul, units_mul_self', one_smul]
    simp [zcomp, bc]
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hb0
  obtain ⟨γ, hγ⟩ := hb0
  change δ (n - 1) n γ = b at hγ
  set a' : Cochain K M (n - 1) := a - n.negOnePow • (Cochain.ofHom φ).comp γ (zero_add _) with ha'
  let w : Cochain (mappingCone φ) M (n - 1) := mappingCone.descCochain φ (0 : Cochain K M (n - 1 - 1)) γ (by omega)
  have hw : δ (n - 1) n w = mappingCone.descCochain φ (n.negOnePow • (Cochain.ofHom φ).comp γ (zero_add _)) b (by omega) := by
    simp only [w]; rw [desc_δ φ _ γ _ n (by omega), hγ, δ_zero, zero_add]
  have hda' : δ (n - 1) n a' = 0 := by
    have e : mappingCone.descCochain φ a' (0 : Cochain L M n) (by omega) = z.1 - δ (n - 1) n w := by
      rw [hz, hw, mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
      simp [ha']
    have e2 := congrArg (δ n (n + 1)) e
    rw [δ_sub, δ_δ, sub_zero, Cocycle.δ_eq_zero, desc_δ φ _ _ _ (n + 1) rfl] at e2
    have := (desc_eq_zero φ e2).1
    simpa using this
  obtain ⟨x, hx⟩ := hsurj (n - 1) (Cocycle.mk a' n (by omega) hda')
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1 - 1) (by omega)] at hx
  obtain ⟨γ', hγ'⟩ := hx
  change δ (n - 1 - 1) (n - 1) γ' = (Cochain.ofHom φ).comp x.1 (zero_add _) - a' at hγ'
  have hdx := Cocycle.δ_eq_zero x n
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨w + n.negOnePow • mappingCone.descCochain φ (0 : Cochain K M (n - 1 - 1)) x.1 (by omega) -
    mappingCone.descCochain φ γ' (0 : Cochain L M (n - 1)) (by omega), ?_⟩
  rw [δ_sub, δ_add, δ_units_smul, hw, desc_δ φ _ _ _ n (by omega), desc_δ φ _ _ _ n (by omega), hγ', hdx]
  change _ = z.1
  rw [hz, mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
  constructor
  · simp only [mappingCone.inl_descCochain, Cochain.comp_add, Cochain.comp_sub, Cochain.comp_units_smul, δ_zero, zero_add,
      Cochain.comp_zero, smul_zero, add_zero, smul_smul, units_mul_self', one_smul, ha']
    abel
  · simp
end Cone

section Geo
variable {R : Type} [CommRing R] (F : Shv R)

theorem hrel_sub {U E : Spc} (f : U ⟶ E) (h : Eqv R f F) (n : ℤ) : Subsingleton (Hrel R f F n) := by
  have hinj : ∀ (n : ℤ) (x : Cocycle ((chains R).obj E) (res R F) n),
      CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) x (zero_add n)) = 0 → CohomologyClass.mk x = 0 := by
    intro n x hx
    apply (h n).1
    change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) x (zero_add n)) = pull R f F n 0
    rw [map_zero]; exact hx
  have hsurj : ∀ (n : ℤ) (y : Cocycle ((chains R).obj U) (res R F) n), ∃ x : Cocycle ((chains R).obj E) (res R F) n,
      CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) x (zero_add n)) = CohomologyClass.mk y := by
    intro n y
    obtain ⟨c, hc⟩ := (h n).2 (CohomologyClass.mk y)
    obtain ⟨x, rfl⟩ := c.mk_surjective
    exact ⟨x, hc⟩
  refine ⟨fun y y' => ?_⟩
  obtain ⟨z, rfl⟩ := y.mk_surjective
  obtain ⟨z', rfl⟩ := y'.mk_surjective
  change CohomologyClass.mk z = CohomologyClass.mk z'
  rw [cone_zero _ hinj hsurj n z, cone_zero _ hinj hsurj n z']

theorem eqv_of_iso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] : Eqv R (sch.map f) F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (sch.map (inv f)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  · rw [← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

theorem eqv_of_square {P Q X Y : Scheme.{0}} (a : P ⟶ X) (f : X ⟶ Y) (h : P ⟶ Q) (c : Q ⟶ Y) (w : a ≫ f = h ≫ c)
    (ha : Eqv R (sch.map a) F) (hh : Eqv R (sch.map h) F) (hc : Eqv R (sch.map c) F) : Eqv R (sch.map f) F := by
  intro n
  have key : ∀ y, pull R (sch.map a) F n (pull R (sch.map f) F n y) = pull R (sch.map h) F n (pull R (sch.map c) F n y) := by
    intro y; rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, w]
  constructor
  · intro y y' e
    apply (hc n).1; apply (hh n).1
    rw [← key, ← key, e]
  · intro x
    obtain ⟨u, hu⟩ := (hh n).2 (pull R (sch.map a) F n x)
    obtain ⟨v, rfl⟩ := (hc n).2 u
    refine ⟨v, (ha n).1 ?_⟩
    rw [key, hu]
end Geo

theorem commGroup_inv_eq_conj_twist_identity {B W S X T : Scheme.{0}} (pA : X ⟶ S) (s : S ⟶ B) (ι : W ⟶ B) [Mono ι] (r : T ⟶ S) (w : T ⟶ W)
    (hw : w ≫ ι = r ≫ s) (hc : (pullback.fst (pullback.fst (pA ≫ s) ι ≫ pA) r ≫ pullback.fst (pA ≫ s) ι) ≫ pA =
      pullback.snd (pullback.fst (pA ≫ s) ι ≫ pA) r ≫ r) :
    IsIso (pullback.lift (pullback.fst (pullback.fst (pA ≫ s) ι ≫ pA) r ≫ pullback.fst (pA ≫ s) ι)
      (pullback.snd (pullback.fst (pA ≫ s) ι ≫ pA) r) hc) := by
  have c1 : pullback.fst pA r ≫ pA ≫ s = (pullback.snd pA r ≫ w) ≫ ι := by
    simp only [Category.assoc, hw]; exact pullback.condition_assoc s
  have c2 : pullback.lift (pullback.fst pA r) (pullback.snd pA r ≫ w) c1 ≫ pullback.fst (pA ≫ s) ι ≫ pA =
      pullback.snd pA r ≫ r := by
    rw [← Category.assoc, pullback.lift_fst, pullback.condition]
  refine ⟨⟨pullback.lift (pullback.lift (pullback.fst pA r) (pullback.snd pA r ≫ w) c1) (pullback.snd pA r) c2, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
      · rw [← cancel_mono ι]
        simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, hw]
        have e3 : pullback.fst (pA ≫ s) ι ≫ pA ≫ s = pullback.snd (pA ≫ s) ι ≫ ι := pullback.condition
        have e4 := pullback.condition_assoc (f := pullback.fst (pA ≫ s) ι ≫ pA) (g := r) s
        simp only [Category.assoc] at e4
        rw [← e3]
        first | exact e4 | exact e4.symm
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
  · apply pullback.hom_ext
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]

theorem closed_eq {A : Type} [CommRing A] [IsLocalRing A] (x : Sp A) (hx : ∀ z : Sp A, z ⤳ x) :
    x = IsLocalRing.closedPoint A :=
  ((IsLocalRing.specializes_closedPoint x).antisymm (hx _)).eq

theorem LeafVanW_of : LeafVanW := by
  intro hH q _ k _ hq i B W Y b ι _ p hp A _ s hA hx m
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE2, -⟩ := hH
  obtain ⟨hHen, hsep⟩ := hA
  haveI : IsProper p := hp
  have hqA : IsUnit (q : A) := by
    have := hq.map (Spec.preimage (s ≫ b)).hom
    simpa using this

  obtain ⟨x, hx1, w0, hw0⟩ := hx
  have hxc := closed_eq x hx1
  have hrpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) =
      IsLocalRing.closedPoint A := IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
  haveI : Surjective (pullback.fst (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) ι) := by
    constructor
    intro t
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) (g := ι)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) w0 (by
        have := congrArg s hrpt
        rw [← hxc, ← hw0] at this
        exact this)
    exact ⟨z, hz.trans (Subsingleton.elim _ _)⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.fst (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) ι)
  have hw : (inv (pullback.fst (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) ι) ≫ pullback.snd _ _) ≫ ι =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

  have e1 := hE2 q A ⟨hHen, hsep⟩ hqA (pullback.snd p s) i
  have e2 := hE2 q A ⟨hHen, hsep⟩ hqA (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s) i
  have hc : (pullback.fst (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
      pullback.fst (pullback.snd p s ≫ s) ι) ≫ pullback.snd p s =
      pullback.snd (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) := by
    rw [Category.assoc, pullback.condition]
  haveI := commGroup_inv_eq_conj_twist_identity (pullback.snd p s) s ι _ _ hw hc
  have heqv : Eqv (ZMod q) (sch.map (prS p ι s)) (tw q i) :=
    eqv_of_square _ _ _ _ _ (pullback.lift_fst _ _ _).symm e2 (eqv_of_iso _ (pullback.lift (pullback.fst (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ pullback.fst (pullback.snd p s ≫ s) ι) _ hc)) e1
  exact hrel_sub _ _ heqv m

end LateralTheory.E.LeafVanWPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafSurj0WPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.E8.TwSec

theorem neg_cochain (R : Type) [CommRing R] (E : Spc) (F : Shv R) (m : ℤ) (hm : m < 0)
    (z : Cochain ((chains R).obj E) (res R F) m) : z = 0 := by
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  rw [Cochain.zero_v]
  by_cases hq : q < 0
  · exact (LateralTheory.E.LeafNegPf.res_isZero R F q hq).eq_of_tgt _ _
  · exact (LateralTheory.E.LeafNegPf.chains_isZero R E p (by omega)).eq_of_src _ _

theorem fgt_zero (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (y : Hrel R f F 0)
    (h : fgt R f F 0 y = 0) : y = 0 := by
  obtain ⟨z, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom (mappingCone.inr ((chains R).map f))) z (zero_add 0)) = 0 at h
  rw [CohomologyClass.mk_eq_zero_iff] at h
  obtain ⟨m, hm, β, hβ⟩ := h
  rw [neg_cochain R E F m (by omega) β, δ_zero] at hβ
  have hz : z = 0 := by
    apply Cocycle.ext
    rw [mappingCone.ext_cochain_from_iff _ (-1) 0 (by omega)]
    refine ⟨(neg_cochain R U F _ (by omega) _).trans (neg_cochain R U F _ (by omega) _).symm, ?_⟩
    rw [Cocycle.coe_zero, Cochain.comp_zero]
    exact hβ.symm
  rw [hz]
  rfl

theorem pull_fgt (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (F : Shv R) (n : ℤ) (y : Hrel R f F n) :
    pull R f F n (fgt R f F n y) = 0 := by
  obtain ⟨z, rfl⟩ := y.mk_surjective
  exact LateralTheory.E.LeafConeExactPf.pre_inr_eq_zero _ n z

theorem twPt : LeafTwPt := LeafTwPt_of LeafTwAdj_of LeafTwGen_of LeafTwFieldZ_of

theorem secKill (q : ℕ) [NeZero q] {X Z : Scheme.{0}} (ι : Z ⟶ X) (j : ℤ) (s : Sec (tw q j) X) (hs : Sec.res ι s = 0)
    (z : Z) : ∃ (W : Scheme.{0}) (w : W ⟶ X), Etale w ∧ ι z ∈ Set.range w ∧ Sec.res w s = 0 := by
  obtain ⟨U, w, hw, ⟨u, hu⟩, t, ht⟩ := LateralTheory.E.LeafOfRingsLocSurjPf.LeafOfRingsLocSurj_of (ZMod q) (twF q j) X s (ι z)
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := w) (g := ι) u z hu
  have e2 : Sec.res (F := tw q j) (pullback.fst w ι) (Sec.res w s) = 0 := by
    rw [← res_comp, pullback.condition, res_comp, hs]
    exact map_zero _
  have hP : ofRings.sec (twF q j) _ (((twF q j).map (Scheme.Γ.map (pullback.fst w ι).op)).hom t) = 0 := by
    rw [← sec_res, ← ht]
    exact e2
  obtain ⟨V, v, -, ⟨v0, hv0⟩, hV⟩ := LeafOfRingsLocInj_of (ZMod q) (twF q j) _ _ hP p
  obtain ⟨W, w', hw', ⟨a, ha⟩, hW⟩ := twPt q j U u t V (v ≫ pullback.fst w ι) v0 (by simp [hv0, hp1])
    ((twF_res_comp j _ _ t).trans hV)
  refine ⟨W, w' ≫ w, inferInstance, ⟨a, by simp [ha, hu]⟩, ?_⟩
  rw [res_comp]
  have e := sec_res (twF q j) w' t
  rw [hW] at e
  exact (congrArg (Sec.res w') ht).trans (e.trans (sec_zero _ _))

def zeroLocus {R : Type} [CommRing R] {F : Shv R} {X : Scheme.{0}} (s : Sec F X) : Set X :=
  {x | ∃ (W : Scheme.{0}) (w : W ⟶ X), Etale w ∧ x ∈ Set.range w ∧ Sec.res w s = 0}

theorem isOpen_zeroLocus {R : Type} [CommRing R] {F : Shv R} {X : Scheme.{0}} (s : Sec F X) : IsOpen (zeroLocus s) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨W, w, hw, hx, h0⟩
  exact ⟨Set.range w, fun y hy => ⟨W, w, hw, hy, h0⟩, w.isOpenMap.isOpen_range, hx⟩

theorem res_zero_of_range {R : Type} [CommRing R] {F : Shv R} {X T : Scheme.{0}} (s : Sec F X) (g : T ⟶ X)
    (hg : ∀ t, g t ∈ zeroLocus s) : Sec.res g s = 0 := by
  apply LateralTheory.E.PointDetect0Pf.etSep R F T
  intro t
  obtain ⟨W, w, hw, ⟨u, hu⟩, h0⟩ := hg t
  obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := w) t u hu.symm
  refine ⟨_, pullback.fst g w, inferInstance, ⟨p, hp1⟩, ?_⟩
  rw [← res_comp, pullback.condition, res_comp, h0]
  exact map_zero _

theorem core (h9 : A9) (q : ℕ) [NeZero q] (i : ℤ) {B W Y : Scheme.{0}} (ι : W ⟶ B) (P : Y ⟶ B) [IsProper P]
    (U : B.Etale) (y : Hrel (ZMod q) (sch.map (prU P ι U)) (tw q i) 0) (x : U.left) (hx : U.hom x ∈ Set.range ι) :
    ∃ (U' : B.Etale) (a : U' ⟶ U), x ∈ Set.range a.left ∧
      ∀ (U'' : B.Etale) (b : U'' ⟶ U'), rY q i P ι (b ≫ a) 0 y = 0 := by
  obtain ⟨e, he, -⟩ := (h9 (ZMod q) (tw q i)).2
  obtain ⟨s, hs⟩ := (e (YU P U)).surjective (fgt (ZMod q) (sch.map (prU P ι U)) (tw q i) 0 y)
  have hZ : Sec.res (prU P ι U) s = 0 := by
    apply (e _).injective
    rw [← he, hs, map_zero]
    exact pull_fgt _ _ _ _ _
  have hcl : IsClosed ((toBY P U) '' (zeroLocus s)ᶜ) :=
    (toBY P U).isClosedMap _ (isOpen_zeroLocus s).isClosed_compl
  let O : U.left.Opens := ⟨_, hcl.isOpen_compl⟩
  have hxO : x ∈ O := by
    rintro ⟨t, ht, htx⟩
    obtain ⟨w0, hw0⟩ := hx
    obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd P U.hom ≫ U.hom) (g := ι) t w0
      (by rw [hw0, ← htx]; rfl)
    apply ht
    rw [← hp1]
    exact secKill q (prU P ι U) i s hZ p
  have hU : Etale U.hom := U.prop
  let U' : B.Etale := MorphismProperty.Over.mk ⊤ (O.ι ≫ U.hom) (inferInstanceAs (Etale (O.ι ≫ U.hom)))
  let a : U' ⟶ U := MorphismProperty.Over.homMk O.ι rfl
  refine ⟨U', a, ⟨⟨x, hxO⟩, rfl⟩, fun U'' b => ?_⟩
  apply fgt_zero
  refine (relNat _ _ _ _ _ _ _ _ _).trans ?_
  rw [← hs, he, res_zero_of_range s _ ?_, map_zero]
  intro t
  by_contra hn
  have h1 : resY P (b ≫ a) ≫ toBY P U = (toBY P U'' ≫ b.left) ≫ O.ι := by
    simp only [resY, toBY, pullback.lift_snd]
    rfl
  have h2 : toBY P U (resY P (b ≫ a) t) ∈ O := by
    rw [← Scheme.Hom.comp_apply, h1]
    exact ((toBY P U'' ≫ b.left) t).2
  exact h2 ⟨_, hn, rfl⟩

theorem LeafSurj0W_of : LateralTheory.E.LeafSurj0Pf.LeafSurj0W := by
  intro hy q _ k _ _ i B W Y0 Y1 Y2 _ ι _ V _ p g1 g2 _ _ h2 _ U y x hx
  exact core hy.2.2.2.2.2.2.2.1 q i ι (g2 ≫ g1 ≫ p) U y x hx

end LateralTheory.E.LeafSurj0WPf
end
end

section

open TensorProduct

namespace LateralTheory.E.LeafZModInjFlatPf

universe v

theorem flat_of_injective_of_ann {R : Type v} [CommRing R] [IsPrincipalIdealRing R]
    (hP : ∀ a : R, ∃ b : R, b * a = 0 ∧ ∀ r : R, r * b = 0 → ∃ s : R, r = s * a)
    (M : Type v) [AddCommGroup M] [Module R M] (hM : Module.Injective R M) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  obtain ⟨a, rfl⟩ : ∃ a : R, I = Ideal.span {a} :=
    ⟨_, (Ideal.span_singleton_generator I).symm⟩
  have ha : a ∈ Ideal.span ({a} : Set R) := Ideal.mem_span_singleton_self a
  have key : ∀ x : Ideal.span ({a} : Set R) ⊗[R] M, ∃ m : M, x = (⟨a, ha⟩ : Ideal.span ({a} : Set R)) ⊗ₜ m := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul i n =>
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 i.2
      refine ⟨s • n, ?_⟩
      rw [← smul_tmul]
      congr 1
      ext
      simp [smul_eq_mul, hs]
    | add x y hx hy =>
      obtain ⟨m1, rfl⟩ := hx
      obtain ⟨m2, rfl⟩ := hy
      exact ⟨m1 + m2, (tmul_add _ _ _).symm⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, rfl⟩ := key x
  simp at hx
  obtain ⟨b, hba, hb⟩ := hP a
  have well : ∀ r r' : R, r * b = r' * b → r • m = r' • m := by
    intro r r' h
    obtain ⟨s, hs⟩ := hb (r - r') (by rw [sub_mul, h, sub_self])
    rw [← sub_eq_zero, ← sub_smul, hs, mul_smul, hx, smul_zero]
  let f : Ideal.span ({b} : Set R) → R := fun x => Classical.choose (Ideal.mem_span_singleton'.1 x.2)
  have hf : ∀ x, f x * b = x := fun x => Classical.choose_spec (Ideal.mem_span_singleton'.1 x.2)
  let g : Ideal.span ({b} : Set R) →ₗ[R] M :=
    { toFun := fun x => f x • m
      map_add' := fun x y => by
        rw [← add_smul]; apply well; rw [hf, add_mul, hf, hf]; rfl
      map_smul' := fun c x => by
        rw [RingHom.id_apply, smul_smul]; apply well; rw [hf, mul_assoc, hf]; rfl }
  obtain ⟨g', hg'⟩ := Module.Baer.of_injective hM _ g
  have hm : m = b • g' 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, hg' b (Ideal.mem_span_singleton_self b)]
    show m = f _ • m
    conv_lhs => rw [← one_smul R m]
    apply well; rw [hf, one_mul]
  rw [hm, ← smul_tmul]
  have : b • (⟨a, ha⟩ : Ideal.span ({a} : Set R)) = 0 := by ext; simp [smul_eq_mul, hba]
  rw [this, zero_tmul]

theorem zmod_ann (q : ℕ) [NeZero q] :
    ∀ a : ZMod q, ∃ b : ZMod q, b * a = 0 ∧ ∀ r : ZMod q, r * b = 0 → ∃ s, r = s * a := by
  intro a
  set d := Nat.gcd a.val q with hd
  have hdq : d ∣ q := Nat.gcd_dvd_right _ _
  have hda : d ∣ a.val := Nat.gcd_dvd_left _ _
  have hq0 : q ≠ 0 := NeZero.ne q
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hq0)
  refine ⟨((q / d : ℕ) : ZMod q), ?_, ?_⟩
  · conv_lhs => rw [← ZMod.natCast_zmod_val a]
    rw [← Nat.cast_mul]
    obtain ⟨t, ht⟩ := hda
    have : q / d * a.val = q * t := by
      rw [ht, ← mul_assoc, Nat.div_mul_cancel hdq]
    rw [this, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  · intro r hr
    rw [← ZMod.natCast_zmod_val r, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hr
    have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hdq) hd0
    have h2 : d * (q / d) ∣ r.val * (q / d) := by rwa [Nat.mul_div_cancel' hdq]
    obtain ⟨t, ht⟩ := Nat.dvd_of_mul_dvd_mul_right hqd h2
    refine ⟨a⁻¹ * t, ?_⟩
    rw [← ZMod.natCast_zmod_val r, ht, Nat.cast_mul, hd, ← ZMod.mul_inv_eq_gcd]
    ring

instance pir_zmod (q : ℕ) : IsPrincipalIdealRing (ZMod q) :=
  IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod q)) ZMod.intCast_surjective

instance pir_ulift (q : ℕ) : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
  IsPrincipalIdealRing.of_surjective (ULift.ringEquiv.{0, 1} (R := ZMod q)).symm
    (ULift.ringEquiv.{0, 1} (R := ZMod q)).symm.surjective

theorem ulift_ann (q : ℕ) [NeZero q] :
    ∀ a : ULift.{1} (ZMod q), ∃ b, b * a = 0 ∧ ∀ r, r * b = 0 → ∃ s, r = s * a := by
  intro a
  obtain ⟨b, hba, hb⟩ := zmod_ann q a.down
  refine ⟨ULift.up b, ULift.ext hba, fun r hr => ?_⟩
  obtain ⟨s, hs⟩ := hb r.down (congrArg ULift.down hr)
  exact ⟨ULift.up s, ULift.ext hs⟩

theorem LeafZModInjFlat_of : LateralTheory.E.LeafTensQIsoPf.LeafZModInjFlat := by
  intro q _ M _ _ hM
  exact flat_of_injective_of_ann (ulift_ann q) M hM

end LateralTheory.E.LeafZModInjFlatPf
end
