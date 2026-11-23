module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair

theorem IsLocModel.exists_finiteType_localization :
    ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L), IsLocModel c R →
    ∃ (S : Subring L) (hS : ∀ a, c a ∈ S) (q : Ideal S), q.IsPrime ∧ (c.codRestrict S hS).FiniteType ∧
      (∀ f : L, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ f * b = a) ∧
      ∀ f : L, f ∈ R ↔ ∃ a b : S, b ∉ q ∧ f * b = a := by
  intro L _ c R hR
  letI := hR.isLocalRing
  letI : Algebra ℂ R := (c.codRestrict R hR.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := hR.essFiniteType
  obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff ℂ R).mp inferInstance
  set A := Algebra.adjoin ℂ (σ : Set R) with hA
  let S : Subring L := A.toSubring.map R.subtype
  have hSR : S ≤ R := by
    rintro _ ⟨x, -, rfl⟩; exact x.2
  have memS : ∀ x : R, x ∈ A → (x : L) ∈ S := fun x hx => ⟨x, hx, rfl⟩
  have hS : ∀ a, c a ∈ S := fun a => memS ⟨c a, hR.const_mem a⟩ (A.algebraMap_mem a)
  let q : Ideal S := (IsLocalRing.maximalIdeal R).comap (Subring.inclusion hSR)
  have unit_ne : ∀ t : R, IsUnit t → (t : L) ≠ 0 := by
    intro t ht h0
    obtain ⟨u, hu⟩ := ht.exists_right_inv
    have := congrArg (fun x : R => (x : L)) hu
    simp [h0] at this
  refine ⟨S, hS, q, Ideal.comap_isPrime _ _, ?_, ?_, ?_⟩
  · have hA' : Algebra.FiniteType ℂ A :=
      (Subalgebra.fg_iff_finiteType A).mp (Subalgebra.fg_adjoin_finset σ)
    let e : A.toSubring ≃+* S := A.toSubring.equivMapOfInjective R.subtype Subtype.val_injective
    have he : c.codRestrict S hS = (e.toRingHom : A →+* S).comp (algebraMap ℂ A) := by
      ext a; rfl
    have h2 : (algebraMap ℂ A).FiniteType := RingHom.finiteType_algebraMap.mpr hA'
    rw [he]
    exact RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ e.surjective) h2
  · intro f
    obtain ⟨r1, hr1, r2, hr2, hr20, e⟩ := hR.frac f
    obtain ⟨t1, ht1A, ht1, h1⟩ := hσ ⟨r1, hr1⟩
    obtain ⟨t2, ht2A, ht2, h2⟩ := hσ ⟨r2, hr2⟩
    refine ⟨r1 * t1 * t2, ?_, r2 * t2 * t1, ?_, ?_, ?_⟩
    · simpa using memS _ (A.mul_mem h1 ht2A)
    · simpa using memS _ (A.mul_mem h2 ht1A)
    · exact mul_ne_zero (mul_ne_zero hr20 (unit_ne _ ht2)) (unit_ne _ ht1)
    · rw [← e]; ring
  · intro f
    constructor
    · intro hf
      obtain ⟨t, htA, ht, h⟩ := hσ ⟨f, hf⟩
      refine ⟨⟨_, memS _ h⟩, ⟨_, memS _ htA⟩, ?_, rfl⟩
      intro hq
      exact (IsLocalRing.mem_maximalIdeal _).1 hq ht
    · rintro ⟨a, b, hb, e⟩
      have hu : IsUnit (Subring.inclusion hSR b) := by
        by_contra h; exact hb ((IsLocalRing.mem_maximalIdeal _).2 h)
      obtain ⟨u, hu'⟩ := hu.exists_right_inv
      have hu'' : (b : L) * (u : L) = 1 := by
        have := congrArg (fun x : R => (x : L)) hu'; simpa using this
      have hf : f = a * u := by rw [← e, mul_assoc, hu'', mul_one]
      rw [hf]; exact R.mul_mem (hSR a.2) u.2

end GlobalTheory.FieldPair
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.OpenSpecField

variable {S : Type} [CommRing S] [IsDomain S] {Y : Scheme.{0}} [IsIntegral Y]
  (j : Sp S ⟶ Y) [IsOpenImmersion j]

abbrev img : Y.Opens := j ''ᵁ ⊤

theorem isAffineOpen_img : IsAffineOpen (img j) := (isAffineOpen_top _).image_of_isOpenImmersion j

theorem mem_img (q : Sp S) : j.base q ∈ img j := ⟨q, trivial, rfl⟩

instance : Nonempty (img j) := ⟨⟨_, mem_img j (Classical.arbitrary (PrimeSpectrum S))⟩⟩

theorem gen_mem_img : genericPoint Y ∈ img j :=
  gen_mem (mem_img j (Classical.arbitrary (PrimeSpectrum S)))

def secEquiv : Γ(Y, img j) ≃+* S :=
  ((j.appIso ⊤) ≪≫ Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv

instance : IsFractionRing Γ(Y, img j) Y.functionField :=
  functionField_isFractionRing_of_isAffineOpen Y _ (isAffineOpen_img j)

def fieldEquiv : Y.functionField ≃+* FractionRing S := IsFractionRing.ringEquivOfRingEquiv (secEquiv j)

theorem fieldEquiv_fnOf (a : Γ(Y, img j)) :
    fieldEquiv j (fnOf _ (gen_mem_img j) a) = algebraMap S (FractionRing S) (secEquiv j a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a

theorem mem_basicOpen_iff (q : Sp S) (b : Γ(Y, img j)) :
    j.base q ∈ Y.basicOpen b ↔ secEquiv j b ∉ q.asIdeal := by
  have h : (Sp S).basicOpen ((j.appIso ⊤).hom b) = (Sp S).basicOpen (j.app (img j) b) := by
    rw [Scheme.Hom.appIso_hom, CommRingCat.comp_apply, Scheme.basicOpen_res]
    exact top_inf_eq _
  change q ∈ j ⁻¹ᵁ Y.basicOpen b ↔ _
  rw [Scheme.preimage_basicOpen, ← h, basicOpen_eq_of_affine']
  exact PrimeSpectrum.mem_basicOpen _ _

theorem secEquiv_algX [Algebra ℂ S] (p : Y ⟶ Sp ℂ) (hjp : j ≫ p = spMap (algebraMap ℂ S)) (a : ℂ) :
    secEquiv j (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (img j) a) = algebraMap ℂ S a := by
  have key : p.appLE ⊤ (img j) (show img j ≤ p ⁻¹ᵁ ⊤ from le_top) ≫ (j.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫ CommRingCat.ofHom (algebraMap ℂ S) := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE_assoc]
    simp only [hjp]
    have e : (spMap (algebraMap ℂ S)).appLE ⊤ ⊤ (show (⊤ : (Sp S).Opens) ≤ spMap (algebraMap ℂ S) ⁻¹ᵁ ⊤ from le_top) = (spMap (algebraMap ℂ S)).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    rw [e]
    exact Scheme.ΓSpecIso_naturality _
  have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv a)) key
  refine Eq.trans ?_ (this.trans ?_)
  · rfl
  · simp

theorem fieldEquiv_constFn [Algebra ℂ S] (p : Y ⟶ Sp ℂ) (hjp : j ≫ p = spMap (algebraMap ℂ S))
    (a : ℂ) : fieldEquiv j (GlobalTheory.Cartier.constFn p a) = algebraMap ℂ (FractionRing S) a := by
  rw [← fnOf_comp_algX p (img j) (gen_mem_img j), RingHom.comp_apply, fieldEquiv_fnOf,
    secEquiv_algX j p hjp, IsScalarTower.algebraMap_apply ℂ S (FractionRing S)]

theorem mem_map_locRing (q : Sp S) (g : FractionRing S) :
    g ∈ (locRing (j.base q)).map (fieldEquiv j).toRingHom ↔
      ∃ a b : S, b ∉ q.asIdeal ∧
        g * algebraMap S (FractionRing S) b = algebraMap S (FractionRing S) a := by
  have hU := isAffineOpen_img j
  have hy := mem_img j q
  have hg := gen_mem_img j
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨V, hyV, c, rfl⟩ := (mem_locRing.1 hf).exists_fnOf
    obtain ⟨b, hbV, hyb⟩ := hU.exists_basicOpen_le ⟨_, hyV⟩ hy
    have := hU.isLocalization_basicOpen b
    obtain ⟨⟨t, s, hs⟩, hts⟩ := IsLocalization.surj (Submonoid.powers b) (resG Y hbV c)
    obtain ⟨n, rfl⟩ := hs
    have hW : genericPoint Y ∈ Y.basicOpen b := gen_mem hyb
    have e1 := congrArg (fnOf _ hW) hts
    change fnOf _ hW (resG Y hbV c * resG Y (Y.basicOpen_le b) (b ^ n)) =
      fnOf _ hW (resG Y (Y.basicOpen_le b) t) at e1
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG] at e1
    refine ⟨secEquiv j t, secEquiv j (b ^ n), ?_, ?_⟩
    · rw [map_pow]
      exact fun h => (mem_basicOpen_iff j q b).1 hyb (q.isPrime.mem_of_pow_mem n h)
    · rw [← fieldEquiv_fnOf, ← fieldEquiv_fnOf]
      change fieldEquiv j _ * _ = _
      rw [← map_mul, e1]
  · rintro ⟨a, b, hb, e⟩
    let a' := (secEquiv j).symm a
    let b' := (secEquiv j).symm b
    have hb' : j.base q ∈ Y.basicOpen b' :=
      (mem_basicOpen_iff j q b').2 (by simpa [b'] using hb)
    refine ⟨fnOf _ hg a' * (fnOf _ hg b')⁻¹, ?_, ?_⟩
    · exact mem_locRing.2 ((regAt_fnOf hy hg a').mul
        ((unitAt_fnOf_iff hy hg b').2 hb').inv.regAt)
    · have hb0 : algebraMap S (FractionRing S) b ≠ 0 := by
        refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ?_)
        rintro rfl
        exact hb q.asIdeal.zero_mem
      change fieldEquiv j _ = g
      rw [map_mul, map_inv₀, fieldEquiv_fnOf, fieldEquiv_fnOf]
      simp only [a', b', RingEquiv.apply_symm_apply]
      rw [← e, mul_inv_cancel_right₀ hb0]

theorem exists_fieldEquiv (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] (Y : Scheme.{0})
    [IsIntegral Y] (p : Y ⟶ Sp ℂ) (j : Sp S ⟶ Y) [IsOpenImmersion j]
    (hjp : j ≫ p = spMap (algebraMap ℂ S)) :
    ∃ e : Y.functionField ≃+* FractionRing S,
      (∀ a : ℂ, e (GlobalTheory.Cartier.constFn p a) = algebraMap ℂ (FractionRing S) a) ∧
      ∀ (q : PrimeSpectrum S) (g : FractionRing S), g ∈ (locRing (j.base q)).map e.toRingHom ↔
        ∃ a b : S, b ∉ q.asIdeal ∧
          g * algebraMap S (FractionRing S) b = algebraMap S (FractionRing S) a :=
  ⟨fieldEquiv j, fieldEquiv_constFn j p hjp, mem_map_locRing j⟩

end GlobalTheory.OpenSpecField
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem formOrd_dForm_of_isPrimeOf : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q),
  IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) →
  ∀ P : Place cL, P.IsPrimeOf Q → (fun ω => @dite ℤ (∃ a, P.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (fun i => (x i : L))) = 0 := by
  intro L _ cL Q hQ D x hx P hP
  let α : ℂ →+* Q := cL.codRestrict Q hQ.const_mem
  let ρ : Q →+* P.ring := RingHom.codRestrict Q.subtype P.ring (fun q => hP.1 q q.2)
  have hρ : ρ.comp α = P.const := RingHom.ext fun _ => Subtype.ext rfl
  have e : dForm cL (fun i => (x i : L)) = P.toRat D (dForm P.const fun i => ρ (x i)) := by
    have h := TopForm.formMap_dForm (D := D) (α := P.const) (β := cL) P.ring.subtype rfl (fun i => ρ (x i))
    refine Eq.trans ?_ h.symm
    congr 1
  let S : Submonoid Q :=
    { carrier := {b | (b : L) ≠ 0 ∧ P.ord b = 0}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨?_, ?_⟩
        · change (a : L) * b ≠ 0
          exact mul_ne_zero ha.1 hb.1
        · change P.ord ((a : L) * b) = 0
          rw [P.ord_mul ha.1 hb.1, ha.2, hb.2, add_zero]
      one_mem' := ⟨one_ne_zero, P.ord_one⟩ }
  letI := α.toAlgebra
  letI := P.const.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower ℂ Q P.ring := IsScalarTower.of_algebraMap_eq' hρ.symm
  haveI : IsLocalization S P.ring :=
    { map_units := fun ⟨b, hb⟩ => by
        have hinv : (b : L)⁻¹ ∈ P.ring := by
          rw [← P.ord_nonneg_iff (inv_ne_zero hb.1), P.ord_inv, hb.2, neg_zero]
        exact IsUnit.of_mul_eq_one (⟨(b : L)⁻¹, hinv⟩ : P.ring)
          (Subtype.ext (mul_inv_cancel₀ hb.1))
      surj := fun z => by
        obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP.2 z z.2
        exact ⟨(⟨a, ha⟩, ⟨⟨b, hb⟩, hb0, hbo⟩), Subtype.ext e⟩
      exists_of_eq := fun {a b} e => by
        have h : (a : L) = b := congrArg (fun z : P.ring => (z : L)) e
        exact ⟨1, by rw [Subtype.ext h]⟩ }
  haveI : Algebra.FormallyEtale Q P.ring := .of_isLocalization S
  have hG : IsFreeGen P.ring (TopForm.formMap D ρ hρ (dForm α x)) :=
    hx.of_isBaseChange (isBaseChange_exteriorPower
      (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ Q P.ring) D)
  rw [TopForm.formMap_dForm] at hG
  rw [e]
  exact P.formOrd_toRat hG

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair.Place

variable {k K : Type} [Field k] [Field K] {c : k →+* K}

theorem ord_eq_zero_iff (E : Place c) {f : K} (hf : f ≠ 0) :
    E.ord f = 0 ↔ f ∈ E.ring ∧ f⁻¹ ∈ E.ring := by
  rw [← E.ord_nonneg_iff hf, ← E.ord_nonneg_iff (inv_ne_zero hf), E.ord_inv]
  omega

end GlobalTheory.FieldPair.Place
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem eval₂_residue_ne_zero_and_inv_mem_of_isUnit :
    ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q)
  (S : Place cL) (ψ : S.ring →+* K) (F : Place cK), S.Contains Q → (∀ a, ψ (S.const a) = cK a) →
  (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) →
  ∀ (m : ℕ) (z : Fin m → Q) (zs : Fin m → S.ring), (∀ i, (zs i : L) = z i) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) →
  ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P ≠ 0 ∧
    (MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P)⁻¹ ∈ F.ring := by
  intro L K _ _ cL cK Q hQ S ψ F hSQ hc hF m z zs hz hu P hP
  let j : Q →+* S.ring := Q.subtype.codRestrict S.ring fun q => hSQ q q.2
  have h1 : (ψ.comp j).comp (cL.codRestrict Q hQ.const_mem) = cK := RingHom.ext fun a => hc a
  have h2 : (fun i => (ψ.comp j) (z i)) = fun i => ψ (zs i) :=
    funext fun i => congrArg ψ (Subtype.ext (hz i).symm)
  have h3 : (ψ.comp j) (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P) =
      MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P := by
    rw [MvPolynomial.hom_eval₂, h1, h2]
  obtain ⟨q, hq⟩ := (hu P hP).exists_right_inv
  have h4 : MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P * (ψ.comp j) q = 1 := by
    rw [← h3, ← map_mul, hq, map_one]
  refine ⟨left_ne_zero_of_mul_eq_one h4, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right h4]
  exact (hF _).2 ⟨j q, q.2, rfl⟩

end GlobalTheory.FieldPair
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.Discrepancy

namespace GlobalTheory.FieldPair

section SlopeTestRemainingChoices

variable {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) {y : X} (hy : y ∈ U)


include hU in
theorem unitAt_fnOf_of_not_mem {s : Γ(X, U)} (hs : s ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) :
    UnitAt y (fnOf U (gen_mem hy) s) := by
  letI := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hy⟩
  exact ⟨_, IsLocalization.map_units (X.presheaf.stalk y)
    (⟨s, hs⟩ : (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl), algebraMap_germ hy s⟩


include hU in
theorem regAt_exists_fraction {f : X.functionField} (hf : RegAt y f) :
    ∃ c s : Γ(X, U), s ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      f * fnOf U (gen_mem hy) s = fnOf U (gen_mem hy) c := by
  letI := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl a
  refine ⟨c, s, s.2, ?_⟩
  have e' := congrArg (algebraMap _ X.functionField) e
  rw [map_mul] at e'
  rw [← algebraMap_germ hy, ← algebraMap_germ hy]
  exact e'

end SlopeTestRemainingChoices

theorem isUnit_iff_inv_mem {K : Type} [Field K] {R : ValuationSubring K} (u : R) :
    IsUnit u ↔ (u : K) ≠ 0 ∧ (u : K)⁻¹ ∈ R := by
  constructor
  · rintro ⟨v, rfl⟩
    have h : ((v : R) : K) * ((v⁻¹ : Rˣ) : R) = 1 := by
      rw [← R.coe_mul, Units.mul_inv]; rfl
    exact ⟨left_ne_zero_of_mul_eq_one h, (inv_eq_of_mul_eq_one_right h) ▸ (v⁻¹ : Rˣ).1.2⟩
  · rintro ⟨h0, hi⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem isPrimeOf_placeEquiv {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) (x : X) :
    (placeEquiv p E).IsPrimeOf (locRing x) ↔ ∃ z, z ⤳ x ∧ E.IsAt z := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have ord0 : ∀ {b : X.functionField}, b ≠ 0 → b ∈ E.ring → b⁻¹ ∈ E.ring →
      (placeEquiv p E).ord b = 0 := fun {b} h0 h1 h2 => by
    have a1 := ((placeEquiv p E).ord_nonneg_iff h0).2 h1
    have a2 := ((placeEquiv p E).ord_nonneg_iff (inv_ne_zero h0)).2 h2
    rw [Place.ord_inv] at a2
    omega
  constructor
  · rintro ⟨hC, hP⟩
    have hT : E.Through x := (contains_placeEquiv E x).1 hC
    let φ : Γ(X, U) →+* E.ring :=
      (fnOf U (gen_mem hx)).codRestrict E.ring fun a => hT _ (regAt_fnOf hx _ a)
    let P : PrimeSpectrum Γ(X, U) := ⟨(IsLocalRing.maximalIdeal E.ring).comap φ, inferInstance⟩
    have memP (s : Γ(X, U)) : s ∉ P.asIdeal ↔
        (fnOf U (gen_mem hx) s ≠ 0 ∧ (fnOf U (gen_mem hx) s)⁻¹ ∈ E.ring) := by
      change φ s ∉ IsLocalRing.maximalIdeal E.ring ↔ _
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact isUnit_iff_inv_mem (φ s)
    have hPQ : P ≤ hU.primeIdealOf ⟨x, hx⟩ := fun s hs => by_contra fun hs' =>
      have h := unitAt_fnOf_of_not_mem hU hx hs'
      (memP s).2 ⟨h.ne_zero, hT _ h.inv.regAt⟩ hs
    have hz : hU.fromSpec P ∈ U := by
      have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
      rwa [hU.range_fromSpec] at this
    let z : U := ⟨hU.fromSpec P, hz⟩
    have hP' : hU.primeIdealOf z = P :=
      hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
    have hzx : (z : X) ⤳ x := by
      have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨x, hx⟩)).mp hPQ).map
        hU.fromSpec.continuous
      rwa [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h
    clear_value z
    refine ⟨z, hzx, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
    · obtain ⟨a, ha, b, hb, hb0, hord, e⟩ := hP f hf
      obtain ⟨b', t, ht, e2⟩ := regAt_exists_fraction hU hx (mem_locRing.1 hb)
      have hut := unitAt_fnOf_of_not_mem hU hx ht
      have htP : t ∉ P.asIdeal := (memP t).2 ⟨hut.ne_zero, hT _ hut.inv.regAt⟩
      have hb'0 : fnOf U (gen_mem hx) b' ≠ 0 := e2 ▸ mul_ne_zero hb0 hut.ne_zero
      have ht0 : (placeEquiv p E).ord (fnOf U (gen_mem hx) t) = 0 :=
        ord0 hut.ne_zero (hT _ hut.regAt) (hT _ hut.inv.regAt)
      have hob' : (placeEquiv p E).ord (fnOf U (gen_mem hx) b') = 0 := by
        rw [← e2, (placeEquiv p E).ord_mul hb0 hut.ne_zero, hord, ht0, add_zero]
      have hb'i : (fnOf U (gen_mem hx) b')⁻¹ ∈ E.ring :=
        ((placeEquiv p E).ord_nonneg_iff (inv_ne_zero hb'0)).1
          (by rw [Place.ord_inv, hob', neg_zero])
      have hb'P : b' ∉ P.asIdeal := (memP b').2 ⟨hb'0, hb'i⟩
      have hub' := unitAt_fnOf_of_not_mem hU z.2 (s := b') (by rw [hP']; exact hb'P)
      have hut' := unitAt_fnOf_of_not_mem hU z.2 (s := t) (by rw [hP']; exact htP)
      have hbz : UnitAt (z : X) b := by
        have eb : b = fnOf U (gen_mem hx) b' * (fnOf U (gen_mem hx) t)⁻¹ := by
          rw [← e2, mul_inv_cancel_right₀ hut.ne_zero]
        rw [eb]
        exact hub'.mul hut'.inv
      have haz : RegAt (z : X) a := regAt_of_specializes hzx (mem_locRing.1 ha)
      have ef : f = a * b⁻¹ := by rw [← e, mul_inv_cancel_right₀ hb0]
      rw [ef]
      exact haz.mul hbz.inv.regAt
    · obtain ⟨c, s, hs, e⟩ := regAt_exists_fraction hU z.2 hf
      have hs' : s ∉ P.asIdeal := by rw [← hP']; exact hs
      obtain ⟨hs0, hsi⟩ := (memP s).1 hs'
      have ef : f = fnOf U (gen_mem hx) c * (fnOf U (gen_mem hx) s)⁻¹ := by
        rw [← e, mul_inv_cancel_right₀ hs0]
      rw [ef]
      exact mul_mem (hT _ (regAt_fnOf hx _ c)) hsi
  · rintro ⟨z, hzx, hz⟩
    refine ⟨(contains_placeEquiv E x).2 (hz.through hzx), fun f hf => ?_⟩
    have hzU : z ∈ U := hzx.mem_open U.isOpen hx
    obtain ⟨c, s, hs, e⟩ := regAt_exists_fraction hU hzU ((hz f).1 hf)
    have hu := unitAt_fnOf_of_not_mem hU hzU hs
    exact ⟨_, mem_locRing.2 (regAt_fnOf hx _ c), _, mem_locRing.2 (regAt_fnOf hx _ s), hu.ne_zero,
      ord0 hu.ne_zero ((hz _).2 hu.regAt) ((hz _).2 hu.inv.regAt), e⟩

end GlobalTheory.FieldPair
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.lintegral_norm_sq_schwartz_pos_finite : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a d : ℕ}
    (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ SB (Matrix (Fin a) (Fin d) k) → Φ ≠ 0 →
    ∀ ν : @Measure (Matrix (Fin a) (Fin d) k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ 0 ∧ ∫⁻ Y, ‖Φ Y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
  first | exact @GlobalTheory.schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top | exact GlobalTheory.schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top | (intros; apply GlobalTheory.schwartzBruhat_matrix_lintegral_sq_ne_zero_ne_top <;> assumption)
end
