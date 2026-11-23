module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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

@[expose] public section

section

open GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem isAlgebraic_of_mul_eq {S K : Type} [CommRing S] [Field K] [Algebra S K] {f : K} (a b : S)
    (hb : b ≠ 0) (e : f * algebraMap S K b = algebraMap S K a) : IsAlgebraic S f := by
  refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h0 => hb ?_, ?_⟩
  · have h1 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 1) h0
    simpa only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_succ, sub_zero,
      Polynomial.coeff_zero, if_true] using h1
  · rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C, mul_comm, e,
      sub_self]

theorem exists_trBasis_mem_of_isLocModel {K : Type} [Field K] (c : ℂ →+* K) (R : Subring K)
    (n : ℕ) (hR : IsLocModel c R) (hx : ∃ x : Fin n → K, TrBasis c x) :
    ∃ xi : Fin n → R, TrBasis c (fun j => (xi j : K)) := by
  letI := c.toAlgebra
  obtain ⟨x, hx⟩ := hx
  haveI : Algebra.IsAlgebraic (Algebra.adjoin ℂ (R : Set K)) K := by
    refine ⟨fun f => ?_⟩
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hR.frac f
    exact isAlgebraic_of_mul_eq (⟨a, Algebra.subset_adjoin ha⟩ : Algebra.adjoin ℂ (R : Set K))
      ⟨b, Algebra.subset_adjoin hb⟩ (fun h => hb0 (congrArg Subtype.val h)) e
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := ℂ) (R : Set K)
  have h1 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) ht
  obtain ⟨e⟩ := Cardinal.eq.1 (h1.trans h2.symm)
  refine ⟨fun j => ⟨(e j : K), hts (e j).2⟩, ?_⟩
  show IsTranscendenceBasis ℂ fun j => ((e j : t) : K)
  exact (isTranscendenceBasis_equiv e).2 ht

end GlobalTheory.FieldPair
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair.Place

variable {k K : Type} [Field k] [Field K] {c : k →+* K} (E : Place c) {n : ℕ}

theorem ord_neg (f : K) : E.ord (-f) = E.ord f := by
  by_cases hf : f = 0
  · simp [hf]
  have h1 : ((-1 : E.ring) : K) = -1 := rfl
  have hu : IsUnit (-1 : E.ring) := isUnit_one.neg
  have h0 : E.ord (-1) = 0 := by rw [← h1]; exact E.ord_eq_zero hu
  rw [neg_eq_neg_one_mul, E.ord_mul (by norm_num) hf, h0, zero_add]

theorem isFormOrd_neg_iff (η : Forms c n) (a : ℤ) : E.IsFormOrd (-η) a ↔ E.IsFormOrd η a := by
  have key : ∀ η : Forms c n, E.IsFormOrd η a → E.IsFormOrd (-η) a := by
    rintro η ⟨ω, hω, f, rfl, hf⟩
    refine ⟨ω, hω, -f, ?_, ?_⟩
    · rw [Units.val_neg, neg_smul]
    · rw [Units.val_neg, E.ord_neg, hf]
  exact ⟨fun h => by simpa using key _ h, key η⟩

theorem formOrd_neg (η : Forms c n) : E.formOrd (-η) = E.formOrd η := by
  by_cases h : ∃ a, E.IsFormOrd η a
  · obtain ⟨a, ha⟩ := h
    rw [((E.isFormOrd_neg_iff η a).2 ha).formOrd_eq, ha.formOrd_eq]
  · have h' : ¬ ∃ a, E.IsFormOrd (-η) a := fun ⟨a, ha⟩ => h ⟨a, (E.isFormOrd_neg_iff η a).1 ha⟩
    rw [formOrd, formOrd, dite_eq_right h, dite_eq_right h']

theorem disc_neg (η : Forms c n) (φ : K →₀ ℚ) : E.disc (-η) φ = E.disc η φ := by
  change (E.formOrd (-η) : ℚ) - E.ordQ φ = (E.formOrd η : ℚ) - E.ordQ φ
  rw [E.formOrd_neg]

end GlobalTheory.FieldPair.Place

namespace GlobalTheory.FieldPair

theorem dForm_comp_perm {k K : Type} [Field k] [Field K] (c : k →+* K) {n : ℕ} (x : Fin n → K)
    (σ : Equiv.Perm (Fin n)) : dForm c (x ∘ σ) = Equiv.Perm.sign σ • dForm c x := by
  rw [dForm_eq, dForm_eq]
  exact (exteriorPower.ιMulti K n).map_perm (fun i => dFun c (x i)) σ

theorem disc_dForm_perm_neg {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ)
    (x : Fin n → K) (σ : Equiv.Perm (Fin n)) (E : Place c) (φ : K →₀ ℚ) :
    E.disc (dForm c (x ∘ σ)) φ = E.disc (dForm c x) φ ∧ E.disc (-dForm c x) φ = E.disc (dForm c x) φ := by
  refine ⟨?_, E.disc_neg _ φ⟩
  rw [dForm_comp_perm]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]
  · rw [h, Units.neg_smul, one_smul, E.disc_neg]

end GlobalTheory.FieldPair
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem exists_ordQ_eq_ord_div : ∀ {k K : Type} [Field k] [Field K] (c : k →+* K) (φ : K →₀ ℚ),
    φ 0 = 0 → ∃ (m : ℕ) (g : Kˣ), 0 < m ∧ ∀ E : Place c, E.ordQ φ = (E.ord (g : K) : ℚ) / m := by
  intro k K _ _ c φ
  induction φ using Finsupp.induction with
  | zero => intro _; exact ⟨1, 1, one_pos, fun E => by simp⟩
  | single_add a b f ha hb ih =>
    intro h0
    have hfa : f a = 0 := Finsupp.notMem_support_iff.mp ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Finsupp.add_apply, Finsupp.single_eq_same, hfa, add_zero] at h0
      exact hb h0
    have hf0 : f 0 = 0 := by
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm ha0), zero_add] at h0
      exact h0
    obtain ⟨m, g, hm, hg⟩ := ih hf0
    refine ⟨m * b.den, g ^ b.den * (Units.mk0 a ha0) ^ (b.num * m), ?_, fun E => ?_⟩
    · exact Nat.mul_pos hm b.pos
    · have hd : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.pos.ne'
      have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      rw [map_add (f := _), Place.ordQ_single, hg E, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_zpow_eq_zpow_val, E.ord_mul (pow_ne_zero _ g.ne_zero)
          (zpow_ne_zero _ (Units.mk0 a ha0).ne_zero), E.ord_pow, E.ord_zpow, Units.val_mk0]
      push_cast
      rw [← Rat.mul_den_eq_num b]
      field_simp
      ring

end GlobalTheory.FieldPair
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.ResidueTransport

variable {k M : Type} [Field k] [Field M] {c : k →+* M}

theorem ord_prod_zpow {ι : Type} (P : Place c) (s : Finset ι) (f : ι → M) (n : ι → ℤ)
    (hf : ∀ i ∈ s, f i ≠ 0) : P.ord (∏ i ∈ s, f i ^ n i) = ∑ i ∈ s, n i * P.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      P.ord_mul (zpow_ne_zero _ (hf a (Finset.mem_insert_self a s)))
        (Finset.prod_ne_zero_iff.2 fun i hi => zpow_ne_zero _ (hf i (Finset.mem_insert_of_mem hi))),
      P.ord_zpow, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ordQ_mapDomain {ι : Type} (P : Place c) (φ : ι →₀ ℚ) (f : ι → M) :
    P.ordQ (Finsupp.mapDomain f φ) = ∑ g ∈ φ.support, φ g * P.ord (f g) := by
  rw [Place.ordQ, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply, Finsupp.sum]
  simp [smul_eq_mul]

theorem ord_prod_eq_mul_ordQ {ι : Type} (P : Place c) (φ : ι →₀ ℚ) (f : ι → M) (N : ℕ)
    (m : ι → ℤ) (hm : ∀ g ∈ φ.support, (m g : ℚ) = N * φ g) (hf : ∀ g ∈ φ.support, f g ≠ 0) :
    (P.ord (∏ g ∈ φ.support, f g ^ m g) : ℚ) = N * P.ordQ (Finsupp.mapDomain f φ) := by
  rw [ord_prod_zpow P _ f m hf, ordQ_mapDomain, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [hm g hg]
  ring

theorem exists_common_den {ι : Type} (s : Finset ι) (φ : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ g ∈ s, ∃ m : ℤ, (m : ℚ) = N * φ g := by
  classical
  refine ⟨∏ g ∈ s, (φ g).den, Finset.prod_pos fun g _ => (φ g).den_pos, fun g hg =>
    ⟨(φ g).num * ∏ x ∈ s.erase g, ((φ x).den : ℤ), ?_⟩⟩
  rw [← Finset.mul_prod_erase s _ hg]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

end GlobalTheory.FieldPair.ResidueTransport

namespace GlobalTheory.FieldPair


open ResidueTransport in
theorem ordQ_mapDomain_residue_eq {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K)
    (Q : Subring L) (u : Q) (S E : Place cL) (ψ : S.ring →+* K) (F : Place cK)
    (hSQ : S.Contains Q) (hSu : S.ord (u : L) = 0) (hu0 : (u : L) ≠ 0)
    (hψ : Function.Surjective ψ)
    (hF : ∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a)
    (hFu : ∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1)
    (hG : ∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
      ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G)
    (φ : S.ring →₀ ℚ) (hsupp : ∀ g ∈ φ.support, ψ g ≠ 0)
    (hPφ : ∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
      P.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) = 0) :
    F.ordQ (Finsupp.mapDomain ψ φ) =
      E.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) := by

  have hker : RingHom.ker ψ = IsLocalRing.maximalIdeal S.ring :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hψ)
  have hunit : ∀ g ∈ φ.support, IsUnit g := fun g hg =>
    IsLocalRing.notMem_maximalIdeal.1 (by rw [← hker, RingHom.mem_ker]; exact hsupp g hg)
  choose! w hw using hunit
  obtain ⟨N, hN, hm⟩ := exists_common_den φ.support φ
  choose! m hm using hm
  have hg0 : ∀ g ∈ φ.support, ((g : S.ring) : L) ≠ 0 := fun g hg h =>
    hsupp g hg (by rw [show g = 0 from Subtype.ext h, map_zero])
  set G : L := ∏ g ∈ φ.support, ((g : S.ring) : L) ^ m g with hGdef
  set H : K := ∏ g ∈ φ.support, ψ g ^ m g with hHdef
  have hGord := fun P : Place cL => ord_prod_eq_mul_ordQ P φ (fun g : S.ring => (g : L)) N m hm hg0
  have hHord := ord_prod_eq_mul_ordQ F φ ψ N m hm hsupp
  have hG0 : G ≠ 0 := Finset.prod_ne_zero_iff.2 fun g hg => zpow_ne_zero _ (hg0 g hg)

  have hPG : ∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0 := by
    intro P hP hPE
    by_cases hPS : P.ring = S.ring
    · obtain rfl : P = S := Place.ext hPS
      rw [hGdef, ord_prod_zpow P _ _ m hg0]
      refine Finset.sum_eq_zero fun g hg => ?_
      rw [← hw g hg, P.ord_eq_zero (w g).isUnit, mul_zero]
    · have h := hGord P
      rw [hPφ P hP hPS hPE, mul_zero] at h
      exact_mod_cast h
  obtain ⟨q, hqU, hGq⟩ := hG G hG0 hPG
  set b := E.ord G with hb

  let uS : S.ring := ⟨u, hSQ _ u.2⟩
  have huS : IsUnit uS := by
    have h1 : (u : L) ∈ S.ring := hSQ _ u.2
    have h2 : (u : L)⁻¹ ∈ S.ring := by
      rw [← S.ord_nonneg_iff (inv_ne_zero hu0), S.ord_inv, hSu]; simp
    exact IsUnit.of_mul_eq_one (⟨_, h2⟩ : S.ring) (Subtype.ext (mul_inv_cancel₀ hu0))
  obtain ⟨r, hr⟩ := hqU.exists_right_inv
  let qS : S.ring := ⟨q, hSQ _ q.2⟩
  let rS : S.ring := ⟨r, hSQ _ r.2⟩
  have hqr : qS * rS = 1 := Subtype.ext (by change ((q * r : Q) : L) = 1; rw [hr]; rfl)
  let qU : S.ringˣ := (IsUnit.of_mul_eq_one rS hqr).unit
  let uU : S.ringˣ := huS.unit
  let W : S.ringˣ := ∏ g ∈ φ.support, w g ^ m g
  let e : S.ringˣ →* Lˣ := Units.map (S.ring.subtype : S.ring →* L)
  let f : S.ringˣ →* Kˣ := Units.map (ψ : S.ring →* K)
  have he : ∀ x, ((e x : Lˣ) : L) = ((x : S.ring) : L) := fun _ => rfl
  have hf : ∀ x, ((f x : Kˣ) : K) = ψ x := fun _ => rfl
  have heW : ((e W : Lˣ) : L) = G := by
    simp only [W, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, he]
    exact Finset.prod_congr rfl fun g hg => by rw [hw g hg]
  have hfW : ((f W : Kˣ) : K) = H := by
    simp only [W, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, hf]
    exact Finset.prod_congr rfl fun g hg => by rw [hw g hg]
  have hWeq : W = qU * uU ^ b := by
    have hinj : Function.Injective e := fun x y h =>
      Units.ext (Subtype.ext (by rw [← he, ← he, h]))
    apply hinj
    apply Units.ext
    rw [heW, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, he, he,
      IsUnit.unit_spec, IsUnit.unit_spec]
    exact hGq
  have hH : H = ψ qS * ψ uS ^ b := by
    rw [← hfW, hWeq, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, hf, hf,
      IsUnit.unit_spec, IsUnit.unit_spec]

  have hq0 : ψ qS * ψ rS = 1 := by rw [← map_mul, hqr, map_one]
  have hψq0 : ψ qS ≠ 0 := left_ne_zero_of_mul_eq_one hq0
  have hψu0 : ψ uS ≠ 0 := (huS.map ψ).ne_zero
  have hFq : F.ord (ψ qS) = 0 := by
    have h1 : 0 ≤ F.ord (ψ qS) := (F.ord_nonneg_iff hψq0).2 ((hF _).2 ⟨qS, q.2, rfl⟩)
    have hinv : (ψ qS)⁻¹ = ψ rS := inv_eq_of_mul_eq_one_right hq0
    have h2 : 0 ≤ F.ord (ψ qS)⁻¹ := (F.ord_nonneg_iff (inv_ne_zero hψq0)).2
      (by rw [hinv]; exact (hF _).2 ⟨rS, r.2, rfl⟩)
    rw [F.ord_inv] at h2
    omega
  have hFH : F.ord H = b := by
    rw [hH, F.ord_mul hψq0 (zpow_ne_zero _ hψu0), F.ord_zpow, hFq, hFu uS rfl]
    ring
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hEG := hGord E
  rw [← hb, ← hFH, hHord] at hEG
  exact mul_left_cancel₀ hNq hEG

end GlobalTheory.FieldPair
end
end

section

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.GraphLocal

open GlobalTheory.FieldPair

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

def placeAlg (E : Place (algebraMap ℂ K)) : Subalgebra ℂ K :=
  { E.ring.toSubring with algebraMap_mem' := E.const_mem }

theorem mem_placeAlg {E : Place (algebraMap ℂ K)} {e : K} : e ∈ placeAlg E ↔ e ∈ E.ring :=
  Iff.rfl


variable (κ') in
def tensMap (A : Subalgebra ℂ K) : A ⊗[ℂ] κ' →ₐ[ℂ] K ⊗[ℂ] κ' :=
  Algebra.TensorProduct.map A.val (AlgHom.id ℂ κ')

theorem tensMap_injective (A : Subalgebra ℂ K) : Function.Injective (tensMap κ' A) := by
  have e : ⇑(tensMap κ' A) = ⇑(LinearMap.rTensor κ' A.val.toLinearMap) := by
    funext w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  rw [e]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective

def tens (A : Subalgebra ℂ K) : Subalgebra ℂ (K ⊗[ℂ] κ') := (tensMap κ' A).range

def tensEquiv (A : Subalgebra ℂ K) : A ⊗[ℂ] κ' ≃ₐ[ℂ] tens (κ' := κ') A :=
  AlgEquiv.ofInjective _ (tensMap_injective A)

@[simp] theorem coe_tensEquiv (A : Subalgebra ℂ K) (w : A ⊗[ℂ] κ') :
    (tensEquiv A w : K ⊗[ℂ] κ') = tensMap κ' A w := rfl

theorem tmul_mem {A : Subalgebra ℂ K} {e : K} (he : e ∈ A) (b : κ') :
    e ⊗ₜ[ℂ] b ∈ tens (κ' := κ') A :=
  ⟨⟨e, he⟩ ⊗ₜ b, rfl⟩

variable {κ : Type} [Field κ] [Algebra ℂ κ]

def graphIdeal (E : Place (algebraMap ℂ K)) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') :
    Ideal (tens (κ' := κ') (placeAlg E)) :=
  Ideal.span ({b | ∃ e : K, 0 < E.ord e ∧ (b : K ⊗[ℂ] κ') = e ⊗ₜ 1} ∪
    {b | ∃ a : R, (b : K ⊗[ℂ] κ') = (a : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π a)})

def gens (E : Place (algebraMap ℂ K)) (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ')
    (hR : E.Contains R) (t : E.ring) {k : ℕ} (z : Fin k → R) :
    Fin (k + 1) → tens (κ' := κ') (placeAlg E) :=
  Fin.cons ⟨(t : K) ⊗ₜ 1, tmul_mem t.2 1⟩ fun i =>
    ⟨(z i : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π (z i)),
      sub_mem (tmul_mem (hR _ (z i).2) 1) (tmul_mem (one_mem (placeAlg E)) _)⟩

variable {L : Type} [Field L] [Algebra (K ⊗[ℂ] κ') L]

theorem one_notMem {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [h𝔭 : 𝔭.IsPrime] :
    (1 : tens (κ' := κ') A) ∉ 𝔭 :=
  (Ideal.ne_top_iff_one 𝔭).1 h𝔭.ne_top

def locAt {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime] : Subring L where
  carrier := {x | ∃ a s : tens (κ' := κ') A, s ∉ 𝔭 ∧
    x * algebraMap (K ⊗[ℂ] κ') L s = algebraMap (K ⊗[ℂ] κ') L a}
  mul_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨a', s', hs', hy⟩
    refine ⟨a * a', s * s', fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs hs', ?_⟩
    simp only [Subalgebra.coe_mul, map_mul]
    rw [← hx, ← hy]
    ring
  one_mem' := ⟨1, 1, one_notMem 𝔭, by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨a', s', hs', hy⟩
    refine ⟨a * s' + a' * s, s * s', fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs hs', ?_⟩
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, map_mul, map_add (f := _)]
    rw [← hx, ← hy]
    ring
  zero_mem' := ⟨0, 1, one_notMem 𝔭, by simp⟩
  neg_mem' := by
    rintro x ⟨a, s, hs, hx⟩
    refine ⟨-a, s, hs, ?_⟩
    simp only [Subalgebra.coe_neg, map_neg]
    rw [← hx]
    ring

def toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime] :
    tens (κ' := κ') A →+* locAt (L := L) 𝔭 where
  toFun b := ⟨algebraMap (K ⊗[ℂ] κ') L b, b, 1, one_notMem 𝔭, by simp⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

@[simp] theorem coe_toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (b : tens (κ' := κ') A) : (toQ (L := L) 𝔭 b : L) = algebraMap (K ⊗[ℂ] κ') L b := rfl

theorem exists_mul_toQ {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
    (x : locAt (L := L) 𝔭) : ∃ a s : tens (κ' := κ') A, s ∉ 𝔭 ∧ x * toQ 𝔭 s = toQ 𝔭 a := by
  obtain ⟨x, a, s, hs, hx⟩ := x
  exact ⟨a, s, hs, Subtype.ext hx⟩

section Inj

variable {A : Subalgebra ℂ K} (𝔭 : Ideal (tens (κ' := κ') A)) [𝔭.IsPrime]
  (hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L))
include hinj

theorem algebraMap_ne_zero {b : tens (κ' := κ') A} (hb : b ≠ 0) :
    algebraMap (K ⊗[ℂ] κ') L b ≠ 0 := fun h =>
  hb (Subtype.ext (hinj (h.trans (map_zero _).symm)))

theorem isUnit_toQ {b : tens (κ' := κ') A} (hb : b ∉ 𝔭) : IsUnit (toQ (L := L) 𝔭 b) := by
  have hb0 : algebraMap (K ⊗[ℂ] κ') L b ≠ 0 :=
    algebraMap_ne_zero hinj fun h => hb (h ▸ 𝔭.zero_mem)
  refine IsUnit.of_mul_eq_one (b := ⟨(algebraMap (K ⊗[ℂ] κ') L b)⁻¹, 1, b, hb, by simp [hb0]⟩)
    (Subtype.ext ?_)
  simp [hb0]

theorem isLocalRing_locAt : IsLocalRing (locAt (L := L) 𝔭) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  obtain ⟨a, s, hs, hx⟩ := exists_mul_toQ 𝔭 x
  by_cases ha : a ∈ 𝔭
  · right
    have hsa : s - a ∉ 𝔭 := fun h => hs (by simpa using add_mem h ha)
    refine isUnit_of_mul_isUnit_left (y := toQ 𝔭 s) ?_
    rw [sub_mul, one_mul, hx, ← map_sub]
    exact isUnit_toQ 𝔭 hinj hsa
  · left
    refine isUnit_of_mul_isUnit_left (y := toQ 𝔭 s) ?_
    rw [hx]
    exact isUnit_toQ 𝔭 hinj ha

theorem isUnit_toQ_iff {b : tens (κ' := κ') A} : IsUnit (toQ (L := L) 𝔭 b) ↔ b ∉ 𝔭 := by
  refine ⟨fun h hb => ?_, isUnit_toQ 𝔭 hinj⟩
  obtain ⟨y, hy⟩ := h.exists_right_inv
  obtain ⟨a, s, hs, e⟩ := exists_mul_toQ 𝔭 y
  have e2 : toQ (L := L) 𝔭 (b * a) = toQ 𝔭 s := by
    rw [map_mul, ← e, ← mul_assoc, hy, one_mul]
  have e3 : b * a = s := Subtype.ext (hinj (congrArg Subtype.val e2))
  exact hs (e3 ▸ 𝔭.mul_mem_right a hb)

theorem toQ_mem_maximalIdeal_iff [IsLocalRing (locAt (L := L) 𝔭)] {b : tens (κ' := κ') A} :
    toQ (L := L) 𝔭 b ∈ IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) ↔ b ∈ 𝔭 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_toQ_iff 𝔭 hinj, not_not]

theorem map_le_maximalIdeal [IsLocalRing (locAt (L := L) 𝔭)] :
    𝔭.map (toQ (L := L) 𝔭) ≤ IsLocalRing.maximalIdeal (locAt (L := L) 𝔭) :=
  Ideal.map_le_iff_le_comap.2 fun _ hb => (toQ_mem_maximalIdeal_iff 𝔭 hinj).2 hb

end Inj

end GlobalTheory.GraphLocal
end
end
