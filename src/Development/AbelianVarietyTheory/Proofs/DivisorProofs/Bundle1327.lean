module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.LocModelTwo

variable {L : Type} [Field L] {cL : ℂ →+* L}

def primeOf (P : Place cL) (Q : Subring L) (hP : P.Contains Q) : Ideal Q :=
  Ideal.comap ((Q.subtype).codRestrict P.ring fun x => hP x x.2) (IsLocalRing.maximalIdeal P.ring)

instance (P : Place cL) (Q : Subring L) (hP : P.Contains Q) : (primeOf P Q hP).IsPrime :=
  Ideal.comap_isPrime _ _

theorem mem_primeOf {P : Place cL} {Q : Subring L} {hP : P.Contains Q} {x : Q} :
    x ∈ primeOf P Q hP ↔ ¬ IsUnit (⟨x, hP x x.2⟩ : P.ring) := Iff.rfl

theorem isUnit_of_ord_eq_zero (P : Place cL) {y : P.ring} (hy : (y : L) ≠ 0) (h : P.ord y = 0) :
    IsUnit y := by
  have hi : (y : L)⁻¹ ∈ P.ring :=
    (P.ord_nonneg_iff (inv_ne_zero hy)).1 (by rw [P.ord_inv, h]; rfl)
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ hy)⟩

theorem ord_zero (P : Place cL) : P.ord 0 = 0 := by simp [Place.ord]

theorem pos_ord_iff {P : Place cL} {Q : Subring L} (hP : P.Contains Q) {x : Q} (hx : (x : L) ≠ 0) :
    0 < P.ord x ↔ x ∈ primeOf P Q hP := by
  rw [mem_primeOf]
  constructor
  · intro h hu
    have := P.ord_eq_zero hu
    simp only at this
    omega
  · intro h
    have h0 : 0 ≤ P.ord x := (P.ord_nonneg_iff hx).2 (hP x x.2)
    refine lt_of_le_of_ne h0 fun e => h ?_
    exact isUnit_of_ord_eq_zero P (y := ⟨x, hP x x.2⟩) hx e.symm

theorem ring_le {P P' : Place cL} {Q : Subring L} (hP : P.IsPrimeOf Q) (hP' : P'.Contains Q)
    (h : primeOf P' Q hP' ≤ primeOf P Q hP.1) : P.ring ≤ P'.ring := by
  intro f hf
  obtain ⟨a, ha, b, hb, hb0, hob, e⟩ := hP.2 f hf
  have hbP : (⟨b, hb⟩ : Q) ∉ primeOf P Q hP.1 := by
    rw [mem_primeOf, not_not]
    exact isUnit_of_ord_eq_zero P (y := ⟨b, hP.1 b hb⟩) hb0 hob
  have hbP' : (⟨b, hb⟩ : Q) ∉ primeOf P' Q hP' := fun h' => hbP (h h')
  rw [mem_primeOf, not_not] at hbP'
  obtain ⟨v, hv⟩ := hbP'.exists_right_inv
  have hv' : b * (v : L) = 1 := congrArg Subtype.val hv
  have : f = a * v := by
    calc f = f * (b * v) := by rw [hv', mul_one]
      _ = a * v := by rw [← mul_assoc, e]
  rw [this]
  exact mul_mem (hP' a ha) v.2

theorem ringKrullDim_eq_one {P : Place cL} {Q : Subring L} [IsLocalRing Q] (hP : P.IsPrimeOf Q)
    (h : IsLocalRing.maximalIdeal Q ≤ primeOf P Q hP.1) : ringKrullDim Q = 1 := by
  have hle : P.ring.toSubring ≤ Q := by
    intro f hf
    obtain ⟨a, ha, b, hb, hb0, hob, e⟩ := hP.2 f hf
    have hbP : (⟨b, hb⟩ : Q) ∉ primeOf P Q hP.1 := by
      rw [mem_primeOf, not_not]
      exact isUnit_of_ord_eq_zero P (y := ⟨b, hP.1 b hb⟩) hb0 hob
    have hbQ : IsUnit (⟨b, hb⟩ : Q) := by
      by_contra hn
      exact hbP (h ((IsLocalRing.mem_maximalIdeal _).2 hn))
    obtain ⟨v, hv⟩ := hbQ.exists_right_inv
    have hv' : b * (v : L) = 1 := congrArg Subtype.val hv
    have : f = a * v := by
      calc f = f * (b * v) := by rw [hv', mul_one]
        _ = a * v := by rw [← mul_assoc, e]
    rw [this]
    exact Q.mul_mem ha v.2
  have hQ : Q = P.ring.toSubring := le_antisymm (fun x hx => hP.1 x hx) hle
  exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.subringCongr hQ)).trans
    (IsDiscreteValuationRing.ringKrullDim_eq_one P.ring)

theorem eq_span_of_mem_of_not_mem {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {t u : R} (hm : Ideal.span {t, u} = IsLocalRing.maximalIdeal R) (p : Ideal R) [p.IsPrime]
    (ht : t ∈ p) (hu : u ∉ p) : p = Ideal.span {t} := by
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem p).2 ht)
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal R)
    (IsNoetherian.noetherian p) (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_
  intro y hy
  have hym : y ∈ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) hy
  rw [← hm, Ideal.mem_span_pair] at hym
  obtain ⟨c, d, e⟩ := hym
  have hdu : d * u ∈ p := by
    have : d * u = y - c * t := by rw [← e]; ring
    rw [this]
    exact p.sub_mem hy (p.mul_mem_left c ht)
  have hd : d ∈ p := ((Ideal.IsPrime.mem_or_mem ‹_› hdu).resolve_right hu)
  rw [← e]
  refine Submodule.add_mem_sup (Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self t)) ?_
  have huM : u ∈ IsLocalRing.maximalIdeal R := hm ▸ Ideal.subset_span (by simp)
  have := Submodule.smul_mem_smul huM hd
  rw [mul_comm]
  exact this

end GlobalTheory.FieldPair.LocModelTwo

namespace GlobalTheory.FieldPair.LocModelTwo

theorem ring_eq_and_ord_eq_zero : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  (∀ P P' : Place cL, P.IsPrimeOf Q → P'.IsPrimeOf Q → 0 < P.ord (t : L) → 0 < P'.ord (t : L) →
    P.ring = P'.ring) ∧
  (∀ P : Place cL, P.IsPrimeOf Q → P.ord (t : L) = 0 ∨ P.ord (u : L) = 0) := by
  intro L _ cL Q hQ t u hm hd
  letI := hQ.isLocalRing
  haveI : IsNoetherianRing Q := by
    letI := (cL.codRestrict Q hQ.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing ℂ Q
  have hA : ∀ P : Place cL, ∀ hP : P.IsPrimeOf Q,
      ¬ (t ∈ primeOf P Q hP.1 ∧ u ∈ primeOf P Q hP.1) := by
    rintro P hP ⟨ht, hu⟩
    have h1 := ringKrullDim_eq_one hP (by
      rw [← hm]
      exact Ideal.span_le.2 (Set.insert_subset_iff.2 ⟨ht, Set.singleton_subset_iff.2 hu⟩))
    rw [hd] at h1
    exact absurd h1 (by decide)
  have hB : ∀ P : Place cL, ∀ hP : P.IsPrimeOf Q, 0 < P.ord (t : L) →
      primeOf P Q hP.1 = Ideal.span {t} := by
    intro P hP hpos
    have ht0 : (t : L) ≠ 0 := fun e => by rw [e, ord_zero] at hpos; exact lt_irrefl _ hpos
    have ht : t ∈ primeOf P Q hP.1 := (pos_ord_iff hP.1 ht0).1 hpos
    exact eq_span_of_mem_of_not_mem hm _ ht fun hu => hA P hP ⟨ht, hu⟩
  refine ⟨fun P P' hP hP' hPt hP't => ?_, fun P hP => ?_⟩
  · have e := (hB P hP hPt).trans (hB P' hP' hP't).symm
    exact le_antisymm (ring_le hP hP'.1 e.ge) (ring_le hP' hP.1 e.le)
  · by_contra h
    push_neg at h
    have hpos : ∀ x : Q, P.ord (x : L) ≠ 0 → x ∈ primeOf P Q hP.1 := by
      intro x hx
      have hx0 : (x : L) ≠ 0 := fun e => hx (by rw [e, ord_zero])
      exact (pos_ord_iff hP.1 hx0).1
        (lt_of_le_of_ne ((P.ord_nonneg_iff hx0).2 (hP.1 x x.2)) (Ne.symm hx))
    exact hA P hP ⟨hpos t h.1, hpos u h.2⟩

end GlobalTheory.FieldPair.LocModelTwo
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FieldPair

theorem residuePlace_of_locModel : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q) (t u : Q),
  Ideal.span {t, u} = (letI := hQ.isLocalRing; IsLocalRing.maximalIdeal Q) → ringKrullDim Q = 2 →
  ∀ (S : Place cL) (ψ : S.ring →+* K), S.IsPrimeOf Q → S.ord (t : L) = 1 →
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∃ F : Place cK, (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) ∧
    ∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1 := by
  intro L K _ _ cL cK Q hQ t u hm hdim S ψ hS ht hψ hc
  letI := hQ.isLocalRing
  have hSQ : ∀ q : Q, (q : L) ∈ S.ring := fun q => hS.1 q q.2
  let φ₀ : Q →+* S.ring := Q.subtype.codRestrict S.ring hSQ
  let φ : Q →+* K := ψ.comp φ₀
  have hker : ∀ s : S.ring, ψ s = 0 ↔ ¬ IsUnit s := by
    intro s
    have hmax := RingHom.ker_isMaximal_of_surjective ψ hψ
    have h := IsLocalRing.eq_maximalIdeal hmax
    rw [← RingHom.mem_ker, h, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hunit : ∀ s : S.ring, (s : L) ≠ 0 → S.ord s = 0 → IsUnit s := by
    intro s hs h0
    have hinv : (s : L)⁻¹ ∈ S.ring :=
      (S.ord_nonneg_iff (inv_ne_zero hs)).1 (by rw [S.ord_inv, h0, neg_zero])
    exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : S.ring) (Subtype.ext (mul_inv_cancel₀ hs))
  have hφt : φ t = 0 := by
    show ψ (φ₀ t) = 0
    rw [hker]
    intro hu
    have h := S.ord_eq_zero hu
    change S.ord (t : L) = 0 at h
    rw [ht] at h
    exact one_ne_zero h
  have hφu : φ u ≠ 0 := by
    intro hu0
    have hsp : Ideal.span {t, u} ≤ RingHom.ker φ := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · exact hφt
      · exact hu0
    have hle : ∀ f ∈ S.ring, f ∈ Q := by
      intro f hf
      obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hS.2 f hf
      have hbu : IsUnit (⟨b, hb⟩ : Q) := by
        by_contra hnu
        have h1 : φ ⟨b, hb⟩ = 0 := hsp (hm ▸ (IsLocalRing.mem_maximalIdeal _).2 hnu)
        exact (hker _).1 h1 (hunit (φ₀ ⟨b, hb⟩) hb0 hbo)
      obtain ⟨v, hv⟩ := hbu.exists_right_inv
      have hv' : b * (v : L) = 1 := congrArg Subtype.val hv
      have hf' : f = a * (v : L) := by
        calc f = f * (b * v) := by rw [hv', mul_one]
          _ = a * v := by rw [← mul_assoc, e]
      rw [hf']
      exact Q.mul_mem ha v.2
    let e : Q ≃+* S.ring := RingEquiv.ofBijective φ₀
      ⟨fun x y h => Subtype.ext (congrArg (fun s : S.ring => (s : L)) h), fun s => ⟨⟨s, hle s s.2⟩, rfl⟩⟩
    have h := ringKrullDim_eq_of_ringEquiv e
    rw [hdim, IsDiscreteValuationRing.ringKrullDim_eq_one] at h
    norm_num at h
  have hmemR : ∀ a : K, a ∈ φ.range ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a := by
    intro a
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨φ₀ q, q.2, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  have hfrac : ∀ a : K, ∃ x y : Q, φ y ≠ 0 ∧ a * φ y = φ x := by
    intro a
    obtain ⟨s, rfl⟩ := hψ a
    obtain ⟨x, hx, y, hy, hy0, hyo, e⟩ := hS.2 s s.2
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => (hker _).1 h (hunit (φ₀ ⟨y, hy⟩) hy0 hyo), ?_⟩
    show ψ s * ψ (φ₀ ⟨y, hy⟩) = ψ (φ₀ ⟨x, hx⟩)
    rw [← map_mul]
    exact congrArg ψ (Subtype.ext e)
  haveI : IsNoetherianRing Q := by
    letI := (cL.codRestrict Q hQ.const_mem).toAlgebra
    haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
    exact Algebra.EssFiniteType.isNoetherianRing ℂ Q
  let R := φ.range
  let φR : Q →+* R := φ.rangeRestrict
  haveI : IsNoetherianRing R := isNoetherianRing_range φ
  haveI : IsLocalRing R := IsLocalRing.of_surjective' φR φ.rangeRestrict_surjective
  have hmR : IsLocalRing.maximalIdeal R = Ideal.span {φR u} := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective φR φ.rangeRestrict_surjective, ← hm,
      Ideal.map_span, Set.image_pair]
    have h0 : φR t = 0 := Subtype.ext hφt
    rw [h0, Ideal.span_insert_zero]
  have hu0R : φR u ≠ 0 := fun h => hφu (congrArg Subtype.val h)
  have hnf : ¬ IsField R := by
    intro hf
    obtain ⟨w, hw⟩ := hf.mul_inv_cancel hu0R
    have hmem : φR u ∈ IsLocalRing.maximalIdeal R := hmR ▸ Ideal.subset_span rfl
    exact (IsLocalRing.mem_maximalIdeal _).1 hmem (IsUnit.of_mul_eq_one w hw)
  haveI hdvr : IsDiscreteValuationRing R :=
    ((IsDiscreteValuationRing.TFAE R hnf).out 1 5).2
      (show (IsLocalRing.maximalIdeal R).IsPrincipal from ⟨_, hmR⟩)
  let V : ValuationSubring K :=
    { R with
      mem_or_inv_mem' := by
        intro a
        obtain ⟨x, y, hy, e⟩ := hfrac a
        obtain ⟨c, hc | hc⟩ := ValuationRing.cond (φR x) (φR y)
        · right
          have hc' : φ x * (c : K) = φ y := congrArg Subtype.val hc
          have h1 : a * c = 1 := by
            refine mul_right_cancel₀ hy ?_
            linear_combination (c : K) * e + hc'
          rw [inv_eq_of_mul_eq_one_right h1]
          exact c.2
        · left
          have hc' : φ y * (c : K) = φ x := congrArg Subtype.val hc
          have h1 : a = c := by
            refine mul_right_cancel₀ hy ?_
            linear_combination e - hc'
          rw [h1]
          exact c.2 }
  have hconst : ∀ a, cK a ∈ V := fun a => (hmemR (cK a)).2 ⟨S.const a, hQ.const_mem a, hc a⟩
  have hφV : ∀ q : Q, φ q ∈ V := fun q => ⟨q, rfl⟩
  let φV : Q →+* V := φ.codRestrict V hφV
  have hφVs : Function.Surjective φV := by
    rintro ⟨v, q, rfl⟩
    exact ⟨q, rfl⟩
  haveI hdvrV : IsDiscreteValuationRing V := hdvr
  have hcomp : cK.codRestrict V hconst = φV.comp (cL.codRestrict Q hQ.const_mem) :=
    RingHom.ext fun a => Subtype.ext (hc a).symm
  let F : Place cK :=
    ⟨V, hconst, hdvrV, hcomp ▸ hQ.essFiniteType.comp (RingHom.FiniteType.of_surjective φV hφVs).essFiniteType⟩
  refine ⟨F, hmemR, fun us hus => ?_⟩
  have h1 : ψ us = ((φV u : V) : K) := by
    show ψ us = ψ (φ₀ u)
    exact congrArg ψ (Subtype.ext hus)
  have hmV : IsLocalRing.maximalIdeal V = Ideal.span {φV u} := hmR
  have hirr : Irreducible (φV u) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmV
  rw [h1]
  exact F.ord_irreducible hirr

end GlobalTheory.FieldPair
end
end

section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem specializes_of_locRing_le (X : Scheme.{0}) [IsIntegral X] [X.IsSeparated] (x z : X)
    (h : locRing x ≤ locRing z) : z ⤳ x := by
  have hgz : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  have hgx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hinjz : Function.Injective (algebraMap (X.presheaf.stalk z) X.functionField) :=
    IsFractionRing.injective _ _
  let ez : X.presheaf.stalk z ≃+* locRing z := RingEquiv.ofBijective
    (algebraMap (X.presheaf.stalk z) X.functionField).rangeRestrict
    ⟨fun _ _ e => hinjz (congrArg Subtype.val e), RingHom.rangeRestrict_surjective _⟩
  let φ : X.presheaf.stalk x →+* X.presheaf.stalk z :=
    ez.symm.toRingHom.comp
      ((Subring.inclusion h).comp (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict)
  have hφ (a : X.presheaf.stalk x) :
      algebraMap (X.presheaf.stalk z) X.functionField (φ a) =
        algebraMap (X.presheaf.stalk x) X.functionField a := by
    have e1 : ez (φ a) = Subring.inclusion h
        ((algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict a) := by
      exact ez.apply_symm_apply _
    exact congrArg Subtype.val e1
  have key : X.presheaf.stalkSpecializes hgx =
      CommRingCat.ofHom φ ≫ X.presheaf.stalkSpecializes hgz := by
    ext a
    exact (hφ a).symm
  let ι := Spec.map (X.presheaf.stalkSpecializes hgz)
  have hdom : IsDominant ι := by
    rw [isDominant_iff]
    show DenseRange (PrimeSpectrum.comap (X.presheaf.stalkSpecializes hgz).hom)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot (X.presheaf.stalkSpecializes hgz).hom).1 hinjz]
    exact bot_le
  let g := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x
  have hfg : X.fromSpecStalk z = g := by
    refine ext_of_isDominant_of_isSeparated (Limits.terminal.from X)
      (Limits.terminal.hom_ext _ _) ι ?_
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgz]
    simp only [g, ι, ← Category.assoc, ← Spec.map_comp, ← key,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgx]
  have hz : z = g (IsLocalRing.closedPoint (X.presheaf.stalk z)) := by
    rw [← hfg, Scheme.fromSpecStalk_closedPoint]
  have hr : g (IsLocalRing.closedPoint (X.presheaf.stalk z)) ∈ Set.range (X.fromSpecStalk x) :=
    ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rw [Scheme.range_fromSpecStalk] at hr
  rw [hz]
  exact hr

end GlobalTheory
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

theorem GlobalTheory.trBasis_card_eq_of_algEquiv : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ] (e : K ≃ₐ[ℂ] κ)
  (n k : ℕ) (x : Fin n → K) (z : Fin k → κ),
  TrBasis (algebraMap ℂ K) x → TrBasis (algebraMap ℂ κ) z → n = k := by
  intro K κ _ _ _ _ e n k x z hx hz
  have eK : (algebraMap ℂ K).toAlgebra = (inferInstance : Algebra ℂ K) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  have eκ : (algebraMap ℂ κ).toAlgebra = (inferInstance : Algebra ℂ κ) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  unfold TrBasis at hx hz
  rw [eK] at hx
  rw [eκ] at hz
  have h1 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hz
  rw [Cardinal.mk_fin, e.trdeg_eq] at h1
  rw [Cardinal.mk_fin, ← h1] at h2
  exact_mod_cast h2.symm
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

theorem locModel_fracField_algEquiv : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ]
  (R : Subring K) (π : R →+* κ), IsLocModel (algebraMap ℂ K) R →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) → Function.Injective π →
  ∃ e : K ≃ₐ[ℂ] κ, ∀ r : R, e r = π r := by
  intro K κ _ _ _ _ R π hR hc hsurj hinj
  haveI : FaithfulSMul R K :=
    (faithfulSMul_iff_algebraMap_injective R K).mpr Subtype.val_injective
  haveI : IsFractionRing R K := IsFractionRing.of_field R K (fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hR.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change z = a / b
    rw [eq_div_iff hb0, e])
  let φ : K →+* κ := IsFractionRing.lift hinj
  have hφ : ∀ r : R, φ (algebraMap R K r) = π r := fun r => IsFractionRing.lift_algebraMap hinj r
  have hφc : ∀ a : ℂ, φ (algebraMap ℂ K a) = algebraMap ℂ κ a := by
    intro a
    have := hφ ⟨algebraMap ℂ K a, hR.const_mem a⟩
    rw [← hc a (hR.const_mem a)]
    exact this
  let ψ : K →ₐ[ℂ] κ := { φ with commutes' := hφc }
  have hbij : Function.Bijective ψ := by
    refine ⟨ψ.toRingHom.injective, fun f => ?_⟩
    obtain ⟨a, b, hb, e⟩ := hsurj f
    have hb' : (b : K) ≠ 0 := by
      intro h
      apply hb
      have : b = 0 := Subtype.ext h
      rw [this, map_zero]
    refine ⟨(a : K) / b, ?_⟩
    change φ ((a : K) / b) = f
    rw [map_div₀]
    have ha := hφ a
    have hb2 := hφ b
    change φ (a : K) = π a at ha
    change φ (b : K) = π b at hb2
    rw [ha, hb2, div_eq_iff hb, e]
  refine ⟨AlgEquiv.ofBijective ψ hbij, fun r => ?_⟩
  exact hφ r

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'], ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ', boxFun φ₁ φ₂ ∈ schA F (κ ⊕ κ') := by
  first | exact @GlobalTheory.SchwartzBox.boxFun_mem_schA | exact GlobalTheory.SchwartzBox.boxFun_mem_schA | (intros; apply GlobalTheory.SchwartzBox.boxFun_mem_schA <;> assumption)
end
