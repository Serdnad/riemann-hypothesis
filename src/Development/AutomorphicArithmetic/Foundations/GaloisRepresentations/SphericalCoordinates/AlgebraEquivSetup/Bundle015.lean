module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

private def sg {E : Type} [Field E] [NumberField E] (U : Set (Plc E)) (N : ℕ) : AddSubgroup (Af E) where
  carrier := {x | ∀ w ∈ U, Valued.v (pLoc E w x) ≤ Valued.v (N : w.adicCompletion E)}
  zero_mem' := fun w _ => by simp
  add_mem' := fun {a b} ha hb w hw => by
    rw [map_add (f := _)]
    exact (Valuation.map_add _ _ _).trans (max_le (ha w hw) (hb w hw))
  neg_mem' := fun {a} ha w hw => by
    rw [map_neg, Valuation.map_neg]
    exact ha w hw

private theorem isOpen_sg_univ {E : Type} [Field E] [NumberField E] {N : ℕ} (hN : 0 < N) :
    IsOpen (sg (E := E) Set.univ N : Set (Af E)) := by
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨c, hc⟩ : ∃ c : Af E, c * (N : Af E) = 1 := by
    refine ⟨algebraMap E (Af E) ((N : E)⁻¹), ?_⟩
    have h : algebraMap E (Af E) ((N : E)⁻¹) * algebraMap E (Af E) (N : E) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hNE, map_one]
    simpa using h
  have hv : ∀ w : Plc E, Valued.v (pLoc E w c) * Valued.v (N : w.adicCompletion E) = 1 := fun w => by
    have h := congrArg (pLoc E w) hc
    rw [map_mul, map_natCast, map_one] at h
    rw [← map_mul, h, map_one]
  have h1 : IsOpen {f : Af E | ∀ w : Plc E, (f w : w.adicCompletion E) ∈
      ((Valued.v.integer : Subring (w.adicCompletion E)) : Set (w.adicCompletion E))} :=
    RestrictedProduct.isOpen_forall_mem (fun w => Valued.isOpen_integer _)
  have h2 : Continuous (fun x : Af E => c * x) := continuous_const.mul continuous_id
  have h3 := h1.preimage h2
  convert h3 using 1
  ext x
  have hm : ∀ w : Plc E, (((c * x : Af E) w : w.adicCompletion E) ∈
      ((Valued.v.integer : Subring (w.adicCompletion E)) : Set (w.adicCompletion E))) ↔
      Valued.v (pLoc E w c) * Valued.v (pLoc E w x) ≤ 1 := fun w => by
    rw [← map_mul, ← map_mul]
    exact Valuation.mem_integer_iff _ _
  constructor
  · intro hx w
    refine (hm w).2 ?_
    calc Valued.v (pLoc E w c) * Valued.v (pLoc E w x)
        ≤ Valued.v (pLoc E w c) * Valued.v (N : w.adicCompletion E) := by
          gcongr
          exact hx w trivial
      _ = 1 := hv w
  · intro hx w _
    have h := (hm w).1 (hx w)
    calc Valued.v (pLoc E w x)
        = Valued.v (pLoc E w c) * Valued.v (pLoc E w x) * Valued.v (N : w.adicCompletion E) := by
          rw [mul_right_comm, hv, one_mul]
      _ ≤ 1 * Valued.v (N : w.adicCompletion E) := by gcongr
      _ = _ := one_mul _

private theorem principalCongruence_map_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (N : ℕ) (w : Plc E)
    (M : GL (Fin n) (Af E)) :
    Cong1 N w (GeneralLinearGroup.map (pLoc E w) M) ↔
      ∀ i k, Valued.v (pLoc E w ((M.val - 1) i k)) ≤ Valued.v (N : w.adicCompletion E) := by
  have h : ∀ i k, ((GeneralLinearGroup.map (pLoc E w) M).val - 1) i k = pLoc E w ((M.val - 1) i k) := by
    intro i k
    by_cases hik : i = k <;> simp [Matrix.sub_apply, Matrix.one_apply, hik]
  simp only [Cong1, h]

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pKNOpen :
    KNIff → KNOpen := by
  intro hI E _ _ _ A n p _ S T N hN
  have hO : IsOpen ((sg {w : Plc E | (p : 𝓞 E) ∉ w.asIdeal} N : AddSubgroup (Af E)) : Set (Af E)) :=
    AddSubgroup.isOpen_mono (H₁ := sg Set.univ N) (fun x hx w _ => hx w trivial) (isOpen_sg_univ hN)
  have hm : Continuous (fun g : GUf E n => mat g) := continuous_fst.comp continuous_subtype_val
  have hc1 : Continuous (fun g : GUf E n => (T.a * mat g * T.a⁻¹ : GL (Fin n) (Af E)).val) :=
    Units.continuous_val.comp ((continuous_const.mul hm).mul continuous_const)
  have hc2 : Continuous (fun g : GUf E n => (T.a * mat g⁻¹ * T.a⁻¹ : GL (Fin n) (Af E)).val) := by
    simp only [map_inv]
    exact Units.continuous_val.comp ((continuous_const.mul hm.inv).mul continuous_const)
  have key : (((S.L.KN N).comap T.j : Subgroup (GUf E n)) : Set (GUf E n)) =
      ⋂ (i : Fin n) (k : Fin n),
        ((fun g : GUf E n => ((T.a * mat g * T.a⁻¹ : GL (Fin n) (Af E)).val - 1) i k) ⁻¹'
            (sg {w : Plc E | (p : 𝓞 E) ∉ w.asIdeal} N : Set (Af E)) ∩
         (fun g : GUf E n => ((T.a * mat g⁻¹ * T.a⁻¹ : GL (Fin n) (Af E)).val - 1) i k) ⁻¹'
            (sg {w : Plc E | (p : 𝓞 E) ∉ w.asIdeal} N : Set (Af E))) := by
    ext g
    have e1 := (hI E A n p S T g).2 N hN
    have e2 := (hI E A n p S T g⁻¹).2 N hN
    rw [map_inv] at e2
    have hmem : g ∈ (((S.L.KN N).comap T.j : Subgroup (GUf E n)) : Set (GUf E n)) ↔
        S.L.CongOne N (T.j g) ∧ S.L.CongOne N (T.j g)⁻¹ := Iff.rfl
    rw [hmem, e1, e2]
    simp only [principalCongruence_map_iff, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩ i k
      exact ⟨fun w hw => h1 w hw i k, fun w hw => h2 w hw i k⟩
    · intro h
      exact ⟨fun w hw i k => (h i k).1 w hw, fun w hw i k => (h i k).2 w hw⟩
  rw [key]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => IsOpen.inter ?_ ?_
  · exact hO.preimage ((hc1.matrix_elem i k).sub continuous_const)
  · exact hO.preimage ((hc2.matrix_elem i k).sub continuous_const)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private lemma memSum_cls {X : Type} [Group X] {K KM K₀ : Subgroup X} {h : X}
    (hc : ∀ k ∈ K, ∀ u ∈ KM, h * k * u * (h * k)⁻¹ ∈ K₀) (k₁ k₂ : K)
    (e : (QuotientGroup.mk k₁ : K ⧸ KM.subgroupOf K) = QuotientGroup.mk k₂) (y : X) :
    h * (k₁ : X) * y ∈ K₀ ↔ h * (k₂ : X) * y ∈ K₀ := by
  have hu : k₁⁻¹ * k₂ ∈ KM.subgroupOf K := QuotientGroup.eq.1 e
  have hu' : (k₁ : X)⁻¹ * k₂ ∈ KM := by simpa [Subgroup.mem_subgroupOf] using hu
  have hm := hc k₁ k₁.2 _ hu'
  have e2 : h * (k₂ : X) * y = (h * k₁ * ((k₁ : X)⁻¹ * k₂) * (h * k₁)⁻¹) * (h * k₁ * y) := by group
  rw [e2]
  exact (K₀.mul_mem_cancel_left hm).symm

private lemma memSum_eq {X : Type} [Group X] (K KM K₀ : Subgroup X) (h y : X)
    [Fintype (K ⧸ KM.subgroupOf K)] :
    memFn K KM K₀ h y =
      ∑ q : K ⧸ KM.subgroupOf K, if h * (q.out : X) * y ∈ K₀ then (1 : ℂ) else 0 := by
  unfold memFn
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [Finset.sum_boole]

theorem UpperTheory.Gal.W2.Seed.pMemSum :
    MemSum := by
  intro X _ K KM K₀ h hK0 hidx hnorm hc
  haveI : (KM.subgroupOf K).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn⟩
  haveI : (KM.subgroupOf K).FiniteIndex := ⟨hidx⟩
  letI : Fintype (K ⧸ KM.subgroupOf K) := Fintype.ofFinite _
  have hex : ∀ y, memFn K KM K₀ h y ≠ 0 →
      ∃ q : K ⧸ KM.subgroupOf K, h * (q.out : X) * y ∈ K₀ := by
    intro y hy
    by_contra hne
    apply hy
    have : IsEmpty {q : K ⧸ KM.subgroupOf K // h * (q.out : X) * y ∈ K₀} :=
      ⟨fun ⟨q, hq⟩ => hne ⟨q, hq⟩⟩
    unfold memFn
    rw [Nat.card_of_isEmpty, Nat.cast_zero]
  have hP : ∀ (a : K) (q : K ⧸ KM.subgroupOf K) (y : X),
      h * (q.out : X) * ((a : X) * y) ∈ K₀ ↔
        h * ((q * (QuotientGroup.mk a : K ⧸ KM.subgroupOf K)).out : X) * y ∈ K₀ := by
    intro a q y
    have e : (QuotientGroup.mk (q.out * a) : K ⧸ KM.subgroupOf K) =
        QuotientGroup.mk (q * (QuotientGroup.mk a : K ⧸ KM.subgroupOf K)).out := by
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    have hcls := memSum_cls hc (q.out * a) (q * (QuotientGroup.mk a : K ⧸ KM.subgroupOf K)).out e y
    have e2 : h * (q.out : X) * ((a : X) * y) = h * ((q.out * a : K) : X) * y := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [e2]
    exact hcls
  refine ⟨?_, ?_, ?_⟩
  · show IsBiInv K₀ (memFn K KM K₀ h) ∧ FinDosetSupp K₀ (memFn K KM K₀ h)
    refine ⟨?_, ?_⟩
    · intro a b g
      unfold memFn
      congr 1
      apply Nat.card_congr
      refine (Equiv.mulRight (QuotientGroup.mk (⟨a, hK0 a.2⟩ : K) : K ⧸ KM.subgroupOf K)).subtypeEquiv ?_
      intro q
      have e1 : h * (q.out : X) * ((a : X) * g * (b : X)) =
          h * (q.out : X) * (((⟨a, hK0 a.2⟩ : K) : X) * g) * (b : X) := by
        rw [← mul_assoc (h * (q.out : X))] <;> rfl
      rw [e1, Subgroup.mul_mem_cancel_right _ b.2]
      exact hP ⟨a, hK0 a.2⟩ q g
    · refine ⟨Finset.univ.image (fun q : K ⧸ KM.subgroupOf K => (h * (q.out : X))⁻¹), fun y hy => ?_⟩
      obtain ⟨q, hq⟩ := hex y hy
      refine ⟨(h * (q.out : X))⁻¹, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, 1, ⟨_, hq⟩, ?_⟩
      simp only [OneMemClass.coe_one, one_mul]
      group
  · intro y hy
    obtain ⟨q, hq⟩ := hex y hy
    exact ⟨_, (q.out).2, hq⟩
  · intro V _ _ Φ hΦ g
    unfold hAct
    have hpt : ∀ x : X ⧸ K₀, memFn K KM K₀ h x.out • Φ (g * x.out) =
        ∑ q : K ⧸ KM.subgroupOf K,
          (if (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀) = x then Φ (g * (h * (q.out : X))⁻¹) else 0) := by
      intro x
      rw [memSum_eq, Finset.sum_smul]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hiff : (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀) = x ↔ h * (q.out : X) * x.out ∈ K₀ := by
        conv_lhs => rw [← QuotientGroup.out_eq' x]
        rw [QuotientGroup.eq, inv_inv]
      by_cases hm : h * (q.out : X) * x.out ∈ K₀
      · rw [if_pos hm, if_pos (hiff.mpr hm), one_smul]
        have hg : g * x.out = g * (h * (q.out : X))⁻¹ * (h * (q.out : X) * x.out) := by group
        rw [hg]
        exact hΦ _ hm _
      · rw [if_neg hm, if_neg (fun e => hm (hiff.mp e)), zero_smul]
    rw [finsum_eq_sum_of_fintype (fun k : K ⧸ KM.subgroupOf K => Φ (g * (h * (k.out : X))⁻¹)),
      finsum_congr hpt, finsum_sum_comm]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [finsum_eq_single _ (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀)]
      · simp
      · intro x hx
        rw [if_neg (Ne.symm hx)]
    · intro q _
      apply Set.Finite.subset (Set.finite_singleton (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀))
      intro x hx
      by_contra hne
      exact hx (if_neg (Ne.symm hne))
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pMemAct :
    MemSum → SumDoset → TfAct → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (V : Type) [AddCommGroup V] [Module ℂ V] (Ψ : X → V), (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Ψ y.out = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out)) → MemAct := by
  intro hMS hSD hTF hS X M M' _ _ _ T L' Kw hfT hap K KM htr hfK hK0 hKM hidx hnor t z h hz hh hc
  have hKMK : KM ≤ K := hKM.trans hK0
  have hcK : ∀ u ∈ KM, h * u * h⁻¹ ∈ K := fun u hu => hK0 (by simpa using hc 1 K.one_mem u hu)
  obtain ⟨hmem, -, hsum⟩ := hMS X K KM T.K₀ h hK0 hidx hnor hc
  refine ⟨hmem, ?_, ?_⟩
  · rw [map_mul, hap.1 t, hz.2, one_mul]
  · intro V _ _ Φ hΦ
    have hΦK : ∀ k ∈ K, ∀ g, Φ (g * k) = Φ g := by
      intro k hk g
      rw [hΦ k (htr.1 hk) g, htr.2 k hk, Units.val_one, one_smul]
    have hΦ0 : ∀ k ∈ T.K₀, ∀ g, Φ (g * k) = Φ g := fun k hk g => hΦK k (hK0 hk) g
    funext g
    rw [Pi.smul_apply, hsum V Φ hΦ0 g, hSD X K KM h hKMK hidx hcK V Φ hΦK hnor g,
      hTF X M M' T L' Kw hfT hap t z hz V Φ hΦ g]
    congr 1
    refine Eq.trans ?_ (hS X M' L' K Kw hfK t V (fun y => Φ (g * z * y)) ?_)
    · show ∑ᶠ x : X ⧸ K, dosetInd ℂ K h⁻¹ x.out • Φ (g * x.out) =
        ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Φ (g * z * y.out)
      rw [hh, ← finsum_comp_equiv (MulAction.toPerm z : Equiv.Perm (X ⧸ K))]
      refine finsum_congr fun q => ?_
      have hzq : (MulAction.toPerm z q : X ⧸ K) = ((z * q.out : X) : X ⧸ K) := by
        rw [MulAction.toPerm_apply]
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rw [MulAction.Quotient.smul_mk, smul_eq_mul]
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (z * q.out)
      have e1 : Φ (g * (z * q.out * k)) = Φ (g * z * q.out) := by
        rw [← mul_assoc, hΦK _ k.2, ← mul_assoc]
      have hmem2 : z * q.out * k ∈ DoubleCoset.doubleCoset (L'.loc t * z) (K : Set X) K ↔
          q.out ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K := by
        simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
        constructor
        · rintro ⟨a, ha, b, hb, e⟩
          refine ⟨a, ha, b * (k : X)⁻¹, K.mul_mem hb (K.inv_mem k.2), ?_⟩
          have hw : a * (L'.loc t * z) * b = z * (a * L'.loc t * b) := by
            rw [← mul_assoc a, ← hz.1, mul_assoc z]
          calc q.out = z⁻¹ * (z * q.out * k) * (k : X)⁻¹ := by group
            _ = z⁻¹ * (z * (a * L'.loc t * b)) * (k : X)⁻¹ := by rw [e, hw]
            _ = a * L'.loc t * (b * (k : X)⁻¹) := by group
        · rintro ⟨a, ha, b, hb, e⟩
          refine ⟨a, ha, b * k, K.mul_mem hb k.2, ?_⟩
          rw [e, ← mul_assoc a, ← hz.1]
          group
      have e2 : dosetInd ℂ K (L'.loc t * z) (z * q.out * k) = dosetInd ℂ K (L'.loc t) q.out := by
        unfold dosetInd
        simp only [Set.indicator_apply, hmem2, Pi.one_apply]
      rw [hzq, hk, e1, e2]
    · intro k hk y
      show Φ (g * z * (y * k)) = Φ (g * z * y)
      rw [← mul_assoc]
      exact hΦK k hk _
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pPPart :
    JEq → PPart := by
  intro hJ E _ _ _ A n p _ S T g
  have hext := (hJ E A n p S T.toAdT T.μ T.mu T.a T.j T.j_mx).1
  have hoff : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w (T.sec (T.j g)) = comp w g :=
    fun w hw => (T.j_eq (T.sec (T.j g)) g).1 (T.j_sec _) w hw
  have hk1 : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w ((T.sec (T.j g))⁻¹ * g) = 1 := by
    intro w hw
    rw [map_mul, map_inv, hoff w hw, inv_mul_cancel]
  have hk2 : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w ((T.sec (T.j g))⁻¹ * g) = comp w g := by
    intro w hw
    rw [map_mul, map_inv, T.sec_p _ w hw, inv_one, one_mul]
  refine ⟨(T.sec (T.j g))⁻¹ * g, by group, hk1, hk2, fun h => hext _ _ fun w => ?_⟩
  rw [map_mul (comp w) (T.sec h), map_mul (comp w) _ (T.sec h)]
  by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
  · rw [T.sec_p h w hw, one_mul, mul_one]
  · rw [hk1 w hw, one_mul, mul_one]
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private theorem card_fibre {G : Type} [Group G] (N P : Subgroup G) [N.Normal] (hNP : N ≤ P) (w : G) :
    Nat.card {q : G ⧸ N // (q.out : G) * w⁻¹ ∈ P} = N.relIndex P := by
  have hk := Subgroup.relIndex_ker P (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk'] at hk
  rw [hk]
  apply Nat.card_congr
  refine (Equiv.mulRight (QuotientGroup.mk w⁻¹ : G ⧸ N)).subtypeEquiv ?_
  intro q
  rw [Equiv.coe_mulRight, Subgroup.mem_map]
  beta_reduce
  have hq : q * (QuotientGroup.mk w⁻¹ : G ⧸ N) = QuotientGroup.mk ((q.out : G) * w⁻¹) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  rw [hq]
  constructor
  · intro hp
    exact ⟨_, hp, rfl⟩
  · rintro ⟨p, hp, e⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at e
    have hm := P.mul_mem hp (hNP e)
    simpa using hm

theorem UpperTheory.Gal.W2.Seed.pSumDoset :
    SumDoset := by
  intro X _ K KM h hKM hidx hhK V _ _ Φ hΦ hnorm g
  obtain ⟨L, hL⟩ : ∃ L : Subgroup X, L = K ⊓ Subgroup.comap (MulEquiv.toMonoidHom (MulAut.conj h)) K :=
    ⟨_, rfl⟩
  rw [← hL]
  haveI : (KM.subgroupOf K).Normal := ⟨fun n hn k => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm k k.2 n hn⟩
  haveI : (KM.subgroupOf K).FiniteIndex := ⟨hidx⟩
  letI : Fintype (K ⧸ KM.subgroupOf K) := Fintype.ofFinite _
  have hLK : L ≤ K := by
    rw [hL]
    exact inf_le_left
  have hKML : KM ≤ L := by
    intro u hu
    rw [hL, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact ⟨hKM hu, hhK u hu⟩
  have hmemL : ∀ k : K, k ∈ L.subgroupOf K ↔ h * (k : X) * h⁻¹ ∈ K := by
    intro k
    rw [Subgroup.mem_subgroupOf, hL, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    exact ⟨fun hh => hh.2, fun hh => ⟨k.2, hh⟩⟩
  have hNP : KM.subgroupOf K ≤ L.subgroupOf K := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hKML hk
  have hcard : ∀ y : X, y ∈ DoubleCoset.doubleCoset h⁻¹ (K : Set X) K →
      Nat.card {q : K ⧸ KM.subgroupOf K // h * (q.out : X) * y ∈ K} = KM.relIndex L := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
    rw [← Subgroup.relIndex_subgroupOf hLK,
      ← card_fibre (KM.subgroupOf K) (L.subgroupOf K) hNP (⟨a, ha⟩ : K)⁻¹]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro q
    rw [inv_inv, hmemL]
    have e : h * (q.out : X) * (a * h⁻¹ * b) = h * ((q.out * ⟨a, ha⟩ : K) : X) * h⁻¹ * b := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [e, Subgroup.mul_mem_cancel_right _ hb]
  have hnot : ∀ y : X, y ∉ DoubleCoset.doubleCoset h⁻¹ (K : Set X) K →
      ∀ q : K ⧸ KM.subgroupOf K, h * (q.out : X) * y ∉ K := by
    intro y hy q hq
    apply hy
    rw [DoubleCoset.mem_doubleCoset]
    exact ⟨((q.out : K) : X)⁻¹, K.inv_mem q.out.2, h * (q.out : X) * y, hq, by group⟩
  have hpt : ∀ x : X ⧸ K, ((KM.relIndex L : ℕ) : ℂ) •
      ((DoubleCoset.doubleCoset h⁻¹ (K : Set X) K).indicator (1 : X → ℂ) x.out • Φ (g * x.out)) =
      ∑ q : K ⧸ KM.subgroupOf K,
        (if (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K) = x then Φ (g * (h * (q.out : X))⁻¹) else 0) := by
    intro x
    have hterm : ∀ q : K ⧸ KM.subgroupOf K,
        (if (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K) = x then Φ (g * (h * (q.out : X))⁻¹) else 0) =
          if h * (q.out : X) * x.out ∈ K then Φ (g * x.out) else 0 := by
      intro q
      have hiff : (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K) = x ↔ h * (q.out : X) * x.out ∈ K := by
        conv_lhs => rw [← QuotientGroup.out_eq' x]
        rw [QuotientGroup.eq, inv_inv]
      by_cases hm : h * (q.out : X) * x.out ∈ K
      · rw [if_pos hm, if_pos (hiff.mpr hm)]
        have hg : g * x.out = g * (h * (q.out : X))⁻¹ * (h * (q.out : X) * x.out) := by group
        rw [hg, hΦ _ hm]
      · rw [if_neg hm, if_neg (fun e => hm (hiff.mp e))]
    rw [Finset.sum_congr rfl (fun q _ => hterm q), ← Finset.sum_filter, Finset.sum_const,
      ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    by_cases hy : x.out ∈ DoubleCoset.doubleCoset h⁻¹ (K : Set X) K
    · rw [Set.indicator_of_mem hy, Pi.one_apply, one_smul, hcard _ hy, Nat.cast_smul_eq_nsmul ℂ]
    · have : IsEmpty {q : K ⧸ KM.subgroupOf K // h * (q.out : X) * x.out ∈ K} :=
        ⟨fun ⟨q, hq⟩ => hnot _ hy q hq⟩
      rw [Set.indicator_of_notMem hy, zero_smul, smul_zero, Nat.card_of_isEmpty, zero_smul]
  unfold hAct dosetInd
  rw [smul_finsum, finsum_eq_sum_of_fintype (fun k : K ⧸ KM.subgroupOf K => Φ (g * (h * (k.out : X))⁻¹)),
    finsum_congr hpt, finsum_sum_comm]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [finsum_eq_single _ (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K)]
    · simp
    · intro x hx
      rw [if_neg (Ne.symm hx)]
  · intro q _
    apply Set.Finite.subset (Set.finite_singleton (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K))
    intro x hx
    by_contra hne
    exact hx (if_neg (Ne.symm hne))
end
