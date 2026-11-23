module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle035
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle033
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle034
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem herbPhi_arith (q h0 h1 a t bI bT cI cT i c : ℕ) (hi : i ≠ 0) (hcT : cT ≠ 0)
    (e1 : a * bT * cT = bI * cI * t) (e2 : cI * c ^ q = i ^ q * cT)
    (e3 : h0 * i * bT = bI * h1 * c) :
    h0 ^ q * a * bT ^ (q + 1) = h1 ^ q * t * bI ^ (q + 1) := by
  have hne : i ^ q * cT ≠ 0 := mul_ne_zero (pow_ne_zero _ hi) hcT
  apply mul_right_cancel₀ hne
  calc h0 ^ q * a * bT ^ (q + 1) * (i ^ q * cT) = (h0 * i * bT) ^ q * (a * bT * cT) := by ring
    _ = (bI * h1 * c) ^ q * (bI * cI * t) := by rw [e1, e3]
    _ = h1 ^ q * t * bI ^ (q + 1) * (cI * c ^ q) := by ring
    _ = _ := by rw [e2]

theorem herbPhi_nrm_dif {A : Type} [CommGroup A] (σ : A →* A) (n : ℕ) (a : A) :
    nrm σ n (dif σ a) = σ^[n] a / a := by
  induction n with
  | zero => simp [nrm_apply]
  | succ n ih =>
    rw [nrm_apply] at ih ⊢
    rw [Finset.prod_range_succ, ih, dif_apply, iterate_map_div, Function.iterate_succ_apply,
      mul_comm, div_mul_div_cancel]

theorem herbPhi_stable (p : ℕ) (A : Type) [CommGroup A] (σ : A →* A) (hp : p.Prime)
    (C : Subgroup A) (hst : ∀ x ∈ C, σ x ∈ C) (hn : ∀ x ∈ C, nrm σ p x = 1)
    (hI : pIdx p C ≠ 0) (hT : pTor p C ≠ 0) :
    (C.map (dif σ)).relIndex C ≠ 0 ∧ Nat.card ↥(C ⊓ fix σ) ≠ 0 ∧
      pIdx p C * Nat.card ↥(C ⊓ fix σ) ^ (p - 1) =
        (C.map (dif σ)).relIndex C ^ (p - 1) * pTor p C := by
  let τ : C →* C := (σ.comp C.subtype).codRestrict C (fun x => hst x x.2)
  have hτ : ∀ x : C, (τ x : A) = σ x := fun x => rfl
  have hit : ∀ (k : ℕ) (x : C), ((τ^[k] x : C) : A) = σ^[k] x := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hτ, ih]
  let lam : Monoid.End C := dif τ
  have hnτ : ∀ a, nrm τ p a = 1 := by
    intro a
    apply Subtype.ext
    have := hn a a.2
    rw [nrm_apply] at this ⊢
    rw [SubmonoidClass.coe_finsetProd]
    simp only [hit]
    exact this
  obtain ⟨h1, h2⟩ := GlobalTheory.T.pow_prime_range_eq_iterated_difference p C τ lam hp (fun _ => rfl) hnτ
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = k + 1 := ⟨p - 2, by have := hp.two_le; omega⟩
  rw [hk] at h1 h2 ⊢
  have eI : pIdx p C = (MonoidHom.range (lam ^ (k + 1) : Monoid.End C)).index := by
    rw [← h1, pIdx, Subgroup.relIndex]
    congr 1
    ext x
    simp only [pows, Subgroup.mem_subgroupOf, Subgroup.mem_map, powMonoidHom_apply]
    constructor
    · rintro ⟨y, hy, e⟩
      exact ⟨⟨y, hy⟩, trivial, Subtype.ext e⟩
    · rintro ⟨y, -, e⟩
      exact ⟨y, y.2, congrArg Subtype.val e⟩
  have eT : pTor p C = Nat.card (MonoidHom.ker (lam ^ (k + 1) : Monoid.End C)) := by
    rw [pTor]
    refine Nat.card_congr ⟨fun x => ⟨⟨x.1, x.2.1⟩, (h2 _).1 (Subtype.ext x.2.2)⟩,
      fun y => ⟨y.1.1, y.1.2, congrArg Subtype.val ((h2 _).2 y.2)⟩, fun _ => rfl, fun _ => rfl⟩
  have ei : (C.map (dif σ)).relIndex C = (MonoidHom.range lam).index := by
    rw [Subgroup.relIndex]
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨y, hy, e⟩
      exact ⟨⟨y, hy⟩, Subtype.ext e⟩
    · rintro ⟨y, e⟩
      exact ⟨y, y.2, congrArg Subtype.val e⟩
  have ec : Nat.card ↥(C ⊓ fix σ) = Nat.card (MonoidHom.ker lam) := by
    refine Nat.card_congr ⟨fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext (div_eq_one.2 x.2.2)⟩,
      fun y => ⟨y.1.1, y.1.2, div_eq_one.1 (congrArg Subtype.val y.2)⟩, fun _ => rfl, fun _ => rfl⟩
  rw [eI] at hI ⊢
  rw [eT] at hT ⊢
  rw [ei, ec]
  exact GlobalTheory.T.index_range_ker_iterate_endomorphism C lam k hI hT

theorem herbrand_prime_order : ∀ (p : ℕ) (A : Type) [CommGroup A] (σ : A →* A), p.Prime → (∀ a, σ^[p] a = a) → pIdx p (⊤ : Subgroup A) ≠ 0 → pTor p (⊤ : Subgroup A) ≠ 0 → (nrm σ p).range.relIndex (fix σ) ≠ 0 ∧ (dif σ).range.relIndex (nrm σ p).ker ≠ 0 ∧ pIdx p (fix σ) ≠ 0 ∧ pTor p (fix σ) ≠ 0 ∧ (nrm σ p).range.relIndex (fix σ) ^ (p - 1) * pIdx p (⊤ : Subgroup A) * pTor p (fix σ) ^ p = (dif σ).range.relIndex (nrm σ p).ker ^ (p - 1) * pTor p (⊤ : Subgroup A) * pIdx p (fix σ) ^ p := by
  intro p A _ σ hp hσ ha ht
  have hker : (dif σ).ker = fix σ := by
    ext x
    rw [MonoidHom.mem_ker, dif_apply, div_eq_one, mem_fix]
  have hcT : pTor p (dif σ).range ≠ 0 := by
    unfold pTor at ht ⊢
    have hfin : Finite {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1} := Nat.finite_of_card_ne_zero ht
    have : Finite {x : A // x ∈ (dif σ).range ∧ x ^ p = 1} :=
      Finite.of_injective (β := {x : A // x ∈ (⊤ : Subgroup A) ∧ x ^ p = 1})
        (fun x => ⟨x.1, trivial, x.2.2⟩) (fun x y h => Subtype.ext (by simpa using h))
    have : Nonempty {x : A // x ∈ (dif σ).range ∧ x ^ p = 1} := ⟨⟨1, one_mem _, one_pow _⟩⟩
    exact Nat.card_pos.ne'
  obtain ⟨hbI, hbT, hcI⟩ := GlobalTheory.T.powIndex_torsion_finite_ker_range p A A (dif σ) ha ht hcT
  obtain ⟨-, -, e1⟩ := GlobalTheory.T.powIndex_torsion_ker_range_mul p A A (dif σ) hbI hbT hcI hcT
  rw [hker] at hbI hbT e1
  obtain ⟨hi, hc, e2⟩ := herbPhi_stable p A σ hp (dif σ).range
    (by rintro _ ⟨y, rfl⟩; exact ⟨σ y, by rw [dif_apply, dif_apply, _root_.map_div]⟩)
    (by rintro _ ⟨y, rfl⟩; rw [herbPhi_nrm_dif, hσ, div_self']) hcI hcT
  have e3 := GlobalTheory.T.norm_difference_index_identity p A σ hσ
  have hle : pows p (fix σ) ≤ (nrm σ p).range := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, ?_⟩
    have hy' : σ y = y := hy
    rw [nrm_apply, Finset.prod_congr rfl (fun i _ => Function.iterate_fixed hy' i)]
    simp
  have h0 : (nrm σ p).range.relIndex (fix σ) ≠ 0 :=
    ne_zero_of_dvd_ne_zero hbI (Subgroup.relIndex_dvd_of_le_left _ hle)
  have h1 : (dif σ).range.relIndex (nrm σ p).ker ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul] at e3
    exact mul_ne_zero (mul_ne_zero h0 hi) hbT e3
  refine ⟨h0, h1, hbI, hbT, ?_⟩
  have := herbPhi_arith (p - 1) _ _ _ _ _ _ _ _ _ _ hi hcT e1 e2 e3
  rwa [Nat.sub_add_cancel hp.one_le] at this

end GlobalTheory.CNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.GaloisDescent

private theorem exists_rational_support_subset_of_galois_stable {V κ : Type} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ ℂ V) (W : Submodule ℂ V)
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) :
    ∀ n : ℕ, ∀ w ∈ W, w ≠ 0 → (b.repr w).support.card = n →
      ∃ u ∈ W, u ≠ 0 ∧ (∀ k, ∃ q : ℚ, b.repr u k = q) ∧
        (b.repr u).support ⊆ (b.repr w).support := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hw0 hcard
  have hrepr0 : b.repr w ≠ 0 := fun h => hw0 (b.repr.map_eq_zero_iff.mp h)
  obtain ⟨k₀, hk₀⟩ := Finsupp.support_nonempty_iff.mpr hrepr0
  have hk₀' : b.repr w k₀ ≠ 0 := Finsupp.mem_support_iff.mp hk₀

  have hvW : (b.repr w k₀)⁻¹ • w ∈ W := W.smul_mem _ hw
  have hvk : ∀ k, b.repr ((b.repr w k₀)⁻¹ • w) k = (b.repr w k₀)⁻¹ * b.repr w k := by
    intro k; simp
  have hv1 : b.repr ((b.repr w k₀)⁻¹ • w) k₀ = 1 := by
    rw [hvk, inv_mul_cancel₀ hk₀']
  by_cases hfix : ∀ σ : ℂ ≃+* ℂ, ∀ k,
      σ (b.repr ((b.repr w k₀)⁻¹ • w) k) = b.repr ((b.repr w k₀)⁻¹ • w) k
  ·
    refine ⟨_, hvW, ?_, fun k => GlobalTheory.T.exists_rat_of_forall_complex_ringEquiv_fixed _ (fun σ => hfix σ k), ?_⟩
    · intro h0
      rw [h0, map_zero, Finsupp.zero_apply] at hv1
      exact zero_ne_one hv1
    · intro k hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      rw [hvk] at hk
      exact right_ne_zero_of_mul hk
  ·
    push Not at hfix
    obtain ⟨σ, k₁, hk₁⟩ := hfix
    obtain ⟨v', hv'W, hv'⟩ := hW σ _ hvW
    have hdW : (b.repr w k₀)⁻¹ • w - v' ∈ W := W.sub_mem hvW hv'W
    have hdk : ∀ k, b.repr ((b.repr w k₀)⁻¹ • w - v') k =
        b.repr ((b.repr w k₀)⁻¹ • w) k - σ (b.repr ((b.repr w k₀)⁻¹ • w) k) := by
      intro k; rw [map_sub, Finsupp.sub_apply, hv']
    have hd0 : (b.repr w k₀)⁻¹ • w - v' ≠ 0 := by
      intro h
      have := hdk k₁
      rw [h, map_zero, Finsupp.zero_apply] at this
      exact hk₁ (sub_eq_zero.mp this.symm).symm
    have hsub : (b.repr ((b.repr w k₀)⁻¹ • w - v')).support ⊆ (b.repr w).support := by
      intro k hk
      rw [Finsupp.mem_support_iff] at hk ⊢
      intro hwk
      apply hk
      rw [hdk, hvk, hwk]
      simp
    have hk₀d : k₀ ∉ (b.repr ((b.repr w k₀)⁻¹ • w - v')).support := by
      rw [Finsupp.mem_support_iff, not_not, hdk, hv1, map_one, sub_self]
    have hlt : (b.repr ((b.repr w k₀)⁻¹ • w - v')).support.card < n := by
      rw [← hcard]
      exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨k₀, hk₀, hk₀d⟩)
    obtain ⟨u, huW, hu0, hurat, husub⟩ := ih _ hlt _ hdW hd0 rfl
    exact ⟨u, huW, hu0, hurat, husub.trans hsub⟩

theorem exists_rational_support_subset {V κ : Type} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ ℂ V) (W : Submodule ℂ V)
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) (n : ℕ) :
    ∀ w ∈ W, w ≠ 0 → (b.repr w).support.card = n →
      ∃ u ∈ W, u ≠ 0 ∧ (∀ k, ∃ q : ℚ, b.repr u k = q) ∧
        (b.repr u).support ⊆ (b.repr w).support :=
  fun w hw hw0 hcard => exists_rational_support_subset_of_galois_stable b W hW n w hw hw0 hcard

private theorem mem_span_rational_of_galois_stable_of_support_card {V κ : Type} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ ℂ V) (W : Submodule ℂ V)
    (hW : ∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) :
    ∀ n : ℕ, ∀ w ∈ W, (b.repr w).support.card = n →
      w ∈ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hcard
  by_cases hw0 : w = 0
  · rw [hw0]; exact Submodule.zero_mem _
  obtain ⟨u, huW, hu0, hurat, husub⟩ :=
    exists_rational_support_subset b W hW n w hw hw0 hcard
  have hru : b.repr u ≠ 0 := fun h => hu0 (b.repr.map_eq_zero_iff.mp h)
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hru
  have huk : b.repr u k ≠ 0 := Finsupp.mem_support_iff.mp hk

  have hdk : ∀ j, b.repr (w - (b.repr w k / b.repr u k) • u) j =
      b.repr w j - (b.repr w k / b.repr u k) * b.repr u j := by
    intro j; simp
  have hsub : (b.repr (w - (b.repr w k / b.repr u k) • u)).support ⊆ (b.repr w).support := by
    intro j hj
    rw [Finsupp.mem_support_iff] at hj ⊢
    intro hwj
    apply hj
    have huj : b.repr u j = 0 := by
      by_contra h
      exact Finsupp.mem_support_iff.mp (husub (Finsupp.mem_support_iff.mpr h)) hwj
    rw [hdk, hwj, huj]
    simp
  have hkout : k ∉ (b.repr (w - (b.repr w k / b.repr u k) • u)).support := by
    rw [Finsupp.mem_support_iff, not_not, hdk, div_mul_cancel₀ _ huk, sub_self]
  have hlt : (b.repr (w - (b.repr w k / b.repr u k) • u)).support.card < n := by
    rw [← hcard]
    exact Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨k, husub hk, hkout⟩)
  have h1 := ih _ hlt _ (W.sub_mem hw (W.smul_mem _ huW)) rfl
  have h2 : u ∈ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} :=
    Submodule.subset_span ⟨huW, hurat⟩
  have h3 := Submodule.add_mem _ h1 (Submodule.smul_mem _ (b.repr w k / b.repr u k) h2)
  rwa [sub_add_cancel] at h3

theorem le_span_rational :
    ∀ (V κ : Type) [AddCommGroup V] [Module ℂ V] (b : Module.Basis κ ℂ V) (W : Submodule ℂ V), (∀ σ : ℂ ≃+* ℂ, ∀ w ∈ W, ∃ w' ∈ W, ∀ k, b.repr w' k = σ (b.repr w k)) → W ≤ Submodule.span ℂ {w | w ∈ W ∧ ∀ k, ∃ q : ℚ, b.repr w k = q} := by
  intro V κ _ _ b W hW w hw
  exact mem_span_rational_of_galois_stable_of_support_card b W hW _ w hw rfl

end GlobalTheory.ClassFin.GaloisDescent
end
