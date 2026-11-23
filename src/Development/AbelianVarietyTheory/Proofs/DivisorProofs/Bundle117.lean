module

public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Artinian.Ring
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Order.Int.LeastGreatest

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory

theorem exists_not_mem_mul_mem_span_of_reduced_artinian (R : Type) [CommRing R] (T : R)
    (hred : IsReduced (R ⧸ Ideal.span {T})) (hart : IsArtinianRing (R ⧸ Ideal.span {T}))
    (n : Ideal R) [n.IsPrime] (z : R) (hz : z ∈ n) :
    ∃ c : R, c ∉ n ∧ c * z ∈ Ideal.span {T} := by
  set x : R ⧸ Ideal.span {T} := Ideal.Quotient.mk _ z
  obtain ⟨k, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : R ⧸ Ideal.span {T})
  simp only [smul_eq_mul, mul_one] at hy
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h0 : x * (1 - x * Ideal.Quotient.mk _ w) = 0 := by
    apply IsReduced.eq_zero
    refine ⟨k + 1, ?_⟩
    have : x ^ k * (1 - x * Ideal.Quotient.mk _ w) = 0 := by
      rw [mul_sub, mul_one, ← mul_assoc, ← pow_succ, hy, sub_self]
    calc (x * (1 - x * Ideal.Quotient.mk _ w)) ^ (k + 1)
        = (x ^ k * (1 - x * Ideal.Quotient.mk _ w)) * (x * (1 - x * Ideal.Quotient.mk _ w) ^ k) := by rw [mul_pow, pow_succ, pow_succ]; ring
      _ = 0 := by rw [this, zero_mul]
  refine ⟨1 - z * w, ?_, ?_⟩
  · intro hc
    have : (1 : R) ∈ n := by
      have := n.add_mem hc (n.mul_mem_right w hz)
      simpa using this
    exact (Ideal.IsPrime.ne_top ‹_›) ((Ideal.eq_top_iff_one _).2 this)
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [x, mul_comm] using h0

theorem maximalIdeal_localization_eq_span_of_reduced_artinian :
    ∀ (R : Type) [CommRing R] (T : R), IsReduced (R ⧸ Ideal.span {T}) → IsArtinianRing (R ⧸ Ideal.span {T}) → ∀ (n : Ideal R) [n.IsPrime], T ∈ n → IsLocalRing.maximalIdeal (Localization.AtPrime n) = Ideal.span {algebraMap R (Localization.AtPrime n) T} := by
  intro R _ T hred hart n _ hT
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro z hz
    obtain ⟨c, hc, hcz⟩ := exists_not_mem_mul_mem_span_of_reduced_artinian R T hred hart n z hz
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hcz
    have hu : IsUnit (algebraMap R (Localization.AtPrime n) c) :=
      IsLocalization.map_units (Localization.AtPrime n) (⟨c, hc⟩ : n.primeCompl)
    rw [Ideal.mem_comap]
    have : algebraMap R (Localization.AtPrime n) z =
        (hu.unit⁻¹ : (Localization.AtPrime n)ˣ) * algebraMap R _ a * algebraMap R _ T := by
      rw [mul_assoc, ← map_mul, ha, map_mul, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hT

end GlobalTheory
end

section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem localization_maximalIdeal_eq_span_of_nilpotent
    (D : Type) [CommRing D] [IsArtinianRing D] (x : D) (hx : IsNilpotent x)
    (hred : IsReduced (D ⧸ Ideal.span {x})) (P : Ideal D) [P.IsMaximal] :
    IsLocalRing.maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap D (Localization.AtPrime P) x} := by
  set L := Localization.AtPrime P
  apply le_antisymm
  · intro a ha

    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := L)
    have hJ : (⊥ : Ideal L).jacobson = IsLocalRing.maximalIdeal L :=
      IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top
    have han : a ^ n = 0 := by
      have : a ^ n ∈ (⊥ : Ideal L).jacobson ^ n := Ideal.pow_mem_pow (hJ ▸ ha) n
      rw [hn] at this
      simpa using this
    obtain ⟨⟨d, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl a
    simp only at han ⊢
    rw [← IsLocalization.mk'_pow, IsLocalization.mk'_eq_zero_iff] at han
    obtain ⟨t, ht⟩ := han
    have hnil : IsNilpotent (Ideal.Quotient.mk (Ideal.span {x}) ((t : D) * d)) := by
      refine ⟨n + 1, ?_⟩
      rw [← map_pow, mul_pow, pow_succ d, ← mul_assoc, pow_succ (t : D), mul_assoc _ (t : D), ht]
      simp
    have hmem : (t : D) * d ∈ Ideal.span {x} :=
      Ideal.Quotient.eq_zero_iff_mem.mp (hnil.eq_zero)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    refine Ideal.mem_span_singleton'.mpr ⟨IsLocalization.mk' L c (t * s), ?_⟩
    rw [IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_eq_mul_mk'_one d s,
      mul_right_comm, ← map_mul, hc, ← IsLocalization.mk'_eq_mul_mk'_one,
      ← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_eq_iff_eq]
    congr 1
    push_cast
    ring
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    refine (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_
    obtain ⟨m, hm⟩ := hx.map (algebraMap D L)
    exact not_isUnit_zero (hm ▸ hu.pow m)

end GlobalTheory
end

section

open IsDedekindDomain NumberField Matrix

namespace GlobalTheory.LatticeBetweenMultiples

lemma one_add_mulVec_mem {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (S : AddSubgroup (Fin n → v.adicCompletion F))
    (hGL : ∀ x : GL (Fin n) (v.adicCompletion F), (∀ i j, x.1 i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, (x⁻¹).1 i j ∈ v.adicCompletionIntegers F) → ∀ w ∈ S, x.1.mulVec w ∈ S)
    (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (hN : N * N = 0)
    (hNi : ∀ i j, N i j ∈ v.adicCompletionIntegers F) {w : Fin n → v.adicCompletion F}
    (hw : w ∈ S) : (1 + N).mulVec w ∈ S := by
  have h1 : (1 + N) * (1 - N) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hN, sub_zero, sub_add_cancel]
  have h2 : (1 - N) * (1 + N) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hN, add_zero, add_sub_cancel_right]
  have h1m : ∀ i j, (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈
      v.adicCompletionIntegers F := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hp : ∀ i j, (1 + N) i j ∈ v.adicCompletionIntegers F := by
    intro i j; rw [Matrix.add_apply]; exact add_mem (h1m i j) (hNi i j)
  have hm : ∀ i j, (1 - N) i j ∈ v.adicCompletionIntegers F := by
    intro i j; rw [Matrix.sub_apply]; exact sub_mem (h1m i j) (hNi i j)
  exact hGL ⟨1 + N, 1 - N, h1, h2⟩ hp hm w hw

theorem eq_multiple_of_standard_lattice : ∀ {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (S : AddSubgroup (Fin n → v.adicCompletion F)),
    (∀ o ∈ v.adicCompletionIntegers F, ∀ w ∈ S, o • w ∈ S) →
    (∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w : Fin n → v.adicCompletion F,
      (∀ i, w i ∈ v.adicCompletionIntegers F) → t • w ∈ S) →
    (∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w ∈ S, ∀ i, t * w i ∈ v.adicCompletionIntegers F) →
    (∀ x : GL (Fin n) (v.adicCompletion F), (∀ i j, x.1 i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, (x⁻¹).1 i j ∈ v.adicCompletionIntegers F) → ∀ w ∈ S, x.1.mulVec w ∈ S) →
    ∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w, w ∈ S ↔ ∀ i, t * w i ∈ v.adicCompletionIntegers F := by
  intro F _ _ v n S hO ⟨tl, htl0, htl⟩ ⟨tu, htu0, htu⟩ hGL
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, one_ne_zero, fun w => ?_⟩
    have hw : w = 0 := Subsingleton.elim _ _
    subst hw
    exact ⟨fun _ i => i.elim0, fun _ => S.zero_mem⟩
  have memO : ∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 :=
    fun x => Iff.rfl

  have hbd : ∀ w ∈ S, ∀ i, Valued.v (w i) ≤ (Valued.v tu)⁻¹ := by
    intro w hw i
    have h := (memO _).1 (htu w hw i)
    rw [map_mul] at h
    have hu : Valued.v tu ≠ 0 := (Valuation.ne_zero_iff _).2 htu0
    calc Valued.v (w i) = (Valued.v tu)⁻¹ * (Valued.v tu * Valued.v (w i)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hu, one_mul]
      _ ≤ (Valued.v tu)⁻¹ * 1 := by gcongr
      _ = (Valued.v tu)⁻¹ := mul_one _
  let P : ℤ → Prop := fun k => ∃ w ∈ S, ∃ i, Valued.v (w i) =
    ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  obtain ⟨mB, hmB⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = (Valued.v tu)⁻¹ :=
    WithZero.ne_zero_iff_exists.1 (inv_ne_zero ((Valuation.ne_zero_iff _).2 htu0))
  have hPb : ∃ b : ℤ, ∀ z, P z → z ≤ b := by
    refine ⟨Multiplicative.toAdd mB, fun z ⟨w, hw, i, hz⟩ => ?_⟩
    have h := hbd w hw i
    rw [hz, ← hmB, WithZero.coe_le_coe] at h
    exact Multiplicative.ofAdd_le.1 (by simpa using h)
  let i₀' : Fin n := ⟨0, hn⟩
  have hPn : ∃ z, P z := by
    have hmem : tl • (fun _ => (1 : v.adicCompletion F)) ∈ S := htl _ (fun _ => one_mem _)
    obtain ⟨m, hm⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = Valued.v tl :=
      WithZero.ne_zero_iff_exists.1 ((Valuation.ne_zero_iff _).2 htl0)
    refine ⟨Multiplicative.toAdd m, _, hmem, i₀', ?_⟩
    simp [← hm]
  obtain ⟨lb, ⟨w₀, hw₀, i₀, hc⟩, hlb⟩ := Int.exists_greatest_of_bdd hPb hPn
  set c := w₀ i₀ with hcdef
  have hvc : Valued.v c ≠ 0 := by rw [hc]; exact WithZero.coe_ne_zero
  have hc0 : c ≠ 0 := fun h => hvc (by rw [h, map_zero])
  have hmax : ∀ w ∈ S, ∀ i, Valued.v (w i) ≤ Valued.v c := by
    intro w hw i
    by_cases h0 : w i = 0
    · rw [h0, map_zero]; exact zero_le'
    obtain ⟨m, hm⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = Valued.v (w i) :=
      WithZero.ne_zero_iff_exists.1 ((Valuation.ne_zero_iff _).2 h0)
    have hk := hlb (Multiplicative.toAdd m) ⟨w, hw, i, by simp [← hm]⟩
    rw [← hm, hc, WithZero.coe_le_coe]
    exact Multiplicative.toAdd_le.1 (by simpa using hk)
  have hint : ∀ w ∈ S, ∀ i, c⁻¹ * w i ∈ v.adicCompletionIntegers F := by
    intro w hw i
    rw [memO, map_mul, map_inv₀]
    calc (Valued.v c)⁻¹ * Valued.v (w i) ≤ (Valued.v c)⁻¹ * Valued.v c :=
          by gcongr; exact hmax w hw i
      _ = 1 := inv_mul_cancel₀ hvc

  have hsingle0 : Pi.single i₀ c ∈ S := by
    let N : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
      fun a b => if b = i₀ ∧ a ≠ i₀ then -(c⁻¹ * w₀ a) else 0
    have hN : N * N = 0 := by
      funext a b
      simp only [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      by_cases hm : m = i₀ <;> simp [N, hm]
    have hNi : ∀ i j, N i j ∈ v.adicCompletionIntegers F := by
      intro i j
      simp only [N]
      split_ifs
      · exact neg_mem (hint w₀ hw₀ i)
      · exact zero_mem _
    have h := one_add_mulVec_mem v S hGL N hN hNi hw₀
    convert h using 1
    funext a
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
    by_cases ha : a = i₀
    · subst ha
      simp [N, Matrix.mulVec, dotProduct, hcdef]
    · simp [N, Matrix.mulVec, dotProduct, ha, Pi.single_apply, ← hcdef]
      field_simp
      ring
  have hsingle : ∀ j, Pi.single j c ∈ S := by
    intro j
    by_cases hj : j = i₀
    · subst hj; exact hsingle0
    let N : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
      fun a b => if a = j ∧ b = i₀ then 1 else 0
    have hN : N * N = 0 := by
      funext a b
      simp only [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      by_cases hm : m = i₀
      · subst hm; simp [N, Ne.symm hj]
      · simp [N, hm]
    have hNi : ∀ i k, N i k ∈ v.adicCompletionIntegers F := by
      intro i k
      simp only [N]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h := one_add_mulVec_mem v S hGL N hN hNi hsingle0
    have heq : (1 + N).mulVec (Pi.single i₀ c) = Pi.single i₀ c + Pi.single j c := by
      funext a
      rw [Matrix.add_mulVec, Matrix.one_mulVec]
      simp [N, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [heq] at h
    simpa using S.sub_mem h hsingle0
  refine ⟨c⁻¹, inv_ne_zero hc0, fun w => ⟨fun hw i => hint w hw i, fun hw => ?_⟩⟩
  have hsum : w = ∑ j, (c⁻¹ * w j) • Pi.single j c := by
    funext a
    rw [Finset.sum_apply, Finset.sum_eq_single a]
    · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      field_simp
    · intro b _ hb
      simp [Pi.single_apply, Ne.symm hb]
    · simp
  rw [hsum]
  exact S.sum_mem (fun j _ => hO _ (hw j) _ (hsingle j))

end GlobalTheory.LatticeBetweenMultiples
end

section

open NumberField IsDedekindDomain Filter

noncomputable section

namespace GlobalTheory.BCT.SuppFin

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_vle (w : HeightOneSpectrum (𝓞 E)) (m : ℤ) :
    IsOpen {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective E w (WithZero.exp m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp m} =
      {y | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isOpen_closedBall _ (by simp [hc0])

theorem exists_bound_of_isCompact (w : HeightOneSpectrum (𝓞 E)) {K : Set (w.adicCompletion E)}
    (hK : IsCompact K) : ∃ N : ℤ, ∀ z ∈ K, Valued.v z ≤ WithZero.exp N := by
  have hcov : K ⊆ ⋃ N : ℤ, {y : w.adicCompletion E | Valued.v y ≤ WithZero.exp N} := by
    intro z _
    rw [Set.mem_iUnion]
    by_cases hz : Valued.v z = 0
    · exact ⟨0, by simp [hz]⟩
    · exact ⟨WithZero.log (Valued.v z), by simp [WithZero.exp_log hz]⟩
  obtain ⟨N, hN⟩ := hK.elim_directed_cover _ (fun N => isOpen_vle w N) hcov
    (Monotone.directed_le fun a b hab y hy => le_trans hy (WithZero.exp_le_exp.2 hab))
  exact ⟨N, fun z hz => hN hz⟩

theorem gl_entries_bounded_of_isCompact : ∀ (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (D : Set (GL (Fin n) (w.adicCompletion E))),
    IsCompact D → ∃ N : ℤ, ∀ h ∈ D, ∀ i j,
      Valued.v (h.val i j) ≤ WithZero.exp N ∧ Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N := by
  intro E _ _ w n D hD
  have h1 : ∀ i j, ∃ N : ℤ, ∀ h ∈ D, Valued.v (h.val i j) ≤ WithZero.exp N := by
    intro i j
    obtain ⟨N, hN⟩ := exists_bound_of_isCompact w
      (hD.image (Units.continuous_val.matrix_elem i j))
    exact ⟨N, fun h hh => hN _ ⟨h, hh, rfl⟩⟩
  have h2 : ∀ i j, ∃ N : ℤ, ∀ h ∈ D, Valued.v ((h⁻¹).val i j) ≤ WithZero.exp N := by
    intro i j
    obtain ⟨N, hN⟩ := exists_bound_of_isCompact w
      (hD.image ((Units.continuous_coe_inv).matrix_elem i j))
    exact ⟨N, fun h hh => hN _ ⟨h, hh, rfl⟩⟩
  choose N1 hN1 using h1
  choose N2 hN2 using h2
  refine ⟨((Finset.univ.sup (fun p : Fin n × Fin n => (N1 p.1 p.2).toNat) : ℕ) : ℤ) ⊔
      ((Finset.univ.sup (fun p : Fin n × Fin n => (N2 p.1 p.2).toNat) : ℕ) : ℤ), ?_⟩
  intro h hh i j
  have a1 : N1 i j ≤ ((Finset.univ.sup (fun p : Fin n × Fin n => (N1 p.1 p.2).toNat) : ℕ) : ℤ) :=
    (Int.self_le_toNat _).trans (Int.ofNat_le.2
      (Finset.le_sup (f := fun p : Fin n × Fin n => (N1 p.1 p.2).toNat) (Finset.mem_univ (i, j))))
  have a2 : N2 i j ≤ ((Finset.univ.sup (fun p : Fin n × Fin n => (N2 p.1 p.2).toNat) : ℕ) : ℤ) :=
    (Int.self_le_toNat _).trans (Int.ofNat_le.2
      (Finset.le_sup (f := fun p : Fin n × Fin n => (N2 p.1 p.2).toNat) (Finset.mem_univ (i, j))))
  exact ⟨(hN1 i j h hh).trans (WithZero.exp_le_exp.2 (a1.trans le_sup_left)),
    (hN2 i j h hh).trans (WithZero.exp_le_exp.2 (a2.trans le_sup_right))⟩

end GlobalTheory.BCT.SuppFin
end
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.isIntegral_matrix_of_pow_bounded {O K : Type} [CommRing O] [IsNoetherianRing O]
    [Field K] [Algebra O K] {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (a : K) (ha : a ≠ 0)
    (h : ∀ (k : ℕ) (i j : Fin n), ∃ b : O, algebraMap O K b = a * (g ^ k) i j) :
    IsIntegral O g := by
  classical
  let ψ : (Fin n → Fin n → O) →ₗ[O] Matrix (Fin n) (Fin n) K :=
    { toFun := fun b => Matrix.of fun i j => algebraMap O K (b i j)
      map_add' := fun b c => by ext i j; simp
      map_smul' := fun c b => by ext i j; simp [Algebra.smul_def] }
  let φ : Matrix (Fin n) (Fin n) K →ₗ[O] Matrix (Fin n) (Fin n) K :=
    { toFun := fun A => a • A
      map_add' := fun A B => smul_add a A B
      map_smul' := fun c A => smul_comm a c A }
  have hφ : Function.Injective φ := fun A B hAB => smul_right_injective _ ha hAB
  have hP : (LinearMap.range ψ).FG := by
    rw [LinearMap.range_eq_map]; exact Submodule.FG.map _ Module.Finite.fg_top
  haveI := isNoetherian_of_fg_of_noetherian _ hP
  have hle : Submodule.map φ (Subalgebra.toSubmodule (Algebra.adjoin O {g})) ≤
      LinearMap.range ψ := by
    rw [Algebra.adjoin_eq_span, ← Submonoid.powers_eq_closure, Submodule.map_span_le]
    rintro _ ⟨k, rfl⟩
    choose b hb using h k
    exact ⟨b, by ext i j; simp [ψ, φ, hb]⟩
  exact IsIntegral.of_mem_of_fg _ (Submodule.fg_of_fg_map_injective φ hφ
    (Submodule.FG.of_le_of_isNoetherian hle)) g (Algebra.self_mem_adjoin_singleton O g)

open NumberField IsDedekindDomain in
private theorem exists_smul_pow_entry_mem_adicCompletionIntegers (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E))
    (hg : IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E))))) :
    ∃ a : w.adicCompletion E, a ≠ 0 ∧ ∀ (k : ℕ) (i j : Fin n),
      a * ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ^ k) i j ∈
        w.adicCompletionIntegers E := by
  set O := w.adicCompletionIntegers E
  set C := closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E)))
  set S : Set (w.adicCompletion E) :=
    ⋃ i, ⋃ j, (fun h : GL (Fin n) (w.adicCompletion E) => (h : Matrix (Fin n) (Fin n) _) i j) '' C
  have hS : IsCompact S := isCompact_iUnion fun i => isCompact_iUnion fun j =>
    hg.image (Units.continuous_val.matrix_elem i j)
  let U : {a : w.adicCompletion E // a ∈ O ∧ a ≠ 0} → Set (w.adicCompletion E) :=
    fun a => (fun x => a.1 * x) ⁻¹' (O : Set _)
  have hUo : ∀ a, IsOpen (U a) := fun a =>
    (Valued.isOpen_integer _).preimage (continuous_const.mul continuous_id)
  have hcov : S ⊆ ⋃ a, U a := by
    intro x _
    by_cases hx : x ∈ O
    · exact Set.mem_iUnion.2 ⟨⟨1, O.one_mem, one_ne_zero⟩, by simpa [U] using hx⟩
    · have hx0 : x ≠ 0 := by
        rintro rfl
        exact hx O.zero_mem
      have hxi : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hx
      exact Set.mem_iUnion.2 ⟨⟨x⁻¹, hxi, inv_ne_zero hx0⟩, by simp [U, hx0, O.one_mem]⟩
  have hdir : Directed (· ⊆ ·) U := by
    rintro ⟨a, ha, ha0⟩ ⟨b, hb, hb0⟩
    refine ⟨⟨a * b, mul_mem ha hb, mul_ne_zero ha0 hb0⟩, ?_, ?_⟩
    · intro x hx
      have := mul_mem hb (show a * x ∈ O from hx)
      simpa [U, mul_assoc, mul_comm, mul_left_comm] using this
    · intro x hx
      have := mul_mem ha (show b * x ∈ O from hx)
      simpa [U, mul_assoc] using this
  haveI : Nonempty {a : w.adicCompletion E // a ∈ O ∧ a ≠ 0} := ⟨⟨1, O.one_mem, one_ne_zero⟩⟩
  obtain ⟨a, hSa⟩ := hS.elim_directed_cover U hUo hcov hdir
  refine ⟨a.1, a.2.2, fun k i j => hSa ?_⟩
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨g ^ k, subset_closure ?_, by simp⟩⟩⟩
  exact Subgroup.npow_mem_zpowers g k


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.isIntegral_of_isCompact_closure_zpowers (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E))
    (hg : IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E))))) :
    IsIntegral (w.adicCompletionIntegers E)
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
  obtain ⟨a, ha0, ha⟩ := exists_smul_pow_entry_mem_adicCompletionIntegers E w n g hg
  exact _root_.GlobalTheory.isIntegral_matrix_of_pow_bounded _ a ha0 fun k i j => ⟨⟨_, ha k i j⟩, rfl⟩

end GlobalTheory
end
