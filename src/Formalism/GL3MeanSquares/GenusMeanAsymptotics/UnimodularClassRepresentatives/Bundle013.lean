module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle001
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle011
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle002
public import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountPowSuccInert
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountSplitOne
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem smul_mem_loc {L : Submodule (𝓞 K) V} {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K}
    (ha : a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) {m : V} (hm : m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    a • m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  obtain ⟨r, s, hs, rfl⟩ := (mem_locR_iff hp a).mp ha
  obtain ⟨t, ht, htm⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hm
  refine Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨s * t, mul_mem hs ht, ?_⟩
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hp hs
  have : (s * t) • ((algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) • m) = r • (t • m) := by
    rw [← algebraMap_smul K (s * t), ← algebraMap_smul K r, ← algebraMap_smul K t, smul_smul,
      smul_smul, map_mul]
    congr 1
    field_simp
  rw [this]
  exact L.smul_mem r htm

theorem isSelfDualMod_loc {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) {p : Ideal (𝓞 K)} (hp : p.IsPrime)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) :
    IsSelfDualMod (locRing p) h (Formalism.HermitianLatticesTheory.loc (K := K) p L).toAddSubgroup := by
  have hu' : ∀ x, x ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L ↔
      ∀ y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L, h y x ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
    intro x
    rw [← Formalism.HermitianLatticesTheory.locDual_mem_dualAt]
    unfold Formalism.HermitianLatticesTheory.IsUnimodularAt at hu
    rw [hu]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha m hm
    exact smul_mem_loc hp ha hm
  · intro x hx y hy
    exact (hu' y).mp hy x hx
  · intro x hx
    exact (hu' x).mpr hx
  · intro x
    obtain ⟨n, hn, hnx⟩ := Formalism.HermitianLatticesTheory.traceReal_mult L hL x
    refine ⟨(n : K), by exact_mod_cast hn, ?_⟩
    rw [Int.cast_smul_eq_zsmul]
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ L hnx

end Formalism.HermitianLattices.Ext.L3.WA
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace C2

theorem geom_of_step (c : ℕ → ℕ) (a : ℕ) (h : ∀ k, 1 ≤ k → c (k + 1) = a * c k) (k : ℕ)
    (hk : 1 ≤ k) : c k = a ^ (k - 1) * c 1 := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [h n hn, ih, show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]
    ring

theorem cast_geom (c : ℕ → ℕ) (q N : ℕ) (X : ℝ) (h : ∀ k, 1 ≤ k → c (k + 1) = q ^ N * c k)
    (h1 : (c 1 : ℝ) = (q : ℝ) ^ N * X) (k : ℕ) (hk : 1 ≤ k) :
    (c k : ℝ) = (q : ℝ) ^ (N * k) * X := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [geom_of_step c (q ^ N) h (j + 1) hk]
  push_cast
  rw [h1]
  ring

theorem inert_alg (q : ℝ) (hq : q ≠ 0) (M : ℕ) (hM : 1 ≤ M) :
    q ^ (M - 1) * (q ^ M - (-1) ^ M) = q ^ (2 * M - 1) * (1 - (-1 : ℝ) ^ M * q ^ (-(M : ℤ))) := by
  obtain ⟨j, rfl⟩ : ∃ j, M = j + 1 := ⟨M - 1, by omega⟩
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, Nat.add_sub_cancel, zpow_neg]
  rw [show ((j + 1 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℤ) from rfl, zpow_natCast]
  field_simp
  ring

theorem split_alg (q : ℝ) (hq : q ≠ 0) (M : ℕ) (hM : 1 ≤ M) :
    q ^ (2 * M - 1) - q ^ (M - 1) = q ^ (2 * M - 1) * (1 - q ^ (-(M : ℤ))) := by
  obtain ⟨j, rfl⟩ : ∃ j, M = j + 1 := ⟨M - 1, by omega⟩
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, Nat.add_sub_cancel, zpow_neg]
  rw [show ((j + 1 : ℕ) : ℤ) = ((j + 1 : ℕ) : ℤ) from rfl, zpow_natCast]
  field_simp
  ring

end C2

theorem localDensity : LocalDensity := by
  intro K _ _ _ hK P hP M k hM hk n hn hnP
  have hPbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have hN0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hPbot
  constructor
  · intro hc
    obtain ⟨q, hq⟩ := exists_sq_absNorm_of_inert hK hP hc
    have hq0 : (q : ℝ) ≠ 0 := by
      intro h0
      have h1 : q = 0 := by exact_mod_cast h0
      rw [h1] at hq
      exact hN0 (by simpa using hq)
    have hsq : Real.sqrt (Ideal.absNorm P : ℝ) = q := by
      rw [hq]
      push_cast
      exact Real.sqrt_sq (Nat.cast_nonneg q)
    rw [hsq]
    have h1 : ((normRepCount K (P ^ 1) M n : ℕ) : ℝ) =
        (q : ℝ) ^ (2 * M - 1) * (1 - (-1 : ℝ) ^ M * (q : ℝ) ^ (-(M : ℤ))) := by
      rw [pow_one]
      have h3 := normRepCount_inert_one hK hP hc M hM n hn hnP q hq
      have h2 : ((normRepCount K P M n : ℕ) : ℝ) = (q : ℝ) ^ (M - 1) * ((q : ℝ) ^ M - (-1) ^ M) := by
        exact_mod_cast h3
      rw [h2, C2.inert_alg _ hq0 M hM]
    exact C2.cast_geom (fun j => normRepCount K (P ^ j) M n) q (2 * M - 1) _
      (fun j hj => normRepCount_pow_succ_inert hK hP hc M j hM hj n hn hnP q hq) h1 k hk
  · intro hc
    have hN : ((Ideal.absNorm P : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN0
    have h1 : ((normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ 1) M n : ℕ) : ℝ) =
        (Ideal.absNorm P : ℝ) ^ (2 * M - 1) * (1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ))) := by
      rw [pow_one]
      have h3 := normRepCount_split_one hK hP hc M hM n hn hnP
      have h2 : ((normRepCount K (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) M n : ℕ) : ℝ) =
          (Ideal.absNorm P : ℝ) ^ (2 * M - 1) - (Ideal.absNorm P : ℝ) ^ (M - 1) := by
        exact_mod_cast h3
      rw [h2, C2.split_alg _ hN M hM]
    exact C2.cast_geom (fun j => normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ j) M n)
      (Ideal.absNorm P) (2 * M - 1) _
      (fun j hj => normRepCount_pow_succ_split hK hP hc M j hM hj n hn hnP) h1 k hk

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem normRepCount_eq_eulerFac_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) :
    (normRepCount K (P ^ k) M n : ℝ) =
      Real.sqrt (Ideal.absNorm P : ℝ) ^ ((2 * M - 1) * k) * (Formalism.HermitianLatticesTheory.eulerFac K M P)⁻¹ := by
  rw [(localDensity K hK P hP M k hM hk n hn hnP).1 hc, Formalism.HermitianLatticesTheory.eulerFac, if_pos hc, inv_inv]

theorem normRepCount_eq_eulerFac_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) :
    (normRepCount K ((P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ^ k) M n : ℝ) =
      (Ideal.absNorm P : ℝ) ^ ((2 * M - 1) * k) *
        (Formalism.HermitianLatticesTheory.eulerFac K M P * Formalism.HermitianLatticesTheory.eulerFac K M (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P))⁻¹ := by
  have hc' : Formalism.HermitianLatticesTheory.conjIdeal (K := K) (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) ≠ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P :=
    fun h => hc ((conjIdeal_conjIdeal hK P).symm.trans h).symm
  have hPbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)
  have hN0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hPbot
  have hN1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact hP.ne_top
  have hN2 : (1 : ℝ) < (Ideal.absNorm P : ℝ) := by
    have : 2 ≤ Ideal.absNorm P := by omega
    exact_mod_cast (by omega : 1 < Ideal.absNorm P)
  have hx : 0 < 1 - (Ideal.absNorm P : ℝ) ^ (-(M : ℤ)) := by
    rw [zpow_neg, zpow_natCast, sub_pos]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hN2 (by omega))
  rw [(localDensity K hK P hP M k hM hk n hn hnP).2 hc, Formalism.HermitianLatticesTheory.eulerFac, Formalism.HermitianLatticesTheory.eulerFac, if_neg hc,
    if_neg hc', absNorm_conjIdeal hK, ← Real.rpow_add hx,
    show (-(1 : ℝ) / 2 + -(1 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one, inv_inv]

end Formalism.HermitianLattices.Ext.L3
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

theorem hermRepUnram [Fact HermRepUnram] : HermRepUnram := Fact.out

theorem orthBasisPos : OrthBasisPos := orthBasisPos_holds

end Formalism.HermitianLattices.Ext.L3
end
end

section

open NumberField

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K : Type} [Field K] [NumberField K] [StarRing K]

namespace BE

theorem exists_gen {R : Type*} [CommRing R] [IsDedekindDomain R] {I P Q : Ideal R} (hI : I ≠ ⊥)
    (hP : P.IsPrime) (hQ : Q.IsPrime) :
    ∃ r ∈ I, r ≠ 0 ∧ ∃ s : R, s ∉ P ∧ s ∉ Q ∧ ∀ x ∈ I, ∃ y : R, s * x = r * y := by
  have hIP : ∀ {P' : Ideal R}, P'.IsPrime → ¬ (I ≤ I * P') := by
    intro P' hP' hle
    have e : I * P' = I * ⊤ := by
      rw [Ideal.mul_top]
      exact le_antisymm (Ideal.mul_le_inf.trans inf_le_left) hle
    exact hP'.ne_top (mul_left_cancel₀ (by rwa [Ideal.zero_eq_bot]) e)
  have hnot : ¬ ((I : Set R) ⊆ ((I * P : Ideal R) : Set R) ∪ ((I * Q : Ideal R) : Set R)) := by
    rw [Ideal.subset_union]
    rintro (h | h)
    · exact hIP hP h
    · exact hIP hQ h
  obtain ⟨r, hrI, hr⟩ := Set.not_subset.mp hnot
  simp only [Set.mem_union, SetLike.mem_coe, not_or] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hr.1 (Submodule.zero_mem _)
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {r} :=
    Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrI))
  have hJP : ∀ {P' : Ideal R}, r ∉ I * P' → ¬ (J ≤ P') := by
    intro P' hr' hJ'
    apply hr'
    have hrr : r ∈ Ideal.span {r} := Ideal.mem_span_singleton_self r
    rw [hJ] at hrr
    exact Ideal.mul_mono_right hJ' hrr
  have hnot2 : ¬ ((J : Set R) ⊆ (P : Set R) ∪ (Q : Set R)) := by
    rw [Ideal.subset_union]
    rintro (h | h)
    · exact hJP hr.1 h
    · exact hJP hr.2 h
  obtain ⟨s, hsJ, hs⟩ := Set.not_subset.mp hnot2
  simp only [Set.mem_union, SetLike.mem_coe, not_or] at hs
  refine ⟨r, hrI, hr0, s, hs.1, hs.2, fun x hx => ?_⟩
  have hmem : s * x ∈ Ideal.span {r} := by
    rw [hJ, mul_comm s x]
    exact Ideal.mul_mem_mul hx hsJ
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨y, by rw [← hy, mul_comm]⟩

theorem avoid_two {R : Type*} [CommRing R] {P Q : Ideal R} (hQ : Q.IsPrime) {a s m : R} (k : R)
    (ha : a ∈ P) (hsP : s ∉ P) (hsQ : s ∉ Q) (hm : m ∉ Q) :
    (s - k * a ∉ P ∧ s - k * a ∉ Q) ∨ (s - (k + m) * a ∉ P ∧ s - (k + m) * a ∉ Q) := by
  have hP : ∀ c : R, s - c * a ∉ P := fun c hc => hsP (by
    have := P.add_mem hc (P.mul_mem_left c ha)
    simpa using this)
  by_cases h1 : s - k * a ∈ Q
  · right
    refine ⟨hP _, fun h2 => ?_⟩
    have hma : m * a ∈ Q := by
      have := Q.sub_mem h1 h2
      have e : s - k * a - (s - (k + m) * a) = m * a := by ring
      rwa [e] at this
    rcases hQ.mem_or_mem hma with h | h
    · exact hm h
    · exact hsQ (by
        have := Q.add_mem h1 (Q.mul_mem_left k h)
        simpa using this)
  · left
    exact ⟨hP _, h1⟩

end BE

theorem principal_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)} (hp : p.IsMaximal)
    (A : AddSubgroup K) (hA : ∀ s ∈ locRing p, ∀ a ∈ A, s * a ∈ A) (h0 : ∃ a ∈ A, a ≠ 0)
    (ht : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ locRing p) :
    ∃ α ∈ A, α ≠ 0 ∧ ∀ a ∈ A, a * α⁻¹ ∈ locRing p := by
  obtain ⟨t, ht0, ht⟩ := ht
  have hpp := hp.isPrime
  let I : Ideal (𝓞 K) :=
    { carrier := {r | algebraMap (𝓞 K) K r * t⁻¹ ∈ A}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, map_add (f := _), add_mul] at *
        exact A.add_mem hx hy
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, mul_assoc] at *
        exact hA _ (algebraMap_mem_locRing p c) _ hx }
  have hmemI : ∀ r : 𝓞 K, r ∈ I ↔ algebraMap (𝓞 K) K r * t⁻¹ ∈ A := fun r => Iff.rfl

  have hrep : ∀ a ∈ A, ∃ x ∈ I, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
      a = algebraMap (𝓞 K) K x / (algebraMap (𝓞 K) K s * t) := by
    intro a ha
    obtain ⟨x, s, hs, hx⟩ := (mem_locR_iff hpp _).1 ((mem_locRing p _).1 (ht a ha))
    have hs0 := algebraMap_ne_zero_of_mem_hcompl hpp hs
    have e : algebraMap (𝓞 K) K x = algebraMap (𝓞 K) K s * (t * a) := by
      rw [hx]; field_simp
    refine ⟨x, ?_, s, hs, ?_⟩
    · rw [hmemI, e]
      have : algebraMap (𝓞 K) K s * (t * a) * t⁻¹ = algebraMap (𝓞 K) K s * a := by field_simp
      rw [this]
      exact hA _ (algebraMap_mem_locRing p s) _ ha
    · rw [e]; field_simp
  have hI : I ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := h0
    obtain ⟨x, hx, s, hs, e⟩ := hrep a ha
    intro hbot
    rw [hbot, Ideal.mem_bot] at hx
    apply ha0
    rw [e, hx]; simp
  obtain ⟨r, hrI, hr0, s, hsP, hsQ, hgen⟩ := BE.exists_gen hI hpp (conjIdeal_isPrime hpp)
  have hs : s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := (mem_hcompl_iff hpp s).2 ⟨hsP, hsQ⟩
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hpp hs
  have hr0' : algebraMap (𝓞 K) K r ≠ 0 := by
    intro h
    exact hr0 ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).1 h)
  refine ⟨algebraMap (𝓞 K) K r * t⁻¹, (hmemI r).1 hrI, mul_ne_zero hr0' (inv_ne_zero ht0), ?_⟩
  intro a ha
  obtain ⟨x, hx, s', hs', e⟩ := hrep a ha
  have hs0' := algebraMap_ne_zero_of_mem_hcompl hpp hs'
  obtain ⟨y, hy⟩ := hgen x hx
  have hy' : algebraMap (𝓞 K) K s * algebraMap (𝓞 K) K x
      = algebraMap (𝓞 K) K r * algebraMap (𝓞 K) K y := by
    rw [← map_mul, ← map_mul, hy]
  rw [mem_locRing, mem_locR_iff hpp]
  refine ⟨y, s * s', mul_mem hs hs', ?_⟩
  rw [e, map_mul]
  field_simp
  linear_combination hy'

theorem unit_or_locRing {p : Ideal (𝓞 K)} (hp : p.IsPrime) (a : K) (ha : a ∈ locRing p)
    (κ : K) (hκ : κ ∈ locRing p) (μ : K) (hna : a⁻¹ ∉ locRing p) (hμ : IsUnitIn (locRing p) μ) :
    IsUnitIn (locRing p) (1 - κ * a) ∨ IsUnitIn (locRing p) (1 - (κ + μ) * a) := by
  obtain ⟨a₁, s₁, hs₁, ea⟩ := (mem_locR_iff hp _).1 ((mem_locRing p _).1 ha)
  obtain ⟨k₁, s₂, hs₂, ek⟩ := (mem_locR_iff hp _).1 ((mem_locRing p _).1 hκ)
  obtain ⟨m₁, s₃, hs₃, em⟩ := (mem_locR_iff hp _).1 ((mem_locRing p _).1 hμ.2.1)
  have h1 := algebraMap_ne_zero_of_mem_hcompl hp hs₁
  have h2 := algebraMap_ne_zero_of_mem_hcompl hp hs₂
  have h3 := algebraMap_ne_zero_of_mem_hcompl hp hs₃
  have hm₁ : m₁ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := (isUnitIn_div_iff hp m₁ hs₃).1 (em ▸ hμ)
  have ha₁ : a₁ ∉ Formalism.HermitianLatticesTheory.hcompl (K := K) p := by
    intro h
    have := (isUnitIn_div_iff hp a₁ hs₁).2 h
    rw [← ea] at this
    exact hna this.2.2
  have hQ := conjIdeal_isPrime hp
  set S : 𝓞 K := s₁ * s₂ * s₃ with hS
  have hSm : S ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := mul_mem (mul_mem hs₁ hs₂) hs₃
  have hS' := (mem_hcompl_iff hp S).1 hSm
  have hM : m₁ * s₂ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p := mul_mem hm₁ hs₂
  have hM' := (mem_hcompl_iff hp _).1 hM
  have e1 : (1 - κ * a) = algebraMap (𝓞 K) K (S - (k₁ * s₃) * a₁) / algebraMap (𝓞 K) K S := by
    rw [ea, ek, hS]; simp only [map_sub, map_mul]; field_simp
  have e2 : (1 - (κ + μ) * a)
      = algebraMap (𝓞 K) K (S - (k₁ * s₃ + m₁ * s₂) * a₁) / algebraMap (𝓞 K) K S := by
    rw [ea, ek, em, hS]; simp only [map_sub, map_mul, map_add (f := _)]; field_simp
  rw [e1, e2, isUnitIn_div_iff hp _ hSm, isUnitIn_div_iff hp _ hSm, mem_hcompl_iff hp,
    mem_hcompl_iff hp]
  have hor : a₁ ∈ p ∨ a₁ ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by
    by_contra h
    push Not at h
    exact ha₁ ((mem_hcompl_iff hp a₁).2 h)
  rcases hor with h | h
  · exact BE.avoid_two hQ (k₁ * s₃) h hS'.1 hS'.2 hM'.2
  · rcases BE.avoid_two hp (k₁ * s₃) h hS'.2 hS'.1 hM'.1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm

theorem isHermSemilocal_locRing (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {p : Ideal (𝓞 K)}
    (hp : p.IsMaximal) : IsHermSemilocal (locRing p) := by
  exact ⟨fun _ ha => star_mem_locRing hp.isPrime ha, frac_locRing p, unram_locRing hK hp,
    principal_locRing hK hp, fun a ha κ hκ μ hna hμ => unit_or_locRing hp.isPrime a ha κ hκ μ hna hμ⟩

end Formalism.HermitianLattices.Ext.L3.WA
end
end
