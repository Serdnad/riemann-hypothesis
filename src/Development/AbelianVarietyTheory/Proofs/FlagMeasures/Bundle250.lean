module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle238
public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle227
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle243
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle152
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.GlueZ

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem star_mem {t : K} (h : t ∈ (1 : Submodule (𝓞 K) K)) : star t ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 h
  have h1 : IsIntegral ℤ (star (algebraMap (𝓞 K) K a)) :=
    map_isIntegral_int (starRingEnd K) a.isIntegral_coe
  exact Submodule.mem_one.2 ⟨⟨_, h1⟩, rfl⟩

def Good (H : HermSpace K V) (S : Submodule K V) (z : V) (M : Submodule (𝓞 K) V) : Prop :=
  dual H M = M ∧ Submodule.span K (M : Set V) = S ∧ ∀ t : K, t • z ∈ M ↔ t ∈ (1 : Submodule (𝓞 K) K)

variable {H : HermSpace K V} {S : Submodule K V} {z : V} {M : Submodule (𝓞 K) V}

theorem Good.z_mem (h : Good H S z M) : z ∈ M := by
  simpa using (h.2.2 1).2 (Submodule.mem_one.2 ⟨1, map_one _⟩)

theorem Good.int (h : Good H S z M) {x y : V} (hx : x ∈ M) (hy : y ∈ M) :
    H.B x y ∈ (1 : Submodule (𝓞 K) K) :=
  ((mem_dual_iff H M x).1 (h.1.symm ▸ hx)).2 y hy

theorem Good.mem_S (h : Good H S z M) {x : V} (hx : x ∈ M) : x ∈ S :=
  h.2.1 ▸ Submodule.subset_span hx

theorem Good.mem_of (h : Good H S z M) {x : V} (hx : x ∈ S)
    (hB : ∀ y ∈ M, H.B x y ∈ (1 : Submodule (𝓞 K) K)) : x ∈ M :=
  h.1 ▸ (mem_dual_iff H M x).2 ⟨h.2.1.symm ▸ hx, hB⟩

theorem Good.exists_one (h : Good H S z M) (hz : H.B z z ≠ 0) : ∃ y ∈ M, H.B y z = 1 := by
  let J : Ideal (𝓞 K) :=
    (M.map ((H.B.flip z).restrictScalars (𝓞 K))).comap (Algebra.linearMap (𝓞 K) K)
  have hJ : ∀ a : 𝓞 K, a ∈ J ↔ ∃ y ∈ M, H.B y z = algebraMap (𝓞 K) K a := fun a => by
    simp [J]
  have hne : J ≠ ⊥ := by
    intro h0
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int h.z_mem h.z_mem)
    have : a ∈ J := (hJ a).2 ⟨z, h.z_mem, ha.symm⟩
    rw [h0, Ideal.mem_bot] at this
    exact hz (by rw [← ha, this, map_zero])
  have htop : J = ⊤ := by
    by_contra hJ1
    obtain ⟨x, hx, hx1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := K) hne hJ1
    apply hx1
    rw [FractionalIdeal.mem_inv_iff (by simpa using hne)] at hx
    have h2 : star x • z ∈ M := by
      refine h.mem_of (S.smul_mem _ (h.mem_S h.z_mem)) fun y hy => ?_
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int hy h.z_mem)
      have h3 := hx (algebraMap (𝓞 K) K a)
        (FractionalIdeal.mem_coeIdeal_of_mem _ ((hJ a).2 ⟨y, hy, ha.symm⟩))
      have h4 : x * algebraMap (𝓞 K) K a ∈ (1 : Submodule (𝓞 K) K) := by
        obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h3
        exact Submodule.mem_one.2 ⟨b, hb⟩
      have h5 := star_mem h4
      rw [ha, star_mul', H.herm] at h5
      simpa using h5
    have h6 := star_mem ((h.2.2 _).1 h2)
    rw [star_star] at h6
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 h6
    exact (FractionalIdeal.mem_one_iff _).2 ⟨b, hb⟩
  obtain ⟨y, hy, e⟩ := (hJ 1).1 (htop ▸ Submodule.mem_top)
  exact ⟨y, hy, by rw [e, map_one]⟩

theorem Good.proj (h : Good H S z M) {y m : V} (hy : y ∈ M) (hy1 : H.B y z = 1) (hm : m ∈ M) :
    ∃ a : 𝓞 K, m - a • y ∈ M ∧ H.B (m - a • y) z = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h.int hm h.z_mem)
  refine ⟨a, M.sub_mem hm (M.smul_mem a hy), ?_⟩
  rw [← algebraMap_smul K a y, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hy1, ← ha]
  simp

theorem count (T : ℕ) (hT : T ≠ 0) (hz : H.B z z = -(T : K)) (M₁ : Submodule (𝓞 K) V) (h₁ : Good H S z M₁) :
    {M : Submodule (𝓞 K) V | Good H S z M ∧ ∀ y, H.B y z = 0 → (y ∈ M ↔ y ∈ M₁)}.encard ≤
      (T ^ Module.finrank ℚ K : ℕ) := by
  have hz0 : H.B z z ≠ 0 := by rw [hz]; simpa using hT
  obtain ⟨y₁, hy₁, e₁⟩ := h₁.exists_one hz0
  have e₁' : H.B z y₁ = 1 := by rw [← H.herm, e₁, star_one]
  set 𝓢 := {M : Submodule (𝓞 K) V | Good H S z M ∧ ∀ y, H.B y z = 0 → (y ∈ M ↔ y ∈ M₁)} with h𝓢
  have key : ∀ M : Submodule (𝓞 K) V, ∃ (y : V) (u : K) (a : 𝓞 K), M ∈ 𝓢 →
      y ∈ M ∧ H.B y z = 1 ∧ y + u • z ∈ M₁ ∧ algebraMap (𝓞 K) K a = 1 - u * T := by
    intro M
    by_cases hM : M ∈ 𝓢
    swap
    · exact ⟨0, 0, 0, fun h => absurd h hM⟩
    obtain ⟨y, hy, e⟩ := hM.1.exists_one hz0
    have hm : y + (-H.B y y₁) • z ∈ M₁ := by
      refine h₁.mem_of (S.add_mem (hM.1.mem_S hy) (S.smul_mem _ (h₁.mem_S h₁.z_mem))) fun m hm => ?_
      obtain ⟨a, ha, ha0⟩ := h₁.proj hy₁ e₁ hm
      have h2 := hM.1.int hy ((hM.2 _ ha0).2 ha)
      have h3 : H.B z (m - a • y₁) = 0 := by rw [← H.herm, ha0, star_zero]
      have h4 : m = (m - a • y₁) + (algebraMap (𝓞 K) K a) • y₁ := by rw [algebraMap_smul]; abel
      generalize m - a • y₁ = m₀ at h2 h3 h4
      rw [h4]
      simp only [map_add (f := _), LinearMap.add_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, h3, e₁',
        smul_eq_mul]
      convert h2 using 1
      ring
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 (h₁.int hm h₁.z_mem)
    refine ⟨y, -H.B y y₁, a, fun _ => ⟨hy, e, hm, ?_⟩⟩
    rw [ha, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, e, hz, smul_eq_mul]
    ring
  choose y u a hyu using key
  let I : Ideal (𝓞 K) := Ideal.span {(T : 𝓞 K)}
  have hle : ∀ M ∈ 𝓢, ∀ M' ∈ 𝓢, Ideal.Quotient.mk I (a M) = Ideal.Quotient.mk I (a M') → M ≤ M' := by
    intro M hM M' hM' e
    obtain ⟨p1, p2, p3, p4⟩ := hyu M hM
    obtain ⟨q1, q2, q3, q4⟩ := hyu M' hM'
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 e)
    have hb' : algebraMap (𝓞 K) K b = u M' - u M := by
      have := congrArg (algebraMap (𝓞 K) K) hb
      rw [map_sub, map_mul, map_natCast, p4, q4] at this
      have hT' : (T : K) ≠ 0 := by exact_mod_cast hT
      apply mul_right_cancel₀ hT'
      rw [this]; ring
    have h5 : y M - y M' ∈ M₁ := by
      have := M₁.add_mem (M₁.sub_mem p3 q3) (M₁.smul_mem b h₁.z_mem)
      rw [← algebraMap_smul K b z, hb', sub_smul] at this
      convert this using 1
      abel
    have h6 : H.B (y M - y M') z = 0 := by rw [map_sub, LinearMap.sub_apply, p2, q2, sub_self]
    have h7 : y M ∈ M' := by simpa using M'.add_mem ((hM'.2 _ h6).2 h5) q1
    intro m hm
    obtain ⟨c, hc, hc0⟩ := hM.1.proj p1 p2 hm
    simpa using M'.add_mem ((hM'.2 _ hc0).2 ((hM.2 _ hc0).1 hc)) (M'.smul_mem c h7)
  have hI : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hT
  haveI : Finite (𝓞 K ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  have h8 : 𝓢.encard ≤ (Set.univ : Set (𝓞 K ⧸ I)).encard :=
    Set.encard_le_encard_of_injOn (f := fun M => Ideal.Quotient.mk I (a M)) (fun _ _ => Set.mem_univ _)
      fun M hM M' hM' e => le_antisymm (hle M hM M' hM' e) (hle M' hM' M hM e.symm)
  refine h8.trans (le_of_eq ?_)
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    Ideal.absNorm_span_natCast, RingOfIntegers.rank]

theorem mem_lattice_zeroTorus {r : ℕ} (N : NF H r) (Λ : Submodule (𝓞 K) V) (y : V) (hy : H.B y N.F'.z = 0) :
    y ∈ latL N.F' N.F Λ ↔ y ∈ flagPairDefinitePartLattice N.F' N.F Λ := by
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  have hc : star N.c ≠ 0 := by
    intro h0
    have := N.c_norm
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have e : N.F'.z = N.c • N.F.z := N.same (Fin.last r) N.j_le
  have hy2 : H.B y N.F.z = 0 := by
    rw [e, LinearMap.map_smulₛₗ, smul_eq_mul] at hy
    exact (mul_eq_zero.1 hy).resolve_left hc
  have h1 : ∀ x ∈ N.F'.X ⊔ N.F.X, H.B y x = 0 := (mem_perp_iff H _ y).1 h.1
  refine (mem_perp_iff H _ y).2 fun x hx => ?_
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hx
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hq
  simp [h1 p hp, hy, hy2, LinearMap.map_smulₛₗ]

end GlobalTheory.DegCnt.GlueZ

theorem GlobalTheory.DegCnt.GlueZ.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ((({L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧ flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (N.NT ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  have good : ∀ Λ', N.IsTerm g Λ' → GlueZ.Good H (uPerp N.F N.F') N.F'.z (latL N.F' N.F Λ') := fun Λ' h => by
    obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ' hg h
    exact ⟨h2.2, h2.1.2, h4⟩
  have hT : N.T ≠ 0 := by
    intro h0
    apply N.F'.hT
    rw [N.hT', h0, Nat.cast_zero]
  have hz : H.B N.F'.z N.F'.z = -(N.T : K) := N.hT' ▸ N.F'.zz
  have h1 := GlueZ.count N.T hT hz _ (good Λ hΛ)
  have h2 : {L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧
      flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ}.encard ≤ (N.T ^ Module.finrank ℚ K : ℕ) := by
    refine (Set.encard_le_encard ?_).trans h1
    rintro _ ⟨Λ', h, rfl, e⟩
    exact ⟨good Λ' h, fun y hy => by rw [GlueZ.mem_lattice_zeroTorus N Λ' y hy, GlueZ.mem_lattice_zeroTorus N Λ y hy, e]⟩
  haveI := hK.1
  have h3 : Module.finrank ℚ K = Formalism.HermitianLatticesTheory.fDeg K * 2 := by
    rw [IsTotallyComplex.finrank, Formalism.HermitianLatticesTheory.fDeg, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero]
    ring
  refine (ENat.toENNReal_le.2 h2).trans (le_of_eq ?_)
  rw [NF.NT, ← pow_mul, ← h3, ← Nat.cast_pow, ENNReal.ofReal_natCast]
  rfl
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagBase.SiegelUnfold


open Filter Topology in
theorem lseriesSummable_idealCount (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1) ?_ (fun _ => Nat.cast_nonneg _)
    zero_le_one hs
  have h : Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  simp only [Real.rpow_one]
  exact Asymptotics.isBigO_of_div_tendsto_nhds (by
    filter_upwards [eventually_gt_atTop 0] with n hn h0
    exact absurd (Nat.cast_eq_zero.1 h0) hn.ne') _ h

theorem hasSum_zetaE (K : Type) [Field K] [NumberField K] {l : ℕ} (hl : 2 ≤ l) :
    HasSum (fun n : ℕ => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ l)⁻¹)
      (zetaE K l) := by
  have hs : 1 < ((l : ℂ)).re := by
    rw [Complex.natCast_re]; exact_mod_cast hl
  have h := Complex.hasSum_re (lseriesSummable_idealCount K hs).hasSum
  unfold zetaE dedekindZeta LSeries
  simp only [Complex.ofReal_natCast] at h
  convert h using 2 with n
  rcases eq_or_ne n 0 with rfl | hn
  · have : l ≠ 0 := by omega
    simp [this]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_natCast, div_eq_mul_inv, ← Complex.ofReal_natCast,
      ← Complex.ofReal_natCast n, ← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.ofReal_re]

theorem tsum_absNorm_pow_inv (K : Type) [Field K] [NumberField K] {l : ℕ} (hl : 2 ≤ l) :
    ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥}, ENNReal.ofReal (((Ideal.absNorm 𝔞.1 : ℝ) ^ l)⁻¹) =
      ENNReal.ofReal (zetaE K l) := by
  have hl0 : l ≠ 0 := by omega
  have h1 : ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥}, ENNReal.ofReal (((Ideal.absNorm 𝔞.1 : ℝ) ^ l)⁻¹) =
      ∑' 𝔞 : Ideal (𝓞 K), ENNReal.ofReal (((Ideal.absNorm 𝔞 : ℝ) ^ l)⁻¹) := by
    refine tsum_subtype_eq_of_support_subset (s := {𝔞 : Ideal (𝓞 K) | 𝔞 ≠ ⊥})
      (f := fun 𝔞 : Ideal (𝓞 K) => ENNReal.ofReal (((Ideal.absNorm 𝔞 : ℝ) ^ l)⁻¹)) ?_
    rintro 𝔞 h rfl
    exact h (by simp [hl0])
  have h := hasSum_zetaE K hl
  rw [h1, ← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) h.summable,
    ← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).tsum_eq, ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  have key : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ENNReal.ofReal (((Ideal.absNorm
        (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I) ⟨n, I⟩) : ℝ) ^ l)⁻¹) =
      ENNReal.ofReal (((n : ℝ) ^ l)⁻¹) := by
    rintro ⟨I, rfl⟩; rfl
  haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  haveI := Fintype.ofFinite {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  rw [tsum_congr key, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, Nat.card_eq_fintype_card]

def sumLat (E : Type) [Field E] [NumberField E] (k : ℕ) (𝔞 : Ideal (𝓞 E))
    (Λ' : Submodule (𝓞 E) (Fin k → E)) : Submodule (𝓞 E) (Fin (k + 1) → E) where
  carrier := {y | (∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Fin.tail y ∈ Λ'}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun t ht => ?_, Λ'.add_mem ha' hb'⟩
    rw [Pi.add_apply, mul_add]
    exact add_mem (ha t ht) (hb t ht)
  zero_mem' := ⟨fun t _ => by simp, Λ'.zero_mem⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨fun t ht => ?_, Λ'.smul_mem c ha'⟩
    have := ha (t * c) (𝔞.mul_mem_right c ht)
    simpa [Algebra.smul_def, mul_assoc] using this

theorem latMean_sum_ne_zero : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 2 ≤ j → ∀ (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal), Measurable w → Measurable Φ → latMean E j (fun L => w (covAt E j L) * ∑' x : {x : VecInf E j // x ∈ L ∧ x ≠ 0}, Φ x.1) = glVol E (j - 1) * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * j - 1)) * zetaE E j) * (∫⁻ x, Φ x) * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  intro E _ _ hE j hj w Φ hw hΦ
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hv : 0 ≤ Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * k + 1)) := by
    unfold Formalism.HermitianLatticesTheory.vInv; positivity
  rw [GlobalTheory.T.lineLatticeMean_sum_eq_tsum_pair_orbits E hE k (sumLat E k) (fun _ _ _ => Iff.rfl) w Φ hw hΦ]
  simp only [fun (𝔞 : {𝔞 : Ideal (𝓞 E) // 𝔞 ≠ ⊥})
      (Λ' : {Λ : Submodule (𝓞 E) (Fin k → E) // Submodule.IsFullLattice E Λ}) =>
    GlobalTheory.T.lineLatticeMean_single_pair_orbit_contribution E hE k (by omega) (sumLat E k) (fun _ _ _ => Iff.rfl) w Φ hw hΦ 𝔞.1 Λ'.1 𝔞.2 Λ'.2]
  simp only [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.ofReal_mul hv,
    Nat.add_sub_cancel, show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  rw [tsum_absNorm_pow_inv E hj]
  rfl

end GlobalTheory.FlagBase.SiegelUnfold
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.SeenIso

section General

variable {K U V W : Type} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem exists_proj [StarRing K] {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {h0 : W →ₗ⋆[K] W →ₗ[K] K}
    (ι : W →ₗ[K] V) (hι : ∀ x y, h (ι x) (ι y) = h0 x y) (X H : Submodule K V)
    (hWX : ∀ w, ι w ∈ X → w = 0)
    (hXι : ∀ x ∈ X, ∀ w, h x (ι w) = 0) (hXH : ∀ x ∈ X, ∀ v ∈ H, h x v = 0)
    (hsp : ∀ v ∈ H, ∃ w, v - ι w ∈ X) (hHX : H ⊓ X = ⊥) :
    ∃ π : H →ₗ[K] W, Function.Injective π ∧ (∀ x y, h0 (π x) (π y) = h x y) ∧
      ∀ x : H, (x : V) - ι (π x) ∈ X := by
  obtain ⟨g, hg⟩ := (X.mkQ ∘ₗ ι).exists_leftInverse_of_injective (by
    rw [eq_bot_iff]
    intro w hw
    exact hWX w ((Submodule.Quotient.mk_eq_zero X).1 hw))
  let p : V →ₗ[K] W := g ∘ₗ X.mkQ
  have hpι : ∀ w, p (ι w) = w := fun w => LinearMap.congr_fun hg w
  have hpX : ∀ u ∈ X, p u = 0 := fun u hu => by
    have : X.mkQ u = 0 := (Submodule.Quotient.mk_eq_zero X).2 hu
    simp only [p, LinearMap.comp_apply, this, map_zero]
  have hF : ∀ x : H, (x : V) - ι (p x) ∈ X := fun x => by
    obtain ⟨w, hw⟩ := hsp x x.2
    have := hpX _ hw
    rw [map_sub, hpι, sub_eq_zero] at this
    rwa [this]
  refine ⟨p ∘ₗ H.subtype, ?_, fun x y => ?_, hF⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have h1 : p x = 0 := hx
    have h2 := hF x
    rw [h1, map_zero, sub_zero] at h2
    have h3 : (x : V) ∈ H ⊓ X := ⟨x.2, h2⟩
    rw [hHX] at h3
    exact Subtype.ext h3
  · change h0 (p x) (p y) = _
    have a := hXH _ (hF x) _ y.2
    have b := hXι _ (hF y) (p x)
    have c : h (ι (p x)) ((y : V) - ι (p y)) = 0 := by rw [← hs.eq, b, map_zero]
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at a
    rw [map_sub, sub_eq_zero] at c
    rw [a, c, hι]

variable [NumberField K] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem finrank_span_map (i : U →ₗ[K] V) (hi : Function.Injective i) (N : Submodule (𝓞 K) U) :
    finrank K (Submodule.span K ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) =
      finrank K (Submodule.span K (N : Set U)) := by
  have : ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V) = i '' (N : Set U) := rfl
  rw [this, ← Submodule.map_span]
  exact (Submodule.equivMapOfInjective i hi _).finrank_eq.symm

theorem card_quot_map (i : U →ₗ[K] V) (hi : Function.Injective i) (A B : Submodule (𝓞 K) U) :
    Nat.card (↥(A.map (i.restrictScalars (𝓞 K))) ⧸
      (B.map (i.restrictScalars (𝓞 K))).comap (A.map (i.restrictScalars (𝓞 K))).subtype) =
      Nat.card (A ⧸ B.comap A.subtype) := by
  have := AddSubgroup.relIndex_map_map_of_injective (f := i.toAddMonoidHom) B.toAddSubgroup A.toAddSubgroup hi
  exact this

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (D : D7) (T : D.host.E) (F : Fg D T) (H : Submodule D.host.E (hS D).V), WHyp D F (Wsp D) → H ≤ orth (hS D) (Xplus F) → H ⊓ Xsp F = ⊥ → ∀ N N' : LatV D, N ≤ toO (hS D) H → N' ≤ toO (hS D) H → detW D (seen D F N) = latDet (hS D) N ∧ rkW D (seen D F N) = finrank D.host.E (spanE (hS D) N) ∧ idxW D (seen D F N) (seen D F N') = idx (hS D) N N' := by
  intro D T F H hW hH hHX N N' hN hN'
  have hm : 0 < D.R.m := lt_of_lt_of_le (by norm_num) D.R.two_le_m
  have hiso : ∀ x y, (hS D).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y := D.sp.iXY_isom 0 hm
  have hXι : ∀ x ∈ Xsp F, ∀ w, (hS D).hT x (D.sp.iXY 0 w) = 0 := fun x hx w =>
    (Formalism.MainNotions.mem_orth_iff _ _).1 (hW.1.le (Submodule.mem_sup_left ⟨w, rfl⟩)) x (Submodule.mem_sup_left hx)
  have hWX : ∀ w, D.sp.iXY 0 w ∈ Xsp F → w = 0 := fun w hw =>
    (D.sp.X 0).nondeg.1 w fun y => by rw [← hiso]; exact hXι _ hw y
  obtain ⟨π, hinj, hπ, hF⟩ := exists_proj (hS D).herm (D.sp.iXY 0) hiso (Xsp F) H hWX hXι
    (fun x hx v hv => (Formalism.MainNotions.mem_orth_iff _ _).1 (hH hv) x (Submodule.mem_sup_left hx))
    (fun v hv => by
      obtain ⟨_, ⟨w, rfl⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 (hW.1.ge (hH hv))
      exact ⟨w, by simpa using hx⟩) hHX
  have key : ∀ M : LatV D, M ≤ toO (hS D) H → ∃ M₀ : Submodule (𝓞 D.host.E) H,
      M = M₀.map (H.subtype.restrictScalars (𝓞 D.host.E)) ∧
        seen D F M = M₀.map (π.restrictScalars (𝓞 D.host.E)) := by
    intro M hM
    refine ⟨M.comap (H.subtype.restrictScalars (𝓞 D.host.E)), ?_, ?_⟩
    · ext x
      constructor
      · intro hx
        exact ⟨⟨x, hM hx⟩, hx, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy
    · ext w
      constructor
      · intro hw
        obtain ⟨l, hl, x, hx, e⟩ := Submodule.mem_sup.1 hw
        refine ⟨⟨l, hM hl⟩, hl, ?_⟩
        have e' : l + x = D.sp.iXY 0 w := e
        have h1 := (Xsp F).add_mem (hF ⟨l, hM hl⟩) hx
        have h2 : w - π ⟨l, hM hl⟩ = 0 := hWX _ (by
          rw [map_sub, ← e']
          convert h1 using 1
          abel)
        exact (sub_eq_zero.1 h2).symm
      · rintro ⟨y, hy, rfl⟩
        refine Submodule.mem_sup.2 ⟨y, hy, _, (Xsp F).neg_mem (hF y), ?_⟩
        change _ = D.sp.iXY 0 (π y)
        abel
  obtain ⟨A, rfl, a⟩ := key N hN
  obtain ⟨B, rfl, b⟩ := key N' hN'
  rw [a, b]
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.T.latDetH_map_injective_isometry _ _ _ ((hS D).hT.domRestrict₁₂ H H) _ π hinj hπ A).trans
      (GlobalTheory.T.latDetH_map_injective_isometry _ _ _ ((hS D).hT.domRestrict₁₂ H H) _ H.subtype H.injective_subtype (fun _ _ => rfl) A).symm
  · exact (finrank_span_map π hinj A).trans (finrank_span_map H.subtype H.injective_subtype A).symm
  · exact (card_quot_map π hinj A B).trans (card_quot_map H.subtype H.injective_subtype A B).symm

end GlobalTheory.LoopC.SeenIso
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.slab_measure_squeeze' : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε (maxK ε ∩ flagM ε W) E → (∀ i, (E i)ᴴ = -E i) → ∀ ν : Measure (Formalism.REAL.UJ ε), ν (maxK ε ∩ flagM ε W)ᶜ = 0 → (∀ l ∈ maxK ε ∩ flagM ε W, ν.map (fun g => g * l) = ν) → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η → ∀ᶠ r in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, u * m * k ∈ hsBall ε r → ν (hsBall ε (r / (1 + η))) ≤ ν {l | l * k ∈ slab ε E ρ r} ∧ ν {l | l * k ∈ slab ε E ρ r} ≤ ν (hsBall ε ((1 + η) * r)) := by
  first | exact @GlobalTheory.IwConst.slab_measure_squeeze | exact GlobalTheory.IwConst.slab_measure_squeeze | (intros; apply GlobalTheory.IwConst.slab_measure_squeeze <;> assumption)
end

section

namespace GlobalTheory.DiscreteSeriesConsequences

theorem of_classification : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Dec.LowKMultOne ∧ GlobalTheory.Dec.DSInfChar ∧
    GlobalTheory.Dec.DSExists ∧ GlobalTheory.Dec.DSUnique ∧ GlobalTheory.Published.DiscreteSeriesUpqExists := by
  intro h
  obtain ⟨hE, -, hU, hI, hM, -, -⟩ :=
    GlobalTheory.ClassificationConsequences.consequences_of_dsClass (GlobalTheory.Published.discreteSeriesClassification_iff.1 h)
  exact ⟨hM, hI, hE, hU, GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hE⟩

end GlobalTheory.DiscreteSeriesConsequences
end
