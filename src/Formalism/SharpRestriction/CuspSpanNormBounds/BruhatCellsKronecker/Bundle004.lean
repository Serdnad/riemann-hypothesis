module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle005
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.Int
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option linter.deprecated false

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S NumberField IsDedekindDomain

section General

private theorem absNorm_eq_prime_pow_of_natCast_mem (K : Type) [Field K] [NumberField K] {g : ℕ} (hg : g.Prime)
    (P : Ideal (𝓞 K)) [hP : P.IsMaximal] (hgP : ((g : ℕ) : 𝓞 K) ∈ P) :
    ∃ m, 0 < m ∧ Ideal.absNorm P = g ^ m := by
  have h1 : (Ideal.absNorm P : ℤ) ∣ Algebra.norm ℤ ((g : ℕ) : 𝓞 K) := Ideal.absNorm_dvd_norm_of_mem hgP
  have h2 : Algebra.norm ℤ ((g : ℕ) : 𝓞 K) = (g : ℤ) ^ Module.finrank ℤ (𝓞 K) := by
    rw [← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap]
  rw [h2] at h1
  have h3 : Ideal.absNorm P ∣ g ^ Module.finrank ℤ (𝓞 K) := by exact_mod_cast h1
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hg).mp h3
  refine ⟨m, Nat.pos_of_ne_zero ?_, hm⟩
  rintro rfl
  rw [pow_zero, Ideal.absNorm_eq_one_iff] at hm
  exact hP.ne_top hm

theorem splitsCompl_down (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (g : ℕ)
    (hg : g.Prime) (h : SplitsCompl E g) : SplitsCompl F g := by
  intro P hP hgP
  obtain ⟨Q, hQ, hQl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) P
  have hPQ : P = Q.comap (algebraMap (𝓞 F) (𝓞 E)) := hQl.over
  have hgQ : ((g : ℕ) : 𝓞 E) ∈ Q := by
    have h1 : algebraMap (𝓞 F) (𝓞 E) ((g : ℕ) : 𝓞 F) ∈ Q := by
      rw [← Ideal.mem_comap, ← hPQ]
      exact hgP
    simpa using h1
  obtain ⟨hN, hsq⟩ := h Q hQ hgQ
  refine ⟨?_, ?_⟩
  · obtain ⟨m, hm0, hm⟩ := absNorm_eq_prime_pow_of_natCast_mem F hg P hgP
    have hinj : Function.Injective (Ideal.quotientMap Q (algebraMap (𝓞 F) (𝓞 E)) hPQ.le) :=
      Ideal.quotientMap_injective' hPQ.ge
    have hcQ : Nat.card (𝓞 E ⧸ Q) = g := by
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hN]
    haveI : Finite (𝓞 E ⧸ Q) := Nat.finite_of_card_ne_zero (by rw [hcQ]; exact hg.ne_zero)
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hcQ, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hm] at hle
    have hm1 : m ≤ 1 := by
      by_contra hc
      have h5 : g ^ 1 < g ^ m := Nat.pow_lt_pow_right hg.one_lt (by omega)
      rw [pow_one] at h5
      omega
    rw [hm, show m = 1 by omega, pow_one]
  · intro hsq2
    apply hsq
    have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) P ≤ Q := Ideal.map_le_iff_le_comap.mpr hPQ.le
    have h2 : algebraMap (𝓞 F) (𝓞 E) ((g : ℕ) : 𝓞 F) ∈ Q ^ 2 := by
      rw [sq] at hsq2 ⊢
      have h3 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hsq2
      rw [Ideal.map_mul] at h3
      exact Ideal.mul_mono hle hle h3
    simpa using h2

variable (K : Type) [Field K] [NumberField K]

def plOver (g : ℕ) : Set (HeightOneSpectrum (𝓞 K)) := {p | ((g : ℕ) : 𝓞 K) ∈ p.asIdeal}

theorem span_ne_bot {g : ℕ} (hg : g.Prime) : Ideal.span {(g : ℤ)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hg.ne_zero

theorem span_isMaximal {g : ℕ} (hg : g.Prime) : (Ideal.span {(g : ℤ)}).IsMaximal := by
  haveI := Fact.mk hg
  exact Int.ideal_span_isMaximal_of_prime g

theorem card_primesOver {g : ℕ} (hg : g.Prime) (h : SplitsCompl K g) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {(g : ℤ)}) (𝓞 K)).card = Module.finrank ℚ K := by
  classical
  haveI := span_isMaximal hg
  rw [← Ideal.sum_ramification_inertia (𝓞 K) ℚ K (span_ne_bot hg), Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun P hP => ?_
  have hP' : P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 K) := by
    rw [← IsDedekindDomain.coe_primesOverFinset (span_ne_bot hg)]
    exact hP
  obtain ⟨hPp, hPl⟩ := hP'
  have hgP : ((g : ℕ) : 𝓞 K) ∈ P := by
    have h1 : (g : ℤ) ∈ P.under ℤ := hPl.over ▸ Ideal.mem_span_singleton_self _
    simpa [Ideal.under_def] using h1
  have hne : P ≠ ⊥ := by
    rintro rfl
    simp only [Submodule.mem_bot, Nat.cast_eq_zero] at hgP
    exact hg.ne_zero hgP
  have hmax : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hne hPp
  obtain ⟨hN, hsq⟩ := h P hmax hgP
  have he : (Ideal.span {(g : ℤ)}).ramificationIdx' P = 1 := by
    apply Ideal.ramificationIdx'_spec
    · rw [Ideal.map_span, Set.image_singleton, pow_one, Ideal.span_singleton_le_iff_mem]
      simpa using hgP
    · rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
      simpa using hsq
  have hf : (Ideal.span {(g : ℤ)}).inertiaDeg' P = 1 := by
    have h1 := Ideal.absNorm_eq_pow_inertiaDeg' P hg
    rw [hN] at h1
    have h2 : g ^ (Ideal.span {(g : ℤ)}).inertiaDeg' P = g ^ 1 := by
      rw [pow_one]
      exact h1.symm
    exact Nat.pow_right_injective hg.two_le h2
  rw [he, hf]

theorem image_plOver {g : ℕ} (hg : g.Prime) :
    HeightOneSpectrum.asIdeal '' plOver K g = (IsDedekindDomain.primesOverFinset (Ideal.span {(g : ℤ)}) (𝓞 K) : Set (Ideal (𝓞 K))) := by
  haveI := span_isMaximal hg
  ext P
  rw [IsDedekindDomain.coe_primesOverFinset (span_ne_bot hg)]
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.isPrime, ⟨?_⟩⟩
    refine (span_isMaximal hg).eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    have hv' : ((g : ℕ) : 𝓞 K) ∈ v.asIdeal := hv
    simpa using hv'
  · rintro ⟨hPp, hPl⟩
    have hgP : ((g : ℕ) : 𝓞 K) ∈ P := by
      have h1 : (g : ℤ) ∈ P.under ℤ := hPl.over ▸ Ideal.mem_span_singleton_self _
      simpa [Ideal.under_def] using h1
    have hne : P ≠ ⊥ := by
      rintro rfl
      simp only [Submodule.mem_bot, Nat.cast_eq_zero] at hgP
      exact hg.ne_zero hgP
    exact ⟨⟨P, hPp, hne⟩, hgP, rfl⟩

theorem injOn_asIdeal (s : Set (HeightOneSpectrum (𝓞 K))) : Set.InjOn HeightOneSpectrum.asIdeal s := fun _ _ _ _ h => HeightOneSpectrum.ext h

theorem finite_plOver {g : ℕ} (hg : g.Prime) : (plOver K g).Finite := by
  have h := image_plOver K hg
  exact Set.Finite.of_finite_image (h ▸ Finset.finite_toSet _) (injOn_asIdeal K _)

theorem ncard_plOver {g : ℕ} (hg : g.Prime) (h : SplitsCompl K g) : (plOver K g).ncard = Module.finrank ℚ K := by
  rw [← (injOn_asIdeal K _).ncard_image, image_plOver K hg, Set.ncard_coe_finset,
    card_primesOver K hg h]

theorem finprod_plOver {g : ℕ} (hg : g.Prime) (h : SplitsCompl K g) (φ : ℝ → ℝ) :
    ∏ᶠ p ∈ plOver K g, φ (Ideal.absNorm p.asIdeal : ℝ) = φ g ^ Module.finrank ℚ K := by
  have hfin := finite_plOver K hg
  have hc : ∀ p ∈ plOver K g, φ (Ideal.absNorm p.asIdeal : ℝ) = φ g := by
    intro p hp
    rw [(h p.asIdeal p.isMaximal hp).1]
  rw [finprod_mem_congr rfl hc, finprod_mem_eq_finite_toFinset_prod _ hfin, Finset.prod_const,
    ← Set.ncard_eq_toFinset_card _ hfin, ncard_plOver K hg h]

theorem disjoint_plOver {g g' : ℕ} (hg : g.Prime) (hg' : g'.Prime) (hne : g ≠ g') :
    Disjoint (plOver K g) (plOver K g') := by
  rw [Set.disjoint_left]
  intro p hp hp'
  obtain ⟨a, b, hab⟩ : IsCoprime (g : ℤ) (g' : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hg hg').mpr hne)
  apply p.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a * g + b * g' : ℤ) : 𝓞 K) = 1 := by rw [hab]; simp
  rw [← h1]
  push_cast
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ hp')

end General

section Record

variable (D : D7)

theorem finrank_hostF_eq : Module.finrank ℚ D.host.F = D.R.f := by
  rw [D.host.der.finrank_F]
  rfl

theorem typedPl_eq : typedPl D = plOver D.host.F (D.host.g 0) ∪ plOver D.host.F (D.host.g 1) := rfl

theorem finprod_typedPl (h0 : SplitsE D (D.host.g 0)) (h1 : SplitsE D (D.host.g 1)) (φ : ℝ → ℝ) :
    ∏ᶠ p ∈ typedPl D, φ (Ideal.absNorm p.asIdeal : ℝ) =
      φ (D.host.g 0 : ℝ) ^ D.R.f * φ (D.host.g 1 : ℝ) ^ D.R.f := by
  have hF0 : SplitsCompl D.host.F (D.host.g 0) := splitsCompl_down D.host.F D.host.E _ (D.host.g_prime 0) h0
  have hF1 : SplitsCompl D.host.F (D.host.g 1) := splitsCompl_down D.host.F D.host.E _ (D.host.g_prime 1) h1
  rw [typedPl_eq, finprod_mem_union (disjoint_plOver _ (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne)
    (finite_plOver _ (D.host.g_prime 0)) (finite_plOver _ (D.host.g_prime 1)),
    finprod_plOver _ (D.host.g_prime 0) hF0, finprod_plOver _ (D.host.g_prime 1) hF1, finrank_hostF_eq]

theorem gaG_eq (h0 : SplitsE D (D.host.g 0)) (h1 : SplitsE D (D.host.g 1)) :
    gaG D = (∏ i ∈ Finset.Icc 1 D.R.k, ((D.host.g 0 : ℝ) ^ i - 1)) ^ D.R.f *
      (∏ i ∈ Finset.Icc 1 D.R.k, ((D.host.g 1 : ℝ) ^ i - 1)) ^ D.R.f := by
  unfold gaG
  exact finprod_typedPl D h0 h1 (fun x : ℝ => ∏ i ∈ Finset.Icc 1 D.R.k, (x ^ i - 1))

end Record

end Formalism.MainNotions.BridgeLemma

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Finset MeasureTheory
open scoped InnerProductSpace

private theorem szh_sf_inner_lemma (N : ℕ) (a : Fin N) :
    ∏ b ∈ univ.filter (fun b : Fin N => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ((N - ((a : ℕ) + 1)).factorial : ℝ) := by
  rw [Finset.prod_nbij (fun b : Fin N => (b : ℕ)) (t := Finset.Ico ((a : ℕ) + 1) N)
    (g := fun j : ℕ => ((j : ℝ) - ((a : ℕ) : ℝ))) ?_ ?_ ?_ ?_]
  · rw [Finset.prod_Ico_eq_prod_range]
    have e : ∀ k ∈ range (N - ((a : ℕ) + 1)),
        ((((a : ℕ) + 1 + k : ℕ) : ℝ) - ((a : ℕ) : ℝ)) = ((k + 1 : ℕ) : ℝ) := by
      intro k _
      push_cast
      ring
    rw [Finset.prod_congr rfl e, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    simp only [Finset.mem_Ico]
    exact ⟨hb, b.2⟩
  · intro x _ y _ hxy
    exact Fin.ext hxy
  · intro j hj
    simp only [Finset.coe_Ico, Set.mem_Ico] at hj
    refine ⟨⟨j, hj.2⟩, ?_, rfl⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    show (a : ℕ) < j
    omega
  · intro b _
    rfl

theorem szh_sf (N : ℕ) :
    ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ range N, (i.factorial : ℝ) := by
  simp_rw [szh_sf_inner_lemma]
  refine (Fin.prod_univ_eq_prod_range (fun i : ℕ => ((N - (i + 1)).factorial : ℝ)) N).trans ?_
  refine Eq.trans ?_ (Finset.prod_range_reflect (fun i : ℕ => (i.factorial : ℝ)) N)
  apply Finset.prod_congr rfl
  intro i _
  show ((N - (i + 1)).factorial : ℝ) = ((N - 1 - i).factorial : ℝ)
  rw [show N - (i + 1) = N - 1 - i by omega]

theorem szh_fdegHC {N : ℕ} (lam : Fin N → ℝ) (h : StrictAnti lam) :
    Formalism.QuantumDeterminants.fdegHC lam = vand lam / ∏ i ∈ range N, (i.factorial : ℝ) := by
  unfold Formalism.QuantumDeterminants.fdegHC vand
  rw [szh_sf]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact abs_of_pos (sub_pos.mpr (h hb))

theorem szh_vand_nonneg {N : ℕ} (lam : Fin N → ℝ) (h : StrictAnti lam) : 0 ≤ vand lam := by
  unfold vand
  apply Finset.prod_nonneg
  intro a _
  apply Finset.prod_nonneg
  intro b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact sub_nonneg.mpr (h hb).le

section Rec

variable (D : D7)

theorem szh_lam_node (τ : D.what₂.Tau) (a : Fin (2 * D.R.rS + D.R.k + 1)) (h : ¬ a.1 < D.R.k - 1) :
    lamSH D.R (D.hc τ) a = -bOne D τ (a.1 - (D.R.k - 1) + 1) := by
  unfold lamSH lamS bOne
  simp [h]
  split_ifs <;> simp

theorem szh_eps_cloud (a : Fin (2 * D.R.rS + D.R.k + 1)) (h : a.1 < D.R.k - 1) : epsSH D.R a = true := by
  unfold epsSH epsS
  simp [h]

theorem szh_eps_first (a : Fin (2 * D.R.rS + D.R.k + 1)) (h : a.1 = D.R.k - 1) : epsSH D.R a = true := by
  unfold epsSH epsS
  simp [h]

variable {D} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ}

theorem szh_anti (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (τ : D.what₂.Tau) : StrictAnti (lamSH D.R (D.hc τ)) := by
  have hr := dimS_eq D.R
  unfold StandingHypotheses at hH
  simp only [] at hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd, -, -, hCl⟩ := hH
  have hk0 : (0 : ℝ) < D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < D.R.k)
  have hm0 : (0 : ℝ) < D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 0 < D.R.m)
  have hpos : 0 < Cl * ↑D.R.k * ↑D.R.m ^ 4 + ↑D.R.r * ↑D.R.m ^ 10 :=
    add_pos_of_pos_of_nonneg (mul_pos (mul_pos hCl hk0) (pow_pos hm0 4)) (by positivity)
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  unfold lamSH
  have h := hd τ (Fin.cast hr (Fin.castSucc i))
    (by have := i.2; simp only [Fin.coe_cast, Fin.coe_castSucc]; omega)
  have e : ∀ hh, (⟨(Fin.cast hr (Fin.castSucc i) : ℕ) + 1, hh⟩ : Fin D.R.r) = Fin.cast hr i.succ :=
    fun hh => Fin.ext (by simp)
  rw [e] at h
  linarith

theorem szh_hc (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.IsHCParam (lamSH D.R (D.hc τ)) := by
  refine ⟨szh_anti hH τ, fun a => ?_⟩
  obtain ⟨j, hj⟩ := D.R.k_even
  have hn : (((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) - 1) / 2 = ((D.R.rS + j : ℕ) : ℝ) := by
    rw [hj]
    push_cast
    ring
  rw [hn]
  unfold lamSH lamS
  split_ifs with h1 h2
  · obtain ⟨z, hz⟩ := (D.hc τ).v_int ⟨_, h1⟩
    exact ⟨z - ((D.R.rS + j : ℕ) : ℤ), by rw [hz]; push_cast; ring⟩
  · obtain ⟨z, hz⟩ := (D.hc τ).b_int ⟨_, h2⟩
    exact ⟨-z - ((D.R.rS + j : ℕ) : ℤ), by rw [hz]; push_cast; ring⟩
  · exact ⟨-((D.R.rS + j : ℕ) : ℤ), by push_cast; ring⟩

theorem szh_gap (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc τ))
      (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L) := by
  have hr := dimS_eq D.R
  have hrdef : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hkm := D.R.m_add_three_le_k
  have hanti := szh_anti hH τ
  unfold StandingHypotheses at hH
  simp only [] at hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap, -⟩ := hH
  have key : ∀ a b : Fin (2 * D.R.rS + D.R.k + 1), a < b → epsSH D.R a ≠ epsSH D.R b →
      Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ≤
        lamSH D.R (D.hc τ) a - lamSH D.R (D.hc τ) b := by
    intro a b hab he
    have hab' : (a : ℕ) < b := hab
    have hbo := b.2
    have hb1 : ¬ (b : ℕ) < D.R.k - 1 := by
      intro h1
      exact he (by rw [szh_eps_cloud D a (by omega), szh_eps_cloud D b h1])
    have hb2 : (b : ℕ) ≠ D.R.k - 1 := by
      intro h2
      exact he (by rw [szh_eps_cloud D a (by omega), szh_eps_first D b h2])
    have hac : a ≤ (⟨(b : ℕ) - 1, by omega⟩ : Fin (2 * D.R.rS + D.R.k + 1)) := by
      show (a : ℕ) ≤ (b : ℕ) - 1
      omega
    have hlac := hanti.antitone hac
    have e1 := szh_lam_node D τ ⟨(b : ℕ) - 1, by omega⟩ (by show ¬ (b : ℕ) - 1 < D.R.k - 1; omega)
    have e2 := szh_lam_node D τ b hb1
    have i1 : (b : ℕ) - 1 - (D.R.k - 1) + 1 = (b : ℕ) - (D.R.k - 1) := by omega
    simp only [i1] at e1
    have hg := hgap τ ((b : ℕ) - (D.R.k - 1)) (by omega) (by omega)
    linarith
  intro a b hab
  rcases lt_trichotomy a b with h | h | h
  · exact (key a b h hab).trans (le_abs_self _)
  · subst h
    exact absurd rfl hab
  · rw [abs_sub_comm]
    exact (key b a h (Ne.symm hab)).trans (le_abs_self _)

theorem szh_b_sq (large₂ : SizeData₂ D) : large₂.sc.b ^ (2 : ℝ) = Real.exp (2 * large₂.sc.L) := by
  unfold Formalism.BasicNotions.Scale.b
  rw [← Real.exp_mul]
  congr 1
  ring

theorem szh_k_le (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (h1 : 1 ≤ Cl) (τ : D.what₂.Tau) :
    (D.R.k : ℝ) ≤ Real.exp (2 * large₂.sc.L) := by
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkC : (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ Cl := by
    calc (D.R.k : ℝ) = (D.R.k : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (D.R.k : ℝ) ^ Cl := Real.rpow_le_rpow_of_exponent_le hk1 h1
  unfold StandingHypotheses at hH
  simp only [] at hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hb, -⟩ := hH
  have hj := hb τ 1 le_rfl (by have := D.R.two_le_m; omega)
  refine hkC.trans ((le_max_left _ _).trans (hj.1.trans (hj.2.trans (le_of_eq ?_))))
  first
    | exact szh_b_sq large₂
    | (unfold Formalism.BasicNotions.Scale.b; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring)

end Rec

end Formalism.MainNotions.BridgeLemma

end
end
