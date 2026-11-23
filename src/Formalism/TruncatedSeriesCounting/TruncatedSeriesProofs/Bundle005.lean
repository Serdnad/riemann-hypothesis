module

public import Formalism.TruncatedSeriesCounting.Bundle001
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.Bundle002
public import Formalism.TruncatedSeriesCounting.Bundle002
public import Formalism.WindowSums.PowerSeriesRelationList
public import Formalism.TruncatedSeriesCounting.StatementX
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

noncomputable section

namespace Formalism.TruncatedSeriesCounting.R9

theorem length_quotient_le_of_pow_smul : LengthQuotientLeOfPowSMul := by
  intro O _ _ _ M _ _ _ _ ℓ e e' FFs J h1 h2
  set A := FFs ⊔ Ideal.span {ℓ ^ e'} • (⊤ : Submodule O M) with hA
  have hx : ∀ x ∈ A, ℓ ^ e • x ∈ J := by
    intro x hxA
    obtain ⟨f, hf, m, hm, rfl⟩ := Submodule.mem_sup.1 hxA
    rw [smul_add]
    exact J.add_mem (h1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hf))
      (J.smul_mem _ (h2 hm))
  have hS := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.submodule_generator_count O M ℓ e A J hx
  let f : (A ⧸ J.comap A.subtype) →ₗ[O] M ⧸ J := (J.comap A.subtype).mapQ J A.subtype le_rfl
  let g : (M ⧸ J) →ₗ[O] M ⧸ (A ⊔ J) :=
    J.mapQ (A ⊔ J) LinearMap.id (fun x hx => Submodule.mem_sup_right hx)
  have hf : Function.Injective f := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    simp only [f, Submodule.mapQ_apply, Submodule.Quotient.eq] at hxy ⊢
    simpa using hxy
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk m, rfl⟩
  have hex : Function.Exact f g := by
    intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hm
      obtain ⟨a, ha, j, hj, rfl⟩ := Submodule.mem_sup.1 hm
      refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
      simp only [f, Submodule.mapQ_apply, Submodule.coe_subtype]
      rw [Submodule.Quotient.eq]
      simpa using J.neg_mem hj
    · rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      simp only [f, Submodule.mapQ_apply, Submodule.coe_subtype, Submodule.Quotient.eq] at hx
      have e1 : m = (a : M) - ((a : M) - m) := by abel
      rw [e1]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left a.2) (Submodule.mem_sup_right hx)
  have hlen := Module.length_eq_add_of_exact f g hf hg hex
  have hq : Module.length O (M ⧸ (A ⊔ J)) ≤ Module.length O (M ⧸ A) := by
    refine Module.length_le_of_surjective (A.mapQ (A ⊔ J) LinearMap.id (fun x hx => Submodule.mem_sup_left hx)) ?_
    intro z
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk m, rfl⟩
  rw [hlen, add_comm]
  exact add_le_add hq hS

end Formalism.TruncatedSeriesCounting.R9
end
end

section

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds

open Finset

private lemma sum_le_sum_cover {K : ℕ} (W : Fin K → Finset ℤ) (S : Finset ℤ)
    (hS : ∀ i ∈ S, ∃ k, i ∈ W k) (g : ℤ → ℕ) :
    ∑ i ∈ S, g i ≤ ∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), g i := by
  calc ∑ i ∈ S, g i ≤ ∑ i ∈ S, ∑ k, if i ∈ W k then g i else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨k, hk⟩ := hS i hi
        calc g i = (fun k' => if i ∈ W k' then g i else 0) k := by simp [hk]
          _ ≤ ∑ k', if i ∈ W k' then g i else 0 :=
            Finset.single_le_sum (f := fun k' => if i ∈ W k' then g i else 0) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ k)
    _ = ∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), g i := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_filter]

theorem kappa_window_bound : KapWin := by
  intro ℓ _ hℓ χ hχ ell K D a L JJ hJJ hD
  obtain ⟨hne, hv⟩ := Formalism.WindowSums.arc_KillerVal ℓ hℓ χ hχ ell JJ
  refine ⟨hne, ?_⟩
  rw [hv]
  set S := JJ.erase 0 with hSdef
  set W : Fin K → Finset ℤ := fun k => Finset.Ico (a k) (a k + (L k : ℤ)) with hWdef
  have hcov : ∀ i ∈ S, ∃ k, i ∈ W k := by
    intro i hi
    have := hJJ (Finset.mem_of_mem_erase hi)
    simpa [Finset.mem_biUnion, hWdef] using this
  have hcard : S.card ≤ ∑ k, L k := by
    have h := sum_le_sum_cover W S hcov (fun _ => 1)
    rw [Finset.card_eq_sum_ones]
    refine h.trans (Finset.sum_le_sum fun k _ => ?_)
    rw [← Finset.card_eq_sum_ones]
    calc (S.filter (fun i => i ∈ W k)).card ≤ (W k).card := by
          apply Finset.card_le_card
          intro i hi
          exact (Finset.mem_filter.mp hi).2
      _ = L k := by simp [hWdef]
  have hsumv : ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ) ≤
      ∑ k, ((L k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D) := by
    calc ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ)
        ≤ ((∑ k, ∑ i ∈ S.filter (fun i => i ∈ W k), padicValInt ℓ i : ℕ) : ℝ) := by
          exact_mod_cast sum_le_sum_cover W S hcov (fun i => padicValInt ℓ i)
      _ = ∑ k, ((∑ i ∈ S.filter (fun i => i ∈ W k), padicValInt ℓ i : ℕ) : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ k, ((L k : ℝ) / ((ℓ : ℝ) - 1) + Real.logb ℓ D) := by
          refine Finset.sum_le_sum fun k _ => ?_
          refine Formalism.WindowSums.arc_WindowSum ℓ (a k) (L k) D _ ?_ ?_ ?_
          · intro i hi
            exact (Finset.mem_filter.mp hi).2
          · intro h0
            have := (Finset.mem_filter.mp h0).1
            simp [hSdef] at this
          · intro i hi
            exact hD i (Finset.mem_of_mem_erase (Finset.mem_filter.mp hi).1)
  have hsplit : ∑ i ∈ S, (1 + ell + padicValInt ℓ i) =
      S.card * (1 + ell) + ∑ i ∈ S, padicValInt ℓ i := by
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  rw [hsplit]
  have hcardR : (S.card : ℝ) ≤ ((∑ k, L k : ℕ) : ℝ) := by exact_mod_cast hcard
  have hmul : (S.card : ℝ) * (1 + ell) ≤ ((∑ k, L k : ℕ) : ℝ) * (1 + ell) :=
    mul_le_mul_of_nonneg_right hcardR (by positivity)
  have hgoal : ((S.card * (1 + ell) + ∑ i ∈ S, padicValInt ℓ i + ell : ℕ) : ℝ) =
      (S.card : ℝ) * (1 + ell) + ((∑ i ∈ S, padicValInt ℓ i : ℕ) : ℝ) + ell := by
    push_cast; ring
  rw [hgoal]
  linarith

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingBounds
end

section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Finset

private lemma sum_shift_val (ℓ : ℕ) (j₀ : ℤ) (T : Finset ℤ) :
    ∑ j ∈ T, padicValInt ℓ (j₀ - j) = ∑ i ∈ T.image (fun j => j₀ - j), padicValInt ℓ i := by
  rw [Finset.sum_image]
  intro a _ b _ h
  simp only at h
  omega

theorem g_coeff_valuation_statement : LemmaGVal := by
  intro ℓ _ h η S b a S₂ hb hbS hS₂ j₀ hj₀
  rw [Finset.mem_Icc] at hj₀
  obtain ⟨hj1, hj2⟩ := hj₀
  have hℓ : (2 : ℝ) ≤ ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).two_le
  have hmem : ∀ j ∈ S₂, ((b : ℤ) + 1 ≤ j ∧ j ≤ (b : ℤ) + S + a) ∨
      (1 - (η : ℤ) ≤ j ∧ j ≤ (η : ℤ) + a) := by
    intro j hj
    have := hS₂ hj
    simpa only [Finset.mem_union, Finset.mem_Icc] using this
  set T₁ : Finset ℤ := (Finset.Icc ((b : ℤ) - a + 1) b).erase j₀ ∪
    S₂.filter (fun j => (b : ℤ) < j) with hT₁
  set T₂ : Finset ℤ := S₂.filter (fun j => ¬ (b : ℤ) < j) with hT₂
  have hsplit : (∑ j ∈ (Finset.Icc ((b : ℤ) - a + 1) (b : ℤ)).erase j₀, padicValInt ℓ (j₀ - j)) +
      ∑ j ∈ S₂, padicValInt ℓ (j₀ - j) =
      ∑ j ∈ T₁, padicValInt ℓ (j₀ - j) + ∑ j ∈ T₂, padicValInt ℓ (j₀ - j) := by
    rw [← Finset.sum_filter_add_sum_filter_not S₂ (fun j => (b : ℤ) < j), ← add_assoc, hT₁,
      hT₂, Finset.sum_union]
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hx)).2
    have h2 := (Finset.mem_filter.mp hx').2
    omega
  rw [hsplit, sum_shift_val, sum_shift_val]
  have c1 : T₁.image (fun j => j₀ - j) ⊆
      Finset.Ico (j₀ - b - S - a) (j₀ - b - S - a + ((2 * a + S : ℕ) : ℤ)) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [Finset.mem_Ico]
    push_cast
    rw [hT₁, Finset.mem_union] at hj
    rcases hj with hj | hj
    · have := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hj)
      omega
    · have h1 := (Finset.mem_filter.mp hj).2
      have h2 := hmem j (Finset.mem_filter.mp hj).1
      omega
  have c2 : (0 : ℤ) ∉ T₁.image (fun j => j₀ - j) := by
    intro hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, hj0⟩ := hi
    rw [hT₁, Finset.mem_union] at hj
    rcases hj with hj | hj
    · have := Finset.ne_of_mem_erase hj
      omega
    · have h1 := (Finset.mem_filter.mp hj).2
      omega
  have c3 : ∀ i ∈ T₁.image (fun j => j₀ - j), |i| ≤ ((2 * (h + η) : ℕ) : ℤ) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    push_cast
    rw [hT₁, Finset.mem_union] at hj
    rw [abs_le]
    rcases hj with hj | hj
    · have := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hj)
      constructor <;> omega
    · have h1 := (Finset.mem_filter.mp hj).2
      have h2 := hmem j (Finset.mem_filter.mp hj).1
      constructor <;> omega
  have d1 : T₂.image (fun j => j₀ - j) ⊆
      Finset.Ico (j₀ - η - a) (j₀ - η - a + ((2 * η + a : ℕ) : ℤ)) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [Finset.mem_Ico]
    push_cast
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 := hmem j (Finset.mem_filter.mp hj).1
    omega
  have d2 : (0 : ℤ) ∉ T₂.image (fun j => j₀ - j) := by
    intro hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, hj0⟩ := hi
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 := hmem j (Finset.mem_filter.mp hj).1
    omega
  have d3 : ∀ i ∈ T₂.image (fun j => j₀ - j), |i| ≤ ((2 * (h + η) : ℕ) : ℤ) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    push_cast
    rw [abs_le]
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 := hmem j (Finset.mem_filter.mp hj).1
    constructor <;> omega
  have w1 := Formalism.WindowSums.arc_WindowSum ℓ (j₀ - b - S - a) (2 * a + S) (2 * (h + η)) _ c1 c2 c3
  have w2 := Formalism.WindowSums.arc_WindowSum ℓ (j₀ - η - a) (2 * η + a) (2 * (h + η)) _ d1 d2 d3
  have hDpos : (1 : ℝ) ≤ ((2 * (h + η) : ℕ) : ℝ) := by
    have : 1 ≤ 2 * (h + η) := by omega
    exact_mod_cast this
  have hlog : 0 ≤ Real.logb ℓ ((2 * (h + η) : ℕ) : ℝ) := Real.logb_nonneg (by linarith) hDpos
  have hlam : lam ℓ (h + η) = Real.logb ℓ ((2 * (h + η) : ℕ) : ℝ) + 1 := by
    simp only [lam]
    push_cast
    ring_nf
  have hsum : ((2 * a + S : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + ((2 * η + a : ℕ) : ℝ) / ((ℓ : ℝ) - 1) =
      (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) := by
    rw [← add_div]
    push_cast
    ring_nf
  rw [hlam]
  push_cast at w1 w2 hlog hsum ⊢
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end

section

namespace Formalism.TruncatedSeriesCounting.X

theorem truncation_remainder_bound : TruncRem1 := by
  intro R _ ℓ hℓ π₀ y K c hc
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy
    have hc0 : c = 0 := by push_cast at hc; omega
    subst hc0
    rw [pow_zero]
    exact Ideal.subset_span (Set.mem_insert _ _) |> fun h => by simpa using h
  · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have e : (π₀ * (π₀ + (ℓ : R)) ^ (ℓ - 1)) ^ (y' + 1) =
        π₀ * ((π₀ + (ℓ : R)) + (-(ℓ : R))) ^ y' * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1)) := by
      rw [show (π₀ + (ℓ : R)) + (-(ℓ : R)) = π₀ by ring, mul_pow, ← pow_mul, pow_succ]
      ring
    rw [e, add_pow (π₀ + (ℓ : R)) (-(ℓ : R)) y', Finset.mul_sum, Finset.sum_mul]
    refine Ideal.sum_mem _ fun m hm => ?_
    have hm' : m ≤ y' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    by_cases hj : c ≤ y' - m
    · have h1 : (-(ℓ : R)) ^ (y' - m) = (ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c)) := by
        have hsplit : (ℓ : R) ^ (y' - m) = (ℓ : R) ^ c * (ℓ : R) ^ (y' - m - c) := by
          rw [← pow_add]
          congr 1
          omega
        rw [neg_pow, hsplit]
        ring
      have hmem : (ℓ : R) ^ c ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K} :=
        Ideal.subset_span (Set.mem_insert _ _)
      rw [h1]
      have : π₀ * ((π₀ + ↑ℓ) ^ m * ((ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c))) * ↑(y'.choose m)) *
          (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) = (ℓ : R) ^ c * (π₀ * (π₀ + ↑ℓ) ^ m * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c)) *
          ↑(y'.choose m) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1))) := by ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hmem
    · have hK : K ≤ m + (ℓ - 1) * (y' + 1) := by
        push_neg at hj
        have h2 : (c : ℤ) ≤ (ℓ : ℤ) * ((y' + 1 : ℕ) : ℤ) - K := hc
        push_cast at h2
        have h3 : (c : ℤ) ≥ (y' : ℤ) - m + 1 := by omega
        zify [hℓ]
        nlinarith [h2, h3]
      have hmem : π₀ * (π₀ + (ℓ : R)) ^ K ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have : π₀ * ((π₀ + ↑ℓ) ^ m * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) =
          π₀ * (π₀ + (ℓ : R)) ^ K * ((π₀ + ↑ℓ) ^ (m + (ℓ - 1) * (y' + 1) - K) * (-(ℓ : R)) ^ (y' - m) *
            ↑(y'.choose m)) := by
        have e2 : (π₀ + (ℓ : R)) ^ K * (π₀ + (ℓ : R)) ^ (m + (ℓ - 1) * (y' + 1) - K) =
            (π₀ + (ℓ : R)) ^ m * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1)) := by
          rw [← pow_add, ← pow_add, Nat.add_sub_cancel' hK]
        linear_combination (π₀ * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * e2.symm
      rw [this]
      exact Ideal.mul_mem_right _ _ hmem

end Formalism.TruncatedSeriesCounting.X
end

section

namespace Formalism.TruncatedSeriesCounting.X

theorem truncation_signature_bound : TruncSig := by
  unfold TruncSig
  intro ℓ hℓ y X M η
  have hl : (3 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have ha : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hlpos : (0 : ℝ) < (ℓ : ℝ) := by linarith
  have hy : (0 : ℝ) ≤ (y : ℝ) := Nat.cast_nonneg y
  have gen : ∀ T : ℝ, 0 ≤ T → (y : ℝ) * ℓ / (ℓ - 1) - max 0 ((ℓ : ℝ) * y - T) ≤ T / (ℓ - 1) := by
    intro T hT
    rw [sub_le_iff_le_add, div_le_iff₀ ha, add_mul, div_mul_cancel₀ _ (ne_of_gt ha)]
    rcases le_total ((ℓ : ℝ) * y - T) 0 with h | h
    · rw [max_eq_left h]; nlinarith
    · rw [max_eq_right h]
      nlinarith [mul_nonneg h (by linarith : (0 : ℝ) ≤ (ℓ : ℝ) - 2)]
  have mono : ∀ T : ℝ, T / ((ℓ : ℝ) - 1) ≤ (T + 1) / ((ℓ : ℝ) - 1) + 1 := by
    intro T
    have h1 : 0 ≤ 1 / ((ℓ : ℝ) - 1) := by positivity
    rw [add_div]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact (gen X (Nat.cast_nonneg _)).trans (mono _)
  · have e : (ℓ : ℝ) * y - η - M = (ℓ : ℝ) * y - (η + M) := by ring
    rw [e]
    have := gen ((η : ℝ) + M) (by positivity)
    have h2 : ((η : ℝ) + M) / (ℓ - 1) ≤ ((M : ℝ) + η) / (ℓ - 1) + 1 := by
      rw [add_comm (η : ℝ)]
      have h3 : 0 ≤ 1 / ((ℓ : ℝ) - 1) := by positivity
      linarith
    linarith
  · have hsq : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := pow_pos ha 2
    have e : (y : ℝ) * ℓ / (ℓ - 1) = (y : ℝ) * ℓ * (ℓ - 1) / (ℓ - 1) ^ 2 := by
      field_simp
    have key : (y : ℝ) * ℓ / (ℓ - 1) - max 0 (((ℓ : ℝ) - 1) * y - X / ℓ) ≤ X / (ℓ - 1) ^ 2 := by
      rw [e, sub_le_iff_le_add, div_le_iff₀ hsq, add_mul, div_mul_cancel₀ _ (ne_of_gt hsq)]
      have hX : (X : ℝ) = X / ℓ * ℓ := (div_mul_cancel₀ _ hlpos.ne').symm
      rcases le_total (((ℓ : ℝ) - 1) * y - X / ℓ) 0 with h | h
      · rw [max_eq_left h]
        have h4 : ((ℓ : ℝ) - 1) * y * ℓ ≤ X := by
          have h5 : ((ℓ : ℝ) - 1) * y ≤ X / ℓ := by linarith
          have := mul_le_mul_of_nonneg_right h5 hlpos.le
          linarith
        nlinarith
      · rw [max_eq_right h]
        have hs2 : (0 : ℝ) ≤ ((ℓ : ℝ) - 1) ^ 2 - ℓ := by nlinarith
        nlinarith [mul_nonneg h hs2]
    have h6 : (0 : ℝ) ≤ 1 := zero_le_one
    linarith

end Formalism.TruncatedSeriesCounting.X
end

section

namespace Formalism.TruncatedSeriesCounting.X

private theorem iter_nzd {A : Type} [CommRing A] (ℓ g : A)
    (h : ∀ a : A, ℓ * a ∈ Ideal.span {g} → a ∈ Ideal.span {g}) :
    ∀ (n : ℕ) (z : A), ℓ ^ n * z ∈ Ideal.span {g} → z ∈ Ideal.span {g} := by
  intro n
  induction n with
  | zero => intro z hz; simpa using hz
  | succ n ih =>
    intro z hz
    apply ih
    apply h
    have e : ℓ * (ℓ ^ n * z) = ℓ ^ (n + 1) * z := by ring
    rw [e]; exact hz

theorem saturation_criterion : SatA := by
  intro A _ _ ℓ f f' hf' hℓf hℓf' x k ⟨b, hb⟩ ⟨a, ha⟩
  have inj : Function.Injective (algebraMap A (FractionRing A)) := IsFractionRing.injective A (FractionRing A)
  have h1 : ℓ ^ k * b = f' * (f * a) := by
    apply inj
    rw [map_mul, map_pow, hb, map_mul (algebraMap A (FractionRing A)) f', ha]
    ring
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (iter_nzd ℓ f' hℓf' k b (by
    rw [h1]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f')))
  have hf'0 : algebraMap A (FractionRing A) f' ≠ 0 := (map_ne_zero_iff _ inj).mpr hf'
  have hx : x = algebraMap A (FractionRing A) c := by
    apply mul_left_cancel₀ hf'0
    rw [← hb, hc, map_mul]
  have h2 : ℓ ^ k * c = f * a := by
    apply inj
    rw [map_mul, map_pow, ← hx, ha]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (iter_nzd ℓ f hℓf k c (by
    rw [h2]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))
  exact ⟨d, by rw [hx, hd]⟩

end Formalism.TruncatedSeriesCounting.X
end

section

namespace Formalism.TruncatedSeriesCounting.X

theorem arc_exponential_identity : ArcExp := by
  intro r σ κ G j' ell hr hσ hκ hG hj
  have hj' : (j' : ℝ) ≤ ell := by exact_mod_cast hj
  have hjG : (j' : ℝ) * G ≤ ell * G := mul_le_mul_of_nonneg_right hj' hG
  have hell : 0 ≤ (ell : ℝ) * G := mul_nonneg (Nat.cast_nonneg _) hG
  rcases le_total (r + κ) (2 * σ + 2 * j' * G + 1) with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

end Formalism.TruncatedSeriesCounting.X
end
