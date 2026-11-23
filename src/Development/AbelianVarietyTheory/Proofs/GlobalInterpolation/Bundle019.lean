module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle013
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedPerronPsi
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.BinaryFormCount

open Finset

variable {k : Type} [Field k] [Fintype k] [DecidableEq k]

theorem card_fibre_eq {t n : k} (hD : t ^ 2 - 4 * n ≠ 0) {c : k} (hc : c ≠ 0) :
    #{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = c}
      = #{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 1} := by
  obtain ⟨u, v, huv⟩ := UnramifiedHermitian.exists_binary_eq_of_finite hD c
  symm
  refine Finset.card_nbij' (fun p => (p.1 * u - n * p.2 * v, p.1 * v + p.2 * u + t * p.2 * v))
    (fun p => ((p.1 * (u + t * v) + n * p.2 * v) / c, (p.2 * u - p.1 * v) / c)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
    linear_combination (u ^ 2 + t * u * v + n * v ^ 2) * hp + huv
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
    field_simp
    linear_combination (u ^ 2 + t * u * v + n * v ^ 2) * hp + c * huv
  · intro p _
    ext
    · simp only; field_simp; linear_combination p.1 * huv
    · simp only; field_simp; linear_combination p.2 * huv
  · intro p _
    ext
    · simp only; field_simp; linear_combination p.1 * huv
    · simp only; field_simp; linear_combination p.2 * huv

theorem card_zero {t n : k} (hD : t ^ 2 - 4 * n ≠ 0) {η : ℝ}
    (h1 : (∃ r : k, r ^ 2 - t * r + n = 0) → η = 1)
    (h2 : (¬ ∃ r : k, r ^ 2 - t * r + n = 0) → η = -1) :
    (#{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 0} : ℝ)
      = Fintype.card k - η + η * Fintype.card k := by
  by_cases h : ∃ r : k, r ^ 2 - t * r + n = 0
  · rw [h1 h]
    obtain ⟨r, hr⟩ := h
    have hne : t - 2 * r ≠ 0 := by
      intro h0
      apply hD
      linear_combination (t - 2 * r) * h0 - 4 * hr
    have e : ({p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 0} : Finset (k × k))
        = (univ.image fun b : k => (-r * b, b)) ∪ (univ.image fun b : k => (-(t - r) * b, b)) := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_image, Prod.mk.injEq,
        exists_eq_right]
      constructor
      · intro hab
        have : (-r * b - a) * (-(t - r) * b - a) = 0 := by linear_combination hab - b ^ 2 * hr
        rcases mul_eq_zero.1 this with h | h
        · exact Or.inl (sub_eq_zero.1 h)
        · exact Or.inr (sub_eq_zero.1 h)
      · rintro (rfl | rfl) <;> linear_combination b ^ 2 * hr
    have i : (univ.image fun b : k => (-r * b, b)) ∩ (univ.image fun b : k => (-(t - r) * b, b))
        = {((0 : k), (0 : k))} := by
      ext ⟨a, b⟩
      simp only [mem_univ, true_and, mem_inter, mem_image, Prod.mk.injEq,
        exists_eq_right, mem_singleton]
      constructor
      · rintro ⟨rfl, h⟩
        have : (t - 2 * r) * b = 0 := by linear_combination -h
        have hb := (mul_eq_zero.1 this).resolve_left hne
        simp [hb]
      · rintro ⟨rfl, rfl⟩; simp
    have := Finset.card_union_add_card_inter (univ.image fun b : k => (-r * b, b))
      (univ.image fun b : k => (-(t - r) * b, b))
    rw [i, ← e, card_image_of_injective _ (fun a b h => congrArg Prod.snd h),
      card_image_of_injective _ (fun a b h => congrArg Prod.snd h), card_singleton,
      card_univ] at this
    have h3 := congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at h3
    linarith
  · rw [h2 h]
    have e : ({p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 0} : Finset (k × k))
        = {((0 : k), (0 : k))} := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq, mem_singleton]
      constructor
      · intro hab
        by_cases hb : b = 0
        · subst hb
          simpa using hab
        · refine (h ⟨-a / b, ?_⟩).elim
          field_simp
          linear_combination hab
      · rintro ⟨rfl, rfl⟩; simp
    rw [e, card_singleton]
    push_cast
    ring

theorem card_fibre {t n : k} (hD : t ^ 2 - 4 * n ≠ 0) {η : ℝ}
    (h1 : (∃ r : k, r ^ 2 - t * r + n = 0) → η = 1)
    (h2 : (¬ ∃ r : k, r ^ 2 - t * r + n = 0) → η = -1) (c : k) :
    (#{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = c} : ℝ)
      = Fintype.card k - η + if c = 0 then η * Fintype.card k else 0 := by
  have hz := card_zero hD h1 h2
  by_cases hc : c = 0
  · rw [if_pos hc, hc, hz]
  rw [if_neg hc, card_fibre_eq hD hc, add_zero]
  have tot := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (k × k))) (t := univ)
    (f := fun p : k × k => p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2) (fun _ _ => mem_univ _)
  rw [← Finset.add_sum_erase _ _ (mem_univ (0 : k)),
    Finset.sum_congr rfl (fun d hd => card_fibre_eq hD (Finset.ne_of_mem_erase hd)),
    sum_const, card_erase_of_mem (mem_univ _), card_univ, card_univ, Fintype.card_prod,
    smul_eq_mul] at tot
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have h3 := congrArg (Nat.cast : ℕ → ℝ) tot
  push_cast [Nat.cast_sub hq.le] at h3
  rw [hz] at h3
  have hq' : (Fintype.card k : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Fintype.card k := by exact_mod_cast hq
    linarith
  apply mul_left_cancel₀ hq'
  linear_combination -h3

theorem card_sum_zero {α : Type} [Fintype α] [DecidableEq α] (Q : α → k) (q η : ℝ)
    (hα : (Fintype.card α : ℝ) = q ^ 2)
    (hQ : ∀ c, (#{p : α | Q p = c} : ℝ) = q - η + if c = 0 then η * q else 0) (M : ℕ) :
    (#{x : Fin M → α | ∑ i, Q (x i) = 0} : ℝ) * q = q ^ (2 * M) + (q - 1) * (η * q) ^ M := by
  induction M with
  | zero => simp
  | succ M ih =>
    have key : (#{x : Fin (M + 1) → α | ∑ i, Q (x i) = 0} : ℝ)
        = q ^ (2 * M) * (q - η) + η * q * #{x : Fin M → α | ∑ i, Q (x i) = 0} := by
      rw [Finset.card_filter, Finset.card_filter]
      push_cast
      rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type_right]
      have : ∀ y : Fin M → α, (∑ a : α, if ∑ i, Q ((Fin.consEquiv fun _ => α) (a, y) i) = 0
          then (1 : ℝ) else 0) = q - η + η * q * if ∑ i, Q (y i) = 0 then 1 else 0 := by
        intro y
        have := hQ (-∑ i, Q (y i))
        rw [Finset.card_filter] at this
        push_cast at this
        simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
          ← eq_neg_iff_add_eq_zero, this, neg_eq_zero, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_congr rfl fun y _ => this y, sum_add_distrib, ← mul_sum, sum_const,
        card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [hα, ← pow_mul]
    rw [key, show 2 * (M + 1) = 2 * M + 2 by ring]
    linear_combination (η * q) * ih

end GlobalTheory.BinaryFormCount

namespace GlobalTheory


open Finset in
theorem ncard_sum_binary_form_ne_zero (k : Type) [Field k] [Finite k] (t n : k)
    (hD : t ^ 2 - 4 * n ≠ 0) (η : ℝ) (h1 : (∃ r : k, r ^ 2 - t * r + n = 0) → η = 1)
    (h2 : (¬ ∃ r : k, r ^ 2 - t * r + n = 0) → η = -1) (M : ℕ) :
    ({x : Fin M × Fin 2 → k | ∑ i : Fin M,
        (x (i, 0) ^ 2 + t * x (i, 0) * x (i, 1) + n * x (i, 1) ^ 2) ≠ 0}.ncard : ℝ)
      * (Nat.card k : ℝ)
      = ((Nat.card k : ℝ) - 1) * ((Nat.card k : ℝ) ^ (2 * M) - (η * (Nat.card k : ℝ)) ^ M) := by
  classical
  haveI := Fintype.ofFinite k
  have hz := BinaryFormCount.card_sum_zero
    (fun p : k × k => p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2) (Fintype.card k) η
    (by rw [Fintype.card_prod]; push_cast; ring) (BinaryFormCount.card_fibre hD h1 h2) M
  have hs := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin M → k × k)))
    (fun x => ∑ i, ((x i).1 ^ 2 + t * (x i).1 * (x i).2 + n * (x i).2 ^ 2) = 0)
  have hb : {x : Fin M × Fin 2 → k | ∑ i : Fin M,
        (x (i, 0) ^ 2 + t * x (i, 0) * x (i, 1) + n * x (i, 1) ^ 2) ≠ 0}.ncard
      = #{x : Fin M → k × k |
        ¬ ∑ i, ((x i).1 ^ 2 + t * (x i).1 * (x i).2 + n * (x i).2 ^ 2) = 0} := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
    refine Finset.card_nbij' (fun x i => (x (i, 0), x (i, 1)))
      (fun x p => ![(x p.1).1, (x p.1).2] p.2) ?_ ?_ ?_ ?_
    · intro x hx
      simpa using hx
    · intro x hx
      simpa using hx
    · intro x _
      ext ⟨i, j⟩
      fin_cases j <;> simp
    · intro x _
      ext i <;> simp
  rw [card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin] at hs
  have h3 := congrArg (Nat.cast : ℕ → ℝ) hs
  push_cast at h3
  rw [hb, Nat.card_eq_fintype_card, pow_mul, pow_two]
  rw [pow_mul, pow_two] at hz
  linear_combination (Fintype.card k : ℝ) * h3 - hz

end GlobalTheory
end

section

open MeasureTheory Topology
open scoped ENNReal

namespace GlobalTheory

theorem exists_bruhat_function_closedEmbedding
    (T T' : Type) [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [T2Space T] [MeasurableSpace T] [BorelSpace T]
    [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T'] [MeasurableSpace T'] [BorelSpace T']
    (j : T' →* T) (hj : IsClosedEmbedding j) (m' : Measure T') [m'.IsHaarMeasure]
    [m'.IsInvInvariant] :
    ∃ b : T → ℝ≥0∞, Measurable b ∧ ∀ t, ∫⁻ s, b (j s * t) ∂m' = 1 := by
  classical
  let H : Subgroup T := j.range
  have hH : IsClosed (H : Set T) := by
    simpa [H, MonoidHom.coe_range] using hj.isClosed_range
  let e : T' ≃* H := MonoidHom.ofInjective hj.injective
  have he : Continuous e := hj.continuous.subtype_mk _
  have hes : Continuous e.symm := by
    rw [hj.isEmbedding.isInducing.continuous_iff]
    have : (fun x : H => j (e.symm x)) = fun x : H => (x : T) := by
      funext x
      exact MonoidHom.apply_ofInjective_symm hj.injective x
    rw [Function.comp_def, this]
    exact continuous_subtype_val
  have : (Measure.map e m').IsHaarMeasure := e.isHaarMeasure_map m' he hes
  obtain ⟨φ, hφ, hint, -⟩ := exists_bruhat_function_closed_subgroup T H hH (Measure.map e m')
  refine ⟨fun x => φ x⁻¹, hφ.comp measurable_inv, fun t => ?_⟩
  show ∫⁻ s, φ (j s * t)⁻¹ ∂m' = 1
  have h1 := hint t⁻¹
  have hm : Measurable (fun h : H => φ (t⁻¹ * (h : T))) :=
    hφ.comp (continuous_const.mul continuous_subtype_val).measurable
  rw [lintegral_map hm he.measurable] at h1
  have h2 : ∀ s : T', ((e s : H) : T) = j s := fun s => rfl
  simp only [h2] at h1
  have h3 : ∀ s : T', (j s * t)⁻¹ = t⁻¹ * j s⁻¹ := fun s => by
    rw [mul_inv_rev, map_inv]
  simp only [h3]
  rw [lintegral_inv_eq_self (fun s => φ (t⁻¹ * j s))]
  exact h1

end GlobalTheory
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.PerronCoeff
open GlobalTheory.PerronPsi

theorem truncated_perron_of_le_two_vonMangoldt : ∃ C : ℝ, 0 < C ∧ ∀ (c : ℕ → ℂ) (u T : ℝ), (∀ n, ‖c n‖ ≤ 2 * Λ n) → 2 ≤ T → T ≤ u → ‖(∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n) - (1 / (2 * Real.pi) : ℂ) * ∫ t in (-T)..T, LSeries c (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) * (u : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)‖ ≤ C * (u * Real.log u ^ 2 / T + Real.log u) := by
  obtain ⟨C, hC, hK⟩ := kernel_bound
  refine ⟨480 * C, by positivity, ?_⟩
  intro c u T hc hT hTu
  have hu : 2 ≤ u := hT.trans hTu
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hL : 1 / 2 ≤ Real.log u := half_le_log hu
  have hL0 : 0 < Real.log u := by linarith
  have hσ1 : 1 < 1 + 1 / Real.log u := by
    have : 0 < 1 / Real.log u := by positivity
    linarith
  have hσ0 : 0 < 1 + 1 / Real.log u := by linarith
  have hc0 : c 0 = 0 := by simpa using hc 0
  have hs : LSeriesSummable c ((1 + 1 / Real.log u : ℝ) : ℂ) := by
    have hΛ : LSeriesSummable (fun n => (Λ n : ℂ)) ((1 + 1 / Real.log u : ℝ) : ℂ) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ1)
    refine Summable.of_norm_bounded (hΛ.norm.mul_left 2) (fun n => ?_)
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    split_ifs with hn
    · simp
    · have hpow : 0 < (n : ℝ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ)).re := by
        have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        positivity
      rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        mul_div_assoc']
      exact div_le_div_of_nonneg_right (hc n) hpow.le
  have hI := interchange c hc0 T hσ0 hu0 hs
  have hS : HasSum (fun n : ℕ => c n * (if 1 ≤ u / (n : ℝ) then (1 : ℂ) else 0))
      (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n) := by
    have e : ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n
        = ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, c n * (if 1 ≤ u / (n : ℝ) then (1 : ℂ) else 0) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
      have : 1 ≤ u / n := by
        rw [le_div_iff₀ hn0, one_mul]
        exact (Nat.le_floor_iff hu0.le).mp h2
      simp [this]
    rw [e]
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [hc0]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
      have : ¬ (1 ≤ u / n) := by
        intro h
        apply hn
        rw [le_div_iff₀ hn0, one_mul] at h
        exact Finset.mem_Icc.mpr ⟨hpos, Nat.le_floor h⟩
      simp [this]
  have hD := hS.sub (hI.mul_left (1 / (2 * Real.pi) : ℂ))
  have hfac : ∀ x y z v : ℂ, x * y - z * (x * v) = x * (y - z * v) := fun _ _ _ _ => by ring
  have hp : 1 < 1 + 1 / (2 * Real.log u) := by
    have : 0 < 1 / (2 * Real.log u) := by positivity
    linarith
  have hsumm : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u))) :=
    Real.summable_one_div_nat_rpow.mpr hp
  have hB : 0 ≤ 2 * u / T := by positivity
  have hnear : HasSum (fun n : ℕ =>
        if n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) then w ⌊u⌋₊ (2 * u / T) n else 0)
      (∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n) := by
    have e : ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n
        = ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)),
          (if n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) then w ⌊u⌋₊ (2 * u / T) n else 0) :=
      Finset.sum_congr rfl (fun n hn => by simp [hn])
    rw [e]
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    simp [hn]
  have hg := (hsumm.hasSum.mul_left (2 * C * (12 * u * Real.log u / T))).add
    (hnear.mul_left (2 * C * (16 * Real.log u)))
  have hA0 : 0 ≤ 2 * C * (12 * u * Real.log u / T) := by positivity
  have hBc0 : 0 ≤ 2 * C * (16 * Real.log u) := by positivity
  have hbound := hD.norm_le_of_bounded hg (fun n => by
    rw [hfac]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp only [hc0, zero_mul, norm_zero]
      refine add_nonneg (mul_nonneg hA0 (by positivity)) (mul_nonneg hBc0 ?_)
      split_ifs
      · exact w_nonneg _ hB _
      · exact le_rfl
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
    have hy : 0 < u / n := div_pos hu0 hn0
    obtain ⟨hK1, hK2⟩ := hK (u / n) (1 + 1 / Real.log u) T hy hσ0 (by linarith)
    have hE0 := norm_nonneg ((1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
        ((u / n : ℝ) : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)
          / (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)) - (if 1 ≤ u / n then 1 else 0))
    rw [norm_mul, norm_sub_rev]
    have hcn : ‖c n‖ ≤ 2 * Real.log n :=
      (hc n).trans (by linarith [ArithmeticFunction.vonMangoldt_le_log (n := n)])
    have hmain := mul_le_mul_of_nonneg_right hcn hE0
    have hfar0 : 0 ≤ 2 * C * (12 * u * Real.log u / T)
        * (1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u))) := mul_nonneg hA0 (by positivity)
    by_cases hfar : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n
    · have h := far_term hu hT0 hpos hC.le hE0 hK2 hfar
      have hnr : 0 ≤ 2 * C * (16 * Real.log u)
          * (if n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) then w ⌊u⌋₊ (2 * u / T) n else 0) := by
        refine mul_nonneg hBc0 ?_
        split_ifs
        · exact w_nonneg _ hB _
        · exact le_rfl
      nlinarith
    · push Not at hfar
      have h := near_term hu hT0 hC.le hE0 hK1 hK2 hfar.1 hfar.2
      have hmem : n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)) := by
        rw [Finset.mem_range]
        have h1 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
        have h2 : (n : ℝ) < ((⌊u⌋₊ + 1 + (⌊u⌋₊ + 1) : ℕ) : ℝ) := by
          push_cast
          linarith [hfar.2]
        exact_mod_cast h2
      rw [if_pos hmem]
      nlinarith)
  refine hbound.trans ?_
  have hZ : ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u)) ≤ 1 + 2 * Real.log u := by
    have h := zeta_bound hp
    have e : 1 / (1 + 1 / (2 * Real.log u) - 1) = 2 * Real.log u := by
      rw [add_sub_cancel_left, one_div_one_div]
    rwa [e] at h
  have hN : Real.log ⌊u⌋₊ ≤ Real.log u := by
    have hpos : (0 : ℝ) < ⌊u⌋₊ := by
      have : 1 ≤ ⌊u⌋₊ := Nat.le_floor (by norm_num; linarith)
      exact_mod_cast this
    exact Real.log_le_log hpos (Nat.floor_le hu0.le)
  have hW : ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n
      ≤ 2 + 2 * u / T * (2 * (1 + Real.log u)) := by
    have h := sum_w ⌊u⌋₊ hB
    have : 2 * u / T * (2 * (1 + Real.log ⌊u⌋₊)) ≤ 2 * u / T * (2 * (1 + Real.log u)) := by
      gcongr
    linarith
  have hX : 0 ≤ u / T := by positivity
  have hint : 0 ≤ (u / T) * Real.log u * (2 * Real.log u - 1) :=
    mul_nonneg (mul_nonneg hX hL0.le) (by linarith)
  have key : 2 * (12 * (u / T) * Real.log u) * (1 + 2 * Real.log u)
      + 2 * (16 * Real.log u) * (2 + 2 * (u / T) * (2 * (1 + Real.log u)))
      ≤ 480 * ((u / T) * Real.log u ^ 2 + Real.log u) := by
    nlinarith
  calc 2 * C * (12 * u * Real.log u / T) * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 1 / (2 * Real.log u))
        + 2 * C * (16 * Real.log u)
          * ∑ n ∈ Finset.range (⌊u⌋₊ + 1 + (⌊u⌋₊ + 1)), w ⌊u⌋₊ (2 * u / T) n
      ≤ 2 * C * (12 * u * Real.log u / T) * (1 + 2 * Real.log u)
        + 2 * C * (16 * Real.log u) * (2 + 2 * u / T * (2 * (1 + Real.log u))) := by
        gcongr
    _ = C * (2 * (12 * (u / T) * Real.log u) * (1 + 2 * Real.log u)
        + 2 * (16 * Real.log u) * (2 + 2 * (u / T) * (2 * (1 + Real.log u)))) := by ring
    _ ≤ C * (480 * ((u / T) * Real.log u ^ 2 + Real.log u)) :=
        mul_le_mul_of_nonneg_left key hC.le
    _ = 480 * C * (u * Real.log u ^ 2 / T + Real.log u) := by ring

end GlobalTheory.PerronCoeff
end
