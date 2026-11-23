module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle075
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle076
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.BoxVolume

theorem prod_zpow_nnreal {ι : Type} (d : ℝ≥0) (hd : d ≠ 0) (f : ι → ℤ) (s : Finset ι) :
    ∏ i ∈ s, d ^ f i = d ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hd]

theorem volM_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [Fintype D] (c : A → D → ℤ),
    volM ν A D {y | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c i j)} =
      ν (𝒪[k] : Set k) ^ (Fintype.card A * Fintype.card D) *
        ENNReal.ofReal ((resCard k : ℝ) ^ (-∑ i, ∑ j, c i j)) := by
  intro k _ _ _ _ _ _ ν _ ϖ hϖ A D _ _ c
  haveI := secondCountable k
  haveI := t2Space k
  have hset : ({y : Matrix A D k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c i j)} :
      Set (A → D → k)) = Set.univ.pi fun i => Set.univ.pi fun j => cball (ϖ ^ c i j) := by
    ext y
    simp only [Set.mem_univ_pi, cball, Set.mem_setOf_eq, Units.val_zpow_eq_zpow_val]
    rfl
  set d : ℝ≥0 := distribHaarChar k ϖ with hd
  have hdq : (d : ℝ) = (resCard k : ℝ)⁻¹ := nabs_unif hϖ
  have hd0 : d ≠ 0 := (distribHaarChar_pos (A := k) (g := ϖ)).ne'
  have hcb : ∀ i j, ν (cball (ϖ ^ c i j)) = ((d ^ c i j : ℝ≥0) : ℝ≥0∞) * ν (𝒪[k] : Set k) := by
    intro i j
    rw [measure_cball, map_zpow]
  rw [volM]
  erw [hset, Measure.pi_pi]
  simp_rw [Measure.pi_pi, hcb, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [← pow_mul, mul_comm (ν _ ^ _)]
  rw [Nat.mul_comm (Fintype.card D)]
  congr 1
  have hz : ∏ i, ∏ j, d ^ c i j = d ^ (∑ i, ∑ j, c i j) := by
    simp_rw [prod_zpow_nnreal d hd0]
  have hz' : (∏ i, ∏ j, ((d ^ c i j : ℝ≥0) : ℝ≥0∞)) =
      ((d ^ (∑ i, ∑ j, c i j) : ℝ≥0) : ℝ≥0∞) := by
    exact_mod_cast hz
  rw [hz', ← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [NNReal.coe_zpow, hdq, _root_.inv_zpow']

end GlobalTheory.BoxVolume
end
end

section

open GlobalTheory.InertZeta

noncomputable section
open Matrix Formalism.UG

namespace GlobalTheory.InertZeta

theorem prod_exp_eq {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, WithZero.exp (f i) = WithZero.exp (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, WithZero.exp_add]

theorem isInt_diagonal {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {f : Fin n → L}
    (hf : ∀ i, f i ∈ intL L) : IsInt (Matrix.diagonal f) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · subst h; exact hf i
  · exact zero_mem _

theorem hasLen_diagonal_zpow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {ϖ : L}
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (d : Fin n → ℤ) :
    HasLen (Matrix.diagonal (fun i => ϖ ^ d i)) (∑ i, (-d i).toNat) := by
  have h0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hpow : ∀ m : ℕ, ϖ ^ m ∈ intL L := fun m => by
    show Valued.v (ϖ ^ m) ≤ 1
    rw [map_pow, hϖ]
    exact pow_le_one' (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num) m
  refine ⟨Matrix.diagonal (fun i => if 0 ≤ d i then 1 else 0), Matrix.diagonal (fun i => if 0 ≤ d i then 0 else 1),
    Matrix.diagonal (fun i => ϖ ^ (-d i).toNat), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact isInt_diagonal fun i => by split_ifs <;> first | exact one_mem _ | exact zero_mem _
  · exact isInt_diagonal fun i => by split_ifs <;> first | exact one_mem _ | exact zero_mem _
  · exact isInt_diagonal fun i => hpow _
  · rw [Matrix.diagonal_mul_diagonal]
    refine isInt_diagonal fun i => ?_
    have : ϖ ^ d i * ϖ ^ (-d i).toNat = ϖ ^ (d i).toNat := by
      rw [← zpow_natCast, ← zpow_add₀ h0, ← zpow_natCast]
      congr 1
      omega
    rw [this]; exact hpow _
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases h : 0 ≤ d i
    · simp [h, Int.toNat_eq_zero.2 (by omega : -d i ≤ 0)]
    · simp only [h, if_false, zero_mul, zero_add, one_mul]
      rw [← zpow_natCast, ← zpow_add₀ h0]
      rw [show d i + (((-d i).toNat : ℕ) : ℤ) = 0 by omega, zpow_zero]
  · rw [Matrix.det_diagonal, map_prod]
    simp only [map_pow, hϖ]
    rw [Finset.prod_congr rfl (fun i _ => (WithZero.exp_nsmul _ _).symm), prod_exp_eq]
    congr 1
    push_cast
    simp

theorem fracExists_of_smith : Smith → FracExists := by
  intro hS L _ _ ϖ n hϖ g hg
  obtain ⟨d, a, a', b, b', ha, ha', hb, hb', ea, eb, rfl⟩ := hS L ϖ n hϖ g hg
  have h := (hasLen_diagonal_zpow hϖ d).mul_mul ha ha' hb hb' ea eb
  rw [h.len_eq]
  exact h

end GlobalTheory.InertZeta
end
end

section

open GlobalTheory.InertZeta

noncomputable section

namespace GlobalTheory.InertZeta

theorem genFun_counts_hasSum {𝕜 : Type} [NormedField 𝕜] [CompleteSpace 𝕜] (c q N : ℕ) (x : 𝕜)
    (hx : ‖(q : 𝕜) ^ (N + 1) * x‖ < 1) :
    HasSum (fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : 𝕜) * x ^ j)
      (c * (1 + q * x) / (1 - ((q : 𝕜) ^ (N + 1) * x) ^ 2)) := by
  set y := (q : 𝕜) ^ (N + 1) * x with hy
  have hy2 : ‖y ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg y]
  have hg := hasSum_geometric_of_norm_lt_one hy2
  have fe : (fun k : ℕ => ((c * q ^ (2 * N * ((2 * k) / 2) + 2 * k) : ℕ) : 𝕜) * x ^ (2 * k)) =
      fun k => (c : 𝕜) * (y ^ 2) ^ k := by
    funext k
    rw [Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
    push_cast
    rw [hy]; ring
  have fo : (fun k : ℕ => ((c * q ^ (2 * N * ((2 * k + 1) / 2) + (2 * k + 1)) : ℕ) : 𝕜) * x ^ (2 * k + 1)) =
      fun k => ((c : 𝕜) * q * x) * (y ^ 2) ^ k := by
    funext k
    rw [show (2 * k + 1) / 2 = k by omega]
    push_cast
    rw [hy]; ring
  have he := hg.mul_left (c : 𝕜)
  have ho := hg.mul_left ((c : 𝕜) * q * x)
  rw [← fe] at he
  rw [← fo] at ho
  have := HasSum.even_add_odd (f := fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : 𝕜) * x ^ j) he ho
  rw [show (c : 𝕜) * (1 + q * x) / (1 - y ^ 2) = c * (1 - y ^ 2)⁻¹ + c * q * x * (1 - y ^ 2)⁻¹ by
    rw [div_eq_mul_inv]; ring]
  exact this

theorem genFun_diff_hasSum {𝕜 : Type} [NormedField 𝕜] (C d : ℕ → ℕ) (x S : 𝕜)
    (h0 : d 0 = C 0) (hs : ∀ j, C (j + 1) = C j + d (j + 1))
    (hA : HasSum (fun j => (C j : 𝕜) * x ^ j) S) :
    HasSum (fun j => (d j : 𝕜) * x ^ j) ((1 - x) * S) := by
  let h : ℕ → 𝕜 := fun j => if j = 0 then 0 else (C (j - 1) : 𝕜) * x ^ j
  have hsh : (fun n => h (n + 1)) = fun n => x * ((C n : 𝕜) * x ^ n) := by
    funext n
    simp only [h, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero n)]
    ring
  have h1 : HasSum (fun n => h (n + 1)) (x * S) := by rw [hsh]; exact hA.mul_left x
  have hh : HasSum h (x * S) := by
    have := (hasSum_nat_add_iff (f := h) 1).1 h1
    simpa [h] using this
  have hd : (fun j => (d j : 𝕜) * x ^ j) = fun j => (C j : 𝕜) * x ^ j - h j := by
    funext j
    rcases j with _ | j
    · simp [h, h0]
    · simp only [h, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, hs j]
      push_cast; ring
  rw [hd, show (1 - x) * S = S - x * S by ring]
  exact hA.sub hh

theorem genFun_fibre_hasSum {ι 𝕜 : Type} [NormedField 𝕜] (f : ι → ℕ) (l j : ℕ) (x : 𝕜)
    (hfin : Set.Finite {i | f i - l = j}) (hl : ∀ i, l ≤ f i) :
    HasSum (fun y : {i // f i - l = j} => x ^ f y.1) ((Set.ncard {i | f i - l = j} : 𝕜) * x ^ (l + j)) := by
  haveI : Finite {i // f i - l = j} := hfin.to_subtype
  haveI : Fintype {i // f i - l = j} := Fintype.ofFinite _
  have hc : ∀ y : {i // f i - l = j}, x ^ f y.1 = x ^ (l + j) := fun y => by
    have := hl y.1; have := y.2
    rw [show f y.1 = l + j by omega]
  have e : Nat.card {i // f i - l = j} = Set.ncard {i | f i - l = j} := Nat.card_coe_set_eq {i : ι | f i - l = j}
  have h := hasSum_fintype (fun y : {i // f i - l = j} => x ^ f y.1)
  rw [Finset.sum_congr rfl (fun y _ => hc y), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, e] at h
  exact h

theorem genFun_holds : GenFun := by
  intro ι f l c q N X hc hq hl hcard hX
  let C : ℕ → ℕ := fun j => c * q ^ (2 * N * (j / 2) + j)
  let g : ι → ℕ := fun i => f i - l
  have hCpos : ∀ j, C j ≠ 0 := fun j =>
    Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  have hle : ∀ j, {i | g i ≤ j} = {i | f i ≤ l + j} := fun j => by
    ext i; simp only [Set.mem_setOf_eq, g]; have := hl i; omega
  have hcum : ∀ j, Set.ncard {i | g i ≤ j} = C j := fun j => by
    rw [hle, ← Nat.card_coe_set_eq]; exact hcard j
  have hfin : ∀ j, Set.Finite {i | g i ≤ j} := fun j => by
    apply Set.finite_of_ncard_ne_zero; rw [hcum]; exact hCpos j
  have hfin' : ∀ j, Set.Finite {i | f i - l = j} := fun j =>
    (hfin j).subset fun i hi => by simp only [Set.mem_setOf_eq, g] at hi ⊢; omega
  let d : ℕ → ℕ := fun j => Set.ncard {i | f i - l = j}
  have h0 : d 0 = C 0 := by
    rw [← hcum 0]
    show Set.ncard {i | f i - l = 0} = _
    congr 1; ext i; simp only [Set.mem_setOf_eq, g]; omega
  have hs : ∀ j, C (j + 1) = C j + d (j + 1) := fun j => by
    have hdis : Disjoint {i | g i ≤ j} {i | f i - l = j + 1} :=
      Set.disjoint_left.2 fun i h1 h2 => by simp only [Set.mem_setOf_eq, g] at h1 h2; omega
    have hun : {i | g i ≤ j + 1} = {i | g i ≤ j} ∪ {i | f i - l = j + 1} := by
      ext i; simp only [Set.mem_setOf_eq, Set.mem_union, g]; omega
    rw [← hcum, ← hcum, hun, Set.ncard_union_eq hdis (hfin j) (hfin' (j + 1))]
  let e := Equiv.sigmaFiberEquiv g
  have hr : ‖(q : ℝ) ^ (N + 1) * ‖X‖‖ < 1 := by
    rw [norm_mul, norm_pow, Real.norm_natCast, norm_norm]
    rwa [norm_mul, norm_pow, Complex.norm_natCast] at hX
  have hRB := (genFun_diff_hasSum C d ‖X‖ _ h0 hs (genFun_counts_hasSum c q N ‖X‖ hr)).mul_left (‖X‖ ^ l)
  have hsumR : Summable (fun i => ‖X‖ ^ f i) := by
    rw [← e.summable_iff]
    refine (summable_sigma_of_nonneg (f := (fun i => ‖X‖ ^ f i) ∘ e) (fun _ => pow_nonneg (norm_nonneg _) _)).2 ⟨fun j => (genFun_fibre_hasSum f l j ‖X‖ (hfin' j) hl).summable, ?_⟩
    refine hRB.summable.congr fun j => ?_
    have ht : ∑' (y : {x // g x = j}), ((fun i => ‖X‖ ^ f i) ∘ e) ⟨j, y⟩ = (d j : ℝ) * ‖X‖ ^ (l + j) :=
      (genFun_fibre_hasSum f l j ‖X‖ (hfin' j) hl).tsum_eq
    rw [ht, pow_add]
    ring
  have hsumC : Summable (fun i => X ^ f i) := Summable.of_norm (by simpa [norm_pow] using hsumR)
  have hB := (genFun_diff_hasSum C d X _ h0 hs (genFun_counts_hasSum c q N X hX)).mul_left (X ^ l)
  have hBC : HasSum (fun j => (d j : ℂ) * X ^ (l + j)) (c * X ^ l * jFac q N X) := by
    have e1 : (fun j => (d j : ℂ) * X ^ (l + j)) = fun j => X ^ l * ((d j : ℂ) * X ^ j) := by
      funext j; rw [pow_add]; ring
    rw [e1, show (c : ℂ) * X ^ l * jFac q N X =
      X ^ l * ((1 - X) * (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2))) by unfold jFac; ring]
    exact hB
  have hsig := HasSum.sigma_of_hasSum (f := (fun i => X ^ f i) ∘ e) hBC
    (fun j => genFun_fibre_hasSum f l j X (hfin' j) hl) (e.summable_iff.2 hsumC)
  exact e.hasSum_iff.1 hsig

end GlobalTheory.InertZeta
end
end

section

open GlobalTheory.InertZeta

namespace GlobalTheory.InertZeta.LeviSum

theorem int_geom (β y₀ : ℂ) (hβ : β ≠ 0) (h1 : ‖y₀ * β‖ < 1) (h2 : ‖y₀ / β‖ < 1) :
    HasSum (fun a : ℤ => β ^ a * y₀ ^ a.natAbs) ((1 - y₀ * β)⁻¹ + y₀ / β * (1 - y₀ / β)⁻¹) := by
  apply HasSum.of_nat_of_neg_add_one
  · have e : ∀ n : ℕ, β ^ (n : ℤ) * y₀ ^ (n : ℤ).natAbs = (y₀ * β) ^ n := fun n => by
      simp [zpow_natCast, mul_pow, mul_comm]
    simp only [e]
    exact hasSum_geometric_of_norm_lt_one h1
  · have e : ∀ n : ℕ, β ^ (-((n : ℤ) + 1)) * y₀ ^ (-((n : ℤ) + 1)).natAbs = y₀ / β * (y₀ / β) ^ n := fun n => by
      rw [show (-((n : ℤ) + 1)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
        show (-((n + 1 : ℕ) : ℤ)).natAbs = n + 1 by omega, div_pow]
      field_simp
      ring
    simp only [e]
    exact (hasSum_geometric_of_norm_lt_one h2).mul_left (y₀ / β)

theorem q_pow (q : ℂ) (hq : q ≠ 0) (N : ℕ) (a : ℤ) :
    q ^ ((2 * N + 2) * a.toNat) * q ^ (-a * ((N : ℤ) + 1)) = (q ^ (N + 1)) ^ a.natAbs := by
  have h : ((a.natAbs : ℕ) : ℤ) = 2 * (a.toNat : ℤ) - a := by omega
  rw [← zpow_natCast, ← zpow_add₀ hq, ← pow_mul, ← zpow_natCast]
  congr 1
  rw [Nat.cast_mul, Nat.cast_mul, h]
  push_cast
  ring

theorem core (Y : Type) (q N : ℕ) (l : Y → ℕ) (ψ : Y → ℂ) (β X₀ Z₀ : ℂ) (hq : 1 ≤ q) (hβ : β ≠ 0)
    (hy : ‖(q : ℂ) ^ (N + 1) * X₀‖ < 1) (h1 : ‖(q : ℂ) ^ (N + 1) * X₀‖ * ‖β‖ < 1)
    (h2 : ‖(q : ℂ) ^ (N + 1) * X₀‖ * ‖β‖⁻¹ < 1)
    (hZ : HasSum (fun b => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) Z₀) :
    HasSum (fun p : ℤ × Y => ((q : ℂ) ^ (2 * l p.2 + (2 * N + 2) * p.1.toNat) * X₀ ^ (p.1.natAbs + l p.2) *
      jFac q N X₀) * (β ^ p.1 * (q : ℂ) ^ (-p.1 * ((N : ℤ) + 1)) * ψ p.2))
      ((1 - X₀) * (1 + q * X₀) * ((1 - (q : ℂ) ^ (N + 1) * X₀ * β)⁻¹ * (1 - (q : ℂ) ^ (N + 1) * X₀ / β)⁻¹) * Z₀) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  set y₀ := (q : ℂ) ^ (N + 1) * X₀ with hy₀
  have hA := int_geom β y₀ hβ (by rw [norm_mul]; exact h1) (by rw [norm_div, div_eq_mul_inv]; exact h2)
  have sA : Summable (fun a : ℤ => ‖β ^ a * y₀ ^ a.natAbs‖) := summable_norm_iff.mpr hA.summable
  have sB : Summable (fun b : Y => ‖((q : ℂ) ^ 2 * X₀) ^ l b * ψ b‖) := summable_norm_iff.mpr hZ.summable
  have sAB : Summable (fun p : ℤ × Y => (β ^ p.1 * y₀ ^ p.1.natAbs) * (((q : ℂ) ^ 2 * X₀) ^ l p.2 * ψ p.2)) :=
    summable_mul_of_summable_norm (f := fun a : ℤ => β ^ a * y₀ ^ a.natAbs)
      (g := fun b : Y => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) sA sB
  have hprod := (HasSum.mul (f := fun a : ℤ => β ^ a * y₀ ^ a.natAbs)
      (g := fun b : Y => ((q : ℂ) ^ 2 * X₀) ^ l b * ψ b) hA hZ sAB).mul_right (jFac q N X₀)
  have n1 : 1 - y₀ * β ≠ 0 := fun h => by
    have e : ‖y₀ * β‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
    rw [norm_mul] at e; linarith
  have n2 : 1 - y₀ / β ≠ 0 := fun h => by
    have e : ‖y₀ / β‖ = 1 := by rw [← sub_eq_zero.mp h, norm_one]
    rw [norm_div, div_eq_mul_inv] at e; linarith
  have hβy : β - y₀ ≠ 0 := fun h => n2 (by rw [← sub_eq_zero.mp h, div_self hβ, sub_self])
  have hβy' : -y₀ + β ≠ 0 := by rwa [neg_add_eq_sub]
  have n3 : 1 - y₀ ^ 2 ≠ 0 := fun h => by
    rw [sub_eq_zero] at h
    have := congrArg norm h
    rw [norm_one, norm_pow] at this
    nlinarith [norm_nonneg y₀]
  have ev : ((1 - y₀ * β)⁻¹ + y₀ / β * (1 - y₀ / β)⁻¹) * Z₀ * jFac q N X₀ =
      (1 - X₀) * (1 + q * X₀) * ((1 - y₀ * β)⁻¹ * (1 - y₀ / β)⁻¹) * Z₀ := by
    simp only [jFac]
    rw [← hy₀]
    field_simp
    ring
  rw [← ev]
  convert hprod using 1
  funext p
  obtain ⟨a, b⟩ := p
  simp only
  rw [hy₀, mul_pow, ← q_pow (q : ℂ) hq0 N a, pow_add, pow_add, mul_pow, ← pow_mul]
  ring

end GlobalTheory.InertZeta.LeviSum

namespace GlobalTheory.InertZeta


open LeviSum in
theorem step : Step := by
  intro Y C q N ℓ l φ₀ α X y Z hq hα hy hy1 hyα hyα' H hZ
  subst hy
  have hg := core Y q N l φ₀ α X Z hq hα hy1 hyα hyα' hZ
  have hfib : ∀ ab : ℤ × Y, HasSum (fun c => X ^ ℓ ab.1 ab.2 c *
      (α ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * φ₀ ab.2))
      (((q : ℂ) ^ (2 * l ab.2 + (2 * N + 2) * ab.1.toNat) * X ^ (ab.1.natAbs + l ab.2) * jFac q N X) *
        (α ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * φ₀ ab.2)) :=
    fun ab => (H X hy1 ab.1 ab.2).mul_right _

  have hXn : ‖(q : ℂ) ^ (N + 1) * ((‖X‖ : ℝ) : ℂ)‖ = ‖(q : ℂ) ^ (N + 1) * X‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have hαn : ‖((‖α‖ : ℝ) : ℂ)‖ = ‖α‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  have hZn : Summable (fun b => ((q : ℂ) ^ 2 * ((‖X‖ : ℝ) : ℂ)) ^ l b * ((‖φ₀ b‖ : ℝ) : ℂ)) := by
    have := Complex.summable_ofReal.mpr (summable_norm_iff.mpr hZ.summable)
    convert this using 2 with b
    push_cast [norm_mul, norm_pow, Complex.norm_natCast]
    ring
  have hgn := core Y q N l (fun b => ((‖φ₀ b‖ : ℝ) : ℂ)) ((‖α‖ : ℝ) : ℂ) ((‖X‖ : ℝ) : ℂ) _ hq
    (by exact_mod_cast norm_ne_zero_iff.mpr hα) (hXn ▸ hy1) (by rw [hXn, hαn]; exact hyα)
    (by rw [hXn, hαn]; exact hyα') hZn.hasSum
  have hfibn : ∀ ab : ℤ × Y, HasSum (fun c => ((‖X‖ : ℝ) : ℂ) ^ ℓ ab.1 ab.2 c *
      (((‖α‖ : ℝ) : ℂ) ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * ((‖φ₀ ab.2‖ : ℝ) : ℂ)))
      (((q : ℂ) ^ (2 * l ab.2 + (2 * N + 2) * ab.1.toNat) * ((‖X‖ : ℝ) : ℂ) ^ (ab.1.natAbs + l ab.2) *
        jFac q N ((‖X‖ : ℝ) : ℂ)) *
        (((‖α‖ : ℝ) : ℂ) ^ ab.1 * (q : ℂ) ^ (-ab.1 * ((N : ℤ) + 1)) * ((‖φ₀ ab.2‖ : ℝ) : ℂ))) :=
    fun ab => (H _ (hXn ▸ hy1) ab.1 ab.2).mul_right _
  have hnorm : ∀ p : (ℤ × Y) × C,
      ((‖X ^ ℓ p.1.1 p.1.2 p.2 * (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2)‖ : ℝ) : ℂ) =
      ((‖X‖ : ℝ) : ℂ) ^ ℓ p.1.1 p.1.2 p.2 *
        (((‖α‖ : ℝ) : ℂ) ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * ((‖φ₀ p.1.2‖ : ℝ) : ℂ)) := by
    intro p
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_zpow, norm_zpow, Complex.norm_natCast]
    push_cast
    rfl
  have hsum : Summable (fun p : (ℤ × Y) × C =>
      X ^ ℓ p.1.1 p.1.2 p.2 * (α ^ p.1.1 * (q : ℂ) ^ (-p.1.1 * ((N : ℤ) + 1)) * φ₀ p.1.2)) := by
    rw [← summable_norm_iff, summable_prod_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun ab => ?_, ?_⟩
    · rw [← Complex.summable_ofReal]
      exact (funext fun c => (hnorm (ab, c)).symm) ▸ (hfibn ab).summable
    · rw [← Complex.summable_ofReal]
      refine hgn.summable.congr fun ab => ?_
      rw [Complex.ofReal_tsum]
      exact ((funext fun c => (hnorm (ab, c)).symm) ▸ (hfibn ab)).tsum_eq.symm
  rw [hg.unique (hsum.hasSum.prod_fiberwise hfib)]
  exact hsum.hasSum

end GlobalTheory.InertZeta
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.det_restrict_range_idempotent_matrix : GlobalTheory.RegSS.IdempotentDet := by
  first | exact @GlobalTheory.RegSS.idempotentDet | exact GlobalTheory.RegSS.idempotentDet | (intros; apply GlobalTheory.RegSS.idempotentDet <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.split_factor_idempotents_exist : GlobalTheory.RegSS.SplitIdempotents := by
  first | exact @GlobalTheory.RegSS.splitIdempotents | exact GlobalTheory.RegSS.splitIdempotents | (intros; apply GlobalTheory.RegSS.splitIdempotents <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.adelic_unit_translate_bounded_of_factors : GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.ProductUnitBounded := by
  first | exact @GlobalTheory.RegSS.productUnitBounded | exact GlobalTheory.RegSS.productUnitBounded | (intros; apply GlobalTheory.RegSS.productUnitBounded <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.nontrivial_split_subtorus_not_central : GlobalTheory.RegSS.UnitaryCommutant → GlobalTheory.RegSS.SubtorusLaurent → GlobalTheory.RegSS.CharacterMonomial → GlobalTheory.RegSS.SubtorusNotCentral := by
  first | exact @GlobalTheory.RegSS.subtorusNotCentral_of | exact GlobalTheory.RegSS.subtorusNotCentral_of | (intros; apply GlobalTheory.RegSS.subtorusNotCentral_of <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.product_fields_baseChange_isField_iff : GlobalTheory.RegSS.TensorFieldIff := by
  first | exact @GlobalTheory.RegSS.tensorFieldIff | exact GlobalTheory.RegSS.tensorFieldIff | (intros; apply GlobalTheory.RegSS.tensorFieldIff <;> assumption)
end

section

open GlobalTheory.RegSS

theorem _root_.GlobalTheory.T.regularSemisimple_selfAdjointPart_etale : GlobalTheory.RegSS.PlusEtale := by
  first | exact @GlobalTheory.RegSS.plusEtale | exact GlobalTheory.RegSS.plusEtale | (intros; apply GlobalTheory.RegSS.plusEtale <;> assumption)
end
