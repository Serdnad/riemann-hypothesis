module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle006
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle009
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Order.Real
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle011
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle012
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Polish
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Metric

namespace GlobalTheory

theorem exists_net_card_le_of_subset_closedBall :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (S : Set E)
      (R δ : ℝ), 0 < δ → 0 ≤ R → S ⊆ closedBall 0 R →
      ∃ T : Finset E, (T : Set E) ⊆ S ∧ (T.card : ℝ) ≤ (1 + 2 * R / δ) ^ Module.finrank ℝ E ∧
        ∀ x ∈ S, ∃ t ∈ T, dist x t ≤ δ := by
  intro E _ _ _ S R δ hδ hR hS
  classical
  let P : Finset E → Prop := fun T =>
    (T : Set E) ⊆ S ∧ (T : Set E).Pairwise fun a b => δ ≤ dist a b
  have hb : ∀ T, P T → (T.card : ℝ) ≤ (1 + 2 * R / δ) ^ Module.finrank ℝ E := fun T hT =>
    finset_card_le_of_separated T hδ hR 0 (fun a ha => hS (hT.1 ha)) hT.2
  obtain ⟨N, hN⟩ := exists_nat_ge ((1 + 2 * R / δ) ^ Module.finrank ℝ E)
  let Q : ℕ → Prop := fun n => ∃ T, P T ∧ T.card = n
  have hQ0 : Q 0 := ⟨∅, ⟨by simp, by simp⟩, rfl⟩
  obtain ⟨T, hT, hTc⟩ : Q (Nat.findGreatest Q N) := Nat.findGreatest_spec (Nat.zero_le N) hQ0
  refine ⟨T, hT.1, hb T hT, fun x hx => ?_⟩
  by_contra hcon
  push Not at hcon
  have hxT : x ∉ T := fun h => by
    have := hcon x h
    rw [dist_self] at this
    linarith
  have hP : P (insert x T) := by
    refine ⟨?_, ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset hx hT.1
    · rw [Finset.coe_insert]
      refine hT.2.insert fun b hb' _ => ⟨(hcon b hb').le, ?_⟩
      rw [dist_comm]
      exact (hcon b hb').le
  have hle : (insert x T).card ≤ N := by
    exact_mod_cast (hb _ hP).trans hN
  have := Nat.le_findGreatest (P := Q) hle ⟨_, hP, rfl⟩
  rw [Finset.card_insert_of_notMem hxT] at this
  omega

end GlobalTheory
end

section

open Finset

namespace GlobalTheory

theorem exists_dyadic_shell_index (ep : ℝ) (hep : 0 < ep) :
    ∃ sh : ℝ → ℕ, (∀ s, s ≤ 2 ^ sh s * ep) ∧ ∀ s j, j < sh s → 2 ^ j * ep < s := by
  classical
  have hex : ∀ s : ℝ, ∃ n : ℕ, s ≤ 2 ^ n * ep := by
    intro s
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / ep) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hep] at hn
    exact hn.le
  refine ⟨fun s => Nat.find (hex s), fun s => Nat.find_spec (hex s), fun s j hj => ?_⟩
  exact not_le.mp (Nat.find_min (hex s) hj)

theorem sum_prod_box_erase_zero (ι : Type) [Fintype ι] [DecidableEq ι] (W : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ (Fintype.piFinset (fun _ : ι => range (N + 1))).erase (fun _ => 0), ∏ v, W (k v)
      = (W 0 + ∑ i ∈ range N, W (i + 1)) ^ Fintype.card ι - W 0 ^ Fintype.card ι := by
  classical
  have hz : (fun _ : ι => (0 : ℕ)) ∈ Fintype.piFinset (fun _ : ι => range (N + 1)) := by
    simp [Fintype.mem_piFinset]
  rw [Finset.sum_erase_eq_sub hz,
    ← Finset.prod_univ_sum (fun _ : ι => range (N + 1)) (fun _ j => W j),
    Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.sum_range_succ', add_comm]

theorem sum_over_dyadic_shells :
    ∀ (Γ ι : Type) [Fintype ι] (d : Γ → ι → ℝ) (w : Γ → ℝ) (A κ h ep c : ℝ), 0 ≤ A → 0 ≤ κ → 0 < ep → 0 < c → ep ≤ 1 / c → κ * ep ≤ Real.log 2 → 32 * κ ≤ h * ep → 1 ≤ h * ep ^ 2 / 16 → (∀ γ v, 0 ≤ d γ v) → (∀ r : ι → ℝ, (∀ v, 0 ≤ r v) → {γ | ∀ v, d γ v ≤ r v}.Finite ∧ (({γ | ∀ v, d γ v ≤ r v}.ncard : ℕ) : ℝ) ≤ A * Real.exp (κ * ∑ v, r v)) → (∀ γ, ∃ v, ep < d γ v) → (∀ γ, 0 ≤ w γ ∧ w γ ≤ ∏ v, Real.exp (-(h / 8) * min (d γ v ^ 2) (d γ v / c))) → Summable w ∧ ∑' γ, w γ ≤ A * (2 * Fintype.card ι * 3 ^ Fintype.card ι * Real.exp (-(h * ep ^ 2 / 16))) := by
  intro Γ ι _ d w A κ h ep c hA hκ hep hc hepc hκep hh hT hd hcount hfar hw
  classical
  obtain ⟨sh, hsh1, hsh2⟩ := exists_dyadic_shell_index ep hep
  obtain ⟨hineq, -, hpow⟩ := shell_sum_elementary_inequalities
  set T : ℝ := h * ep ^ 2 / 16 with hTdef
  have hhpos : 0 < h := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    have h1 : h * ep ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (sq_nonneg ep)
    linarith
  have hκT : κ * ep ≤ T / 2 := by
    have h1 : 32 * κ * ep ≤ h * ep * ep := mul_le_mul_of_nonneg_right hh hep.le
    rw [hTdef]
    nlinarith

  let F : ℕ → ℝ := fun j => if j = 0 then 1 else Real.exp (-T * 2 ^ j)
  let W : ℕ → ℝ := fun j => Real.exp (κ * (2 ^ j * ep)) * F j
  let K : Γ → ι → ℕ := fun γ v => sh (d γ v)
  have hF0 : ∀ j, 0 ≤ F j := by
    intro j
    simp only [F]
    split_ifs
    · exact zero_le_one
    · exact (Real.exp_pos _).le
  have hW0 : ∀ j, 0 ≤ W j := fun j => mul_nonneg (Real.exp_pos _).le (hF0 j)

  have hwF : ∀ γ, w γ ≤ ∏ v, F (K γ v) := by
    intro γ
    refine (hw γ).2.trans (Finset.prod_le_prod₀ (fun v _ => (Real.exp_pos _).le) (fun v _ => ?_))
    have hmin0 : 0 ≤ min (d γ v ^ 2) (d γ v / c) := le_min (sq_nonneg _) (div_nonneg (hd γ v) hc.le)
    simp only [F, K]
    split_ifs with hk
    · rw [Real.exp_le_one_iff]
      nlinarith
    · rw [Real.exp_le_exp]
      have hlt : sh (d γ v) - 1 < sh (d γ v) := Nat.sub_lt (Nat.pos_of_ne_zero hk) one_pos
      have hbig := hsh2 (d γ v) _ hlt
      have hp1 : (1 : ℝ) ≤ 2 ^ (sh (d γ v) - 1) := one_le_pow₀ (by norm_num)
      have hge : ep ≤ d γ v := by nlinarith
      have hm := hineq (d γ v) ep c hep hge hc hepc
      have h2 : (2 : ℝ) ^ sh (d γ v) = 2 * 2 ^ (sh (d γ v) - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hm2 : ep ^ 2 * 2 ^ (sh (d γ v) - 1) ≤ min (d γ v ^ 2) (d γ v / c) := by
        have : ep * (2 ^ (sh (d γ v) - 1) * ep) ≤ ep * d γ v :=
          mul_le_mul_of_nonneg_left hbig.le hep.le
        nlinarith
      have hm3 := mul_le_mul_of_nonneg_left hm2 hhpos.le
      rw [h2, hTdef]
      nlinarith

  have hfib : ∀ (u : Finset Γ) (k : ι → ℕ),
      ((u.filter fun γ => K γ = k).card : ℝ) ≤ A * ∏ v, Real.exp (κ * (2 ^ k v * ep)) := by
    intro u k
    have hr : ∀ v, 0 ≤ (2 : ℝ) ^ k v * ep := fun v => mul_nonneg (pow_nonneg (by norm_num) _) hep.le
    obtain ⟨hfin, hcard⟩ := hcount (fun v => 2 ^ k v * ep) hr
    have hsub : ((u.filter fun γ => K γ = k : Finset Γ) : Set Γ) ⊆ {γ | ∀ v, d γ v ≤ 2 ^ k v * ep} := by
      intro γ hγ
      have hγ' := Finset.mem_filter.mp (Finset.mem_coe.mp hγ)
      intro v
      have := hsh1 (d γ v)
      rw [← hγ'.2]
      exact this
    have hle := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at hle
    calc ((u.filter fun γ => K γ = k).card : ℝ)
        ≤ (({γ | ∀ v, d γ v ≤ 2 ^ k v * ep}.ncard : ℕ) : ℝ) := by exact_mod_cast hle
      _ ≤ A * Real.exp (κ * ∑ v, 2 ^ k v * ep) := hcard
      _ = A * ∏ v, Real.exp (κ * (2 ^ k v * ep)) := by
        rw [Finset.mul_sum, Real.exp_sum]

  have hpart : ∀ u : Finset Γ, ∑ γ ∈ u, w γ
      ≤ A * (2 * Fintype.card ι * 3 ^ Fintype.card ι * Real.exp (-(h * ep ^ 2 / 16))) := by
    intro u
    set N : ℕ := u.sup fun γ => Finset.univ.sup (K γ) with hN
    set B := (Fintype.piFinset fun _ : ι => range (N + 1)).erase (fun _ => 0) with hB
    have hmaps : ∀ γ ∈ u, K γ ∈ B := by
      intro γ hγ
      rw [hB, Finset.mem_erase, Fintype.mem_piFinset]
      refine ⟨?_, fun v => ?_⟩
      · intro h0
        obtain ⟨v, hv⟩ := hfar γ
        have h1 : K γ v = 0 := congrFun h0 v
        have h2 := hsh1 (d γ v)
        simp only [K] at h1
        rw [h1, pow_zero, one_mul] at h2
        linarith
      · rw [Finset.mem_range, Nat.lt_succ_iff]
        exact (Finset.le_sup (f := K γ) (Finset.mem_univ v)).trans
          (Finset.le_sup (f := fun γ => Finset.univ.sup (K γ)) hγ)
    have hal0 : 0 ≤ W 0 := hW0 0
    have hal2 : W 0 ≤ 2 := by
      show Real.exp (κ * (2 ^ 0 * ep)) * (if (0 : ℕ) = 0 then 1 else Real.exp (-T * 2 ^ 0)) ≤ 2
      rw [if_pos rfl, pow_zero, one_mul, mul_one]
      calc Real.exp (κ * ep) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hκep
        _ = 2 := Real.exp_log (by norm_num)
    have hT1 : 1 ≤ T := hT
    have hWs : ∀ i, W (i + 1) ≤ Real.exp (-T) * (1 / 2 : ℝ) ^ i := by
      intro i
      refine le_trans ?_ (exp_neg_mul_two_pow_le_geometric T hT1 i)
      simp only [W, F, if_neg (Nat.succ_ne_zero i)]
      rw [← Real.exp_add, Real.exp_le_exp, pow_succ]
      have hp : (0 : ℝ) ≤ 2 ^ i := pow_nonneg (by norm_num) _
      nlinarith
    have hexpT : Real.exp (-T) ≤ 1 / 2 := by
      have h1 : Real.exp (-T) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      have h2 : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
      have h3 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
      have h4 : 0 < Real.exp (-1) := Real.exp_pos _
      nlinarith
    have hbe : ∑ i ∈ range N, W (i + 1) ≤ 2 * Real.exp (-T) := by
      calc ∑ i ∈ range N, W (i + 1) ≤ ∑ i ∈ range N, Real.exp (-T) * (1 / 2 : ℝ) ^ i :=
            Finset.sum_le_sum fun i _ => hWs i
        _ = Real.exp (-T) * ∑ i ∈ range N, (1 / 2 : ℝ) ^ i := by rw [Finset.mul_sum]
        _ ≤ Real.exp (-T) * 2 :=
            mul_le_mul_of_nonneg_left (sum_geometric_two_le N) (Real.exp_pos _).le
        _ = 2 * Real.exp (-T) := mul_comm _ _
    have hbe0 : 0 ≤ ∑ i ∈ range N, W (i + 1) := Finset.sum_nonneg fun i _ => hW0 _
    have hbe1 : ∑ i ∈ range N, W (i + 1) ≤ 1 := by linarith
    have hbox := sum_prod_box_erase_zero ι W N
    have key := hpow (W 0) (∑ i ∈ range N, W (i + 1)) (Fintype.card ι) hal0 hal2 hbe0 hbe1
    calc ∑ γ ∈ u, w γ ≤ ∑ γ ∈ u, ∏ v, F (K γ v) := Finset.sum_le_sum fun γ _ => hwF γ
      _ = ∑ k ∈ B, ∑ γ ∈ u with K γ = k, ∏ v, F (k v) :=
          (Finset.sum_fiberwise_of_maps_to' hmaps (fun k => ∏ v, F (k v))).symm
      _ = ∑ k ∈ B, ((u.filter fun γ => K γ = k).card : ℝ) * ∏ v, F (k v) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ B, (A * ∏ v, Real.exp (κ * (2 ^ k v * ep))) * ∏ v, F (k v) :=
          Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_right (hfib u k) (Finset.prod_nonneg fun v _ => hF0 _)
      _ = A * ∑ k ∈ B, ∏ v, W (k v) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_assoc, ← Finset.prod_mul_distrib]
      _ = A * ((W 0 + ∑ i ∈ range N, W (i + 1)) ^ Fintype.card ι - W 0 ^ Fintype.card ι) := by
          rw [hB, hbox]
      _ ≤ A * (Fintype.card ι * (2 * Real.exp (-T)) * 3 ^ Fintype.card ι) := by
          refine mul_le_mul_of_nonneg_left (key.trans ?_) hA
          have h3 : (0 : ℝ) ≤ 3 ^ Fintype.card ι := pow_nonneg (by norm_num) _
          have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbe hn) h3
      _ = A * (2 * Fintype.card ι * 3 ^ Fintype.card ι * Real.exp (-(h * ep ^ 2 / 16))) := by
          rw [hTdef]
          ring
  have hw0 : 0 ≤ w := fun γ => (hw γ).1
  exact ⟨summable_of_sum_le hw0 hpart, Real.tsum_le_of_sum_le hw0 hpart⟩

end GlobalTheory
end

section

open NumberField Finset

namespace GlobalTheory.IdealBoundedNorm

theorem finite_setOf_absNorm_le (K : Type) [Field K] [NumberField K] (Y : ℝ) :
    {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}.Finite := by
  refine ((Finset.range (⌊Y⌋₊ + 1) : Set ℕ).toFinite.biUnion
    fun n _ => Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).subset ?_
  rintro I ⟨-, hI⟩
  refine Set.mem_biUnion (x := Ideal.absNorm I) ?_ rfl
  simpa [Nat.lt_succ_iff] using Nat.le_floor hI

theorem ncard_absNorm_le_pow_pred (K : Type) [Field K] [NumberField K] (Y : ℝ) (hY : 1 ≤ Y) :
    ((({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}).ncard : ℕ) : ℝ)
      ≤ Y * (1 + Real.log Y) ^ (Module.finrank ℚ K - 1) := by
  classical
  have hS := finite_setOf_absNorm_le K Y

  have key : ({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}).ncard
      ≤ ∑ n ∈ Ioc 0 ⌊Y⌋₊, (ArithmeticFunction.zeta ^ Module.finrank ℚ K : ArithmeticFunction ℕ) n := by
    rw [← hS.coe_toFinset, Set.ncard_coe_finset]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun I => Ideal.absNorm I) (t := Ioc 0 ⌊Y⌋₊) ?_]
    · refine Finset.sum_le_sum fun n hn => ?_
      refine le_trans ?_ (GlobalTheory.ncard_ideal_absNorm_eq_le K (Finset.mem_Ioc.1 hn).1.ne')
      rw [← Set.ncard_coe_finset]
      refine Set.ncard_le_ncard ?_ (Ideal.finite_setOfPred_absNorm_eq n)
      intro I hI
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hI ⊢
      exact hI.2
    · intro I hI
      simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq] at hI
      simp only [Finset.coe_Ioc, Set.mem_Ioc]
      exact ⟨Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 hI.1), Nat.le_floor hI.2⟩
  have hm : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  calc ((({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}).ncard : ℕ) : ℝ)
      ≤ ((∑ n ∈ Ioc 0 ⌊Y⌋₊,
          (ArithmeticFunction.zeta ^ Module.finrank ℚ K : ArithmeticFunction ℕ) n : ℕ) : ℝ) := by
        exact_mod_cast key
    _ ≤ Y * (1 + Real.log Y) ^ (Module.finrank ℚ K - 1) := GlobalTheory.sum_zeta_pow_le hm hY

theorem ncard_absNorm_le : ∀ (K : Type) [Field K] [NumberField K] (Y : ℝ), 1 ≤ Y →
    ((({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ Y}).ncard : ℕ) : ℝ)
      ≤ Y * (1 + Real.log Y) ^ Module.finrank ℚ K := by
  intro K _ _ Y hY
  refine (ncard_absNorm_le_pow_pred K Y hY).trans ?_
  have hl : 1 ≤ 1 + Real.log Y := by linarith [Real.log_nonneg hY]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hl (Nat.sub_le _ _)) (by linarith)

end GlobalTheory.IdealBoundedNorm
end

section

open Finset

namespace GlobalTheory

theorem packing_geometric_mean_subspaces : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (U : ι → Submodule ℝ W) (N : ℕ), (∀ v, Module.finrank ℝ (U v) ≤ N) → ∀ (α : Type) (T : Finset α) (y : α → ι → W) (la X : ℝ), 0 < la → 0 < X → (∀ t ∈ T, ∀ v, y t v ∈ U v ∧ ‖y t v‖ ≤ X) → (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → la ≤ (∏ v, ‖y t v - y t' v‖) ^ ((1 : ℝ) / Fintype.card ι)) → (T.card : ℝ) ≤ (1 + 2 * X / la) ^ (N * Fintype.card ι) := by
  intro ι _ _ W _ _ _ U N hU α T y la X hla hX hT hsep
  classical
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hexp : (1 : ℝ) / Fintype.card ι ≠ 0 := by
    have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hcard
    positivity

  have hinj : Set.InjOn y T := by
    intro t ht t' ht' he
    by_contra hne
    have h := hsep t ht t' ht' hne
    rw [he] at h
    simp only [sub_self, norm_zero] at h
    have h0 : (∏ _v : ι, (0 : ℝ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary ι)) rfl
    rw [h0, Real.zero_rpow hexp] at h
    linarith
  rcases Nat.eq_zero_or_pos N with hN | hN
  ·
    subst hN
    have hzero : ∀ t ∈ T, y t = 0 := by
      intro t ht
      funext v
      have hb : U v = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp (hU v))
      have hm := (hT t ht v).1
      rw [hb, Submodule.mem_bot] at hm
      exact hm
    have h1 : T.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      exact hinj ha hb (by rw [hzero a ha, hzero b hb])
    simp only [zero_mul, pow_zero]
    exact_mod_cast h1
  ·
    have key := packing_geometric_mean_separated ι
      (fun v => ↥(U v) × (Fin (N - Module.finrank ℝ (U v)) → ℝ)) N hN
      (fun v => by
        simp only [Module.finrank_prod, Module.finrank_fin_fun]
        have := hU v
        omega)
      la
      (↑(T.attach.image (fun t : T => fun v =>
        ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)))))
      (fun _ => X) hla (fun _ => hX)
    have hnormpt : ∀ (v : ι) (a : U v),
        ‖((a, (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)) :
          ↥(U v) × (Fin (N - Module.finrank ℝ (U v)) → ℝ))‖ = ‖(a : W)‖ := by
      intro v a
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
      rfl
    obtain ⟨-, hbound⟩ := key (by
      intro s hs s' hs' hne
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach,
        true_and] at hs hs'
      obtain ⟨a, rfl⟩ := hs
      obtain ⟨b, rfl⟩ := hs'
      have hab : (a : α) ≠ b := by
        intro h
        apply hne
        rw [Subtype.ext h]
      have e : ∀ v, ‖((⟨y a v, (hT a a.2 v).1⟩ : U v),
            (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)) -
          ((⟨y b v, (hT b b.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ))‖ =
          ‖y a v - y b v‖ := by
        intro v
        rw [Prod.mk_sub_mk, sub_zero, hnormpt]
        rfl
      simp only [e]
      exact hsep a a.2 b b.2 hab)
    have hset : {s ∈ (↑(T.attach.image (fun t : T => fun v =>
        ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)))) :
          Set (∀ v, ↥(U v) × (Fin (N - Module.finrank ℝ (U v)) → ℝ))) |
          ∀ v, ‖s v‖ ≤ (fun _ => X) v} =
        ↑(T.attach.image (fun t : T => fun v =>
          ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ)))) := by
      apply Set.sep_eq_self_iff_mem_true.mpr
      intro s hs
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_attach,
        true_and] at hs
      obtain ⟨a, rfl⟩ := hs
      intro v
      rw [hnormpt]
      exact (hT a a.2 v).2
    have hinj' : Function.Injective (fun t : T => fun v =>
        ((⟨y t v, (hT t t.2 v).1⟩ : U v), (0 : Fin (N - Module.finrank ℝ (U v)) → ℝ))) := by
      intro a b hab
      apply Subtype.ext
      apply hinj a.2 b.2
      funext v
      have := congrFun hab v
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at this
      exact this.1
    rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj',
      Finset.card_attach] at hbound
    have hX' : (∏ _v : ι, X) ^ ((1 : ℝ) / Fintype.card ι) = X := by
      rw [Finset.prod_const, Finset.card_univ, one_div]
      exact Real.pow_rpow_inv_natCast hX.le hcard.ne'
    rw [hX'] at hbound
    exact hbound

end GlobalTheory
end

section

open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.sum_fibre_two_index_encard_bound : ∀ (α Θ : Type) (S : Finset α) (xf yf : α → ℕ) (Φ : α → Θ) (Tr : ℕ → ℕ → Set Θ) (f : α → ℝ) (B₁ B₂ : ℕ → ℝ) (R₁ R₂ : Finset ℕ), (∀ a ∈ S, 0 ≤ f a) → (∀ a ∈ S, xf a ∈ R₁ ∧ yf a ∈ R₂ ∧ Φ a ∈ Tr (xf a) (yf a)) → (∀ a ∈ S, ∑ b ∈ S.filter (fun b => Φ b = Φ a ∧ xf b = xf a ∧ yf b = yf a), f b ≤ B₁ (xf a) * B₂ (yf a)) → ENNReal.ofReal (∑ a ∈ S, f a) ≤ ∑ x ∈ R₁, ∑ y ∈ R₂, (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
  first | exact @GlobalTheory.sum_fibre_two_index_bound | exact GlobalTheory.sum_fibre_two_index_bound | (intros; apply GlobalTheory.sum_fibre_two_index_bound <;> assumption)
end

section

open scoped ENNReal

theorem _root_.GlobalTheory.T.tsum_inv_card_stabilizer_eq_tsum_mul_card_fiber : ∀ {Γ L Y : Type} [Group Γ] [MulAction Γ L] [MulAction Γ Y] (π : L → Y), (∀ (g : Γ) (x : L), π (g • x) = g • π x) → (∀ y : Y, (∃ x, π x = y) → Finite (MulAction.stabilizer Γ y)) → (∑' o : MulAction.orbitRel.Quotient Γ L, (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹) = ∑' o : MulAction.orbitRel.Quotient Γ Y, (((MulAction.stabilizer Γ o.out : Set Γ).encard : ℝ≥0∞))⁻¹ * (((π ⁻¹' {o.out}).encard : ℝ≥0∞)) := by
  first | exact @GlobalTheory.tsum_inv_stabilizer_eq_tsum_mul_fiber | exact GlobalTheory.tsum_inv_stabilizer_eq_tsum_mul_fiber | (intros; apply GlobalTheory.tsum_inv_stabilizer_eq_tsum_mul_fiber <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_unitary_mulVec_eq_of_form_eq' : ∀ (E : Type) [Field E] [CharZero E] [StarRing E] (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Jᴴ = J → J.det ≠ 0 → ∀ x y : Fin n → E, star x ⬝ᵥ (J *ᵥ x) = star y ⬝ᵥ (J *ᵥ y) → star x ⬝ᵥ (J *ᵥ x) ≠ 0 → ∃ γ : Matrix (Fin n) (Fin n) E, γᴴ * J * γ = J ∧ γ *ᵥ x = y := by
  first | exact @GlobalTheory.exists_unitary_mulVec_eq_of_form_eq | exact GlobalTheory.exists_unitary_mulVec_eq_of_form_eq | (intros; apply GlobalTheory.exists_unitary_mulVec_eq_of_form_eq <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.measurableSet_iwasawa_slice_of_transversal : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G] (N M K : Subgroup G) (σ : G → G), MeasurableSet (N : Set G) → MeasurableSet (M : Set G) → MeasurableSet (K : Set G) → Measurable σ → (∀ x, σ x * x⁻¹ ∈ K ⊓ M) → (∀ l ∈ K ⊓ M, ∀ x, σ (l * x) = σ x) → (∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N) → (∀ u ∈ N, ∀ m ∈ M, u * m ∈ K → u = 1) → ∀ DN DM : Set G, MeasurableSet DN → MeasurableSet DM → ∃ D : Set G, MeasurableSet D ∧ ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, (u * m * k ∈ D ↔ u ∈ DN ∧ m * (k * (σ k)⁻¹) ∈ DM) := by
  first | exact @GlobalTheory.exists_measurableSet_slice_of_transversal | exact GlobalTheory.exists_measurableSet_slice_of_transversal | (intros; apply GlobalTheory.exists_measurableSet_slice_of_transversal <;> assumption)
end
