module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle763
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle684
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle765
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012

@[expose] public section

section

open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL

theorem numBlockSetsOfTotalSize_zero {r : ℕ} (b : Fin r → ℕ) : splitDoublingNBlock b 0 = 1 := by
  unfold splitDoublingNBlock
  rw [Finset.card_eq_one]
  refine ⟨∅, ?_⟩
  ext J
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (h1 hx)
    have : i ∈ Finset.univ.filter fun i => b i ∈ J := by simp [hx]
    rw [h2] at this
    simp at this
  · rintro rfl
    simp

theorem numBlockSetsOfTotalSize_le_choose {r : ℕ} (b : Fin r → ℕ) (j : ℕ) : splitDoublingNBlock b j ≤ r.choose j := by
  unfold splitDoublingNBlock
  have h : r.choose j = (Finset.powersetCard j (Finset.univ : Finset (Fin r))).card := by simp
  rw [h]
  refine Finset.card_le_card_of_injOn (fun J => Finset.univ.filter fun i => b i ∈ J) ?_ ?_
  · intro J hJ
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hJ
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hJ.2⟩
  · intro J hJ K hK hJK
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_powerset] at hJ hK
    have key : ∀ i, b i ∈ J ↔ b i ∈ K := fun i => by
      have := Finset.ext_iff.1 hJK i
      simpa using this
    ext x
    constructor
    · intro hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (hJ.1 hx)
      exact (key i).1 hx
    · intro hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (hK.1 hx)
      exact (key i).2 hx

theorem gam_le_pow (q l : ℕ) : gam q l ≤ q ^ l := by
  unfold gam
  split_ifs with h
  · simp [h]
  · exact Nat.sub_le _ _

theorem gam_cast {q k : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k) :
    (gam q k : ℝ) = (q : ℝ) ^ k * (1 - 1 / (q : ℝ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  unfold gam
  rw [if_neg (by omega), Nat.add_sub_cancel, Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]
  push_cast
  field_simp
  ring

theorem one_add_pow_le_two_mul {x : ℝ} (hx : 0 ≤ x) {r : ℕ} (h : (r : ℝ) * x ≤ 1) :
    (1 + x) ^ r ≤ 1 + 2 * (r * x) := by
  have h0 : 0 ≤ (r : ℝ) * x := by positivity
  have h1 : (1 + x) ^ r ≤ Real.exp x ^ r :=
    pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp x]) r
  rw [← Real.exp_nat_mul] at h1
  have h2 := Real.abs_exp_sub_one_le (x := r * x) (by rwa [abs_of_nonneg h0])
  rw [abs_of_nonneg h0] at h2
  linarith [(abs_le.1 h2).2]

theorem sum_choose_mul_pow_le {x : ℝ} (hx : 0 ≤ x) (r k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (r.choose j : ℝ) * x ^ j ≤ (1 + x) ^ r := by
  have h1 : ∑ j ∈ Finset.range (k + 1), (r.choose j : ℝ) * x ^ j
      ≤ ∑ j ∈ Finset.range (k + r + 1), (r.choose j : ℝ) * x ^ j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
      (fun _ _ _ => by positivity)
  have h2 : ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * x ^ j
      = ∑ j ∈ Finset.range (k + r + 1), (r.choose j : ℝ) * x ^ j := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) ?_
    intro j _ hj
    rw [Nat.choose_eq_zero_of_lt (by simpa using hj)]
    simp
  rw [add_comm 1 x, add_pow]
  refine h1.trans (le_of_eq ?_)
  rw [← h2]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_comm]

theorem sum_numBlockSets_mul_gamma_two_sided_bounds : ∀ (r k q : ℕ) (b : Fin r → ℕ), 1 ≤ k → 1 ≤ r → r ≤ q → 2 ≤ q → (q : ℝ) ^ k * (1 - 1 / (q : ℝ)) ≤ ((∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam q (k - j) : ℕ) : ℝ) ∧ ((∑ j ∈ Finset.range (k + 1), splitDoublingNBlock b j * gam q (k - j) : ℕ) : ℝ) ≤ (q : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (q : ℝ)) := by
  intro r k q b hk hr hrq hq
  have hq0 : (0 : ℝ) < q := by positivity
  have hg := gam_cast (q := q) (k := k) (by omega) hk
  rw [Finset.sum_range_succ', numBlockSetsOfTotalSize_zero, one_mul, Nat.sub_zero]
  push_cast
  rw [hg]
  constructor
  · have : 0 ≤ ∑ j ∈ Finset.range k, (splitDoublingNBlock b (j + 1) : ℝ) * (gam q (k - (j + 1)) : ℝ) :=
      Finset.sum_nonneg fun _ _ => by positivity
    linarith
  · have hx : (0 : ℝ) ≤ 1 / q := by positivity
    have h1 := sum_choose_mul_pow_le hx r k
    have h2 := one_add_pow_le_two_mul hx (r := r) (by
      rw [mul_one_div, div_le_one hq0]; exact_mod_cast hrq)
    rw [Finset.sum_range_succ'] at h1
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one] at h1
    have h3 : ∑ j ∈ Finset.range k, (splitDoublingNBlock b (j + 1) : ℝ) * (gam q (k - (j + 1)) : ℝ)
        ≤ (q : ℝ) ^ k * ∑ j ∈ Finset.range k, (r.choose (j + 1) : ℝ) * (1 / (q : ℝ)) ^ (j + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' : j + 1 ≤ k := by simpa using hj
      have e : (q : ℝ) ^ k * ((r.choose (j + 1) : ℝ) * (1 / (q : ℝ)) ^ (j + 1))
          = (r.choose (j + 1) : ℝ) * (q : ℝ) ^ (k - (j + 1)) := by
        conv_lhs => rw [← Nat.sub_add_cancel hj', pow_add]
        rw [one_div_pow]
        field_simp
      rw [e]
      exact_mod_cast Nat.mul_le_mul (numBlockSetsOfTotalSize_le_choose b _) (gam_le_pow _ _)
    have h4 : ∑ j ∈ Finset.range k, (r.choose (j + 1) : ℝ) * (1 / (q : ℝ)) ^ (j + 1)
        ≤ 2 * (r * (1 / (q : ℝ))) := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 (pow_nonneg hq0.le k)
    have e : (q : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (q : ℝ))
        = (q : ℝ) ^ k * (2 * (r * (1 / (q : ℝ)))) + (q : ℝ) ^ k * (1 - 1 / (q : ℝ)) := by ring
    rw [e]
    linarith

end GlobalTheory.FinGL
end

section

noncomputable section

namespace GlobalTheory.FinGL.SortWh

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem mem_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G) (χ : G → ℂ)
    (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

variable {F : Type} [Field F] {r : ℕ}

def bd (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i k => if b i = b k then M i k else 0

theorem bd_apply (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) (i k : Fin r) :
    bd b M i k = if b i = b k then M i k else 0 := rfl

theorem bd_one (b : Fin r → ℕ) : bd b (1 : Matrix (Fin r) (Fin r) F) = 1 := by
  ext i k
  rw [bd_apply]
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply_ne]
    rintro rfl
    exact h rfl

theorem bd_bd (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) : bd b (bd b M) = bd b M := by
  ext i k
  simp only [bd_apply]
  split_ifs <;> rfl

theorem bd_mul (b : Fin r → ℕ) {M N : Matrix (Fin r) (Fin r) F} (hM : M.BlockTriangular b) (hN : N.BlockTriangular b) :
    bd b (M * N) = bd b M * bd b N := by
  ext i k
  simp only [bd_apply, Matrix.mul_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun l _ => ?_
    rcases lt_trichotomy (b l) (b i) with h1 | h1 | h1
    · rw [hM h1]; simp
    · rw [if_pos h1.symm, if_pos (h1.trans h)]
    · rw [hN (show b k < b l by omega)]; simp
  · refine (Finset.sum_eq_zero fun l _ => ?_).symm
    by_cases h1 : b i = b l
    · rw [if_neg (show ¬ b l = b k by omega), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem bd_tri (b : Fin r → ℕ) (M : Matrix (Fin r) (Fin r) F) : (bd b M).BlockTriangular b := by
  intro i k h
  rw [bd_apply, if_neg (by omega)]

def levi (b : Fin r → ℕ) (p : blockTri (κ := F) b) : blockTri (κ := F) b :=
  ⟨⟨bd b ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F), bd b (((p⁻¹ : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F),
    by rw [← bd_mul b p.2 (p⁻¹).2, ← Units.val_mul]; simp [bd_one],
    by rw [← bd_mul b (p⁻¹).2 p.2, ← Units.val_mul]; simp [bd_one]⟩, bd_tri b _⟩

theorem levi_apply (b : Fin r → ℕ) (p : blockTri (κ := F) b) (i k : Fin r) :
    ((levi b p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k =
      if b i = b k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k else 0 := rfl

theorem sigma_levi {V : Type} [AddCommGroup V] [Module ℂ V] {b : Fin r → ℕ}
    {σ : Representation ℂ (blockTri (κ := F) b) V} (hσ : IsCuspDatum b σ) (p : blockTri (κ := F) b) :
    σ (levi b p) = σ p := by
  have h : σ (p⁻¹ * levi b p) = 1 := by
    refine hσ.infl _ fun i k hik => ?_
    have h1 : bd b ((((p⁻¹ * levi b p : blockTri (κ := F) b)) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 := by
      rw [Subgroup.coe_mul, Units.val_mul, bd_mul b (p⁻¹).2 (levi b p).2]
      have : bd b ((levi b p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
          bd b ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) := bd_bd b _
      rw [this, ← bd_mul b (p⁻¹).2 p.2, ← Units.val_mul]
      simp [bd_one]
    have h2 := congrFun (congrFun h1 i) k
    rwa [bd_apply, if_pos hik] at h2
  have : levi b p = p * (p⁻¹ * levi b p) := by group
  rw [this, map_mul, h, mul_one]

theorem edgeSum_levi (b : Fin r → ℕ) (p : blockTri (κ := F) b) :
    edgeSum (blkEdge b) (levi b p : GL (Fin r) F) = edgeSum (blkEdge b) (p : GL (Fin r) F) := by
  unfold edgeSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · rw [levi_apply, if_pos h.2]
  · rfl

section Perm

variable {b : Fin r → ℕ} {j : ℕ} {w : Equiv.Perm (Fin r)}

theorem lt_iff (h1 : ∀ a c : Fin r, a < c → b (w a) = b (w c) → w a < w c) {a c : Fin r} (h : b (w a) = b (w c)) :
    a < c ↔ w a < w c := by
  refine ⟨fun hac => h1 a c hac h, fun hw => ?_⟩
  rcases lt_trichotomy a c with h' | h' | h'
  · exact h'
  · subst h'; exact absurd hw (lt_irrefl _)
  · exact absurd (h1 c a h' h.symm) (not_lt.2 hw.le)

theorem edge_iff (hb : Monotone b) (h1 : ∀ a c : Fin r, a < c → b (w a) = b (w c) → w a < w c)
    (h2 : ∀ a e c : Fin r, a ≤ e → e ≤ c → b (w a) = b (w c) → b (w e) = b (w a))
    (h4 : ∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) ≠ b (w c)) {a c : Fin r} (h : b (w a) = b (w c)) :
    blkEdge b (w a) (w c) ↔ cutEdge j a c := by
  constructor
  · rintro ⟨e1, -⟩
    have hac : a < c := (lt_iff h1 h).2 (by rw [Fin.lt_def]; omega)
    have hac' : a.val < c.val := hac
    have hc : c.val = a.val + 1 := by
      by_contra hne
      let e : Fin r := ⟨a.val + 1, by have := c.2; omega⟩
      have hae : a < e := by rw [Fin.lt_def]; simp [e]
      have hec : e < c := by rw [Fin.lt_def]; simp only [e]; omega
      have hbe := h2 a e c hae.le hec.le h
      have k1 : (w a).val < (w e).val := h1 a e hae hbe.symm
      have k2 : (w e).val < (w c).val := h1 e c hec (hbe.trans h)
      omega
    refine ⟨hc, fun hj => h4 a c (by omega) (by omega) h⟩
  · rintro ⟨e1, -⟩
    refine ⟨?_, h⟩
    have hac : a < c := by rw [Fin.lt_def]; omega
    have hw : (w a).val < (w c).val := h1 a c hac h
    by_contra hne
    let i : Fin r := ⟨(w a).val + 1, by have := (w c).2; omega⟩
    have hai : w a < i := by rw [Fin.lt_def]; simp [i]
    have hic : i < w c := by rw [Fin.lt_def]; simp only [i]; omega
    obtain ⟨e, he⟩ := w.surjective i
    have k1 : b (w a) ≤ b i := hb hai.le
    have k2 : b i ≤ b (w c) := hb hic.le
    rw [← he] at hai hic k1 k2
    have l1 : a.val < e.val := (lt_iff h1 (by omega)).2 hai
    have l2 : e.val < c.val := (lt_iff h1 (by omega)).2 hic
    omega

end Perm

theorem eig_conj_eq_leviWh : ∀ (F : Type) [Field F] (ψ : AddChar F ℂ) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ (j : ℕ) (w : Equiv.Perm (Fin r)) (x : GL (Fin r) F), (∀ (g : GL (Fin r) F) (a c : Fin r), ((x⁻¹ * g * x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c = (g : Matrix (Fin r) (Fin r) F) (w a) (w c)) → (∀ a c : Fin r, a < c → b (w a) = b (w c) → w a < w c) → (∀ a e c : Fin r, a ≤ e → e ≤ c → b (w a) = b (w c) → b (w e) = b (w a)) → (∀ a c : Fin r, cutEdge j a c → b (w c) ≤ b (w a)) → (∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) ≠ b (w c)) → eig σ {p | x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r} (fun p => ψ (edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x))) = eig σ {p | (p : GL (Fin r) F) ∈ unip F r} (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) := by
  intro F _ ψ r V _ _ b σ hσ j w x hx h1 h2 h3 h4
  have hsum : ∀ p : blockTri (κ := F) b, edgeSum (cutEdge j) (x⁻¹ * (p : GL (Fin r) F) * x) =
      edgeSum (blkEdge b) (p : GL (Fin r) F) := by
    intro p
    unfold edgeSum
    rw [← Equiv.sum_comp w (fun i => ∑ k, if blkEdge b i k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k else 0)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp w (fun k => if blkEdge b (w a) k then ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (w a) k else 0)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hx]
    by_cases h : b (w a) = b (w c)
    · simp only [edge_iff hσ.mono h1 h2 h4 h]
    · rw [if_neg (show ¬ blkEdge b (w a) (w c) from fun h' => h h'.2)]
      split_ifs with hc
      · exact p.2 (lt_of_le_of_ne (h3 a c hc) (Ne.symm h))
      · rfl
  ext v
  rw [mem_eig, mem_eig]
  constructor
  · intro H p hp
    have hp' : (p : GL (Fin r) F) ∈ unip F r := hp
    have hm : x⁻¹ * (levi b p : GL (Fin r) F) * x ∈ unip F r := by
      refine ⟨mem_blockTri.2 fun a c hac => ?_, fun a => ?_⟩
      · rw [hx, levi_apply]
        split_ifs with h
        · exact unip_lower hp' (h1 c a hac h.symm)
        · rfl
      · rw [hx, levi_apply, if_pos rfl, unip_diag hp']
    have := H (levi b p) hm
    rw [sigma_levi hσ, hsum, edgeSum_levi] at this
    exact this
  · intro H p hp
    have hp' : x⁻¹ * (p : GL (Fin r) F) * x ∈ unip F r := hp
    have hm : (levi b p : GL (Fin r) F) ∈ unip F r := by
      refine ⟨mem_blockTri.2 fun i k hik => ?_, fun i => ?_⟩
      · obtain ⟨a, rfl⟩ := w.surjective i
        obtain ⟨c, rfl⟩ := w.surjective k
        rw [levi_apply]
        split_ifs with h
        · rw [← hx]
          exact unip_lower hp' ((lt_iff h1 h.symm).2 hik)
        · rfl
      · obtain ⟨a, rfl⟩ := w.surjective i
        rw [levi_apply, if_pos rfl, ← hx, unip_diag hp']
    have := H (levi b p) hm
    rw [sigma_levi hσ, edgeSum_levi] at this
    rw [hsum]
    exact this

end GlobalTheory.FinGL.SortWh
end
end

section

noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open Formalism.L2.DIV Module

variable {F : Type} [Field F] {r : ℕ}

def colSet (F : Type) [Field F] (b : Fin r → ℕ) (k : ℕ) : Set (blockTri (κ := F) b) :=
  {p | (p : GL (Fin r) F) ∈ unip F r ∧ ∀ i j : Fin r, j.val < k →
    ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j}

def colChar (ψ : AddChar F ℂ) (b : Fin r → ℕ) (k : Fin r) (l : Fin r → F) (p : blockTri (κ := F) b) : ℂ :=
  ψ (∑ i, l i * ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k +
    edgeSum (fun i j => blkEdge b i j ∧ k < j) (p : GL (Fin r) F))

theorem mem_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G)
    (χ : G → ℂ) (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem eig_congr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G)
    (χ χ' : G → ℂ) (h : ∀ g ∈ S, χ g = χ' g) : eig τ S χ = eig τ S χ' := by
  ext v
  simp only [mem_eig]
  exact forall₂_congr fun g hg => by rw [h g hg]

end GlobalTheory.FinGL.LeviWh
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover : GlobalTheory.EtC.A5 := by
  first | exact @GlobalTheory.EtC.classes_die_on_etale_cover | exact GlobalTheory.EtC.classes_die_on_etale_cover | (intros; apply GlobalTheory.EtC.classes_die_on_etale_cover <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem hasVal_subst : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B) (f : MvPowerSeries τ Q) (q : Q), (∀ j, constantCoeff (u j) = 0) → DIn (⊤ : Ideal B) f → HasVal p (fun j => E (u j)) f q → HasVal p z (subst (up Q u) f) q := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z hz E hE τ _ _ u f q hu hf hq
  intro m
  obtain ⟨M0, hM0⟩ := GlobalTheory.T.tail_subst_pAdically_small_of_integral_differential p B O Q θ hF σ z hz τ u f hu hf m
  obtain ⟨M1, hM1⟩ := hq m
  obtain ⟨g, hg⟩ : ∃ g : MvPolynomial τ Q, g = trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => max M0 M1) f := ⟨_, rfl⟩
  obtain ⟨N2, hN2⟩ := GlobalTheory.T.hasVal_subst_polynomial_eval p B O Q θ hF σ z hz E hE τ u hu g m
  refine ⟨N2, fun N' hN' => ?_⟩
  obtain ⟨b1, hb1⟩ := hM1 (max M0 M1) (le_max_right _ _)
  obtain ⟨b2, hb2⟩ := hN2 N' hN'
  obtain ⟨b3, hb3⟩ := hM0 (max M0 M1) (le_max_left _ _) (Finsupp.equivFunOnFinite.symm fun _ => N')
  rw [← hg] at hb1 hb3
  have hs : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun j => by
    simp [up, hu j]
  have hsplit : subst (up Q u) f = subst (up Q u) (g : MvPowerSeries τ Q) + subst (up Q u) (f - (g : MvPowerSeries τ Q)) := by
    rw [← subst_add hs]; congr 1; ring
  refine ⟨b1 + b2 - b3, ?_⟩
  rw [hsplit, map_add (f := _), map_add (f := _)]
  simp only [map_mul, map_sub, map_add (f := _), map_pow, map_natCast] at hb1 hb2 hb3 ⊢
  linear_combination hb1 + hb2 - hb3

end GlobalTheory.QLog
end
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pDivGroup_dual_tangent_of_quasiLogarithm : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ f : MvPowerSeries (Fin d) E, QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  first | exact @GlobalTheory.QLogTangent.main | exact GlobalTheory.QLogTangent.main | (intros; apply GlobalTheory.QLogTangent.main <;> assumption)
end

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pDivGroup_dual_tangent_linear_kills_integral : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f g : MvPowerSeries (Fin d) E) (l l' : G.dual.Lie) (a : O), c.IsLie f l → c.IsLie g l' → (QL c.μ ⊤ f → QL c.μ ⊤ g → c.IsLie (f + algebraMap O E a • g) (l + a • l')) ∧ ((∃ s : MvPowerSeries (Fin d) O, f = map (algebraMap O E) s) → l = 0) ∧ (cob1 (up E c.μ) f = 0 → l = 0) := by
  first | exact @GlobalTheory.LieLin.main | exact GlobalTheory.LieLin.main | (intros; apply GlobalTheory.LieLin.main <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.semilinearPDivGroupHom_eval_two_variable_series : ∀ (p : ℕ) (k k' : Type) [CommRing k] [CommRing k'] (σ : k →+* k') (d e : ℕ) (G : PDivGroup p k) (G' : PDivGroup p k') (c : Chart G d) (c' : Chart G' e) (s : SemiHom σ G' G) (φ : Fin d → MvPowerSeries (Fin e) k'), (∀ n j, c'.ev n (φ j) = s.app n (c.x n j)) → ∀ n t, c'.ev₂ n (pull2 φ (MvPowerSeries.map σ t)) = (s.app n).two (c.ev₂ n t) := by
  first | exact @GlobalTheory.Katz.semiHom_ev₂_pull2 | exact GlobalTheory.Katz.semiHom_ev₂_pull2 | (intros; apply GlobalTheory.Katz.semiHom_ev₂_pull2 <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.eq_zero_of_eval_cube_levels : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∀ n i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)) ∧ ∀ f : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k, (∀ n (h : ∀ i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n)) (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)), evA k _ h f = 0) → f = 0 := by
  first | exact @GlobalTheory.Katz.Chart.eq_zero_of_ev_cube | exact GlobalTheory.Katz.Chart.eq_zero_of_ev_cube | (intros; apply GlobalTheory.Katz.Chart.eq_zero_of_ev_cube <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.lazard_one_variable_exists_witt_lift : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : ℕ) (a : ℕ → k), 2 ≤ N → (∀ i, i ≤ N → a i = a (N - i)) → (∀ i j l, 0 < i → 0 < j → 0 < l → i + j + l = N → a (i + j) * ((i + j).choose i : k) = a i * ((j + l).choose j : k)) → ∃ t : Fr p k, ∀ i, 0 < i → i < N → ∃ w : WittVector p k, t * (N.choose i : Fr p k) = algebraMap (WittVector p k) (Fr p k) w ∧ WittVector.constantCoeff w = a i := by
  first | exact @GlobalTheory.LazardOne.exists_lift | exact GlobalTheory.LazardOne.exists_lift | (intros; apply GlobalTheory.LazardOne.exists_lift <;> assumption)
end
