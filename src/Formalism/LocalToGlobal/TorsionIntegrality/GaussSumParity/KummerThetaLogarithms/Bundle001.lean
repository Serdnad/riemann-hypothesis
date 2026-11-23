module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle002
public import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionHypothesesOfConditions
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ExponentialSpecification
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
public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (lgF at1 UnrOK)

namespace OrbitCoverLemmas

end OrbitCoverLemmas

namespace OrbitCoverLemmas

def blk {K : Type} [Field K] (lam : K) (k x : Bool) : K :=
  if x = false then (if k = false then 1 else lam) else (if k = false then 2⁻¹ else -lam * 2⁻¹)

theorem blk_gram {K : Type} [Field K] (σ : K →+* K) (lam : K) (h2 : (2 : K) ≠ 0)
    (h : lam * σ lam = -1) (x x' : Bool) :
    ∑ k, blk lam k x * σ (blk lam k x') = if x ≠ x' then 1 else 0 := by
  have s2 : σ 2 = 2 := map_ofNat σ 2
  cases x <;> cases x' <;> simp [blk, map_inv₀, s2]
  · linear_combination h
  · field_simp; linear_combination -h
  · field_simp; linear_combination -h
  · field_simp; linear_combination h

theorem lam_spec {K : Type} [Field K] (σ : K →+* K) (m : ℕ) (hm : 0 < m) (ζ : K)
    (hζ : IsPrimitiveRoot ζ ((2 * m + 1) ^ 2 - 1)) (hσ : σ ζ = ζ ^ (2 * m + 1)) :
    (ζ ^ m) * σ (ζ ^ m) = -1 := by
  have e : (2 * m + 1) ^ 2 - 1 = (m * (2 * m + 2)) * 2 := by
    have : (2 * m + 1) ^ 2 = (m * (2 * m + 2)) * 2 + 1 := by ring
    omega
  have hp : IsPrimitiveRoot (ζ ^ (m * (2 * m + 2))) 2 := by
    have := hζ.pow_of_dvd (p := m * (2 * m + 2)) (by positivity) (by rw [e]; exact Dvd.intro _ rfl)
    rwa [e, Nat.mul_div_cancel_left _ (by positivity)] at this
  have := hp.eq_neg_one_of_two_right
  rw [map_pow, hσ, ← this]; ring

theorem norm_two {K : Type} [NormedField K] [IsUltrametricDist K] (m : ℕ)
    (h : ‖((2 * m + 1 : ℕ) : K)‖ < 1) : ‖(2 : K)‖ = 1 := by
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one K 2
    simpa using this
  refine le_antisymm h2 ?_
  by_contra hlt
  rw [not_le] at hlt
  have hm : ‖(m : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
  have e : (1 : K) = ((2 * m + 1 : ℕ) : K) + -(2 * (m : K)) := by push_cast; ring
  have h1 : ‖(1 : K)‖ < 1 := by
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h ?_)
    rw [norm_neg, norm_mul]
    calc ‖(2 : K)‖ * ‖(m : K)‖ ≤ ‖(2 : K)‖ * 1 := by gcongr
      _ < 1 := by rwa [mul_one]
  rw [norm_one] at h1
  exact lt_irrefl _ h1

end OrbitCoverLemmas

theorem gram_matrix_exists : GramExists := by
  intro K _ _ _ l σ hU hζ E _ _
  obtain ⟨ζ, hζ⟩ := hζ
  obtain ⟨hp, hl2, hnl, -, -⟩ := id hU
  obtain ⟨m, rfl⟩ : ∃ m, l = 2 * m + 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · omega
    · exact h
  have hm : 0 < m := by omega
  have hσζ : σ ζ = ζ ^ (2 * m + 1) := teichSigma K _ 2 σ hU (by norm_num) ζ hζ.pow_eq_one
  have hN0 : (2 * m + 1) ^ 2 - 1 ≠ 0 := by
    have : 1 < (2 * m + 1) ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have nζ : ‖ζ‖ = 1 := FormalExponential.norm_eq_one_of_pow hN0 hζ.pow_eq_one
  have hσσ : σ (σ ζ) = ζ := by
    rw [hσζ, map_pow, hσζ, ← pow_mul, ← sq]
    have e : (2 * m + 1) ^ 2 = ((2 * m + 1) ^ 2 - 1) + 1 := by omega
    rw [e, pow_succ, hζ.pow_eq_one, one_mul]
  have hlam := OrbitCoverLemmas.lam_spec σ m hm ζ hζ hσζ
  have n2 : ‖(2 : K)‖ = 1 := by
    refine OrbitCoverLemmas.norm_two m ?_
    rw [hnl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have nlam : ‖ζ ^ m‖ = 1 := by rw [norm_pow, nζ, one_pow]
  have s2 : σ 2 = 2 := map_ofNat σ 2
  have hblk : ∀ k x : Bool, ‖OrbitCoverLemmas.blk (ζ ^ m) k x‖ ≤ 1 ∧
      σ (σ (OrbitCoverLemmas.blk (ζ ^ m) k x)) = OrbitCoverLemmas.blk (ζ ^ m) k x := by
    intro k x
    cases k <;> cases x <;> simp [OrbitCoverLemmas.blk, nlam, hσσ, n2, s2, map_inv₀]
  refine ⟨fun k x => if k.2 = x.2 then OrbitCoverLemmas.blk (ζ ^ m) k.1 x.1 else 0, fun k x => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hblk _ _
    · simp
  · rintro ⟨b, e⟩ ⟨b', e'⟩
    rw [Fintype.sum_prod_type]
    dsimp only
    by_cases h : e = e'
    · subst h
      have h3 : ∀ k : Bool, ∑ y : E, (if y = e then OrbitCoverLemmas.blk (ζ ^ m) k b else 0) *
          σ (if y = e then OrbitCoverLemmas.blk (ζ ^ m) k b' else 0) =
          OrbitCoverLemmas.blk (ζ ^ m) k b * σ (OrbitCoverLemmas.blk (ζ ^ m) k b') := by
        intro k
        rw [Finset.sum_eq_single e]
        · simp
        · intro y _ hy
          simp [hy]
        · simp
      simp only [h3]
      rw [OrbitCoverLemmas.blk_gram σ _ h2 hlam]
      simp
    · rw [if_neg (fun h' => h h'.2)]
      refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun y _ => ?_
      by_cases hy : y = e
      · have : ¬ y = e' := fun h' => h (hy ▸ h')
        simp [this]
      · simp [hy]

end Formalism.L2.Th1.D
end
end

section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.InvariantFactorPaths.G7 (UnrOK)

namespace TraceDualSums

lemma sum_zmod {M : Type} [AddCommMonoid M] (d : ℕ) [NeZero d] (F : ℕ → M) :
    (∑ s : ZMod d, F s.val) = ∑ i ∈ Finset.range d, F i := by
  cases d with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ n =>
    rw [Finset.sum_range]
    rfl

lemma sum_range_even {M : Type} [AddCommMonoid M] (m : ℕ) (g : ℕ → M) :
    (∑ i ∈ Finset.range (2 * m), if i % 2 = 0 then g i else 0) =
      ∑ k ∈ Finset.range m, g (2 * k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    have h1 : (2 * m) % 2 = 0 := by omega
    have h2 : ¬ (2 * m + 1) % 2 = 0 := by omega
    rw [if_pos h1, if_neg h2, add_zero]

lemma norm_det_le {K : Type} [NormedField K] [IsUltrametricDist K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro p _
  rw [Units.smul_def, zsmul_eq_mul, norm_mul, norm_prod]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one K _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => h _ _)

lemma inv_shift {K : Type} [Field K] {m : ℕ} [NeZero m] (τ : K →+* K)
    (V P : Matrix (Fin m) (Fin m) K) (hVP : V * P = 1)
    (hV : ∀ k r, τ (V k r) = V (k + 1) r) : ∀ r k, τ (P r k) = P r (k + 1) := by
  have h1 : (V.map τ) * (P.map τ) = 1 := by
    rw [← Matrix.map_mul, hVP]
    exact Matrix.map_one τ (map_zero τ) (map_one τ)
  have h2 : V.map τ = V.submatrix (Equiv.addRight (1 : Fin m)) id := by
    ext k r
    exact hV k r
  have h3 : (V.submatrix (Equiv.addRight (1 : Fin m)) id) *
      (P.submatrix id (Equiv.addRight (1 : Fin m))) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hVP, Matrix.submatrix_one_equiv]
  have h4 : P.map τ = P.submatrix id (Equiv.addRight (1 : Fin m)) := by
    rw [← Matrix.inv_eq_right_inv h1, h2, Matrix.inv_eq_right_inv h3]
  intro r k
  exact congrFun (congrFun h4 r) k

end TraceDualSums

open TraceDualSums Fin.NatCast in
theorem trace_dual_exists : TrDualExists := by
  intro K _ _ _ l d _ σ hU hd ζ hζ
  obtain ⟨m, rfl⟩ := hd
  have hd0 : m + m ≠ 0 := NeZero.ne (m + m)
  have hm0 : m ≠ 0 := by omega
  have hdm : (m + m) / 2 = m := by omega
  rw [hdm]
  have : NeZero m := ⟨hm0⟩
  have hp : l.Prime := hU.1
  have hl3 : 2 < l := hU.2.1
  have hlt : ‖(l : K)‖ < 1 := by
    rw [hU.2.2.1]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hpos : 1 ≤ l ^ (m + m) := Nat.one_le_pow _ _ hp.pos
  have hnd : ¬ l ∣ l ^ (m + m) - 1 := by
    intro h
    have h1 : l ∣ l ^ (m + m) := dvd_pow_self l hd0
    have h2 : l ∣ 1 := by
      have := (Nat.dvd_sub h1 h)
      rwa [Nat.sub_sub_self hpos] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hN : ‖((l ^ (m + m) - 1 : ℕ) : K)‖ = 1 :=
    Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd hp hlt hnd
  have hN0 : l ^ (m + m) - 1 ≠ 0 := by
    intro h
    rw [h] at hnd
    exact hnd (dvd_zero l)
  have nζ : ‖ζ‖ = 1 := FormalExponential.norm_eq_one_of_pow hN0 hζ.pow_eq_one
  have hσζ : σ ζ = ζ ^ l := teichSigma K l (m + m) σ hU (by omega) ζ hζ.pow_eq_one
  have hit : ∀ j, σ^[j] ζ = ζ ^ (l ^ j) := B4.iterate_of_pow hσζ
  have hper : σ^[m + m] ζ = ζ := by
    rw [hit, show l ^ (m + m) = (l ^ (m + m) - 1) + 1 by omega, pow_succ, hζ.pow_eq_one, one_mul]
  let τ : K →+* K := σ.comp σ
  have hτ : ∀ (k : ℕ) (a : K), τ^[k] a = σ^[2 * k] a := by
    intro k a
    rw [Function.iterate_mul]
    rfl
  have hper' : Function.IsPeriodicPt τ m ζ := by
    show τ^[m] ζ = ζ
    rw [hτ, two_mul]
    exact hper
  let x : Fin m → K := fun k => σ^[2 * k.val] ζ
  have hxn : ∀ j : ℕ, x (j : Fin m) = τ^[j] ζ := by
    intro j
    show σ^[2 * ((j : Fin m) : ℕ)] ζ = _
    rw [Fin.val_natCast, ← hτ, hper'.iterate_mod_apply]
  have hxs : ∀ k, τ (x k) = x (k + 1) := by
    intro k
    have h : k + 1 = ((k.val + 1 : ℕ) : Fin m) := by
      rw [Nat.cast_succ, Fin.cast_val_eq_self]
    rw [h, hxn, Function.iterate_succ_apply', ← hxn, Fin.cast_val_eq_self]
  let V : Matrix (Fin m) (Fin m) K := Matrix.vandermonde x
  have hVa : ∀ k r, V k r = x k ^ (r : ℕ) := fun k r => Matrix.vandermonde_apply x k r
  have hVs : ∀ k r, τ (V k r) = V (k + 1) r := by
    intro k r
    rw [hVa, hVa, map_pow, hxs]
  have hxpow : ∀ k, x k = ζ ^ (l ^ (2 * k.val)) := fun k => hit _
  have hxN : ∀ k, x k ^ (l ^ (m + m) - 1) = 1 := by
    intro k
    rw [hxpow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have nx : ∀ k, ‖x k‖ = 1 := fun k => FormalExponential.norm_eq_one_of_pow hN0 (hxN k)
  have hsmall : ∀ k : Fin m, l ^ (2 * k.val) < l ^ (m + m) - 1 := by
    intro k
    have hk := k.2
    have h1 : l ^ (2 * k.val) ≤ l ^ (m + m - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : l ^ (m + m) = l ^ (m + m - 1) * l := by
      rw [← pow_succ]
      congr 1
      omega
    have h3 : 1 ≤ l ^ (m + m - 1) := Nat.one_le_pow _ _ hp.pos
    have h4 : l ^ (m + m - 1) * 3 ≤ l ^ (m + m - 1) * l := Nat.mul_le_mul_left _ hl3
    omega
  have hinj : Function.Injective x := by
    intro i j hij
    rw [hxpow, hxpow] at hij
    have h1 := hζ.pow_inj (hsmall i) (hsmall j) hij
    have h2 := Nat.pow_right_injective hp.two_le h1
    exact Fin.ext (by omega)
  have hdiff : ∀ i j, i ≠ j → ‖x j - x i‖ = 1 := by
    intro i j hij
    refine le_antisymm ?_ ?_
    · rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_neg, nx, nx, max_self]
    · by_contra hlt'
      exact hij (hinj (FormalExponential.root_eq_of_norm_lt hN (hxN j) (hxN i) (not_le.1 hlt'))).symm
  have hdet : ‖V.det‖ = 1 := by
    rw [Matrix.det_vandermonde, norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [norm_prod]
    exact Finset.prod_eq_one fun j hj => hdiff i j (ne_of_lt (Finset.mem_Ioi.1 hj))
  have hdet0 : V.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact zero_ne_one hdet
  let P : Matrix (Fin m) (Fin m) K := V⁻¹
  have hVP : V * P = 1 := Matrix.mul_nonsing_inv V (isUnit_iff_ne_zero.2 hdet0)
  have hPV : P * V = 1 := Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.2 hdet0)
  have hVint : ∀ k r, ‖V k r‖ ≤ 1 := by
    intro k r
    rw [hVa, norm_pow, nx, one_pow]
  have hPint : ∀ r k, ‖P r k‖ ≤ 1 := by
    intro r k
    show ‖(V⁻¹) r k‖ ≤ 1
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', norm_mul, norm_inv,
      hdet, inv_one, one_mul, Matrix.adjugate_apply]
    refine norm_det_le _ fun i j => ?_
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs <;> simp
    · exact hVint i j
  have hPs := inv_shift τ V P hVP hVs
  have hPn : ∀ (r : Fin m) (j : ℕ), τ^[j] (P r 0) = P r (j : Fin m) := by
    intro r j
    induction j with
    | zero => simp
    | succ j ih => rw [Function.iterate_succ_apply', ih, hPs, Nat.cast_succ]
  refine ⟨fun r => ζ ^ (r : ℕ), fun r => P r 0,
    ⟨fun r => ⟨by rw [norm_pow, nζ, one_pow], hPint r 0⟩, fun r => ⟨?_, ?_⟩⟩, ⟨?_, ?_⟩⟩
  · show σ^[m + m] (ζ ^ (r : ℕ)) = ζ ^ (r : ℕ)
    rw [iterate_map_pow, hper]
  · show σ^[m + m] (P r 0) = P r 0
    rw [← two_mul, ← hτ, hPn, Fin.natCast_self]
  · rw [Fintype.card_fin, two_mul]
  · intro r r'
    show (∑ s : ZMod (m + m), if s.val % 2 = 0 then σ^[s.val] (ζ ^ (r : ℕ) * P r' 0) else 0) = _
    rw [sum_zmod (m + m) (fun i => if i % 2 = 0 then σ^[i] (ζ ^ (r : ℕ) * P r' 0) else 0),
      ← two_mul, sum_range_even m (fun i => σ^[i] (ζ ^ (r : ℕ) * P r' 0)), Finset.sum_range]
    have hterm : ∀ k : Fin m, σ^[2 * (k : ℕ)] (ζ ^ (r : ℕ) * P r' 0) = P r' k * V k r := by
      intro k
      rw [iterate_map_mul, iterate_map_pow, ← hτ k.val (P r' 0), hPn, Fin.cast_val_eq_self, hVa,
        mul_comm]
    rw [Finset.sum_congr rfl fun k _ => hterm k, ← Matrix.mul_apply, hPV, Matrix.one_apply]
    simp only [eq_comm]

end Formalism.L2.Th1.D
end
end
