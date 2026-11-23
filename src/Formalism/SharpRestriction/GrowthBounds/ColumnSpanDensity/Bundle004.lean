module

import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle003
public import Formalism.PolynomialDimension.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundLargeConductor
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundOfEdgeCount
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

private theorem choose_add_succ_succ_eq_choose_mul_div (A m : ℕ) :
    ((A + (m + 1)).choose (m + 1) : ℚ) = ((A + m).choose m : ℚ) * ((A : ℚ) + m + 1) / ((m : ℚ) + 1) := by
  have h : (A + m + 1) * (A + m).choose m = (A + m + 1).choose (m + 1) * (m + 1) := by
    first
    | exact Nat.add_one_mul_choose_eq (A + m) m
    | exact Nat.succ_mul_choose_eq (A + m) m
  rw [eq_div_iff (by positivity), show A + (m + 1) = A + m + 1 by omega]
  have h' : (((A + m + 1) * (A + m).choose m : ℕ) : ℚ) = (((A + m + 1).choose (m + 1) * (m + 1) : ℕ) : ℚ) := by
    rw [h]
  push_cast at h'
  linear_combination -h'

private theorem choose_succ_eq_choose_mul_div (A m : ℕ) :
    ((A + m).choose (m + 1) : ℚ) = ((A + m).choose m : ℚ) * (A : ℚ) / ((m : ℚ) + 1) := by
  have h := Nat.choose_succ_right_eq (A + m) m
  rw [Nat.add_sub_cancel] at h
  rw [eq_div_iff (by positivity)]
  exact_mod_cast h

theorem prodA (m A : ℕ) :
    ∏ j : Fin m, (((A : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) = ((A + m).choose m : ℚ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih, choose_add_succ_succ_eq_choose_mul_div]
    ring

theorem prodB (m B : ℕ) :
    ∏ j : Fin m, (((B : ℚ) + (m : ℚ) - ((j : ℕ) : ℚ)) / ((m : ℚ) - ((j : ℕ) : ℚ))) = ((B + m).choose m : ℚ) := by
  rw [← prodA m B, ← Equiv.prod_comp Fin.revPerm]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj := j.isLt
  have hr : (((Fin.revPerm j : Fin m) : ℕ) : ℚ) = (m : ℚ) - ((j : ℕ) : ℚ) - 1 := by
    rw [Fin.revPerm_apply, Fin.val_rev, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hr]
  congr 1 <;> ring

theorem weylDim_const (m : ℕ) (d : ℤ) : weylDim m (fun _ => d) = 1 := by
  unfold weylDim
  refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
  split_ifs with h
  · have hij : (i : ℕ) < (j : ℕ) := h
    have hq : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
    simp only [sub_self, Int.cast_zero, zero_add]
    exact div_self (sub_pos.mpr hq).ne'
  · rfl

private theorem weylDim_cons_eq_prod_mul (n : ℕ) (a : ℤ) (lam : Fin n → ℤ) :
    weylDim (n + 1) (Fin.cons a lam) =
      (∏ j : Fin n, (((a - lam j : ℤ) : ℚ) + ((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) * weylDim n lam := by
  unfold weylDim
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp only [lt_self_iff_false, ↓reduceIte, one_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [if_pos (Fin.succ_pos j)]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_succ, Fin.val_zero]
    push_cast
    congr 1 <;> ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fin.prod_univ_succ]
    simp only [Fin.not_lt_zero, ↓reduceIte, one_mul]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Fin.cons_succ, Fin.val_succ, Fin.succ_lt_succ_iff]
    split_ifs
    · push_cast
      congr 1 <;> ring
    · rfl

private theorem weylDim_snoc_eq_mul_prod (n : ℕ) (lam : Fin n → ℤ) (b : ℤ) :
    weylDim (n + 1) (Fin.snoc lam b) =
      weylDim n lam * ∏ i : Fin n, (((lam i - b : ℤ) : ℚ) + (n : ℚ) - ((i : ℕ) : ℚ)) / ((n : ℚ) - ((i : ℕ) : ℚ)) := by
  unfold weylDim
  have h1 : ∀ g : Fin (n + 1) → ℚ, (∏ j : Fin (n + 1), if Fin.last n < j then g j else 1) = 1 :=
    fun g => Finset.prod_eq_one fun j _ => if_neg (not_lt.mpr (Fin.le_last j))
  rw [Fin.prod_univ_castSucc, h1, mul_one, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_castSucc, if_pos (Fin.castSucc_lt_last i)]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Fin.snoc_castSucc, Fin.coe_castSucc, Fin.castSucc_lt_castSucc_iff]
  · simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]

theorem weylDim_hwt_eq (m A B : ℕ) : weylDim (m + 2) (hwt m A B) = (dimHar (m + 1) A B : ℚ) := by
  unfold hwt
  rw [weylDim_cons_eq_prod_mul, weylDim_snoc_eq_mul_prod, weylDim_const, one_mul, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
  push_cast
  try simp only [sub_zero, zero_sub, neg_neg, sub_neg_eq_add, zero_add]
  rw [prodA m A, prodB m B]
  unfold dimHar dimPol
  have hle : (if A = 0 ∨ B = 0 then 0 else (A - 1 + (m + 1)).choose (m + 1) * (B - 1 + (m + 1)).choose (m + 1)) ≤
      (A + (m + 1)).choose (m + 1) * (B + (m + 1)).choose (m + 1) := by
    split_ifs
    · exact Nat.zero_le _
    · exact Nat.mul_le_mul (Nat.choose_le_choose _ (by omega)) (Nat.choose_le_choose _ (by omega))
  rw [Nat.cast_sub hle, Nat.cast_mul, choose_add_succ_succ_eq_choose_mul_div A m, choose_add_succ_succ_eq_choose_mul_div B m]
  split_ifs with h
  · rcases h with rfl | rfl <;> push_cast <;> field_simp <;> ring
  · push_neg at h
    rw [Nat.cast_mul, show A - 1 + (m + 1) = A + m by omega, show B - 1 + (m + 1) = B + m by omega,
      choose_succ_eq_choose_mul_div A m, choose_succ_eq_choose_mul_div B m]
    field_simp
    ring

theorem weylDim_vec (m d : ℕ) :
    weylDim (m + 2) (Fin.cons (d : ℤ) (Fin.snoc (fun _ : Fin m => (0 : ℤ)) 0)) = (dimPol (m + 1) d : ℚ) := by
  unfold dimPol
  have hz : (Fin.snoc (fun _ : Fin m => (0 : ℤ)) 0 : Fin (m + 1) → ℤ) = fun _ => 0 := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]
    · simp only [Fin.snoc_castSucc]
  rw [hz, weylDim_cons_eq_prod_mul, weylDim_const, mul_one]
  push_cast
  try simp only [sub_zero]
  rw [prodA (m + 1) d]

theorem weylDim_cov (m d : ℕ) :
    weylDim (m + 2) (Fin.cons (d : ℤ) (Fin.snoc (fun _ : Fin m => (d : ℤ)) 0)) = (dimPol (m + 1) d : ℚ) := by
  unfold dimPol
  rw [weylDim_cons_eq_prod_mul, weylDim_snoc_eq_mul_prod, weylDim_const, one_mul, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
  push_cast
  try simp only [sub_self, zero_add, sub_zero]
  have h1 : (∏ j : Fin m, (((j : ℕ) : ℚ) + 1) / (((j : ℕ) : ℚ) + 1)) = 1 :=
    Finset.prod_eq_one fun j _ => div_self (by positivity)
  rw [prodB m d, h1, one_mul, choose_add_succ_succ_eq_choose_mul_div d m]
  ring

theorem finrank_tensor (Kf : Type) [Field Kf] (S : Type) [Fintype S] [DecidableEq S] (k n : ℕ)
    (ν : S → Fin n → ℕ) :
    Module.finrank Kf (Formalism.GradedWeylDivisibility.tensorLat Kf Kf fun s => Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)) =
      ∏ s, Module.finrank Kf (Formalism.GradedWeylDivisibility.dualWeyl Kf k n (ν s)) := by
  apply Formalism.MainNotions.ColumnSystems.Pf.finrank_tensor <;> assumption

theorem RS.charZeroO {p n' : ℕ} (R : RS p n') : CharZero R.O := by
  obtain ⟨c, hc⟩ := CharP.exists R.O
  rcases CharP.char_is_prime_or_zero R.O c with h | h
  · exfalso
    have hc0 : (c : R.O) = 0 := CharP.cast_eq_zero R.O c
    by_cases hcp : c = p
    · exact R.p_ne (hcp ▸ hc0)
    · have hcop : Nat.Coprime c p := (Nat.coprime_primes h R.std.1.prime).2 hcp
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
      have h1 : ((a * c + b * p : ℤ) : R.O) = 1 := by rw [hab]; simp
      push_cast at h1
      rw [hc0, mul_zero, zero_add] at h1
      exact R.p_not_unit (IsUnit.of_mul_eq_one_right _ h1)
  · subst h
    exact CharP.charP_to_charZero R.O

theorem RS.charZero {p n' : ℕ} (R : RS p n') : CharZero R.Kf := by
  have := R.charZeroO
  have hfr : IsFractionRing R.O R.Kf := R.std.1.frac_O
  exact charZero_of_injective_algebraMap (IsFractionRing.injective R.O R.Kf)

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem lpRingIndep_of (h1 : RestRSIso) (h2 : RestHLTransport) : LPRingIndep := by
  unfold LPRingIndep
  intro p n' R₁ R₂ m r lam0 t D κ cStar hLP
  obtain ⟨I⟩ := h1 p n' R₁ R₂
  obtain ⟨Φ, Ψ, hΨ, hLat, hEdge, hHL, hHLe, hdim⟩ := h2 p n' R₁ R₂ I m lam0

  have hwK : ∀ z : ℤ, I.φK (algebraMap R₁.O R₁.Kf R₁.w ^ z) = algebraMap R₂.O R₂.Kf R₂.w ^ z := by
    intro z; rw [map_zpow₀, I.hOK, I.hw]
  have hpK : ∀ z : ℤ, I.φK ((p : R₁.Kf) ^ z) = (p : R₂.Kf) ^ z := by
    intro z; rw [map_zpow₀, map_natCast]

  let back : Edge R₂.W R₂.Qq (m + 1) → Edge R₁.W R₁.Qq (m + 1) := fun e => ⟨Φ.symm e.src, Φ.symm e.tgt⟩
  have hback : ∀ e, (⟨Φ (back e).src, Φ (back e).tgt⟩ : Edge R₂.W R₂.Qq (m + 1)) = e := by
    intro e; cases e; simp [back]
  have hbackEdge : ∀ e, IsEdge p n' r e → IsEdge p n' r (back e) := by
    intro e he; rw [hEdge r (back e), hback]; exact he
  have hHLe' : ∀ e x, x ∈ HLe p R₁.ι R₁.σ R₁.w lam0 (back e) ↔ Ψ x ∈ HLe p R₂.ι R₂.σ R₂.w lam0 e := by
    intro e x; have h := hHLe (back e) x; rwa [hback] at h
  unfold LPprime at hLP ⊢
  obtain ⟨hc, hall⟩ := hLP
  refine ⟨hc, fun L hL => ?_⟩
  have hL1 : IsLattice R₁.W (Φ.symm L) := by rw [hLat, Φ.apply_symm_apply]; exact hL
  have hAt := hall _ hL1
  unfold LPprimeAt at hAt ⊢
  obtain ⟨M, e, F, he, hF, hF', n, hn, hG⟩ := hAt
  refine ⟨M, fun i => ⟨Φ (e i).src, Φ (e i).tgt⟩, fun i => Ψ (F i), ?_, ?_, ?_, n, ?_, ?_⟩
  · intro i
    refine ⟨(hEdge r (e i)).1 (he i).1, ?_⟩
    show Φ (e i).tgt = L
    rw [(he i).2, Φ.apply_symm_apply]
  · intro i
    have hFi := hF i
    simp only [Nsrc, Re, Submodule.mem_inf, Submodule.mem_iInf] at hFi ⊢
    refine ⟨?_, ?_⟩
    · have h := sl_scale I.φK Ψ hΨ _ (hHL (e i).src) hFi.1
      rwa [hwK] at h
    · intro e' he'
      have hb : IsEdge p n' r (back e') ∧ (back e').src = (e i).src := by
        refine ⟨hbackEdge e' he'.1, ?_⟩
        show Φ.symm e'.src = (e i).src
        rw [he'.2]; exact Φ.symm_apply_apply _
      have h := sl_scale I.φK Ψ hΨ _ (hHLe' e') (hFi.2 (back e') hb)
      rwa [hwK] at h
  · intro i e' he' hsrc hne
    have hb : (back e').src = (e i).src := by
      show Φ.symm e'.src = (e i).src
      rw [hsrc]; exact Φ.symm_apply_apply _
    have hne' : back e' ≠ e i := by
      intro h; apply hne; rw [← hback e', h]
    have hx := hF' i (back e') (hbackEdge e' he') hb hne'
    simp only [Re] at hx ⊢
    have h := sl_scale2 I.φK Ψ hΨ _ _ (hHLe' e') hx
    rwa [hwK, hwK] at h
  · rw [← hdim]; exact hn
  ·
    have hN : ∀ G, G ∈ Ntgt p n' R₁.ι R₁.σ R₁.w r lam0 t (Φ.symm L) →
        dT I.φK Ψ hΨ G ∈ Ntgt p n' R₂.ι R₂.σ R₂.w r lam0 t L := by
      intro G hG
      simp only [Ntgt, Re', Submodule.mem_inf, Submodule.mem_iInf] at hG ⊢
      refine ⟨?_, ?_⟩
      · have h := sl_scale_dual I.φO I.φK Ψ hΨ I.hOK _ (hHL (Φ.symm L)) hG.1
        rwa [hwK, Φ.apply_symm_apply] at h
      · intro e' he'
        have hb : IsEdge p n' r (back e') ∧ (back e').tgt = Φ.symm L := by
          refine ⟨hbackEdge e' he'.1, ?_⟩
          show Φ.symm e'.tgt = Φ.symm L
          rw [he'.2]
        have h := sl_scale_dual I.φO I.φK Ψ hΨ I.hOK _ (hHLe' e') (hG.2 (back e') hb)
        rwa [hwK] at h
    unfold GoodRankK at hG ⊢
    obtain ⟨u, Mt, hu⟩ := hG
    have hdTv : ∀ (G : Module.Dual R₁.Kf (Vsp R₁.Kf lam0)) v, dT I.φK Ψ hΨ G v = I.φK (G (Ψ.symm v)) :=
      fun _ _ => rfl
    let u₂ : (Fin n → R₂.O) →ₗ[R₂.O] Ntgt p n' R₂.ι R₂.σ R₂.w r lam0 t L :=
      { toFun := fun x => ⟨dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j)), hN _ (u _).2⟩
        map_add' := by
          intro x y
          have hx : (fun j => I.φO.symm ((x + y) j)) =
              (fun j => I.φO.symm (x j)) + (fun j => I.φO.symm (y j)) := by
            funext j; simp
          apply Subtype.ext
          apply LinearMap.ext
          intro v
          simp only [hx, map_add (f := _), Submodule.coe_add, LinearMap.add_apply, hdTv]
        map_smul' := by
          intro c x
          have hx : (fun j => I.φO.symm ((c • x) j)) = I.φO.symm c • (fun j => I.φO.symm (x j)) := by
            funext j; simp
          apply Subtype.ext
          apply LinearMap.ext
          intro v
          show I.φK ((u fun j => I.φO.symm ((c • x) j) : Module.Dual R₁.Kf (Vsp R₁.Kf lam0)) (Ψ.symm v)) =
            (c • (dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j)) : Module.Dual R₂.Kf (Vsp R₂.Kf lam0))) v
          rw [hx, map_smul, LinearMap.smul_apply, hdTv]
          simp only [SetLike.val_smul, Submodule.coe_smul_of_tower, LinearMap.smul_apply]
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, I.hOK, RingEquiv.apply_symm_apply] }
    refine ⟨u₂, Mt.map I.φO, ?_⟩
    intro x j
    have hbe : ∀ i (G : Module.Dual R₁.Kf (Vsp R₁.Kf lam0)),
        be p r lam0 (Ψ (F i)) (dT I.φK Ψ hΨ G) = I.φK (be p r lam0 (F i) G) := by
      intro i G
      simp only [be]
      rw [← hpK, ← hΨ, dT_apply]
    have hx := hu (fun j => I.φO.symm (x j)) j
    show ∑ i, algebraMap R₂.O R₂.Kf (I.φO (Mt j i)) *
        be p r lam0 (Ψ (F i)) (dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j))) =
      algebraMap R₂.O R₂.Kf ((p : R₂.O) ^ D * x j)
    calc ∑ i, algebraMap R₂.O R₂.Kf (I.φO (Mt j i)) *
          be p r lam0 (Ψ (F i)) (dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j)))
        = ∑ i, I.φK (algebraMap R₁.O R₁.Kf (Mt j i) *
            be p r lam0 (F i) (u fun j => I.φO.symm (x j) : Module.Dual R₁.Kf (Vsp R₁.Kf lam0))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hbe, map_mul, I.hOK]
      _ = I.φK (∑ i, algebraMap R₁.O R₁.Kf (Mt j i) *
            be p r lam0 (F i) (u fun j => I.φO.symm (x j) : Module.Dual R₁.Kf (Vsp R₁.Kf lam0))) :=
          (map_sum _ _ _).symm
      _ = I.φK (algebraMap R₁.O R₁.Kf ((p : R₁.O) ^ D * I.φO.symm (x j))) := by rw [hx]
      _ = algebraMap R₂.O R₂.Kf ((p : R₂.O) ^ D * x j) := by
          rw [I.hOK, map_mul, map_pow, map_natCast, RingEquiv.apply_symm_apply]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem kF_nonneg (X : Dat) (K : Cst) (R : RS X.p X.n') (al be : X.TT → ℕ) : 0 ≤ X.kF K R al be :=
  Real.sInf_nonneg fun _ h => h.1

open Classical in
theorem kText_nonneg (X : Dat) (K : Cst) (R : RS X.p X.n') (hb : 0 < X.b') (aa bb : X.TT → ℤ) :
    0 ≤ X.kText K R aa bb := by
  unfold Dat.kText
  have h1 : 0 ≤ (if X.Inside aa bb then
      X.kF K R (fun s => (aa s - X.ccl).toNat) (fun s => (bb s - X.ccl).toNat) else 1) := by
    split_ifs
    · exact kF_nonneg _ _ _ _ _
    · exact zero_le_one
  have h2 := kF_nonneg X K R (fun s => (aa s + X.ccl).toNat) (fun s => (bb s + X.ccl).toNat)
  have h3 : 0 ≤ 12 * (X.N : ℝ) * X.k * X.ccl / X.b' := by
    unfold Dat.k
    positivity
  linarith

theorem theorem_I_of_intermediate_bounds (D : Formalism.BasicNotions.D7) (FM : Cst → Dat → Prop) (hR : LPRingIndep) (hLP : ∀ K C, MidLP K C)
    (hMean : ∀ K : Cst, K.Pos → MidMean D K (FM K)) (hN1 : ∀ K : Cst, K.Pos → TransportedAlt K (FactsLP K))
    (hN2 : ∀ K : Cst, K.Pos → TransportedAlt K (fun _ => FM K)) : SecondPartClosed D := by
  intro hA
  obtain ⟨T0, hT0, h0⟩ := hA 4 (by norm_num)
  refine ⟨T0, hT0, fun C₀ hC₀ => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C₀ hC₀
  obtain ⟨T2, hT2, h2⟩ := h1 T1 T1 T1 le_rfl le_rfl le_rfl
  obtain ⟨CA, Ckap, Ct, Cs, hCA, hCkap, hCt, hCs, hAdm⟩ := h2 T2 le_rfl
  let K : Cst := ⟨C₀, T2, CA, T1, T1, T1, Ckap, Ct, Cs⟩
  have hK : K.Pos := ⟨lt_of_lt_of_le hT0 hC₀, hT2, hCA, hT1, hT1, hT1, hCkap, hCt, hCs⟩
  obtain ⟨Ta, Ca, hTa, hCa, hFa⟩ := hN1 K hK
  obtain ⟨Tb, Cb, hTb, hCb, hFb⟩ := hN2 K hK
  refine ⟨max Ta Tb, max (max Ca Cb) K.Cmean, lt_max_of_lt_left hTa,
    lt_max_of_lt_left (lt_max_of_lt_left hCa), fun CH hCH => ?_⟩
  intro p n' m TT G' N₁ Y Yb a b' bl bu ccl Dp cStar hH
  have hm : m ≠ 0 := by
    have := hH.2.2.2.2.2.2.1
    omega
  have hY : 1 ≤ Y := hH.1
  let X : Dat := ⟨p, n', m, hm, TT, G', N₁, Y, Yb, a, b', bl, bu, ccl, Dp, cStar⟩
  have hX : X.Hyp K.C₀ CH := hH
  have hLPf : FactsLP K (max (max Ca Cb) K.Cmean) X :=
    hFa CH (le_trans (le_max_left _ _) hCH) _ (le_trans (le_max_left _ _) (le_max_left _ _)) X hX
  have hMf : FM K X :=
    hFb CH (le_trans (le_max_right _ _) hCH) (max (max Ca Cb) K.Cmean)
      (le_trans (le_max_right _ _) (le_max_left _ _)) X hX
  have hnn : 0 ≤ (TT.card : ℝ) * N₁ / Y := by positivity
  by_cases hne : Nonempty (RS p n')
  · obtain ⟨R₀⟩ := hne
    refine ⟨X.kText K R₀, kText_nonneg X K R₀ hLPf.bpos, ?_, ?_⟩
    · have h := hMean K hK hAdm X hMf R₀
      have h' : K.Cmean * (TT.card : ℝ) * N₁ / Y ≤ max (max Ca Cb) K.Cmean * (TT.card : ℝ) * N₁ / Y := by
        have := mul_le_mul_of_nonneg_right (le_max_right (max Ca Cb) K.Cmean) hnn
        calc K.Cmean * (TT.card : ℝ) * N₁ / Y = K.Cmean * ((TT.card : ℝ) * N₁ / Y) := by ring
          _ ≤ max (max Ca Cb) K.Cmean * ((TT.card : ℝ) * N₁ / Y) := this
          _ = _ := by ring
      exact le_trans h h'
    · intro W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hstd aw bw lam0 hW t ht
      let R : RS p n' := ⟨W, Qq, O, Kf, ι, σ, j, w, hstd⟩
      exact hR p n' R₀ R m 1 lam0 t Dp _ cStar (hLP K _ X hLPf R₀ aw bw lam0 hW t ht)
  · refine ⟨fun _ _ => 0, fun _ _ => le_rfl, ?_, ?_⟩
    · have h0 : meanKap TT m Y a bl bu (fun _ _ => (0 : ℝ)) = 0 := by simp [meanKap]
      rw [h0]
      have hC : 0 ≤ max (max Ca Cb) K.Cmean := le_of_lt (lt_max_of_lt_left (lt_max_of_lt_left hCa))
      have := mul_nonneg hC hnn
      calc (0 : ℝ) ≤ max (max Ca Cb) K.Cmean * ((TT.card : ℝ) * N₁ / Y) := this
        _ = _ := by ring
    · intro W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hstd
      exact absurd ⟨(⟨W, Qq, O, Kf, ι, σ, j, w, hstd⟩ : RS p n')⟩ hne

end Formalism.MainNotions.flipOneThree.Pf

end
end
