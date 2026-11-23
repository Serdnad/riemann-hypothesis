module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle017
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle008
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TwoSumsCondition
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle006
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle005
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TheoremSFromKOneOf
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaGeCOfNorm
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GainOfCapacityLoss
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

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Fl

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem ne_sum_le (s : Fin (G.P.n' v)) (r : ℕ) (hm : 2 ≤ G.P.m) (hb : s ∈ Fl.TT v → 0 ≤ Fl.b v s) :
    ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), (lamI (G.P.lam0 v) s a : ℝ) ≤
      r * Fl.c + (if s ∈ Fl.TT v ∧ G.P.m + 1 ≤ r then (Fl.a v s : ℝ) else 0) := by
  have h1 : ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), (lamI (G.P.lam0 v) s a : ℝ) ≤
      ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), ((Fl.c : ℝ) + (if s ∈ Fl.TT v ∧ a = 1 then (Fl.a v s : ℝ) else 0)) := by
    apply Finset.sum_le_sum
    intro a _
    have := ne_lamI_le Fl v s a hm hb
    by_cases hc : s ∈ Fl.TT v ∧ a = 1
    · rw [if_pos hc] at this ⊢
      exact_mod_cast this
    · rw [if_neg hc] at this ⊢
      exact_mod_cast this
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((Icc (G.P.m + 2 - r) (G.P.m + 1)).card : ℝ) ≤ r := by
    rw [Nat.card_Icc]
    have : G.P.m + 1 + 1 - (G.P.m + 2 - r) ≤ r := by omega
    exact_mod_cast this
  have h3 := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg Fl.c : (0 : ℝ) ≤ Fl.c)
  have h4 : ∑ a ∈ Icc (G.P.m + 2 - r) (G.P.m + 1), (if s ∈ Fl.TT v ∧ a = 1 then (Fl.a v s : ℝ) else 0) =
      (if s ∈ Fl.TT v ∧ G.P.m + 1 ≤ r then (Fl.a v s : ℝ) else 0) := by
    by_cases hs : s ∈ Fl.TT v
    · simp only [hs, true_and]
      rw [Finset.sum_ite_eq' (Icc (G.P.m + 2 - r) (G.P.m + 1)) 1 (fun _ => (Fl.a v s : ℝ))]
      have : (1 ∈ Icc (G.P.m + 2 - r) (G.P.m + 1)) ↔ G.P.m + 1 ≤ r := by
        rw [Finset.mem_Icc]; omega
      simp only [this]
    · simp [hs]
  rw [h4] at h1
  linarith

end Fl

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem ne_k_pos : (1 : ℝ) ≤ D.R.k := by
  have h2 := D.R.m_add_three_le_k
  have : 1 ≤ D.R.k := by omega
  exact_mod_cast this

theorem ne_bT_le (hS : Formalism.MainNotions.SizesAt L) (t) : (L.bT t : ℝ) ≤ 5 / 4 * L.sc.b' := by
  have hx := L.sc.one_lt_alt
  have hLa := hS.2.2.2.2.2.2.2.2.1
  have hRho := hS.2.2.2.2.2.2.2.2.2.1
  have hBot := hS.2.2.2.2.2.2.2.2.2.2.1 t
  unfold Formalism.MainNotions.SizeRho at hRho
  have hk := ne_k_pos (D := D)
  have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_nonneg L.sc.x_pos.le _) hLa.1
  have h1 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k :=
    div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg L.sc.x_pos.le _) (Real.log_nonneg hx.le)) hLa0) (by linarith)
  have h2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
  have h3 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
    have : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
        4 * (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    linarith
  have h4 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  have h5 := mul_le_mul_of_nonneg_right h3 L.sc.b'_pos.le
  linarith

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lamF altF)

variable {p : ℕ} [hp : Fact p.Prime] {n' r0 r1 : ℕ} (K' : Type) [Field K'] [Algebra (K0 p) K']

def Aw (w : WW p) (k : ℕ) : K' := wK' p K' ((sigW p)^[k] w)

def FrobSumH (p n' r0 r1 : ℕ) (K' : Type) [Field K'] (R : Subring K') : Prop :=
  ∀ (s : Finset (Fin n')) (x : Fin n' → MvPowerSeries (Zidx n' r0 r1) K'), (∀ i ∈ s, IntR R (x i)) →
    ∃ Y : MvPowerSeries (Zidx n' r0 r1) K', IntR R Y ∧
      (∑ i ∈ s, x i) ^ p = ∑ i ∈ s, x i ^ p + MvPowerSeries.C (p : K') * Y

def FrobWH (p : ℕ) [Fact p.Prime] : Prop := ∀ a : WW p, ∃ y : WW p, sigW p a = a ^ p + (p : WW p) * y

variable {K'} (vp : K')

theorem th_Aw_mem (w : WW p) (k : ℕ) : Aw K' w k ∈ Rp p K' vp := W_mem_Rp p K' vp _

theorem th_Aw_succ (hW : FrobWH p) (w : WW p) (k : ℕ) :
    ∃ y ∈ Rp p K' vp, Aw K' w (k + 1) = Aw K' w k ^ p + (p : K') * y := by
  obtain ⟨y, hy⟩ := hW ((sigW p)^[k] w)
  refine ⟨wK' p K' y, ?_, ?_⟩
  · have h1 := th_Aw_mem vp y 0
    simpa [Aw] using h1
  · simp only [Aw, wK', Function.iterate_succ_apply', hy, map_add (f := _), map_mul, map_pow, map_natCast]

theorem th_frob_lin (hF : FrobSumH p n' r0 r1 K' (Rp p K' vp)) (hW : FrobWH p) (w : WW p) (P : Finset (Fin n'))
    (e : Fin n' → ℕ) (x : Fin n' → MvPowerSeries (Zidx n' r0 r1) K') (hx : ∀ s, IntR (Rp p K' vp) (x s)) :
    Cg (Rp p K' vp) (p : K') ((∑ s ∈ P, MvPowerSeries.C (Aw K' w (e s)) * x s) ^ p)
      (∑ s ∈ P, MvPowerSeries.C (Aw K' w (e s + 1)) * x s ^ p) := by
  have hint : ∀ s ∈ P, IntR (Rp p K' vp) (MvPowerSeries.C (Aw K' w (e s)) * x s) :=
    fun s _ => IntR_mul (IntR_C (R := Rp p K' vp) (th_Aw_mem vp w _)) (hx s)
  obtain ⟨Y, hY, hEq⟩ := hF P (fun s => MvPowerSeries.C (Aw K' w (e s)) * x s) hint
  have h1 : Cg (Rp p K' vp) (p : K') ((∑ s ∈ P, MvPowerSeries.C (Aw K' w (e s)) * x s) ^ p)
      (∑ s ∈ P, (MvPowerSeries.C (Aw K' w (e s)) * x s) ^ p) := ⟨Y, hY, hEq⟩
  refine cg_trans h1 (cg_sum _ _ _ fun s _ => ?_)
  obtain ⟨z, hz, hzeq⟩ := th_Aw_succ vp hW w (e s)
  rw [mul_pow, ← map_pow]
  refine cg_mul (IntR_pow (hx s) p) (IntR_C (R := Rp p K' vp) (th_Aw_mem vp w _)) ?_ (cg_refl _)
  refine cg_of_coeff fun n => ?_
  by_cases hn : n = 0
  · subst hn
    refine ⟨-z, Subring.neg_mem _ hz, ?_⟩
    rw [MvPowerSeries.coeff_zero_C, MvPowerSeries.coeff_zero_C, hzeq]
    ring
  · refine ⟨0, Subring.zero_mem _, ?_⟩
    rw [MvPowerSeries.coeff_C, MvPowerSeries.coeff_C, if_neg hn, if_neg hn]
    ring

def linK (K' : Type) [Field K'] [Algebra (K0 p) K'] (w : WW p) (P : Finset (Fin n')) (a : Fin r0) (b : Fin r1)
    (k : ℕ) : MvPowerSeries (Zidx n' r0 r1) K' :=
  ∑ s ∈ P, MvPowerSeries.C (Aw K' w (s.val + k)) * MvPowerSeries.X (s, a, b) ^ (p ^ k)

theorem th_linK_int (w : WW p) (P : Finset (Fin n')) (a : Fin r0) (b : Fin r1) (k : ℕ) :
    IntR (Rp p K' vp) (linK K' w P a b k) := by
  unfold linK
  exact IntR_sum _ _ fun s _ => IntR_mul (IntR_C (R := Rp p K' vp) (th_Aw_mem vp w _))
    (IntR_pow (IntR_X (R := Rp p K' vp) _) _)

theorem th_linK_const (w : WW p) (P : Finset (Fin n')) (a : Fin r0) (b : Fin r1) :
    MvPowerSeries.constantCoeff (linK K' w P a b 0) = 0 := by
  simp [linK]

theorem th_claimF (hF : FrobSumH p n' r0 r1 K' (Rp p K' vp)) (hW : FrobWH p) (w : WW p) (P : Finset (Fin n'))
    (a : Fin r0) (b : Fin r1) (k : ℕ) :
    Cg (Rp p K' vp) (p : K') (linK K' w P a b 0 ^ (p ^ k)) (linK K' w P a b k) := by
  induction k with
  | zero =>
    apply cg_of_eq
    simp only [pow_zero, pow_one]
  | succ k ih =>
    have hL : IntR (Rp p K' vp) (linK K' w P a b 0) := th_linK_int vp w P a b 0
    have h1 := cg_pow (IntR_pow hL (p ^ k)) (th_linK_int vp w P a b k) ih p
    rw [← pow_mul, ← pow_succ] at h1
    refine cg_trans h1 ?_
    have h2 := th_frob_lin vp hF hW w P (fun s => s.val + k) (fun s => MvPowerSeries.X (s, a, b) ^ (p ^ k))
      (fun s => IntR_pow (IntR_X (R := Rp p K' vp) _) _)
    simp only [← pow_mul, ← pow_succ] at h2
    exact h2

theorem th_coeff_linK (w : WW p) (P : Finset (Fin n')) (a : Fin r0) (b : Fin r1) (k : ℕ)
    (n : Zidx n' r0 r1 →₀ ℕ) :
    MvPowerSeries.coeff n (linK K' w P a b k) =
      ∑ s ∈ P, Aw K' w (s.val + k) * (if n = Finsupp.single (s, a, b) (p ^ k) then 1 else 0) := by

  simp only [linK, map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X_pow]

theorem th_reindex (w : WW p) (hper : (sigW p)^[n'] w = w) (P : Finset (Fin n'))
    (hPa : ∀ s ∈ P, ∀ d, posAdd s (2 * d) ∈ P) (hPs : ∀ s ∈ P, ∀ d, posSub s (2 * d) ∈ P)
    (a : Fin r0) (b : Fin r1) (n : Zidx n' r0 r1 →₀ ℕ) (l : ℕ) :
    (-1 : K') ^ l * ∑ s ∈ P, Aw K' w (s.val + 2 * l) *
        (if n = Finsupp.single (s, a, b) (p ^ (2 * l)) then 1 else 0) =
      ∑ t ∈ P, Aw K' w t.val *
        (if n = Finsupp.single (posSub t (2 * l), a, b) (p ^ (2 * l)) then (-1 : K') ^ l else 0) := by
  have hAw : ∀ s : Fin n', Aw K' w (posAdd s (2 * l)).val = Aw K' w (s.val + 2 * l) := by
    intro s
    simp only [Aw, posAdd]
    rw [Function.IsPeriodicPt.iterate_mod_apply hper]
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_nbij' (fun t => posSub t (2 * l)) (fun s => posAdd s (2 * l)) (fun t ht => hPs t ht l)
    (fun s hs => hPa s hs l) (fun t _ => th_posAdd_posSub t _) (fun s _ => th_posSub_posAdd s _) (fun t _ => ?_)
  have h1 : Aw K' w t.val = Aw K' w ((posSub t (2 * l)).val + 2 * l) := by
    rw [← hAw, th_posAdd_posSub]
  rw [h1]
  split_ifs <;> ring

theorem th_claimM (hF : FrobSumH p n' r0 r1 K' (Rp p K' vp)) (hW : FrobWH p) (μ : PowerSeries K')
    (hT1 : ∀ n, ∃ y ∈ Rp p K' vp, PowerSeries.coeff n μ - PowerSeries.coeff n (altF K' p) = (p : K') * y)
    (w : WW p) (hper : (sigW p)^[n'] w = w) (P : Finset (Fin n'))
    (hPa : ∀ s ∈ P, ∀ d, posAdd s (2 * d) ∈ P) (hPs : ∀ s ∈ P, ∀ d, posSub s (2 * d) ∈ P)
    (a : Fin r0) (b : Fin r1) :
    Cg (Rp p K' vp) (p : K') (PowerSeries.subst (linK K' w P a b 0) μ)
      (∑ t ∈ P, MvPowerSeries.C (Aw K' w t.val) * sSer p K' t a b) := by
  have hL0 := th_linK_const (K' := K') w P a b
  have hsL : PowerSeries.HasSubst (linK K' w P a b 0) := PowerSeries.HasSubst.of_constantCoeff_zero hL0

  have h1 : Cg (Rp p K' vp) (p : K') (PowerSeries.subst (linK K' w P a b 0) μ)
      (PowerSeries.subst (linK K' w P a b 0) (altF K' p)) := by
    choose y hy he using hT1
    have e : μ = altF K' p + PowerSeries.C (p : K') * PowerSeries.mk y := by
      ext n
      rw [map_add (f := _), PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← he n]
      ring
    refine ⟨PowerSeries.subst (linK K' w P a b 0) (PowerSeries.mk y),
      IntR_psubst hL0 (th_linK_int vp w P a b 0) (fun n => by rw [PowerSeries.coeff_mk]; exact hy n), ?_⟩
    conv_lhs => rw [e]
    rw [PowerSeries.subst_add hsL, PowerSeries.subst_mul hsL, PowerSeries.subst_C]
  refine cg_trans h1 (cg_of_coeff fun n => ?_)
  rw [Formalism.InvariantFactorPaths.G7.TwoS.coeff_subst_altF hp.out.two_le hL0 n]
  choose y hy he using fun l => cg_coeff (th_claimF vp hF hW w P a b (2 * l)) n
  refine ⟨∑ l ∈ range (n.degree + 1), (-1 : K') ^ l * y l,
    Subring.sum_mem _ fun l _ => (Rp p K' vp).mul_mem ((Rp p K' vp).pow_mem ((Rp p K' vp).neg_mem
      (Rp p K' vp).one_mem) l) (hy l), ?_⟩
  have e2 : MvPowerSeries.coeff n (∑ t ∈ P, MvPowerSeries.C (Aw K' w t.val) * sSer p K' t a b) =
      ∑ l ∈ range (n.degree + 1), (-1 : K') ^ l * MvPowerSeries.coeff n (linK K' w P a b (2 * l)) := by

    rw [map_sum]
    simp only [MvPowerSeries.coeff_C_mul, th_coeff_linK, th_reindex w hper P hPa hPs a b n]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum]
    rfl
  rw [e2, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← pow_mul, he l]
  ring

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

def eb_Pc (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (I : X.ColCh j) :
    MvPolynomial (Formalism.DworkPowerSeriesWeights.ZV (2 * (X.G.P.n' v / 2)) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
      (MvPolynomial (ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j)) K') :=
  ∏ s : ea_S X v, Formalism.DworkPowerSeriesWeights.minorProd
    (fun (i : Fin (NN X.G.P.m X.t j)) (b : Fin (NN X.G.P.m X.t (j + 1))) =>
      (∑ a : Fin (NN X.G.P.m X.t j), MvPolynomial.C (MvPolynomial.X (s, i, a)) * MvPolynomial.X (s, a, b) :
        MvPolynomial (Formalism.DworkPowerSeriesWeights.ZV (2 * (X.G.P.n' v / 2)) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
          (MvPolynomial (ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j)) K')))
    (ea_hts X v j s) (ea_hp X v j s) (ea_Ic X v j I s)

theorem eb_poly (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (I : X.ColCh j) :
    MvPolynomial.map (MvPolynomial.map (Int.castRingHom K')) (X.PIv j I v) =
      MvPolynomial.rename (ea_eps X v j) (MvPolynomial.map
        (MvPolynomial.rename (eb_phi X v j) : MvPolynomial _ K' →ₐ[K'] MvPolynomial _ K').toRingHom
        (eb_Pc X v j K' I)) := by
  unfold Sys.PIv eb_Pc Formalism.DworkPowerSeriesWeights.minorProd
  simp only [map_prod]
  refine (Fintype.prod_equiv (ea_e X v).symm _ _ fun s => ?_).symm
  rw [Finset.prod_range]
  exact Finset.prod_congr rfl fun c _ => eb_fac X v j K' I s c

theorem eb_jet (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (F : MvPowerSeries (X.ZA j) K') (I : X.ColCh j) :
    applyD (X.PIv j I v) F = MvPolynomial.rename (eb_phi X v j)
      (Formalism.DworkPowerSeriesWeights.frameJet (ea_colN X v j) (ea_hts X v j) (ea_hp X v j) (ea_Ic X v j I) (resV (ea_eps X v j) F)) := by
  rw [eb_applyD, eb_poly, eb_J_rename _ (eb_eps_inj X v j), eb_J_map]
  rfl

theorem eb_brJet : ea_BrJet X := by
  intro v j K' _ F I n
  rw [eb_jet]
  by_cases h : ∃ n', Finsupp.mapDomain (eb_phi X v j) n' = n
  · obtain ⟨n', rfl⟩ := h
    exact Or.inr ⟨n', MvPolynomial.coeff_rename_mapDomain _ (eb_phi_inj X v j) _ n'⟩
  · exact Or.inl (MvPolynomial.coeff_rename_eq_zero _ _ _ fun u hu => absurd ⟨u, hu⟩ h)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem ea_applyD_scale {σ τ K : Type} [Field K] (q E : ℕ) (P : MvPolynomial σ (MvPolynomial τ ℤ))
    (f : MvPowerSeries σ K) :
    applyD ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P) f = ((q : K) ^ E) • applyD P f := by
  classical
  have hc : ∀ n, AddMonoidAlgebra.coeff ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P) n =
      (q : MvPolynomial τ ℤ) ^ E * AddMonoidAlgebra.coeff P n := by
    intro n
    have : (q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E = MvPolynomial.C ((q : MvPolynomial τ ℤ) ^ E) := by
      rw [map_pow, map_natCast]
    rw [this, MvPolynomial.coeff_C_mul]
  have hsub : ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P).support ⊆ P.support := by
    intro n hn
    rw [MvPolynomial.mem_support_iff, hc] at hn
    rw [MvPolynomial.mem_support_iff]
    intro h0
    rw [h0, mul_zero] at hn
    exact hn rfl
  unfold applyD
  rw [Finset.sum_subset hsub (fun n _ hn => by
    rw [MvPolynomial.notMem_support_iff.1 hn, map_zero, smul_zero]), Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hc, map_mul, map_pow, map_natCast, smul_comm]
  congr 1
  rw [MvPolynomial.smul_eq_C_mul, map_pow, map_natCast]

theorem ea_applyD_zero {σ τ K : Type} [Field K] (f : MvPowerSeries σ K) :
    applyD (0 : MvPolynomial σ (MvPolynomial τ ℤ)) f = 0 := by
  unfold applyD
  rw [MvPolynomial.support_zero, Finset.sum_empty]

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

theorem ea_PIvS_eq (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    PIvS X j I i0 v = (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^
      (∑ s : Fin (X.G.P.n' v), ∑ c ∈ range (X.nuv v (j + 1) s 1).toNat, X.colExp j I i0 v s c) * X.PIv j I v := by
  unfold PIvS Sys.PIv
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem ea_colFac_zero (j : ℕ) (I : X.ColCh j) (v : X.Pl) (s : Fin (X.G.P.n' v)) (c : ℕ)
    (h : ¬ Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val) : X.colFac j I v s c = 0 := by
  unfold Function.Injective at h
  push Not at h
  obtain ⟨x, y, hxy, hne⟩ := h
  unfold Sys.colFac
  refine Matrix.det_zero_of_column_eq hne fun k => ?_
  show (∑ a : Fin (NN X.G.P.m X.t j), _ * MvPolynomial.X (⟨v, (s, a, I v s c x.val)⟩ : X.ZA j)) =
    ∑ a : Fin (NN X.G.P.m X.t j), _ * MvPolynomial.X (⟨v, (s, a, I v s c y.val)⟩ : X.ZA j)
  have hxy' : I v s c x.val = I v s c y.val := hxy
  rw [hxy']

theorem ea_card_img {H N : ℕ} (g : Fin H → Fin N) (hg : Function.Injective g) (i : ℕ) :
    ((univ.image g) ∩ univ.filter (fun b : Fin N => b.val < i)).card =
      (univ.filter fun x : Fin H => (g x).val < i).card := by
  rw [← Finset.card_image_of_injective _ hg]
  congr 1
  ext b
  simp only [mem_inter, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨x, rfl⟩, hb⟩
    exact ⟨x, hb, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, hx⟩

theorem ea_Exp_eq (v : X.Pl) (j i : ℕ) (I : X.ColCh j)
    (h : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ), Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val) :
    ∑ s : Fin (X.G.P.n' v), ∑ c ∈ range (X.nuv v (j + 1) s 1).toNat, X.colExp j I (fun _ => i) v s c =
      ea_Exp X v j i I := by
  unfold ea_Exp
  refine (Fintype.sum_equiv (ea_e X v).symm _ _ fun s' => ?_).symm
  rw [← Fin.sum_univ_eq_sum_range (fun c => X.colExp j I (fun _ => i) v ((ea_e X v).symm s') c)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 := ea_card_img (ea_Ic X v j I s' c) (h ((ea_e X v).symm s') c.val) i
  have e2 := ea_card_fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)
    (fun x => (I v ((ea_e X v).symm s') c.val x).val < i)
  have e3 : ((univ.image (ea_Ic X v j I s' c)) ∩
      univ.filter (fun b : Fin (NN X.G.P.m X.t (j + 1)) => b.val < i)).card =
      ((range (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)).filter
        fun x => (I v ((ea_e X v).symm s') c.val x).val < i).card := e1.trans e2
  rw [e3]
  unfold Sys.colExp
  have hv : ((ea_e X v).symm s').val = s'.val := rfl
  by_cases hodd : s'.val % 2 = 0
  · rw [if_pos hodd, if_neg (by unfold IsOddPos; rw [hv]; omega)]
    rfl
  · rw [if_neg hodd, if_pos (by unfold IsOddPos; rw [hv]; omega)]

theorem ea_brScale : ea_BrScale X := by
  intro v j i K' _ F I n
  by_cases h : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ), c ∈ range (X.nuv v (j + 1) s 1).toNat →
      X.colFac j I v s c ≠ 0
  · by_cases h2 : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ),
        Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val
    · right
      rw [ea_PIvS_eq, ea_applyD_scale, MvPolynomial.coeff_smul, smul_eq_mul, ea_Exp_eq X v j i I h2]
    ·
      right
      rw [ea_PIvS_eq, ea_applyD_scale, MvPolynomial.coeff_smul, smul_eq_mul]
      congr 2
      unfold ea_Exp
      refine (Fintype.sum_equiv (ea_e X v).symm _ _ fun s' => ?_).symm
      rw [← Fin.sum_univ_eq_sum_range (fun c => X.colExp j I (fun _ => i) v ((ea_e X v).symm s') c)]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hinj : Function.Injective fun i' : Fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val) =>
          I v ((ea_e X v).symm s') c.val i'.val := by
        by_contra hni
        exact h _ c.val (mem_range.2 c.isLt) (ea_colFac_zero X j I v _ _ hni)
      have e1 := ea_card_img (ea_Ic X v j I s' c) hinj i
      have e2 := ea_card_fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)
        (fun x => (I v ((ea_e X v).symm s') c.val x).val < i)
      have e3 : ((univ.image (ea_Ic X v j I s' c)) ∩
          univ.filter (fun b : Fin (NN X.G.P.m X.t (j + 1)) => b.val < i)).card =
          ((range (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)).filter
            fun x => (I v ((ea_e X v).symm s') c.val x).val < i).card := e1.trans e2
      rw [e3]
      unfold Sys.colExp
      have hv : ((ea_e X v).symm s').val = s'.val := rfl
      by_cases hodd : s'.val % 2 = 0
      · rw [if_pos hodd, if_neg (by unfold IsOddPos; rw [hv]; omega)]
        rfl
      · rw [if_neg hodd, if_pos (by unfold IsOddPos; rw [hv]; omega)]
  · left
    push Not at h
    obtain ⟨s, c, hc, h0⟩ := h
    have hz : PIvS X j I (fun _ => i) v = 0 := by
      unfold PIvS
      refine Finset.prod_eq_zero (Finset.mem_univ s) (Finset.prod_eq_zero hc ?_)
      rw [h0, mul_zero]
    rw [hz, ea_applyD_zero, MvPolynomial.coeff_zero]
    rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
