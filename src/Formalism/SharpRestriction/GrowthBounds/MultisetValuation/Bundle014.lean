module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartB
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AofUpdate
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle004
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle012
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle013
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle005
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF Gser Aser Aser' AA leadT G1)

section Scale

variable (p : ℕ) [hp : Fact p.Prime] (K' : Type) [Field K'] [Algebra (K0 p) K']

theorem th_vp_ne (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) : vp ≠ 0 := by
  intro hv
  have hpos : p ^ 2 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow two_ne_zero hp.out.one_lt)
  rw [hv, zero_pow hpos] at hvp
  have hp0 : (p : K') ≠ 0 := by
    rw [← map_natCast (algebraMap (K0 p) K')]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hp.out.ne_zero)
  exact hp0 hvp.symm

theorem th_wt_AA (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) {x y : Fin 2} (hxy : x ≠ y) (d : Fin 2 →₀ ℕ) :
    ∃ r ∈ Rp p K' vp, vp ^ d.degree * MvPowerSeries.coeff d (AA K' p x y - leadT K' p x y) = vp ^ (p + 1) * r := by
  classical
  have hp2 := hp.out.two_le
  rw [map_sub, Formalism.InvariantFactorPaths.G7.leadT_eq, MvPowerSeries.coeff_monomial]
  by_cases hd : d = Finsupp.single x 1 + Finsupp.single y p
  · have hx : d x = (p ^ 2) ^ 0 := by rw [hd]; simp [hxy.symm]
    have hy : d y = p * (p ^ 2) ^ 0 := by rw [hd]; simp [hxy]
    rw [if_pos hd, Formalism.InvariantFactorPaths.G7.coeff_AA_of K' hp2 le_rfl hx hy]
    exact ⟨0, (Rp p K' vp).zero_mem, by simp⟩
  · rw [if_neg hd, sub_zero]
    by_cases h : MvPowerSeries.coeff d (AA K' p x y) = 0
    · exact ⟨0, (Rp p K' vp).zero_mem, by rw [h]; simp⟩
    · obtain ⟨i, j, hij, hx, hy⟩ := Formalism.InvariantFactorPaths.G7.coeff_AA_ne_zero h
      have hj : 1 ≤ j := by
        by_contra hj
        obtain rfl : j = 0 := by omega
        obtain rfl : i = 0 := by omega
        apply hd
        ext z
        rcases Formalism.InvariantFactorPaths.G7.finset_fin_two_eq_cases x y hxy z with rfl | rfl
        · simp [hx, hxy.symm]
        · simp [hy, hxy]
      have h4 : 4 ≤ p ^ 2 := by nlinarith
      obtain ⟨gi, hgi, hi', _⟩ := Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.geom_sum_mul_pred h4 i
      obtain ⟨gj, hgj, hj', _⟩ := Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.geom_sum_mul_pred h4 j
      have hle : i + j + 1 ≤ gi + p * gj := by nlinarith
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      have hdeg : d.degree = (p ^ 2 - 1) * k + (p ^ 2 - 1) * (i + j + 1) + (p + 1) := by
        rw [Formalism.InvariantFactorPaths.G7.degree_fin_two_eq_add_of_ne hxy, hx, hy, hgi, hgj]
        have : (p ^ 2 - 1) * gi + 1 + p * ((p ^ 2 - 1) * gj + 1) = (p ^ 2 - 1) * (gi + p * gj) + (p + 1) := by ring
        rw [this, hk]
        ring
      refine ⟨(p : K') ^ k, (Rp p K' vp).pow_mem (natCast_mem _ p) k, ?_⟩
      rw [Formalism.InvariantFactorPaths.G7.coeff_AA_of K' hp2 hij hx hy, hdeg, pow_add, pow_add, pow_mul, pow_mul, hvp]
      have hp0 := pK'_ne p K'
      field_simp

theorem exists_atPi_G1_eq_C_pow_mul_integral_series (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K')) {c c' : K'} (hc : c ∈ Rp p K' vp)
    (hc' : c' ∈ Rp p K' vp) :
    ∃ Rr : MvPowerSeries (Fin 2) K', IntR (Rp p K' vp) Rr ∧ MvPowerSeries.constantCoeff Rr = 0 ∧
      atPi vp (G1 p c c') = MvPowerSeries.C (vp ^ (p + 1)) * Rr := by
  have hv : vp ^ (p + 1) ≠ 0 := pow_ne_zero _ (th_vp_ne p K' vp hvp)
  refine ⟨MvPowerSeries.C ((vp ^ (p + 1))⁻¹) * atPi vp (G1 p c c'), fun d => ?_, ?_, ?_⟩
  · obtain ⟨r1, hr1, e1⟩ := th_wt_AA p K' vp hvp (show (0 : Fin 2) ≠ 1 by decide) d
    obtain ⟨r2, hr2, e2⟩ := th_wt_AA p K' vp hvp (show (1 : Fin 2) ≠ 0 by decide) d
    rw [MvPowerSeries.coeff_C_mul]
    have e : MvPowerSeries.coeff d (atPi vp (G1 p c c')) = vp ^ (p + 1) * (c * r1 - c' * r2) := by
      show vp ^ d.degree * MvPowerSeries.coeff d (G1 p c c') = _
      unfold G1
      rw [map_sub, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul]
      linear_combination c * e1 - c' * e2
    rw [e, ← mul_assoc, inv_mul_cancel₀ hv, one_mul]
    exact (Rp p K' vp).sub_mem ((Rp p K' vp).mul_mem hc hr1) ((Rp p K' vp).mul_mem hc' hr2)
  · rw [map_mul]
    have : MvPowerSeries.constantCoeff (atPi vp (G1 p c c')) = 0 := by
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
      show vp ^ (0 : Fin 2 →₀ ℕ).degree * MvPowerSeries.coeff 0 (G1 p c c') = 0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.InvariantFactorPaths.G7.constant_coeff_g_one hp.out.ne_zero, mul_zero]
    rw [this, mul_zero]
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hv, map_one, one_mul]

end Scale

theorem th_subst_scale {κ τ R : Type} [Finite κ] [CommRing R] (vp : R) (s : κ → MvPowerSeries τ R)
    (hs : MvPowerSeries.HasSubst s) (f : MvPowerSeries κ R) :
    MvPowerSeries.subst (fun k => MvPowerSeries.C vp * s k) f = MvPowerSeries.subst s (atPi vp f) := by
  rw [atPi_eq_rescale, MvPowerSeries.rescale_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.smul_X _) hs]
  congr 1
  funext k
  have : ((fun _ : κ => vp) • (MvPowerSeries.X : κ → MvPowerSeries κ R)) k =
      MvPowerSeries.C vp * MvPowerSeries.X k := by
    rw [Pi.smul_apply', MvPowerSeries.smul_eq_C_mul]
  rw [this, ← MvPowerSeries.coe_substAlgHom hs, map_mul, MvPowerSeries.substAlgHom_X]
  congr 1
  exact ((MvPowerSeries.substAlgHom hs).commutes vp).symm

theorem th_map_Gser {p : ℕ} {K K2 : Type} [Field K] [Field K2] (φ : K →+* K2) (c c' : K) :
    MvPowerSeries.map φ (Gser p c c') = Gser p (φ c) (φ c') := by
  unfold Gser
  rw [map_sub, map_mul, map_mul, MvPowerSeries.map_C, MvPowerSeries.map_C]
  unfold Aser Aser'
  congr 2
  · funext n
    change φ (∑ i ∈ Finset.range (n 0 + 1), ∑ j ∈ Finset.range (n 1 + 1),
      if i ≤ j ∧ n 0 = (p ^ 2) ^ i ∧ n 1 = p * (p ^ 2) ^ j then ((p : K) ^ (i + j + 1))⁻¹ else 0) = _

    simp [map_sum, apply_ite, map_inv₀]
  · funext n
    change φ (∑ i ∈ Finset.range (n 1 + 1), ∑ j ∈ Finset.range (n 0 + 1),
      if i ≤ j ∧ n 1 = (p ^ 2) ^ i ∧ n 0 = p * (p ^ 2) ^ j then ((p : K) ^ (i + j + 1))⁻¹ else 0) = _

    simp [map_sum, apply_ite, map_inv₀]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem sum_Icc_shift (f : ℕ → ℝ) (m : ℕ) : ∑ j ∈ Icc 1 m, f j = ∑ j ∈ range m, f (j + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem sum_ind {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset ι) (f : ι → ℝ) :
    ∑ v ∈ A, f v = ∑ v, if v ∈ A then f v else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp

theorem basic₂ {ι : Type} [Fintype ι] [DecidableEq ι] (mm : ℕ) (VV BB : Finset ι) (hBB : BB ⊆ VV)
    (Gn G0n PRn Prr : ι → ℕ → ℝ) (S : ι → ℝ) (dG : ℕ → ℝ) (inB : ℕ → ι → Prop) [∀ j v, Decidable (inB j v)]
    (hin : ∀ j v, inB j v ↔ v ∈ BB ∧ G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1))
    (hPR : ∀ v ∈ VV, ∀ j < mm, Prr v (j + 1) ≤ PRn v (j + 1))
    (hS : ∀ v ∈ VV, ∑ j ∈ range mm, max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 ≤ S v) :
    ∑ j ∈ range mm, (∑ v ∈ VV, max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) +
        ∑ v ∈ univ \ VV, G0n v (j + 1)) - ∑ j ∈ range mm, dG j ≤
      ∑ v ∈ VV \ BB, S v + ∑ j ∈ range mm, (∑ v, (if inB j v then Gn v (j + 1) else G0n v (j + 1)) - dG j -
        ∑ v, (if inB j v then Prr v (j + 1) else 0)) := by
  have hS' : ∑ j ∈ range mm, ∑ v, (if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0)
      ≤ ∑ v ∈ VV \ BB, S v := by
    rw [Finset.sum_comm, sum_ind (VV \ BB) S]
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : v ∈ VV \ BB
    · simp only [hv, ↓reduceIte]
      exact hS v (Finset.mem_sdiff.1 hv).1
    · simp [hv]
  have key : ∀ j ∈ range mm,
      (∑ v ∈ VV, max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) + ∑ v ∈ univ \ VV, G0n v (j + 1)) - dG j ≤
      ∑ v, (if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0) +
      ((∑ v, (if inB j v then Gn v (j + 1) else G0n v (j + 1))) - dG j -
        ∑ v, (if inB j v then Prr v (j + 1) else 0)) := by
    intro j hj
    have hj' : j < mm := Finset.mem_range.1 hj
    suffices h : ∑ v, ((if v ∈ VV then max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) else 0) +
        (if v ∈ univ \ VV then G0n v (j + 1) else 0) + (if inB j v then Prr v (j + 1) else 0)) ≤
        ∑ v, ((if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0) +
        (if inB j v then Gn v (j + 1) else G0n v (j + 1))) by
      rw [sum_ind VV, sum_ind (univ \ VV)]
      simp only [Finset.sum_add_distrib] at h
      linarith
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : v ∈ VV
    · have hv2 : v ∉ univ \ VV := by simp [hv]
      by_cases hb : v ∈ BB
      · have hv3 : v ∉ VV \ BB := by simp [hb]
        by_cases hi : inB j v
        · have h1 := ((hin j v).1 hi).2
          have h2 := hPR v hv j hj'
          simp only [hv, hv2, hv3, hi, ↓reduceIte]
          rw [max_eq_left h1]
          linarith
        · have h1 : ¬ (G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1)) := fun h => hi ((hin j v).2 ⟨hb, h⟩)
          simp only [hv, hv2, hv3, hi, ↓reduceIte]
          rw [max_eq_right (le_of_lt (not_le.1 h1))]
          linarith
      · have hv3 : v ∈ VV \ BB := Finset.mem_sdiff.2 ⟨hv, hb⟩
        have hi : ¬ inB j v := fun h => hb ((hin j v).1 h).1
        simp only [hv, hv2, hv3, hi, ↓reduceIte]
        have hm : max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) ≤
            max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 + G0n v (j + 1) := by
          have := le_max_left (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0
          have := le_max_right (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0
          exact max_le (by linarith) (by linarith)
        linarith
    · have hv2 : v ∈ univ \ VV := by simp [hv]
      have hb : v ∉ BB := fun h => hv (hBB h)
      have hv3 : v ∉ VV \ BB := by simp [hv]
      have hi : ¬ inB j v := fun h => hb ((hin j v).1 h).1
      simp only [hv, hv2, hv3, hi, ↓reduceIte]
      linarith
  have hsum := Finset.sum_le_sum key
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum ⊢
  linarith

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem PrZ_cast (v : X.Pl) (j : ℕ) :
    ((PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j : ℤ) : ℝ) = X.Conclusion₂ v j := by
  simp only [Sys.Conclusion₂, PrZ, Pr]
  push_cast
  congr 1
  obtain ⟨k, hk⟩ := (X.G.P.setting v).even
  rw [hk]
  have h2 : ((k + k : ℕ) : ℤ) / 2 = (k : ℤ) := by omega
  rw [h2]
  push_cast
  ring

theorem lift_bound_of_integrality (D : Formalism.BasicNotions.D7) {Y : Pend X} (hfr : IsFractionRing X.G.O X.G.Kf) (hp : (p : X.G.Kf) ≠ 0)
    (hL : LinD X) (hF : FormB X Y) (hE : EntCondition X Y) (h4 : Conclusion4 D X)
    (hy : ∀ v, ∀ F ∈ X.Int 0, X.yv v F ∈ X.Int 0) : LowTermBound D X Y := by
  intro Gn G0n PRn S VV hG hLow hPr hS F hF
  choose u m hu hm hrest using h4
  have hπ : (algebraMap X.G.O X.G.Kf X.vp) ≠ 0 := by
    intro h0
    exact X.unif.ne_zero ((IsFractionRing.injective X.G.O X.G.Kf) (h0.trans (map_zero _).symm))
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨BB, hBB, Lv, hnd, hLv, F0, hF0, rfl⟩ := hx
    obtain ⟨F1, hF1, rfl⟩ := hF0
    let Q : ℕ → X.Pl → Bool := fun j v => decide (G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1))
    have hmemL : ∀ v, v ∈ Lv ↔ v ∈ BB := fun v => by rw [← hLv, List.mem_toFinset]
    have h1 : ∀ v ∈ Lv, ∀ j < X.mm, Gn v (j + 1) ≤ X.gv v (j + 1) := fun v hv j hj =>
      hG v (hBB ((hmemL v).1 hv)) (j + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have hmi := main_ind hfr hp hL hF hE u m hu (fun v j hj => (hrest v j hj).2.1)
      (fun v j hj => (hrest v j hj).2.2.1) (fun v j hj => (hrest v j hj).1) hy Lv hnd Gn G0n Q h1 hLow
      X.mm le_rfl F1 hF1
    have hnum : (∑ j ∈ Icc 1 X.mm, (∑ v ∈ VV, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ univ \ VV, G0n v j) -
        ∑ j ∈ range X.mm, (X.dG j : ℝ)) ≤ ∑ v ∈ VV \ BB, S v + ∑ j ∈ range X.mm, bbJ X Lv Gn G0n Q j := by
      rw [sum_Icc_shift]
      have hb := basic₂ X.mm VV BB hBB Gn G0n PRn (fun v j => X.Conclusion₂ v j) S (fun j => (X.dG j : ℝ))
        (fun j v => v ∈ Lv.filter (Q j))
        (fun j v => by simp only [List.mem_filter, hmemL, Q, decide_eq_true_eq])
        (fun v hv j hj => hPr v hv (j + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩))
        (fun v hv => by rw [← sum_Icc_shift (fun j => max (Gn v j - PRn v j - G0n v j) 0)]; exact hS v hv)
      refine hb.trans (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [bbJ, PrS]
      push_cast [PrZ_cast]
      rfl
    unfold Sys.vGe scale at hmi ⊢
    obtain ⟨I, hI, hIeq⟩ := hmi
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply] at hIeq ⊢
    rw [fold_eq hL]
    set g := ∑ j ∈ range X.mm, bbJ X Lv Gn G0n Q j with hg
    set T : ℝ := (∑ j ∈ Icc 1 X.mm, (∑ v ∈ VV, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ univ \ VV, G0n v j) -
        ∑ j ∈ range X.mm, (X.dG j : ℝ)) with hT
    have hceil : ⌈T * (X.eO : ℝ)⌉ ≤ ⌈g * (X.eO : ℝ)⌉ + ∑ v ∈ VV \ BB, ⌈S v * (X.eO : ℝ)⌉ := by
      rw [Int.ceil_le]
      push_cast
      have h8 : (0 : ℝ) ≤ (X.eO : ℝ) := Nat.cast_nonneg _
      have h6 : (∑ v ∈ VV \ BB, S v) * (X.eO : ℝ) ≤ ∑ v ∈ VV \ BB, (⌈S v * (X.eO : ℝ)⌉ : ℝ) := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun v _ => Int.le_ceil _
      have h7 := Int.le_ceil (g * (X.eO : ℝ))
      have h9 := mul_le_mul_of_nonneg_right hnum h8
      nlinarith
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = ⌈g * (X.eO : ℝ)⌉ + ∑ v ∈ VV \ BB, ⌈S v * (X.eO : ℝ)⌉ - ⌈T * (X.eO : ℝ)⌉ :=
      ⟨_, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨X.vp ^ n • I, Submodule.smul_mem _ _ hI, ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    rw [map_smul, map_smul, ← hIeq, ← algebraMap_smul X.G.Kf (X.vp ^ n) I, smul_smul, smul_smul]
    congr 1
    unfold Sys.vsc
    rw [map_pow, ← zpow_natCast, ← zpow_add₀ hπ, ← zpow_add₀ hπ, hn]
    congr 1
    ring
  | zero =>
    unfold Sys.vGe
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    unfold Sys.vGe at *
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    unfold Sys.vGe at *
    rw [← algebraMap_smul X.G.Kf a x, map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ a hx

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime]

def ea_RestSExpV (X : Sys p) : Prop :=
  DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be → ∀ (j : ℕ) (v : X.Pl),
  ∀ (K1 : Type) [Field K1] [Algebra (K0 p) K1] (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∃ u : Fin (X.G.P.n' v) → K', (∀ s, u s ∈ Rp p K' vp) ∧
      ∃ V : MvPowerSeries (X.ZA j) K', IntR (Rp p K' vp) V ∧
        atPi vp (MvPowerSeries.map (algebraMap K1 K')
          (X.ThZA K1 j (MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (-(
            ∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
              sub2 p be (MvPowerSeries.X (Sum.inl ⟨v, e⟩)) (MvPowerSeries.X (Sum.inr ⟨v, e⟩)) :
            MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p))))))) =
          expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * X.hhA K' j v u)) * V

theorem ea_restSU_of (X : Sys p) (Y : Pend X) (hE : ea_RestSExpV X) : ea_RestSU X Y := by
  intro hD hbe v j U hU K' _ _ _ _ R' vp hvp hRp hOc
  obtain ⟨u, hu, V, hV, heq⟩ := hE hD Y.be hbe j v Y.Kc K' vp hvp
  have heq' : atPi vp (MvPowerSeries.map (algebraMap Y.Kc K')
      (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v))))) =
      expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * X.hhA K' j v u)) * V := heq
  refine ⟨u, fun s => hRp (hu s), ?_⟩
  rw [ThZA_mul, map_mul, atPi_mul, heq', mul_assoc]
  have hW : IntR R' (atPi vp (MvPowerSeries.map (algebraMap Y.Kc K') (X.ThZA Y.Kc j U))) :=
    restSIntA (X := X) j Y.Kc Y.Oc U hU K' R' vp hvp hRp hOc
  have hVW := IntR_mul (fun n => hRp (hV n)) hW
  have hp0 : (p : K') ≠ 0 := by
    rw [← map_natCast (algebraMap (K0 p) K') p]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  exact inClass_of_exp hp0 (fun k => hRp (piFact (p := p) (vp := vp) (hvp := hvp) (k := k))) (X.hhA K' j v u) (hhA_const (X := X) K' j v u) hVW

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

def nd_NeedSize : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D),
    Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D, nc_Size D L Y u w hg t0 j

def PriceBound (C₀ : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    C₀ ≤ K.Pr1 → (Formalism.MainNotions.G.rG L.sc < D.R.k ∧ 2 ≤ L.sc.x) → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

theorem nc_need3_of (C₀ : ℝ) (hS : nd_NeedSize) (hP : PriceBound C₀) : nc_Need3 C₀ :=
  fun D L X Y K _ _ h3 h4 hSz hT hL u w hg hlog t0 ht0 j hj =>
    ⟨hS D L X Y hSz hT hL u w hg hlog t0 ht0 j hj, hP D L X Y K h3 h4 hSz hT hL u w hg hlog t0 ht0 j hj⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
