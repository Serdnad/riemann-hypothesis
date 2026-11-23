module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PrimeLogSum
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle012
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle121
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle163
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle231
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle160
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066

@[expose] public section

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem sum_padicVal_log {n : ℕ} (hn : n ≠ 0) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hsub : n.primeFactors ⊆ S) :
    ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p = Real.log n := by
  have h1 : ∑ p ∈ n.primeFactors, (padicValNat p n : ℝ) * Real.log p =
      ∑ p ∈ S, (padicValNat p n : ℝ) * Real.log p := by
    refine Finset.sum_subset hsub fun p hpS hp => ?_
    have hpp := hS p hpS
    have hnd : ¬ p ∣ n := fun hd => hp (Nat.mem_primeFactors.2 ⟨hpp, hd, hn⟩)
    simp [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hnd]
  rw [← h1]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization, Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Nat.cast_pow, Real.log_pow, Nat.factorization_def n (Nat.prime_of_mem_primeFactors hp),
      Nat.padicValNat_def]
  · intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).pos
    positivity

theorem log_hostRd (E : Type) [Field E] [NumberField E] :
    Real.log (hostRd E) = Real.log ((discr E).natAbs : ℝ) / (Module.finrank ℚ E : ℝ) := by
  have hd : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero E)
  have he : |(discr E : ℝ)| = ((discr E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hostRd, Real.log_rpow hd, he]
  ring

theorem costTwo_bound (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H)
    (B : ℝ) (hB : 128 ≤ B)
    (hbad : (Nat.primeFactors (2 * (discr E).natAbs) ∪ l.M'.primeFactors).card ≤ ⌊B⌋₊) :
    0 ≤ costTwo l B ∧ costTwo l B ≤ 60 * (Real.log B + Real.log (hostRd E)) := by
  classical
  set N : ℕ := ⌊B⌋₊ with hN
  set P : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime with hP
  set Q : Finset ℕ := Nat.primeFactors (2 * (discr E).natAbs) ∪ l.M'.primeFactors with hQ
  set n : ℝ := (Module.finrank ℚ E : ℝ) with hn
  set d : ℕ := (discr E).natAbs with hd
  have hd0 : d ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hn0 : 0 < n := by
    rw [hn]; exact_mod_cast Module.finrank_pos
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => by
    rcases Finset.mem_union.1 hp with h | h <;> exact Nat.prime_of_mem_primeFactors h
  have hSp : ∀ p ∈ P ∪ Q, p.Prime := fun p hp => by
    rcases Finset.mem_union.1 hp with h | h
    · exact hPp p h
    · exact hQp p h
  have hcost : costTwo l B = ∑ p ∈ P ∪ Q, exTwo E p * Real.log p := by
    rw [costTwo, GlobalTheory.CompHt.htPrimes_eq, finsum_mem_coe_finset]
  have hterm : ∀ p ∈ P ∪ Q, exTwo E p * Real.log p =
      Real.log p / ((p : ℝ) - 1) + 40 / n * ((padicValNat p d : ℝ) * Real.log p)
        + (if p = 2 then Real.log 2 else 0) := by
    intro p _
    rw [exTwo, GlobalTheory.CovHt.htEx, ← hd, ← hn]
    by_cases h2 : p = 2
    · subst h2; simp only [if_true]; ring_nf
    · simp only [h2, if_false]; ring
  have ha0 : ∀ p : ℕ, p.Prime → 0 ≤ Real.log p / ((p : ℝ) - 1) := fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact div_nonneg (Real.log_natCast_nonneg p) (by linarith)

  have hA : ∑ p ∈ P ∪ Q, Real.log p / ((p : ℝ) - 1) ≤ Real.log N + 2.2 + (Real.log N + 1) := by
    have hN128 : 128 ≤ N := by
      rw [hN]; exact Nat.le_floor (by exact_mod_cast hB)
    have hNr : (128 : ℝ) ≤ N := by exact_mod_cast hN128
    have h3 : ∑ p ∈ P, Real.log p / ((p : ℝ) - 1) ≤ Real.log N + 2.2 := by
      have hPe : P = (Finset.Iic N).filter Nat.Prime := by
        ext p; simp [hP]
      rw [hPe]; exact ReciprocityTheory.ChartRestriction.G.H1.primeLogSum_nat N (by omega)
    have hL1 : 1 ≤ Real.log ((N : ℝ) + 1) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [Real.exp_one_lt_d9]
    have hL2 : Real.log ((N : ℝ) + 1) ≤ Real.log N + 1 := by
      have h := Real.log_le_sub_one_of_pos (show 0 < ((N : ℝ) + 1) / N by positivity)
      rw [Real.log_div (by linarith) (by linarith)] at h
      have : ((N : ℝ) + 1) / N ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    have h4 : ∑ p ∈ Q \ P, Real.log p / ((p : ℝ) - 1) ≤ Real.log N + 1 := by
      calc ∑ p ∈ Q \ P, Real.log p / ((p : ℝ) - 1) ≤ ∑ _p ∈ Q \ P, Real.log ((N : ℝ) + 1) / N := by
            refine Finset.sum_le_sum fun p hp => ?_
            obtain ⟨hq, hnp⟩ := Finset.mem_sdiff.1 hp
            have hp1 : N + 1 ≤ p := by
              by_contra hc
              exact hnp (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hQp p hq⟩)
            have hp2 : (N : ℝ) + 1 ≤ p := by exact_mod_cast hp1
            have h := Real.log_le_sub_one_of_pos (show 0 < (p : ℝ) / ((N : ℝ) + 1) from div_pos (by linarith) (by linarith))
            rw [Real.log_div (by linarith) (by linarith)] at h
            have h5 : (N : ℝ) * ((p : ℝ) / ((N : ℝ) + 1) - 1) ≤ p - (N + 1) := by
              have e : (p : ℝ) / ((N : ℝ) + 1) - 1 = (p - (N + 1)) / ((N : ℝ) + 1) := by field_simp
              rw [e, ← mul_div_assoc, div_le_iff₀ (by linarith)]
              nlinarith
            rw [div_le_div_iff₀ (by linarith) (by linarith)]
            nlinarith [mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ N by linarith),
              mul_le_mul_of_nonneg_left hL1 (show (0 : ℝ) ≤ p - (N + 1) by linarith)]
        _ = (Q \ P).card * (Real.log ((N : ℝ) + 1) / N) := by simp
        _ ≤ N * (Real.log ((N : ℝ) + 1) / N) := by
            have : (((Q \ P).card : ℕ) : ℝ) ≤ N := by exact_mod_cast (Finset.card_le_card Finset.sdiff_subset).trans hbad
            exact mul_le_mul_of_nonneg_right this (div_nonneg (by linarith) (by linarith))
        _ = Real.log ((N : ℝ) + 1) := by field_simp
        _ ≤ Real.log N + 1 := hL2
    rw [← Finset.union_sdiff_self_eq_union, Finset.sum_union Finset.disjoint_sdiff]
    linarith

  have hdsub : d.primeFactors ⊆ P ∪ Q := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdv := Nat.dvd_of_mem_primeFactors hp
    refine Finset.mem_union_right _ (Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨hpp, ?_, ?_⟩))
    · exact Dvd.dvd.mul_left hdv 2
    · exact mul_ne_zero two_ne_zero hd0
  have hC : ∑ p ∈ P ∪ Q, 40 / n * ((padicValNat p d : ℝ) * Real.log p) = 40 * Real.log (hostRd E) := by
    rw [← Finset.mul_sum, sum_padicVal_log hd0 hSp hdsub, log_hostRd]
    ring

  have hT0 : 0 ≤ ∑ p ∈ P ∪ Q, (if p = 2 then Real.log 2 else 0) :=
    Finset.sum_nonneg fun p _ => by
      split_ifs
      · exact Real.log_nonneg (by norm_num)
      · exact le_rfl
  have hT : ∑ p ∈ P ∪ Q, (if p = 2 then Real.log 2 else 0) ≤ Real.log 2 := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact Real.log_nonneg (by norm_num)
  have hsum : costTwo l B = ∑ p ∈ P ∪ Q, Real.log p / ((p : ℝ) - 1) + 40 * Real.log (hostRd E)
      + ∑ p ∈ P ∪ Q, (if p = 2 then Real.log 2 else 0) := by
    rw [hcost, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib, hC]
  have hL : 0 ≤ Real.log (hostRd E) := by
    rw [log_hostRd]
    exact div_nonneg (Real.log_natCast_nonneg _) hn0.le
  have hA0 : 0 ≤ ∑ p ∈ P ∪ Q, Real.log p / ((p : ℝ) - 1) :=
    Finset.sum_nonneg fun p hp => ha0 p (hSp p hp)
  have hNB : Real.log N ≤ Real.log B := by
    have hN1 : 1 ≤ N := by
      rw [hN]; exact Nat.le_floor (by norm_num; linarith)
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    exact Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have hB7 : 7 * Real.log 2 ≤ Real.log B := by
    have h : Real.log ((2 : ℝ) ^ 7) ≤ Real.log B := Real.log_le_log (by norm_num) (by norm_num; linarith)
    rw [Real.log_pow] at h
    exact_mod_cast h
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  refine ⟨?_, ?_⟩
  · rw [hsum]; linarith
  · rw [hsum]; linarith

end GlobalTheory.CompanionTheory.Ar.Plug
end

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem norm_wt_eq_iSup {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Top.Wt Ψ N) :
    ‖lam‖ = ⨆ k : Ψ × Fin N, |lam k.1 k.2| := by
  apply le_antisymm
  · have h0 : 0 ≤ ⨆ k : Ψ × Fin N, |lam k.1 k.2| := Real.iSup_nonneg fun _ => abs_nonneg _
    refine (pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact le_ciSup (f := fun k : Ψ × Fin N => |lam k.1 k.2|) (Set.finite_range _).bddAbove (τ, i)
  · refine Real.iSup_le (fun k => ?_) (norm_nonneg _)
    calc |lam k.1 k.2| = ‖lam k.1 k.2‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖lam k.1‖ := norm_le_pi_norm _ _
      _ ≤ ‖lam‖ := norm_le_pi_norm _ _

theorem flagDeg_eq_const_mul_vdm {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (lam : Top.Wt Ψ N) :
    Top.flagDeg lam = (((Top.dimFl Ψ N).factorial : ℝ) *
      ∏ _τ : Ψ, ∏ i : Fin N, ∏ k : Fin N, (if i < k then ((k : ℝ) - (i : ℝ))⁻¹ else 1)) *
        GlobalTheory.CompHt.vdm lam := by
  rw [(Top.flagDeg_eq_weyl Ψ N lam).1, mul_assoc, GlobalTheory.CompHt.vdm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hI : Finset.Ioi i = Finset.univ.filter (fun k => i < k) := by ext; simp
  rw [hI, Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs
  · rw [div_eq_inv_mul]
  · simp

theorem flagDeg_mul_vdm {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (lam mu : Top.Wt Ψ N) :
    Top.flagDeg lam * GlobalTheory.CompHt.vdm mu = Top.flagDeg mu * GlobalTheory.CompHt.vdm lam := by
  rw [flagDeg_eq_const_mul_vdm lam, flagDeg_eq_const_mul_vdm mu]
  ring

theorem vdm_cast {ι : Type} (i₁ i₂ : Fintype ι) {N : ℕ} (w : ι → Fin N → ℤ) :
    ((@GlobalTheory.CompHt.vdm ι i₁ N ℤ _ w : ℤ) : ℝ) = @GlobalTheory.CompHt.vdm ι i₂ N ℝ _ fun τ i => (w τ i : ℝ) := by
  obtain rfl := Subsingleton.elim i₁ i₂
  simp [GlobalTheory.CompHt.vdm]

section Entries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem towerWt_wtOf (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) :
    towerWt Dw (GlobalTheory.AllWt.wtOf Dw u 0).1 = reW u := by
  funext τ n
  simp only [towerWt, reW]
  split_ifs with hn
  · rw [GlobalTheory.AllWt.wtOf_big (Dw := Dw) u 0 τ n hn]
    simp
  · have hn' := n.isLt
    have hq : Dw.p + Dw.q - 1 - (n : ℕ) < Dw.q := by omega
    rw [GlobalTheory.AllWt.wtOf_small (Dw := Dw) u 0 τ _ hq]
    have hf : (⟨Dw.p + (Dw.q - 1 - (Dw.p + Dw.q - 1 - (n : ℕ))), by omega⟩ : Fin (Dw.p + Dw.q)) = n :=
      Fin.ext (by simp only; omega)
    rw [hf]
    simp

theorem gap_reW {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (τ : CMType H) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) :
    Top.gap Dw.p (reW u) τ = (u τ ⟨Dw.p - 1, by omega⟩ : ℝ) - u τ ⟨Dw.p, by omega⟩ := by
  have h1 : Dw.p - 1 < Dw.p + Dw.q := by omega
  have h2 : Dw.p < Dw.p + Dw.q := by omega
  simp only [Top.gap, Top.ent, dif_pos h1, dif_pos h2, reW]

theorem regDominant_reW {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (h : ∀ τ, StrictAnti (u τ)) :
    Top.RegDominant (reW u) := fun τ _ _ hab => by
  simp only [reW]
  exact_mod_cast h τ hab

theorem weightHyp_reW_one {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q)
    (h : ∀ τ, StrictAnti (u τ)) : Top.WeightHyp Dw.p (reW u) 1 := by
  refine ⟨one_pos, regDominant_reW u h, fun τ => ?_, fun τ a b _ hab => ?_⟩
  · rw [gap_reW u τ hp hq]
    have hlt : (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) < ⟨Dw.p, by omega⟩ :=
      Fin.mk_lt_mk.2 (by omega)
    have h1 := h τ hlt
    have h2 : u τ ⟨Dw.p, by omega⟩ + 1 ≤ u τ ⟨Dw.p - 1, by omega⟩ := h1
    have h3 : ((u τ ⟨Dw.p, by omega⟩ : ℝ)) + 1 ≤ u τ ⟨Dw.p - 1, by omega⟩ := by exact_mod_cast h2
    linarith
  · have hne : u τ a - u τ b ≠ 0 := sub_ne_zero.2 fun e => hab ((h τ).injective e)
    have h1 : (1 : ℤ) ≤ |u τ a - u τ b| := Int.one_le_abs hne
    simp only [reW]
    exact_mod_cast h1

theorem weightHyp_reW_of_wtGap {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ) (hq : 1 ≤ Dw.q)
    (hqp : Dw.q < Dw.p) (hg : GlobalTheory.CovHt.WtGap u g) : Top.WeightHyp Dw.p (reW u) g := by
  obtain ⟨hg0, hanti, hdist⟩ := hg
  have hp : 1 ≤ Dw.p := by omega
  refine ⟨hg0, regDominant_reW u hanti, fun τ => ?_, fun τ a b ha hab => ?_⟩
  · rw [gap_reW u τ hp hq]
    have hlt : (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) < ⟨Dw.p, by omega⟩ :=
      Fin.mk_lt_mk.2 (by omega)
    have h1 := hdist τ ⟨Dw.p, by omega⟩ ⟨Dw.p - 1, by omega⟩ (le_refl _) (ne_of_gt hlt)
    have h2 : (u τ ⟨Dw.p, by omega⟩ : ℝ) < u τ ⟨Dw.p - 1, by omega⟩ := by
      exact_mod_cast hanti τ hlt
    rw [abs_sub_comm, abs_of_pos (sub_pos.2 h2)] at h1
    exact h1
  · have ha' : Dw.p ≤ (a : ℕ) := by
      have hn : ¬ Dw.p ≤ Dw.p + Dw.q - Dw.p := by omega
      simpa only [Top.InSmall, if_neg hn] using ha
    exact hdist τ a b ha' hab

theorem bound_eq_root_weight_bound {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ) :
    GlobalTheory.CovHt.bndB u g = Top.bigB0 (reW u) g := by
  simp only [GlobalTheory.CovHt.bndB, Top.bigB0, norm_wt_eq_iSup, reW]
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]

theorem covHt_l1_eq_l1_reW {Dw : Datum H} (u : GlobalTheory.AllWt.Weight Dw) : GlobalTheory.CovHt.l1 u = Top.l1 (reW u) := by
  unfold GlobalTheory.CovHt.l1 Top.l1 reW
  congr!

end Entries

theorem integer_weights_vocab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) [DecidableEq (CMType H)] (u : GlobalTheory.AllWt.Weight Dw), towerWt Dw (GlobalTheory.AllWt.wtOf Dw u 0).1 = reW u ∧ (GlobalTheory.AllWt.wtOf Dw u 0) = ((GlobalTheory.AllWt.wtOf Dw u 0).1, 0) ∧ (∀ n : ℕ, n • (GlobalTheory.AllWt.wtOf Dw u 0) = GlobalTheory.AllWt.wtOf Dw (n • u) 0) ∧ (∀ j, (nOf u j : ℝ) = RM.coef (reW u) 0 j) ∧ GlobalTheory.CovHt.l1 u = Top.l1 (reW u) ∧ GlobalTheory.CompHt.dimFlag Dw = (Top.dimFl (CMType H) (Dw.p + Dw.q)) ∧ (∀ v : GlobalTheory.AllWt.Weight Dw, Top.flagDeg (reW u) * ((GlobalTheory.CompHt.vdm v : ℤ) : ℝ) = Top.flagDeg (reW v) * ((GlobalTheory.CompHt.vdm u : ℤ) : ℝ)) ∧ (1 ≤ Dw.p → 1 ≤ Dw.q → (∀ τ, StrictAnti (u τ)) → Top.WeightHyp Dw.p (reW u) 1) ∧ ∀ g : ℝ, GlobalTheory.CovHt.bndB u g = Top.bigB0 (reW u) g ∧ (1 ≤ Dw.q → Dw.q < Dw.p → GlobalTheory.CovHt.WtGap u g → Top.WeightHyp Dw.p (reW u) g) := by
  intro E _ _ _ H Dw l Xo c RM _ u
  refine ⟨towerWt_wtOf Dw u, ?_, fun n => ?_, ?_, covHt_l1_eq_l1_reW u, ?_, fun v => ?_, weightHyp_reW_one u,
    fun g => ⟨bound_eq_root_weight_bound u g, fun hq hqp hg => weightHyp_reW_of_wtGap u g hq hqp hg⟩⟩
  · exact Prod.ext rfl (by simp [GlobalTheory.AllWt.wtOf_snd])
  · rw [GlobalTheory.CompHt.nsmul_wtOf, smul_zero]
  · rintro (_ | r)
    · simp [nOf, Top.RootModel.coef]
    · simp [nOf, Top.RootModel.coef, reW]
  · simp only [GlobalTheory.CompHt.dimFlag, Formalism.DegreeFormula.dimFl, Top.dimFl]
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  · have e : ∀ w : GlobalTheory.AllWt.Weight Dw, ((GlobalTheory.CompHt.vdm w : ℤ) : ℝ) = GlobalTheory.CompHt.vdm (reW w) :=
      fun w => vdm_cast _ _ w
    rw [e, e]
    exact flagDeg_mul_vdm (reW u) (reW v)

end GlobalTheory.CompanionTheory.Ar.Plug
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.StratOpen

theorem charZero_of_point {k : Type} [Field k] (x : Sp k ⟶ Sp ℚ) : CharZero k :=
  (RingHom.charZero_iff (Spec.preimage x).hom.injective).1 inferInstance

theorem core (hE : GlobalTheory.Published.SemiAbelianHomExtension) (Z : Scheme.{0}) [IsIntegral Z] [AlgebraicGeometry.IsNoetherian Z]
    (s : Z ⟶ Sp ℚ) (G : Over Z) [GrpObj G] (hG : IsSemiAbelian G) (g : ℕ) (hg : SmoothOfRelativeDimension g G.hom)
    (Z' : Scheme.{0}) [IsIntegral Z'] (π : Z' ⟶ Z) (hfin : IsFinite π) (hsurj : Surjective π) (hnorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z')
    (L' : Type) [Field L'] (j : Sp L' ⟶ Z') (hj : GlobalTheory.IsGenericPointHom j)
    (τ : TorusExtension ((Over.pullback (j ≫ π)).obj G)) (m : ℕ) (P : Fin m → (Over.mk (j ≫ π) ⟶ G))
    (hPi : Function.Injective P) (hP2 : ∀ i, P i ^ 2 = 1)
    (hcount : letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X = 2 ^ (2 * g)) :
    ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (G' : Over Z') (_ : GrpObj G') (φ : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (u : splitTorus Z' X ⟶ G') (U : Z.Opens), IsFinite π ∧ Surjective π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsGrpPullback G' G π φ ∧ IsMonHom u ∧ (U : Set Z).Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ (x ≫ π) ⁻¹ᵁ U → (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) ∧ ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ : TorusExtension Gk, letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X, (t ≫ u).left = p.left ≫ ψ := by
  have hsm := hG.smooth
  have hsep := hG.separated
  have hG' : IsSemiAbelian ((Over.pullback π).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hG.comm
      infer_instance
    · have := hG.smooth
      change Smooth (pullback.snd G.hom π)
      infer_instance
    · have := hG.separated
      change IsSeparated (pullback.snd G.hom π)
      infer_instance
    · have := hG.quasiCompact
      change QuasiCompact (pullback.snd G.hom π)
      infer_instance
    · have := hG.geomConnected
      change GeometricallyConnected (pullback.snd G.hom π)
      infer_instance
    · intro Ω _ _ q
      obtain ⟨E⟩ := hG.fibres Ω (q ≫ π)
      exact ⟨torusExtOfIso (pullCompIso q π G) E⟩
  have hsep' := hG'.separated
  have hLN : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian π
  have hCS : CompactSpace Z' := QuasiCompact.compactSpace_of_compactSpace π
  have hN' : AlgebraicGeometry.IsNoetherian Z' := {}
  let τ' : TorusExtension ((Over.pullback j).obj ((Over.pullback π).obj G)) := torusExtOfIso (pullCompIso j π G) τ
  letI := τ'.addCommGroup
  haveI := τ'.free
  haveI := τ'.finite
  obtain ⟨u, hu, hmono⟩ := GlobalTheory.T.torus_extension_split_map hE Z' hnorm ((Over.pullback π).obj G) hG' L' j hj τ'
  obtain ⟨V₁, hV₁, hC⟩ := GlobalTheory.T.torus_kernel_trivial_open Z' ((Over.pullback π).obj G) τ'.X u L' j hj hmono
  obtain ⟨V₂, hV₂, hD⟩ := GlobalTheory.T.two_torsion_spread_open Z' Z π G L' j hj m P hPi hP2
  have hVne : ((V₁ ⊓ V₂ : Z'.Opens) : Set Z').Nonempty :=
    nonempty_preirreducible_inter V₁.isOpen V₂.isOpen hV₁ hV₂
  obtain ⟨U, hU, hUV⟩ := GlobalTheory.T.finite_surjective_open_image Z Z' π hfin hsurj (V₁ ⊓ V₂) hVne
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd hcount.symm (by simp)
    · exact h
  refine ⟨Z', inferInstance, π, (Over.pullback π).obj G, inferInstance, pullback.fst G.hom π, τ'.X, τ'.addCommGroup, τ'.free, τ'.finite, u, U, hfin, hsurj, hnorm, isGrpPullback_pullback G π, hu, hU, ?_⟩
  intro k _ x hx
  have hxV : ∀ W : Z'.Opens, V₁ ⊓ V₂ ≤ W → ⊤ ≤ x ⁻¹ᵁ W := fun W hW y _ => hW (hUV (hx trivial))
  have mono : ∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' τ'.X), t ≫ u = 1 → t = 1 := by
    intro A _ g t ht
    refine hC A (spMap g ≫ x) (fun y _ => ?_) t ht
    have h1 := hxV V₁ inf_le_left (show (spMap g) y ∈ (⊤ : (Sp k).Opens) from trivial)
    simpa using h1
  refine ⟨mono, ?_⟩
  intro Gk _ ψ hψ τk
  letI := τk.grpB
  letI := τk.addCommGroup
  haveI := τk.free
  haveI := τk.finite
  obtain ⟨Q, hQi, hQ2⟩ := hD k x (hxV V₂ inf_le_right)
  have h2 : ((2 : ℕ) : k) ≠ 0 := by
    haveI : CharZero k := charZero_of_point (x ≫ π ≫ s)
    exact Nat.cast_ne_zero.2 two_ne_zero
  have hle := GlobalTheory.T.two_torsion_card_bound Z G hG g hg k h2 (x ≫ π) Gk (ψ ≫ pullback.fst G.hom π) (hψ.comp (isGrpPullback_pullback G π)) τk m Q hQi hQ2
  have hrk : Module.finrank ℤ τk.X ≤ Module.finrank ℤ τ'.X := by
    have h3 : m * 2 ^ Module.finrank ℤ τk.X ≤ m * 2 ^ Module.finrank ℤ τ'.X := hle.trans hcount.ge
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (Nat.le_of_mul_le_mul_left h3 hm)
  intro A _ gg p
  exact GlobalTheory.T.torus_extension_rank_bound Z' ((Over.pullback π).obj G) τ'.X u k x mono Gk ψ hψ τk hrk A gg p

theorem strat_open : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (G : Over Z) [GrpObj G], IsSemiAbelian G → ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (G' : Over Z') (_ : GrpObj G') (φ : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (u : splitTorus Z' X ⟶ G') (U : Z.Opens), IsFinite π ∧ Surjective π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsGrpPullback G' G π φ ∧ IsMonHom u ∧ (U : Set Z).Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ (x ≫ π) ⁻¹ᵁ U → (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) ∧ ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ : TorusExtension Gk, letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X, (t ≫ u).left = p.left ≫ ψ := by
  intro hE Z _ s _ _ G _ hG
  have hLN : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  have hCS : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  have hN : AlgebraicGeometry.IsNoetherian Z := {}
  have hsm := hG.smooth
  have hsep := hG.separated
  have hfq := hG.quasiCompact
  let z : Sp Z.functionField ⟶ Z := Z.fromSpecStalk (genericPoint Z)
  have hz : GlobalTheory.IsGenericPointHom z := GlobalTheory.IsGenericPointHom.fromSpecStalk Z
  haveI : CharZero Z.functionField := charZero_of_point (z ≫ s)
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.smoothGrp_relDim Z Z.functionField z G (fun q => by
    have : genPt z = genericPoint Z := by
      have := hz.range_eq
      have h2 : genPt z ∈ Set.range z := ⟨_, rfl⟩
      rw [this] at h2
      exact h2
    rw [this]
    exact genericPoint_specializes q)
  obtain ⟨L', _, _, hfd, hB⟩ := GlobalTheory.T.torus_extension_two_torsion Z G hG g hg Z.functionField z
  obtain ⟨Z', _, π, j, hfin, hsurj, hnorm, hj, hjπ⟩ := GlobalTheory.T.finite_normal_cover_generic_point Z s Z.functionField z hz L'
  rw [← hjπ] at hB
  obtain ⟨τ, m, P, hPi, hP2, hcount⟩ := hB
  exact core hE Z s G hG g hg Z' π hfin hsurj hnorm L' j hj τ m P hPi hP2 hcount

end GlobalTheory.CompanionTheory.Ar.StratOpen
end
