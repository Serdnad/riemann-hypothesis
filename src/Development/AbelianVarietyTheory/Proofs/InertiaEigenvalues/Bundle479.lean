module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle007
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle075
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle203
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle231
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle225
public import GroundTheory.LocalFields.HerbrandFunction
public import GroundTheory.LocalFields.SeparableClosure
public import Mathlib.FieldTheory.Galois.Abelian
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle246
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle471
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle450
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle079
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle238
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle265
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle125
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle288
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle453
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompletionFrameOfLattice
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultisetBaseLatticeEqJumpsMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaReductionBaseLatticeBounds
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle472
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Algebra.Nonarchimedean.Completion
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem GlobalTheory.oneVarCount_onto_independentZeros : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 1 ≤ h → μ ≠ 0 → ∃ τ : ℝ, (∀ t : ℂ_[l], ‖t‖ ≤ τ → ∃ y : Fl l, ‖sh y‖ ≤ ‖(l : ℂ_[l])‖ ∧ ‖∑ i : Fin h, μ i * lam h i y - t‖ ≤ ‖(l : ℂ_[l])‖ * τ) ∧ ∃ x : Fin h → Fl l, (∀ a, ‖sh (x a)‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ a, ‖∑ i : Fin h, μ i * lam h i (x a)‖ ≤ ‖(l : ℂ_[l])‖ * τ) ∧ ∀ n : Fin h → ℕ, ‖sh (∑ a, n a • x a)‖ ≤ ‖(l : ℂ_[l])‖ ^ l ^ h → ∀ a, l ∣ n a := by
  intro l _ h μ hh hμ
  obtain ⟨sh1, sh0, shmul, shpow, shle, shsurj, shadd, shneg⟩ := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hlD : ∀ D : ℕ, l ^ D ≠ 0 := fun D => (pow_pos (Fact.out : l.Prime).pos D).ne'
  obtain ⟨σ, hσ⟩ := shsurj (l : ℂ_[l]) hl1.le
  obtain ⟨t, D, E, M, a, ρ, ht, hME, ha, haN, hρl, hρ1, hρD, haM, hak, hpoly⟩ :=
    GlobalTheory.T.untiltFrobeniusLaurentSeries_eq_polynomial_mod_prime l h μ σ hh hμ hσ
  have hshv : ∀ u : Fl l, ‖sh (σ * u ^ l ^ D)‖ ≤ ‖(l : ℂ_[l])‖ := by
    intro u
    rw [shmul, shpow, hσ, norm_mul, norm_pow]
    calc ‖(l : ℂ_[l])‖ * ‖sh u‖ ^ l ^ D ≤ ‖(l : ℂ_[l])‖ * 1 := by
          gcongr; exact pow_le_one₀ (norm_nonneg _) (shle u)
      _ = _ := mul_one _
  refine ⟨‖t‖, ?_, ?_⟩
  · intro t' ht'
    have hb : ‖t' / t‖ ≤ 1 := by
      rw [norm_div]; exact div_le_one_of_le₀ ht' (norm_nonneg _)
    obtain ⟨W, hW, hPW⟩ := GlobalTheory.T.exists_root_additive_poly_eq_of_unit_coeff l E (M + h) a hME ha haN (t' / t) hb
    obtain ⟨u, hu⟩ := shsurj W hW
    refine ⟨σ * u ^ l ^ D, hshv u, ?_⟩
    have key := hpoly u
    have e : t * (t' / t) = t' := by field_simp
    rw [hu, hPW, e] at key
    exact key
  · have hρ0 : 0 < ρ := lt_of_lt_of_le hl0 hρl
    obtain ⟨Z, hZc, hZ, hsep⟩ := GlobalTheory.T.exists_separated_roots_additive_poly l E M h a ρ hME ha haN hρ0 hρ1 haM hak
    choose! u hu using fun (W : ℂ_[l]) (hW : ‖W‖ ≤ 1) => shsurj W hW
    let v : ℂ_[l] → Fl l := fun W => σ * u W ^ l ^ D
    let K' : AddSubgroup (Fl l) :=
      { carrier := {x | ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ ^ l ^ h}
        zero_mem' := by
          show ‖sh (0 : Fl l)‖ ≤ _
          rw [sh0, norm_zero]; positivity
        add_mem' := by
          intro x y hx hy
          exact (GlobalTheory.T.tiltUntilt_add_estimate_le l _ x y hx hy).2
        neg_mem' := by
          intro x hx
          show ‖sh (-x)‖ ≤ _
          rw [shneg]; exact hx }
    have hchar : ∀ x : Fl l, l • x = 0 := fun x => by
      rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    have hsepv : ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → v W - v W' ∉ K' := by
      intro W hW W' hW' hne hmem
      have hsepW := hsep W hW W' hW' hne
      have hvd : v W - v W' = σ * (u W - u W') ^ l ^ D := by
        simp only [v]; rw [sub_pow_char_pow, mul_sub]
      have hmem' : ‖sh (v W - v W')‖ ≤ ‖(l : ℂ_[l])‖ ^ l ^ h := hmem
      rw [hvd, shmul, shpow, hσ, norm_mul, norm_pow, ← hρD] at hmem'
      have hd : ‖sh (u W - u W')‖ ≤ ρ := by
        by_contra hcon
        push_neg at hcon
        have h1 : ρ ^ l ^ D < ‖sh (u W - u W')‖ ^ l ^ D := pow_lt_pow_left₀ hcon hρ0.le (hlD D)
        have h2 := mul_lt_mul_of_pos_left h1 hl0
        linarith
      have h2 := shadd (u W - u W') (u W')
      rw [sub_add_cancel, hu W (hZ W hW).1, hu W' (hZ W' hW').1] at h2
      have e3 : W - W' = (W - sh (u W - u W') - W') + sh (u W - u W') := by ring
      have h3 : ‖W - W'‖ ≤ max ‖W - sh (u W - u W') - W'‖ ‖sh (u W - u W')‖ := by
        rw [e3]; exact IsUltrametricDist.norm_add_le_max _ _
      have h4 : ‖W - W'‖ ≤ ρ := h3.trans (max_le (h2.trans hρl) hd)
      linarith
    obtain ⟨x, hxZ, hx⟩ := GlobalTheory.T.exists_independent_mod_prime_of_pow_le_card l (Fl l) ℂ_[l] K' h Z v hchar hZc hsepv
    refine ⟨fun b => v (x b), fun b => hshv (u (x b)), ?_, fun n hn => hx n hn⟩
    intro b
    have key := hpoly (u (x b))
    rw [hu _ (hZ _ (hxZ b)).1, (hZ _ (hxZ b)).2, mul_zero, sub_zero] at key
    exact key
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_frobeniusSeries_acris_untilt : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (x : Fl l), 2 ≤ h → ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = lam h j x := by
  first | exact @GlobalTheory.PSer.series_acris | exact GlobalTheory.PSer.series_acris | (intros; apply GlobalTheory.PSer.series_acris <;> assumption)
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem lam_add_sub_le : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (x y : Fl l), 1 ≤ h → r < 1 → ‖sh x‖ ≤ r → ‖sh y‖ ≤ r → ‖lam h j (x + y) - lam h j x - lam h j y‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
  intro l _ h j r x y hh hr hx hy
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) hx
  have hxy : ‖sh (x + y)‖ ≤ r := (GlobalTheory.T.tiltUntilt_add_estimate_le l r x y hx hy).2
  have sx := (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r x hh hr hx).1
  have sy := (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r y hh hr hy).1
  have sxy := (GlobalTheory.T.untiltFrobeniusLaurentSeries_hasSum_bound_frobenius l h j r (x + y) hh hr hxy).1
  have hs := (sxy.sub sx).sub sy
  have hg := (GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j r hh hr0 hr).1
  have hpw := GlobalTheory.T.tiltFrobeniusIntegerPower_laws l
  have hε : 0 ≤ ‖(l : ℂ_[l])‖ * gam l h j r :=
    mul_nonneg (norm_nonneg _) (GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j r hh hr0 hr).2.2.1
  have key := GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le ℂ_[l] ℤ _ _ ∅ _ hε hs (by
    intro n _
    set k : ℤ := n * h + j
    beta_reduce
    rw [hpw.1 k x y]
    have e : (l : ℂ_[l]) ^ (-n) * sh (pw k x + pw k y) - (l : ℂ_[l]) ^ (-n) * sh (pw k x)
        - (l : ℂ_[l]) ^ (-n) * sh (pw k y)
        = (l : ℂ_[l]) ^ (-n) * (sh (pw k x + pw k y) - sh (pw k x) - sh (pw k y)) := by ring
    rw [e, norm_mul, norm_zpow]
    have hl0 : 0 ≤ (l : ℝ) ^ k := zpow_nonneg (Nat.cast_nonneg _) _
    have bx : ‖sh (pw k x)‖ ≤ r ^ ((l : ℝ) ^ k) := by
      rw [hpw.2.2.2.2.2.2 k x]; exact Real.rpow_le_rpow (norm_nonneg _) hx hl0
    have by' : ‖sh (pw k y)‖ ≤ r ^ ((l : ℝ) ^ k) := by
      rw [hpw.2.2.2.2.2.2 k y]; exact Real.rpow_le_rpow (norm_nonneg _) hy hl0
    have ha := (GlobalTheory.T.tiltUntilt_add_estimate_le l _ (pw k x) (pw k y) bx by').1
    have hn : 0 ≤ ‖(l : ℂ_[l])‖ ^ (-n) := zpow_nonneg (norm_nonneg _) _
    calc ‖(l : ℂ_[l])‖ ^ (-n) * ‖sh (pw k x + pw k y) - sh (pw k x) - sh (pw k y)‖
        ≤ ‖(l : ℂ_[l])‖ ^ (-n) * (‖(l : ℂ_[l])‖ * r ^ ((l : ℝ) ^ k)) :=
          mul_le_mul_of_nonneg_left ha hn
      _ = ‖(l : ℂ_[l])‖ * (‖(l : ℂ_[l])‖ ^ (-n) * r ^ ((l : ℝ) ^ k)) := by ring
      _ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := mul_le_mul_of_nonneg_left (hg n) (norm_nonneg _))
  simpa using key

end GlobalTheory.PSer
end

section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory

theorem untilt_sum_sub_le : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (s : Finset ι) (r : ℝ) (x : ι → Fl l), 0 ≤ r → (∀ i ∈ s, ‖sh (x i)‖ ≤ r) → ‖sh (∑ i ∈ s, x i) - ∑ i ∈ s, sh (x i)‖ ≤ ‖(l : ℂ_[l])‖ * r ∧ ‖sh (∑ i ∈ s, x i)‖ ≤ r := by
  intro l _ ι s r x hr hs
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : sh (0 : Fl l) = 0 := by
      have h : (0 : Fl l).untilt = 0 := Perfection.teichmuller_zero
      simp only [sh, h]; rfl
    simp only [Finset.sum_empty, h0, sub_zero, norm_zero]
    exact ⟨mul_nonneg (norm_nonneg _) hr, hr⟩
  | insert a t ha ih =>
    have ih' := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
    have hxa : ‖sh (x a)‖ ≤ r := hs a (Finset.mem_insert_self a t)
    obtain ⟨h1, h2⟩ := GlobalTheory.T.tiltUntilt_add_estimate_le l r (x a) (∑ i ∈ t, x i) hxa ih'.2
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨?_, h2⟩
    have : sh (x a + ∑ i ∈ t, x i) - (sh (x a) + ∑ i ∈ t, sh (x i)) =
        (sh (x a + ∑ i ∈ t, x i) - sh (x a) - sh (∑ i ∈ t, x i)) + (sh (∑ i ∈ t, x i) - ∑ i ∈ t, sh (x i)) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ih'.1)

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.pow_mem_upperRamificationGroup_abelian_real : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e : ℕ) (v : ℝ), 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M v, σ ^ p ∈ upperRamificationGroup F ↥M (min (2 * v) (v + e)) := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_real | exact GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_real | (intros; apply GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_real <;> assumption)
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ConcaveOn ℝ (Set.Ioc 0 1) (fun r => vr l r x) ∧ ContinuousOn (fun r => vr l r x) (Set.Ioc 0 1) ∧ ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧ ∀ t ∈ Set.Icc r (r + δ), vr l t x = vr l r x + k * (t - r) := by
  first | exact @GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope | exact GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope | (intros; apply GlobalTheory.PMon.Gauss.vr_concave_cont_rightSlope <;> assumption)
end

section

noncomputable section
namespace GlobalTheory.TopSteps.TrivLine
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem exists_diff_of_sum_eq_zero {k : Type} [Field k] {n : ℕ} [NeZero n] (c : ZMod n → k) (hc : ∑ i, c i = 0) :
    ∃ d : ZMod n → k, ∀ i, c i = d (i - 1) - d i := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  refine ⟨fun i => -∑ j ∈ Finset.range (i.val + 1), c (j : ZMod (n + 1)), fun i => ?_⟩
  have hall : ∑ j ∈ Finset.range (n + 1), c (j : ZMod (n + 1)) = 0 := by
    rw [← hc, Finset.sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    exact ZMod.natCast_zmod_val (n := n + 1) x
  by_cases hi : i = 0
  · subst hi
    have h1 : ((0 : ZMod (n + 1)) - 1).val = n := by
      rw [zero_sub]; exact ZMod.val_neg_one n
    simp only [h1, ZMod.val_zero, hall]
    simp
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (fun h => hi ((ZMod.val_eq_zero i).1 h))
    have hlt := ZMod.val_lt i
    have hi' : i = ((j + 1 : ℕ) : ZMod (n + 1)) := by
      rw [show j + 1 = i.val from hj.symm, ZMod.natCast_zmod_val]
    have h1 : (i - 1).val = j := by
      have : i - 1 = (j : ZMod (n + 1)) := by rw [hi']; push_cast; ring
      rw [this, ZMod.val_natCast_of_lt (by omega)]
    simp only [h1, hj, Nat.succ_eq_add_one]
    rw [Finset.sum_range_succ _ (j + 1), ← hi']
    ring

variable {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l}

theorem mem_of_inZZ (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (h1 : Dt.T1 l) (h2 : Dt.T2 l)
    (h3 : Dt.T3 l) (b g : ZMod n → Vc k 1) (hZ : InZZ (F.D (chr 1)) Dt (M.Nχ 0) b g) (i : ZMod n) :
    b i ∈ M.Nχ 0 i := by
  have hω : M.ω ^ (-(0 : ℤ)) = 1 := by simp
  have ht : (0 : ℤ) < Dt.t := by exact_mod_cast Dt.one_le_letterBlockLength
  have hlat := M.χ_lat 0 (by norm_num) ht i
  rw [hω] at hlat
  obtain ⟨hL, hC, hP, hS⟩ := hlat
  rw [sh_zero_eq] at hP
  obtain ⟨z0, z1, zG, zB⟩ := hZ i
  have hv := vv_ne_zero k
  have hφ : (F.D (chr 1)).φ i (g (i - 1)) ∈ sh 1 (M.Nχ 0 i) := by
    obtain ⟨y, hy, e⟩ := mem_sh_iff_exists.1 (hZ (i - 1)).2.1
    obtain ⟨u, hu⟩ := R.φ_v
    obtain ⟨l', hl'⟩ := Nat.exists_eq_add_of_le (Fact.out : l.Prime).one_le
    have hy' : (F.D (chr 1)).φ i y ∈ M.Nχ 0 i := by
      rw [← hP]; exact Submodule.subset_span ⟨y, hy, rfl⟩
    refine mem_sh_iff_exists.2 ⟨((u : k⟦X⟧) * PowerSeries.X ^ l') • (F.D (chr 1)).φ i y,
      Submodule.smul_mem _ _ hy', ?_⟩
    rw [← e, (F.D (chr 1)).φ_semi i, zpow_one, hu, ← algebraMap_smul k⸨X⸩ ((u : k⟦X⟧) * PowerSeries.X ^ l'),
      smul_smul]
    congr 1
    change _ * (((u : k⟦X⟧) * PowerSeries.X ^ l' : k⟦X⟧) : k⸨X⸩) = _
    rw [map_mul, map_pow, ← vv_eq_coe_X, hl']
    ring
  have hnab : nab ((F.D (chr 1)).γ i) (b i) ∈ M.Nχ 0 i := by
    have := mem_sh_iff_smul_mem.1 (Submodule.sub_mem _ hφ z1)
    rw [← z0, zpow_neg_one] at this
    exact this
  have key : ∀ J : ℤ, 0 ≤ J → J ≤ Dt.η i → b i ∈ sh (-J) (M.Nχ 0 i) → b i ∈ M.Nχ 0 i := by
    intro J hJ hJ' hb
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hJ
    have hl := h1 i
    have := (GlobalTheory.PhiGam.Window.nab_bijective_window R _ ((F.D (chr 1)).γ_semi i) _ hL hC (-(m : ℤ)) m (by
      intro j hj
      rw [hS, resCount, Multiset.card_eq_zero]
      refine (@Multiset.filter_eq_nil _ _ (_) _).2 ?_
      intro a ha e
      rw [Multiset.mem_singleton] at ha
      subst ha
      have e' : ((m - j : ℕ) : k) = 0 := by
        rw [Nat.cast_sub hj.le]
        push_cast at e
        linear_combination e
      have := Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff k l _).1 e')
      omega)).1 (b i) hb (by rw [neg_add_cancel, sh_zero_eq]; exact hnab)
    rwa [neg_add_cancel, sh_zero_eq] at this
  obtain ⟨-, -, wG, wB⟩ := GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i
  cases hty : Dt.ty i with
  | G =>
    obtain ⟨-, -, a1, a2⟩ := wG hty
    exact key _ (by omega) (by omega) (zG hty)
  | Bd =>
    obtain ⟨-, -, a1, a2⟩ := wB hty
    have := (zB hty).1
    rw [hP] at this
    exact key _ (by omega) a2 this

theorem exists_const_pair (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (h1 : Dt.T1 l)
    (h2 : Dt.T2 l) (h3 : Dt.T3 l) (z : G → Fin 1 → k) (hz : z ∈ M.twistedModelAdmissibleCocycles (chr 1)) :
    ∃ (b g m : ZMod n → Vc k 1) (c : ZMod n → k), Repr F (chr 1) z b g ∧
      ∀ i, b i = (F.D (chr 1)).φ i (m (i - 1)) - m i + c i • F.unit i ∧ g i = (F.D (chr 1)).γ i (m i) - m i := by
  obtain ⟨N, b, g, hN, hR, hZ⟩ := GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair F M h1 h2 h3 (chr 1) z hz
  have hω : M.ω ^ (-(0 : ℤ)) = 1 := by simp
  have ht : (0 : ℤ) < Dt.t := by exact_mod_cast Dt.one_le_letterBlockLength
  have hCH := GlobalTheory.T.twistedPhiGammaModel_character_eq_standard F M h1 h2 h3 0 le_rfl ht N
  rw [hω] at hCH
  obtain rfl := hCH hN
  have hb : ∀ i, ∃ β : k⟦X⟧, b i = (β : k⸨X⸩) • F.unit i := fun i => by
    have := mem_of_inZZ F M h1 h2 h3 b g hZ i
    rw [M.χ_zero, Submodule.mem_span_singleton] at this
    obtain ⟨β, e⟩ := this
    exact ⟨β, by rw [← e, ← algebraMap_smul k⸨X⸩ β]; rfl⟩
  have hg : ∀ i, ∃ β : k⟦X⟧, PowerSeries.constantCoeff β = 0 ∧ g i = (β : k⸨X⸩) • F.unit i := fun i => by
    obtain ⟨y, hy, e⟩ := mem_sh_iff_exists.1 (hZ i).2.1
    rw [M.χ_zero, Submodule.mem_span_singleton] at hy
    obtain ⟨β, rfl⟩ := hy
    refine ⟨PowerSeries.X * β, by simp, ?_⟩
    rw [← e, ← algebraMap_smul k⸨X⸩ β, zpow_one, smul_smul, map_mul, ← vv_eq_coe_X]; rfl
  choose β hβ using hb
  choose δ hδ0 hδ using hg
  have eφ : ∀ i (a : k⸨X⸩), (F.D (chr 1)).φ i (a • F.unit (i - 1)) = R.φ a • F.unit i := fun i a => by
    rw [(F.D (chr 1)).φ_semi i, F.unit_φ]
  have eγ : ∀ i (a : k⸨X⸩), (F.D (chr 1)).γ i (a • F.unit i) = R.γ a • F.unit i := fun i a => by
    rw [(F.D (chr 1)).γ_semi i, F.unit_γ]
  obtain ⟨m, c, hm⟩ := GlobalTheory.PhiGam.TrivCocycle.main R β δ hδ0 (fun i => by
    have e := (hZ i).1
    rw [hβ i, hδ i, hδ (i - 1), eφ, eγ, ← sub_smul, ← sub_smul] at e
    exact smul_left_injective _ (F.unit_ne i) e)
  refine ⟨b, g, fun i => (m i : k⸨X⸩) • F.unit i, c, hR, fun i => ⟨?_, ?_⟩⟩
  · rw [hβ, (hm i).1, eφ, add_smul, sub_smul]
    congr 1
    apply funext
    intro j
    change (algebraMap k k⸨X⸩) (c i) * F.unit i j = c i • F.unit i j
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
      HahnSeries.C_mul_eq_smul]
    simp
  · rw [hδ, (hm i).2, eγ, sub_smul]

theorem main : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ z : Fin 2 → G → Fin 1 → k, (∀ a, z a ∈ M.twistedModelAdmissibleCocycles (chr 1)) → ¬ LinearIndependent k (fun a => (cob (chr (1 : G →* kˣ))).mkQ (z a)) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 z hz hli
  choose b g m c hR hm using fun a => exists_const_pair F M h1 h2 h3 (z a) (hz a)
  have key : ∀ (p q : Fin 2) (x : k), x * ∑ i, c p i + ∑ i, c q i = 0 →
      x • (cob (chr (1 : G →* kˣ))).mkQ (z p) + (cob (chr (1 : G →* kˣ))).mkQ (z q) = 0 := by
    intro p q x hx
    obtain ⟨d, hd⟩ := exists_diff_of_sum_eq_zero (fun i => x * c p i + c q i)
      (by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hx])
    have hr := GlobalTheory.T.repr_smul_add F (chr 1) x (z p) (z q) _ _ _ _ (hR p) (hR q)
    have h0 := GlobalTheory.T.mem_coboundaries_of_herrPair_coboundary F (chr 1) _ _ _ hr (by
      refine ⟨fun i => x • m p i + m q i + d i • F.unit i, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
      · change (F.D (chr 1)).φ i (x • m p (i - 1) + m q (i - 1) + d (i - 1) • F.unit (i - 1)) -
          (x • m p i + m q i + d i • F.unit i) = x • b p i + b q i
        have e : d (i - 1) = x * c p i + c q i + d i := by rw [hd i]; ring
        rw [map_add (f := _), map_add (f := _), map_smul, map_smul, F.unit_φ, (hm p i).1, (hm q i).1, e]
        module
      · change (F.D (chr 1)).γ i (x • m p i + m q i + d i • F.unit i) -
          (x • m p i + m q i + d i • F.unit i) = x • g p i + g q i
        rw [map_add (f := _), map_add (f := _), map_smul, map_smul, F.unit_γ, (hm p i).2, (hm q i).2]
        module)
    rw [← map_smul, ← map_add (f := _)]
    exact (Submodule.Quotient.mk_eq_zero _).2 h0
  rw [Fintype.linearIndependent_iff] at hli
  by_cases hs : ∑ i, c 0 i = 0
  · have := hli ![1, 0] (by
      rw [Fin.sum_univ_two, add_comm]
      have := key 1 0 0 (by rw [hs]; ring)
      simpa using this) 0
    simp at this
  · have := hli ![-(∑ i, c 1 i) / ∑ i, c 0 i, 1] (by
      rw [Fin.sum_univ_two]
      have := key 0 1 (-(∑ i, c 1 i) / ∑ i, c 0 i) (by field_simp; ring)
      simpa using this) 1
    simp at this

end GlobalTheory.TopSteps.TrivLine
end
end

section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.whittakerDimension_cuspidal_greenDegree_eq_one : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → χ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) → wh ψ χ = 1 := by
  first | exact @GlobalTheory.GLq.wh_cusp_eq_one | exact GlobalTheory.GLq.wh_cusp_eq_one | (intros; apply GlobalTheory.GLq.wh_cusp_eq_one <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.exists_decompletion_frame_of_lattice : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ), HypW S E T M0 h0 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l), IsDec (D.locA l).actC (D.loc l).χQ K (mN l s (M0 + h0)) M Dm U g ∧ ∀ a i j, (Dm⁻¹ * A a * Dm) i j ∈ intC (Ks K (mN l s (M0 + h0))) := by
  first | exact @GlobalTheory.Cyc.Decomp.exists_decompletion | exact GlobalTheory.Cyc.Decomp.exists_decompletion | (intros; apply GlobalTheory.Cyc.Decomp.exists_decompletion <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.senMultiset_base_lattice_eq_jumps_mod : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∀ N : Lats k S.n A.m, (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) → ∀ i x, sen ((F.D A).γ i) (N i) x = resCount (U i) 0 x := by
  first | exact @GlobalTheory.BaseSen.sen_base | exact GlobalTheory.BaseSen.sen_base | (intros; apply GlobalTheory.BaseSen.sen_base <;> assumption)
end

section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.phiGamma_reduction_base_lattice_bounds : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∀ N : Lats k S.n A.m, (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) → ∀ w w' : ZMod S.n → ℕ, (∀ i, ∀ u ∈ U i, -(w i : ℤ) ≤ u ∧ u ≤ w' i) → ABC (F.D A) (fun i => w i) (fun i => w' i) N := by
  first | exact @GlobalTheory.BaseABC.base_abc | exact GlobalTheory.BaseABC.base_abc | (intros; apply GlobalTheory.BaseABC.base_abc <;> assumption)
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.transport_keeps_cuspidal_twists_characters : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → (∀ (x : IrrGL (k := k)) (x' : IrrGL (k := k')), RepRel i x x' → (x.IsCusp ↔ x'.IsCusp) ∧ ∀ s : ℂ, RepRel i (x.nu s) (x'.nu s)) ∧ ∀ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ'), (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → RepRel i (IrrGL.ofChar χ hχ) (IrrGL.ofChar χ' hχ') := by
  first | exact @GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar | exact GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar | (intros; apply GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar <;> assumption)
end
