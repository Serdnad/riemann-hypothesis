module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassTelescope
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LValEtaBounds
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.SizeQ

theorem one_le_size (D : D7) (b C : ℝ) (Z : GramM D) : 1 ≤ sizeZ D b C Z := by
  unfold sizeZ
  refine Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
    (fun x y hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl (fun τ _ => ?_)
  exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x)
    (fun x y hx hy => one_le_mul_of_one_le_of_one_le hx hy) le_rfl (fun l _ => le_max_left _ _)

private lemma one_add_logb_two_mul_le_of_log_le_sqrt (f r : ℕ) (hf : 1 ≤ f) (hr : 1 ≤ r)
    (hlog : Real.log f ≤ Real.sqrt r) : 1 + Real.logb 2 (2 * (f : ℝ)) ≤ 2 * (r : ℝ) + 2 := by
  have hf0 : (0 : ℝ) < f := by exact_mod_cast hf
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hsq : Real.sqrt r ≤ r := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hsplit : Real.logb 2 (2 * (f : ℝ)) = 1 + Real.log f / Real.log 2 := by
    rw [Real.logb, Real.log_mul (by norm_num) hf0.ne', add_div, div_self (by linarith)]
  have hdiv : Real.log f / Real.log 2 ≤ 2 * r := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

theorem classNumber_le (D : D7) (b : ℝ) (hb : 1 ≤ b) (hrd : D.host.rdE ≤ b) (hf : 1 ≤ D.R.f)
    (hr : 1 ≤ D.R.rS) (hlog : Real.log D.R.f ≤ Real.sqrt D.R.rS) :
    (classNumber D.host.E : ℝ) ≤ b ^ ((D.R.m : ℝ) * D.R.f) := by
  obtain ⟨-, hdeg, -, hm, hrd1, -⟩ := GlobalTheory.real_places_facts D
  have hcn := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.classNumberBound D.host.E
  have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  have hdeg' : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f := by rw [hdeg]; push_cast; ring

  have hdisc : |(NumberField.discr D.host.E : ℝ)| = D.host.rdE ^ (2 * (D.R.f : ℝ)) := by
    rw [Formalism.BasicNotions.Host.rdE, hdeg', ← Real.rpow_mul (abs_nonneg _), one_div,
      inv_mul_cancel₀ (by positivity), Real.rpow_one]
  rw [hdisc, hdeg', ← Real.rpow_mul (by linarith)] at hcn
  have hc := one_add_logb_two_mul_le_of_log_le_sqrt D.R.f D.R.rS hf hr hlog
  have hf1r : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hlb : 0 ≤ Real.logb 2 (2 * (D.R.f : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hm' : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by rw [hm]; push_cast; ring
  calc (classNumber D.host.E : ℝ)
      ≤ D.host.rdE ^ (2 * (D.R.f : ℝ) * ((1 + Real.logb 2 (2 * (D.R.f : ℝ))) / 2)) := hcn
    _ ≤ b ^ (2 * (D.R.f : ℝ) * ((1 + Real.logb 2 (2 * (D.R.f : ℝ))) / 2)) :=
        Real.rpow_le_rpow (by linarith) hrd (by positivity)
    _ ≤ b ^ ((D.R.m : ℝ) * D.R.f) := by
        apply Real.rpow_le_rpow_of_exponent_le hb
        rw [hm']
        nlinarith

private lemma le_rpow_abs_div_eight_of_mul_pow_le (k b Cg g : ℝ) (hk : 0 ≤ k) (hb : 1 ≤ b) (h1 : (k * b) ^ 8 ≤ g)
    (h2 : g ≤ b ^ Cg) : k ≤ b ^ (|Cg| / 8) := by
  have hk8 : k ^ 8 ≤ b ^ |Cg| := by
    calc k ^ 8 ≤ (k * b) ^ 8 := by
          apply pow_le_pow_left₀ hk; nlinarith
      _ ≤ b ^ Cg := h1.trans h2
      _ ≤ b ^ |Cg| := Real.rpow_le_rpow_of_exponent_le hb (le_abs_self _)
  by_contra hlt
  push_neg at hlt
  have hpos : 0 ≤ b ^ (|Cg| / 8) := Real.rpow_nonneg (by linarith) _
  have := pow_lt_pow_left₀ hlt hpos (by norm_num : (8 : ℕ) ≠ 0)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)] at this
  norm_num at this
  linarith

theorem main : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ Z : GramM D, (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f * 9 ^ D.R.f ≤ HHZ D large₂.sc.b C Z := by
  intro Cg cb Cu cT CT C0 A
  refine ⟨|Cg| / 8 + 3 / 2 + 6, ?_⟩
  intro C hC D large₂ u u' C' Cl hCl hH Z
  obtain ⟨⟨hS0, -, -⟩, hSt, -⟩ := hH
  obtain ⟨-, -, hmf, -, hlogf, -, -, -, -, -, hlrd, hg1, hg1b, -, -, -, -, -, hv, -, -, -, -, -, -⟩ := hS0
  have hr : 1 ≤ D.R.rS := hSt.1
  obtain ⟨-, -, -, hm, hrd1, -⟩ := GlobalTheory.real_places_facts D

  set b := large₂.sc.b with hbdef
  have hL : 0 < large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hbexp : b = Real.exp large₂.sc.L := rfl
  have hrd2 : 2 ≤ D.host.rdE := by
    have : D.host.v = D.host.rdE / 2 := rfl
    linarith
  have hrdb : D.host.rdE ≤ b := by
    have hlog : Real.log D.host.rdE ≤ large₂.sc.L := by
      have : large₂.sc.L / Cl ≤ large₂.sc.L := div_le_self hL.le hCl
      linarith
    calc D.host.rdE = Real.exp (Real.log D.host.rdE) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp large₂.sc.L := Real.exp_le_exp.mpr hlog
      _ = b := hbexp.symm
  have hb2 : 2 ≤ b := hrd2.trans hrdb
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hm4 : 4 ≤ D.R.m := by omega
  have hf1 : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf

  have hk : (D.R.k : ℝ) ≤ b ^ (|Cg| / 8) := le_rpow_abs_div_eight_of_mul_pow_le _ _ _ _ (Nat.cast_nonneg _) hb1 hg1 hg1b
  have hsq : D.host.rdE ^ ((1 : ℝ) / 2) ≤ b ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (by linarith) hrdb (by norm_num)
  have hbase : 2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2) ≤ b ^ (|Cg| / 8 + 3 / 2) := by
    have e : b ^ (|Cg| / 8 + 3 / 2) = b ^ (1 : ℝ) * b ^ (|Cg| / 8) * b ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]; ring_nf
    rw [e, Real.rpow_one]
    have h0 : 0 ≤ D.host.rdE ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
    have h0' : 0 ≤ (D.R.k : ℝ) := Nat.cast_nonneg _
    have h0'' : 0 ≤ b ^ (|Cg| / 8) := Real.rpow_nonneg hb0.le _
    calc 2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2) ≤ b * b ^ (|Cg| / 8) * D.host.rdE ^ ((1 : ℝ) / 2) := by
          gcongr
      _ ≤ b * b ^ (|Cg| / 8) * b ^ ((1 : ℝ) / 2) := by gcongr
  have hcls := classNumber_le D b hb1 hrdb hf1 hr hlogf
  have h18 : (2 : ℝ) ^ D.R.f * 9 ^ D.R.f ≤ b ^ ((5 : ℝ) * D.R.f) := by
    rw [← mul_pow, Real.rpow_mul hb0.le, Real.rpow_natCast]
    apply pow_le_pow_left₀ (by norm_num)
    have : (2 : ℝ) ^ (5 : ℝ) ≤ b ^ (5 : ℝ) := Real.rpow_le_rpow (by norm_num) hb2 (by norm_num)
    have h32 : (2 : ℝ) ^ (5 : ℝ) = 32 := by norm_num
    linarith

  set e1 : ℝ := |Cg| / 8 + 3 / 2 with he1
  have he1n : 0 ≤ e1 := by positivity
  have hpow : (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f ≤ b ^ (e1 * D.R.f) := by
    rw [Real.rpow_mul hb0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) hbase _
  have hprod : (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f * 9 ^ D.R.f
      ≤ b ^ ((e1 + D.R.m + 5) * D.R.f) := by
    have e : b ^ ((e1 + D.R.m + 5) * D.R.f) = b ^ (e1 * D.R.f) * b ^ ((D.R.m : ℝ) * D.R.f) * b ^ ((5 : ℝ) * D.R.f) := by
      rw [← Real.rpow_add hb0, ← Real.rpow_add hb0]; ring_nf
    rw [e, mul_assoc _ ((2 : ℝ) ^ D.R.f)]
    have hc0 : (0 : ℝ) ≤ classNumber D.host.E := Nat.cast_nonneg _
    have hq0 : (0 : ℝ) ≤ (2 : ℝ) ^ D.R.f * 9 ^ D.R.f := by positivity
    gcongr

  have hm1 : (4 : ℝ) ≤ D.R.m := by exact_mod_cast hm4
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hC1 : 1 ≤ C := by
    have : 0 ≤ |Cg| / 8 := by positivity
    linarith
  have hexp : (e1 + D.R.m + 5) * D.R.f ≤ C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by
    have h1 : e1 + D.R.m + 5 ≤ C * D.R.m := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ C - (e1 + 6)) (by linarith : (0 : ℝ) ≤ D.R.m),
        mul_nonneg he1n (by linarith : (0 : ℝ) ≤ D.R.m - 1)]
    have hm2 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
    have h2 : 1 ≤ C * (D.R.m : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hC1 hm2
    have h3 : e1 + D.R.m + 5 ≤ C * (D.R.m : ℝ) ^ 2 * (C * D.R.m) :=
      h1.trans (le_mul_of_one_le_left (by positivity) h2)
    calc (e1 + D.R.m + 5) * D.R.f ≤ C * (D.R.m : ℝ) ^ 2 * (C * D.R.m) * D.R.f :=
          mul_le_mul_of_nonneg_right h3 hf0
      _ = C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m) := by ring
  have hsz := one_le_size D b C Z
  unfold HHZ
  rw [← Real.rpow_mul hb0.le]
  calc _ ≤ b ^ ((e1 + D.R.m + 5) * D.R.f) := hprod
    _ ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) := Real.rpow_le_rpow_of_exponent_le hb1 hexp
    _ ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) * sizeZ D b C Z ^ 4 := by
        have : 1 ≤ sizeZ D b C Z ^ 4 := one_le_pow₀ hsz
        have : 0 ≤ b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * D.R.m)) := Real.rpow_nonneg hb0.le _
        nlinarith

end GlobalTheory.LoopC.SizeQ
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.MassRatioInvBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private lemma sqrt_pow_eq_pow_sqrt (a : ℝ) (ha : 0 ≤ a) (f : ℕ) : Real.sqrt (a ^ f) = Real.sqrt a ^ f := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg a) f), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt ha]

private lemma one_le_factorial_mul_exp_div_pow (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ ((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk0 : (0 : ℝ) < (k : ℝ) ^ k := pow_pos hkpos k
  have hn : (k - 1).factorial * k = k.factorial := by
    rw [mul_comm]; exact Nat.mul_factorial_pred (by omega)
  have hf : ((k - 1).factorial : ℝ) * k = (k.factorial : ℝ) := by exact_mod_cast hn
  rw [hf, le_div_iff₀ hk0, one_mul, Real.exp_one_pow]
  have h := Real.pow_div_factorial_le_exp (x := (k : ℝ)) (Nat.cast_nonneg k) k
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hfac] at h
  rw [mul_comm]
  exact h

theorem one_le_ratio_mul (f k : ℕ) (v L : ℝ) (hv : 0 < v) (hk : 1 ≤ k) (hL : ((2 : ℝ) ^ f)⁻¹ ≤ L) :
    1 ≤ (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) ^ f / Real.sqrt ((2 * v) ^ f) * L *
      ((Real.exp 1 * Real.pi / (k * v)) ^ (k * f) * (2 * (k : ℝ) * (2 * v) ^ ((1 : ℝ) / 2)) ^ f) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpi := Real.pi_pos
  have hs0 : 0 < Real.sqrt (2 * v) := Real.sqrt_pos.mpr (by linarith)
  have hrp : (2 * v) ^ ((1 : ℝ) / 2) = Real.sqrt (2 * v) := by rw [Real.sqrt_eq_rpow]
  rw [hrp, sqrt_pow_eq_pow_sqrt (2 * v) (by linarith) f, pow_mul]

  have hcol : (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) ^ f / Real.sqrt (2 * v) ^ f * L *
      (((Real.exp 1 * Real.pi / (k * v)) ^ k) ^ f * (2 * (k : ℝ) * Real.sqrt (2 * v)) ^ f) =
      ((((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) * (Real.exp 1 * Real.pi / (k * v)) ^ k *
        (2 * (k : ℝ) * Real.sqrt (2 * v)) / Real.sqrt (2 * v)) ^ f * L := by
    rw [div_pow, mul_pow, mul_pow]
    ring

  have hbase : (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) * (Real.exp 1 * Real.pi / (k * v)) ^ k *
      (2 * (k : ℝ) * Real.sqrt (2 * v)) / Real.sqrt (2 * v) =
      (((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k) * 2 := by
    have hv0 : v ≠ 0 := hv.ne'
    have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
    have hp0 : Real.pi ≠ 0 := hpi.ne'
    have hs : Real.sqrt (2 * v) ≠ 0 := hs0.ne'
    rw [div_pow, div_pow, mul_pow, mul_pow]
    field_simp
  rw [hcol, hbase, mul_pow]
  have hA := one_le_factorial_mul_exp_div_pow k hk
  have hAf : 1 ≤ (((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k) ^ f := one_le_pow₀ hA
  have h2 : 1 ≤ (2 : ℝ) ^ f * L := by
    have h := mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 2 ^ f)
    rwa [mul_inv_cancel₀ (by positivity)] at h
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k) ^ f * ((2 : ℝ) ^ f * L) :=
        mul_le_mul hAf h2 zero_le_one (by linarith)
    _ = _ := by ring

theorem stdH_eq (D : D7) (j : ℕ) : Cnt.stdH D.host.E j = massTelescope_form D.host.E j := rfl

theorem stdLat_eq (D : D7) (j : ℕ) : Cnt.stdLat D.host.E j = massTelescope_lat D.host.E j := by
  unfold Cnt.stdLat massTelescope_lat
  congr 2
  funext i
  simp [Pi.basisFun_apply]

theorem massS_eq (D : D7) (j : ℕ) :
    Cnt.massS D j = mass (massTelescope_form D.host.E j) (massTelescope_lat D.host.E j) := by
  unfold Cnt.massS Cnt.massU
  rw [stdH_eq, stdLat_eq]

theorem mass_pred_le : ∀ D : D7, UnitaryVolumeMass.stMassRatio D → Cnt.massS D (D.R.k - 1) ≤ Cnt.massS D D.R.k * ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) * (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f) := by
  intro D hM
  have hk : 5 ≤ D.R.k := D.R.k_ge
  have hrd : D.host.rdE = 2 * D.host.v := by
    unfold Formalism.BasicNotions.Host.v
    ring
  have hv : 0 < D.host.v := by
    unfold Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
    have hd : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero D.host.E))
    exact div_pos (Real.rpow_pos_of_pos hd _) two_pos
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hL := (GlobalTheory.EtaValueBound.lValEta_bounds D.host.E hK D.R.k (by omega)).1
  rw [Formalism.MainNotions.StandardLattice.fDeg_host] at hL
  have hrat := hM D.R.k (by omega) (Fin D.R.k → D.host.E) (Fin (D.R.k - 1) → D.host.E)
    (massTelescope_form D.host.E D.R.k) (massTelescope_form D.host.E (D.R.k - 1))
    (massTelescope_lat D.host.E D.R.k) (massTelescope_lat D.host.E (D.R.k - 1))
    (massTelescope_symm D.host.E _) (massTelescope_symm D.host.E _)
    (massTelescope_ortho D.host.E _) (massTelescope_ortho D.host.E _)
  unfold massRatioRightSide at hrat
  rw [Formalism.MainNotions.StandardLattice.fDeg_host, Formalism.MainNotions.StandardLattice.vInv_host] at hrat
  have key := one_le_ratio_mul D.R.f D.R.k D.host.v (lValEta D.host.E D.R.k) hv (by omega) hL
  rw [massS_eq, massS_eq, hrd]
  set a := mass (massTelescope_form D.host.E D.R.k) (massTelescope_lat D.host.E D.R.k) with ha
  set b := mass (massTelescope_form D.host.E (D.R.k - 1)) (massTelescope_lat D.host.E (D.R.k - 1))
    with hb
  set R := (((D.R.k - 1).factorial : ℝ) * (D.host.v / Real.pi) ^ D.R.k) ^ D.R.f /
    Real.sqrt ((2 * D.host.v) ^ D.R.f) * lValEta D.host.E D.R.k with hR

  have hb0 : 0 ≤ b := by
    rw [hb]
    unfold mass
    split_ifs
    · exact Finset.sum_nonneg fun _ _ => by positivity
    · exact le_rfl
  have hRpos : 0 < R := by
    have h2 : (0 : ℝ) < (2 ^ D.R.f)⁻¹ := by positivity
    have hLpos : 0 < lValEta D.host.E D.R.k := lt_of_lt_of_le h2 hL
    have hpi := Real.pi_pos
    rw [hR]
    positivity
  have hbne : b ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hrat
    linarith
  have hab : a = R * b := by rw [← hrat, div_mul_cancel₀ a hbne]
  rw [hab]
  calc b = b * 1 := (mul_one b).symm
    _ ≤ b * (R * ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
        (2 * (D.R.k : ℝ) * (2 * D.host.v) ^ ((1 : ℝ) / 2)) ^ D.R.f)) :=
        mul_le_mul_of_nonneg_left key hb0
    _ = _ := by ring

end GlobalTheory.MassRatioInvBound
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Count GlobalTheory.GaussMean
open Formalism.MainNotions.S (AutInst uMat)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SiegelWeilMean

theorem lintegral_eq_of_meanC {α : Type} [MeasurableSpace α] (μ : Measure α) (S : Set α) (hS : μ S < ⊤)
    (G : α → ENNReal) (hG : Measurable G) (hfin : ∫⁻ a in S, G a ∂μ < ⊤) (c : ℝ)
    (h : meanC μ S (fun a => ((G a).toReal : ℂ)) = (c : ℂ)) :
    ∫⁻ a in S, G a ∂μ = μ S * ENNReal.ofReal c := by
  by_cases h0 : μ S = 0
  · rw [h0, zero_mul, setLIntegral_measure_zero _ _ h0]
  have h1 : (μ S).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0, hS.ne⟩
  unfold meanC at h
  beta_reduce at h
  rw [integral_complex_ofReal, integral_toReal hG.aemeasurable (ae_lt_top hG hfin.ne), Complex.real_smul] at h
  have h2 : (μ S).toReal⁻¹ * (∫⁻ a in S, G a ∂μ).toReal = c := by exact_mod_cast h
  rw [← h2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin.ne, ← mul_assoc,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_toReal hS.ne, ENNReal.mul_inv_cancel h0 hS.ne, one_mul]

theorem exists_transport (I : AutInst) (T : HA (AF I.F) I.cm.sig I.J ≃ₜ* I.GA)
    (hT : ∀ h, (show HR (AF I.F) I.cm.sig I.J from h) ∈ HFinIn (AF I.F) I.cm.sig I.J ↔ T h ∈ I.GFset)
    (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA) (hfund : I.IsFundDom (I.muA μf) fund) :
    ∃ (μ : Measure (HA (AF I.F) I.cm.sig I.J)) (S : Set (HA (AF I.F) I.cm.sig I.J)), μ.IsHaarMeasure ∧
      IsFundamentalDomain (HFinIn (AF I.F) I.cm.sig I.J) S μ ∧ Measurable T ∧ μ S = I.muA μf fund ∧
      ∀ f : I.GA → ENNReal, ∫⁻ h in S, f (T h) ∂μ = ∫⁻ x in fund, f x ∂(I.muA μf) := by
  obtain ⟨_, _, _, -⟩ := GlobalTheory.CongTop.adelic_topology I
  haveI : ∀ v, (Formalism.REAL.muG (I.ε v)).IsHaarMeasure := fun v => by unfold Formalism.REAL.muG; infer_instance
  haveI : (Measure.pi fun v => Formalism.REAL.muG (I.ε v)).IsHaarMeasure := Measure.pi.isHaarMeasure _
  haveI : (I.muA μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  haveI : BorelSpace I.GA := inferInstance
  haveI : BorelSpace (HA (AF I.F) I.cm.sig I.J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (AF I.F) I.cm.sig I.J) := inferInstance
  obtain ⟨Γ, hΓ, -, -, hF⟩ := GlobalTheory.RatDiscrete.rational_points I
  let e : HA (AF I.F) I.cm.sig I.J ≃ᵐ I.GA := T.toHomeomorph.toMeasurableEquiv
  have hp : MeasurePreserving e ((I.muA μf).map e.symm) (I.muA μf) :=
    (MeasurePreserving.symm e.symm ⟨e.symm.measurable, rfl⟩ :)
  have hmem : ∀ g : Γ, (show HR (AF I.F) I.cm.sig I.J from T.symm g) ∈ HFinIn (AF I.F) I.cm.sig I.J := fun g => by
    refine (hT (T.symm g)).2 ?_
    have : T (T.symm g) = g := T.apply_symm_apply _
    exact this.symm ▸ (hΓ ▸ g.2 : g.1 ∈ I.GFset)
  refine ⟨(I.muA μf).map e.symm, e ⁻¹' fund, T.symm.isHaarMeasure_map _, ?_, e.measurable,
    hp.measure_preimage_equiv _, fun f => hp.setLIntegral_comp_preimage_emb e.measurableEmbedding f _⟩
  refine (hF μf fund hfund).preimage_of_equiv hp.quasiMeasurePreserving
    (e := fun g => ⟨T.symm g, hmem g⟩) ⟨fun a b hab => ?_, fun b => ?_⟩ fun g x => ?_
  · exact Subtype.ext (T.symm.injective (congrArg Subtype.val hab))
  · exact ⟨⟨T b.1, by rw [← SetLike.mem_coe, hΓ]; exact (hT _).1 b.2⟩, Subtype.ext (T.symm_apply_apply _)⟩
  · change T (T.symm g * x) = g * T x
    rw [map_mul, T.apply_symm_apply]

theorem const_eq {ι κ : Type} [Fintype κ] (q : ι → ℝ) (hq : ∀ u, 0 < q u) (m : ι → ℤ)
    (hm : (Function.support m).Finite) (a : ι → ℝ) (Lv : ℝ) (ha : HasProd a Lv⁻¹) (lam g : κ → ℝ)
    (hlam : ∀ v, lam v ≠ 0) (w : ℝ) (hw : 0 < w) (n f : ℕ) (hf : Fintype.card κ = f)
    (hp : ∏ᶠ u, q u ^ m u = (2 * w) ^ f * ∏ v, |lam v|) :
    ((∏ v, 2 ^ n * |lam v| ^ ((n : ℝ) - 1 / 2) * g v : ℝ) : ℂ) *
      ∏' u, (((q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)) * a u : ℝ) : ℂ) =
      (((2 * w) ^ ((f : ℝ) / 2) * (w ^ (n * f))⁻¹ / Lv * ∏ v, g v : ℝ) : ℂ) := by
  have hout : ∀ u ∉ hm.toFinset, m u = 0 := fun u hu => by simpa using hu
  have h1 : HasProd (fun u => (q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)))
      (∏ u ∈ hm.toFinset, (q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ))) :=
    hasProd_prod_of_ne_finset_one fun u hu => by simp [hout u hu]
  have h2 : ∏ u ∈ hm.toFinset, (q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)) =
      ((2 * w) ^ f * ∏ v, |lam v|) ^ ((1 / 2 : ℝ) - (n : ℝ)) := by
    rw [Real.finsetProd_rpow _ _ (fun u _ => (zpow_pos (hq u) _).le) _, ← hp,
      finprod_eq_prod_of_mulSupport_subset _ (s := hm.toFinset)]
    intro u hu
    by_contra h
    exact hu (by simp [hout u h])
  have h3 := (h1.mul ha).map Complex.ofRealHom Complex.continuous_ofReal
  have h4 : ∏' u, (((q u ^ m u) ^ ((1 / 2 : ℝ) - (n : ℝ)) * a u : ℝ) : ℂ) = _ := h3.tprod_eq
  rw [h4, h2, Complex.ofRealHom_eq_coe, ← Complex.ofReal_mul]
  congr 1
  have hl : 0 < ∏ v, |lam v| := Finset.prod_pos fun v _ => abs_pos.2 (hlam v)
  have h5 : (∏ v, |lam v|) ^ ((n : ℝ) - 1 / 2) * (∏ v, |lam v|) ^ ((1 / 2 : ℝ) - (n : ℝ)) = 1 := by
    rw [← Real.rpow_add hl]; simp
  have h6 : ((2 * w) ^ f) ^ ((1 / 2 : ℝ) - (n : ℝ)) = (2 * w) ^ ((f : ℝ) / 2) * ((2 * w) ^ (n * f))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast (2 * w) (n * f),
      ← Real.rpow_neg (by positivity), ← Real.rpow_add (by positivity)]
    congr 1; push_cast; ring
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hf,
    Real.finsetProd_rpow _ _ (fun v _ => abs_nonneg _) _, Real.mul_rpow (by positivity) hl.le, h6, mul_pow, pow_mul 2]
  have : (2 ^ n : ℝ) ^ f ≠ 0 := by positivity
  have h7 : (∏ v, |lam v|) ^ ((1 / 2 : ℝ) - (n : ℝ)) = ((∏ v, |lam v|) ^ ((n : ℝ) - 1 / 2))⁻¹ :=
    eq_inv_of_mul_eq_one_right h5
  have : (∏ v, |lam v|) ^ ((n : ℝ) - 1 / 2) ≠ 0 := by positivity
  rw [h7]
  field_simp


end GlobalTheory.SiegelWeilMean
end
end
