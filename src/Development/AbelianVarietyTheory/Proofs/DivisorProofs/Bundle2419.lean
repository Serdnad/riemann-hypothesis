module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqClassSumOfHom
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle767
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2101
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroBoundedSectionShiftedWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LoweredWeightInterpolationAtPoints
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

namespace GlobalTheory.Proof.componentDegrees_sum_le_total_degree

theorem degOn_sum_le : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ G : WTZ D.host.E, GoodW U (xiR D) V dict G → rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G ∧ (∑ᶠ Z : Comp Xo c, degOn U (xiR D) V dict Z G) ≤ degW U (xiR D) V dict G := by
  intro D H Dw l Xo c r U V dict hc G hG
  haveI : Finite (Comp Xo c) := finite_comp
  have hS : Splits U G := GlobalTheory.T.cuspForms_supLattice_split_over_components D H Dw l Xo c r U V dict (fun σ hσ => (hc.2 σ hσ).1) G
  have hO := GlobalTheory.T.components_peterssonOrthogonal_and_masses D H Dw l Xo c r U V dict hc G
  have hA : Adds U V dict G := GlobalTheory.T.component_ranks_degrees_add_with_masses D H Dw l Xo c r U V dict G hS hO.1
  obtain ⟨-, hr, -, -, hd⟩ := hA.2 hG
  refine ⟨hr, ?_⟩
  rw [hd]
  haveI : Fintype (Comp Xo c) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  refine Finset.sum_le_sum fun Z _ => ?_
  have hlog : (∑ σ : c.F →+* ℂ, Real.log (mass U V dict Z σ)) ≤ 0 :=
    Finset.sum_nonpos fun σ _ => Real.log_nonpos (hO.2.1 Z σ).1 (hO.2.1 Z σ).2
  have hq : ((∑ σ : c.F →+* ℂ, Real.log (mass U V dict Z σ)) / (Module.finrank ℚ c.F : ℝ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hlog (Nat.cast_nonneg _)
  have hk : (0:ℝ) ≤ (rankOn U Z G : ℝ) / 2 := by positivity
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hk hq]

end GlobalTheory.Proof.componentDegrees_sum_le_total_degree
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.OneMeasureRatio

theorem log_r_add_three_le (D : D7) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) :
    Real.log ((D.R.r : ℝ) + 3) ≤ L := by
  have hr : 6 ≤ D.R.r := by
    unfold Ranks.r; have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hf : 2 ≤ D.R.f := by
    unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
  have hn : D.R.r ≤ D.R.nV := by unfold Ranks.nV; omega
  have hr' : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hf' : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hn' : (D.R.r : ℝ) ≤ D.R.nV := by exact_mod_cast hn
  have h1 := hL.1
  rw [← Real.log_exp L]
  refine Real.log_le_log (by positivity) ?_
  have a1 : 2 * (D.R.r : ℝ) ≤ (D.R.f : ℝ) * D.R.r := mul_le_mul_of_nonneg_right hf' (by positivity)
  have a2 : 2 * (D.R.r : ℝ) * D.R.r ≤ (D.R.f : ℝ) * D.R.r * D.R.nV :=
    mul_le_mul a1 hn' (by positivity) (by positivity)
  have : (D.R.r : ℝ) + 3 ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := by nlinarith
  linarith

end GlobalTheory.OneMeasureRatio
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.OneMeasDim

theorem two_mul_card_pairs_le (p : ℕ) :
    2 * ∑ i : Fin p, (Finset.univ.filter (fun j : Fin p => i < j)).card ≤ p ^ 2 := by
  have e : ∑ i : Fin p, (Finset.univ.filter (fun j : Fin p => i < j)).card = ∑ i ∈ Finset.range p, i := by
    rw [← Finset.sum_range_reflect]
    rw [Fin.sum_univ_eq_sum_range (fun i => p - 1 - i) p |>.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  rw [e, mul_comm, Finset.sum_range_id_mul_two]
  rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

theorem abs_factor_le (d : ℤ) (i j : ℕ) (hij : i < j) :
    |((((d : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) : ℚ) : ℝ)| ≤ 1 + |(d : ℝ)| := by
  have hs : (1 : ℝ) ≤ (j : ℝ) - (i : ℝ) := by
    have : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
    linarith
  have hs0 : (0 : ℝ) < (j : ℝ) - (i : ℝ) := by linarith
  push_cast
  rw [abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
  have h1 : |(d : ℝ) + (j : ℝ) - (i : ℝ)| ≤ |(d : ℝ)| + ((j : ℝ) - (i : ℝ)) := by
    have := abs_add_le (d : ℝ) ((j : ℝ) - (i : ℝ))
    rw [abs_of_pos hs0] at this
    rw [show (d : ℝ) + (j : ℝ) - (i : ℝ) = (d : ℝ) + ((j : ℝ) - (i : ℝ)) by ring]
    exact this
  nlinarith [abs_nonneg (d : ℝ)]

theorem abs_weylDimU_le {p : ℕ} (lam : Fin p → ℤ) (B : ℝ) (hB : ∀ a b, |((lam a - lam b : ℤ) : ℝ)| ≤ B) :
    |((Formalism.IndefR.Mult.weylDimU lam : ℚ) : ℝ)| ≤
      (1 + B) ^ (∑ i : Fin p, (Finset.univ.filter (fun j : Fin p => i < j)).card) := by
  unfold Formalism.IndefR.Mult.weylDimU
  rw [Rat.cast_prod, Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
  rw [Rat.cast_prod, Finset.abs_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j hj => ?_
  have hij : (i : ℕ) < (j : ℕ) := (Finset.mem_filter.1 hj).2
  have := abs_factor_le (lam i - lam j) i j hij
  exact this.trans (by linarith [hB i j])

end GlobalTheory.OneMeasDim

namespace GlobalTheory.OneMeasDim

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem abs_wt_sub_le (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (a b : Fin ((Wc D i).sig (tauE D τ)).1 ⊕ Fin ((Wc D i).sig (tauE D τ)).2) :
    |((Formalism.L2.NTheta.wtOf D (Wc D i) τ a - Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ)| ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i := by
  have hw : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases hab : a = b
  · subst hab; simpa using hw
  set c : ℝ := (((D.hc τ).e i : ℚ) : ℝ)
  set g : (Fin ((Wc D i).sig (tauE D τ)).1 ⊕ Fin ((Wc D i).sig (tauE D τ)).2) → ℝ :=
    fun x => |((Formalism.L2.NTheta.wtOf D (Wc D i) τ x : ℤ) : ℝ) + c| with hg
  have h1 : |((Formalism.L2.NTheta.wtOf D (Wc D i) τ a - Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ)| ≤ g a + g b := by
    rw [hg]; push_cast
    have := abs_sub (((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) + c) (((Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ) + c)
    rw [show (((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) + c) - (((Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ) + c) =
      ((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) - ((Formalism.L2.NTheta.wtOf D (Wc D i) τ b : ℤ) : ℝ) by ring] at this
    exact this
  have h2 : g a + g b ≤ ∑ x, g x := by
    rw [← Finset.sum_pair hab]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
  have h3 : ∑ x, g x ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize D i := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.wtSize
    exact Finset.single_le_sum (f := fun τ' => ∑ x, |((Formalism.L2.NTheta.wtOf D (Wc D i) τ' x : ℤ) : ℝ) + (((D.hc τ').e i : ℚ) : ℝ)|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
  linarith

theorem log_dimAt_le : ∀ (D : D7) (i : Fin D.R.m) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) (τ : D.what₂.Tau),
    Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L := by
  intro D i L hL τ
  obtain ⟨hf, hs, -, -⟩ := hL

  have hb2 : (2 : ℝ) ≤ Real.exp L := by
    have hr : 1 ≤ D.R.r := by
      have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Formalism.BasicNotions.Ranks.r; omega
    have hfn : 2 ≤ D.R.f := by
      unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
    have hn : 1 ≤ D.R.nV := by unfold Formalism.BasicNotions.Ranks.nV; omega
    have : (2 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := by
      have : 2 ≤ D.R.f * D.R.r * D.R.nV := by
        calc 2 ≤ D.R.f := hfn
          _ = D.R.f * 1 * 1 := by ring
          _ ≤ D.R.f * D.R.r * D.R.nV := by gcongr
      exact_mod_cast this
    linarith
  have hL0 : 0 ≤ L := by
    by_contra h; push_neg at h
    have := Real.exp_lt_exp.2 h; rw [Real.exp_zero] at this; linarith
  set b := Real.exp L with hbdef
  set B := b ^ 2
  have h1B : 1 + B ≤ Real.exp (3 * L) := by
    rw [show 3 * L = L + L + L by ring, Real.exp_add, Real.exp_add, ← hbdef]
    nlinarith
  have hlog1B : Real.log (1 + B) ≤ 3 * L := by
    have := Real.log_le_log (by positivity) h1B
    rwa [Real.log_exp] at this

  set p := ((Wc D i).sig (tauE D τ)).1
  set q := ((Wc D i).sig (tauE D τ)).2
  have hpq : p + q = D.R.r := by
    have hr := D.sp.W_rank ((i:ℕ)+1) (by omega) (by have := i.2; omega)
    rw [← hr]; obtain ⟨e, -⟩ := (D.sp.W_sig ((i:ℕ)+1)) (tauE D τ); simpa using (Fintype.card_congr e).symm
  set κ := Formalism.L2.NTheta.wtOf D (Wc D i) τ
  have hent : ∀ a b, |((κ a - κ b : ℤ) : ℝ)| ≤ B := fun a b => (abs_wt_sub_le D i τ a b).trans (hs i)
  set N1 := ∑ a : Fin p, (Finset.univ.filter (fun j : Fin p => a < j)).card
  set N2 := ∑ a : Fin q, (Finset.univ.filter (fun j : Fin q => a < j)).card
  have w1 := abs_weylDimU_le (fun a => κ (Sum.inl a)) B (fun a b => hent _ _)
  have w2 := abs_weylDimU_le (fun a => κ (Sum.inr a)) B (fun a b => hent _ _)
  have hdim : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ =
      ((Formalism.IndefR.Mult.weylDimU (fun a => κ (Sum.inl a)) : ℚ) : ℝ) *
        ((Formalism.IndefR.Mult.weylDimU (fun a => κ (Sum.inr a)) : ℚ) : ℝ) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt Formalism.IndefR.Mult.dimK; push_cast; rfl
  have habs : |GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ| ≤ (1 + B) ^ (N1 + N2) := by
    rw [hdim, abs_mul, pow_add]
    exact mul_le_mul w1 w2 (abs_nonneg _) (by positivity)
  have hlog : Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ ((N1 + N2 : ℕ) : ℝ) * Real.log (1 + B) := by
    rw [← Real.log_abs]
    rcases eq_or_ne (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) 0 with h0 | h0
    · rw [h0, abs_zero, Real.log_zero]
      have hB0 : (0 : ℝ) ≤ B := sq_nonneg b
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
    · have := Real.log_le_log (abs_pos.2 h0) habs
      rwa [Real.log_pow] at this
  have hN : 2 * (N1 + N2) ≤ D.R.r ^ 2 := by
    have a1 : 2 * N1 ≤ p ^ 2 := two_mul_card_pairs_le p
    have a2 : 2 * N2 ≤ q ^ 2 := two_mul_card_pairs_le q
    have a3 : p ^ 2 + q ^ 2 ≤ (p + q) ^ 2 := by ring_nf; omega
    rw [← hpq]; omega
  have hN' : 2 * ((N1 + N2 : ℕ) : ℝ) ≤ (D.R.r : ℝ) ^ 2 := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ ((N1 + N2 : ℕ) : ℝ) := Nat.cast_nonneg _
  calc Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ ((N1 + N2 : ℕ) : ℝ) * Real.log (1 + B) := hlog
    _ ≤ ((N1 + N2 : ℕ) : ℝ) * (3 * L) := mul_le_mul_of_nonneg_left hlog1B hN0
    _ = 3 / 2 * (2 * ((N1 + N2 : ℕ) : ℝ)) * L := by ring
    _ ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L := by gcongr

end GlobalTheory.OneMeasDim
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExactRatioProof

open scoped InnerProductSpace ComplexConjugate

theorem L1 : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ : ℝ) : ℂ) := GlobalTheory.T.prod_lowestKTypeDims_indep_complexEmbedding

theorem K2aux (D : D7) (T : CoreJ D) (h : LawsJ T) (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ) (hs : GoodEmb T.Q.c s)
    (f : FDSec (T.U ((i : ℕ) + 1) s).X) (W : HSp D) (hV : T.V ((i : ℕ) + 1) s = W) :
    eLpNorm' (fun q : AutQ W => ‖(hV ▸ ((lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) : ℂ) •
      adel (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s)
        (muPin (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (T.mu ((i : ℕ) + 1) s) (T.cE ((i : ℕ) + 1) s)) f) :
          GA D W → ℂ) q.out‖) 2 (muQ1 W) =
      ENNReal.ofReal (lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) *
        petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s))
          (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f := by
  subst hV
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hmu := h.muUnit _ hj s hs
  have hcu := h.cUnit _ hj s hs
  set c := lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) with hcdef
  have hc0 : 0 < c := lieFacZ_pos _ _
  unfold petE
  rw [← Real.enorm_eq_ofReal hc0.le, ← eLpNorm'_const_smul c (by norm_num)]
  refine eLpNorm'_congr_norm_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, norm_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc0, adel_muPin]
  rw [hcu, hmu.2.1]
  simp only [abs_one, one_mul, abs_norm, abs_of_nonneg (ptN_nonneg _ _ _)]
  unfold ptN
  rw [pnorm_eq_of_unit _ _ _ _ (hmu.2.2.2 _)]

theorem K2 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ), GoodEmb T.Q.c s → ∀ (hV : T.V ((i : ℕ) + 1) s = Wc D i) (f : FDSec (T.U ((i : ℕ) + 1) s).X), eLpNorm' (fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) 2 (muQ1 (Wc D i)) = ENNReal.ofReal (lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) * petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s)) (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f :=
  fun D T h i s hs hV f => K2aux D T h i s hs f (Wc D i) hV

theorem K3 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ), GoodEmb T.Q.c s → ∀ f ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.scalarForms T i s, petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s)) (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f ≠ ⊤ := by
  intro D T h i s hs f hf
  obtain ⟨th, hr, -, hdu⟩ := h.dictU _ ⟨Nat.le_add_left _ _, i.2⟩ s hs
  exact petE_ne_top _ _ _ prob_le_one hdu.2.2.2.1 hf

end GlobalTheory.ExactRatioProof
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.DimAtOne

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_le_dimAt : ∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), 1 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ := by
  intro D i τ
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt
  have h := Formalism.L2.NTheta.holOK_kapW (D.hc τ) _ _ (GlobalTheory.AdelicScalar.sig_add i τ)
  have h1 : (1 : ℚ) ≤ dimK _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) τ) :=
    one_le_mul_of_one_le_of_one_le (GlobalTheory.AdelicScalar.one_le_weylDimU _ h.1) (GlobalTheory.AdelicScalar.one_le_weylDimU _ h.2.1)
  exact_mod_cast h1

end GlobalTheory.DimAtOne
end

section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem facBetween_zero_boundAll : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c), ∀ (f : Lt1 Dw) (k : ℕ), FacBetween Xo la f k 0 (boundAll p (rk f) k) ∧ (k < p → FacBetween Xo la f k 0 0) := by
  intro E _ _ _ H Dw l Xo c p _ la f k
  letI := H.starRing
  have hch : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Nonempty (IntegralChartA3 Xo c T io y) :=
    fun T io y => by
      obtain ⟨C, -⟩ := (@GlobalTheory.IntChartExists.intChart_exists E _ _ _ H Dw l Xo c H.starRing).2.2 (fun _ => rfl) T io y
      exact ⟨C⟩
  have hB : ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p),
      0 ≤ nuFacC Ch X f k ∧ nuFacC Ch X f k ≤ ((boundAll p (rk f) k : ℝ) : EReal) ∧ (k < p → nuFacC Ch X f k = 0) := by
    intro T io y Ch X
    have h1 := GlobalTheory.T.formalGroupDeterminantPowDepth_bounds X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) _ k (fgl Ch X) (frame Ch X f)
      (isSatFrame_frame Ch X f)
    refine ⟨h1.1, ?_, fun hk => GlobalTheory.T.formalGroupDeterminantPowDepth_eq_zero_of_lt_prime X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) _ k (fgl Ch X) (frame Ch X f)
      (isSatFrame_frame Ch X f) hk⟩
    have h2 := h1.2.2
    unfold boundAll
    exact h2
  have hmain : ∀ B : ℝ, (∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y)
      (X : ValExt T p), nuFacC Ch X f k ≤ (B : EReal)) → FacBetween Xo la f k 0 B := by
    intro B hb T io e ho y
    refine ⟨?_, fun _ => ?_⟩
    · rw [EReal.coe_zero]
      exact le_nuFac fun Ch X => (hB T io y Ch X).1
    · obtain ⟨Ch⟩ := hch T io y
      obtain ⟨X⟩ := nonempty_valExt_of_overLa la ho
      exact (nuFac_le Ch X f k).trans (hb T io y Ch X)
  refine ⟨hmain _ fun T io y Ch X => (hB T io y Ch X).2.1, fun hk => hmain 0 fun T io y Ch X => ?_⟩
  rw [(hB T io y Ch X).2.2 hk, EReal.coe_zero]

end GlobalTheory.RefSum
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.weil_vacuum_not_mem_augmentation_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    G.M'.vac v ∉ augAt om' v := by
  first | exact @GlobalTheory.InertVacLag.vac_not_mem_augAt | exact GlobalTheory.InertVacLag.vac_not_mem_augAt | (intros; apply GlobalTheory.InertVacLag.vac_not_mem_augAt <;> assumption)
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.exists_totallySplitPrime_upperLevel_unipotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C), LevelHyp M → ∃ g : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g ∧ 3 * r < g ∧ ∀ c, ∀ β ∈ M.upper c, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver (M.comp c).L' g β := by
  first | exact @GlobalTheory.levelHyp_totallySplit_unipotent | exact GlobalTheory.levelHyp_totallySplit_unipotent | (intros; apply GlobalTheory.levelHyp_totallySplit_unipotent <;> assumption)
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.exists_upperArithmeticGroup_unipotentUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (c : C) (g : ℕ), M.UnipotentOver g → ∃ Γo : Subgroup (GL (Fin r) E), (∀ γ ∈ Γo, IsUStab (M.comp c).Gm (M.comp c).L' γ) ∧ (∀ γ ∈ Γo, GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver (M.comp c).L' g γ) ∧ ∀ u : U, u • c = c → M.tr u c ∈ Γo := by
  first | exact @GlobalTheory.UpperArith.upper_subgroup | exact GlobalTheory.UpperArith.upper_subgroup | (intros; apply GlobalTheory.UpperArith.upper_subgroup <;> assumption)
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.isTotallySplitRationalPrime_of_splitsCompletely : ∀ (E : Type) [Field E] [NumberField E] (g : ℕ), SplitsCompletely E g → GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g := by
  first | exact @GlobalTheory.SplitLevelsBall.isTotallySplitPrime_of_splitsCompletely | exact GlobalTheory.SplitLevelsBall.isTotallySplitPrime_of_splitsCompletely | (intros; apply GlobalTheory.SplitLevelsBall.isTotallySplitPrime_of_splitsCompletely <;> assumption)
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.exists_nonzero_boundedSection_shiftedWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (Xa : ArchInM X.toData) (Fl : FlatM X.toData Xa), GlobalTheory.Shares.Margins X.toData Xa → 0 < X.p0 → X.p0 < r → GapsGe X.p0 Xa.L 1 → PairGe Xa.L (1.9 * Xa.T) → GapsGe X.p0 (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 0 → PairGe (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 1 → ∀ s : ℕ, Even s → s ≤ Xa.T → ∀ u : Frame X.Ψ r → ℂ, u ∈ X.SS (deMul X.Ψ r X.p0 s) → (∃ x ∈ X.dom, u x ≠ 0) → ∃ w : Frame X.Ψ r → ℂ, X.IsBddSec ((nd X.toData + 4) • Xa.L - 2 • deMul X.Ψ r X.p0 s) w ∧ ∃ x ∈ X.dom, w x ≠ 0 := by
  first | exact @GlobalTheory.ShareSection.exists_bddSec_shift | exact GlobalTheory.ShareSection.exists_bddSec_shift | (intros; apply GlobalTheory.ShareSection.exists_bddSec_shift <;> assumption)
end

section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.loweredWeight_interpolation_at_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (Xa : ArchInM X.toData) (Fl : FlatM X.toData Xa), GlobalTheory.Shares.Margins X.toData Xa → 0 < X.p0 → X.p0 < r → GapsGe X.p0 Xa.L 1 → PairGe Xa.L (1.9 * Xa.T) → GapsGe X.p0 (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 0 → PairGe (Xa.Fp - kLog X.Ψ r - (nd X.toData + 2) • Xa.L) 1 → ∀ s : ℕ, Even s → s ≤ Xa.T → ∀ u : Frame X.Ψ r → ℂ, u ∈ X.SS (deMul X.Ψ r X.p0 s) → (∃ x ∈ X.dom, u x ≠ 0) → ∀ j : Fin Fl.δ, ∃ F : Frame X.Ψ r → ℂ, DifferentiableOn ℂ F X.dom ∧ (∀ j', F (Fl.xs j') = if j' = j then 1 else 0) ∧ ∀ α : Fin (nd X.toData) → ℕ, ∑ q, α q ≤ Xa.T → (fun x => F x * monoM X.toData Fl.s α x * Fl.w0 x ^ (Xa.T - ∑ q, α q)) ∈ X.SS (Xa.Fp + Xa.T • Xa.L - deMul X.Ψ r X.p0 s) := by
  first | exact @GlobalTheory.LowerInterp.lowered_interp | exact GlobalTheory.LowerInterp.lowered_interp | (intros; apply GlobalTheory.LowerInterp.lowered_interp <;> assumption)
end
