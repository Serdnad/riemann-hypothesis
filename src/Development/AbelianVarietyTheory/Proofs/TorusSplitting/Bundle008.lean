module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle019
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle003
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle002
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfNormLeTwo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PaThDiffLe

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EtaVal.UnitNorm

theorem vV_unit_mul_pow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) (u : Vˣ) (n : ℕ) :
    vV V (algebraMap V (FractionRing V) (u * ϖ ^ n)) = n := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal V).intValuation (u : V) = 1 := by
    rw [HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal (u : V)).1 h u.isUnit
  have h2 : (IsDiscreteValuationRing.maximalIdeal V).intValuation ϖ = WithZero.exp (-1 : ℤ) :=
    HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hϖ.maximalIdeal_eq
  rw [vV, valV, HeightOneSpectrum.valuation_of_algebraMap, map_mul, map_pow, h1, h2, _root_.one_mul,
    ← WithZero.exp_nsmul, WithZero.log_exp]
  simp

theorem norm_map_unit {V F : Type} [CommRing V] [NormedField F] (f : V →+* F) (hf : ∀ a, ‖f a‖ ≤ 1)
    (u : Vˣ) : ‖f u‖ = 1 := by
  have h : ‖f u‖ * ‖f (u⁻¹ : Vˣ)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm (hf _) ?_
  calc (1 : ℝ) = ‖f u‖ * ‖f (u⁻¹ : Vˣ)‖ := h.symm
    _ ≤ ‖f u‖ * 1 := mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)
    _ = ‖f u‖ := _root_.mul_one _

theorem logb_norm_uniformiser : ∀ (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (ϖ : T.V), Irreducible ϖ → ∀ (C : SCF (Formalism.MainNotions.WeightAlgebra.resCh la)) (f : T.V →+* ↥C.S), (∀ a, ‖f a‖ ≤ 1) → -Real.logb (Formalism.MainNotions.WeightAlgebra.resCh la) ‖f ϖ‖ * ((e : ℝ) * Formalism.BasicNotions.eWL K la) = 1 ∧ 0 < Formalism.BasicNotions.eWL K la := by
  intro K _ _ la T io e ho ϖ hϖ C f hf
  have hE := Formalism.MainNotions.ModuliIntegralCharts.H1.H1algLink.eWL_eq la
  refine ⟨?_, hE ▸ Nat.pos_of_ne_zero (Formalism.MainNotions.ModuliIntegralCharts.H1.H1algLink.ramOverZ_ne_zero la)⟩
  have hp : (Formalism.MainNotions.WeightAlgebra.resCh la).Prime := Crude.resCharOf_prime la
  have hv : vLa la ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : K) = Formalism.BasicNotions.eWL K la := by
    rw [hE]; exact Crude.crv_vLa_char la
  have hn := C.norm_p
  generalize Formalism.BasicNotions.eWL K la = E at hv ⊢
  have h0 : ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : T.V) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
  have h1 := vV_unit_mul_pow hϖ u n
  rw [← hu, map_natCast, ← map_natCast io, ho.2, hv] at h1
  have h2 : ((e : ℝ) * E) = n := by exact_mod_cast h1
  have h3 : ‖f ϖ‖ ^ n = ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : ℝ)⁻¹ := by
    rw [← hn, ← map_natCast f, hu, map_mul, norm_mul, norm_map_unit f hf u, _root_.one_mul, map_pow, norm_pow]
  have hp1 : (1 : ℝ) < ((Formalism.MainNotions.WeightAlgebra.resCh la : ℕ) : ℝ) := by exact_mod_cast hp.one_lt
  have h4 := congrArg (Real.logb (Formalism.MainNotions.WeightAlgebra.resCh la)) h3
  rw [Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one hp1] at h4
  rw [h2]
  linarith

end GlobalTheory.EtaVal.UnitNorm
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaAn

theorem page_rows : ∀ (D : D7) (large₂ : SizeData₂ D) (CA : ℝ), WeightAlgebra.ParA large₂ CA → SizesAt large₂ → 2 ≤ large₂.sc.L ∧ Real.log D.R.r ≤ large₂.sc.L ∧ Real.log D.host.rdE ≤ 2 * large₂.sc.L ∧ Real.log D.R.f ≤ 2 * large₂.sc.L ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧ 16 ≤ D.R.f := by
  intro D large₂ CA hA hS
  have hm4 := host_m_pow_four_le_f hS
  rw [hostSize_f] at hm4
  have hm2 := D.R.two_le_m
  have h16 : 16 ≤ D.R.f := by
    have : 2 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4
    omega
  have hC : SizeCond large₂ := hS.2.2.2.2.2.1
  have hQ : SizeQD large₂ := hS.2.2.2.2.2.2.1
  have hrd1 : 1 ≤ D.host.rdE := hQ.2.2.2.2.2.2.1
  have hrd2 : D.host.rdE ≤ (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) := hQ.2.2.2.2.2.2.2
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by
    have h0 : D.host.q * D.host.d ≠ 0 := by
      intro h
      have h' : (D.host.q : ℝ) * D.host.d = 0 := by exact_mod_cast h
      rw [h', Real.sqrt_zero, mul_zero] at hrd2
      linarith
    have : 1 ≤ D.host.q * D.host.d := Nat.one_le_iff_ne_zero.mpr h0
    exact_mod_cast this
  have hsq : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hc : szCond large₂ = (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by
    unfold szCond; ring
  have hfn : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hfc : (D.R.f : ℝ) ≤ szCond large₂ := by
    have h4 : ((4 * D.R.n : ℕ) : ℝ) ≤ ((D.host.QS * D.host.q * D.host.d : ℕ) : ℝ) := Nat.cast_le.2 D.host.four_ord_le_condN
    push_cast at h4
    rw [hc, hfn]; nlinarith
  have hrc : D.host.rdE ≤ szCond large₂ := by
    rw [hc]
    have : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
        (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have h0 : 0 ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by positivity
    nlinarith
  have hf1 : (1 : ℝ) ≤ D.R.f := by linarith
  have hc1 : 1 ≤ szCond large₂ := le_trans hf1 hfc
  have hrt : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have ht3 : (3 : ℝ) ≤ D.R.t := by
    have : 3 ≤ D.R.t := by omega
    exact_mod_cast this
  have hrt' : (D.R.r : ℝ) ≤ D.R.t := by
    have : D.R.r ≤ D.R.t := by omega
    exact_mod_cast this
  have hr1' : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hlt : 1 ≤ Real.log D.R.t := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlc : 0 ≤ Real.log (szCond large₂) := Real.log_nonneg hc1
  have hmain : 36 * Real.log (szCond large₂) + 150 * Real.log D.R.t ≤ large₂.sc.L / 2 := by
    have h1 : Real.sqrt large₂.sc.b = Real.exp (large₂.sc.L / 2) := by
      unfold Scale.b
      rw [Real.exp_half]
    have h2 : szCond large₂ ^ 36 * (D.R.t : ℝ) ^ 150 ≤ Real.exp (large₂.sc.L / 2) := h1 ▸ hC
    have hp : 0 < szCond large₂ ^ 36 := by positivity
    have hp' : 0 < (D.R.t : ℝ) ^ 150 := by positivity
    have h3 := Real.log_le_log (mul_pos hp hp') h2
    rw [Real.log_exp, Real.log_mul hp.ne' hp'.ne', Real.log_pow, Real.log_pow] at h3
    exact_mod_cast h3
  have a1 : Real.log D.R.r ≤ Real.log D.R.t := Real.log_le_log (by linarith) hrt'
  have a2 : Real.log D.host.rdE ≤ Real.log (szCond large₂) := Real.log_le_log (by linarith) hrc
  have a3 : Real.log D.R.f ≤ Real.log (szCond large₂) := Real.log_le_log (by linarith) hfc
  refine ⟨by linarith, by linarith, by linarith, by linarith, hA.2.2.2.2.1, h16⟩

end GlobalTheory.EtaAn
end

section

open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.ThetaTorus

theorem gSup_holds : GSupStatement := gSup GlobalTheory.packingCount

theorem propA_holds : PropAStatement := propA GlobalTheory.packingCount GlobalTheory.gaussTail_of_card_le

theorem dim_holds : DimStatement := dim

theorem J_holds : JStatement :=
  jOf GlobalTheory.ext_all_inputs GlobalTheory.T.greedy_splitting_principal_torus_exists GlobalTheory.charStatement_holds
    (colTorus GlobalTheory.ext_all_inputs propA_holds gSup_holds)
    (colAbel GlobalTheory.ext_all_inputs propA_holds gSup_holds)
    (colEmpty GlobalTheory.ext_all_inputs propA_holds gSup_holds)

theorem N_holds : NStatement := lemmaN dim_holds

theorem I_holds : IStatement := iOf J_holds N_holds

end GlobalTheory.ThetaTorus
end
