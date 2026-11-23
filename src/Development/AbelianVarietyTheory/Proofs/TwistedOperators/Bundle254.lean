module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Formalism.SatakeDualWeyl.Bundle001
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.Bundle005
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle240
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle231
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationLevelProjectorFixed
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
public import Formalism.SatakeDualWeyl.StatementG
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.Bundle014
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

theorem conj_LvTw_div_dLoc_inert : ∀ (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w) → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 → (B w).map star = B w → (m w : ℂ) = (-1) ^ D.R.nV → quadSign D v = -1 → starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) = eulerFac (B w) (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.t + 1))⁻¹) * ∏ j ∈ Finset.range D.R.r, (1 - (-(qV D.host.F v : ℂ)) ^ j * (((star (m w) : ℂˣ) : ℂ) * ((qV D.host.F v : ℂ) ^ (D.R.r + D.R.t))⁻¹)) := by
  intro D B m v w hv hq hB hm hs
  set q : ℕ := Ideal.absNorm v.asIdeal with hqdef
  have hqV : qV D.host.F v = q := rfl
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (GlobalTheory.LFun.one_lt_absNorm v).ne_bot
  have hstar : ((star (m w) : ℂˣ) : ℂ) = (-1) ^ D.R.nV := by
    rw [Units.coe_star, hm]; simp
  have hinv : ((m w : ℂ))⁻¹ = (-1) ^ D.R.nV := by rw [hm, ← inv_pow, inv_neg, inv_one]
  have hnp : npow v (-(2 * ((1 + (D.R.t : ℂ)) / 2))) = ((q : ℂ) ^ (D.R.t + 1))⁻¹ := by
    rw [npow, show -(2 * ((1 + (D.R.t : ℂ)) / 2)) = -((D.R.t + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.cpow_neg, Complex.cpow_natCast]
  rw [LvTw_inert B m hv hq, hnp, hinv, hstar, hqV, map_div₀, Complex.conj_ofReal]
  have hx : starRingEnd ℂ ((-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹) =
      (-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹ := by simp
  have hconjE : starRingEnd ℂ (eulerFac (B w) ((-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹)) =
      eulerFac (B w) ((-1 : ℂ) ^ D.R.nV * ((q : ℂ) ^ (D.R.t + 1))⁻¹) := by
    conv_rhs => rw [← hB]
    simp only [eulerFac, eulerPoly, map_inv₀, map_multiset_prod, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, map_sub, map_one, map_mul, Units.coe_star, hx]
    rfl
  rw [hconjE, div_eq_mul_inv]
  congr 1
  have hqt : ∀ i : ℕ, quadTerm D v i = (-1 : ℝ) ^ i / (q : ℝ) ^ i := by
    intro i; rw [quadTerm, hs]
  have hd : ((dLoc D v : ℝ) : ℂ)⁻¹ = ∏ i ∈ Finset.Ioc D.R.t (D.R.r + D.R.t), (1 - (-1 : ℂ) ^ i / (q : ℂ) ^ i) := by
    rw [dLoc, Complex.ofReal_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr (by rfl) fun i _ => ?_
    rw [Complex.ofReal_inv, inv_inv, hqt]
    push_cast; ring
  rw [hd]
  have key : ∀ a j : ℕ, (-1 : ℂ) ^ a / (q : ℂ) ^ a = (-(q : ℂ)) ^ j * ((-1 : ℂ) ^ (a + j) * ((q : ℂ) ^ (a + j))⁻¹) := by
    intro a j
    calc (-1 : ℂ) ^ a / (q : ℂ) ^ a = ((-1 : ℂ) ^ j * (-1) ^ j) * ((-1 : ℂ) ^ a / (q : ℂ) ^ a) * ((q : ℂ) ^ j * ((q : ℂ) ^ j)⁻¹) := by
          rw [← mul_pow, neg_one_mul, neg_neg, one_pow, mul_inv_cancel₀ (pow_ne_zero _ hq0)]; ring
      _ = _ := by rw [neg_pow, pow_add, pow_add, mul_inv]; ring
  refine Finset.prod_nbij' (fun i => D.R.r + D.R.t - i) (fun j => D.R.r + D.R.t - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi; rw [Finset.mem_Ioc] at hi; rw [Finset.mem_range]; omega
  · intro j hj; rw [Finset.mem_range] at hj; rw [Finset.mem_Ioc]; omega
  · intro i hi; rw [Finset.mem_Ioc] at hi; omega
  · intro j hj; rw [Finset.mem_range] at hj; omega
  · intro i hi
    have hi' := Finset.mem_Ioc.1 hi
    have e : D.R.nV = i + (D.R.r + D.R.t - i) := by show D.R.r + D.R.t = _; omega
    rw [e, key i (D.R.r + D.R.t - i), ← e]
    show _ = 1 - _ * (_ * ((q : ℂ) ^ (D.R.r + D.R.t))⁻¹)
    rfl

end GlobalTheory.FinZeta
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocZetaSplit

theorem prod_map_conj_eq (A : Multiset ℂˣ) (hA : A.map star = A.map (·⁻¹)) (f : ℂ → ℂ) :
    (A.map fun b : ℂˣ => f (starRingEnd ℂ (b : ℂ))).prod = (A.map fun b : ℂ ˣ => f ((b : ℂ)⁻¹)).prod := by
  have h := congrArg (fun M : Multiset ℂˣ => (M.map fun b : ℂˣ => f (b : ℂ)).prod) hA
  simpa [Multiset.map_map, Function.comp_def, Units.coe_star, Units.val_inv_eq_inv_val] using h

theorem conj_LvTw_div_dLoc : ∀ (D : D7) (B : Fam D.host.E) (m : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)), w ≠ w' → (∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) = v ↔ u = w ∨ u = w') → Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal → Ideal.absNorm w'.asIdeal = Ideal.absNorm v.asIdeal → B w' = (B w).map (·⁻¹) → (B w).map star = (B w).map (·⁻¹) → m w * m w' = 1 → ‖(m w : ℂ)‖ = 1 → quadSign D v = 1 → starRingEnd ℂ (LvTw B m v ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v : ℂ)) = eulerFac ((B w).map (star (m w) * ·)) (npow w (-((1 + (D.R.t : ℂ)) / 2))) * eulerFac ((B w).map fun β => (star (m w) * β)⁻¹) (npow w (-((1 + (D.R.t : ℂ)) / 2))) * ∏ i ∈ Finset.Ioc D.R.t (D.R.r + D.R.t), (1 - ((qV D.host.E w : ℂ) ^ i)⁻¹) := by
  intro D B m v w w' hne hv hqw hqw' hB' hstar hm1 hnorm hsign
  classical
  set s : ℂ := (1 + (D.R.t : ℂ)) / 2 with hs
  set X : ℂ := npow w (-s) with hXdef
  set μ : ℂ := (m w : ℂ) with hμ
  have hX : starRingEnd ℂ X = X := by
    have : X = (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (-((1 + (D.R.t : ℝ)) / 2)) : ℝ) := by
      rw [hXdef, npow, Complex.ofReal_cpow (by positivity)]
      push_cast
      rfl
    rw [this, Complex.conj_ofReal]
  have hX' : npow w' (-s) = X := by rw [hXdef, npow, npow, hqw, hqw']
  have hinv : ((m w' : ℂ))⁻¹ = μ := inv_eq_of_mul_eq_one_left (by rw [hμ, ← Units.val_mul, hm1, Units.val_one])
  have hμc : starRingEnd ℂ μ = μ⁻¹ := (Complex.inv_eq_conj hnorm).symm
  have hμc' : starRingEnd ℂ μ⁻¹ = μ := by rw [map_inv₀, hμc, inv_inv]
  have e : Formalism.L2.Host.aboveF (L := D.host.E) D.host.F v = {w, w'} := by ext u; simp [mem_aboveF, hv]
  have hL : LvTw B m v s = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod *
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [LvTw_eq, e, Finset.prod_pair hne, hB', Multiset.map_map, hX', hinv]
    simp only [Function.comp_def, Units.val_inv_eq_inv_val]
    rfl
  have hc1 : starRingEnd ℂ ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod =
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    have := prod_map_conj_eq (B w) hstar (fun z => (1 - z * μ * X)⁻¹)
    simp only [Function.comp_def, map_inv₀, map_sub, map_one, map_mul, hμc', hX]
    exact this
  have hc2 : starRingEnd ℂ ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod =
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    have := prod_map_conj_eq (B w) hstar (fun z => (1 - z⁻¹ * μ⁻¹ * X)⁻¹)
    simp only [inv_inv] at this
    simp only [Function.comp_def, map_inv₀, map_sub, map_one, map_mul, hμc, hX]
    exact this
  have hstarμ : ((star (m w) : ℂˣ) : ℂ) = μ⁻¹ := by rw [Units.coe_star, ← hμc]; rfl
  have hr1 : eulerFac ((B w).map (star (m w) * ·)) X = ((B w).map fun b : ℂˣ => (1 - (b : ℂ) * μ⁻¹ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_mul, hstarμ]
    ring
  have hr2 : eulerFac ((B w).map fun β => (star (m w) * β)⁻¹) X =
      ((B w).map fun b : ℂˣ => (1 - (b : ℂ)⁻¹ * μ * X)⁻¹).prod := by
    rw [eulerFac_eq_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
    simp only [Function.comp_apply, Units.val_inv_eq_inv_val, Units.val_mul, hstarμ, mul_inv, inv_inv]
    ring
  have hd : (dLoc D v : ℂ) = (∏ i ∈ Finset.Ioc D.R.t (D.R.r + D.R.t), (1 - ((qV D.host.E w : ℂ) ^ i)⁻¹))⁻¹ := by
    rw [← Finset.prod_inv_distrib, dLoc]
    push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [quadTerm, hsign, qV, hqw]
  rw [map_div₀, Complex.conj_ofReal, hd, div_inv_eq_mul, hL, map_mul, hc1, hc2, hr1, hr2]
  ring

end GlobalTheory.LocZetaSplit
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HostAAPartition

theorem host_AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h0
    have h1 := D.host.𝔟_spec.1
    rw [h0, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1
  have hc : D.host.ccE ≠ ⊥ := by
    unfold Formalism.BasicNotions.Host.ccE
    rw [Ne, Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 D.host.K) (𝓞 D.host.E))]
    exact D.host.ccK_ne_bot
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  exact mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hc)
    (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hb))

theorem host_AA_partition : ∀ (D : D7), ∃ (m : ℕ) (a c : Fin m → D.host.E), (∀ i, a i ∈ D.host.AA) ∧ (∀ i, ∀ x ∈ D.host.AA, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧ ∑ i, a i * c i = 1 := by
  intro D
  set I := D.host.AA with hI
  have hne : I ≠ 0 := host_AA_ne_zero D
  have h1 : (1 : D.host.E) ∈ I * I⁻¹ := by
    rw [mul_inv_cancel₀ hne]
    exact FractionalIdeal.one_mem_one _
  have key : ∀ z ∈ I * I⁻¹, ∃ (m : ℕ) (a c : Fin m → D.host.E), (∀ i, a i ∈ I) ∧
      (∀ i, ∀ x ∈ I, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧ ∑ i, a i * c i = z := by
    intro z hz
    refine FractionalIdeal.mul_induction_on (C := fun z => ∃ (m : ℕ) (a c : Fin m → D.host.E),
      (∀ i, a i ∈ I) ∧ (∀ i, ∀ x ∈ I, ∃ b : 𝓞 D.host.E, (b : D.host.E) = c i * x) ∧
        ∑ i, a i * c i = z) hz ?_ ?_
    · intro u hu v hv
      refine ⟨1, fun _ => u, fun _ => v, fun _ => hu, ?_, by simp⟩
      intro _ x hx
      have hvx : v * x ∈ I⁻¹ * I := FractionalIdeal.mul_mem_mul hv hx
      rw [inv_mul_cancel₀ hne, FractionalIdeal.mem_one_iff] at hvx
      obtain ⟨b, hb⟩ := hvx
      exact ⟨b, hb⟩
    · rintro u v ⟨m, a, c, ha, hc, rfl⟩ ⟨n, a', c', ha', hc', rfl⟩
      refine ⟨m + n, Fin.append a a', Fin.append c c', ?_, ?_, ?_⟩
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa using ha j
        · simpa using ha' j
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa using hc j
        · simpa using hc' j
      · rw [Fin.sum_univ_add]
        simp
  exact key 1 h1

end GlobalTheory.HostAAPartition
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
open Formalism.IndefR.CxPass Formalism.IndefR.CxPass.LevelOperators

noncomputable section

namespace GlobalTheory.KerProjGood

theorem starProjection_comm {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (S : Submodule ℂ V) (T : V →ₗ[ℂ] V) (hT : ∀ u ∈ S, T u ∈ S) (hTa : ∀ u ∈ S, LinearMap.adjoint T u ∈ S) (z : V) :
    (S.starProjection (T z) : V) = T (S.starProjection z) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hT _ (Submodule.coe_mem _)) fun w hw => ?_
  rw [← map_sub, ← LinearMap.adjoint_inner_right]
  have h := Submodule.sub_starProjection_mem_orthogonal (K := S) z
  rw [inner_eq_zero_symm]
  exact h _ (hTa w hw)

end GlobalTheory.KerProjGood


open GlobalTheory.KerProjGood in
theorem GlobalTheory.kerProj_goodL : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j, ∀ y ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j, ((LinearMap.ker ((R.toCx3 F).θ' j A3.A.fam.μ0)).starProjection y : (R.toCx3 F).FLC j A3.A.fam.μ0) ∈ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hC _ _ hG j y hy
  have hM := hC.base.models
  have hK := RealDat3.kFormL_of (F := F) hM
  have hJ := RealDat3.jIsoL_of (F := F) hM
  set X := R.toCx3 F with hX
  set t := A3.A.fam.μ0
  have sp := lift_embeddings_span hK j t
  have jr : ∀ (g : G) x, X.jL j t ((A3.fam3.F.L j t).r g x) = X.opLC j t (Sum.inr g) (X.jL j t x) :=
    fun g x => X.jL_opL hK j t (Sum.inr g) x

  have hker : ∀ (g : G), ∀ u ∈ LinearMap.ker (X.θ' j t), X.opLC j t (Sum.inr g) u ∈ LinearMap.ker (X.θ' j t) := by
    intro g u hu
    rw [LinearMap.mem_ker] at hu ⊢
    have h := congrArg (fun f => f u) (theta_rho (r := (A3.fam3.F.L j t).r) (ρ := fun g => X.opLC j t (Sum.inr g))
      sp jr (fun g x => hG.2 j t g x) g)
    simp only [LinearMap.comp_apply] at h
    rw [h, hu, map_zero]
  have hadj : ∀ g : G, LinearMap.adjoint (X.opLC j t (Sum.inr g)) = X.opLC j t (Sum.inr g⁻¹) := fun g =>
    (X.opLC_adjoint hK F.cv hJ j t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.ok2.lifts j t).act g f f').symm
  have hcomm : ∀ (g : G) z, ((LinearMap.ker (X.θ' j t)).starProjection (X.opLC j t (Sum.inr g) z) : X.FLC j t) =
      X.opLC j t (Sum.inr g) ((LinearMap.ker (X.θ' j t)).starProjection z) := fun g z =>
    starProjection_comm _ _ (hker g) (fun u hu => by rw [hadj]; exact hker g⁻¹ u hu) z
  have hrange : U2.goodL A3 X F.P0 F.ψ0 F.P1 F.ψ1 j = LinearMap.range (opV A3.fam3.base3.v0.embedding
      (fun g => X.opLC j t (Sum.inr g)) (goodAt (A3.fam3.F.lvlA F.P0 F.ψ0).X (A3.fam3.F.lvlA F.P0 F.ψ0).P
        (A3.fam3.F.lvlA F.P0 F.ψ0).ψ)) := by
    show X.goodPartComplexPoints F.cv false j t = _
    unfold CxData.goodPartComplexPoints
    rw [show F.cv.v0L X.zs false j t = BlockGood.goodR (A3.fam3.F.L j t) (A3.fam3.F.lvlA F.P0 F.ψ0) from rfl, goodR_eq]
    conv_rhs => rw [LinearMap.range_eq_map, ← sp, Submodule.map_span]
    congr 1
    ext u
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨X.jL j t x, ⟨x, rfl⟩, (j_opF jr _ x).symm⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, j_opF jr _ x⟩
  rw [hrange] at hy ⊢
  obtain ⟨z, rfl⟩ := hy
  refine ⟨(LinearMap.ker (X.θ' j t)).starProjection z, ?_⟩

  simp only [opV, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hcomm]
  exact Finset.sum_congr rfl fun g _ => congrArg _ (hcomm g z).symm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.FrameAdjAdd

theorem frMapAdj_add_isIntM_redM : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (x y : WO S T),
  IsIntM (frMapAdj S T βS βT x) → IsIntM (frMapAdj S T βS βT y) →
  IsIntM (frMapAdj S T βS βT (x + y)) ∧
  ∀ PP : Pl D.host.E, redM PP (frMapAdj S T βS βT (x + y)) = redM PP (frMapAdj S T βS βT x) + redM PP (frMapAdj S T βS βT y) := by
  intro D S T βS βT x y hx hy
  have hadd : frMapAdj S T βS βT (x + y) = frMapAdj S T βS βT x + frMapAdj S T βS βT y := by
    unfold frMapAdj
    rw [Matrix.map_add (⇑(cA D)) (map_add (cA D)), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.map_add (⇑(toEAf D)) (map_add (toEAf D)), Matrix.mul_add, Matrix.add_mul]
  have hI : IsIntM (frMapAdj S T βS βT (x + y)) := by
    intro i j
    rw [hadd]
    exact add_mem (hx i j) (hy i j)
  refine ⟨hI, fun PP => ?_⟩
  ext i j
  have h1 := hI i j
  have h2 := hx i j
  have h3 := hy i j
  simp only [redM, Matrix.add_apply, dif_pos h1, dif_pos h2, dif_pos h3]
  rw [← RingHom.map_add (f := _)]
  congr 1
  apply Subtype.ext
  simp [hadd]

end GlobalTheory.FrameAdjAdd
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)
open Classical

namespace GlobalTheory.TraceFrames

theorem hO_eq_trace_mul {D : D7} (S T : HSp D) (k y : WO S T) :
    hO S T y k = Matrix.trace (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
      ((k : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose) (T.gram.map (incA D))
      * (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by
  simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]; enter [2, c]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]




theorem toEAf_hO_eq_trace_frames {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Datum.EAf D))
    (βT : GL (Fin T.rank) (Datum.EAf D)) (k y : WO S T) :
    toEAf D (hO S T y k) = Matrix.trace (frMapAdj S T βS βT k * frMapO S T βS βT y) := by
  set X₀ : Matrix (Fin S.rank) (Fin T.rank) (AE D) := HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
      ((k : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose) (T.gram.map (incA D)) with hX
  set Y₀ : Matrix (Fin T.rank) (Fin S.rank) (AE D) := y with hY
  set A : Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D) := (βS⁻¹).val with hA
  set A' : Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D) := βS.val with hA'
  set B : Matrix (Fin T.rank) (Fin T.rank) (Datum.EAf D) := βT.val with hB
  set B' : Matrix (Fin T.rank) (Fin T.rank) (Datum.EAf D) := (βT⁻¹).val with hB'
  set Xf : Matrix (Fin S.rank) (Fin T.rank) (Datum.EAf D) := X₀.map (toEAf D) with hXf
  set Yf : Matrix (Fin T.rank) (Fin S.rank) (Datum.EAf D) := Y₀.map (toEAf D) with hYf
  have hBB : HMul.hMul B B' = (1 : Matrix (Fin T.rank) (Fin T.rank) (Datum.EAf D)) := Units.mul_inv βT
  have hAA : HMul.hMul A' A = (1 : Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D)) := Units.mul_inv βS
  have h1 : frMapAdj S T βS βT k = HMul.hMul (HMul.hMul A Xf) B := rfl
  have h2 : frMapO S T βS βT y = HMul.hMul (HMul.hMul B' Yf) A' := rfl
  have h4 : HMul.hMul Xf Yf = (HMul.hMul X₀ Y₀ : Matrix (Fin S.rank) (Fin S.rank) (AE D)).map (toEAf D) :=
    (Matrix.map_mul).symm
  have h3 : (HMul.hMul (HMul.hMul (HMul.hMul A Xf) B) (HMul.hMul (HMul.hMul B' Yf) A') :
      Matrix (Fin S.rank) (Fin S.rank) (Datum.EAf D)) = HMul.hMul A (HMul.hMul (HMul.hMul Xf Yf) A') := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B B', hBB, Matrix.one_mul]
  rw [h1, h2, h3, Matrix.trace_mul_comm, Matrix.mul_assoc, hAA, Matrix.mul_one, h4, hO_eq_trace_mul]

  simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]
  rfl

end GlobalTheory.TraceFrames
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.surjective_reduction_onto_finiteLevelGroup : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ γ : G0g D.nd, ∃ k ∈ X.B.I.Kset, cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) = γ := by
  first | exact @GlobalTheory.SeeMatchOnto.onto | exact GlobalTheory.SeeMatchOnto.onto | (intros; apply GlobalTheory.SeeMatchOnto.onto <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.reduction_conjugated_unitary_element_eq_one_iff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, (cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) = 1 ↔ k ∈ X.B.I.Kg X.B.g) := by
  first | exact @GlobalTheory.KapRed.red_kap_eq_one_iff | exact GlobalTheory.KapRed.red_kap_eq_one_iff | (intros; apply GlobalTheory.KapRed.red_kap_eq_one_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conj_translatedRowEvaluation_levelProjector_fixed : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → LevelMatchA R F X h t → ∀ S ∈ EP R F, ∀ y : ∀ τ, ↥(GlobalTheory.RowEvalHH.Wsub R X c τ), X.B.Re (GlobalTheory.RowEvalHH.evF R X h t c S y) = GlobalTheory.RowEvalHH.evF R X h t c S y := by
  first | exact @GlobalTheory.RowEvalHH.Re_evF | exact GlobalTheory.RowEvalHH.Re_evF | (intros; apply GlobalTheory.RowEvalHH.Re_evF <;> assumption)
end
