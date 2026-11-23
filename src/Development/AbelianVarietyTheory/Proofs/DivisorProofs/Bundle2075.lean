module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1976
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle052
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle054
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle252
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle003
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SmulOneSecEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv.RealChar

variable {D : D7} {S T : HSp D} (C : GlobalTheory.Ker.Ctx S T)

theorem xB_mem_dom {B : C.Bas} (hB : C.IsB B) : C.xB B ∈ C.X.dom :=
  GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C hB)

theorem Th_ne_zero {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ)
    (h0 : φ ≠ 0) : C.Th x φ ≠ 0 := by
  intro h
  obtain ⟨l1, l2, -⟩ := GlobalTheory.Ker.Ctx.th_laws D S T C x hx φ hφ
  have h3 : GlobalTheory.SW.IsSB ((0 : ℂ) • φ) := by
    rw [zero_smul]
    exact GlobalTheory.SW.isSB_zero
  refine h0 (((l1 _ h3).2 ?_).trans (zero_smul ℂ φ))
  rw [l2, h, smul_zero]

theorem Th_zero {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) : C.Th x (0 : TF S.rank C.g) = 0 := by
  have h := (GlobalTheory.Ker.Ctx.th_laws D S T C x hx 0 GlobalTheory.SW.isSB_zero).2.1 0
  rwa [zero_smul, zero_smul] at h

theorem scalar_eq {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : GlobalTheory.Ker.IsWeak C.ψ S T om)
    {u : GA D T} {B B' : C.Bas} (hB : C.IsB B) (hB' : C.IsB B') {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ)
    (h0 : φ ≠ 0) {c c' : ℂ} (hc' : ‖c'‖ = 1)
    (e : om (1, u) (C.Th (C.xB B) φ) = c • C.Th (C.xB (C.mvB u B)) φ)
    (e' : om (1, u) (C.Th (C.xB B') φ) = c' • C.Th (C.xB (C.mvB u B')) φ) : c = c' := by
  obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := GlobalTheory.Ker.ScalarProduct.ip_basic D S T C
  have hmv : ∀ A, C.IsB A → C.IsB (C.mvB u A) := fun A hA =>
    (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 A hA).2.2.2.2.2 u).1
  have hth : ∀ A, C.IsB A → C.IsTh (C.Th (C.xB A) φ) := fun A hA =>
    (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ (xB_mem_dom C hA) φ hφ).1.1
  have hd : dbl C.X C.bas C.idx φ φ 0 ≠ 0 := by
    intro hc
    have h1 := GlobalTheory.AdTh.Overlap.ipO_Th C hμ (xB_mem_dom C hB) (xB_mem_dom C hB) hφ hφ
    rw [hc, zero_mul] at h1
    exact Th_ne_zero C (xB_mem_dom C hB) hφ h0 ((hip μ 𝓕 hμ _ (hth B hB)).2.1 h1)
  have hk : kZero C.X C.idx (C.xB B) (C.xB B') (0 : Fin S.rank → Fin C.g → ℂ) 0 ≠ 0 := by
    rw [GlobalTheory.AdTh.Overlap.kZero_zero]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero (pow_ne_zero _ (mul_ne_zero
      (DblPoint.det_aLin_ne_zero (xB_mem_dom C hB) (xB_mem_dom C hB') τ)
      (DblPoint.det_aAnti_ne_zero (xB_mem_dom C hB) (xB_mem_dom C hB') τ)))
  have h1 := ((hip μ 𝓕 hμ _ (hth B hB)).2.2.2 _ (hth B' hB')).2.2.2.2.2 om hom (1, u)
  have h2 : GlobalTheory.Ker.ipO μ 𝓕 (c • C.Th (C.xB (C.mvB u B)) φ) (c' • C.Th (C.xB (C.mvB u B')) φ) =
      c * conj c' * GlobalTheory.Ker.ipO μ 𝓕 (C.Th (C.xB (C.mvB u B)) φ) (C.Th (C.xB (C.mvB u B')) φ) := by
    rw [GlobalTheory.Ker.ipO, GlobalTheory.Ker.ipO, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  rw [e, e', h2, GlobalTheory.AdTh.Overlap.ipO_Th C hμ (xB_mem_dom C (hmv B hB)) (xB_mem_dom C (hmv B' hB')) hφ hφ,
    GlobalTheory.AdTh.Overlap.ipO_Th C hμ (xB_mem_dom C hB) (xB_mem_dom C hB') hφ hφ,
    GlobalTheory.AdTh.Overlap.kZero_mvB C hB u] at h1
  have h3 : c * conj c' = 1 := mul_right_cancel₀ (mul_ne_zero hd hk) (h1.trans (one_mul _).symm)
  have h4 : c' * conj c' = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc']
    simp
  linear_combination c' * h3 - c * h4

end GlobalTheory.FrameEquiv.RealChar


open GlobalTheory.FrameEquiv.RealChar in

theorem GlobalTheory.FrameEquiv.exists_real_character : ∀ (D : D7) (S T : HSp D) (C : GlobalTheory.Ker.Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak C.ψ S T om → ∃ χ : GA D T → ℂ, (∀ u ∈ GinfC T, ‖χ u‖ = 1) ∧ (∀ u ∈ GinfC T, ∀ u' ∈ GinfC T, χ (u * u') = χ u * χ u') ∧ ∀ u ∈ GinfC T, ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, GlobalTheory.SW.IsSB φ → om (1, u) (C.Th (C.xB B) φ) = χ u • C.Th (C.xB (C.mvB u B)) φ := by
  intro D S T C om hom
  by_cases hex : ∃ φ₀ : TF S.rank C.g, GlobalTheory.SW.IsSB φ₀ ∧ φ₀ ≠ 0
  swap
  · refine ⟨fun _ => 1, fun _ _ => norm_one, fun _ _ _ _ => (mul_one _).symm, fun u _ B hB φ hφ => ?_⟩
    have h0 : φ = 0 := by
      by_contra h
      exact hex ⟨φ, hφ, h⟩
    have hmv : C.IsB (C.mvB u B) := (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.2.2.2.2 u).1
    rw [h0, Th_zero C (xB_mem_dom C hB), Th_zero C (xB_mem_dom C hmv), map_zero, smul_zero]
  obtain ⟨φ₀, s₀, n₀⟩ := hex
  obtain ⟨⟨B₀, hB₀⟩, hJ⟩ := GlobalTheory.Ker.onBasis_frame_period D S T C
  have hr := GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hom 1 (one_mem _)
  choose! χ hχ1 hχ using fun u hu => hr u hu B₀ hB₀
  have main : ∀ u ∈ GinfC T, ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, GlobalTheory.SW.IsSB φ →
      om (1, u) (C.Th (C.xB B) φ) = χ u • C.Th (C.xB (C.mvB u B)) φ := fun u hu B hB φ hφ => by
    obtain ⟨c, -, hc⟩ := hr u hu B hB
    rw [← scalar_eq C hom hB hB₀ s₀ n₀ (hχ1 u hu) (hc φ₀ s₀) (hχ u hu φ₀ s₀)]
    exact hc φ hφ
  refine ⟨χ, hχ1, fun u hu u' hu' => ?_, main⟩
  have h1 := main (u * u') (mul_mem hu hu') B₀ hB₀ φ₀ s₀
  obtain ⟨hm, hmul, -⟩ := (hJ B₀ hB₀).2.2.2.2.2 u'
  have e : ((1, u * u') : GA D S × GA D T) = (1, u) * (1, u') := by simp
  rw [e, map_mul, mul_apply_eq_comp, main u' hu' B₀ hB₀ φ₀ s₀, map_smul, main u hu _ hm φ₀ s₀, hmul u,
    smul_smul] at h1
  have hne := Th_ne_zero C (xB_mem_dom C ((hJ _ hm).2.2.2.2.2 u).1) s₀ n₀
  rw [mul_comm]
  exact (smul_left_injective ℂ hne h1).symm
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis
open scoped ComplexConjugate

variable {D : D7}

theorem hasDerivAt_line_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (E Φ : V → ℂ)
    (hE : Differentiable ℝ E) (hΦ : Differentiable ℝ Φ) (K : ℂ) (z v : V) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * K) * (E (z + t • v) * Φ (z + t • v)))
      (K * (E z * Φ z) + (fderiv ℝ E z v * Φ z + E z * fderiv ℝ Φ z v)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * K)) K 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const K).cexp
    simpa using this
  have hl : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hE' : HasDerivAt (fun t : ℝ => E (z + t • v)) (fderiv ℝ E z v) 0 := by
    have := (hE (z + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rwa [zero_smul, add_zero] at this
  have hΦ' : HasDerivAt (fun t : ℝ => Φ (z + t • v)) (fderiv ℝ Φ z v) 0 := by
    have := (hΦ (z + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rwa [zero_smul, add_zero] at this
  refine (h1.mul (hE'.mul hΦ')).congr_deriv ?_
  simp only [Pi.mul_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero, zero_smul, add_zero, one_mul]

theorem formAt_gram_one {S T : HSp D} (hS1 : S.gram = 1) (hT1 : T.gram = 1) (τ : D.what₂.Tau)
    (x y : Fin T.rank → Fin S.rank → ℂ) :
    ((GlobalTheory.OrientedHeis.formAt S T τ x y : ℝ) : ℂ) = Complex.I * (Formalism.L2.Pj.xiR D : ℂ) * (∑ i, ∑ j, x i j * conj (y i j)) -
      Complex.I * (Formalism.L2.Pj.xiR D : ℂ) * conj (∑ i, ∑ j, x i j * conj (y i j)) := by
  have hS : ∀ a b, tauE D τ ((S.gram⁻¹) a b) = if a = b then 1 else 0 := fun a b => by
    rw [hS1, inv_one, Matrix.one_apply]; split_ifs <;> simp
  have hT : ∀ a b, tauE D τ (T.gram a b) = if a = b then 1 else 0 := fun a b => by
    rw [hT1, Matrix.one_apply]; split_ifs <;> simp
  have hs : ∑ a, ∑ b, ∑ e, ∑ d, tauE D τ (S.gram⁻¹ a b) * conj (y e b) * tauE D τ (T.gram e d) * x d a =
      ∑ i, ∑ j, x i j * conj (y i j) := by
    simp only [hS, hT, ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    have h1 : ∀ a : Fin S.rank, (∑ b : Fin S.rank, ∑ e : Fin T.rank,
        if a = b then conj (y e b) * x e a else 0) = ∑ e : Fin T.rank, conj (y e a) * x e a := fun a => by
      rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
    simp only [h1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm (conj (y i j)) (x i j)
  unfold GlobalTheory.OrientedHeis.formAt
  rw [hs, GlobalTheory.FockPos.xi_zero_eq_host τ]
  push_cast
  rw [Complex.re_eq_add_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem omO_gram_one {S T : HSp D} (hS1 : S.gram = 1) (hT1 : T.gram = 1) (z v : RW T S) :
    ((GlobalTheory.OrientedHeis.omO S T z v : ℝ) : ℂ) =
      Complex.I * (Formalism.L2.Pj.xiR D : ℂ) * (∑ τ, ∑ i, ∑ j, z τ i j * conj (v τ i j)) -
        Complex.I * (Formalism.L2.Pj.xiR D : ℂ) * conj (∑ τ, ∑ i, ∑ j, z τ i j * conj (v τ i j)) := by
  show ((∑ τ, GlobalTheory.OrientedHeis.formAt S T τ (z τ) (v τ) : ℝ) : ℂ) = _
  rw [Complex.ofReal_sum]

  simp only [formAt_gram_one hS1 hT1, map_sum, Finset.mul_sum, Finset.sum_sub_distrib]

theorem reads_isFockVacAt : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Differentiable ℂ G → Reads ψ θ hS hT cc δ r G f → ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f := by
  intro D ψ θ S T a d hS hT cc δ r hset G f hG hR τ
  subst hS hT
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hset.inf
  have hψ := hset.std
  have hth : IsThetaFunO ψ S T f := hR.1
  have hR' := ((reads_iff hset.crv hset.scale G f).1 hR).2
  obtain ⟨hEd, hEc⟩ := GlobalTheory.FockPos.gauss_cr (ι := D.what₂.Tau) (m := T.rank) (n := S.rank) (-Formalism.L2.Pj.xiR D)
  set E : VC D S.rank T.rank → ℂ := fun Z =>
    Complex.exp ((Real.pi * (-Formalism.L2.Pj.xiR D) * ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2 : ℝ) : ℂ) with hEdef
  let L : VC D S.rank T.rank →L[ℂ] VC D S.rank T.rank := LinearMap.toContinuousLinearMap
    { toFun := fun Z τ i j => δ * embT D τ r * Z τ i j
      map_add' := fun Y Z => by funext τ i j; simp only [Pi.add_apply]; ring
      map_smul' := fun c Z => by funext τ i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  set Φ : VC D S.rank T.rank → ℂ := fun Z => G (fun τ i j => δ * embT D τ r * Z τ i j) with hΦdef
  have hΦd : Differentiable ℂ Φ := hG.comp L.differentiable
  have hΦc : ∀ z v : VC D S.rank T.rank, fderiv ℝ Φ z (Complex.I • v) = Complex.I * fderiv ℝ Φ z v := fun z v => by
    rw [((hΦd z).hasFDerivAt.restrictScalars ℝ).fderiv]
    exact (fderiv ℂ Φ z).map_smul Complex.I v
  have hreal : ∀ w : WO S T, w.map (finPart D) = 0 → ∀ x : RW T S, (w + iotaW σ T S x).map (finPart D) = 0 := by
    intro w hw x
    have h2 := h.real_iota T S x
    ext i j
    have a1 := congrFun (congrFun hw i) j
    have a2 := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at a1 a2 ⊢
    rw [Matrix.add_apply, map_add (finPart D), a1, a2, add_zero]
  have hval : ∀ w : WO S T, w.map (finPart D) = 0 → f w = E (piW θ T S w) * Φ (piW θ T S w) := by
    intro w hw
    rw [hR' w hw]
    have hz : GlobalTheory.FockPos.zCo θ 1 1 w = piW θ T S w := by
      funext τ
      have e : ∀ n, GlobalTheory.FockPos.frAt (D := D) (1 : GL (Fin n) D.host.E) τ = 1 := fun n =>
        Matrix.map_one _ (map_zero _) (map_one _)
      simp only [GlobalTheory.FockPos.zCo, e, inv_one, Matrix.one_mul, Matrix.mul_one]
      rfl
    rw [GlobalTheory.FockPos.gaussO, hz]
    show Complex.exp _ * G _ = Complex.exp _ * G _
    congr 2
    push_cast
    ring
  have hline : ∀ (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) (x : RW T S),
      (∀ t : ℝ, lineAt θ τ u t = iotaW σ T S (t • x)) → ∀ w : WO S T, w.map (finPart D) = 0 →
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f w =
        (-(Real.pi * Complex.I) * ((GlobalTheory.OrientedHeis.omO S T (piW θ T S w) x : ℝ) : ℂ)) *
            (E (piW θ T S w) * Φ (piW θ T S w)) +
          (fderiv ℝ E (piW θ T S w) x * Φ (piW θ T S w) + E (piW θ T S w) * fderiv ℝ Φ (piW θ T S w) x) := by
    intro u x hx w hw
    have hfun : (fun t : ℝ => heisO ψ S T (lineAt θ τ u t) f w) = fun t : ℝ =>
        Complex.exp ((t : ℂ) * (-(Real.pi * Complex.I) * ((GlobalTheory.OrientedHeis.omO S T (piW θ T S w) x : ℝ) : ℂ))) *
          (E (piW θ T S w + t • x) * Φ (piW θ T S w + t • x)) := by
      funext t
      rw [hx t, heisO_iota h hψ, hval _ (hreal w hw _), AddMonoidHom.map_add (f := _), h.pi_iota T S, LinearMap.map_smul]
      congr 2
      rw [smul_eq_mul, Complex.ofReal_mul]
      ring
    rw [Formalism.IndefR.Datum.dRho, hfun]
    exact (hasDerivAt_line_mul E Φ hEd (hΦd.restrictScalars ℝ) _ _ _).deriv
  let X : Matrix (Fin T.rank) (Fin S.rank) ℂ → RW T S := fun u τ' i j => if τ' = τ then u i j else 0
  have hX : ∀ u (t : ℝ), lineAt θ τ u t = iotaW σ T S (t • X u) := fun u t => by
    rw [GlobalTheory.VacUnique.Ann.lineAt_eq h S T τ u t]
    congr 2
    funext τ' i j
    by_cases e : τ' = τ
    · subst e
      simp [X, Pi.single, Function.update]
    · simp [X, e, Pi.single, Function.update]
  have hXI : ∀ u, X (Complex.I • u) = Complex.I • X u := fun u => by
    funext τ' i j
    by_cases e : τ' = τ <;> simp [X, e]
  have hJ : ∀ u : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      cplxO (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) u = Complex.I • u :=
    fun u => by simp only [cplxO, Matrix.one_mul, Matrix.mul_one]
  intro u
  have hθa : IsThetaFunO ψ S T (annih (heisO ψ S T) θ τ (cplxO 1 1) u f) := by
    have hc := (GlobalTheory.ThetaClosed.thetaClosed ψ θ hψ hset.inf S T f hth).2
    exact (GlobalTheory.FinWeilO.thetaSub ψ S T).add_mem (hc τ u)
      ((GlobalTheory.FinWeilO.thetaSub ψ S T).smul_mem Complex.I (hc τ _))
  refine GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real hθa fun w hw => ?_
  have hw' : w.map (finPart D) = 0 := hw
  show Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f w +
    Complex.I * Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO 1 1 u) f w = 0
  rw [hJ, hline u (X u) (hX u) w hw', hline _ (X (Complex.I • u)) (hX _) w hw', hXI]
  have hp' : ∑ τ', ∑ i, ∑ j, piW θ T S w τ' i j * conj ((Complex.I • X u) τ' i j) =
      -Complex.I * ∑ τ', ∑ i, ∑ j, piW θ T S w τ' i j * conj (X u τ' i j) := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [omO_gram_one hset.gS hset.gT, omO_gram_one hset.gS hset.gT, hp', hΦc]
  simp only [map_mul, map_neg, Complex.conj_I, neg_neg]
  have key := hEc (piW θ T S w) (X u)
  rw [Complex.ofReal_neg] at key
  set P := ∑ τ', ∑ i, ∑ j, piW θ T S w τ' i j * conj (X u τ' i j) with hP
  linear_combination (Φ (piW θ T S w)) * key +
    (E (piW θ T S w) * Φ (piW θ T S w) * (Real.pi : ℂ) * (Formalism.L2.Pj.xiR D : ℂ) *
        (Complex.I ^ 2 * (P + conj P) - 2 * P) + E (piW θ T S w) * fderiv ℝ Φ (piW θ T S w) (X u)) * Complex.I_sq

end GlobalTheory.NormExact
end
end

section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SchwartzAInt

open GlobalTheory.RegSch.IkSchwartz GlobalTheory.PartialIntegral



theorem integrable_pure {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (μ : Measure (Mx D m n))
    [μ.IsAddHaarMeasure] (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ) (g : (Fin m → Fin n → AEf D) → ℂ)
    (hg : g ∈ WeilM.SB (Fin m → Fin n → AEf D)) :
    Integrable (fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) μ := by
  haveI : IsModuleTopology (Af D.host.F) (AEf D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AEf D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : LocallyCompactSpace (AEf D) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AEf D) := e0.secondCountableTopology
  haveI : T2Space (AEf D) := e0.isEmbedding.t2Space
  letI : MeasurableSpace (Fin m → Fin n → AEf D) := borel _
  haveI : BorelSpace (Fin m → Fin n → AEf D) := ⟨rfl⟩
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := (lattice_Mx D m n).1
  obtain ⟨e, he⟩ := exists_split hθ m n
  let μr : Measure (D.what₂.Tau → Fin m → Fin n → ℂ) := Measure.addHaar
  let ν : Measure (Fin m → Fin n → AEf D) := Measure.addHaar
  obtain ⟨c, hc⟩ := exists_integral_split e μ μr ν
  have hf : Integrable (fun x => f x) μr := f.integrable
  have hg' : Integrable g ν := hg.1.continuous.integrable_of_hasCompactSupport hg.2
  have := (hc _ _ hf hg').1
  convert this using 2 with x
  rw [he]

theorem integrable_of_mem : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)),
    IsCovolOne (ratMx D m n) μ 𝓕 → ∀ Φ ∈ schwartzA θ m n, Integrable Φ μ := by
  intro D θ hθ m n μ 𝓕 hμ Φ hΦ
  haveI := hμ.1
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact integrable_pure hθ μ f g hg
  | zero => exact integrable_zero _ _ _
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact h.smul c

end GlobalTheory.SchwartzAInt
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

theorem _root_.GlobalTheory.T.arithmeticGroup_conj_isometry_moves_cover_point : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → ∀ (k₂ : (U₂ σ₂).Comp) (k : (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).Comp) (δ : GL (Fin D.R.r) D.host.E), ((U₂ σ₂).X k₂).Gm = ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Gm → (∀ v w, herm ((U₂ σ₂).X k₂).Gm ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U₂ σ₂).X k₂).Gm v w) → GlobalTheory.LevModel.Over d σ₂ (U (σ₂.comp (d.eF : c.F →+* d.c₂.F))) (U₂ σ₂) k₂ k δ → ∀ γ₂ ∈ ((U₂ σ₂).X k₂).Γ, ∀ x ∈ ((U₂ σ₂).X k₂).dom, ∀ x' : Frame ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, GlobalTheory.LevModel.Moved ((U₂ σ₂).X k₂) ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k) δ x x' → ∃ γ ∈ ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Γ, ∃ b ∈ Bor ((U (σ₂.comp (d.eF : c.F →+* d.c₂.F))).X k).Ψ D.R.r, lact (MulAut.conj δ γ₂) x' = rmul (lact γ x') b := by
  first | exact @GlobalTheory.LevModel.lact_conj_eq_rmul | exact GlobalTheory.LevModel.lact_conj_eq_rmul | (intros; apply GlobalTheory.LevModel.lact_conj_eq_rmul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.TransNZ

open GlobalTheory.MBLow.TranslateSection GlobalTheory.MBLow.TrSec

theorem eq_projectionPullbackSection_of_inverseImage {S : Scheme.{0}} (P : PolAV S) (s : P.L.Sec)
    (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver S))) (h : IsPolAVSectionInverseImage P (baseOver S) s th) :
    th = thSec P s := by
  have key : ∀ j : Fin 1 → P.L.ι, th.f j = (thSec P s).f j := by
    intro j
    have hj : j = fun _ => j 0 := funext fun k => by rw [Subsingleton.elim k 0]
    rw [hj, h (j 0) (chart_le P _), projectionPullbackSectionBaseProduct_isInverseImage P s (j 0) (chart_le P _)]
  cases th; cases hth : thSec P s
  simp only [hth] at key
  congr
  exact funext key

end GlobalTheory.TransNZ


open GlobalTheory.MBLow.TranslateSection GlobalTheory.MBLow.TrSec in
theorem GlobalTheory.TransNZ.exists_ne : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : KeyIn K) (m : ℕ), Odd m → 3 ≤ m →
    ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)), (∀ z : baseOver (Sp K) ⟶ x.P.A, z ^ (m ^ 2) = 1 → ∃ i, pt i = z) →
    ∀ (th : LB.Sec (LPow x.P.A x.P.L ((1 : ℕ) : ℤ) (baseOver (Sp K)))), IsPolAVSectionInverseImage x.P (baseOver (Sp K)) x.th th →
    ∀ (U : I → ThetaGrp x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))
      (t : I → LB.Sec (LPow x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))),
    (∀ i, SymLift x.P.A x.P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (pt i) (U i) ∧ Tr x.P x.rig m th (U i) (t i)) →
    ∃ i, (SecMod.mk (fst (baseOver (Sp K)) x.P.A).left (t i) : EA x.P (𝟙 (Sp K)) (m ^ 2)) ≠ 0 := by
  intro K _ _ _ x m hm hm3 I pt hpt th hth U t hUt
  have hm1 : 1 ≤ m := by omega
  obtain ⟨i₀, -⟩ := hpt 1 (one_pow _)
  obtain ⟨-, α, s₁, hα, -, hs₁, ht⟩ := hUt i₀
  obtain ⟨p₀⟩ : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨a, -, ha⟩ := x.th_ne p₀
  have e := GlobalTheory.TransNZ.eq_projectionPullbackSection_of_inverseImage x.P x.th th hth
  have hp₁ := nonzero_thSec x.P x.th a ha
  rw [← e] at hp₁
  obtain ⟨q, hq⟩ := mulT_surjective x.P m hm1 ((λ_ x.P.A).inv.left.base a)
  have hq' := mem_nonzeroLocus_of_isTwistPull x.P.isLB _ _ _ _ _ α th s₁ hs₁ q (hq ▸ hp₁)
  obtain ⟨r, hr⟩ := translT_surjective x.P.A (U i₀).pt q
  have hr' := mem_nonzeroLocus_of_isTwistPull x.P.isLB _ _ _ _ _ (U i₀).φ s₁ (t i₀) ht r (hr ▸ hq')
  refine ⟨i₀, fun h0 => ?_⟩
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hr'
  have hz : (t i₀).f k = 0 := (GlobalTheory.UU.SecMod.eq_zero_iff_coord _).1 h0 k
  rw [hz, Scheme.basicOpen_zero] at hk
  exact hk
end
end
