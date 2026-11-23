module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle264
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle279
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle266
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle278
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.Bundle001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle014
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferent
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle276
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

noncomputable section

namespace GlobalTheory.ThetaTransl.CubeSer

open PowerSeries

theorem taylorCoeffAtZero_deriv (F : ℂ → ℂ) (n : ℕ) : coef1 (deriv F) n = ((n : ℂ) + 1) * coef1 F (n + 1) := by
  simp only [coef1]
  rw [← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  have h : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h' : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  field_simp

theorem algEnt_deriv {F : ℂ → ℂ} (hF : AlgEnt F) : AlgEnt (deriv F) := by
  refine ⟨?_, fun n => ?_⟩
  · have h := (hF.1.contDiff (n := 2)).differentiable_iteratedDeriv 1 (by norm_num)
    simpa [iteratedDeriv_one] using h
  · rw [taylorCoeffAtZero_deriv]
    exact mul_mem (add_mem (natCast_mem _ n) (one_mem _)) (hF.2 _)

variable {p : ℕ} [Fact p.Prime]

theorem padicTaylorSeries_deriv_eq_derivative (lam : Qbar →+* ℂ_[p]) {F : ℂ → ℂ} (hF : AlgEnt F) :
    GL3Theta.ser1 lam (deriv F) = d⁄dX (GL3Theta.ser1 lam F) := by
  ext n
  rw [coeff_derivative, GlobalTheory.SerTransport.coeff_padicTransportSeries, GlobalTheory.SerTransport.coeff_padicTransportSeries, taylorCoeffAtZero_deriv]
  obtain ⟨a, ha⟩ := GlobalTheory.SerTransport.exists_coef hF
  rw [ha]
  have e : ((n : ℂ) + 1) * (a (n + 1) : ℂ) = ((((n : Qbar) + 1) * a (n + 1) : Qbar) : ℂ) := by
    push_cast; rfl
  rw [e, GlobalTheory.SerTransport.lamC_coe, GlobalTheory.SerTransport.lamC_coe, map_mul, map_add (f := _), map_natCast, map_one,
    mul_comm]

theorem atU_deriv (g : GL3Theta.G1 p) {F : ℂ → ℂ} (hF : AlgEnt F) :
    d⁄dX (g.atU F) =
      g.atU (deriv F) * (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * d⁄dX g.l) := by
  have hs := HasSubst.of_constantCoeff_zero' (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.SerTransport.atU_eq, GlobalTheory.SerTransport.atU_eq, derivative_subst hs, padicTaylorSeries_deriv_eq_derivative g.lam hF,
    Derivation.leibniz, derivative_C, smul_zero, add_zero, smul_eq_mul]

theorem bddSer_derivative {f : PowerSeries ℂ_[p]} (hf : BddSer f) : BddSer (d⁄dX f) := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨B, fun n => ?_⟩
  rw [coeff_derivative, norm_mul]
  have h1 : ‖((n : ℂ_[p]) + 1)‖ ≤ 1 := by
    exact_mod_cast IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n + 1)
  calc _ ≤ B * 1 := mul_le_mul (hB _) h1 (norm_nonneg _) ((norm_nonneg _).trans (hB 0))
    _ = B := mul_one B

end GlobalTheory.ThetaTransl.CubeSer

namespace GlobalTheory.ThetaTransl.CubeSer

open PowerSeries

theorem sqThD_atU : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar →
    g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar →
      AlgEnt (sqThD g.abelian₂ v) ∧ ∃ w : PowerSeries ℂ_[p], BddSer w ∧
        g.atU (sqThD g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * w := by
  intro p _ g hOk hL h2 h3 hd hσ v hv hw
  obtain ⟨-, hwi, -, -, hA⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hOk hL h2 h3 hd
  have hq : IsWq g.W g.wq := hOk.2.1
  obtain ⟨hS, hB⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  obtain ⟨hmul, hconst, -, -⟩ := GlobalTheory.SerTransport.transport p g
  obtain ⟨i1, i2, i3, i4, i6, -⟩ := hOk.1
  obtain ⟨vI, hvI, hvl⟩ := PI.JetsPhW.Inv.inverse_omega_holds p g.W g.wq i1 i2 i3 i4 i6 hq
  rw [PI.JetsPhW.Inv.dX_eq_derivative] at hvl
  change vI * d⁄dX g.l = 1 at hvl
  have hσd := algEnt_deriv hσ
  have hSd := algEnt_deriv hS
  have hm2 : (((-2 : Qbar)) : ℂ) = -2 := by push_cast; rfl
  have hc := hconst (((-2 : Qbar)) : ℂ) (-2 : Qbar).2
  have hl2 : lamC g.lam (((-2 : Qbar)) : ℂ) = -2 := by
    rw [GlobalTheory.SerTransport.lamC_coe, map_neg, map_ofNat]
  have k1 := (hmul (sgStar g.abelian₂) (deriv (sqTh g.abelian₂ v)) hσ hSd).1
  have k2 := (hmul (deriv (sgStar g.abelian₂)) (sqTh g.abelian₂ v) hσd hS).1
  have k3 := (hmul (fun _ => (((-2 : Qbar)) : ℂ)) (fun z => deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z)
    hc.1 k2.1).1
  have k4 := (hmul (fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z)
    (fun z => (((-2 : Qbar)) : ℂ) * (deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z)) k1.1 k3.1).2
  have hT : sqThD g.abelian₂ v = fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z +
      (((-2 : Qbar)) : ℂ) * (deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z) := by
    funext z
    rw [hm2]
    simp only [sqThD]
    ring
  refine ⟨hT ▸ k4.1, ?_⟩
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he
  set L := lineSer g.wq⁻¹ (xAt g v) with hL'
  obtain ⟨-, hbdd, hCb, hX, -⟩ := SerRing.series_ring_laws p
  refine ⟨vI * (X * d⁄dX L - 2 * L), ?_, ?_⟩
  · have hX2 : BddSer (X ^ 2 : PowerSeries ℂ_[p]) := by
      rw [pow_two]; exact (hbdd _ _ ⟨1, hX⟩ ⟨1, hX⟩).2.2
    have hLb : BddSer L := by
      rw [hL', lineSer]; exact (hbdd _ _ ⟨1, hwi⟩ (hbdd _ _ (hCb _).1 hX2).2.2).2.1
    have h2b : BddSer (2 : PowerSeries ℂ_[p]) := by
      rw [show (2 : PowerSeries ℂ_[p]) = C 2 from (map_ofNat C 2).symm]; exact (hCb 2).1
    refine (hbdd _ _ ⟨1, fun n => hvI n⟩ (hbdd _ _ ((hbdd _ _ ⟨1, hX⟩ (bddSer_derivative hLb)).2.2)
      ((hbdd _ _ h2b hLb).2.2)).2.1).2.2
  · have dA := atU_deriv g hσ
    have dB := atU_deriv g hS
    rw [hA] at dA
    rw [hB] at dB
    have hDA : d⁄dX (C ε * X * e) = C ε * (e + X * d⁄dX e) := by
      simp only [Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul]
      ring
    have hDB : d⁄dX (e ^ 2 * L) =
        2 * e * d⁄dX e * L + e ^ 2 * d⁄dX L := by
      simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rw [hDA] at dA
    rw [hDB] at dB
    have F4 : C ε * C ε⁻¹ = (1 : PowerSeries ℂ_[p]) := by
      rw [← map_mul, mul_inv_cancel₀ (Units.ne_zero _), map_one]
    set a1 := g.atU (deriv (sgStar g.abelian₂))
    set b1 := g.atU (deriv (sqTh g.abelian₂ v))
    set x := C ε
    set y := C ε⁻¹
    set l' := d⁄dX g.l
    set E' := d⁄dX e
    set L'' := d⁄dX L
    have ha1 : a1 = (e + X * E') * vI := by
      linear_combination (-a1) * F4 + (-a1 * x * y) * hvl + (-y * vI) * dA + ((e + X * E') * vI) * F4
    have hb1 : b1 = y * (2 * e * E' * L + e ^ 2 * L'') * vI := by
      linear_combination (-b1) * F4 + (-b1 * x * y) * hvl + (-y * vI) * dB
    have hT' : g.atU (sqThD g.abelian₂ v) = x * X * e * b1 + C (-2) * (a1 * (e ^ 2 * L)) := by
      rw [← hA, ← hB, ← hl2]
      calc g.atU (sqThD g.abelian₂ v) = g.atU (fun z => sgStar g.abelian₂ z * deriv (sqTh g.abelian₂ v) z +
            (((-2 : Qbar)) : ℂ) * (deriv (sgStar g.abelian₂) z * sqTh g.abelian₂ v z)) := by rw [← hT]
        _ = _ := by rw [k4.2, k1.2, k3.2, k2.2, hc.2]
    rw [hT', show (C (-2) : PowerSeries ℂ_[p]) = -2 by rw [map_neg, map_ofNat]]
    linear_combination (x * X * e) * hb1 - (2 * e ^ 2 * L) * ha1 +
      (X * e * (2 * e * E' * L + e ^ 2 * L'') * vI) * F4

end GlobalTheory.ThetaTransl.CubeSer
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter Topology

noncomputable section

namespace GlobalTheory.EvenTheta.MulLat

variable {Λ : AddSubgroup ℂ}

theorem trFac_ne (z ω : ℂ) : GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ≠ 0 := Complex.exp_ne_zero _

theorem differentiable_trFac (ω : ℂ) : Differentiable ℂ fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ z ω := by
  unfold GlobalTheory.EvenTheta.Fibres.trFac
  fun_prop

theorem exists_sg_mul_sq (h : IsLat Λ) {β : ℂ} (hβ : ∀ ω ∈ Λ, β * ω ∈ Λ) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, sgStar Λ (β * z) ^ 2 = sgStar Λ z ^ 2 * G z := by
  have hσ := h.differentiable
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (h.sg_eq_zero z).not.2 hz
  set u := dslope (sgStar Λ) 0 with hu_def
  have hU : Differentiable ℂ u :=
    differentiableOn_univ.1 ((Complex.differentiableOn_dslope Filter.univ_mem).2 hσ.differentiableOn)
  have hu0 : u 0 = 1 := by
    rw [hu_def, dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.1]
  have eu : ∀ z, sgStar Λ z = z * u z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(h.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  refine exists_entire_of_locally_dvd (F := fun z => sgStar Λ (β * z) ^ 2) (S := fun z => sgStar Λ z ^ 2)
    (h.dense_compl.mono fun z hz => pow_ne_zero 2 (hne z hz)) fun w => ?_
  by_cases hw : w ∈ Λ
  · have hT := differentiable_trFac (Λ := Λ) w
    have hT' := differentiable_trFac (Λ := Λ) (β * w)
    set D : ℂ → ℂ := fun z => u (z - w) ^ 2 * GlobalTheory.EvenTheta.Fibres.trFac Λ (β * (z - w)) (β * w) ^ 2
      with hD_def
    have hD : Differentiable ℂ D := by
      rw [hD_def]
      have h1 : Differentiable ℂ fun z => u (z - w) := hU.comp (by fun_prop)
      have h2 : Differentiable ℂ fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ (β * (z - w)) (β * w) :=
        hT'.comp (by fun_prop)
      fun_prop
    have hD0 : D w ≠ 0 := by
      simp only [hD_def, sub_self, hu0]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (trFac_ne _ _))
    set N : ℂ → ℂ := fun z => β ^ 2 * u (β * (z - w)) ^ 2 * GlobalTheory.EvenTheta.Fibres.trFac Λ (z - w) w ^ 2
      with hN_def
    have hN : Differentiable ℂ N := by
      rw [hN_def]
      have h1 : Differentiable ℂ fun z => u (β * (z - w)) := hU.comp (by fun_prop)
      have h2 : Differentiable ℂ fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ (z - w) w :=
        hT.comp (by fun_prop)
      fun_prop
    refine ⟨fun z => N z / D z, (hN.analyticAt w).div (hD.analyticAt w) hD0, ?_⟩
    filter_upwards [hD.continuous.continuousAt.eventually_ne hD0] with z hz
    have hz1 : u (z - w) ≠ 0 := fun h0 => hz (by simp [hD_def, h0])
    have e1 := GlobalTheory.EvenTheta.Fibres.sg_sq h hw (z - w)
    have e2 := GlobalTheory.EvenTheta.Fibres.sg_sq h (hβ w hw) (β * (z - w))
    rw [sub_add_cancel] at e1
    rw [show β * (z - w) + β * w = β * z by ring] at e2
    have t1 := trFac_ne (Λ := Λ) (z - w) w
    have t2 := trFac_ne (Λ := Λ) (β * (z - w)) (β * w)
    simp only [hN_def, hD_def]
    rw [eu (z - w)] at e1
    rw [eu (β * (z - w))] at e2
    have hz' : u (z - w) ^ 2 * GlobalTheory.EvenTheta.Fibres.trFac Λ (β * (z - w)) (β * w) ^ 2 ≠ 0 := hz
    rw [mul_div_assoc', eq_div_iff hz']
    linear_combination u (z - w) ^ 2 * e2 - β ^ 2 * u (β * (z - w)) ^ 2 * e1
  · refine ⟨fun z => sgStar Λ (β * z) ^ 2 / sgStar Λ z ^ 2,
      (((hσ.comp (by fun_prop : Differentiable ℂ fun z => β * z)).pow 2).analyticAt w).div
        ((hσ.analyticAt w).pow 2) (pow_ne_zero 2 (hne w hw)), ?_⟩
    filter_upwards [hσ.continuous.continuousAt.eventually_ne (hne w hw)] with y hy
    field_simp

end GlobalTheory.EvenTheta.MulLat

namespace GlobalTheory.EvenTheta.MulLat

variable {Λ : AddSubgroup ℂ}

theorem val_zero (h : IsLat Λ) {β : ℂ} {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (eG : ∀ z, sgStar Λ (β * z) ^ 2 = sgStar Λ z ^ 2 * G z) : G 0 = β ^ 2 := by
  have hσ := h.differentiable
  set u := dslope (sgStar Λ) 0 with hu_def
  have hU : Differentiable ℂ u :=
    differentiableOn_univ.1 ((Complex.differentiableOn_dslope Filter.univ_mem).2 hσ.differentiableOn)
  have hu0 : u 0 = 1 := by
    rw [hu_def, dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.1]
  have eu : ∀ z, sgStar Λ z = z * u z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(h.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  have hGc := hG.continuous
  have hUc := hU.continuous
  have key := congrFun (Continuous.ext_on (dense_compl_singleton (0 : ℂ))
    (f := fun z => u z ^ 2 * G z) (g := fun z => β ^ 2 * u (β * z) ^ 2) (by fun_prop)
    (by fun_prop) fun z hz => by
      have hz : z ≠ 0 := hz
      have e := eG z
      rw [eu, eu z] at e
      refine mul_left_cancel₀ (pow_ne_zero 2 hz) ?_
      beta_reduce
      linear_combination -e) 0
  simpa [hu0] using key

theorem sg_mul_sq : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (β : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β * starRingEnd ℂ β = ((k + 1 : ℕ) : ℂ) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ ∧ β * Q i ∈ Λ) ∧ ∀ z, sgStar Λ (β * z) ^ 2 = β ^ 2 * sgStar Λ z ^ 2 * ∏ i, sqTh Λ (Q i) z := by
  intro Λ h β k hβ hN
  have hβ0 : β ≠ 0 := by
    rintro rfl
    norm_num at hN
    exact Nat.cast_add_one_ne_zero k hN.symm
  have hσ := h.differentiable
  have hσc := hσ.continuous
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (h.sg_eq_zero z).not.2 hz
  obtain ⟨G, hG, eG⟩ := exists_sg_mul_sq h hβ
  have hGc := hG.continuous
  have hG0 := val_zero h hG eG
  have hev : ∀ z, G (-z) = G z := fun z => by
    refine congrFun (Continuous.ext_on h.dense_compl (f := fun z => G (-z)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have h1 := eG (-z)
    rw [h.sg_neg, neg_sq, mul_neg, h.sg_neg, neg_sq] at h1
    exact h1.symm.trans (eG z)
  have hlaw : ∀ ω ∈ Λ, ∀ z, G (z + ω) * GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k) = G z := by
    intro ω hω z
    have hTc : Continuous fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ z ω :=
      (differentiable_trFac ω).continuous
    refine congrFun (Continuous.ext_on h.dense_compl
      (f := fun z => G (z + ω) * GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have ea := GlobalTheory.EvenTheta.Fibres.sg_sq h hω z
    have eb := GlobalTheory.EvenTheta.Fibres.sg_sq h (hβ ω hω) (β * z)
    rw [GlobalTheory.EvenTheta.Fibres.trFac_mul hN] at eb
    have egz := eG z
    have egw := eG (z + ω)
    rw [mul_add] at egw
    beta_reduce
    linear_combination egz + eb - GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k + 2) * egw -
      G (z + ω) * GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k) * ea
  obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.EvenTheta.exists_eq_prod_sqTh Λ h k (fun z => G z / β ^ 2)
    (hG.div_const _) (fun z => by simp only [hev]) (by simp only [hG0]; exact div_self (pow_ne_zero 2 hβ0))
    (fun ω hω z => GlobalTheory.EvenTheta.Fibres.law_of_fac h (F := fun z => G z / β ^ 2) (k := k) hω z (by
      show G (z + ω) / β ^ 2 * _ = G z / β ^ 2
      rw [div_mul_eq_mul_div, hlaw ω hω z]))
  have hfac : ∀ z, sgStar Λ (β * z) ^ 2 = β ^ 2 * sgStar Λ z ^ 2 * ∏ i, sqTh Λ (Q i) z := fun z => by
    rw [eG z, ← hQe z]
    field_simp
  refine ⟨Q, fun i => ⟨hQ i, ?_⟩, hfac⟩
  refine (h.sg_eq_zero _).1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ?_)
  rw [hfac, Finset.prod_eq_zero (Finset.mem_univ i)
    ((h.sqTh_eq_zero (hQ i) _).2 (Or.inr (by rw [sub_self]; exact Λ.zero_mem))), mul_zero]

end GlobalTheory.EvenTheta.MulLat
end
end

section

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility GlobalTheory.Branching
open Formalism.MainNotions.PrimeDegreeVariant (embGL Interlace)
open scoped DirectSum

namespace GlobalTheory.Branching

theorem rowDiv_eq_zero_of_unipotent_fixed {n : ℕ} (nu : DomWeight n) (q : MvPolynomial (Fin n × Fin n) ℂ)
    (hq : ∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id →
      (∀ a, (g : Matrix (Fin n) (Fin n) ℂ) a a = 1) → sqAct ℂ n nu g q = q)
    (a b : Fin n) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv ℂ a b k q = 0 := by
  have hfix : ∀ t : ℂ, rowAct ℂ (lfockq_mat a b t) q = q := by
    intro t
    have htri : (lfockq_mat a b t).transpose.BlockTriangular id := by
      intro i j hij
      have hij' : j < i := hij
      simp only [Matrix.transpose_apply, lfockq_mat]
      rw [if_neg hij'.ne, if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hab hij'
    have hdiag : ∀ i, (lfockq_mat a b t).transpose i i = 1 := by
      intro i
      simp only [Matrix.transpose_apply, lfockq_mat]
      rw [if_pos trivial, if_neg, add_zero]
      rintro ⟨h1, h2⟩
      exact hab.ne (h2.symm.trans h1)
    have hdet : (lfockq_mat a b t).transpose.det = 1 := by
      rw [Matrix.det_of_upperTriangular htri]
      simp only [hdiag, Finset.prod_const_one]
    let g : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ▸ one_ne_zero :
      (lfockq_mat a b t).transpose.det ≠ 0)
    have hg : (g : Matrix (Fin n) (Fin n) ℂ) = (lfockq_mat a b t).transpose := rfl
    have hd : Matrix.GeneralLinearGroup.det g = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hg, hdet, Units.val_one]
    have := hq g htri hdiag
    unfold sqAct at this
    rwa [detPow, hd, one_zpow, Units.val_one, one_smul, hg, Matrix.transpose_transpose] at this
  have hP : rowGen ℂ a b q = Polynomial.C q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective
      (C_injective (Fin n × Fin n) ℂ))
    rintro _ ⟨t, rfl⟩
    show Polynomial.eval _ _ = Polynomial.eval _ _
    rw [lfockq_eval_rowGen, hfix, Polynomial.eval_C]
  rw [rowDiv, hP, Polynomial.coeff_C, if_neg (by omega)]

theorem exists_ne_zero_map_eq_zero_of_weight_ne (n : ℕ) (mu nu : DomWeight n) (hne : mu ≠ nu)
    (φ : (sqRep ℂ n mu).IntertwiningMap (sqRep ℂ n nu)) :
    ∃ f : nablaSq ℂ n mu, f ≠ 0 ∧ φ f = 0 := by
  let f : nablaSq ℂ n mu := ⟨extremal ℂ n mu, hwMem ℂ n n le_rfl _ (factNatW n mu).1⟩
  refine ⟨f, fun h => hwNe ℂ n n le_rfl mu.natW (congrArg Subtype.val h), ?_⟩
  have hint : ∀ g x, φ (sqRep ℂ n mu g x) = sqRep ℂ n nu g (φ x) := fun g x =>
    Representation.IntertwiningMap.isIntertwining _ _ φ g x
  obtain ⟨c, hc⟩ : ∃ c : ℂ, (φ f : MvPolynomial (Fin n × Fin n) ℂ) = c • extremal ℂ n nu := by
    apply hwLine ℂ n n le_rfl nu.natW (factNatW n nu).1 _ (φ f).2
    intro a b hab k hk
    refine rowDiv_eq_zero_of_unipotent_fixed nu _ (fun g h1 h2 => ?_) a b hab k hk
    have e : sqRep ℂ n mu g f = f := Subtype.ext ((factSqHighestWeight ℂ n mu).2 g h1 h2)
    rw [← sqRep_coe, ← hint, e]
  obtain ⟨i, hi⟩ : ∃ i, mu.w i ≠ nu.w i := by
    by_contra h
    push Not at h
    apply hne
    obtain ⟨w, hw⟩ := mu
    obtain ⟨w', hw'⟩ := nu
    have : w = w' := funext h
    subst this
    rfl
  let u : ℂˣ := Units.mk0 2 two_ne_zero
  let t : Fin n → ℂˣ := fun a => if a = i then u else 1
  have hprod : ∀ lam : DomWeight n, ((∏ a, (t a) ^ (lam.w a) : ℂˣ) : ℂ) = (2 : ℂ) ^ lam.w i := by
    intro lam
    rw [Finset.prod_eq_single i (fun b _ hb => by simp [t, hb]) (by simp)]
    simp [t, u]
  have e : sqRep ℂ n mu (diagGL ℂ n t) f = (2 : ℂ) ^ mu.w i • f := by
    apply Subtype.ext
    rw [← hprod]
    exact (factSqHighestWeight ℂ n mu).1 t
  have e2 : sqRep ℂ n nu (diagGL ℂ n t) (φ f) = (2 : ℂ) ^ nu.w i • φ f := by
    let h : nablaSq ℂ n nu := ⟨extremal ℂ n nu, hwMem ℂ n n le_rfl _ (factNatW n nu).1⟩
    have hc' : φ f = c • h := Subtype.ext hc
    have e3 : sqRep ℂ n nu (diagGL ℂ n t) h = (2 : ℂ) ^ nu.w i • h := by
      apply Subtype.ext
      rw [← hprod]
      exact (factSqHighestWeight ℂ n nu).1 t
    rw [hc', map_smul, e3, smul_comm]
  have e4 := hint (diagGL ℂ n t) f
  rw [e, e2, map_smul, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at e4
  refine e4.resolve_left fun h => hi ?_
  have h' : ((2 : ℝ) ^ mu.w i) = (2 : ℝ) ^ nu.w i := by
    simpa [norm_zpow] using congrArg norm h
  exact zpow_right_injective₀ (by norm_num) (by norm_num) h'

end GlobalTheory.Branching
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_traceDual_family_inverseHalfDifferent : ∀ (D : D7), ∃ (r : ℕ) (a a' : Fin r → D.host.E), (∀ k, a k ∈ D.host.AA0) ∧ (∀ k, a' k ∈ D.host.AA0) ∧ ∀ t : D.host.E, t = ∑ k, (Algebra.trace D.host.K D.host.E (t * D.host.conj (a' k))) • a k := by
  first | exact @GlobalTheory.exists_trace_dual_family_halfDifferent | exact GlobalTheory.exists_trace_dual_family_halfDifferent | (intros; apply GlobalTheory.exists_trace_dual_family_halfDifferent <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_adelicUnitary_of_localFamily_almostAll_trivial : ∀ (D : D7) (V : HSp D) (γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram), {v | γ v ≠ 1}.Finite → ∃ k ∈ GfC V, ∀ v : HeightOneSpectrum (𝓞 D.host.F), (finMat D.sp.cm.sig V.gram k).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)) = (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1 := by
  first | exact @GlobalTheory.LocalUnitaryGlue.exists_finite_adelic | exact GlobalTheory.LocalUnitaryGlue.exists_finite_adelic | (intros; apply GlobalTheory.LocalUnitaryGlue.exists_finite_adelic <;> assumption)
end
