module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InVarAddInVarNeZero
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalC
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalD
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.AnaSysW
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Bundle001
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Taylor0ConstMul
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.TransW
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KJoint
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NormLeOneOfQuad
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle090
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle094
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle151
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle152
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle154
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Formalism.L2.Th1
open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve Unif)
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.L2.Th1.D (normInt)
open Formalism.G (unitBall)

namespace GlobalTheory.ThLoc

theorem endoDatum_of_model (d : ℕ) (L : PeriodPair) (hmod : d % 4 = 3) (hCM : HasCMBy d L)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (W : WeierstrassCurve ℂ_[p]) (hU : Unif p L ι W)
    (hW : IntCurve W) (m n : ℤ) (hN : ¬ (p : ℤ) ∣ normInt d m n) :
    ∃ (S : Finset ℂ) (neg : S → S) (xP yP : S → ℂ_[p]),
      C.IsEndoCurve W neg xP yP (ι ((m : ℂ) + (n : ℂ) * omegaK d)) ∧
      (∀ P, ‖xP P‖ ≤ 1) ∧ (∀ P, ‖yP P‖ ≤ 1) ∧
      ι ((m : ℂ) + (n : ℂ) * omegaK d) * ι ((m : ℂ) + (n : ℂ) * (1 - omegaK d)) =
        (Fintype.card S : ℂ_[p]) + 1 ∧
      ι ((m : ℂ) + (n : ℂ) * omegaK d) *
          (ι ((m : ℂ) + (n : ℂ) * omegaK d) - ι ((m : ℂ) + (n : ℂ) * (1 - omegaK d))) *
          ι (F.s2 L) = ∑ P, (xP P + W.b₂ / 12) := by
  have hN0 : normInt d m n ≠ 0 := by
    intro h
    apply hN
    rw [h]
    exact dvd_zero _
  obtain ⟨S, neg, hcard, hker, hnegP, hE, hprod, hs2C⟩ := D.CurveNormEndomorphisms.cdata L hmod hCM m n hN0
  have hpN : ¬ p ∣ (S.card + 1) := by
    intro h
    apply hN
    rw [← hcard]
    exact_mod_cast h
  have hpt : ∀ P : S, E.ptW p L ι W (P : ℂ) =
      .some _ _ (E.AnaSysW.nonsing hU (P : ℂ) (hker P).2) := by
    intro P
    unfold E.ptW
    rw [dite_eq_left ⟨(hker P).2, E.AnaSysW.nonsing hU (P : ℂ) (hker P).2⟩]
  have hint : ∀ P : S, ‖E.AnaSysW.xc p L ι W P‖ ≤ 1 ∧ ‖E.AnaSysW.yc p L ι W P‖ ≤ 1 := by
    intro P
    have h := E.TransW.ptW_int E.analytic_point_map_add E.analytic_point_eq_zero_iff hU hW (P : ℂ) (S.card + 1) hpN
      (hker P).1 (hker P).2
    rw [hpt P] at h
    exact h
  refine ⟨S, neg, fun P => E.AnaSysW.xc p L ι W P, fun P => E.AnaSysW.yc p L ι W P,
    ?_, fun P => (hint P).1, fun P => (hint P).2, ?_, ?_⟩
  · apply D.CurveNormEndomorphisms.endoCurve_of_endoZ (RingHom.id ℂ_[p]) W
      (wF := fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[p])
        (F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))
    · intro P
      exact (E.AnaSysW.nonsing hU (P : ℂ) (hker P).2).1
    · intro P
      constructor
      · simp only [E.AnaSysW.xc, (hnegP P).1]
      · simp only [WeierstrassCurve.Affine.negY, E.AnaSysW.xc, E.AnaSysW.yc]
        rw [(hnegP P).2, (hnegP P).1, map_neg]
        ring
    · have h := D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[p]) hE
      simp only [PowerSeries.map_id, RingHom.id_apply, E.AnaSysW.xc, sub_add_cancel]
      rw [E.weierstrass_series_eq_transported p L ι W hU]
      exact h
  · rw [← map_mul, hprod, Fintype.card_coe]
    simp

  · rw [← map_sub, ← map_mul, ← map_mul, hs2C, map_sum]
    simp [E.AnaSysW.xc]

theorem jets_phW_three (d : ℕ) (L : PeriodPair) (hmod : d % 4 = 3) (h3 : d % 3 = 2) (hCM : HasCMBy d L)
    (ι : ℂ ≃+* ℂ_[3]) (W : WeierstrassCurve ℂ_[3]) (hU : Unif 3 L ι W) (hW : IntCurve W)
    (i : ℕ) (hi : 1 ≤ i) : ‖C.jet (logSer W) (E.phW 3 L ι W) i‖ ≤ 1 := by
  have hnorm : normInt d (-1) 2 = d := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, (d : ℤ) + 1 = 4 * k := ⟨((d : ℤ) + 1) / 4, by omega⟩
    have hdiv : ((d : ℤ) + 1) / 4 = k := by omega
    unfold normInt
    rw [hdiv]
    linear_combination -hk
  have hN : ¬ ((3 : ℕ) : ℤ) ∣ normInt d (-1) 2 := by
    rw [hnorm]
    omega
  obtain ⟨S, neg, xP, yP, hE, hx, hy, hprod, hs⟩ :=
    endoDatum_of_model d L hmod hCM 3 ι W hU hW (-1) 2 hN
  set al := ι (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK d) with hal
  set albar := ι (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * (1 - omegaK d)) with halbar
  have hsum : al + albar = ((0 : ℤ) : ℂ_[3]) := by
    rw [hal, halbar, ← map_add (f := _)]
    have e : (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK d) +
        (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * (1 - omegaK d)) = 0 := by
      push_cast
      ring
    rw [e]
    simp
  have hsq : al ^ 2 = -(d : ℂ_[3]) := by
    rw [hal, ← map_pow]
    have e : (((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK d) ^ 2 = -(d : ℂ) := by
      push_cast
      linear_combination 4 * D.CurveNormEndomorphisms.omega_sq d
    rw [e, map_neg, map_natCast]
  have h2 : ‖(2 : ℂ_[3])‖ = 1 := Top.OrthogonalGaussModelNormLemmas.norm_two 3 (by norm_num)
  have hal1 : ‖al‖ = 1 := by
    have h1 := congrArg norm hsq
    rw [norm_pow, norm_neg, E.ScaledModelNorms.norm_nat 3 (show ¬ 3 ∣ d by omega)] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1
  have hdiff : ‖al - albar‖ = 1 := by
    have e : al - albar = 2 * al := by
      have := hsum
      push_cast at this
      linear_combination -this
    rw [e, norm_mul, h2, hal1, one_mul]
  have hb : ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 3 * k := ⟨(d + 1) / 3, by omega⟩
    have hk' : (d : ℂ_[3]) + 1 = 3 * (k : ℂ_[3]) := by exact_mod_cast hk
    have e : (al ^ 2 - 1) * (W.b₂ / 12) = -((k : ℂ_[3]) * W.b₂) / 2 ^ 2 := by
      rw [hsq]
      linear_combination (-W.b₂ / 12) * hk'
    have hb2 : ‖W.b₂‖ ≤ 1 := by
      have hm : W.b₂ ∈ unitBall ℂ_[3] := by
        obtain ⟨a1, a2, -⟩ := Top.OrthogonalGaussModelNormLemmas.coeffIn hW
        unfold WeierstrassCurve.b₂
        exact add_mem (pow_mem a1 2) (mul_mem (ofNat_mem _ 4) a2)
      exact hm
    rw [e, norm_div, norm_pow, h2, one_pow, div_one, norm_neg, norm_mul]
    exact mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one _ k) (norm_nonneg _) hb2
  have h := G.curveJetsUnramThm ℂ_[3] W (Top.OrthogonalGaussModelNormLemmas.coeffIn hW) h2 (ι (F.s2 L)) al albar 0 S neg xP yP
    hE hx hy hprod hal1 hsum hdiff hb hs i hi
  unfold E.phW
  rw [← E.weierstrass_series_eq_transported 3 L ι W hU]
  exact h

theorem intS_exp_mul_translate (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (L : PeriodPair) (ι : ℂ ≃+* ℂ_[p])
    (W : WeierstrassCurve ℂ_[p]) (hU : Unif p L ι W) (hW : IntCurve W) (ω₀ : ℂ) (hω : ω₀ ∈ L.lattice)
    (hω2 : ω₀ / 2 ∉ L.lattice) (s : ℂ) (N : ℕ) (hN : 0 < N) (hlN : ¬ p ∣ N)
    (hNs : (N : ℂ) * s ∈ L.lattice) :
    E.IntS (B.fExp (E.phW p L ι W) * E.inW p ι W (F.opU L s (F.th0 L (ω₀ / 2)))) := by
  have hl2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  have h2t : ((2 : ℕ) : ℂ) * (ω₀ / 2) ∈ L.lattice := by simpa using E.TransW.half_mem hω 1
  obtain ⟨hc1, -⟩ := E.analytic_translate_model p L ι W hU hW (ω₀ / 2) 2 (by norm_num) hl2' h2t hω2
  have hN2 : ¬ p ∣ 2 * N := fun h => ((Nat.Prime.dvd_mul Fact.out).1 h).elim hl2' hlN
  have m3 : ((2 * N : ℕ) : ℂ) * (s + ω₀ / 2) ∈ L.lattice := by
    rw [mul_add]
    exact add_mem (E.TransW.two_mem hNs) (E.TransW.half_mem hω N)
  have hsim := (E.TransW.hW_sim p L ι W (ω₀ / 2) s (2 * N) (by omega) (E.TransW.two_mem hNs)
    (E.TransW.half_mem hω N) hω2).mul_left (B.fExp (E.phW p L ι W))
  refine (hsim.gaussOne ?_).1
  rw [mul_left_comm, ← E.TransW.gW_eq]
  exact E.Tor.gaussOne_C_mul (by rw [norm_inv, hc1, inv_one])
    (E.TransW.gW_gauss E.analytic_translate_system_model E.analytic_point_map_add E.analytic_point_eq_zero_iff hU hW _ (2 * N) hN2 m3)

theorem thetaZJetsThree : ThetaZJetsThree := by
  intro d L hd8 hd3 hCM ι W hU hW ω₀ hω h1 _ n _ κ _ r s N hr hN h3N hs
  have hω2 : ω₀ / 2 ∉ L.lattice := fun h => h1 (hCM _ h)
  obtain ⟨hlp, -, -, -, hu⟩ := C.curveFrame ℂ_[3] (unitBall ℂ_[3]) W (Top.OrthogonalGaussModelNormLemmas.coeffIn hW)
  have hph : PowerSeries.constantCoeff (E.phW 3 L ι W) = 0 := E.AnaSysW.cc_phW 3 L ι W
  obtain ⟨e1, hInt⟩ := E.prodInt ℂ_[3] κ n (E.phW 3 L ι W) r
    (fun k i => B.fExp (E.phW 3 L ι W) * E.inW 3 ι W (F.opU L (s k i) (F.th0 L (ω₀ / 2))))
    hph hr (fun k i => intS_exp_mul_translate 3 (by norm_num) L ι W hU hW ω₀ hω hω2 (s k i) N hN h3N
      (hs k i))
  have key := (G.kernelTwo ℂ_[3] _ _ _ hlp hu hph
    (jets_phW_three d L (by omega) hd3 hCM ι W hU hW) n (fun _ => 1) (fun _ => by simp) _
    (fun m => hInt m)).1
  obtain ⟨hl0, -, hv0, -, hlv⟩ := hlp
  rw [Top.KJ.phSum_one] at key
  change Formalism.DworkPowerSeriesWeights.JetsIntegral (G.toZ _ (Formalism.DworkPowerSeriesWeights.mvExp _ * _)) at key
  rw [← e1, Top.KJ.toZ_thetaProd hv0] at key
  convert key using 1
  unfold Top.thetaZ
  congr 1
  funext k i
  change _ = PowerSeries.subst _ (B.fExp (-(E.phW 3 L ι W)) * _)
  rw [← mul_assoc, ← B.fExp_add (by rw [map_neg]; exact neg_eq_zero.2 hph) hph,
    neg_add_cancel, B.ParO.fExp_zero, one_mul]
  unfold E.inW
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hl0)
    (PowerSeries.HasSubst.of_constantCoeff_zero' hv0), hlv]
  exact (PowerSeries.X_subst _).symm

end GlobalTheory.ThLoc
end
end

section

noncomputable section

namespace GlobalTheory.ValCmp

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.MainNotions.G

theorem dualIso_det_genM_ne_zero (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : (genM R n).det ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2) h
  rw [RingHom.map_det, map_zero] at h1
  have h2 : (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2).mapMatrix
      (genM R n) = 1 := by
    ext a b
    simp [genM]
  rw [h2, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem dualIso_cofRel_unique {R : Type} [CommRing R] [IsDomain R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g g' : MP R (m + 1)} (h : CofRel R m ν f g) (h' : CofRel R m ν f g') : g = g' :=
  mul_left_cancel₀ (pow_ne_zero _ (dualIso_det_genM_ne_zero R (m + 1))) (h.trans h'.symm)

theorem dualIso_cofRel_add {R : Type} [CommRing R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g f' g' : MP R (m + 1)} (h : CofRel R m ν f g) (h' : CofRel R m ν f' g') :
    CofRel R m ν (f + f') (g + g') := by
  unfold CofRel at *
  rw [mul_add, map_add (f := _), h, h']

theorem dualIso_cofRel_smul {R : Type} [CommRing R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g : MP R (m + 1)} (c : R) (h : CofRel R m ν f g) : CofRel R m ν (c • f) (c • g) := by
  unfold CofRel at *
  rw [mul_smul_comm, map_smul, h]

theorem dualIso_cofRel_zsmul {R : Type} [CommRing R] {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g : MP R (m + 1)} (c : ℤ) (h : CofRel R m ν f g) : CofRel R m ν (c • f) (c • g) := by
  unfold CofRel at *
  rw [mul_smul_comm, map_zsmul, h]

theorem dualIso_map_genM {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) :
    (MvPolynomial.map φ).mapMatrix (genM R n) = genM S n := by
  ext1 a b
  simp [genM]

theorem dualIso_map_cofAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) (f : MP R n) :
    MvPolynomial.map φ (cofAct R n f) = cofAct S n (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [cofAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [cofAct, aeval_X]
    rw [← dualIso_map_genM φ n, ← RingHom.map_adjugate]
    rfl

theorem dualIso_cofRel_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ} {ν : Fin (m + 1) → ℕ}
    {f g : MP R (m + 1)} (h : CofRel R m ν f g) :
    CofRel S m ν (MvPolynomial.map φ f) (MvPolynomial.map φ g) := by
  unfold CofRel at *
  rw [← dualIso_map_cofAct, ← h, map_mul, map_pow, RingHom.map_det, dualIso_map_genM]

theorem dualIso_nuDual_antitone {m : ℕ} {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) : Antitone (nuDual ν) := by
  intro i j hij
  have := hν (Fin.rev_le_rev.2 hij)
  simp only [nuDual]
  omega

theorem dualIso_nuDual_last {m : ℕ} (ν : Fin (m + 1) → ℕ) : nuDual ν (Fin.last m) = 0 := by
  simp [nuDual]

theorem dualIso_nuDual_nuDual {m : ℕ} {ν : Fin (m + 1) → ℕ} (hν : Antitone ν) (hl : ν (Fin.last m) = 0) :
    nuDual (nuDual ν) = ν := by
  funext i
  have := hν (Fin.zero_le i)
  simp only [nuDual, Fin.rev_rev, Fin.rev_zero, hl]
  omega

theorem dualIso_units_smul_smul {M : Type} [AddCommGroup M] (ε : ℤˣ) (x : M) : (ε : ℤ) • (ε : ℤ) • x = x := by
  rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]

theorem dualIso_exists_map (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ) (hν : Antitone ν)
    (hl : ν (Fin.last m) = 0) :
    ∃ Ψ : MP K (m + 1) →ₗ[K] MP K (m + 1), ∀ f ∈ dualWeyl K (m + 1) (m + 1) ν, CofRel K m ν f (Ψ f) := by
  choose G hG using GlobalTheory.T.exists_cofactorTwist_dualWeyl K m ν hν hl
  let Ψ₀ : dualWeyl K (m + 1) (m + 1) ν →ₗ[K] MP K (m + 1) :=
    { toFun := fun f => G f.1 f.2
      map_add' := fun f g =>
        dualIso_cofRel_unique (hG _ (f + g).2).2 (dualIso_cofRel_add (hG _ f.2).2 (hG _ g.2).2)
      map_smul' := fun c f =>
        dualIso_cofRel_unique (hG _ (c • f).2).2 (dualIso_cofRel_smul c (hG _ f.2).2) }
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_extend Ψ₀
  refine ⟨Ψ, fun f hf => ?_⟩
  have h1 : Ψ f = G f hf := LinearMap.congr_fun hΨ ⟨f, hf⟩
  rw [h1]
  exact (hG f hf).2

theorem dualIso_lattice (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] (m : ℕ)
    (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) (hl : ν (Fin.last m) = 0)
    (Ψ : MP Kf (m + 1) →ₗ[Kf] MP Kf (m + 1))
    (hΨ : ∀ f ∈ dualWeyl Kf (m + 1) (m + 1) ν, CofRel Kf m ν f (Ψ f))
    (A B : Submodule O (MP O (m + 1))) (hA : A ≤ dualWeyl O (m + 1) (m + 1) ν)
    (hB : B ≤ dualWeyl O (m + 1) (m + 1) (nuDual ν))
    (hAB : ∀ f ∈ A, ∃ g ∈ B, CofRel O m ν f g) (hBA : ∀ g ∈ B, ∃ f ∈ A, CofRel O m (nuDual ν) g f) :
    (A.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap).map (Ψ.restrictScalars O) =
      B.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap := by
  have key : ∀ f ∈ A, ∀ g, CofRel O m ν f g →
      Ψ (MvPolynomial.map (algebraMap O Kf) f) = MvPolynomial.map (algebraMap O Kf) g := fun f hf g hfg =>
    dualIso_cofRel_unique (hΨ _ (dualWeylMap O Kf _ _ _ _ _ (hA hf))) (dualIso_cofRel_map _ hfg)
  apply le_antisymm
  · rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    obtain ⟨g, hg, hfg⟩ := hAB f hf
    exact ⟨g, hg, (key f hf g hfg).symm⟩
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨f, hf, hgf⟩ := hBA g hg
    obtain ⟨ε, hε⟩ := GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive O m (nuDual ν) (dualIso_nuDual_antitone hν) (dualIso_nuDual_last ν)
    have h1 := hε g (hB hg) f hgf
    rw [dualIso_nuDual_nuDual hν hl] at h1
    have h2 := dualIso_cofRel_zsmul (ε : ℤ) h1
    rw [dualIso_units_smul_smul] at h2
    have h3 : (ε : ℤ) • f ∈ A := A.toAddSubgroup.zsmul_mem hf _
    exact ⟨_, ⟨_, h3, rfl⟩, key _ h3 g h2⟩

theorem exists_posOk_dual (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] (m : ℕ)
    (ν : Fin (m + 1) → ℕ) (hν : Antitone ν) (hl : ν (Fin.last m) = 0) (e c : ℤ) :
    ∃ Ψ : MP Kf (m + 1) →ₗ[Kf] MP Kf (m + 1),
      PosOk O Kf (m + 1) ν (nuDual ν) e (-(e + ν 0 + c)) c (fun h => (h⁻¹).transpose) Ψ := by
  obtain ⟨Ψ, hΨ⟩ := dualIso_exists_map Kf m ν hν hl
  have hν' := dualIso_nuDual_antitone hν
  have hl' := dualIso_nuDual_last ν
  have hdd := dualIso_nuDual_nuDual hν hl
  refine ⟨Ψ, fun f hf h0 => ?_, ?_, fun h hh f hf => ?_, ?_, ?_⟩
  · obtain ⟨ε, hε⟩ := GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive Kf m ν hν hl
    have h1 := hε f hf _ (hΨ f hf)
    rw [h0] at h1
    have h2 : CofRel Kf m (nuDual ν) 0 0 := by simp [CofRel]
    have h3 := dualIso_cofRel_unique h1 h2
    rw [← dualIso_units_smul_smul ε f, h3, smul_zero]
  · apply le_antisymm
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨g, hg, hfg⟩ := GlobalTheory.T.exists_cofactorTwist_dualWeyl Kf m ν hν hl f hf
      rw [dualIso_cofRel_unique (hΨ f hf) hfg]
      exact hg
    · intro g hg
      obtain ⟨f, hf, hgf⟩ := GlobalTheory.T.exists_cofactorTwist_dualWeyl Kf m _ hν' hl' g hg
      obtain ⟨ε, hε⟩ := GlobalTheory.T.cofactorTwistRelation_dualWeight_involutive Kf m _ hν' hl'
      have h1 := hε g hg f hgf
      rw [hdd] at h1 hf
      have h2 := dualIso_cofRel_zsmul (ε : ℤ) h1
      rw [dualIso_units_smul_smul] at h2
      have h3 : (ε : ℤ) • f ∈ dualWeyl Kf (m + 1) (m + 1) ν :=
        (dualWeyl Kf (m + 1) (m + 1) ν).toAddSubgroup.zsmul_mem hf _
      exact ⟨_, h3, dualIso_cofRel_unique (hΨ _ h3) h2⟩
  · have h1 := GlobalTheory.T.cofactorTwistRelation_rowAct_equivariant Kf m ν h hh f hf _ (hΨ f hf)
    have h2 := dualIso_cofRel_unique (hΨ _ (dualWeylRowStable Kf _ _ _ h⁻¹ f hf)) h1
    have h3 : (h⁻¹).transpose⁻¹ = h.transpose := by
      rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hh]
    have h4 : (h⁻¹).transpose.det = (h.det)⁻¹ := by
      rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    simp only [rnd, LinearMap.smul_apply, map_smul, AlgHom.toLinearMap_apply, h2, h3, h4, smul_smul, inv_zpow']
    rw [← zpow_add₀ hh.ne_zero, ← zpow_add₀ hh.ne_zero]
    congr 2
    ring
  · refine dualIso_lattice O Kf m ν hν hl Ψ hΨ _ _ le_rfl le_rfl (GlobalTheory.T.exists_cofactorTwist_dualWeyl O m ν hν hl) fun g hg => ?_
    have := GlobalTheory.T.exists_cofactorTwist_dualWeyl O m _ hν' hl' g hg
    rwa [hdd] at this
  · refine dualIso_lattice O Kf m ν hν hl Ψ hΨ _ _ (weylLeDual O _ _ _ _ hν) (weylLeDual O _ _ _ _ hν')
      (GlobalTheory.T.weylLattice_exists_cofactorTwist_dual O m ν hν hl) fun g hg => ?_
    have := GlobalTheory.T.weylLattice_exists_cofactorTwist_dual O m _ hν' hl' g hg
    rwa [hdd] at this

end GlobalTheory.ValCmp
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.hyperbolicCoordinates_isotropic : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → (∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i) → (∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0) → (∀ e e', ∑ i, σ (fOf D p σ om R g e i) * fOf D p σ om R g e' i = 0) ∧ (∀ e e', ∑ i, σ (fOf' D p σ oms R g e i) * fOf' D p σ oms R g e' i = 0) := by
  first | exact @GlobalTheory.KerStd.HypCoord.fOf_isotropic | exact GlobalTheory.KerStd.HypCoord.fOf_isotropic | (intros; apply GlobalTheory.KerStd.HypCoord.fOf_isotropic <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.hyperbolicCoordinates_dual : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g h : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → OrbitPlaces.IsReps D p R → TrDual (nP D p) σ om oms → (∀ z a b i, σ (g z a b i) = h (posPl D p z 1) a b i) → (∀ w z a b a₁ b₁, ∑ i, h w a b i * g z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b = b₁ then 1 else 0) → ∀ e e', ∑ i, σ (fOf D p σ om R g e i) * fOf' D p σ oms R g e' i = if e = e' then 1 else 0 := by
  first | exact @GlobalTheory.KerStd.HypCoord.fOf_fOf'_dual | exact GlobalTheory.KerStd.HypCoord.fOf_fOf'_dual | (intros; apply GlobalTheory.KerStd.HypCoord.fOf_fOf'_dual <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.hyperbolicCoordinates_integral_sigma_sq_fixed : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (R : Finset (OrbitPlaces.Pl D)) (N N' r : ℕ) (g : OrbitPlaces.Pl D → Fin N → Fin N' → Fin r → MaximalUnramifiedExtension p), OrbitPlaces.OrbOK D p → (∀ x : MaximalUnramifiedExtension p, ‖x‖ ≤ 1 → ‖σ x‖ ≤ 1) → OwOK (nP D p) σ om oms → (∀ z a b i, ‖g z a b i‖ ≤ 1) → (∀ z a b i, σ (σ (g z a b i)) = g (posPl D p z 2) a b i) → (∀ e i, ‖fOf D p σ om R g e i‖ ≤ 1 ∧ σ (σ (fOf D p σ om R g e i)) = fOf D p σ om R g e i) ∧ (∀ e i, ‖fOf' D p σ oms R g e i‖ ≤ 1 ∧ σ (σ (fOf' D p σ oms R g e i)) = fOf' D p σ oms R g e i) := by
  first | exact @GlobalTheory.KerStd.HypCoord.fOf_integral_sigma_sq | exact GlobalTheory.KerStd.HypCoord.fOf_integral_sigma_sq | (intros; apply GlobalTheory.KerStd.HypCoord.fOf_integral_sigma_sq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents : ∀ {D : D7} (V : HSp D), (∀ f : Formalism.L2.Theta.AE D, f * f = f → cA D f = f → (∃ L : Subgroup (GA D V), ∀ g, g ∈ L ↔ SuppF V f g) ∧ (∀ g : GA D V, ∃ g₁ g₂, SuppF V f g₁ ∧ SuppF V (1 - f) g₂ ∧ g = g₁ * g₂) ∧ ∀ f' g g', f * f' = 0 → SuppF V f g → SuppF V f' g' → Commute g g') ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)), ∃ e f, IsPrimeIdem P e f) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → f * f = f ∧ cA D f = f ∧ (∀ g, SuppF V f g → g ∈ GfC V) ∧ (∀ e' f', IsPrimeIdem P e' f' → e' = e ∧ f' = f) ∧ ∀ P' e' f', IsPrimeIdem P' e' f' → f * f' = 0 ∨ (f' = f ∧ (P' = P ∨ Formalism.IndefR.Lev.IsConjPl P P'))) ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) P' e, IsIdemAt e P → Formalism.IndefR.Lev.IsConjPl P P' → IsIdemAt (cA D e) P' := by
  first | exact @GlobalTheory.IdemSupport.supported_group_and_prime_idempotents | exact GlobalTheory.IdemSupport.supported_group_and_prime_idempotents | (intros; apply GlobalTheory.IdemSupport.supported_group_and_prime_idempotents <;> assumption)
end
