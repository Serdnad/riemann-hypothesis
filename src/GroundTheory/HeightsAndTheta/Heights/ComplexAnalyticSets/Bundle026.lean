module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle065
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle010
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
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
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open Polynomial

theorem DiscrAdjoin.proof : DiscrAdjoin.Statement := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ _ ℓ hℓ hadj
  have hK : IsIntegral K ℓ := Algebra.IsIntegral.isIntegral ℓ
  have hFK : minpoly K ℓ = (minpoly R ℓ).map (algebraMap R K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hℓ
  have hFm : (minpoly R ℓ).Monic := minpoly.monic hℓ
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hdegK : (minpoly K ℓ).natDegree = (minpoly R ℓ).natDegree := by
    rw [hFK, natDegree_map_eq_of_injective hinj]
  have hdeg : (minpoly R ℓ).natDegree = Module.finrank K L := by
    have h1 := IntermediateField.adjoin.finrank hK
    rw [hadj, IntermediateField.finrank_top', hdegK] at h1
    exact h1.symm
  have hpos : 0 < (minpoly R ℓ).natDegree := minpoly.natDegree_pos hℓ
  have hF'deg : (derivative (minpoly R ℓ)).natDegree ≤ (minpoly R ℓ).natDegree - 1 :=
    natDegree_derivative_le _
  have hres := resultant_deriv (f := minpoly R ℓ) (natDegree_pos_iff_degree_pos.mp hpos)
  rw [hFm.leadingCoeff, mul_one] at hres
  have hdisc : (minpoly R ℓ).discr = (-1) ^ ((minpoly R ℓ).natDegree *
      ((minpoly R ℓ).natDegree - 1) / 2) * resultant (minpoly R ℓ) (derivative (minpoly R ℓ))
        (minpoly R ℓ).natDegree ((minpoly R ℓ).natDegree - 1) := by
    rw [hres, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  refine ⟨hdeg, ?_, ?_⟩
  · intro h0
    have hR : resultant (minpoly R ℓ) (derivative (minpoly R ℓ)) (minpoly R ℓ).natDegree
        ((minpoly R ℓ).natDegree - 1) = 0 := by rw [hres, h0, mul_zero]
    have hRK := congrArg (algebraMap R K) hR
    rw [← resultant_map_map, map_zero, ← derivative_map, ← hFK, ← hdegK] at hRK
    have hsep : (minpoly K ℓ).Separable := Algebra.IsSeparable.isSeparable K ℓ
    have hle : (derivative (minpoly K ℓ)).natDegree ≤ (minpoly K ℓ).natDegree - 1 :=
      natDegree_derivative_le _
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, resultant_add_right_deg _ _ _ _ k le_rfl, coeff_natDegree, (minpoly.monic hK).leadingCoeff,
      one_pow, one_mul] at hRK
    exact resultant_ne_zero _ _ hsep hRK
  · intro z hz
    obtain ⟨p, q, -, -, hpq⟩ := exists_mul_add_mul_eq_C_resultant (minpoly R ℓ)
      (derivative (minpoly R ℓ)) le_rfl hF'deg (Or.inl hpos.ne')
    have hev := congrArg (aeval ℓ) hpq
    simp only [map_add (f := _), map_mul, minpoly.aeval, zero_mul, zero_add, aeval_C] at hev
    have hadjK : Algebra.adjoin K {ℓ} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hK.isAlgebraic, hadj,
        IntermediateField.top_toSubalgebra]
    have hzmem : z ∈ (Algebra.traceForm K L).dualSubmodule
        (Subalgebra.toSubmodule (Algebra.adjoin R {ℓ})) := by
      rw [LinearMap.BilinForm.mem_dualSubmodule]
      intro y hy
      rw [Submodule.mem_one]
      have hyint : IsIntegral R y := adjoin_le_integralClosure hℓ hy
      have htr : IsIntegral R (Algebra.trace K L (z * y)) := Algebra.isIntegral_trace (hz.mul hyint)
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp htr
      exact ⟨r, by simpa [Algebra.traceForm_apply] using hr⟩
    rw [traceForm_dualSubmodule_adjoin R K hadjK hℓ] at hzmem
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hzmem
    have hd : aeval ℓ (derivative (minpoly K ℓ)) = aeval ℓ (derivative (minpoly R ℓ)) := by
      rw [hFK, derivative_map, aeval_map_algebraMap]
    rw [hd]
    have hq : aeval ℓ q ∈ Algebra.adjoin R {ℓ} := aeval_mem_adjoin_singleton R ℓ
    have hw' : w ∈ Algebra.adjoin R {ℓ} := hw
    have key : (minpoly R ℓ).discr • ((aeval ℓ (derivative (minpoly R ℓ)))⁻¹ • w) =
        ((-1 : L) ^ ((minpoly R ℓ).natDegree * ((minpoly R ℓ).natDegree - 1) / 2) * aeval ℓ q * w) *
          (aeval ℓ (derivative (minpoly R ℓ)) * (aeval ℓ (derivative (minpoly R ℓ)))⁻¹) := by
      rw [hdisc, Algebra.smul_def, smul_eq_mul, map_mul, ← hev, map_pow, map_neg, map_one]
      ring
    rw [key]
    by_cases hd0 : aeval ℓ (derivative (minpoly R ℓ)) = 0
    · rw [hd0, zero_mul, mul_zero]
      exact zero_mem _
    · rw [mul_inv_cancel₀ hd0, mul_one]
      exact mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) hq) hw'

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open AdicCompletion

variable {R : Type} [CommRing R] (I : Ideal R) (D : Derivation ℤ R R)

theorem derivation_mem_pow_of_mem_pow_succ {n : ℕ} {r : R} (hr : r ∈ I ^ (n + 1)) : D r ∈ I ^ n :=
  by apply _root_.UpperTheory.Reformulated.B.Qn11.derivation_mem_pow_of_mem_pow_succ <;> assumption

theorem pow_smul_top_eq (n : ℕ) : (I ^ n • ⊤ : Ideal R) = I ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

noncomputable def derivQuot (n : ℕ) :
    R ⧸ (I ^ (n + 1) • ⊤ : Ideal R) →+ R ⧸ (I ^ n • ⊤ : Ideal R) :=
  QuotientAddGroup.lift (I ^ (n + 1) • ⊤ : Ideal R).toAddSubgroup
    ((Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R)).toAddMonoidHom.comp (D : R →ₗ[ℤ] R).toAddMonoidHom)
    (fun r hr => by
      change r ∈ (I ^ (n + 1) • ⊤ : Ideal R) at hr
      rw [AddMonoidHom.mem_ker]
      change Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) (D r) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_smul_top_eq]
      rw [pow_smul_top_eq] at hr
      exact derivation_mem_pow_of_mem_pow_succ I D hr)

theorem derivQuot_mk (n : ℕ) (r : R) :
    derivQuot I D n (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) (D r) := rfl

theorem exists_rep_succ (x : AdicCompletion I R) (n : ℕ) :
    ∃ a : R, x.val (n + 1) = Ideal.Quotient.mk (I ^ (n + 1) • ⊤ : Ideal R) a ∧
      x.val n = Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) a := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.val (n + 1))
  refine ⟨a, ha.symm, ?_⟩
  rw [← x.property (Nat.le_succ n), ← ha]
  rfl

noncomputable def derivCompletionAdd : AdicCompletion I R →+ AdicCompletion I R where
  toFun x := ⟨fun n => derivQuot I D n (x.val (n + 1)), fun {m n} hmn => by
    change transitionMap I R hmn (derivQuot I D n (x.val (n + 1))) = derivQuot I D m (x.val (m + 1))
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.val (n + 1))
    have hm : x.val (m + 1) = Ideal.Quotient.mk (I ^ (m + 1) • ⊤ : Ideal R) a := by
      rw [← x.property (Nat.succ_le_succ hmn), ← ha]
      rfl
    rw [hm, ← ha, derivQuot_mk, derivQuot_mk]
    rfl⟩
  map_zero' := AdicCompletion.ext fun n => map_zero (derivQuot I D n)
  map_add' x y := AdicCompletion.ext fun n => map_add (derivQuot I D n) _ _

noncomputable def derivCompletion : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R) :=
  Derivation.mk' (derivCompletionAdd I D).toIntLinearMap (fun a b => by
    refine AdicCompletion.ext fun n => ?_
    obtain ⟨p, hp1, hp0⟩ := exists_rep_succ I a n
    obtain ⟨q, hq1, hq0⟩ := exists_rep_succ I b n
    change derivQuot I D n ((a * b).val (n + 1)) =
      a.val n * derivQuot I D n (b.val (n + 1)) + b.val n * derivQuot I D n (a.val (n + 1))
    rw [val_mul, hp1, hq1, hp0, hq0, ← map_mul, derivQuot_mk, derivQuot_mk, derivQuot_mk, D.leibniz,
      smul_eq_mul (α := R), smul_eq_mul (α := R), map_add, map_mul, map_mul])

theorem DerivationAdicCompletion.proof : DerivationAdicCompletion.Statement := by
  intro R _ I D
  refine ⟨derivCompletion I D, fun r => AdicCompletion.ext fun n => ?_⟩
  rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology

noncomputable section

theorem measurable_poincareDeepWeight' : Measurable poincareDeepWeight := by
  have hn : Measurable fun z : ℂ => ‖z‖ ^ 2 := (continuous_norm.pow 2).measurable
  exact Measurable.ite (measurableSet_lt hn.log measurable_const) (hn.mul (hn.log.pow_const 2)).inv
    measurable_const

theorem integrableOn_inv_log_sq_mul :
    IntegrableOn (fun r : ℝ => ((Real.log r) ^ 2 * r)⁻¹) (Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2)))) := by
  have hρ1 : Real.exp (-(Real.exp 1 / 2)) < 1 :=
    Real.exp_lt_one_iff.2 (by have := Real.exp_pos 1; linarith)
  have hcont0 : ContinuousAt (fun r : ℝ => -(Real.log r)⁻¹) 0 := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    simpa using (Real.tendsto_log_nhdsNE_zero.inv_tendsto_atBot).neg
  refine intervalIntegral.integrableOn_deriv_of_nonneg (g := fun r : ℝ => -(Real.log r)⁻¹) ?_ ?_ ?_
  · intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      exact hcont0.continuousWithinAt
    · have hl : Real.log x ≠ 0 := (Real.log_neg h (hx.2.trans_lt hρ1)).ne
      exact ((Real.continuousAt_log h.ne').inv₀ hl).neg.continuousWithinAt
  · intro x hx
    have hl : Real.log x ≠ 0 := (Real.log_neg hx.1 (hx.2.trans hρ1)).ne
    have hx0 : x ≠ 0 := hx.1.ne'
    have : HasDerivAt (fun r : ℝ => -(Real.log r)⁻¹) (-(-x⁻¹ / Real.log x ^ 2)) x :=
      ((Real.hasDerivAt_log hx0).inv hl).neg
    refine this.congr_deriv ?_
    rw [neg_div, neg_neg]
    ring
  · intro x hx
    exact inv_nonneg.2 (mul_nonneg (sq_nonneg _) hx.1.le)

theorem ofReal_mul_poincareDeepWeight_le (r : ℝ) :
    ENNReal.ofReal r * ENNReal.ofReal (if Real.log (|r| ^ 2) < -Real.exp 1 then
        (|r| ^ 2 * Real.log (|r| ^ 2) ^ 2)⁻¹ else 0) ≤
      (Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2)))).indicator
        (fun r : ℝ => ENNReal.ofReal (((Real.log r) ^ 2 * r)⁻¹ / 4)) r := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ENNReal.ofReal_of_nonpos hr]
  · rw [abs_of_pos hr]
    split_ifs with hc
    · have hl : Real.log (r ^ 2) = 2 * Real.log r := by rw [Real.log_pow]; norm_num
      rw [hl] at hc
      have hlr : Real.log r < -(Real.exp 1 / 2) := by linarith
      have hl0 : Real.log r ≠ 0 := (hlr.trans (by have := Real.exp_pos 1; linarith)).ne
      rw [Set.indicator_of_mem (show r ∈ Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2))) from ⟨hr, ((Real.log_lt_iff_lt_exp hr).1 hlr).le⟩), ← ENNReal.ofReal_mul hr.le, hl]
      refine le_of_eq (congrArg ENNReal.ofReal ?_)
      field_simp
      ring
    · simp

theorem lintegral_poincareDeepWeight_lt_top :
    ∫⁻ z : ℂ, ENNReal.ofReal (poincareDeepWeight z) < ⊤ := by
  set ρ := Real.exp (-(Real.exp 1 / 2))
  set h : ℝ → ENNReal := (Set.Ioc 0 ρ).indicator
    (fun r : ℝ => ENNReal.ofReal (((Real.log r) ^ 2 * r)⁻¹ / 4)) with hh
  have hm : Measurable h := by
    refine Measurable.indicator ?_ measurableSet_Ioc
    exact ENNReal.measurable_ofReal.comp
      (((Real.measurable_log.pow_const 2).mul measurable_id).inv.div_const 4)
  rw [← Complex.lintegral_comp_polarCoord_symm]
  calc ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • ENNReal.ofReal (poincareDeepWeight (Complex.polarCoord.symm p))
      ≤ ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, h p.1 * (fun _ : ℝ => (1 : ENNReal)) p.2 := by
        rw [polarCoord_target]
        refine lintegral_mono fun p => ?_
        simp only [poincareDeepWeight, Complex.norm_polarCoord_symm, smul_eq_mul, mul_one, hh]
        exact ofReal_mul_poincareDeepWeight_le p.1
    _ = (∫⁻ r in Set.Ioi 0, h r) * ∫⁻ _ in Set.Ioo (-Real.pi) Real.pi, 1 := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact lintegral_prod_mul hm.aemeasurable aemeasurable_const
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ?_ ?_
        · refine (setLIntegral_le_lintegral _ _).trans_lt ?_
          rw [hh, lintegral_indicator measurableSet_Ioc]
          exact ((integrableOn_inv_log_sq_mul).div_const 4).lintegral_lt_top
        · rw [setLIntegral_one, Real.volume_Ioo]
          exact ENNReal.ofReal_lt_top

theorem TubeDeepWeightMass.proof : TubeDeepWeightMass.Statement := by
  intro d R
  set T : Set (Fin d → ℂ) := {w | ∀ i, ‖w i‖ ≤ R} with hTdef
  have hT : volume T < ⊤ := by
    have hsub : T ⊆ Metric.closedBall (0 : Fin d → ℂ) |R| := by
      intro w hw
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg (abs_nonneg R)).2 fun i => (hw i).trans (le_abs_self R)
    exact (measure_mono hsub).trans_lt measure_closedBall_lt_top
  have e := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0
  have hpre : {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R} =
      MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0 ⁻¹' (Set.univ ×ˢ T) := by
    ext z
    simp [hTdef, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.tail]
  have key := e.setLIntegral_comp_preimage_emb (MeasurableEquiv.measurableEmbedding _)
    (fun p : ℂ × (Fin d → ℂ) => ENNReal.ofReal (poincareDeepWeight p.1) * (fun _ => (1 : ENNReal)) p.2)
    (Set.univ ×ˢ T)
  rw [hpre]
  simp only [mul_one] at key
  have h0 : ∀ z : Fin (d + 1) → ℂ, (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0 z).1 = z 0 := fun z => rfl
  simp only [h0] at key
  rw [key, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have := lintegral_prod_mul (μ := (volume : Measure ℂ).restrict Set.univ)
    (ν := (volume : Measure (Fin d → ℂ)).restrict T)
    (ENNReal.measurable_ofReal.comp measurable_poincareDeepWeight').aemeasurable
    (aemeasurable_const (b := (1 : ENNReal)))
  simp only [mul_one, Function.comp_apply] at this
  rw [this, Measure.restrict_univ, setLIntegral_one]
  exact ENNReal.mul_lt_top lintegral_poincareDeepWeight_lt_top hT

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def FormalFibreQuotient.Statement : Prop :=
  ∀ (B A : Type) [CommRing B] [CommRing A] (f : B →+* A), Function.Surjective f → IsNoetherianRing B →
    ∀ (m : Ideal A) (P : Ideal (AdicCompletion m A)) [P.IsPrime],
      ∃ P' : PrimeSpectrum (AdicCompletion (m.comap f) B),
        P'.asIdeal.comap (algebraMap B (AdicCompletion (m.comap f) B)) =
            (P.comap (algebraMap A (AdicCompletion m A))).comap f ∧
          Nonempty (primeFibreLocalRing A P ≃+* primeFibreLocalRing B P'.asIdeal)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ExtensionQuotientLength.proof : ExtensionQuotientLength.Statement := by
  intro R B _ _ _ r hinj hr hfin
  set a := Algebra.linearMap R B
  set P : Submodule R B := LinearMap.range a
  set rP : Submodule R B := Submodule.map a (Ideal.span {r})
  set rB : Submodule R B := (Ideal.span {algebraMap R B r}).restrictScalars R
  have hrPP : rP ≤ P := by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  have hrPrB : rP ≤ rB := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    exact Ideal.mem_span_singleton'.2 ⟨algebraMap R B c, by simp [a]⟩
  have hPr : P ≤ rP.comap (r • LinearMap.id) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨r * x, Ideal.mem_span_singleton'.2 ⟨x, mul_comm _ _⟩, by simp [a, Algebra.smul_def]⟩

  let f₁ := (Ideal.span {r}).mapQ rP a (Submodule.le_comap_map _ _)
  let g₁ := rP.mapQ P LinearMap.id hrPP
  have hf₁ : Function.Injective f₁ := by
    refine (injective_iff_map_eq_zero _).2 fun q hq ↦ ?_
    induction q using Submodule.Quotient.induction_on with | _ x => ?_
    simp only [f₁, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq ⊢
    obtain ⟨y, hy, hyx⟩ := hq
    rwa [← hinj hyx]
  have hg₁ : Function.Surjective g₁ := fun q ↦ by
    induction q using Submodule.Quotient.induction_on with | _ b => exact ⟨Submodule.Quotient.mk b, rfl⟩
  have he₁ : Function.Exact f₁ g₁ := by
    intro q
    induction q using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [g₁, f₁, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Submodule.Quotient.mk x, rfl⟩
    · rintro ⟨q, hq⟩
      induction q using Submodule.Quotient.induction_on with | _ x => ?_
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hq
      simpa using P.sub_mem (hrPP hq) ⟨x, rfl⟩

  let f₂ := P.mapQ rP (r • LinearMap.id) hPr
  let g₂ := rP.mapQ rB LinearMap.id hrPrB
  have hf₂ : Function.Injective f₂ := by
    refine (injective_iff_map_eq_zero _).2 fun q hq ↦ ?_
    induction q using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [f₂, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.smul_apply,
      LinearMap.id_apply] at hq ⊢
    obtain ⟨y, hy, hyb⟩ := hq
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    refine ⟨c, (mul_cancel_left_mem_nonZeroDivisors hr).1 ?_⟩
    simpa [a, Algebra.smul_def, mul_comm] using hyb
  have hg₂ : Function.Surjective g₂ := fun q ↦ by
    induction q using Submodule.Quotient.induction_on with | _ b => exact ⟨Submodule.Quotient.mk b, rfl⟩
  have he₂ : Function.Exact f₂ g₂ := by
    intro q
    induction q using Submodule.Quotient.induction_on with | _ b => ?_
    simp only [g₂, f₂, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero,
      Set.mem_range]
    constructor
    · intro hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 (show b ∈ Ideal.span {algebraMap R B r} from hb)
      exact ⟨Submodule.Quotient.mk c, by simp [Algebra.smul_def, mul_comm]⟩
    · rintro ⟨q, hq⟩
      induction q using Submodule.Quotient.induction_on with | _ c => ?_
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hq
      have hc : r • c ∈ rB := Ideal.mem_span_singleton'.2 ⟨c, by simp [Algebra.smul_def, mul_comm]⟩
      simpa using rB.sub_mem hc (hrPrB hq)
  have h₁ := Module.length_eq_add_of_exact f₁ g₁ hf₁ hg₁ he₁
  have h₂ := Module.length_eq_add_of_exact f₂ g₂ hf₂ hg₂ he₂
  rw [← (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {algebraMap R B r})).length_eq]
  rw [h₁, add_comm] at h₂
  exact (WithTop.add_left_inj hfin).1 h₂

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem IdealHeightSpread.proof : IdealHeightSpread.Statement := by
  intro R _ _ I P _ _
  classical
  have hF := I.finite_minimalPrimes_of_isNoetherianRing R

  let a : Ideal R → R := fun p =>
    if h : ¬ (p : Set R) ⊆ P then Classical.choose (Set.not_subset.mp h) else 1
  have ha : ∀ p : Ideal R, ¬ p ≤ P → a p ∈ p ∧ a p ∉ P := by
    intro p h
    have h' : ¬ (p : Set R) ⊆ P := h
    simp only [a, dif_pos h']
    exact Classical.choose_spec (Set.not_subset.mp h')
  let s : Finset (Ideal R) := hF.toFinset.filter (fun p => ¬ p ≤ P)
  refine ⟨∏ p ∈ s, a p, ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨p, hp, hpP⟩
    exact (ha p (Finset.mem_filter.mp hp).2).2 hpP
  · intro Q _ _ hgQ
    rw [Ideal.height_eq_inf_minimalPrimes (I.map (algebraMap R (Localization.AtPrime Q)))]
    refine le_iInf₂ fun J hJ => ?_
    have hJp : J.IsPrime := hJ.isPrime
    have hmin : J.comap (algebraMap R (Localization.AtPrime Q)) ∈ I.minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map Q.primeCompl] at hJ
      exact hJ
    set p := J.comap (algebraMap R (Localization.AtPrime Q)) with hpdef
    have hpp : p.IsPrime := hmin.1.1

    have hpQ : p ≤ Q := by
      intro x hx
      by_contra hxQ
      have hu := IsLocalization.map_units (Localization.AtPrime Q) (⟨x, hxQ⟩ : Q.primeCompl)
      exact hJp.ne_top (Ideal.eq_top_of_isUnit_mem J hx hu)

    have hpP : p ≤ P := by
      by_contra hnot
      apply hgQ
      apply hpQ
      have hps : p ∈ s := Finset.mem_filter.mpr ⟨hF.mem_toFinset.mpr hmin, hnot⟩
      exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a hps) (ha p hnot).1
    have hdisj : Disjoint (P.primeCompl : Set R) (p : Set R) := by
      rw [Set.disjoint_left]
      intro x hx hxp
      exact hx (hpP hxp)
    have hJh : J.height = p.height := (IsLocalization.height_under Q.primeCompl J).symm
    rw [hJh, ← IsLocalization.height_map_of_disjoint P.primeCompl (S := Localization.AtPrime P) p hdisj]
    exact Ideal.height_mono (Ideal.map_mono hmin.1.2)

end GroundTheory.Heights₂.Heights
end
