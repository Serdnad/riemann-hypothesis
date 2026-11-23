module

public import Formalism.IncomingBounds.Bundle002
public import Mathlib.RingTheory.PowerSeries.Exp
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallPointMultiplicativeCoordinateExistsUnique
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorsionLiftPairingInOrthogonalFrame
public import Formalism.PeriodIntegrals.Bundle018
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle021
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Formalism.LocalToGlobal.CharacterGerms.Bundle004
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.RealPlaceAnalysis.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HStable
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum

@[expose] public section

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

lemma hatmul_DT_C_mul {q : ℕ} [Fact q.Prime] (c : ℂ_[q]) (f : ℂ_[q]⟦X⟧) :
    DT (C c * f) = C c * DT f := by
  unfold DT
  rw [← smul_eq_C_mul, Derivation.map_smul, smul_eq_C_mul]
  ring

lemma hatmul_const_log {q : ℕ} [Fact q.Prime] (ω : ℂ_[q]) :
    constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
  have : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [logS]
  simp [this]

lemma hatmul_DT_hat {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ)
    (hG : AnalyticAt ℂ G 0) :
    DT (hat ι (C ω * logS) G) = C ω * hat ι (C ω * logS) (deriv G) := by
  obtain ⟨-, -, -, -, hd, -, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
  obtain ⟨-, -, -, -, hl, -⟩ := GlobalTheory.T.cpBinomialPowerSubOneSeries_integrality_composition_log q
  have h1 : DT (C ω * logS : ℂ_[q]⟦X⟧) = C ω := by rw [hatmul_DT_C_mul, hl, mul_one]
  unfold DT at h1 ⊢
  have hd' : d⁄dX (hat ι (C ω * logS) G) =
      d⁄dX (C ω * logS) * hat ι (C ω * logS) (deriv G) := hd G hG
  rw [hd', ← mul_assoc, h1]

lemma hatmul_iter {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (k : ℕ) :
    ∀ (G : ℂ → ℂ), AnalyticAt ℂ G 0 →
      DT^[k] (hat ι (C ω * logS) G) = C (ω ^ k) * hat ι (C ω * logS) (iteratedDeriv k G) := by
  induction k with
  | zero => intro G _; simp
  | succ k ih =>
    intro G hG
    have hk : AnalyticAt ℂ (iteratedDeriv k G) 0 := by
      rw [iteratedDeriv_eq_iterate]
      exact hG.iterated_deriv k
    rw [Function.iterate_succ_apply', ih G hG, hatmul_DT_C_mul, hatmul_DT_hat ι ω _ hk,
      iteratedDeriv_succ, pow_succ, map_mul, mul_assoc]

lemma hatmul_subst {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ) (a : ℤ_[q]) :
    hat ι (C (ω * zc a) * logS) G = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧) := by
  obtain ⟨-, -, -, -, -, -, hs⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
  obtain ⟨hm, -⟩ := GlobalTheory.T.cpBinomialPowerSubOneSeries_integrality_composition_log q
  obtain ⟨-, h0, -, hl⟩ := hm a
  have hsub : HasSubst (mulS a : ℂ_[q]⟦X⟧) := HasSubst.of_constantCoeff_zero' h0
  rw [hs G _ h0, ← smul_eq_C_mul (a := ω), subst_smul hsub, hl, smul_eq_C_mul, map_mul, mul_assoc]

theorem hat_multiplicative_chart : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ), AnalyticAt ℂ G 0 → (DT (hat ι (C ω * logS) G) = C ω * hat ι (C ω * logS) (deriv G)) ∧ (∀ k : ℕ, constantCoeff (DT^[k] (hat ι (C ω * logS) G)) = ω ^ k * ι (iteratedDeriv k G 0)) ∧ (∀ (α : ℂ) (a : ℤ_[q]), ι α = zc a → hat ι (C ω * logS) (fun z => G (α * z)) = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧)) ∧ ∀ a : ℤ_[q], hat ι (C (ω * zc a) * logS) G = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧) := by
  intro q _ ι ω G hG
  refine ⟨hatmul_DT_hat ι ω G hG, fun k => ?_, fun α a ha => ?_, hatmul_subst ι ω G⟩
  · obtain ⟨-, -, -, hc, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
    rw [hatmul_iter ι ω k G hG, map_mul, hc, constantCoeff_C]
  · obtain ⟨-, -, -, -, -, hα, -⟩ := GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws q ι _ (hatmul_const_log ω)
    rw [hα G α hG, ← hatmul_subst, ha, map_mul, ← mul_assoc, mul_comm (C (zc a))]

end GlobalTheory.MomOne
end

section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

theorem _root_.GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), M.MChart ω → (∀ ζ : ℂ_[q], ‖ζ - 1‖ < 1 → ∃ p, M.At ω ζ p) ∧ (∀ p, M.Small p → ∃ ζ, M.At ω ζ p) ∧ (∀ ζ ζ' p, M.At ω ζ p → M.At ω ζ' p → ζ = ζ') ∧ (∀ ζ p p', M.At ω ζ p → (M.At ω ζ p' ↔ p - p' ∈ M.L.lattice)) ∧ M.At ω 1 0 := by
  first | exact @GlobalTheory.MomOne.SmallPt.at_exists_unique | exact GlobalTheory.MomOne.SmallPt.at_exists_unique | (intros; apply GlobalTheory.MomOne.SmallPt.at_exists_unique <;> assumption)
end

section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

namespace GlobalTheory

section

variable {C : Type} [Field C] [CharZero C] {σ : Type}

omit [CharZero C] in
theorem mvExp_coeff_apply (a : MvPowerSeries σ C) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m (mvExp a) =
      ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (a ^ k) / (k.factorial : C) := rfl

theorem mvExp_eq_subst_exp (a : MvPowerSeries σ C) (ha : MvPowerSeries.constantCoeff a = 0) :
    mvExp a = PowerSeries.subst a (PowerSeries.exp C) := by
  ext m
  rw [mvExp_coeff_apply, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp [div_eq_mul_inv, mul_comm]
  · intro k hk
    by_contra hk'
    apply hk
    have hlt : m.degree < k := by simpa using hk'
    have : MvPowerSeries.coeff m (a ^ k) = 0 :=
      MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hlt)
        (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k ha))
    simp [this]

theorem mfact_mul_coeff_mvExp_linear [Fintype σ] (y : σ → C) (m : σ →₀ ℕ) :
    (mfact m : C) * MvPowerSeries.coeff m (mvExp (∑ s, y s • (MvPowerSeries.X s : MvPowerSeries σ C))) =
      ∏ i ∈ m.support, y i ^ m i := by
  classical
  have hL : (∑ s, y s • (MvPowerSeries.X s : MvPowerSeries σ C)) =
      ((∑ s, y s • (MvPolynomial.X s : MvPolynomial σ C) : MvPolynomial σ C) : MvPowerSeries σ C) := by

    rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.smul_eq_C_mul, MvPolynomial.coe_mul,
      MvPolynomial.coe_C, MvPolynomial.coe_X, MvPowerSeries.smul_eq_C_mul]
  have hdeg : (m.sum fun _ e => e) = m.degree := by
    rw [Finsupp.degree_apply]; rfl
  rw [mvExp_coeff_apply, hL, Finset.sum_eq_single m.degree]
  · rw [← MvPolynomial.coe_pow, MvPolynomial.coeff_coe,
      MvPolynomial.coeff_linearCombination_X_pow_of_fintype, if_pos hdeg]
    have hs : mfact m * m.multinomial = m.degree.factorial := by
      rw [Finsupp.multinomial_eq, Finsupp.degree_apply, ← Nat.multinomial_spec]; rfl
    have hs' : (mfact m : C) * (m.multinomial : C) = (m.degree.factorial : C) := by exact_mod_cast hs
    have h0 : (m.degree.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [← mul_div_assoc, ← mul_assoc, hs', mul_div_cancel_left₀ _ h0]
    rfl
  · intro k _ hk
    rw [← MvPolynomial.coe_pow, MvPolynomial.coeff_coe,
      MvPolynomial.coeff_linearCombination_X_pow_of_fintype, if_neg (by rw [hdeg]; exact Ne.symm hk), zero_div]
  · intro h
    exact absurd (Finset.self_mem_range_succ _) h

end

theorem mvExp_add_subst_linear : ∀ (C : Type) [Field C] [CharZero C] (σ : Type) [Fintype σ],
  (∀ a b : MvPowerSeries σ C, MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 → mvExp (a + b) = mvExp a * mvExp b) ∧
  (∀ a : MvPowerSeries σ C, MvPowerSeries.constantCoeff a = 0 → mvExp a = PowerSeries.subst a (PowerSeries.exp C)) ∧
  (∀ (τ : Type) [Fintype τ] (φ : σ → MvPowerSeries τ C) (a : MvPowerSeries σ C), (∀ s, MvPowerSeries.constantCoeff (φ s) = 0) → MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.subst φ (mvExp a) = mvExp (MvPowerSeries.subst φ a)) ∧
  (∀ (y : σ → C) (P : MvPolynomial σ C), jetAt0 P (mvExp (∑ s, y s • (MvPowerSeries.X s : MvPowerSeries σ C))) = MvPolynomial.eval y P) := by
  intro C _ _ σ _
  refine ⟨fun a b ha hb => ?_, fun a ha => mvExp_eq_subst_exp a ha, fun τ _ φ a hφ ha => ?_, fun y P => ?_⟩
  · rw [mvExp_eq_subst_exp a ha, mvExp_eq_subst_exp b hb,
      mvExp_eq_subst_exp (a + b) (by rw [map_add (f := _), ha, hb, add_zero])]
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add ha hb
  · have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ
    rw [mvExp_eq_subst_exp a ha,
      mvExp_eq_subst_exp _ (MvPowerSeries.constantCoeff_subst_eq_zero hs hφ ha),
      PowerSeries.subst_def, PowerSeries.subst_def,
      MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero ha).const hs]
  · rw [MvPolynomial.eval_eq, jetAt0]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_assoc, mfact_mul_coeff_mvExp_linear]

end GlobalTheory
end

section

open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

theorem _root_.GlobalTheory.T.torsion_lift_pairing_in_orthogonal_frame :
    ∀ (q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (ι : ℂ ≃+* ℂ_[q])
      (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (r : ℕ)
      (b : Fin r → Fin g → ℂ) (n m s s₀ : ℕ) (eps : ℂ) (y : Fin r → Fin (q ^ n)),
      (∀ z : Qbar, ι (z : ℂ) = lam z) → S.Ok → Split S.d q →
      (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) →
      (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → (∀ i, b i ∈ S.La) → IsIdem lam S.d m eps →
      2 * n ≤ m → (s₀ * ∏ i, a i) ∣ s →
      let y' (i : Fin g) : ℂ := beta S.d S.Hm ((s : ℂ) • liftY q n eps b y) (x i) / (a i : ℂ)
      (∀ i, Good ι S.d n s₀ (y' i)) ∧
        ∀ (A : Fin r → ℤ_[q]) (A' : Fin g → ℤ_[q]),
          (∀ i, GlobalTheory.MomOne.zc (A' i) =
            ∑ j, GlobalTheory.MomOne.zc (A j) * ι (beta S.d S.Hm (x i) (b j))) →
          kap S.Hm (vecA n b A) ((s : ℂ) • liftY q n eps b y) ∈ Qbar ∧
            ι (kap S.Hm (vecA n b A) ((s : ℂ) • liftY q n eps b y)) =
              ∏ i, ι (kap1 S.d 1 (y' i)) ^ (PadicInt.toZModPow n (A' i)).val := by
  first | exact @GlobalTheory.MomOne.kapFrame | exact GlobalTheory.MomOne.kapFrame | (intros; apply GlobalTheory.MomOne.kapFrame <;> assumption)
end

section

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.QuotientMeasureSigmaFinite

theorem sigmaFinite_of_pos_lintegral_ne_top {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {g : X → ℝ≥0∞} (hg : Measurable g) (hpos : ∀ x, g x ≠ 0) (hfin : ∫⁻ x, g x ∂ν ≠ ∞) :
    SigmaFinite ν := by
  refine Measure.sigmaFinite_of_countable (S := Set.range fun n : ℕ => {x | ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x})
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨n, rfl⟩
    have h0 : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (by simp)
    have h1 : ((n : ℝ≥0∞) + 1)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (by simp)
    exact (meas_ge_le_lintegral_div hg.aemeasurable h0 h1).trans_lt (ENNReal.div_lt_top hfin h0)
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hpos x)
    refine Set.mem_sUnion.2 ⟨_, ⟨n, rfl⟩, ?_⟩
    show ((n : ℝ≥0∞) + 1)⁻¹ ≤ g x
    exact le_trans (ENNReal.inv_le_inv.2 le_self_add) hn.le

theorem measurable_mul_pair (k r : ℕ) :
    Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j : Formalism.QuantumDeterminants.Mt k r)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem sigmaFinite_of_isQuotMeas {k r : ℕ} {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    [SigmaFinite μG] [SFinite μS] (hS : μS ≠ 0)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS ν) : SigmaFinite ν := by
  obtain ⟨h, hpos, hmeas, hint⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  have hne : ∀ y, h y ≠ 0 := fun y => (hpos y).ne'
  have hF : Measurable fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      ((h (fun i j => (Matrix.of p.2 * Matrix.of p.1) i j) : NNReal) : ℝ≥0∞) :=
    (measurable_coe_nnreal_ennreal.comp hmeas).comp (measurable_mul_pair k r)
  have hq' : ∫⁻ x, (h x : ℝ≥0∞) ∂μG =
      ∫⁻ x, (∫⁻ s, (h (fun i j => (Matrix.of s * Matrix.of x) i j) : ℝ≥0∞) ∂μS) ∂ν :=
    hq _ (measurable_coe_nnreal_ennreal.comp hmeas)

  refine sigmaFinite_of_pos_lintegral_ne_top
    (g := fun x => ∫⁻ s, (h (fun i j => (Matrix.of s * Matrix.of x) i j) : ℝ≥0∞) ∂μS)
    hF.lintegral_prod_right' ?_ ?_
  · intro x hx
    have hfm : Measurable fun s : Formalism.QuantumDeterminants.Mt k r =>
        ((h (fun i j => (Matrix.of s * Matrix.of x) i j) : NNReal) : ℝ≥0∞) :=
      (measurable_coe_nnreal_ennreal.comp hmeas).comp
        (Measurable.of_eval fun i => Measurable.of_eval fun j => by
          simp only [Matrix.mul_apply, Matrix.of_apply]
          fun_prop)
    rw [lintegral_eq_zero_iff hfm] at hx
    apply hS
    rw [← Measure.measure_univ_eq_zero]
    have h0 := ae_iff.1 hx
    simpa [hne] using h0
  · rw [← hq']
    exact (hint.trans ENNReal.one_lt_top).ne

end GlobalTheory.QuotientMeasureSigmaFinite
end

section

open Formalism.REAL Finset

theorem _root_.GlobalTheory.T.exists_qminor_sub_eq_polynomial : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (s : ℂ), ∃ c : ℕ → A, ∀ u : ℂ, qminor E a b (u - s) = ∑ i ∈ Finset.range (t + 1), u ^ i • c i := by
  first | exact @GlobalTheory.qminor_polyMap | exact GlobalTheory.qminor_polyMap | (intros; apply GlobalTheory.qminor_polyMap <;> assumption)
end

section

open Formalism.REAL Finset

theorem _root_.GlobalTheory.T.qminor_commute_of_commute_columns : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (x : A) (a b : Fin t → Fin n) (u : ℂ), (∀ (c : Fin n) (i : Fin t), E c (b i) * x = x * E c (b i)) → qminor E a b u * x = x * qminor E a b u := by
  first | exact @GlobalTheory.qminor_comm_of_comm_columns | exact GlobalTheory.qminor_comm_of_comm_columns | (intros; apply GlobalTheory.qminor_comm_of_comm_columns <;> assumption)
end

section

open Formalism.REAL Finset

theorem _root_.GlobalTheory.T.exists_eigenSplit_of_resolventIdentity : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (n : ℕ) (Ω : Module.End ℂ N) (X : ℂ → Module.End ℂ N) (d : ℕ) (c : ℕ → Module.End ℂ N) (ν : Fin n → ℂ), Function.Injective ν → (∀ u, X u = ∑ i ∈ Finset.range d, u ^ i • c i) → (∀ (u : ℂ) (w : N), u • X u w + Ω (X u w) = (∏ s, (u + ν s)) • w) → ∀ w : N, ∃ v : Fin n → N, w = ∑ s, v s ∧ ∀ s (u : ℂ), X u (v s) = (∏ t ∈ Finset.univ.erase s, (u + ν t)) • v s := by
  first | exact @GlobalTheory.exists_sum_eigen_split_of_resolvent | exact GlobalTheory.exists_sum_eigen_split_of_resolvent | (intros; apply GlobalTheory.exists_sum_eigen_split_of_resolvent <;> assumption)
end

section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdicColimit

variable {R : Type} [CommRing R] (I : Ideal R)

abbrev thickι (e : ℕ) (T : Over (Spec (CommRingCat.of R))) : (thickObj R I e T).left ⟶ T.left :=
  pullback.fst T.hom (thick R I e)

abbrev thickHom (e : ℕ) {T' T : Over (Spec (CommRingCat.of R))} (r : T' ⟶ T) :
    (thickObj R I e T').left ⟶ (thickObj R I e T).left :=
  ((Over.pullback (thick R I e)).map r).left

def IsAdicColimit (T : Over (Spec (CommRingCat.of R))) : Prop :=
  ∀ (X : Scheme.{0}) (f : ∀ e : ℕ, (thickObj R I e T).left ⟶ X), (∀ e, thickMap R I e T ≫ f (e + 1) = f e) →
    ∃! g : T.left ⟶ X, ∀ e, thickι I e T ≫ g = f e

instance mono_thick (e : ℕ) : Mono (thick R I e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

instance mono_thickι (e : ℕ) (T : Over (Spec (CommRingCat.of R))) : Mono (thickι I e T) :=
  inferInstanceAs (Mono (pullback.fst T.hom (thick R I e)))

@[reassoc]
theorem thickMap_ι (e : ℕ) (T : Over (Spec (CommRingCat.of R))) :
    thickMap R I e T ≫ thickι I (e + 1) T = thickι I e T :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
theorem thickHom_ι (e : ℕ) {T' T : Over (Spec (CommRingCat.of R))} (r : T' ⟶ T) :
    thickHom I e r ≫ thickι I e T = thickι I e T' ≫ r.left :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem thickMap_thickHom (e : ℕ) {T' T : Over (Spec (CommRingCat.of R))} (r : T' ⟶ T) :
    thickMap R I e T' ≫ thickHom I (e + 1) r = thickHom I e r ≫ thickMap R I e T := by
  rw [← cancel_mono (thickι I (e + 1) T), Category.assoc, Category.assoc, thickHom_ι, thickMap_ι,
    thickMap_ι_assoc, thickHom_ι]

variable {I}

theorem IsAdicColimit.hom_ext {T : Over (Spec (CommRingCat.of R))} (h : IsAdicColimit I T) {X : Scheme.{0}}
    {g g' : T.left ⟶ X} (e : ∀ e, thickι I e T ≫ g = thickι I e T ≫ g') : g = g' :=
  (h X (fun e => thickι I e T ≫ g') fun e => thickMap_ι_assoc I e T g').unique e fun _ => rfl

theorem IsAdicColimit.of_iso {T' T : Over (Spec (CommRingCat.of R))} (r : T' ≅ T) (h : IsAdicColimit I T') :
    IsAdicColimit I T := by
  intro X f hf
  obtain ⟨g, hg, hu⟩ := h X (fun e => thickHom I e r.hom ≫ f e) fun e => by
    rw [thickMap_thickHom_assoc, hf]
  refine ⟨r.inv.left ≫ g, fun e => ?_, fun g' hg' => ?_⟩
  · rw [← thickHom_ι_assoc, hg, ← Over.comp_left_assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  · rw [← hu (r.hom.left ≫ g') fun e => by rw [← thickHom_ι_assoc, hg'], ← Over.comp_left_assoc, Iso.inv_hom_id]
    exact (Category.id_comp _).symm

theorem isAdicColimit_of_factor {T : Over (Spec (CommRingCat.of R))} (n : ℕ)
    (σ : T.left ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))) (hσ : σ ≫ thick R I n = T.hom) : IsAdicColimit I T := by
  intro X f hf
  let s : T.left ⟶ (thickObj R I n T).left := pullback.lift (𝟙 _) σ ((Category.id_comp _).trans hσ.symm)
  have hs : s ≫ thickι I n T = 𝟙 _ := pullback.lift_fst _ _ _
  have key : ∀ (m k : ℕ) (W : Scheme.{0}) (a : W ⟶ (thickObj R I m T).left) (b : W ⟶ (thickObj R I (m + k) T).left),
      a ≫ thickι I m T = b ≫ thickι I (m + k) T → a ≫ f m = b ≫ f (m + k) := by
    intro m k
    induction k generalizing m with
    | zero => intro W a b h; rw [(cancel_mono _).1 h]; rfl
    | succ k ih =>
      intro W a b h
      have := ih (m + 1) W (a ≫ thickMap R I m T)
      rw [show m + 1 + k = m + (k + 1) by omega] at this
      rw [← this b (by rw [Category.assoc, thickMap_ι, h]), Category.assoc, hf]
  refine ⟨s ≫ f n, fun e => ?_, fun g hg => by rw [← hg n, reassoc_of% hs]⟩
  rw [← Category.assoc]
  rcases le_total e n with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [← key e k _ (𝟙 _) _ (by rw [Category.assoc, hs, Category.id_comp, Category.comp_id]), Category.id_comp]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [key n k _ _ (𝟙 _) (by rw [Category.assoc, hs, Category.id_comp, Category.comp_id]), Category.id_comp]

end GlobalTheory.AdicColimit
end
end

section

set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem bilinPart_eigen_mem_range : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (a : O) (u u' : Fin d → R) (α α' : R), (dAct k B a).mulVec (fun i => algebraMap R k (u i)) = algebraMap R k α • (fun i => algebraMap R k (u i)) → (dAct k B (star a)).mulVec (fun i => algebraMap R k (u' i)) = algebraMap R k α' • (fun i => algebraMap R k (u' i)) → IsUnit (α - α') → dotProduct (fun i => algebraMap R k (u i)) ((bilinPart k h).mulVec (fun i => algebraMap R k (u' i))) ∈ (algebraMap R k).range := by
  intro R _ d O _ _ k _ _ _ B h hc a u u' α α' hu hu' hα
  choose M hM using fun i j => WickVanishing.M_int B h hc a i j
  set v : Fin d → k := fun i => algebraMap R k (u i) with hv
  set v' : Fin d → k := fun i => algebraMap R k (u' i) with hv'
  have hS : sg1 k h = -(bilinPart k h).transpose := by
    ext i j
    simp only [WickVanishing.gaugeBilinearTerm_eq_neg_double_sum, Matrix.neg_apply, Matrix.transpose_apply, bilinPart]
  have e1 : dotProduct v' ((sg1 k h * dAct k B a - (dAct k B (star a)).transpose * sg1 k h).mulVec v) =
      -(algebraMap R k (α - α') * dotProduct v ((bilinPart k h).mulVec v')) := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu, dotProduct_sub,
      Matrix.dotProduct_mulVec v' (dAct k B (star a)).transpose, Matrix.vecMul_transpose, hu', Matrix.mulVec_smul,
      dotProduct_smul, smul_dotProduct, hS, Matrix.neg_mulVec, dotProduct_neg,
      Matrix.dotProduct_mulVec v', Matrix.vecMul_transpose, dotProduct_comm _ v, map_sub]
    simp only [smul_eq_mul]
    ring
  have e2 : dotProduct v' ((sg1 k h * dAct k B a - (dAct k B (star a)).transpose * sg1 k h).mulVec v) =
      algebraMap R k (∑ i, u' i * ∑ j, M i j * u j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hM, dotProduct, Matrix.mulVec, hv, hv']
  obtain ⟨w, hw⟩ := hα.exists_left_inv
  refine ⟨-(w * ∑ i, u' i * ∑ j, M i j * u j), ?_⟩
  rw [map_neg, map_mul, ← e2, e1, mul_neg, neg_neg, ← mul_assoc, ← map_mul, hw, map_one, one_mul]

end GlobalTheory
end
