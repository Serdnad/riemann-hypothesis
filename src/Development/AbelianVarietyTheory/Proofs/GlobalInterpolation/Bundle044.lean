module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPoint
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasurePreservingGlue
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle038
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle037
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle033
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle034
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle012
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionUniqueSimpleExceptionalZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionZeroFreeRegion
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormDiscriminantSuperlatticeOddIndexEq
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExtensionRepIndexTwoOfTraceInvariant
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle043
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FinalB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003

@[expose] public section

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

namespace GlobalTheory.SphereMassProof

theorem qf_pos_eq (M : ℕ) (x : Sp M 0) : qf x = ∑ i, ‖x i‖ ^ 2 := by
  simp [qf, Fintype.sum_sum_type, Complex.normSq_eq_norm_sq]

theorem dx_ball (M : ℕ) (hM : 1 ≤ M) (b : ℝ) (hb : 0 ≤ b) :
    dx M 0 {x | qf x ≤ b} = ENNReal.ofReal ((2 * Real.pi) ^ M / (M.factorial : ℝ) * b ^ M) := by
  haveI : Nonempty (Fin M ⊕ Fin 0) := ⟨Sum.inl ⟨0, hM⟩⟩
  have h := Complex.volume_sum_rpow_le (Fin M ⊕ Fin 0) (p := 2) (by norm_num) (Real.sqrt b)
  have e : {x : Sp M 0 | qf x ≤ b} =
      {x : Fin M ⊕ Fin 0 → ℂ | (∑ i, ‖x i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ Real.sqrt b} := by
    ext x
    simp only [Set.mem_setOf_eq, ← Real.sqrt_eq_rpow, Real.rpow_two, qf_pos_eq]
    exact (Real.sqrt_le_sqrt_iff hb).symm
  have hc : Fintype.card (Fin M ⊕ Fin 0) = M := by simp
  rw [dx, Measure.smul_apply, e, h, hc, smul_eq_mul]
  have g1 : Real.Gamma (2 / 2 + 1) = 1 := by
    rw [show (2 / 2 + 1 : ℝ) = 2 by norm_num, Real.Gamma_two]
  have g2 : Real.Gamma (2 * (M : ℝ) / 2 + 1) = M.factorial := by
    rw [show (2 * (M : ℝ) / 2 + 1) = M + 1 by ring, Real.Gamma_nat_eq_factorial]
  rw [g1, g2, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), pow_mul, Real.sq_sqrt hb,
    ← ENNReal.ofReal_mul (by positivity), show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [mul_pow, add_zero]
  ring

theorem isCompact_shell (M : ℕ) : IsCompact {x : Sp M 0 | qf x ∈ Set.Icc (1 / 2 : ℝ) 2} := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_Icc.preimage GlobalTheory.RealPlaceCompare.continuous_qf) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Sp M 0)) (r := 2)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  have h1 : ‖x i‖ ^ 2 ≤ ∑ j, ‖x j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖x j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : qf x ≤ 2 := hx.2
  rw [qf_pos_eq] at h2
  nlinarith [norm_nonneg (x i)]

theorem exists_mass {M : ℕ} {fib : ℝ → Measure (Sp M 0)} (h : IsDxDq fib) :
    ∃ G : ℝ → ℝ, Continuous G ∧ (∀ t, 0 ≤ G t) ∧
      ∀ t ∈ Set.Icc (1 / 2 : ℝ) 2, fib t Set.univ = ENNReal.ofReal (G t) := by
  obtain ⟨χ, h1, hc, hs, h01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (isCompact_shell M) (isOpen_ne (x := (0 : Sp M 0))) (by
      rintro x hx rfl
      have : (1 / 2 : ℝ) ≤ qf (0 : Sp M 0) := hx.1
      rw [qf_pos_eq] at this
      norm_num at this)
  obtain ⟨hi, hg⟩ := h.2.2 χ χ.continuous hc hs
  refine ⟨fun t => ∫ v, χ v ∂(fib t), continuousOn_univ.1 hg,
    fun t => integral_nonneg fun v => (h01 v).1, fun t ht => ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal (hi t trivial)
    (Filter.Eventually.of_forall fun v => (h01 v).1), ← lintegral_one]
  apply lintegral_congr_ae
  filter_upwards [GlobalTheory.RealPlaceCompare.ae_qf h t] with v hv
  have : χ v = 1 := h1 (show qf v ∈ Set.Icc (1 / 2 : ℝ) 2 from hv ▸ ht)
  simp [this]

theorem dx_shell {M : ℕ} {fib : ℝ → Measure (Sp M 0)} (h : IsDxDq fib) (a b : ℝ) (ha : 0 ≤ a) :
    dx M 0 (qf ⁻¹' Set.Ioc a b) = ∫⁻ t in Set.Ioc a b, fib t Set.univ := by
  have hq : Measurable (qf : Sp M 0 → ℝ) := GlobalTheory.RealPlaceCompare.continuous_qf.measurable
  have hO : MeasurableSet {x : Sp M 0 | x ≠ 0} := isOpen_ne.measurableSet
  have key := GlobalTheory.IsFibreFamily_lintegral_preimage hq isOpen_ne subset_rfl h
    (({x : Sp M 0 | x ≠ 0}).indicator 1) (measurable_one.indicator hO)
    (fun v hv => Set.indicator_of_notMem hv _) (Set.Ioc a b) measurableSet_Ioc
  have hsub : qf ⁻¹' Set.Ioc a b ⊆ {x : Sp M 0 | x ≠ 0} := by
    rintro x hx rfl
    have : a < qf (0 : Sp M 0) := hx.1
    rw [qf_pos_eq] at this
    norm_num at this
    linarith
  rw [Set.indicator_indicator, Set.inter_eq_left.2 hsub,
    lintegral_indicator_one (hq measurableSet_Ioc), Measure.restrict_apply (hq measurableSet_Ioc),
    Set.inter_eq_left.2 hsub] at key
  rw [key]
  refine lintegral_congr fun t => ?_
  rw [lintegral_indicator_one hO]
  refine measure_congr (Filter.eventuallyEq_univ.2 ?_)
  have h1 : ∀ᵐ y ∂(fib t), y ∈ qf ⁻¹' {id t} ∩ {x : Sp M 0 | x ≠ 0} := h.1 t
  filter_upwards [h1] with y hy using hy.2

theorem sphereMass : SphereMass := by
  intro M hM
  refine ⟨GlobalTheory.RealPlaceCompare.exists_isDxDq M 0, fun fib h => ?_⟩
  obtain ⟨G, hG, hG0, hGm⟩ := exists_mass h
  have hq : Measurable (qf : Sp M 0 → ℝ) := GlobalTheory.RealPlaceCompare.continuous_qf.measurable
  set C : ℝ := (2 * Real.pi) ^ M / (M.factorial : ℝ) with hC
  have hC0 : 0 ≤ C := by have := Real.pi_pos; positivity
  have hint : ∀ b ∈ Set.Ioo (1 / 2 : ℝ) 2,
      ∫ t in (1 / 2 : ℝ)..b, G t = C * b ^ M - C * (1 / 2) ^ M := by
    intro b hb
    have hb0 : 0 ≤ b := by linarith [hb.1]
    have e1 : qf ⁻¹' Set.Ioc (1 / 2 : ℝ) b =
        {x : Sp M 0 | qf x ≤ b} \ {x | qf x ≤ 1 / 2} := by
      ext x; simp [and_comm]
    have e2 := dx_shell h (1 / 2) b (by norm_num)
    have hfin : dx M 0 {x : Sp M 0 | qf x ≤ 1 / 2} ≠ ⊤ := by
      rw [dx_ball M hM _ (by norm_num)]; exact ENNReal.ofReal_ne_top
    rw [e1, measure_diff (s₁ := {x : Sp M 0 | qf x ≤ b}) (s₂ := {x : Sp M 0 | qf x ≤ 1 / 2})
      (fun x (hx : qf x ≤ 1 / 2) => (hx.trans hb.1.le : qf x ≤ b))
      (measurableSet_le hq measurable_const).nullMeasurableSet hfin,
      dx_ball M hM _ hb0, dx_ball M hM _ (by norm_num), ← hC,
      ← ENNReal.ofReal_sub _ (by positivity),
      setLIntegral_congr_fun measurableSet_Ioc
        (fun t ht => hGm t ⟨ht.1.le, ht.2.trans hb.2.le⟩),
      ← ofReal_integral_eq_lintegral_ofReal (hG.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (Filter.Eventually.of_forall hG0)] at e2
    rw [intervalIntegral.integral_of_le hb.1.le]
    refine ((ENNReal.ofReal_eq_ofReal_iff ?_ (integral_nonneg hG0)).1 e2).symm
    have : (1 / 2 : ℝ) ^ M ≤ b ^ M := pow_le_pow_left₀ (by norm_num) hb.1.le M
    nlinarith
  have d1 : HasDerivAt (fun b => ∫ t in (1 / 2 : ℝ)..b, G t) (G 1) 1 :=
    (hG.integral_hasStrictDerivAt _ _).hasDerivAt
  have d2 : HasDerivAt (fun b : ℝ => C * b ^ M - C * (1 / 2) ^ M)
      (C * ((M : ℝ) * 1 ^ (M - 1))) 1 := ((hasDerivAt_pow M 1).const_mul C).sub_const _
  have d3 : HasDerivAt (fun b => ∫ t in (1 / 2 : ℝ)..b, G t) (C * ((M : ℝ) * 1 ^ (M - 1))) 1 := by
    refine d2.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num) (show (1 : ℝ) < 2 by norm_num)]
      with b hb using hint b hb
  rw [hGm 1 ⟨by norm_num, by norm_num⟩, d1.unique d3, hC, cM]
  congr 1
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  have hk : ((k.factorial : ℝ)) ≠ 0 := by positivity
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    one_pow, mul_one]
  field_simp

end GlobalTheory.SphereMassProof
end

section

namespace GlobalTheory.ThetaWeberObj

theorem thetaWeberStatement : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeberStatement :=
  GlobalTheory.ThetaWeberRoad.thetaWeberStatement_of Formalism.L2.Th1.F.thetaLine Formalism.L2.Th1.F.sgStarBasic
    Formalism.L2.Th1.F.sgStarAdd

end GlobalTheory.ThetaWeberObj
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

theorem rowDiv_smul_rat {r n : ℕ} (a b : Fin r) (k : ℕ) (c : ℚ)
    (f : MvPolynomial (Fin r × Fin n) ℚ) : rowDiv ℚ a b k (c • f) = c • rowDiv ℚ a b k f := by
  simp only [rowDiv, map_smul, Polynomial.coeff_smul]

theorem gel_hw_rat (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) (k : ℕ) :
    gel ℚ N N k (hw ℚ le_rfl ν) = hcVal ℚ (fun i => (ν i : ℚ)) k • hw ℚ le_rfl ν := by
  have hrel := (GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange ℚ N N).1
  have hwt := GlobalTheory.T.rowPolarizationOperators_action_on_rowWeight ℚ N N (rowNu (r := N) ν) (hw ℚ le_rfl ν) (hwRowWeight ℚ N N le_rfl ν hν)
  have hnu : ∀ a : Fin N, rowNu (r := N) ν a = ν a := by
    intro a
    simp [rowNu]
  have key := GlobalTheory.T.trace_glMatrixUnit_pow_highestWeight_mod ℚ (MvPolynomial (Fin N × Fin N) ℚ) N (rowE ℚ N N) hrel ⊥
    (fun a b f hf => by
      rw [Submodule.mem_bot] at hf ⊢
      rw [hf, map_zero])
    (fun i => (ν i : ℚ)) (hw ℚ le_rfl ν)
    (fun a b hab => by
      rw [Submodule.mem_bot, (GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange ℚ N N).2.1 a b]
      exact hwRaise ℚ N N le_rfl ν a b 1 hab le_rfl)
    (fun a => by
      rw [Submodule.mem_bot, hwt.1 a, hnu a, sub_self]) k
  rw [Submodule.mem_bot, sub_eq_zero] at key
  exact key

theorem gel_dualWeyl_rat (N : ℕ) (ν : Fin N → ℕ) (hν : Antitone ν) (k : ℕ)
    (f : MvPolynomial (Fin N × Fin N) ℚ) (hf : f ∈ dualWeyl ℚ N N ν) :
    gel ℚ N N k f = hcVal ℚ (fun i => (ν i : ℚ)) k • f := by
  set c : ℚ := hcVal ℚ (fun i => (ν i : ℚ)) k with hc
  have hrel := (GlobalTheory.T.rowPolarizationOperators_relations_divPow_baseChange ℚ N N).1
  have hcomm : ∀ a b, gel ℚ N N k * rowE ℚ N N a b = rowE ℚ N N a b * gel ℚ N N k := fun a b =>
    ((GlobalTheory.T.glMatrixUnit_pow_commutator_and_trace_central (Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ)) N (rowE ℚ N N) hrel k).2 a b).symm
  let M : Submodule ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
    dualWeyl ℚ N N ν ⊓ LinearMap.ker (gel ℚ N N k - c • (LinearMap.id))
  have hmem : ∀ g, g ∈ M ↔ g ∈ dualWeyl ℚ N N ν ∧ gel ℚ N N k g = c • g := by
    intro g
    simp [M, Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
  have hle : M ≤ dualWeyl ℚ N N ν := inf_le_left
  have hclosed : RowDivClosed M := by
    intro a b j g hg
    obtain ⟨hg1, hg2⟩ := (hmem g).1 hg
    refine (hmem _).2 ⟨rowDivStable ℚ N N ν a b j g hg1, ?_⟩
    rw [GlobalTheory.Alc.comm_rowDiv_of_comm_rowE N N (gel ℚ N N k) hcomm a b j g, hg2, rowDiv_smul_rat]
  have hhw : hw ℚ le_rfl ν ∈ M :=
    (hmem _).2 ⟨hwMem ℚ N N le_rfl ν hν, gel_hw_rat N ν hν k⟩
  have heq := closedEqNabla N N le_rfl ν hν M hle hclosed hhw
  exact ((hmem f).1 (heq ▸ hf)).2

end GlobalTheory.Alc
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.SWQ

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem Bd_add_left_AF (a : Fin N → F) (u v w : Fin N → AF F) :
    Bd (AF F) a (u + v) w = Bd (AF F) a u w + Bd (AF F) a v w := by
  simp only [Bd, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem Bd_rat_rat (a : Fin N → F) (η ξ : Fin N → F) :
    Bd (AF F) a (rat η) (rat ξ) = algebraMap F (AF F) (Bd F a η ξ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Bd, rat, map_sum, map_mul, Algebra.algebraMap_self, RingHom.id_apply]

theorem charOrth : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ ξ : Fin N → F, ξ ≠ 0 → ∫ u in D, ψ (Bd (AF F) a u (rat ξ)) ∂(muV N ν) = 0 := by
  intro F _ _ N ψ lam ν a hC D hD _ ξ hξ
  haveI := hC.2.2.2.1.1
  have hmem : ∀ u : Fin N → AF F, u ∈ AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) →
      ∃ η, u = rat η := by
    let φ : (Fin N → F) →+ (Fin N → AF F) :=
      AddMonoidHom.mk' rat (fun x y => by funext l; simp only [rat, Pi.add_apply, map_add (f := _)])
    intro u hu
    have hle : AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) ≤ φ.range :=
      (AddSubgroup.closure_le _).mpr (by rintro _ ⟨η, rfl⟩; exact ⟨η, rfl⟩)
    obtain ⟨η, hη⟩ := hle hu
    exact ⟨η, hη.symm⟩
  haveI : (muV N ν).IsAddLeftInvariant := by unfold muV; infer_instance
  haveI : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  haveI : Countable (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) := by
    have hs : (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))) :
        Set (Fin N → AF F)).Countable :=
      (Set.countable_range (rat : (Fin N → F) → (Fin N → AF F))).mono fun u hu => by
        obtain ⟨η, rfl⟩ := hmem u hu
        exact ⟨η, rfl⟩
    exact hs.to_subtype
  obtain ⟨_, ⟨_, _, hF, x, hx⟩, _, _, ha⟩ := hC
  have hadd : ∀ u v : Fin N → AF F, ψ (Bd (AF F) a (u + v) (rat ξ)) =
      ψ (Bd (AF F) a u (rat ξ)) * ψ (Bd (AF F) a v (rat ξ)) := fun u v => by
    rw [Bd_add_left_AF, AddChar.map_add_eq_mul]
  have hper : ∀ g ∈ AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F))),
      ∀ u, ψ (Bd (AF F) a (g + u) (rat ξ)) = ψ (Bd (AF F) a u (rat ξ)) := by
    intro g hg u
    obtain ⟨η, rfl⟩ := hmem g hg
    rw [hadd, Bd_rat_rat, hF, one_mul]
  obtain ⟨l, hl⟩ : ∃ l, ξ l ≠ 0 := by
    by_contra h
    push_neg at h
    exact hξ (funext h)
  have hc : (2 * a l * ξ l) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (ha l)) hl
  set u₀ : Fin N → AF F := Pi.single l (algebraMap F (AF F) (2 * a l * ξ l)⁻¹ * x) with hu₀def
  have hu₀ : ψ (Bd (AF F) a u₀ (rat ξ)) = ψ x := by
    congr 1
    simp only [Bd, rat]
    rw [Finset.sum_eq_single l]
    · rw [hu₀def, Pi.single_eq_same]
      have e : algebraMap F (AF F) (2 * a l) * (algebraMap F (AF F) (2 * a l * ξ l)⁻¹ * x) *
          algebraMap F (AF F) (ξ l) = algebraMap F (AF F) (2 * a l * ξ l * (2 * a l * ξ l)⁻¹) * x := by
        simp only [map_mul]; ring
      rw [e, mul_inv_cancel₀ hc, map_one, one_mul]
    · intro b _ hb
      rw [hu₀def, Pi.single_eq_of_ne hb]
      simp
    · intro h; exact absurd (Finset.mem_univ l) h
  have hD' := hD.vadd_of_comm u₀
  have h1 := hD.setIntegral_eq hD' (f := fun u => ψ (Bd (AF F) a u (rat ξ))) (fun g s => by
    show ψ (Bd (AF F) a ((g : Fin N → AF F) + s) (rat ξ)) = _
    exact hper g g.2 s)
  have h2 := (measurePreserving_add_left (muV N ν) u₀).setIntegral_image_emb
    (measurableEmbedding_addLeft u₀) (fun u => ψ (Bd (AF F) a u (rat ξ))) D
  have e : u₀ +ᵥ D = (fun s => u₀ + s) '' D := rfl
  rw [e, h2] at h1
  simp only [hadd, hu₀] at h1
  rw [integral_const_mul] at h1
  have hx1 : (1 : ℂ) - ψ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have : ((1 : ℂ) - ψ x) * ∫ u in D, ψ (Bd (AF F) a u (rat ξ)) ∂(muV N ν) = 0 := by
    rw [sub_mul, one_mul, ← h1, sub_self]
  exact (mul_eq_zero.mp this).resolve_left hx1

end GlobalTheory.SWQ
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.SWQ

theorem exists_adeles_haarMeasure_covolume_one : ∀ (F : Type) [Field F] [NumberField F], ∃ ν : Measure (AF F), IsCov1 ν := by
  intro F _ _
  let Γ : AddSubgroup (AF F) := (algebraMap F (AF F)).range.toAddSubgroup
  have hdisc : DiscreteTopology Γ := by
    obtain ⟨U, hU, hU0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
    obtain ⟨V, hVU, hVo, h0V⟩ := mem_nhds_iff.1 hU
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have : ({0} : Set Γ) = ((↑) : Γ → AF F) ⁻¹' V := by
      ext ⟨x, hx⟩
      obtain ⟨y, rfl⟩ := hx
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · intro h
        have : algebraMap F (AF F) y = 0 := congrArg Subtype.val h
        rw [this]; exact h0V
      · intro h
        have := hU0 y (hVU h)
        subst this
        ext; simp
    rw [this]
    exact hVo.preimage continuous_subtype_val
  letI : MeasurableSpace (Multiplicative (AF F)) := borel _
  haveI : BorelSpace (Multiplicative (AF F)) := ⟨rfl⟩
  haveI : SecondCountableTopology (Multiplicative (AF F)) := inferInstanceAs (SecondCountableTopology (AF F))
  haveI : DiscreteTopology (AddSubgroup.toSubgroup Γ) := hdisc
  obtain ⟨hc, D, hDm, hD⟩ := GlobalTheory.discreteSubgroup_countable_and_exists_strict_fundamentalDomain (AddSubgroup.toSubgroup Γ)
  haveI : Countable Γ := hc
  let D' : Set (AF F) := Multiplicative.ofAdd ⁻¹' D
  have hDm' : MeasurableSet D' := hDm
  have hfd : ∀ m : Measure (AF F), IsAddFundamentalDomain Γ D' m := by
    intro m
    refine IsAddFundamentalDomain.mk' hDm'.nullMeasurableSet ?_
    intro x
    obtain ⟨γ, hγ, huniq⟩ := hD (Multiplicative.ofAdd x)
    refine ⟨⟨γ.1.toAdd, γ.2⟩, hγ, ?_⟩
    intro g hg
    have := huniq ⟨Multiplicative.ofAdd g.1, g.2⟩ hg
    ext
    exact congrArg (fun s => Multiplicative.toAdd s.1) this
  let μ : Measure (AF F) := Measure.addHaar
  have hμD := hfd μ
  obtain ⟨K, hK, hKx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  have hfin : μ D' < ∞ := by
    calc μ D' ≤ μ (⋃ γ : Γ, (γ +ᵥ K) ∩ D') := by
          apply measure_mono
          intro d hd
          obtain ⟨x, hx⟩ := hKx d
          refine Set.mem_iUnion.2 ⟨⟨algebraMap F (AF F) x, x, rfl⟩, ?_, hd⟩
          refine ⟨_, hx, ?_⟩
          show algebraMap F (AF F) x + (d - algebraMap F (AF F) x) = d
          abel
      _ ≤ ∑' γ : Γ, μ ((γ +ᵥ K) ∩ D') := measure_iUnion_le _
      _ = μ K := (hμD.measure_eq_tsum K).symm
      _ < ∞ := hK.measure_lt_top
  have hpos : μ D' ≠ 0 := by
    intro h0
    have := hμD.measure_eq_tsum' Set.univ
    simp only [Set.univ_inter] at this
    have h2 : ∀ g : Γ, μ (g +ᵥ D') = 0 := fun g => by
      rw [measure_vadd]; exact h0
    simp only [h2, tsum_zero] at this
    exact (Measure.measure_univ_ne_zero.2 (NeZero.ne μ)) this
  refine ⟨(μ D')⁻¹ • μ, ?_, D', hDm', hfd _, ?_⟩
  · exact Measure.IsAddHaarMeasure.smul (μ := μ) (ENNReal.inv_ne_zero.2 hfin.ne) (ENNReal.inv_ne_top.2 hpos)
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin.ne]

end GlobalTheory.SWQ
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.rayClassLFunction_unique_simple_exceptional_zero : ∃ c : ℝ, 0 < c ∧ ∀ (𝓕 : LFam) (χ ψ : AddChar 𝓕.G ℂ) (β β' : ℝ), χ * χ = 1 → ψ * ψ = 1 → 3 / 4 ≤ β → 3 / 4 ≤ β' → 1 - c / 𝓕.ell 0 ≤ β → 1 - c / 𝓕.ell 0 ≤ β' → 𝓕.F χ β = 0 → 𝓕.F ψ β' = 0 → χ = ψ ∧ β = β' ∧ deriv (𝓕.F χ) β ≠ 0 := by
  first | exact @GlobalTheory.Hk.RealZero.main | exact GlobalTheory.Hk.RealZero.main | (intros; apply GlobalTheory.Hk.RealZero.main <;> assumption)
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.rayClassLFunction_zero_free_region : ∃ c : ℝ, 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 3 / 4 ≤ s.re → 𝓕.F χ s = 0 → (χ * χ ≠ 1 ∨ s.im ≠ 0) → s.re < 1 - c / 𝓕.ell s.im := by
  first | exact @GlobalTheory.Hk.ZeroFree.zero_free_region | exact GlobalTheory.Hk.ZeroFree.zero_free_region | (intros; apply GlobalTheory.Hk.ZeroFree.zero_free_region <;> assumption)
end

section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

theorem _root_.GlobalTheory.T.norm_discriminant_superlattice_odd_index_eq : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (L' : PeriodPair) (N : ℕ), q ≠ 2 → M.Ok → Nat.Coprime N (2 * q) → M.L.lattice ≤ L'.lattice → (∀ x ∈ L'.lattice, (N : ℂ) * x ∈ M.L.lattice) → ‖M.ι (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2)‖ = ‖M.ι (M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2)‖ := by
  first | exact @GlobalTheory.MomDisc.norm_disc_eq | exact GlobalTheory.MomDisc.norm_disc_eq | (intros; apply GlobalTheory.MomDisc.norm_disc_eq <;> assumption)
end

section

open Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.exists_extension_rep_index_two_of_trace_invariant : ∀ (Γ k : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [CharZero k] [IsAlgClosed k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ) (η : Γ →* ℤˣ), IsOpen (η.ker : Set Γ) → ∀ r : η.ker →* GL (Fin n) k, Continuous r → IsSSRep r → (∀ (g : Γ) (h h' : η.ker), (h' : Γ) = g * h * g⁻¹ → ((r h' : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((r h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∃ ρ : Γ →* GL (Fin n) k, Continuous ρ ∧ IsSSRep ρ ∧ ∀ h : η.ker, ρ h = r h := by
  first | exact @GlobalTheory.IndexTwoExt.main | exact GlobalTheory.IndexTwoExt.main | (intros; apply GlobalTheory.IndexTwoExt.main <;> assumption)
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

theorem _root_.GlobalTheory.T.sum_norm_sq_primitive_char_sum_le : ∀ (Q M N : ℕ) (a : ℕ → ℂ), 1 ≤ Q → ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}, ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod (q + 1))‖ ^ 2 ≤ ((Q : ℝ) ^ 2 + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  first | exact @GlobalTheory.multiplicative_large_sieve | exact GlobalTheory.multiplicative_large_sieve | (intros; apply GlobalTheory.multiplicative_large_sieve <;> assumption)
end
