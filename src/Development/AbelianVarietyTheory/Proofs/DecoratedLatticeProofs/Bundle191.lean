module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMajorantCoordinateCosetMeasure
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle168
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle181
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle167
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle088
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle171
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSplitsHyperbolicPlusCore
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

theorem _root_.GlobalTheory.T.heisenbergTranslate_theta_continuous_differentiable_sobolev : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (k : ℕ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → Filter.Tendsto (fun u : WO S T => supSob ψ θ k (heisO ψ S T u f - f)) (nhds 0) (nhds 0) ∧ ∀ L : ℝ →+ WO S T, Continuous L → (∀ t, (L t).map (finPart D) = 0) → IsThetaFunO ψ S T (fun p => deriv (fun t : ℝ => heisO ψ S T (L t) f p) 0) ∧ Filter.Tendsto (fun t : ℝ => supSob ψ θ k ((t⁻¹ : ℂ) • (heisO ψ S T (L t) f - f) - fun p => deriv (fun t : ℝ => heisO ψ S T (L t) f p) 0)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  first | exact @GlobalTheory.HeisTaylor.heisO_taylor | exact GlobalTheory.HeisTaylor.heisO_taylor | (intros; apply GlobalTheory.HeisTaylor.heisO_taylor <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

theorem _root_.GlobalTheory.T.integrable_majorant_coordinate_coset_measure : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (P : Fin m → Fin n → Prop) (a : Mx D m n) (μ : Measure (Mx D m n)), IsFiniteMeasureOnCompacts μ → (∀ᵐ x ∂μ, ∀ i j, ¬ P i j → x i j = a i j) → (∀ t : Mx D m n, (∀ i j, ¬ P i j → t i j = 0) → Measure.map (fun x => x + t) μ = μ) → ∃ N : ℕ, ∀ K : Set (Mx D m n), IsCompact K → Integrable (maj θ K N) μ := by
  first | exact @GlobalTheory.Unf.MajInt.maj_integrable | exact GlobalTheory.Unf.MajInt.maj_integrable | (intros; apply GlobalTheory.Unf.MajInt.maj_integrable <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SuperposS

variable {D : D7}

theorem symplOH_zero_right {S T : HSp D} (x : WO S T) : symplOH S T x 0 = 0 := by
  simpa using GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := T) x 0 0

theorem symplOH_zero_left {S T : HSp D} (x : WO S T) : symplOH S T 0 x = 0 := by
  simpa using GlobalTheory.OrientedHeis.symplOH_add_left (S := S) (T := T) 0 0 x

theorem psi_neg_mul (ψ : AddChar (AF D.host.F) ℂ) (s : AF D.host.F) : ψ (-s) * ψ s = 1 := by
  rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

variable {S A B T : HSp D} (o : OrthDec S A B)

theorem symm_add (r u : WO A T) (y : WO B T) :
    (o.resS T).symm (u + r, y) = (o.resS T).symm (u, y) + (o.resS T).symm (r, 0) := by
  rw [← map_add (f := _)]; simp

theorem sympl_ext_right (r u : WO A T) (y : WO B T) :
    symplOH S T ((o.resS T).symm (u, y)) ((o.resS T).symm (r, 0)) = symplOH A T u r := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp [symplOH_zero_right]

theorem sympl_ext_left (r u : WO A T) (y : WO B T) :
    symplOH S T ((o.resS T).symm (r, 0)) ((o.resS T).symm (u, y)) = symplOH A T r u := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp [symplOH_zero_left]

def ext0 (T : HSp D) : WO A T →+ WO S T := (o.resS T).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

theorem matrixExtendByZero_apply (r : WO A T) : ext0 o T r = (o.resS T).symm (r, 0) := rfl

theorem continuous_wittExtendByZero : Continuous (ext0 o T) :=
  (o.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const)

theorem matrixExtendByZero_map {R : Type} [Semiring R] (f : AE D →+* R) (r : WO A T) (h : r.map f = 0) : (ext0 o T r).map f = 0 := by
  rw [matrixExtendByZero_apply, o.resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.map_mul, h, Matrix.zero_mul]

theorem homExtensionByZeroOrthDecomp_rational (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) : ext0 o T (ratW T A γ) = ratW T S (γ * o.qA) := by
  rw [matrixExtendByZero_apply, o.resS_symm_apply, Matrix.zero_mul, add_zero, OrthDec.pA, ratW, ratW, rat, Matrix.map_mul]

end GlobalTheory.SuperposS

namespace GlobalTheory.SuperposS

theorem superpos_isTheta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO B T) (a : Ω → ℂ), Measurable k → Integrable a μ → IsThetaFunO ψ A T fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ := by
  intro D ψ hψ S A B T o F hF Ω _ μ k a hk ha
  haveI : BorelSpace (WO B T) := ⟨rfl⟩
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF
  have hFm : ∀ u : WO A T, Measurable fun w => F ((o.resS T).symm (u, k w)) := fun u =>
    (hF.cont.comp ((o.continuous_resS_symm T).comp (continuous_const.prodMk continuous_id))).measurable.comp hk
  refine ⟨fun γ u => ?_, ?_, ?_, ?_⟩
  ·
    beta_reduce
    have e : ∀ w, a w * F ((o.resS T).symm (ratW T A γ + u, k w)) =
        ψ (-symplOH A T (ratW T A γ) u) * (a w * F ((o.resS T).symm (u, k w))) := by
      intro w
      rw [add_comm, symm_add, add_comm, ← matrixExtendByZero_apply, homExtensionByZeroOrthDecomp_rational, hF.quasi, ← homExtensionByZeroOrthDecomp_rational, matrixExtendByZero_apply, sympl_ext_left]
      ring
    simp_rw [e]
    exact integral_const_mul _ _
  ·
    obtain ⟨U, hU, hl⟩ := hF.level
    refine ⟨U.comap (ext0 o T), hU.preimage (continuous_wittExtendByZero o), fun u hu h0 => ?_⟩
    have hj := hl _ hu (matrixExtendByZero_map o _ u h0)
    funext v
    simp only [heisO]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only []
    have e := congrFun hj ((o.resS T).symm (v, k w))
    simp only [heisO] at e
    rw [symm_add, ← matrixExtendByZero_apply]
    conv_rhs => rw [← e]
    rw [matrixExtendByZero_apply, sympl_ext_right]
    ring
  ·
    obtain ⟨-, -, i3, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank A.rank
    haveI : FirstCountableTopology (WO A T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
    refine continuous_of_dominated (bound := fun w => ‖a w‖ * C) (fun u => ?_) (fun u => ?_) (ha.norm.mul_const C) ?_
    · exact ha.aestronglyMeasurable.mul (hFm u).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun w => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    · refine Filter.Eventually.of_forall fun w => ?_
      exact continuous_const.mul (hF.cont.comp ((o.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const)))
  ·
    intro n L hLc hL0 w
    obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
    obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
    let L' : (Fin n → ℝ) →+ WO S T := (ext0 o T).comp L
    have hL'c : Continuous L' := (continuous_wittExtendByZero o).comp hLc
    have hL'0 : ∀ t, (L' t).map (finPart D) = 0 := fun t => matrixExtendByZero_map o _ (L t) (hL0 t)
    let M : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW T S :=
      ((GlobalTheory.FockCompare.piW θ T S).comp L').toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ T S).comp hL'c)
    let N : (Fin n → ℝ) →L[ℝ] GlobalTheory.FockCompare.RW T A :=
      ((GlobalTheory.FockCompare.piW θ T A).comp L).toRealLinearMap ((GlobalTheory.FockCompare.continuous_pi' hθ T A).comp hLc)
    have hM : ∀ t, L' t = GlobalTheory.FockCompare.iotaW σ T S (M t) := fun t => (h.iota_pi (hL'0 t)).symm
    have hN : ∀ t, L t = GlobalTheory.FockCompare.iotaW σ T A (N t) := fun t => (h.iota_pi (hL0 t)).symm
    let om := LinearMap.toContinuousLinearMap (GlobalTheory.OrientedHeis.omO A T (GlobalTheory.FockCompare.piW θ T A w))
    have key : ∀ t, (∫ x, a x * F ((o.resS T).symm (w + L t, k x)) ∂μ) =
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F ((o.resS T).symm (w, k x)) ∂μ := by
      intro t
      have hph : ψ (-symplOH A T w (L t)) = Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) := by
        have e1 : -symplOH A T w (L t) = symplOH A T w (L (-t)) := by
          rw [map_neg]
          have := GlobalTheory.OrientedHeis.symplOH_add_right (S := A) (T := T) w (L t) (-L t)
          rw [add_neg_cancel, symplOH_zero_right] at this
          linear_combination this
        rw [e1, hN (-t), GlobalTheory.OrientedHeis.psi_symplOH h hψ]
        rfl
      rw [← hph, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [heisO]
      rw [← hM, symm_add, ← matrixExtendByZero_apply]
      show _ = _ * (a x * (ψ (symplOH S T ((o.resS T).symm (w, k x)) ((o.resS T).symm (L t, 0))) * _))
      rw [sympl_ext_right]
      change a x * F (_ + ext0 o T (L t)) = ψ (-symplOH A T w (L t)) * (a x * (ψ (symplOH A T w (L t)) * F (_ + ext0 o T (L t))))
      have := psi_neg_mul ψ (symplOH A T w (L t))
      linear_combination (-(a x * F ((o.resS T).symm (w, k x) + (ext0 o T) (L t)))) * this
    have hf : (fun t => (fun u => ∫ x, a x * F ((o.resS T).symm (u, k x)) ∂μ) (w + L t)) = fun t =>
        Complex.exp (-(Real.pi * Complex.I) * ((om (N (-t)) : ℝ) : ℂ)) *
          ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (M t)) F ((o.resS T).symm (w, k x)) ∂μ :=
      funext key
    rw [hf]
    refine ContDiff.mul ?_ ((GlobalTheory.T.contDiff_heisenbergSuperposition_thetaFunction_real D θ σ h ψ hψ S T F hF Ω μ _ a ?_ ha).comp M.contDiff)
    · exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (om.contDiff.comp (N.contDiff.comp contDiff_neg))))
    · exact ((o.continuous_resS_symm T).comp (continuous_const.prodMk continuous_id)).measurable.comp hk

end GlobalTheory.SuperposS

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.isThetaFun_superposition_target_orthSummand : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (T A B S : HSp D) (o : OrthDec T A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO S B) (a : Ω → ℂ), Measurable k → Integrable a μ → IsThetaFunO ψ S A fun u => ∫ w, a w * F ((o.resT S).symm (u, k w)) ∂μ := by
  first | exact @GlobalTheory.SuperposT.superpos_target | exact GlobalTheory.SuperposT.superpos_target | (intros; apply GlobalTheory.SuperposT.superpos_target <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.theta_function_orthogonal_sum_approx_finite_sums : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (P : Fin n → WO A T → ℂ) (g : Fin n → WO B T → ℂ), (∀ i, Continuous (P i)) ∧ (∀ i (γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), P i (ratW T A γ + u) = ψ (-(symplOH A T (ratW T A γ) u)) * P i u) ∧ (∀ i, IsThetaFunO ψ B T (g i)) ∧ ∀ w, ‖f w - ∑ i, P i ((o.resS T) w).1 * g i ((o.resS T) w).2‖ ≤ ε := by
  first | exact @GlobalTheory.ThetaSplitApprox.exists_approx | exact GlobalTheory.ThetaSplitApprox.exists_approx | (intros; apply GlobalTheory.ThetaSplitApprox.exists_approx <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

theorem secW_cA (D : D7) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (hc : IsConjAt D.sp.cm.sig h c)
    (z : w.adicCompletion D.host.E) : secW hw h (c z) = cA D (secW hw h z) := by
  obtain ⟨y, rfl⟩ := (GlobalTheory.LFun.InertChart.complEquiv hw h).surjective z
  have e1 : c (GlobalTheory.LFun.InertChart.complEquiv hw h y) =
      GlobalTheory.LFun.InertChart.complEquiv hw h (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ D.sp.cm.sig y) := hc y
  rw [e1]
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _) =
    cA D (GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _))
  rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  exact (GlobalTheory.EmbChart.sigR_tensAt v _ y).symm

theorem thW_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsConjAt D.sp.cm.sig h c → (∀ z, c (c z) = z) → ∀ z, thW ψ hw h (k * c k) (c z) * thW ψ hw h (k * c k) z = 1 := by
  intro D ψ v w hw h c k hc hcc z
  have h1 : secW hw h (k * c k * c z) = cA D (secW hw h (k * c k * z)) := by
    rw [← secW_cA D hw h c hc]
    congr 1
    rw [map_mul c, map_mul c, hcc, mul_comm k (c k)]
  rw [thW_apply, thW_apply, h1, ← GlobalTheory.DualPairCheck.trace_cA (_ * cA D _), RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA,
    GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg, neg_mul, LinearMap.map_neg,
    ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]

end GlobalTheory.InertFrameLoc
end
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameSympl

open Formalism.UG (cT cT_mul cT_one antiJ)
open GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : IsInertAt D.host.F D.host.E v w} {h : w.under (𝓞 D.host.F) = v}

def evW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) : AE D →+* w.adicCompletion D.host.E :=
  (GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp (compFin D.host.F D.host.E v)

theorem secW_apply (z : w.adicCompletion D.host.E) :
    secW hw h z = GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z) := rfl

theorem secW_mul_right (z : w.adicCompletion D.host.E) (A : AE D) :
    secW hw h z * A = secW hw h (z * evW hw h A) := by
  rw [secW_apply, secW_apply, GlobalTheory.EmbChart.tensAt_mul_right]
  congr 1
  rw [map_mul (GlobalTheory.LFun.InertChart.complEquiv hw h).symm]
  show _ = _ * (GlobalTheory.LFun.InertChart.complEquiv hw h).symm ((GlobalTheory.LFun.InertChart.complEquiv hw h) _)
  rw [RingEquiv.symm_apply_apply]

theorem evW_secW (z : w.adicCompletion D.host.E) : evW hw h (secW hw h z) = z := by
  show GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v (GlobalTheory.EmbChart.tensAt D.host.E v
    ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z))) = z
  rw [GlobalTheory.EmbChart.compFin_tensAt, RingEquiv.apply_symm_apply]

theorem evW_incA (a : D.host.E) : evW hw h (incA D a) = algebraMap D.host.E _ a := by
  show GlobalTheory.LFun.toCompl h (compFin D.host.F D.host.E v ((1 : AF D.host.F) ⊗ₜ[D.host.F] a)) = _
  show GlobalTheory.LFun.toCompl h ((evFin D.host.F v 1) ⊗ₜ[D.host.F] a) = _
  rw [map_one, GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]

theorem incA_mul_secW (a : D.host.E) (z : w.adicCompletion D.host.E) :
    incA D a * secW hw h z = secW hw h (algebraMap D.host.E _ a * z) := by
  rw [mul_comm, secW_mul_right, evW_incA, mul_comm]

theorem cA_secW {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} (hc : GlobalTheory.LFun.IsConjAt D.sp.cm.sig h c)
    (z : w.adicCompletion D.host.E) : cA D (secW hw h z) = secW hw h (c z) := by
  rw [secW_apply, secW_apply]
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig (GlobalTheory.EmbChart.tensAt D.host.E v _) = GlobalTheory.EmbChart.tensAt D.host.E v _
  rw [GlobalTheory.EmbChart.sigR_tensAt]
  congr 1
  apply (GlobalTheory.LFun.InertChart.complEquiv hw h).injective
  rw [RingEquiv.apply_symm_apply]
  have := hc ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)
  exact this.symm.trans (congrArg c ((GlobalTheory.LFun.InertChart.complEquiv hw h).apply_symm_apply z))

theorem hO_map_secW {S T : HSp D} {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E}
    (hc : GlobalTheory.LFun.IsConjAt D.sp.cm.sig h c) (M N : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    hO S T (M.map (secW hw h)) (N.map (secW hw h)) = secW hw h (Matrix.trace
      ((S.gram⁻¹.map (algebraMap D.host.E (w.adicCompletion D.host.E)) : Matrix (Fin S.rank) (Fin S.rank) _) *
      cT c N * (T.gram.map (algebraMap D.host.E (w.adicCompletion D.host.E)) : Matrix (Fin T.rank) (Fin T.rank) _) * M)) := by

  simp only [hO, Matrix.map_apply, cA_secW hc, incA_mul_secW, secW_mul_right, evW_incA, evW_secW, ← map_sum]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Matrix.map_apply, cT, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm) ?_
  rw [Finset.sum_comm]

variable {L : Type} [Field L]

theorem cT_smul' (c : L →+* L) {m n : ℕ} (k : L) (A : Matrix (Fin m) (Fin n) L) : cT c (k • A) = c k • cT c A := by
  ext i j
  simp [cT, Matrix.smul_apply]

theorem inv_eq_of_frame (c : L →+* L) {n : ℕ} {G G' : Matrix (Fin n) (Fin n) L} (hG : G' * G = 1) (a : GL (Fin n) L)
    (ha : cT c a.1 * G * a.1 = antiJ L n) : G' = a.1 * antiJ L n * cT c a.1 := by
  have h1 : G * a.1 = cT c (a⁻¹).1 * antiJ L n := by
    rw [← ha, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Units.mul_inv, cT_one, Matrix.one_mul]
  have h2 : G * (a.1 * antiJ L n * cT c a.1) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc (cT c (a⁻¹).1),
      Formalism.UG.P.fIwasawa_antiJ_mul_antiJ, Matrix.mul_one, ← cT_mul, Units.mul_inv, cT_one]
  rw [← Matrix.mul_one G', ← h2, ← Matrix.mul_assoc, hG, Matrix.one_mul]

theorem trace_frame (c : L →+* L) {n n' : ℕ} (k : L) (aS : GL (Fin n) L) (aT : GL (Fin n') L)
    (GT J' : Matrix (Fin n') (Fin n') L) (J : Matrix (Fin n) (Fin n) L) (hT : cT c aT.1 * GT * aT.1 = J')
    (x y : Matrix (Fin n') (Fin n) L) :
    Matrix.trace (aS.1 * J * cT c aS.1 * cT c (k • (aT.1 * y * (aS⁻¹).1)) * GT * (k • (aT.1 * x * (aS⁻¹).1))) =
      k * c k * Matrix.trace (J * cT c y * J' * x) := by
  rw [cT_smul', cT_mul, cT_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cT c aS.1) (cT c (aS⁻¹).1), ← cT_mul, Units.inv_mul, cT_one, Matrix.one_mul,
    ← Matrix.mul_assoc GT aT.1, ← Matrix.mul_assoc (cT c aT.1) (GT * aT.1), ← Matrix.mul_assoc (cT c aT.1) GT, hT, Matrix.trace_mul_comm aS.1]
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  ring

theorem hO_uPt {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : IsInertAt D.host.F D.host.E v w} {h : w.under (𝓞 D.host.F) = v} {S T : HSp D}
    {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} (k : w.adicCompletion D.host.E)
    {aS : GL (Fin S.rank) (w.adicCompletion D.host.E)} {aT : GL (Fin T.rank) (w.adicCompletion D.host.E)}
    (hc : GlobalTheory.LFun.IsConjAt D.sp.cm.sig h c)
    (hS : cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = antiJ _ S.rank)
    (hT : cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = antiJ _ T.rank)
    (x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    hO S T (uPt hw h k aS aT x) (uPt hw h k aS aT y) =
      secW hw h (k * c k * Matrix.trace (antiJ (w.adicCompletion D.host.E) S.rank * cT c y * antiJ (w.adicCompletion D.host.E) T.rank * x)) := by
  have hG : (S.gram⁻¹.map (algebraMap D.host.E (w.adicCompletion D.host.E)) : Matrix (Fin S.rank) (Fin S.rank) _) *
      S.gram.map (algebraMap D.host.E (w.adicCompletion D.host.E)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S),
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [uPt, uPt, hO_map_secW hc, inv_eq_of_frame c hG aS hS, trace_frame c k aS aT _ _ _ hT]

theorem symplOH_uPt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), IsConjAt D.sp.cm.sig h c → Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = Formalism.UG.antiJ _ S.rank → Formalism.UG.cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = Formalism.UG.antiJ _ T.rank → ∀ x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), ψ (symplOH S T (uPt hw h k aS aT x) (uPt hw h k aS aT y)) = thW ψ hw h (k * c k) (2⁻¹ * GlobalTheory.Hk3.locH c 1 (GlobalTheory.SphTheta.antiG _ S.rank) (GlobalTheory.SphTheta.antiG _ T.rank) x y) := by
  intro D ψ v w hw h S T c k aS aT hc hS hT x y
  have h2 : (2 : w.adicCompletion D.host.E) ≠ 0 := by
    have : CharZero (w.adicCompletion D.host.E) := algebraRat.charZero _
    exact two_ne_zero
  have hx : (2⁻¹ : w.adicCompletion D.host.E) • x + (2⁻¹ : w.adicCompletion D.host.E) • x = x := by
    rw [← add_smul, ← two_mul, mul_inv_cancel₀ h2, one_smul]
  have hl : GlobalTheory.Hk3.locH c 1 (GlobalTheory.SphTheta.antiG _ S.rank) (GlobalTheory.SphTheta.antiG _ T.rank) x y =
      Matrix.trace (antiJ (w.adicCompletion D.host.E) S.rank * cT c y * antiJ (w.adicCompletion D.host.E) T.rank * x) := by
    rw [GlobalTheory.Hk3.locH, one_mul]
    rfl
  conv_lhs => rw [← hx, uPt_add, GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_self]
  rw [thW_apply, symplO, hO_uPt k hc hS hT, hl, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_assoc]

end GlobalTheory.InertFrameSympl
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kappa_splitHalfPoint_multiplies_by_character : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (L' W₀ : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n), IsSumFrame B.o B.ζ α α₀ → ∀ t : n → k, IsHalf (cA D p.e) ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t))) ∧ ∀ x : WO B.V₀ W₀, IsHalf p.e x → ψ (symplO B.V₀ W₀ x ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wRow p ζ' β t)))) = (χ (-(t ⬝ᵥ fun i => rd α₀ β x i (Sum.inr 0))) : ℂ) := by
  first | exact @GlobalTheory.KappaRowChar.kappa_wRow_char | exact GlobalTheory.KappaRowChar.kappa_wRow_char | (intros; apply GlobalTheory.KappaRowChar.kappa_wRow_char <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.neg_halfPoint_translates_lastFrameRow : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (S₀ A L W₀ : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (β : Frame p W₀ n) (γ : Frame p A n'') (γ₀ : Frame p S₀ (n'' ⊕ Fin 1)), IsSumFrame o ζ γ γ₀ → ∀ t : n → k, IsHalf p.e ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wRow p ζ β t)) ∧ ∀ i j, rd β γ₀ ((o.resT W₀).symm (0, -GlobalTheory.FinPl.LineAct.wRow p ζ β t)) i j = Sum.elim (fun _ => 0) (fun _ => -t j) i := by
  exact GlobalTheory.FinPl.LineAct.neg_wRow_half_rd
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.isSelfDualLatticeAtPlace_comap_unitarySupported : ∀ (D : D7) (S : HSp D) (v : Pl D) (g : GA D S), g ∈ grpAt S (· = v) → ∀ Λ : AddSubgroup (Fin S.rank → AE D), IsSDAt S v Λ → IsSDAt S v (Λ.comap (Matrix.mulVecLin (mt S g)).toAddMonoidHom) := by
  first | exact @GlobalTheory.IwaPlace.SdComap.isSDAt_comap | exact GlobalTheory.IwaPlace.SdComap.isSDAt_comap | (intros; apply GlobalTheory.IwaPlace.SdComap.isSDAt_comap <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.selfDualLatticeAtPlace_splits_hyperbolic_plus_core : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (N : AddSubgroup (Fin S.rank → AE D)) (α β : Fin ρ → AE D), IsSDAt S v N → (∀ i, α i ∈ idAt D (· = v)) → (∀ i, β i ∈ idAt D (· = v)) → (∀ i, α i * β i = ε) → (∀ i, colMul d.jX i (α i) ∈ N) → (∀ i, colMul d.jY i (cA D (β i)) ∈ N) → ∃ Λ₀ : AddSubgroup (Fin S₀.rank → AE D), IsSDAt S₀ v Λ₀ ∧ ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) → (z ∈ N ↔ (∀ i, (d.pX *ᵥ z) i * β i ∈ intAt D (· = v)) ∧ (∀ i, (d.pY *ᵥ z) i * cA D (α i) ∈ intAt D (· = v)) ∧ d.p0 *ᵥ z ∈ Λ₀) := by
  first | exact @GlobalTheory.IwaDecomp.selfDual_split | exact GlobalTheory.IwaDecomp.selfDual_split | (intros; apply GlobalTheory.IwaDecomp.selfDual_split <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.selfDualLattice_hyperbolic_line_ideals_at_place : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), IsSDAt S v (latV S L (· = v)) → MonoAt d L L₀ v → ∃ α β : Fin ρ → AE D, (∀ i, α i ∈ idAt D (· = v)) ∧ (∀ i, β i ∈ idAt D (· = v)) ∧ (∀ i, α i * β i = ε) ∧ (∀ i, ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ a * β i ∈ intAt D (· = v)) ∧ (∀ i, ∀ a ∈ idAt D (· = v), colMul d.jY i a ∈ latV S L (· = v) ↔ a * cA D (α i) ∈ intAt D (· = v)) := by
  first | exact @GlobalTheory.IwaIdeals.ideals_at_place | exact GlobalTheory.IwaIdeals.ideals_at_place | (intros; apply GlobalTheory.IwaIdeals.ideals_at_place <;> assumption)
end
