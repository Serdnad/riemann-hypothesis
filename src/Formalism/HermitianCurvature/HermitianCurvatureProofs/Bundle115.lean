module

public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle079
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle066
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle099
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle089
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle065
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle027
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle072
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QxChain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle069
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RttUpperRelationsFromDescent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle038
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle087
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle060
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointInChart
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle112
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle057
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockTwoDiagonalZeroSize
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostermanDensityOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixOneZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateCommuteRaisingConstant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FubiniHeadLastPart

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P

theorem jacquet_derivative_formula : Formalism.FourierDecayAlt.JF.JWords :=
  bessel_words_of_domain bessel_integral_domain

theorem jacquet_smooth_coordinates : Formalism.FourierDecayAlt.JF.JqSmooth :=
  bessel_smooth_of_parts jacquet_derivative_formula big_cell_domain

theorem casimir_under_jacquet_integral : Formalism.FourierDecayAlt.JF.CVUnderInt :=
  capelli_under_integral_of_parts jacquet_derivative_formula capelli_word_sum rewrite_rho_action

theorem right_transfer_upper_levels : Formalism.FourierDecayAlt.Q.RTTUpper :=
  rtt_upper_relations_from_descent chain_descent_relation resSurj_statement capelli_commutation operator_preserves_fusion_forms
    transfer_triples rtt_sandwich rtt_independence leading_term_alt transfer_linear_local

theorem right_transfer_all_levels : Formalism.FourierDecayAlt.Q.RTTLevel :=
  rtt_level_from_upper right_transfer_upper_levels level_transfer level_group_image flag_frame_transfer
    transfer_linear_local

namespace JacquetIntegral

theorem detCore : Formalism.FourierDecayAlt.Q.DetAt fun P => Fin.last P.r :=
  determinant_capelli_from_descent right_transfer_all_levels quantum_determinant_from_rtt determinant_hat right_type_action
    left_type_action operator_preserves_fusion_forms transfer_linear_local

end JacquetIntegral

theorem actual_operators_exist : Formalism.FourierDecayAlt.Q.ActualOpsExist :=
  actual_operators_from_parts operator_preserves_fusion_forms transfer_linear_local transfer_joint_smooth radial_operators

theorem actual_adjointness : Formalism.FourierDecayAlt.Q.ActualAdjoint :=
  actual_adjointness_from_hermitian hermitian_haar_invariance

theorem actual_start : Formalism.FourierDecayAlt.Q.ActualStart :=
  actual_start_from_level_starts right_transfer_all_levels JacquetIntegral.detCore transfer_linear_local

namespace JacquetIntegral

theorem normalFormActual_of_fromModule (h : Formalism.FourierDecayAlt.Q.NormalFormFromModule) : Formalism.FourierDecayAlt.Q.NormalFormActual :=
  h actual_start zeta_commutes leading_term_alt spectral_two_by_two actual_operators_exist

theorem levelStartActual_of_normalForm (h : Formalism.FourierDecayAlt.Q.NormalFormActual) : Formalism.FourierDecayAlt.Q.LevelStartActual :=
  level_start_from_normal_form h actual_start model_is_normal_form interlace_sign_two

theorem levelStartActual_of_fromModule (h : Formalism.FourierDecayAlt.Q.NormalFormFromModule) : Formalism.FourierDecayAlt.Q.LevelStartActual :=
  levelStartActual_of_normalForm (normalFormActual_of_fromModule h)

end JacquetIntegral

end Formalism.FourierDecayAlt.P
end

section

open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def V1 (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] : Submodule ℂ (ℂ → E) where
  carrier := {f | ContDiffOn ℝ ∞ f {τ | τ ≠ 0}}
  zero_mem' := contDiffOn_const
  add_mem' := fun hf hg => hf.add hg
  smul_mem' := fun c f hf => by
    change ContDiffOn ℝ ∞ (fun τ => c • f τ) _
    exact hf.const_smul c

theorem isOpen_ne_zero_complex : IsOpen {τ : ℂ | τ ≠ 0} := isOpen_ne

theorem differentiableAt_of_punctured_smooth {f : ℂ → E} (hf : f ∈ V1 E) {τ : ℂ} (hτ : τ ≠ 0) : DifferentiableAt ℝ f τ :=
  (hf.differentiableOn (by simp)).differentiableAt (isOpen_ne_zero_complex.mem_nhds hτ)

theorem contDiffOn_fderiv_punctured {f : ℂ → E} (hf : f ∈ V1 E) (v : ℂ) : ContDiffOn ℝ ∞ (fun τ => fderiv ℝ f τ v) {τ | τ ≠ 0} :=
  (hf.fderiv_of_isOpen isOpen_ne_zero_complex (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_wirtinger_dz {f : ℂ → E} (hf : f ∈ V1 E) : ContDiffOn ℝ ∞ (PBP.dz f) {τ | τ ≠ 0} := by
  unfold PBP.dz
  exact ((contDiffOn_fderiv_punctured hf 1).sub ((contDiffOn_fderiv_punctured hf Complex.I).const_smul Complex.I)).const_smul _

theorem contDiffOn_wirtinger_dzbar {f : ℂ → E} (hf : f ∈ V1 E) : ContDiffOn ℝ ∞ (PBP.dzb f) {τ | τ ≠ 0} := by
  unfold PBP.dzb
  exact ((contDiffOn_fderiv_punctured hf 1).add ((contDiffOn_fderiv_punctured hf Complex.I).const_smul Complex.I)).const_smul _

theorem dz_add {f g : ℂ → E} (hf : f ∈ V1 E) (hg : g ∈ V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dz (f + g) τ = PBP.dz f τ + PBP.dz g τ := by
  unfold PBP.dz
  rw [fderiv_add (differentiableAt_of_punctured_smooth hf hτ) (differentiableAt_of_punctured_smooth hg hτ)]
  simp only [ContinuousLinearMap.add_apply, smul_add, smul_sub]
  abel

theorem dzb_add {f g : ℂ → E} (hf : f ∈ V1 E) (hg : g ∈ V1 E) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dzb (f + g) τ = PBP.dzb f τ + PBP.dzb g τ := by
  unfold PBP.dzb
  rw [fderiv_add (differentiableAt_of_punctured_smooth hf hτ) (differentiableAt_of_punctured_smooth hg hτ)]
  simp only [ContinuousLinearMap.add_apply, smul_add]
  abel

theorem dz_smul {f : ℂ → E} (hf : f ∈ V1 E) (c : ℂ) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dz (c • f) τ = c • PBP.dz f τ := by
  unfold PBP.dz
  rw [fderiv_const_smul (differentiableAt_of_punctured_smooth hf hτ)]
  simp only [ContinuousLinearMap.smul_apply, smul_sub, smul_comm c Complex.I, smul_comm c (1 / 2 : ℂ)]

theorem dzb_smul {f : ℂ → E} (hf : f ∈ V1 E) (c : ℂ) {τ : ℂ} (hτ : τ ≠ 0) :
    PBP.dzb (c • f) τ = c • PBP.dzb f τ := by
  unfold PBP.dzb
  rw [fderiv_const_smul (differentiableAt_of_punctured_smooth hf hτ)]
  simp only [ContinuousLinearMap.smul_apply, smul_add, smul_comm c Complex.I, smul_comm c (1 / 2 : ℂ)]

def off0 (f : ℂ → E) : ℂ → E := fun τ => if τ = 0 then 0 else f τ

theorem off_zero_mem_punctured_smooth {f : ℂ → E} (hf : ContDiffOn ℝ ∞ f {τ | τ ≠ 0}) : off0 f ∈ V1 E :=
  hf.congr fun τ hτ => by simp [off0, show τ ≠ 0 from hτ]

theorem cd_id : ContDiffOn ℝ ∞ (fun τ : ℂ => τ) {τ | τ ≠ 0} := contDiffOn_id
theorem cd_conj : ContDiffOn ℝ ∞ (fun τ : ℂ => conj τ) {τ | τ ≠ 0} := Complex.conjCLE.contDiff.contDiffOn
theorem cd_inv : ContDiffOn ℝ ∞ (fun τ : ℂ => τ⁻¹) {τ | τ ≠ 0} := by
  intro τ hτ
  exact (contDiffAt_inv ℂ (show τ ≠ 0 from hτ)).restrict_scalars ℝ |>.contDiffWithinAt
theorem cd_conjinv : ContDiffOn ℝ ∞ (fun τ : ℂ => (conj τ)⁻¹) {τ | τ ≠ 0} := by
  intro τ hτ
  have h1 : ContDiffAt ℝ ∞ (fun τ : ℂ => conj τ) τ := Complex.conjCLE.contDiff.contDiffAt
  have h2 : conj τ ≠ 0 := by simpa using (show τ ≠ 0 from hτ)
  exact (((contDiffAt_inv ℂ h2).restrict_scalars ℝ).comp τ h1).contDiffWithinAt

def opP (κ : ℂ) : Module.End ℂ (V1 E) where
  toFun f := ⟨off0 fun τ => τ • PBP.dz f.1 τ + κ • f.1 τ,
    off_zero_mem_punctured_smooth ((cd_id.smul (contDiffOn_wirtinger_dz f.2)).add (f.2.const_smul κ))⟩
  map_add' f g := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, Submodule.coe_add, Pi.add_apply]
      rw [dz_add f.2 g.2 hτ]
      simp only [smul_add]
      abel
  map_smul' c f := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]
      rw [dz_smul f.2 c hτ]
      simp only [smul_add, smul_comm τ c, smul_comm κ c]

def opPb (κ : ℂ) : Module.End ℂ (V1 E) where
  toFun f := ⟨off0 fun τ => conj τ • PBP.dzb f.1 τ + κ • f.1 τ,
    off_zero_mem_punctured_smooth ((cd_conj.smul (contDiffOn_wirtinger_dzbar f.2)).add (f.2.const_smul κ))⟩
  map_add' f g := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, Submodule.coe_add, Pi.add_apply]
      rw [dzb_add f.2 g.2 hτ]
      simp only [smul_add]
      abel
  map_smul' c f := by
    ext τ
    by_cases hτ : τ = 0
    · simp [off0, hτ]
    · simp only [off0, hτ, if_false, SetLike.val_smul, Pi.smul_apply, RingHom.id_apply]
      rw [dzb_smul f.2 c hτ]
      simp only [smul_add, smul_comm (conj τ) c, smul_comm κ c]

def opM (m : ℂ → ℂ) (hm : ContDiffOn ℝ ∞ m {τ | τ ≠ 0}) : Module.End ℂ (V1 E) where
  toFun f := ⟨fun τ => m τ • f.1 τ, hm.smul f.2⟩
  map_add' f g := by ext τ; simp [smul_add]
  map_smul' c f := by ext τ; simp [smul_comm (m τ) c]

def site1 (κ : ℂ) : Wd.Site (Q.Pr (V1 E)) :=
  ⟨Q.mkP (opP κ) (-(opPb κ)), Q.mkP (opM (fun τ => τ) cd_id) (opM (fun τ => conj τ) cd_conj),
    Q.mkP (opM (fun τ => τ⁻¹) cd_inv) (opM (fun τ => (conj τ)⁻¹) cd_conjinv)⟩

def act1 {S : Type} [Fintype S] [DecidableEq S] (M : Wd.SlopeTestRemainingChoices S (Q.Pr (V1 E))) (x : Wd.Ix S → V1 E) : Wd.Ix S → V1 E :=
  fun a => ∑ b, (M a b).1 (x b)

def oneBT {S : Type} [Fintype S] [DecidableEq S] (κ : ℂ) (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → V1 E) :
    Wd.Ix S → V1 E :=
  act1 (Wd.bT (site1 κ) w) x

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section frame

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem gcl_hsVec_add (A A' : Wq →L[ℂ] Wp) : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
  ext i
  simp [B.hsVec]

theorem gcl_hsVec_sum {ι : Type} (s : Finset ι) (A : ι → (Wq →L[ℂ] Wp)) :
    B.hsVec (∑ i ∈ s, A i) = ∑ i ∈ s, B.hsVec (A i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · ext i
    simp [B.hsVec]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, gcl_hsVec_add, ih]

theorem gcl_hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  ext i
  simp [B.hsVec]

theorem gcl_wRc_smooth (P : M.Par) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => ((wR P.k P.TT ζ : ℝ) : ℂ)) (Ann P) := by
  have hre : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => ζ.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => ζ.im) := Complex.imCLM.contDiff
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => Complex.normSq ζ - P.TT) := by
    simp_rw [Complex.normSq_apply]
    exact ((hre.mul hre).add (him.mul him)).sub contDiff_const
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => wR P.k P.TT ζ) (Ann P) := by
    simp only [wR]
    exact ((h1.pow _).contDiffOn).sqrt (fun ζ hζ => (pow_pos (sub_pos.2 hζ) _).ne')
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h2

theorem gcl_wR_ne (P : M.Par) {ζ : ℂ} (hζ : ζ ∈ Ann P) : ((wR P.k P.TT ζ : ℝ) : ℂ) ≠ 0 := by
  have h : 0 < Complex.normSq ζ - P.TT := sub_pos.2 hζ
  have hw : 0 < wR P.k P.TT ζ := by
    unfold wR
    exact Real.sqrt_pos.2 (pow_pos h _)
  exact Complex.ofReal_ne_zero.2 hw.ne'

theorem gcl_dZ_smooth {g : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s) (hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g s) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (NF.dZ g) s ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (NF.dZb g) s := by
  have hd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ g y) s :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hs).1 hg).2
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ g y 1) s :=
    hd.clm_apply contDiffOn_const
  have hI : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => fderiv ℝ g y Complex.I) s :=
    hd.clm_apply contDiffOn_const
  refine ⟨?_, ?_⟩
  · exact contDiffOn_const.mul (h1.sub (contDiffOn_const.mul hI))
  · exact contDiffOn_const.mul (h1.add (contDiffOn_const.mul hI))

theorem gcl_wirt_slice {r : ℕ} (F : MA.E r → ℂ) (x : MA.E r) (hF : DifferentiableAt ℝ F x) :
    MA.wirt M.vz F x = NF.dZ (fun ζ => F (x.1, ζ)) x.2 ∧
      MA.wirt M.vzb F x = NF.dZb (fun ζ => F (x.1, ζ)) x.2 := by
  have hmap : HasFDerivAt (fun ζ : ℂ => (x.1, ζ))
      ((0 : ℂ →L[ℝ] (Fin r → ℂ)).prod (ContinuousLinearMap.id ℝ ℂ)) x.2 :=
    (hasFDerivAt_const x.1 x.2).prodMk (hasFDerivAt_id x.2)
  have hF' : HasFDerivAt F (fderiv ℝ F x) (x.1, x.2) := by
    simpa using hF.hasFDerivAt
  have hcomp : HasFDerivAt (fun ζ => F (x.1, ζ))
      ((fderiv ℝ F x).comp ((0 : ℂ →L[ℝ] (Fin r → ℂ)).prod (ContinuousLinearMap.id ℝ ℂ))) x.2 :=
    hF'.comp x.2 hmap
  have hd : ∀ v : ℂ, fderiv ℝ (fun ζ => F (x.1, ζ)) x.2 v = fderiv ℝ F x (0, v) := by
    intro v
    rw [hcomp.fderiv]
    simp
  have e1 : MA.dirE (r := r) M.vz = ((0 : Fin r → ℂ), (1 : ℂ)) := by
    simp [MA.dirE, M.vz]
  have e2 : MA.dirE (r := r) M.vzb = ((0 : Fin r → ℂ), (1 : ℂ)) := by
    simp [MA.dirE, M.vzb]
  refine ⟨?_, ?_⟩
  · simp only [MA.wirt, NF.dZ, e1, hd]
    simp [M.vz] <;> ring
  · simp only [MA.wirt, NF.dZb, e2, hd]
    simp [M.vzb] <;> ring

theorem gcl_radR_sum {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type} (s : Finset ι) (F : ι → Q.Fn k r E)
    (x : (Fin r → ℂ) × ℂ) :
    NF.radR k r z z' μsec (∑ i ∈ s, F i) x = ∑ i ∈ s, NF.radR k r z z' μsec (F i) x := by
  by_cases hx : x ∈ NF.QR k r z z'
  · simp [NF.radR, Set.indicator, hx, Finset.sum_apply]
  · simp [NF.radR, Set.indicator, hx]

theorem gcl_trR_val (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      ((wR P.k P.TT q.1.2 : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1)) := by
  have hmem := radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ
  have hq : q.1 ∈ NF.QR P.k P.r Bs.z Bs.z' := by
    obtain ⟨h1, h2⟩ := q.2
    refine ⟨h1, ?_⟩
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
    exact h2
  have h1 : ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) =
      rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
    simp only [trR, MA.toSm, dif_pos hmem]
  rw [h1]
  simp [rawR, NF.radR, Set.indicator_of_mem hq]

end frame

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem bounded_operators_square_integrable : BoundedOperatorsSquareIntegrable := by
  intro P L hTT hL b hb u hu π
  have hLaw : (MA.DQ P).Laws P.TT := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT.le
  have hPW : ∃ C, Formalism.FourierDecayAlt.P.MAx3.I4.PW b C := by
    induction hb using Submonoid.closure_induction with
    | mem x hx => exact Formalism.FourierDecayAlt.P.MAx3.I4.PW_gen hTT hL hLaw hx
    | one => exact ⟨1, Formalism.FourierDecayAlt.P.MAx3.I4.PW_one⟩
    | mul x y _ _ h1 h2 =>
      obtain ⟨C1, h1⟩ := h1
      obtain ⟨C2, h2⟩ := h2
      exact ⟨_, Formalism.FourierDecayAlt.P.MAx3.I4.PW_mul h1 h2⟩
  obtain ⟨C, hC0, Mx, hMb, hMe⟩ := hPW
  have hmeas := jd_evQ_meas P (MA.actA P b u π)
  have hL2u : ∀ π', MemLp (MA.evQ P (u π')) 2 (MA.mu0 P.r P.TT) := fun π' =>
    (memLp_two_iff_integrable_sq_norm (jd_evQ_meas P (u π'))).2 (hu π')
  have hs : MemLp (fun q => ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖) 2 (MA.mu0 P.r P.TT) :=
    memLp_finsetSum _ fun π' _ => (hL2u π').norm
  have hg : MemLp (fun q => C * ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖) 2 (MA.mu0 P.r P.TT) := hs.const_mul C
  refine (memLp_two_iff_integrable_sq_norm hmeas).1 (hg.of_le hmeas (Filter.Eventually.of_forall fun q => ?_))
  rw [hMe u q π]
  calc ‖∑ π', Mx q π π' * MA.evQ P (u π') q‖ ≤ ∑ π', ‖Mx q π π' * MA.evQ P (u π') q‖ := norm_sum_le _ _
    _ ≤ ∑ π', C * ‖MA.evQ P (u π') q‖ := Finset.sum_le_sum fun π' _ => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hMb q π π') (norm_nonneg _)
    _ = C * ∑ π', ‖MA.evQ P (u π') q‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖C * ∑ π' ∈ Finset.univ, ‖MA.evQ P (u π') q‖‖ := le_abs_self _

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem hat_bounded_decay_holds : JDHatBdd := by
  intro P L hTT hL X hX b hb
  have hLaw : (MA.DQ P).Laws P.TT := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT
  have hS := Formalism.FourierDecayAlt.P.MAx3.H.hyp_model hL hLaw
  have hV := Formalism.FourierDecayAlt.P.MAx3.K.hypV_model hL hLaw
  have gen : ∀ b' ∈ Submonoid.closure (MA.bddSet P L), ∀ X' ∈ MA.hatSet P L,
      b' * X' ∈ Submodule.span ℂ (bddHat P L) := fun b' hb' X' hX' =>
    Submodule.subset_span ⟨b', hb', X', hX', rfl⟩
  have mA : ∀ y, L.Ahat y ∈ MA.hatSet P L := fun y => Or.inl (Or.inl (Or.inl ⟨y, rfl⟩))
  have mR : ∀ y, L.R0 y ∈ MA.hatSet P L := fun y => Or.inl (Or.inl (Or.inr ⟨y, rfl⟩))
  have mAv : ∀ y, L.Ahatv y ∈ MA.hatSet P L := fun y => Or.inl (Or.inr ⟨y, rfl⟩)
  have mRv : ∀ y, L.R0v y ∈ MA.hatSet P L := fun y => Or.inr ⟨y, rfl⟩
  have sumA : ∀ ts : List (ℂ × MA.A P (MA.DQ P) × ℂ), (∀ x ∈ ts, x.2.1 ∈ Submonoid.closure (MA.bddSet P L)) →
      (ts.map fun x => x.1 • (x.2.1 * L.Ahat x.2.2)).sum ∈ Submodule.span ℂ (bddHat P L) := by
    intro ts hts
    refine list_sum_mem fun u hu => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
    exact Submodule.smul_mem _ _ (gen _ (hts x hx) _ (mA _))
  have sumAv : ∀ ts : List (ℂ × MA.A P (MA.DQ P) × ℂ), (∀ x ∈ ts, x.2.1 ∈ Submonoid.closure (MA.bddSet P L)) →
      (ts.map fun x => x.1 • (x.2.1 * L.Ahatv x.2.2)).sum ∈ Submodule.span ℂ (bddHat P L) := by
    intro ts hts
    refine list_sum_mem fun u hu => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
    exact Submodule.smul_mem _ _ (gen _ (hts x hx) _ (mAv _))
  rcases hX with (((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩)
  · obtain ⟨t, ht⟩ := hS.ahat b hb
    rw [ht y]; exact gen _ hb _ (mA _)
  · obtain ⟨t, ts, hts, he⟩ := hS.r0 b hb y
    rw [he]; exact Submodule.add_mem _ (gen _ hb _ (mR _)) (sumA ts hts)
  · obtain ⟨t, ht⟩ := hV.ahatv b hb
    rw [ht y]; exact gen _ hb _ (mAv _)
  · obtain ⟨t, ts, hts, he⟩ := hV.r0v b hb y
    rw [he]; exact Submodule.add_mem _ (gen _ hb _ (mRv _)) (sumAv ts hts)

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

namespace Formalism.FourierDecayAlt.P

theorem kloosterman_density : Formalism.FourierDecayAlt.KB.KloostDens :=
  PBJ.Asm.kloosterman_density_of_parts PBJ.fubini_head_last_part PBJ.freeze_last_entry PBJ.long_orbital_integral_multiple PBJ.block_orbital_integral_multiple

end Formalism.FourierDecayAlt.P
end
