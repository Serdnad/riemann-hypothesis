module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle293
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle284
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle262
public import Formalism.HermitianLattices.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle300
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.AutomorphicFormsFiniteDimensional
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.PeriodIntegrals.Bundle024
public import Formalism.PeriodIntegrals.Bundle020
public import Formalism.PeriodIntegrals.Bundle013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle302
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle003
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CyclicDiscriminantLatticesFormOneGenus
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle301
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle303
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevValueAtOneFixedCompactDiagSignUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.FatouI

theorem lintegral_le_of_liminf {X : Type*} [MeasurableSpace X] (ν : Measure X) (F : X → ENNReal)
    (g : ℕ → X → ENNReal) (hg : ∀ j, Measurable (g j))
    (hF : ∀ᵐ γ ∂ν, F γ ≤ Filter.liminf (fun j => g j γ) Filter.atTop) (b : ℕ → ℝ) (L : ℝ)
    (hb : ∀ j, ∫⁻ γ, g j γ ∂ν = ENNReal.ofReal (b j))
    (hL : Filter.Tendsto b Filter.atTop (nhds L)) : ∫⁻ γ, F γ ∂ν ≤ ENNReal.ofReal L := by
  refine (lintegral_mono_ae hF).trans ((lintegral_liminf_le hg).trans ?_)
  simp_rw [hb]
  exact (ENNReal.tendsto_ofReal hL).liminf_eq.le

variable {k r : ℕ}

theorem measurable_besselTwoSidedAction_joint :
    Measurable fun q : Mt k r × (Mt k r × Mt k r) => act2 (Matrix.of q.1) q.2 := by
  let m : Mt k r × Mt k r → Mt k r := fun q => lmulM (Matrix.of q.1) q.2
  have hmul : Continuous m :=
    Continuous.matrix_mul (X := Mt k r × Mt k r) continuous_fst continuous_snd
  have hm : Measurable m := hmul.measurable
  have h1 : Measurable fun q : Mt k r × (Mt k r × Mt k r) => m (q.2.1, q.1) :=
    hm.comp (measurable_snd.fst.prodMk measurable_fst)
  have h2 : Measurable fun q : Mt k r × (Mt k r × Mt k r) => invM q.2.2 :=
    measurable_invM.comp measurable_snd.snd
  have h3 : Measurable fun q : Mt k r × (Mt k r × Mt k r) => m (m (q.2.1, q.1), invM q.2.2) :=
    hm.comp (h1.prodMk h2)
  exact h3

theorem hsNormSq_eq_sum {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem DD_stable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (hσ : IsURepOn (GG k r) σ) (hG : IsClosedSub k r (GG k r)) :
    ∀ g ∈ GG k r, ∀ v ∈ (DD σ w : Set H), σ g v ∈ (DD σ w : Set H) := by
  intro g hg v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h, hh, rfl⟩ := hv
    have := mem_DD σ w (hG.2.2.2.1 g hg h hh)
    rw [hσ.1.2 g hg h hh] at this
    exact this
  | zero => simp
  | add u v _ _ hu hv => rw [map_add (f := _)]; exact (DD σ w).add_mem hu hv
  | smul a v _ hv => rw [map_smul]; exact (DD σ w).smul_mem a hv

theorem integrable_coef {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (hσ : IsURepOn (GG k r) σ) {S : Set (Mat k r)} (hS : IsClosedSub k r S)
    {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ) {a C : ℝ} (hfin : normInt μ a < ⊤) (u v : H)
    (hC : ∀ g ∈ GG k r, ‖coef σ u v g‖ ≤ C * opn g ^ (-a)) :
    Integrable (fun p : Mt k r => coef σ u v (Matrix.of p)) μ := by
  have hae : ∀ᵐ p ∂μ, (Matrix.of p : Mat k r) ∈ S := hμ.2.2.1
  have hSm : MeasurableSet {p : Mt k r | (Matrix.of p : Mat k r) ∈ S} :=
    IsClosed.measurableSet (α := Mt k r) hS.2.1
  refine ⟨?_, ?_⟩
  · have hc : ContinuousOn (fun p : Mt k r => coef σ u v (Matrix.of p))
        {p : Mt k r | (Matrix.of p : Mat k r) ∈ S} :=
      ContinuousOn.inner (𝕜 := ℂ) continuousOn_const ((hσ.2.2 u).mono hS.1)
    have := hc.aestronglyMeasurable (μ := μ) hSm
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {p : Mt k r | (Matrix.of p : Mat k r) ∈ S}) hae] at this
  · refine lt_of_le_of_lt (b := ∫⁻ x, ENNReal.ofReal C * ENNReal.ofReal (opn (Matrix.of x) ^ (-a)) ∂μ)
      (lintegral_mono_ae ?_) ?_
    · filter_upwards [hae] with p hp
      rw [← ENNReal.ofReal_mul' (Real.rpow_nonneg (opn_nonneg _) _), ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hC _ (hS.1 hp))
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem dis_of_continuousOn {Ω S S' : Set (Mat k r)} {μG μS μS' ν : Measure (Mt k r)}
    (hG : IsClosedSub k r (GG k r)) (hS : IsClosedSub k r S) (hS' : IsClosedSub k r S')
    (hμG : IsHaarOn (GG k r) μG) (hμ : IsHaarOn S μS) (hμ' : IsHaarOn S' μS') (hΩ : Ω ⊆ GG k r)
    (hν : IsDis Ω μG μS μS' ν) (f : Mat k r → ℝ) (hf0 : ∀ g, 0 ≤ f g) (hf : ContinuousOn f (GG k r))
    (hfi : Integrable (fun g : Mt k r => f (Matrix.of g)) μG) :
    ∃ g : Mt k r → ENNReal, Measurable g ∧
      (∀ γ : Mt k r, Matrix.of γ ∈ Ω →
        g γ = ∫⁻ p, ENNReal.ofReal (f (Matrix.of (act2 (Matrix.of γ) p))) ∂(μS.prod μS')) ∧
      ∫⁻ γ, g γ ∂ν = ENNReal.ofReal (∫ g, f (Matrix.of g) ∂μG) := by
  classical
  haveI := hμ.1
  haveI := hμ'.1
  have hGm : MeasurableSet {p : Mt k r | (Matrix.of p : Mat k r) ∈ GG k r} :=
    IsClosed.measurableSet (α := Mt k r) hG.2.1
  let f0 : Mt k r → ℝ := {p : Mt k r | (Matrix.of p : Mat k r) ∈ GG k r}.piecewise
    (fun p => f (Matrix.of p)) (fun _ => 0)
  have hf0m : Measurable f0 :=
    ContinuousOn.measurable_piecewise (f := fun p : Mt k r => f (Matrix.of p)) hf continuousOn_const hGm
  have hf0e : ∀ p : Mt k r, Matrix.of p ∈ GG k r → f0 p = f (Matrix.of p) := fun p hp =>
    Set.piecewise_eq_of_mem _ _ _ hp
  have hF : Measurable fun p => ENNReal.ofReal (f0 p) := hf0m.ennreal_ofReal
  refine ⟨fun γ => ∫⁻ p, ENNReal.ofReal (f0 (act2 (Matrix.of γ) p)) ∂(μS.prod μS'), ?_, ?_, ?_⟩
  · exact (hF.comp measurable_besselTwoSidedAction_joint).lintegral_prod_right'
  · intro γ hγ
    have h1 : ∀ᵐ p ∂μS, (Matrix.of p : Mat k r) ∈ S := hμ.2.2.1
    have h2 : ∀ᵐ p ∂μS', (Matrix.of p : Mat k r) ∈ S' := hμ'.2.2.1
    have h1' := Measure.quasiMeasurePreserving_fst (μ := μS) (ν := μS') |>.ae h1
    have h2' := Measure.quasiMeasurePreserving_snd (μ := μS) (ν := μS') |>.ae h2
    refine lintegral_congr_ae ?_
    filter_upwards [h1', h2'] with p hp hp'
    rw [hf0e]
    exact hG.2.2.2.1 _ (hG.2.2.2.1 _ (hS.1 hp) _ (hΩ hγ)) _ (hG.2.2.2.2 _ (hS'.1 hp'))
  · rw [← hν.2.2 _ hF, ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall fun g => hf0 _)]
    have h1 : ∀ᵐ p ∂μG, (Matrix.of p : Mat k r) ∈ GG k r := hμG.2.2.1
    refine lintegral_congr_ae ?_
    filter_upwards [h1] with p hp
    rw [hf0e p hp]

end GlobalTheory.SgInf.FatouI


open GlobalTheory.SgInf.FatouI in
theorem GlobalTheory.SgInf.lintegral_hsNormSq_Iint_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ ν : Measure (Mt k r), IsDis (Greg k r z z') μG μS μS' ν → ∀ x ∈ DD σ w, ∀ y ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∫⁻ γ, ENNReal.ofReal (hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ x y ξ ξ' (Matrix.of γ))) ∂ν ≤ ENNReal.ofReal (d⁻¹ * (⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ).re * (⟪ξ', be (psiGen k r z' c') π' μS' σ x x ξ'⟫_ℂ).re) := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hStd hSd hSd' ν hν x hx y hy ξ ξ'
  obtain ⟨hG, -, -, hS, -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSd.1 hSd.2.1
  obtain ⟨-, -, -, hS', -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z' hSd'.1 hSd'.2.1
  obtain ⟨Om, hOm⟩ := GlobalTheory.T.exists_isFolnerSequenceBessel k r z μS hSd.1 hSd.2.1 hSd.2.2.2.1
  obtain ⟨Om', hOm'⟩ := GlobalTheory.T.exists_isFolnerSequenceBessel k r z' μS' hSd'.1 hSd'.2.1 hSd'.2.2.2.1
  have hdec := hStd.2.2.2.2.2.2.2.1
  have ha : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a := by
    have h1 : (2 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
      have := hStd.1
      exact_mod_cast (by omega : 2 ≤ 2 * r + k + 1)
    have h2 : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < ((2 * r + k + 1 : ℕ) : ℝ) ^ 5 :=
      pow_lt_pow_right₀ (by linarith) (by norm_num)
    have := hStd.2.2.2.2.2.2.1
    linarith
  have hiy : Integrable (fun p : Mt k r => coef σ y y (Matrix.of p)) μS := by
    obtain ⟨C, hC⟩ := hdec y hy y hy
    exact integrable_coef σ hStd.2.1 hS hSd.2.2.2.1 (GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r _ μS a hS hSd.2.2.2.1 ha) y y hC
  have hix : Integrable (fun p : Mt k r => coef σ x x (Matrix.of p)) μS' := by
    obtain ⟨C, hC⟩ := hdec x hx x hx
    exact integrable_coef σ hStd.2.1 hS' hSd'.2.2.2.1 (GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r _ μS' a hS' hSd'.2.2.2.1 ha) x x hC
  have h62 := fun j => GlobalTheory.T.bessel_functional_two_sided k r σ w a μG d z c π μS z' c' π' μS' hStd hSd hSd' x y ξ ξ' (Om j) (Om' j)
    (hOm.1 j).1 (hOm'.1 j).1 (hOm.1 j).2.2.2.2 (hOm'.1 j).2.2.2.2 hiy hix
  have h63 := GlobalTheory.T.besselFolner_overlap_average_tendsto_form k r σ w a μG d z c π μS hStd hSd Om hOm y hy ξ
  have h63' := GlobalTheory.T.besselFolner_overlap_average_tendsto_form k r σ w a μG d z' c' π' μS' hStd hSd' Om' hOm' x hx ξ'
  have h64 := GlobalTheory.T.hsNormSq_Iint_le_liminf_alt k r σ w a μG d z c π μS z' c' π' μS' hStd hSd hSd' Om Om' hOm hOm' x hx y hy ξ ξ'
  have hadj := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSd (DD σ w) (DD_stable σ w hStd.2.1 hG) hdec
    y hy y hy).2.2.1
  have him : (⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ).im = 0 := by
    rw [← Complex.conj_eq_iff_im, inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, hadj]
  have hcont : Continuous (hsNormSq : (Wq →L[ℂ] Wp) → ℝ) := by
    have : (hsNormSq : (Wq →L[ℂ] Wp) → ℝ) = fun A => ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 :=
      funext hsNormSq_eq_sum
    rw [this]
    fun_prop
  have hnn : ∀ A : Wq →L[ℂ] Wp, 0 ≤ hsNormSq A := fun A => by
    rw [hsNormSq_eq_sum]; positivity
  have hdis := fun j => dis_of_continuousOn hG hS hS' hStd.2.2.2.2.1 hSd.2.2.2.1 hSd'.2.2.2.1
    (Greg_subset z z') hν (fun g => hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π'
      (μS.restrict (Om j)) (μS'.restrict (Om' j)) σ x y ξ ξ' g)) (fun g => hnn _)
      (hcont.comp_continuousOn (h62 j).1) (h62 j).2.1
  choose g hgm hge hgi using hdis
  have hpos : ∀ j, 0 < (μS (Om j)).toReal := fun j =>
    ENNReal.toReal_pos (hOm.1 j).2.2.2.1.ne' (hOm.1 j).2.2.2.2.ne
  have hpos' : ∀ j, 0 < (μS' (Om' j)).toReal := fun j =>
    ENNReal.toReal_pos (hOm'.1 j).2.2.2.1.ne' (hOm'.1 j).2.2.2.2.ne
  refine lintegral_le_of_liminf ν _ (fun j γ => g j γ / (μS (Om j) * μS' (Om' j)))
    (fun j => (hgm j).div_const _) ?_
    (fun j => (∫ g, hsNormSq (Iint (psiGen k r z c) (psiGen k r z' c') π π'
      (μS.restrict (Om j)) (μS'.restrict (Om' j)) σ x y ξ ξ' (Matrix.of g)) ∂μG) /
        ((μS (Om j)).toReal * (μS' (Om' j)).toReal)) _ ?_ ?_
  · have h1 : ∀ᵐ γ ∂ν, (Matrix.of γ : Mat k r) ∈ Greg k r z z' := hν.2.1
    filter_upwards [h1] with γ hγ
    simp_rw [fun j => hge j γ hγ]
    exact h64 _ hγ
  · intro j
    simp_rw [div_eq_mul_inv (g j _)]
    rw [lintegral_mul_const _ (hgm j), hgi j, ENNReal.ofReal_div_of_pos (mul_pos (hpos j) (hpos' j)),
      ENNReal.ofReal_mul (hpos j).le, ENNReal.ofReal_toReal (hOm.1 j).2.2.2.2.ne,
      ENNReal.ofReal_toReal (hOm'.1 j).2.2.2.2.ne, div_eq_mul_inv]
  · have hT := (Complex.continuous_re.tendsto _).comp ((h63.const_mul ((d : ℂ)⁻¹)).mul h63')
    convert hT using 2 with j
    · have e := (h62 j).2.2
      rw [Function.comp_apply, ← mul_div_assoc (d : ℂ)⁻¹, div_mul_div_comm, ← e]
      norm_cast
    · rw [← Complex.ofReal_inv, mul_assoc (_ : ℂ), Complex.re_ofReal_mul, Complex.mul_re, him]
      ring
end
end

section

noncomputable section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G

namespace GlobalTheory.BinaryRep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gram_diag_pos {r : ℕ} (τ : E →+* ℂ) (d : Fin r → E)
    (hd : ∀ i, (τ (d i)).im = 0 ∧ 0 < (τ (d i)).re) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      FD.gram τ (Matrix.diagonal d) Q = Matrix.diagonal fun a : Fin r => ((FD.sgn r (a : ℕ) : ℝ) : ℂ) := by
  classical
  set q : Fin r → ℝ := fun i => (Real.sqrt (τ (d i)).re)⁻¹ with hq
  have hq2 : ∀ i, (q i : ℂ) * τ (d i) * (q i : ℂ) = 1 := by
    intro i
    have h1 : τ (d i) = ((τ (d i)).re : ℂ) := Complex.ext rfl (by simp [(hd i).1])
    have h2 : q i * q i * (τ (d i)).re = 1 := by
      rw [hq]
      simp only
      rw [← mul_inv, Real.mul_self_sqrt (hd i).2.le, inv_mul_cancel₀ (hd i).2.ne']
    rw [h1]
    exact_mod_cast (by linarith [h2] : q i * (τ (d i)).re * q i = 1)
  refine ⟨Matrix.diagonal fun i => (q i : ℂ), ?_, ?_⟩
  · rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    have : (q i : ℂ) ≠ 0 := fun h => by simpa [h] using hq2 i
    exact this
  · ext a b
    simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      have hs : FD.sgn r (a : ℕ) = 1 := by simp [FD.sgn, a.isLt]
      simp [hs, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Complex.conj_ofReal]
      rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp only [if_true, Complex.conj_ofReal]
      linear_combination hq2 a
    · simp [hab, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : a = x
      · subst hx
        simp [hab]
      · simp [hx]

end GlobalTheory.BinaryRep

namespace GlobalTheory.BinaryRep

theorem represents_totallyPositive : ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ a b n : K, star a = a → star b = b → star n = n →
    (∀ φ : K →+* ℂ, 0 < (φ a).re) → (∀ φ : K →+* ℂ, 0 < (φ b).re) → (∀ φ : K →+* ℂ, 0 < (φ n).re) →
    ∃ s t : K, a * (s * star s) + b * (t * star t) = n := by
  intro K _ _ _ hc a b n ha hb hn hpa hpb hpn
  haveI : IsCMField K := GlobalTheory.OrthoLattice.isCMField_of_star K hc.1 hc.2.1
  let φ0 : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  have hst : ∀ x : K, star x = FD.cc x := fun x =>
    φ0.injective (by rw [FD.cc, IsCMField.complexEmbedding_complexConj]; exact hc.2.1 φ0 x)
  have hreal : ∀ x : K, star x = x → ∀ τ : K →+* ℂ, (τ x).im = 0 := by
    intro x hx τ
    have h := hc.2.1 τ x
    rw [hx] at h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hne : ∀ x : K, (∀ φ : K →+* ℂ, 0 < (φ x).re) → x ≠ 0 := by
    intro x hx h0
    have := hx φ0
    simp [h0] at this
  have ha0 := hne a hpa
  have hb0 := hne b hpb
  have hn0 := hne n hpn
  have hca : FD.cc a = a := by rw [← hst, ha]
  have hcb : FD.cc b = b := by rw [← hst, hb]
  have hcn : FD.cc n = n := by rw [← hst, hn]
  have hcab : FD.cc (a * b * n) = a * b * n := by
    rw [← hst, star_mul, star_mul, ha, hb, hn]; ring
  set G : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![a, b] with hG
  set G' : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![n, a * b * n] with hG'
  have herm_diag : ∀ d : Fin 2 → K, (∀ i, FD.cc (d i) = d i) →
      ∀ i j, FD.cc (Matrix.diagonal d i j) = Matrix.diagonal d j i := by
    intro d hd i j
    by_cases h : i = j
    · subst h; simp [hd]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), FD.cc]
  have hGh : ∀ i j, FD.cc (G i j) = G j i :=
    herm_diag _ (fun i => by fin_cases i <;> simp [hca, hcb])
  have hG'h : ∀ i j, FD.cc (G' i j) = G' j i :=
    herm_diag _ (fun i => by fin_cases i <;> simp [hcn, hcab])
  have hdG : G.det = a * b := by simp [hG, Matrix.det_diagonal, Fin.prod_univ_two]
  have hdG' : G'.det = n * (a * b * n) := by simp [hG', Matrix.det_diagonal, Fin.prod_univ_two]
  have hpos : ∀ d : Fin 2 → K, (∀ i, star (d i) = d i ∧ ∀ φ : K →+* ℂ, 0 < (φ (d i)).re) →
      ∀ τ : K →+* ℂ, ∀ i, (τ (d i)).im = 0 ∧ 0 < (τ (d i)).re :=
    fun d hd τ i => ⟨hreal _ (hd i).1 τ, (hd i).2 τ⟩
  have habn : star (a * b * n) = a * b * n := by rw [star_mul, star_mul, ha, hb, hn]; ring
  have hpabn : ∀ φ : K →+* ℂ, 0 < (φ (a * b * n)).re := by
    intro φ
    have e : ∀ x : K, star x = x → (φ x : ℂ) = ((φ x).re : ℂ) := fun x hx =>
      Complex.ext rfl (by simp [hreal x hx φ])
    rw [map_mul, map_mul, e a ha, e b hb, e n hn]
    simp only [← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_pos (mul_pos (hpa φ) (hpb φ)) (hpn φ)
  obtain ⟨γ, hγ⟩ := (GlobalTheory.QNorm.landherr_and_landherrSt.2) K 2 G G' hGh hG'h
    (by rw [hdG]; exact mul_ne_zero ha0 hb0)
    (by rw [hdG']; exact mul_ne_zero hn0 (mul_ne_zero (mul_ne_zero ha0 hb0) hn0))
    (fun τ => ⟨2,
      gram_diag_pos τ ![a, b] (hpos _ (fun i => by fin_cases i <;> simp [ha, hb, hpa, hpb]) τ),
      gram_diag_pos τ ![n, a * b * n]
        (hpos _ (fun i => by fin_cases i; exacts [⟨hn, hpn⟩, ⟨habn, hpabn⟩]) τ)⟩)
    ⟨n, by rw [hdG', hdG, hcn]; ring⟩
  have h := hγ (Pi.single 0 1) (Pi.single 0 1)
  set v := (γ : Matrix (Fin 2) (Fin 2) K) *ᵥ Pi.single 0 1 with hv
  refine ⟨v 0, v 1, ?_⟩
  simp only [FD.herm, Fin.sum_univ_two, hG, hG', Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
    Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)] at h
  simp [FD.cc] at h
  rw [hst, hst]
  simp only [FD.cc]
  linear_combination h

end GlobalTheory.BinaryRep
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.exists_haarMeasure_unipotentRadical_covolume_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ μ : Measure (Nsub (AF F) σ J P), μ.IsHaarMeasure ∧ covol μ = 1 := by
  first | exact @GlobalTheory.NsubHaarCovol.exists_haar_covol_one | exact GlobalTheory.NsubHaarCovol.exists_haar_covol_one | (intros; apply GlobalTheory.NsubHaarCovol.exists_haar_covol_one <;> assumption)
end

section

namespace GlobalTheory

theorem rowsFinDim_link : Formalism.L2.SG.RowsDef.RowsFinDim :=
  CompanionTheory.D.gk.RF.automorphic_forms_finite_dimensional

end GlobalTheory
end

section

namespace GlobalTheory.Sloc.CoefWeighted

theorem coefWeightedLoc_uncond : Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc :=
  ReciprocityTheory.ChartRestriction.DS.coefWeightedLoc

end GlobalTheory.Sloc.CoefWeighted
end

section


theorem _root_.GlobalTheory.T.capelli_eigenvalue_kFinite_discreteSeries_coeff : PI.KFinSmooth → PI.DSInfCharCap.DSInfCharCap → PI.CapelliEig.CapEig := by
  first | exact @GlobalTheory.CapelliEigenvalue.capEig | exact GlobalTheory.CapelliEigenvalue.capEig | (intros; apply GlobalTheory.CapelliEigenvalue.capEig <;> assumption)
end

section


theorem _root_.GlobalTheory.T.haar_unitaryGroupWb_density_chart : PI.RhsWLim.W.HaarDens := by
  first | exact @GlobalTheory.HaarDensChart.haarDens | exact GlobalTheory.HaarDensChart.haarDens | (intros; apply GlobalTheory.HaarDensChart.haarDens <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.RowsGenus

theorem main : ∀ (D : D7) (u : D.what₂.Word), (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) → ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ Λ' : LatV D, IsRowLat D F0 Λ' → L0X D Λ' (lf D F0) ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)) := by
  intro D u hp _ hs F0 he hz Λ hΛ Λ' hΛ'
  have h := (GlobalTheory.Mass.RowPerp.main D u F0 he hz).2
  exact ((GlobalTheory.Mass.CyclicGenus.main D.host.E (D.sp.X 0).V (D.sp.X 0).hT D.sp.cm.cmUnram (D.sp.X 0).herm
    (D.sp.X 0).nondeg (Tu D u) hp hs).2 _ _ (h Λ hΛ).1 (h Λ hΛ).2).2 (h Λ' hΛ')

end GlobalTheory.LoopC.RowsGenus
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.MassAtRecord

theorem massRatio_at_record : ∀ D : D7, UnitaryVolumeMass.stMassRatio D := fun D => by
  letI := D.host.cmStar
  exact fun j hj V V' _ _ _ _ _ _ _ _ f f' L L' hs hs' ho ho' =>
    GlobalTheory.T.siegel_massRatio_unimodular_definite D.host.E D.sp.cm.cmUnram j hj V V' f f' L L' hs hs' ho ho'

end GlobalTheory.MassAtRecord
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

theorem _root_.GlobalTheory.T.exists_adelic_unitaryGroup_models_equiv : ∀ I : AutInst, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt I.F I.E I.cm.sig ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND I.cm.sig I.J ∧ ∃ T : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J ≃ₜ* I.GA, (∀ h, (show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J from h) ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J ↔ T h ∈ I.GFset) ∧ (∀ h, I.fmat (T h).2 = (Formalism.MainNotions.StandardLattice.finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _)) ∧ ∀ v θ, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ → ∀ h, uMat ((T h).1 v) = (I.P v)⁻¹ * Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J θ h * I.P v := by
  first | exact @GlobalTheory.AdelicModels.exists_adelic_equiv | exact GlobalTheory.AdelicModels.exists_adelic_equiv | (intros; apply GlobalTheory.AdelicModels.exists_adelic_equiv <;> assumption)
end

section

open MeasureTheory Matrix Formalism.MainNotions.S
open scoped ENNReal

theorem _root_.GlobalTheory.T.sobolev_valueAtOne_fixedCompact_diagSignUnitary : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ) (Q : Set (Formalism.REAL.UJ ε)), IsCompact Q ∧ (∀ l ∈ S, ∀ X ∈ l, Formalism.REAL.inG ε X) ∧ 0 ≤ C ∧ ∀ F : List (Matrix (Fin n) (Fin n) ℂ) → Matrix (Fin n) (Fin n) ℂ → ℂ, (∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ContinuousOn (F l) (UJset ε)) → (∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Formalism.REAL.inG ε Y) → ∀ X, Formalism.REAL.inG ε X → ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => F l (g * NormedSpace.exp ((t : ℂ) • X))) (F (X :: l) g) 0) → ENNReal.ofReal (‖F [] 1‖ ^ 2) ≤ ENNReal.ofReal C * (S.map fun l => ∫⁻ y in Q, ENNReal.ofReal (‖F l (umat y)‖ ^ 2) ∂(Formalism.REAL.muG ε)).sum := by
  first | exact @GlobalTheory.SobolevHaar.sobolev_at_one_compact | exact GlobalTheory.SobolevHaar.sobolev_at_one_compact | (intros; apply GlobalTheory.SobolevHaar.sobolev_at_one_compact <;> assumption)
end
