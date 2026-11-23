module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevIntegrationByParts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle235
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelMultiplierOnEigenfunction
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
public import Mathlib.Analysis.Matrix.Normed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCholeskyFactor
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalTestFunctionExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionGood
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle236
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC

@[expose] public section

section


theorem _root_.GlobalTheory.T.sobolev_integration_by_parts : PositivityTheory.RgBcC.Fc.IbpSob := by
  first | exact @GlobalTheory.CompanionTheory.FcCalc.Ibp.ibpSob | exact GlobalTheory.CompanionTheory.FcCalc.Ibp.ibpSob | (intros; apply GlobalTheory.CompanionTheory.FcCalc.Ibp.ibpSob <;> assumption)
end

section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.positive_cone_isOpen : ∀ n : ℕ, IsOpen (PositivityTheory.RgBcC.cone n) := by
  first | exact @GlobalTheory.CompanionTheory.ConeHaar.isOpen_cone | exact GlobalTheory.CompanionTheory.ConeHaar.isOpen_cone | (intros; apply GlobalTheory.CompanionTheory.ConeHaar.isOpen_cone <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.gelfand_operator_adjoint : LgFacts → RCalc → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (s : Bool) (m : ℕ) (f h : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) → Cpt f → Cpt h → ∫ y : G n, ⟪gel s m f y.val, h y.val⟫_ℂ ∂μ = (-1 : ℂ) ^ m * ∫ y : G n, ⟪f y.val, gelT (!s) m h y.val⟫_ℂ ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.Ibp.ibp_gel | exact GlobalTheory.CompanionTheory.WaveMult.Ibp.ibp_gel | (intros; apply GlobalTheory.CompanionTheory.WaveMult.Ibp.ibp_gel <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.kernel_multiplier_on_eigenfunction : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (val : Inf n → ℂ) (T : ℝ), IsMult μ E k val T → ∀ χ, ∀ f ∈ CE E, IsEig χ f → ∀ x ∈ GLs n, act μ E k f x = val χ • f x := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.act_eq_val_of_isMult | exact GlobalTheory.CompanionTheory.WaveMult.act_eq_val_of_isMult | (intros; apply GlobalTheory.CompanionTheory.WaveMult.act_eq_val_of_isMult <;> assumption)
end

section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.smooth_positive_definite_sqrt : ∀ n : ℕ, ∃ σ₀ : Mat n → Mat n, ContDiffOn ℝ ∞ σ₀ {P | P.PosDef} ∧ ∀ P : Mat n, P.PosDef → σ₀ P * (σ₀ P)ᴴ = P := by
  first | exact @GlobalTheory.CompanionTheory.ConeHaar.Chol.exists_smooth_section | exact GlobalTheory.CompanionTheory.ConeHaar.Chol.exists_smooth_section | (intros; apply GlobalTheory.CompanionTheory.ConeHaar.Chol.exists_smooth_section <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis


theorem _root_.GlobalTheory.T.exists_summable_majorant_lattice_sum : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) {C : Set (GL ι 𝔸[k])} (hC : IsCompact C), ∃ u : (ι → k) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → k,
      ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ)‖ ≤ u ξ := by
  first | exact @GlobalTheory.CompanionTheory.EisRkNBound.exists_summable_bound_thetaC | exact GlobalTheory.CompanionTheory.EisRkNBound.exists_summable_bound_thetaC | (intros; apply GlobalTheory.CompanionTheory.EisRkNBound.exists_summable_bound_thetaC <;> assumption)
end

section


theorem _root_.GlobalTheory.T.spherical_test_function_exists : PositivityTheory.RgEis.TestSph := by
  first | exact @GlobalTheory.CompanionTheory.RgEisTestSph.testSph | exact GlobalTheory.CompanionTheory.RgEisTestSph.testSph | (intros; apply GlobalTheory.CompanionTheory.RgEisTestSph.testSph <;> assumption)
end

section


theorem _root_.GlobalTheory.T.standard_section_good : PositivityTheory.RgEis.StdGood := by
  first | exact @GlobalTheory.CompanionTheory.StdGoodAd.stdGood | exact GlobalTheory.CompanionTheory.StdGoodAd.stdGood | (intros; apply GlobalTheory.CompanionTheory.StdGoodAd.stdGood <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.ZetaAlongK

open PositivityTheory.RgEis PositivityTheory.RgEis.MG GroundTheory.Global GroundTheory.Automorphic

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem firstCountable_gl : FirstCountableTopology (GL ι 𝔸[k]) := by
  have h1 : SecondCountableTopology (Matrix ι ι 𝔸[k]) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → 𝔸[k]))
  have h2 : SecondCountableTopology (Matrix ι ι 𝔸[k])ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix ι ι 𝔸[k])).symm.isEmbedding.secondCountableTopology
  have h3 : SecondCountableTopology (GL ι 𝔸[k]) :=
    (Units.isEmbedding_embedProduct (M := Matrix ι ι 𝔸[k])).secondCountableTopology
  infer_instance

theorem differentiableAt_globalZeta_of_majorant {F : 𝔸[k] → ℂ} (hFc : Continuous F)
    (χ : HeckeCharacter k) {s₀ : ℂ} {δ : ℝ} (hδ : 0 < δ) {f₀ f₁ f₂ : IdeleGroup k → ℝ}
    (i₀ : Integrable f₀ (ideleMeasure k)) (i₁ : Integrable f₁ (ideleMeasure k))
    (i₂ : Integrable f₂ (ideleMeasure k))
    (b₀ : ∀ t : IdeleGroup k, ‖F t‖ * (IdeleGroup.ideleModule k t : ℝ) ^ s₀.re ≤ f₀ t)
    (b₁ : ∀ t : IdeleGroup k, ‖F t‖ * (IdeleGroup.ideleModule k t : ℝ) ^ (s₀.re - 2 * δ) ≤ f₁ t)
    (b₂ : ∀ t : IdeleGroup k, ‖F t‖ * (IdeleGroup.ideleModule k t : ℝ) ^ (s₀.re + 2 * δ) ≤ f₂ t) :
    DifferentiableAt ℂ (globalZeta F χ) s₀ := by
  have hT : ∀ x : IdeleGroup k, 0 < (IdeleGroup.ideleModule k x : ℝ) :=
    fun x ↦ (IdeleGroup.ideleModule k x).2
  set G : ℂ → IdeleGroup k → ℂ := fun s x ↦
    F x * (χ.toIdele x : ℂ) * ((IdeleGroup.ideleModule k x : ℝ) : ℂ) ^ s with hG
  set G' : ℂ → IdeleGroup k → ℂ :=
    fun s x ↦ G s x * Complex.log (IdeleGroup.ideleModule k x : ℝ) with hG'
  set bound : IdeleGroup k → ℝ := fun x ↦ (f₁ x + f₂ x) / δ with hbound
  have hbound_int : Integrable bound (ideleMeasure k) := (i₁.add i₂).div_const δ
  have hcont' : Continuous (G' s₀) :=
    (continuous_zetaIntegrand hFc χ s₀).mul
      ((Complex.continuous_ofReal.comp continuous_ideleModule_val).clog
        fun x ↦ Complex.ofReal_mem_slitPlane.2 (hT x))
  have hint₀ : Integrable (G s₀) (ideleMeasure k) := by
    refine i₀.mono' (continuous_zetaIntegrand hFc χ s₀).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)
    simp only [hG]
    rw [norm_zetaIntegrand]
    exact b₀ x
  have hle : ∀ x, ∀ s ∈ Metric.ball s₀ δ, ‖G' s x‖ ≤ bound x := by
    intro x s hs
    have hre : |s.re - s₀.re| < δ := by
      have := (Complex.abs_re_le_norm (s - s₀)).trans_lt (mem_ball_iff_norm.1 hs)
      rwa [Complex.sub_re] at this
    have hnorm : ‖G' s x‖ = ‖F x‖ * ((IdeleGroup.ideleModule k x : ℝ) ^ s.re *
        |Real.log (IdeleGroup.ideleModule k x : ℝ)|) := by
      simp only [hG', hG]
      rw [norm_mul, norm_zetaIntegrand, ← Complex.ofReal_log (hT x).le, Complex.norm_real,
        Real.norm_eq_abs, mul_assoc]
    rw [hnorm]
    calc ‖F x‖ * ((IdeleGroup.ideleModule k x : ℝ) ^ s.re * |Real.log (IdeleGroup.ideleModule k x : ℝ)|)
        ≤ ‖F x‖ * (((IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re - 2 * δ) +
            (IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re + 2 * δ)) / δ) :=
          mul_le_mul_of_nonneg_left (rpow_mul_abs_log_le (hT x) hδ hre) (norm_nonneg _)
      _ = (‖F x‖ * (IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re - 2 * δ) +
            ‖F x‖ * (IdeleGroup.ideleModule k x : ℝ) ^ (s₀.re + 2 * δ)) / δ := by ring
      _ ≤ bound x := div_le_div_of_nonneg_right (add_le_add (b₁ x) (b₂ x)) hδ.le
  have hdiff : ∀ x, ∀ s ∈ Metric.ball s₀ δ, HasDerivAt (fun s ↦ G s x) (G' s x) s := by
    intro x s _
    have h := ((Complex.hasStrictDerivAt_const_cpow (y := s)
      (Or.inl (Complex.ofReal_ne_zero.2 (hT x).ne'))).hasDerivAt).const_mul
        (F x * (χ.toIdele x : ℂ))
    refine h.congr_deriv ?_
    simp only [hG', hG]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ideleMeasure k) (F := G)
    (F' := G') (x₀ := s₀) (bound := bound) (Metric.ball_mem_nhds s₀ hδ)
    (Eventually.of_forall fun s ↦ (continuous_zetaIntegrand hFc χ s).aestronglyMeasurable)
    hint₀ hcont'.aestronglyMeasurable
    (Eventually.of_forall fun x s hs ↦ hle x s hs) hbound_int
    (Eventually.of_forall fun x s hs ↦ hdiff x s hs)
  exact key.2.differentiableAt

def col (m : GL ι 𝔸[k]) (i : ι) : ι → 𝔸[k] := (m : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i 1

theorem continuous_col (i : ι) : Continuous fun m : GL ι 𝔸[k] => col m i :=
  (Units.continuous_val (M := Matrix ι ι 𝔸[k])).matrix_mulVec continuous_const

theorem continuous_line {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (x : ι → 𝔸[k]) :
    Continuous fun t : 𝔸[k] => Ψ (t • x) :=
  hΨ.comp (continuous_id.smul continuous_const)

def Maj (Ψ : (ι → 𝔸[k]) → ℂ) (i : ι) (C : Set (GL ι 𝔸[k])) : Prop :=
  ∀ a b : ℝ, 1 < a → ∃ f : IdeleGroup k → ℝ, Integrable f (ideleMeasure k) ∧
    ∀ x : ℝ, a ≤ x → x ≤ b → ∀ m ∈ C, ∀ t : IdeleGroup k,
      ‖Ψ ((t : 𝔸[k]) • col m i)‖ * (IdeleGroup.ideleModule k t : ℝ) ^ x ≤ f t

theorem differentiableOn_lineZeta {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} (h : Maj Ψ i C) {m : GL ι 𝔸[k]} (hm : m ∈ C) :
    DifferentiableOn ℂ (fun s => lineZeta Ψ ω s (col m i)) {s | 1 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 1 < s₀.re := hs₀
  set δ := (s₀.re - 1) / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨f₀, i₀, b₀⟩ := h s₀.re s₀.re hs₀'
  obtain ⟨f₁, i₁, b₁⟩ := h (s₀.re - 2 * δ) (s₀.re - 2 * δ) (by rw [hδdef]; linarith)
  obtain ⟨f₂, i₂, b₂⟩ := h (s₀.re + 2 * δ) (s₀.re + 2 * δ) (by linarith)
  exact (differentiableAt_globalZeta_of_majorant (F := fun t => Ψ (t • col m i))
    (continuous_line hΨ _) ω hδ i₀ i₁ i₂ (fun t => b₀ _ le_rfl le_rfl m hm t)
    (fun t => b₁ _ le_rfl le_rfl m hm t) (fun t => b₂ _ le_rfl le_rfl m hm t)).differentiableWithinAt

theorem norm_lineZeta_le {Ψ : (ι → 𝔸[k]) → ℂ} (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} {f : IdeleGroup k → ℝ} {a b : ℝ} (hf : Integrable f (ideleMeasure k))
    (h : ∀ x : ℝ, a ≤ x → x ≤ b → ∀ m ∈ C, ∀ t : IdeleGroup k,
      ‖Ψ ((t : 𝔸[k]) • col m i)‖ * (IdeleGroup.ideleModule k t : ℝ) ^ x ≤ f t)
    {s : ℂ} (h1 : a ≤ s.re) (h2 : s.re ≤ b) {m : GL ι 𝔸[k]} (hm : m ∈ C) :
    ‖lineZeta Ψ ω s (col m i)‖ ≤ ∫ t, f t ∂ideleMeasure k := by
  refine norm_integral_le_of_norm_le hf (Eventually.of_forall fun t => ?_)
  rw [norm_zetaIntegrand (fun a => Ψ (a • col m i)) ω s t]
  exact h _ h1 h2 m hm t

def ig (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (i : ι) (y : ℂ × GL ι 𝔸[k]) (t : IdeleGroup k) : ℂ :=
  Ψ ((t : 𝔸[k]) • col y.2 i) * (ω.toIdele t : ℂ) * ((IdeleGroup.ideleModule k t : ℝ) : ℂ) ^ y.1

theorem norm_ig (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (i : ι) (y : ℂ × GL ι 𝔸[k]) (t : IdeleGroup k) :
    ‖ig Ψ ω i y t‖ = ‖Ψ ((t : 𝔸[k]) • col y.2 i)‖ * (IdeleGroup.ideleModule k t : ℝ) ^ y.1.re :=
  norm_zetaIntegrand (fun a => Ψ (a • col y.2 i)) ω y.1 t

theorem continuous_ig {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k) (i : ι)
    (y : ℂ × GL ι 𝔸[k]) : Continuous (ig Ψ ω i y) :=
  continuous_zetaIntegrand (continuous_line hΨ (col y.2 i)) ω y.1

theorem continuous_ig_param {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k) (i : ι)
    (t : IdeleGroup k) : Continuous fun y : ℂ × GL ι 𝔸[k] => ig Ψ ω i y t := by
  have c1 : Continuous fun y : ℂ × GL ι 𝔸[k] => Ψ ((t : 𝔸[k]) • col y.2 i) :=
    hΨ.comp ((continuous_const : Continuous fun _ : ℂ × GL ι 𝔸[k] => (t : 𝔸[k])).smul
      ((continuous_col i).comp continuous_snd))
  refine (c1.mul continuous_const).mul ?_
  exact continuous_fst.const_cpow (Or.inl (Complex.ofReal_ne_zero.2 (IdeleGroup.ideleModule k t).2.ne'))

theorem eventually_near {C : Set (GL ι 𝔸[k])} {s₀ : ℂ} {m₀ : GL ι 𝔸[k]} {a b : ℝ} (ha : a < s₀.re)
    (hb : s₀.re < b) : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝[{s | 1 < s.re} ×ˢ C] (s₀, m₀),
      a ≤ y.1.re ∧ y.1.re ≤ b ∧ y.2 ∈ C := by
  have hc : Continuous fun y : ℂ × GL ι 𝔸[k] => y.1.re := Complex.continuous_re.comp continuous_fst
  have e1 : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝 (s₀, m₀), a < y.1.re :=
    hc.continuousAt.eventually (lt_mem_nhds ha)
  have e2 : ∀ᶠ y : ℂ × GL ι 𝔸[k] in 𝓝 (s₀, m₀), y.1.re < b :=
    hc.continuousAt.eventually (gt_mem_nhds hb)
  filter_upwards [nhdsWithin_le_nhds e1, nhdsWithin_le_nhds e2, self_mem_nhdsWithin] with y y1 y2 y3
  exact ⟨y1.le, y2.le, y3.2⟩

theorem continuousOn_ig {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} (h : Maj Ψ i C) :
    ContinuousOn (fun y : ℂ × GL ι 𝔸[k] => ∫ t, ig Ψ ω i y t ∂ideleMeasure k)
      ({s | 1 < s.re} ×ˢ C) := by
  have := firstCountable_gl (k := k) (ι := ι)
  rintro ⟨s₀, m₀⟩ ⟨hs₀, hm₀⟩
  have hs₀' : 1 < s₀.re := hs₀
  obtain ⟨f, hf, hb⟩ := h ((1 + s₀.re) / 2) (s₀.re + 1) (by linarith)
  have hnear := eventually_near (C := C) (m₀ := m₀) (s₀ := s₀) (a := (1 + s₀.re) / 2) (b := s₀.re + 1)
    (by linarith) (by linarith)
  refine continuousWithinAt_of_dominated (bound := f) ?_ ?_ hf ?_
  · exact Eventually.of_forall fun y => (continuous_ig hΨ ω i y).aestronglyMeasurable
  · filter_upwards [hnear] with y hy
    refine Eventually.of_forall fun t => ?_
    rw [norm_ig]
    exact hb _ hy.1 hy.2.1 _ hy.2.2 t
  · exact Eventually.of_forall fun t => (continuous_ig_param hΨ ω i t).continuousWithinAt

theorem continuousOn_lineZeta {Ψ : (ι → 𝔸[k]) → ℂ} (hΨ : Continuous Ψ) (ω : HeckeCharacter k)
    {i : ι} {C : Set (GL ι 𝔸[k])} (h : Maj Ψ i C) :
    ContinuousOn (fun y : ℂ × GL ι 𝔸[k] => lineZeta Ψ ω y.1 (col y.2 i))
      ({s | 1 < s.re} ×ˢ C) :=
  continuousOn_ig hΨ ω h

theorem zt_eq {G : Type} [Group G] (π : G →* GL ι 𝔸[k]) (d : ι → IdeleGroup k) (i : ι)
    (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (s : ℂ) (g : G) :
    zt π d i Ψ ω s g = lineZeta Ψ ω s (col (kap π d g)⁻¹ i) := rfl

theorem zetaK : EpConv → ZetaK := by
  intro hE G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hS Ψ hΨ
  have hΨc : Continuous Ψ := GJMatrix.continuous_of_mem_schwartzBruhatPi hΨ
  have hcont : Continuous fun g : G => (kap π d g)⁻¹ :=
    ((continuous_const.mul hS.cont).mul continuous_const).inv
  have hC : IsCompact ((fun g : G => (kap π d g)⁻¹) '' (K : Set G)) := hK.image hcont
  have hM : Maj Ψ i ((fun g : G => (kap π d g)⁻¹) '' (K : Set G)) :=
    fun a b ha => (hE k ι Ψ hΨ).1 i a b _ ha hC
  have hmem : ∀ κ : K, (kap π d κ)⁻¹ ∈ (fun g : G => (kap π d g)⁻¹) '' (K : Set G) :=
    fun κ => ⟨κ, κ.2, rfl⟩
  refine ⟨fun κ => differentiableOn_lineZeta hΨc ω hM (hmem κ), ?_, ?_⟩
  · have hmap : Continuous fun y : ℂ × K => (y.1, (kap π d (y.2 : G))⁻¹) :=
      continuous_fst.prodMk (hcont.comp (continuous_subtype_val.comp continuous_snd))
    have hS' : Set.MapsTo (fun y : ℂ × K => (y.1, (kap π d (y.2 : G))⁻¹))
        ({s : ℂ | 1 < s.re} ×ˢ Set.univ)
        ({s : ℂ | 1 < s.re} ×ˢ ((fun g : G => (kap π d g)⁻¹) '' (K : Set G))) :=
      fun y hy => ⟨hy.1, hmem y.2⟩
    have h2 := ContinuousOn.comp (continuousOn_lineZeta hΨc ω hM) hmap.continuousOn hS'
    exact h2.congr fun y _ => zt_eq π d i Ψ ω y.1 y.2
  · intro a b ha
    obtain ⟨f, hf, hb⟩ := (hE k ι Ψ hΨ).1 i a b _ ha hC
    exact ⟨∫ t, f t ∂ideleMeasure k, fun s h1 h2 κ => norm_lineZeta_le ω hf hb h1 h2 (hmem κ)⟩

end GlobalTheory.CompanionTheory.ZetaAlongK
end
end

section

open MeasureTheory Filter Topology
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisAvg

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem pointwise_bound {K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {φ : K → ℂ} {M : ℝ}
    (hM1 : 1 ≤ M) (hM : ∀ κ, ‖ρ κ‖ ≤ M) (hc : ∀ p ∈ P, ‖c p‖ = 1) (hL : Law K P c φ)
    (hN : Near K P {v | ‖ρ v - 1‖ ≤ 1 / (4 * M)} φ) {w : W} (hw : w ∈ secSp K P c ρ) (κ : K) :
    ‖φ κ • ρ κ w - ((‖φ κ‖ : ℝ) : ℂ) • w‖ ≤ ‖φ κ‖ * ‖w‖ / 2 := by
  by_cases h0 : φ κ = 0
  · simp [h0]
  obtain ⟨r, v, hr, hv, rfl, hn⟩ := hN κ h0
  have hM0 : 0 < M := by linarith
  have hcr : ‖c r‖ = 1 := hc _ hr
  have hφ : φ (r * v) = c r * φ v := hL r v hr
  have hnorm : ‖φ (r * v)‖ = ‖φ v‖ := by rw [hφ, norm_mul, hcr, one_mul]
  have hwr : c r • ρ r w = w := hw r hr
  obtain ⟨u, hu⟩ : ∃ u, u = ρ v w - w := ⟨_, rfl⟩
  have hub : ‖u‖ ≤ ‖w‖ / (4 * M) := by
    have h1 : u = (ρ v - 1) w := by simp [hu]
    have hv' : ‖ρ v - 1‖ ≤ 1 / (4 * M) := hv
    rw [h1]
    calc ‖(ρ v - 1) w‖ ≤ ‖ρ v - 1‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 / (4 * M) * ‖w‖ := by gcongr
      _ = ‖w‖ / (4 * M) := by ring
  have hrb : ‖c r • ρ r u‖ ≤ ‖w‖ / 4 := by
    rw [norm_smul, hcr, one_mul]
    calc ‖ρ r u‖ ≤ ‖ρ r‖ * ‖u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * (‖w‖ / (4 * M)) := by
          gcongr
          exact hM r
      _ = ‖w‖ / 4 := by field_simp
  have hexp : φ (r * v) • ρ (r * v) w - ((‖φ (r * v)‖ : ℝ) : ℂ) • w =
      (φ v - ((‖φ v‖ : ℝ) : ℂ)) • w + φ v • (c r • ρ r u) := by
    have h2 : ρ v w = w + u := by simp [hu]
    have h3 : ρ (r * v) w = ρ r w + ρ r u := by
      rw [map_mul, ContinuousLinearMap.mul_apply, h2, map_add (f := _)]
    rw [hnorm, hφ, h3, smul_add, mul_comm, mul_smul, hwr, sub_smul, mul_smul]
    abel
  rw [hexp, hnorm]
  calc ‖(φ v - ((‖φ v‖ : ℝ) : ℂ)) • w + φ v • (c r • ρ r u)‖
      ≤ ‖φ v - ((‖φ v‖ : ℝ) : ℂ)‖ * ‖w‖ + ‖φ v‖ * ‖c r • ρ r u‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ ‖φ v‖ / 4 * ‖w‖ + ‖φ v‖ * (‖w‖ / 4) := by gcongr
    _ = ‖φ v‖ * ‖w‖ / 2 := by ring

theorem avg_sub_bound [FiniteDimensional ℂ W] {K : Subgroup G} [MeasurableSpace K] [BorelSpace K]
    [CompactSpace K] (μ : Measure K) [IsProbabilityMeasure μ] {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ)
    {φ : K → ℂ} (hφ : Continuous φ) (w : W)
    (h : ∀ κ, ‖φ κ • ρ κ w - ((‖φ κ‖ : ℝ) : ℂ) • w‖ ≤ ‖φ κ‖ * ‖w‖ / 2) :
    ‖avg μ ρ φ w - ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w‖ ≤ (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hint : Integrable (fun κ => φ κ • ρ κ) μ :=
    (hφ.smul hρ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun κ => ‖φ κ‖) μ :=
    hφ.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint3 : Integrable (fun κ => φ κ • ρ κ w) μ := by
    have := hint.apply_continuousLinearMap w
    exact this
  have hint4 : Integrable (fun κ => ((‖φ κ‖ : ℝ) : ℂ) • w) μ :=
    (hint2.ofReal (𝕜 := ℂ)).smul_const w
  have e1 : avg μ ρ φ w = ∫ κ, φ κ • ρ κ w ∂μ := ContinuousLinearMap.integral_apply hint w
  have e2 : ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w = ∫ κ, ((‖φ κ‖ : ℝ) : ℂ) • w ∂μ := by
    rw [integral_smul_const, integral_complex_ofReal]
  rw [e1, e2, ← integral_sub hint3 hint4]
  have e3 : (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 = ∫ κ, ‖φ κ‖ * ‖w‖ / 2 ∂μ := by
    rw [integral_div, integral_mul_const]
  rw [e3]
  exact norm_integral_le_of_norm_le ((hint2.mul_const _).div_const _) (Eventually.of_forall h)

theorem mass_pos {K : Subgroup G} [MeasurableSpace K] [BorelSpace K] [CompactSpace K]
    [IsTopologicalGroup K] (μ : Measure K) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    {φ : K → ℂ} (hφ : Continuous φ) (h1 : φ 1 = 1) : 0 < ∫ κ, ‖φ κ‖ ∂μ := by
  refine hφ.norm.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (fun _ => norm_nonneg _) (x := 1) ?_
  simp [h1]

end Abstract

theorem avgInv_of_avgMem : AvgMem → AvgInv := by
  intro hA G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hH hP Γ P c hPar
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI := hH
  haveI := hP
  obtain ⟨M, hM1, hM⟩ : ∃ M : ℝ, 1 ≤ M ∧ ∀ κ, ‖ρ κ‖ ≤ M := by
    obtain ⟨C, hC⟩ := (isCompact_range hρ).isBounded.exists_norm_le
    exact ⟨max 1 C, le_max_left _ _, fun κ => (hC _ ⟨κ, rfl⟩).trans (le_max_right _ _)⟩
  have hM0 : 0 < M := by linarith
  refine ⟨{v | ‖ρ v - 1‖ ≤ 1 / (4 * M)}, ?_, ?_⟩
  · have ht : Tendsto (fun v => ρ v - 1) (𝓝 (1 : K)) (𝓝 0) := by
      have h5 := hρ.tendsto (1 : K)
      rw [map_one] at h5
      simpa using h5.sub_const 1
    have h4 : (0 : ℝ) < 1 / (4 * M) := by positivity
    filter_upwards [ht (Metric.closedBall_mem_nhds 0 h4)] with v hv
    simpa using hv
  · intro φ hφ h1 hL hN
    have hI : 0 < ∫ κ, ‖φ κ‖ ∂μ := mass_pos μ hφ h1
    have hb : ∀ w ∈ secSp K P c ρ,
        ‖avg μ ρ φ w - ((∫ κ, ‖φ κ‖ ∂μ : ℝ) : ℂ) • w‖ ≤ (∫ κ, ‖φ κ‖ ∂μ) * ‖w‖ / 2 := fun w hw =>
      avg_sub_bound μ hρ hφ w (pointwise_bound hM1 hM hPar.ch.norm hL hN hw)
    have hmem : ∀ w : W, avg μ ρ φ w ∈ secSp K P c ρ := fun w =>
      hA G W K ρ hK hρ μ hH hP Γ P c hPar φ hφ hL w
    let T : secSp K P c ρ →ₗ[ℂ] secSp K P c ρ :=
      ((avg μ ρ φ : W →L[ℂ] W) : W →ₗ[ℂ] W).restrict fun w _ => hmem w
    have hinj : Function.Injective T := by
      refine (injective_iff_map_eq_zero T).mpr fun w hw => ?_
      have h0 : avg μ ρ φ (w : W) = 0 := congrArg Subtype.val hw
      have h6 := hb w w.2
      rw [h0, zero_sub, norm_neg, norm_smul, Complex.norm_real, Real.norm_of_nonneg hI.le] at h6
      have h7 : ‖(w : W)‖ = 0 := by
        have h8 : 0 ≤ ‖(w : W)‖ := norm_nonneg _
        nlinarith
      exact Subtype.ext (norm_eq_zero.mp h7)
    let e := LinearEquiv.ofInjectiveEndo T hinj
    refine ⟨LinearMap.toContinuousLinearMap ((secSp K P c ρ).subtype ∘ₗ e.symm.toLinearMap), fun w => ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply w)

end GlobalTheory.CompanionTheory.RgEisAvg
end

section

open PositivityTheory.Rg.Mass

theorem _root_.GlobalTheory.T.counting_formula : TestEx → LSide → RSide → Cnt := by
  first | exact @GlobalTheory.CompanionTheory.RgMass.cnt | exact GlobalTheory.CompanionTheory.RgMass.cnt | (intros; apply GlobalTheory.CompanionTheory.RgMass.cnt <;> assumption)
end
