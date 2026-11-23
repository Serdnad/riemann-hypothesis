module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle194
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle060
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle278
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle220
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle213
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle200
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle187
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle193
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle191
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle188
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipApplyCastSuccLast
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle283
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.InductionParabolicGroups
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.lp_coefficient_center_norm_preserved : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (p : ℝ), CoeffLp p π → ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ (v : V) (l : Module.Dual ℂ V), IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} → ‖l (π z v)‖ = ‖l v‖ := by
  first | exact @GlobalTheory.CompanionTheory.CoeffCentral.norm_coeff_central | exact GlobalTheory.CompanionTheory.CoeffCentral.norm_coeff_central | (intros; apply GlobalTheory.CompanionTheory.CoeffCentral.norm_coeff_central <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule

theorem map_eq_sqrt_smul {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ+ G) (ν : Measure G) [ν.IsAddHaarMeasure] (c : ℝ≥0)
    (h : ν.map (e ∘ e) = c • ν) : ν.map e = NNReal.sqrt c • ν := by
  haveI : (ν.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν e
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, ν.map e = b • ν :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (ν.map e) ν⟩
  have he : Measurable e := e.continuous.measurable
  have h2 : ν.map (e ∘ e) = (b * b) • ν := by
    rw [← Measure.map_map he he, hb, Measure.map_smul b he.aemeasurable, hb, smul_smul]
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G)
  have hpos : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have hfin : ν K ≠ ∞ := hK.measure_lt_top.ne
  have hbc : b * b = c := by
    have h3 : ((b * b : ℝ≥0) • ν) K = (c • ν) K := by rw [← h2, h]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 h3
  rw [hb, ← hbc, NNReal.sqrt_mul_self]

theorem scalH_scalH {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (a b : R) (S : HermR R σ n) :
    scalH R σ a (scalH R σ b S) = scalH R σ (a * b) S := by
  apply Subtype.ext
  simp only [scalH_coe, smul_smul, map_mul]

theorem scalH_one {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ n) : scalH R σ 1 S = S := by
  apply Subtype.ext
  simp only [scalH_coe, map_one, one_smul]

def scalEquiv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (n : ℕ) (l : F) (hl : l ≠ 0) : HermR R σ n ≃ₜ+ HermR R σ n :=
  have hc : ∀ a : R, Continuous (scalH R σ (n := n) a) := fun a => by
    obtain ⟨iTR, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
    haveI := iTR
    exact Continuous.subtype_mk ((continuous_const_smul _).comp continuous_subtype_val) _
  have hm : algebraMap F R l * algebraMap F R l⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hl, map_one]
  { toFun := scalH R σ (algebraMap F R l)
    invFun := scalH R σ (algebraMap F R l⁻¹)
    left_inv := fun S => by rw [scalH_scalH, mul_comm, hm, scalH_one]
    right_inv := fun S => by rw [scalH_scalH, hm, scalH_one]
    map_add' := fun S T => by
      apply Subtype.ext
      simp [scalH_coe]
    continuous_toFun := hc _
    continuous_invFun := hc _ }

def oneByOne {F E : Type} [Field F] [Field E] [Algebra F E] (l : F) : Matrix (Fin 1) (Fin 1) E :=
  Matrix.of fun _ _ => algebraMap F E l

theorem action_eq {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (l : F) (S : HermR R σ 1) :
    ((scalH R σ (algebraMap F R l) (scalH R σ (algebraMap F R l) S) : HermR R σ 1) :
        Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) ((oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) *
        (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        (oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R) := by
  have h1 : inclR R (algebraMap F E l) = algebraMap R (R ⊗[F] E) (algebraMap F R l) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes l
  have h2 : sigR R σ (algebraMap R (R ⊗[F] E) (algebraMap F R l)) =
      algebraMap R (R ⊗[F] E) (algebraMap F R l) := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  ext i j
  simp only [scalH_coe, cT, oneByOne, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul, h1, h2]
  have hi : i = default := Subsingleton.elim _ _
  have hj : j = default := Subsingleton.elim _ _
  subst hi hj
  ring

theorem local_scal {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) (l : F) (hl : l ≠ 0) (c : ℝ≥0)
    (ν : Measure (HermR R σ 1)) (hν : ν.IsAddHaarMeasure)
    (h : ∀ τ : HermR R σ 1 → HermR R σ 1, (∀ S, (τ S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) ((oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) *
        (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        (oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) → ν.map τ = c • ν) :
    ν.map (scalH R σ (algebraMap F R l)) = NNReal.sqrt c • ν := by
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  haveI := iTR
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hcm R 1
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  exact map_eq_sqrt_smul (scalEquiv σ hcm R 1 l hl) ν c (h _ (action_eq R σ l))

theorem scal_module : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ l : F, l ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (HermR (Ainf F) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Ainf F) σ (algebraMap F (Ainf F) l)) = cinf • ν) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ ν : Measure (HermR (Fv F v) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Fv F v) σ (algebraMap F (Fv F v) l)) = c v • ν := by
  intro F E _ _ _ _ _ σ hcm l hl
  have hdet : (oneByOne l : Matrix (Fin 1) (Fin 1) E).det ≠ 0 := by
    rw [Matrix.det_fin_one]
    exact (map_ne_zero (algebraMap F E)).2 hl
  obtain ⟨ci, c, hu, hi, hv⟩ := GlobalTheory.T.hermitian_matrix_euler_product F E σ hcm 1 (oneByOne l) hdet
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  refine ⟨NNReal.sqrt ci, fun v => NNReal.sqrt (c v), (PositivityTheory.PlacePermOperatorBicommutantSpan.up_alg F ci ci c c hu hu).2.2.2.2.2.1, ?_, ?_⟩
  · intro ν hν
    exact local_scal σ hcm (Ainf F) (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1) l hl ci ν hν (hi ν hν)
  · intro v ν hν
    exact local_scal σ hcm (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) l hl (c v) ν hν (hv v ν hν)

end GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule

end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd.Vanish

variable {n : ℕ} {W : Type} [NormedAddCommGroup W]

theorem dens_nonneg [NormedSpace ℝ W] (u : ℝ → Mat n → W) (s : ℝ) (y : Mat n) : 0 ≤ dens u s y := by
  unfold dens
  have : 0 ≤ ∑ p : Ix n, ‖Rt (hm p) u s y‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  positivity

theorem sq_le_dens [NormedSpace ℝ W] (u : ℝ → Mat n → W) (s : ℝ) (y : Mat n) :
    ‖u s y‖ ^ 2 ≤ dens u s y := by
  unfold dens
  have : 0 ≤ ∑ p : Ix n, ‖Rt (hm p) u s y‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  nlinarith [sq_nonneg ‖dt u s y‖]

theorem dens_continuousOn [NormedSpace ℝ W] (u : ℝ → Mat n → W) (hu : Sm u) (s : ℝ) :
    ContinuousOn (dens u s) (GLs n) := by
  obtain ⟨h1, h2, h3, -, -⟩ := GlobalTheory.CompanionTheory.WaveSpd.sm_calculus u hu
  have a : ContinuousOn (dt u s) (GLs n) := ((GlobalTheory.CompanionTheory.WaveSpd.sm_calculus (dt u) h1).2.2.1 s).continuousOn
  have b : ContinuousOn (u s) (GLs n) := (h3 s).continuousOn
  have c : ∀ p : Ix n, ContinuousOn (Rt (hm p) u s) (GLs n) := fun p =>
    ((GlobalTheory.CompanionTheory.WaveSpd.sm_calculus (Rt (hm p) u) (h2 (hm p))).2.2.1 s).continuousOn
  unfold dens
  refine ((a.norm.pow 2).add (continuousOn_const.mul ?_)).add (b.norm.pow 2)
  exact continuousOn_finsetSum _ (fun p _ => (c p).norm.pow 2)

theorem weighted_zero [NormedSpace ℝ W] (ℓ : Mat n → ℝ) (hℓ : ContinuousOn ℓ (GLs n))
    (χ : ℝ → ℝ) (hχ : ∀ x, 1 ≤ x → χ x = 0) (u : ℝ → Mat n → W) (r : ℝ)
    (h0 : ∀ y ∈ GLs n, ℓ y < r + 1 → u 0 y = 0) (h1 : ∀ y ∈ GLs n, dt u 0 y = 0)
    (y : Mat n) (hy : y ∈ GLs n) : χ (ℓ y - r) * dens u 0 y = 0 := by
  by_cases hc : 1 ≤ ℓ y - r
  · rw [hχ _ hc, zero_mul]
  · have hlt : ℓ y < r + 1 := by linarith
    have hnh : GLs n ∈ nhds y := isOpen_GLs.mem_nhds hy
    have hca : ContinuousAt ℓ y := hℓ.continuousAt hnh
    have hev : u 0 =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [hca.eventually_lt continuousAt_const hlt, hnh] with z hz hzG
      exact h0 z hzG hz
    have hR : ∀ p : Ix n, Rt (hm p) u 0 y = 0 := fun p => by
      change fderiv ℝ (u 0) y (y * hm p) = 0
      rw [hev.fderiv_eq]
      simp
    have hd : dens u 0 y = 0 := by
      unfold dens
      simp [hR, h1 y hy, h0 y hy hlt]
    rw [hd, mul_zero]

theorem energy_vanish : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (ℓ : Mat n → ℝ), ContDiffOn ℝ ∞ ℓ (GLs n) → (∀ R : ℝ, IsCompact {y : G n | ℓ y.val ≤ R}) →
    ∀ (C₁ : ℝ), 0 ≤ C₁ → (∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ ℓ y (y * hm p)| ≤ C₁) →
    (∀ Ψ : Mat n → ℝ, ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < ℓ y → Ψ y = 0) →
      ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0) →
    ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → (∀ x, deriv χ x ≤ 0) → (∀ x, 0 ≤ χ x) →
    (∀ x, 1 ≤ x → χ x = 0) → ∀ (u : ℝ → Mat n → W), Sm u → ∀ (A : W →L[ℝ] W),
    (∀ s, ∀ y ∈ GLs n, dt (dt u) s y =
      (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + A (u s y)) →
    ∀ (C : ℝ), C₁ * (1 + Fintype.card (Ix n)) ≤ C → ∀ (r : ℝ), (∀ x, x ≤ 0 → χ x = 1) →
    (∀ y ∈ GLs n, ℓ y < r + 1 → u 0 y = 0) → (∀ y ∈ GLs n, dt u 0 y = 0) →
    ∀ t : ℝ, 0 ≤ t → ∀ y ∈ GLs n, ℓ y + C * t ≤ r → u t y = 0 := by
  intro n W _ _ _ _ μ _ ℓ hℓ hcpt C₁ hC₁ hb hdiv χ hχs hχd hχ0 hχ1 u hu A hwave C hC r hχ2 h0 h1
    t ht y hy hyt
  obtain ⟨K, hK⟩ := GlobalTheory.T.energy_estimate_of_length_function μ ℓ hℓ hcpt C₁ hC₁ hb hdiv χ hχs hχd hχ0 hχ1 u hu A hwave C hC r
  choose e' he' hle using hK
  have hℓc : ContinuousOn ℓ (GLs n) := hℓ.continuousOn
  have hnn : ∀ (s : ℝ) (z : G n), 0 ≤ χ (ℓ z.val + C * s - r) * dens u s z.val := fun s z =>
    mul_nonneg (hχ0 _) (dens_nonneg u s _)
  have hzero : (∫ z : G n, χ (ℓ z.val + C * t - r) * dens u t z.val ∂μ) = 0 := by
    refine GlobalTheory.CompanionTheory.WaveSpd.GronwallZero.eq_zero_of_deriv_le_mul
      (fun s => ∫ z : G n, χ (ℓ z.val + C * s - r) * dens u s z.val ∂μ) e' K t ht he' hle
      (fun s => integral_nonneg (hnn s)) ?_
    have : ∀ z : G n, χ (ℓ z.val + C * 0 - r) * dens u 0 z.val = 0 := fun z => by
      have := weighted_zero ℓ hℓc χ hχ1 u r h0 h1 z.val (val_mem_GLs z)
      simpa using this
    simp only [this, integral_zero]
  have hval : Continuous (fun z : G n => z.val) := Units.continuous_val
  have hcont : Continuous (fun z : G n => χ (ℓ z.val + C * t - r) * dens u t z.val) := by
    have c1 : Continuous (fun z : G n => ℓ z.val) := hℓc.comp_continuous hval val_mem_GLs
    have c2 : Continuous (fun z : G n => dens u t z.val) :=
      (dens_continuousOn u hu t).comp_continuous hval val_mem_GLs
    exact (hχs.continuous.comp ((c1.add continuous_const).sub continuous_const)).mul c2
  have hsupp : HasCompactSupport (fun z : G n => χ (ℓ z.val + C * t - r) * dens u t z.val) := by
    refine HasCompactSupport.intro (hcpt (1 + r - C * t)) ?_
    intro z hz
    have hz' : 1 + r - C * t < ℓ z.val := not_le.1 hz
    have : χ (ℓ z.val + C * t - r) = 0 := hχ1 _ (by linarith)
    simp only [this, zero_mul]
  let yu : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero y hy
  have hyu : yu.val = y := rfl
  have hat : χ (ℓ y + C * t - r) * dens u t y = 0 := by
    by_contra hne
    have := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (x := yu) hsupp
      (fun z => hnn t z) (by simpa [hyu] using hne)
    exact this.ne' hzero
  rw [hχ2 _ (by linarith), one_mul] at hat
  have hsq := sq_le_dens u t y
  rw [hat] at hsq
  have : ‖u t y‖ ^ 2 = 0 := le_antisymm hsq (by positivity)
  simpa using this

end GlobalTheory.CompanionTheory.WaveSpd.Vanish
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

theorem fewEq : FewEqSt := by
  have gen := GlobalTheory.T.cocycle_units_trivialize_modulo_ideal
  have data := GlobalTheory.T.trivial_pullback_gives_unit_cocycle
  have mingens := GlobalTheory.T.minimal_generators_local_ideal
  have flat := GlobalTheory.T.minimal_generators_base_change
  have dep := GlobalTheory.T.dependency_statement
  have fibre := GlobalTheory.T.first_cohomology_rank_bound_at_closed_point
  have cocycle := GlobalTheory.T.unit_cocycle_lift_modulo_maximal
  have finish := GlobalTheory.T.unit_cocycle_lift_minimal_generators
  intro R _ _ _ X s n hsm hpr hF M hM I hI hJ
  have hIm : I ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  obtain ⟨r, t, ht, hmin⟩ := mingens R I
  have hsep : X.IsSeparated := by
    have : IsSeparated (s ≫ terminal.from (Sp R)) := inferInstance
    rw [Subsingleton.elim (s ≫ terminal.from (Sp R)) (terminal.from X)] at this
    exact ⟨this⟩
  haveI : Flat s := inferInstance

  let A := {q : M.ι × X.Opens // IsAffineOpen q.2 ∧ q.2 ≤ M.U q.1}
  let V : A → X.Opens := fun a => a.1.2
  let j : A → M.ι := fun a => a.1.1
  have hj : ∀ a, V a ≤ M.U (j a) := fun a => a.2.2
  have hA : ∀ a, IsAffineOpen (V a) := fun a => a.2.1
  have hAA : ∀ a b, IsAffineOpen (V a ⊓ V b) := fun a b => (hA a).inf (hA b)
  have hAAA : ∀ a b d, IsAffineOpen (V a ⊓ V b ⊓ V d) := fun a b d => (hAA a b).inf (hA d)
  have hV : ⨆ a, V a = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.exists_chart M hM x
    obtain ⟨W, hW, hxW, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(i, W), hW, hle⟩, hxW⟩
  have hsq : I * I ≤ IsLocalRing.maximalIdeal R * I := Ideal.mul_mono_left hIm
  suffices hrn : r ≤ n by
    refine ⟨fun i => if h : i.1 < r then t ⟨i.1, h⟩ else 0, le_antisymm ?_ ?_⟩
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases h : i.1 < r
      · simp only [h, dif_pos]
        rw [← ht]
        exact Ideal.subset_span ⟨_, rfl⟩
      · simp only [h, dif_neg, not_false_eq_true]
        exact zero_mem _
    · rw [← ht, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      refine Ideal.subset_span ⟨⟨i.1, i.2.trans_le hrn⟩, ?_⟩
      simp
  by_contra hrn
  obtain ⟨u, z, hz, hc⟩ := data R X s I M hM A V j hj hA hAA ((hJ I).2 le_rfl)

  let w : ∀ a, Γ(X, V a) := fun a => z a * (2 - u a * z a)
  have hw : ∀ a, u a * w a - 1 ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a) := fun a => by
    have h2 : (u a * z a - 1) * (u a * z a - 1) ∈ ext s (IsLocalRing.maximalIdeal R * I) (V a) := by
      refine Ideal.map_mono hsq ?_
      rw [Ideal.map_mul]
      exact Ideal.mul_mem_mul (hz a) (hz a)
    have : u a * w a - 1 = -((u a * z a - 1) * (u a * z a - 1)) := by simp only [w]; ring
    rw [this]
    exact neg_mem h2
  obtain ⟨b, hb1, hb2⟩ := cocycle R X s _ I r t ht hIm M hM A V j hj u w hw hc
  have hb3 : ∀ i a c d, rs X (le₁₂ V a c d) (b i a c) + rs X (le₂₃ V a c d) (b i c d) -
        rs X (le₁₃ V a c d) (b i a d) ∈ ext s (IsLocalRing.maximalIdeal R) (V a ⊓ V c ⊓ V d) := fun i a c d =>
    flat R _ _ (GlobalTheory.SmallExtLift.cst_flat s (hAAA a c d)) r t I ht hmin _ (hb1 a c d) i
  obtain ⟨e, β, ⟨l, hl⟩, he⟩ := fibre dep R X s inferInstance n r (not_le.1 hrn) hF A V hV hA b hb3
  obtain ⟨J, y, z', hIJ, hy1, hy2⟩ := finish R X s I r t ht hIm hmin M A V j hj u w b e β l hw hb2 hl he
  exact hIJ ((hJ J).1 (gen R X s J M hM A V j hj hV y z' hy1 hy2))

end GlobalTheory.CompanionTheory.FewEq
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem _root_.GlobalTheory.T.twisted_action_smooth : ∀ {G M V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → ∀ (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G), Continuous s → ∀ (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n), IsSmooth (twAct ρ N θ s hs) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.twAct_isSmooth | exact GlobalTheory.CompanionTheory.BZMir.twAct_isSmooth | (intros; apply GlobalTheory.CompanionTheory.BZMir.twAct_isSmooth <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.BlockIndex

theorem sum_castLE_eq_range {h : ℕ} (d : Fin h → ℕ) (a : Fin h) :
    ∑ b : Fin a, d (Fin.castLE a.2.le b) =
      ∑ c ∈ Finset.range a, (fun c => if hc : c < h then d ⟨c, hc⟩ else 0) c := by
  rw [← Fin.sum_univ_eq_sum_range (fun c => if hc : c < h then d ⟨c, hc⟩ else 0) a]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dite_eq_left (b.2.trans a.2)] <;> rfl

theorem partial_sum_succ_le {h : ℕ} (d : Fin h → ℕ) {a b : Fin h} (hab : b < a) :
    ∑ c : Fin b, d (Fin.castLE b.2.le c) + d b ≤ ∑ c : Fin a, d (Fin.castLE a.2.le c) := by
  have hsub : Finset.range ((b : ℕ) + 1) ⊆ Finset.range a := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (show (b : ℕ) + 1 ≤ a from hab))
  have key := Finset.sum_le_sum_of_subset (f := fun c => if hc : c < h then d ⟨c, hc⟩ else 0) hsub
  rw [Finset.sum_range_succ, dite_eq_left b.2] at key
  rw [GlobalTheory.CompanionTheory.BlockIndex.sum_castLE_eq_range d b, GlobalTheory.CompanionTheory.BlockIndex.sum_castLE_eq_range d a]
  exact key

theorem stdBlocks_lt_of_lt {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {a b : Fin h} (hab : b < a)
    (x : Fin (d a)) (y : Fin (d b)) : stdBlocks d hd ⟨b, y⟩ < stdBlocks d hd ⟨a, x⟩ := by
  rw [Fin.lt_def, GlobalTheory.SmGL.stdBlocks_val,
    GlobalTheory.SmGL.stdBlocks_val]
  have h1 := GlobalTheory.CompanionTheory.BlockIndex.partial_sum_succ_le d hab
  have h2 := y.2
  omega

theorem blockIdx_monotone : ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), Monotone (Zl.JC.blockIdx d hd) := by
  intro h N d hd i j hij
  by_contra H
  rw [not_le] at H
  have H' : ((GlobalTheory.SmGL.stdBlocks d hd).symm j).1 <
      ((GlobalTheory.SmGL.stdBlocks d hd).symm i).1 := H
  have key := GlobalTheory.CompanionTheory.BlockIndex.stdBlocks_lt_of_lt d hd H'
    ((GlobalTheory.SmGL.stdBlocks d hd).symm i).2
    ((GlobalTheory.SmGL.stdBlocks d hd).symm j).2
  simp only [Sigma.eta, Equiv.apply_symm_apply] at key
  exact absurd hij (not_le.mpr key)

end GlobalTheory.CompanionTheory.BlockIndex
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.LeviBlockIdx

theorem leviEmb_mem_levi_blockIdx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (g : Levi k (fun a => Fin (d a))), leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd) := by
  intro k _ _ _ _ h N d hd g
  rw [GroundTheory.Automorphic.Parabolic.mem_levi]
  intro i j hij
  obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective j
  have hab : a ≠ b := by
    simpa [Zl.JC.blockIdx] using hij
  exact leviEmb_apply_ne k (stdBlocks d hd) g hab x y

end GlobalTheory.CompanionTheory.LeviBlockIdx
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.levi_embedding_mem_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (g : Levi k (fun a => Fin (d a))), leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd) := by
  intro k _ _ _ _ h N d hd g
  rw [GroundTheory.Automorphic.Parabolic.mem_levi]
  intro i j hij
  obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective j
  have hab : a ≠ b := by
    simpa [Zl.JC.blockIdx] using hij
  exact leviEmb_apply_ne k (stdBlocks d hd) g hab x y
end
