module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle047
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanGramFiberContinuousDensity
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PrimitiveVectorQuadraticLevelMeasure
public import GroundTheory.GlobalFields.Bundle001
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Mathlib.MeasureTheory.Measure.Haar.DistribChar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulA
public import GroundTheory.GlobalFields.TateThesis.AdeleScaling
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle006
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle053
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle054
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasurable
public import GroundTheory.GlobalFields.TateThesis.Bundle006

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FstarPer

theorem oh_mul {F : Type} [Field F] [NumberField F] {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) :
    x * y ∈ Oh F :=
  fun v => mul_mem (hx v) (hy v)

theorem continuous_qf {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (h : A F) (B : Matrix ι ι (A F)) : Continuous (qf h B) := by
  unfold qf
  exact continuous_const.mul (continuous_id.dotProduct ((continuous_const (y := B)).matrix_mulVec continuous_id))

theorem fstar_periodic : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, opU ψ (hf F) (Bf B) ((N : A F) * x) φ = φ ∧ ∀ y : A F, fstar ψ (hf F) (Bf B) (muF B lf) φ (y + (N : A F) * x) = fstar ψ (hf F) (Bf B) (muF B lf) φ y := by
  intro F _ _ _ _ lf _ _ ψ hψ ι _ _ M B ρ P _ φ hφ
  have hK : IsCompact (qf (hf F) (Bf B) '' tsupport φ) :=
    IsCompact.image hφ.2 (continuous_qf _ _)
  obtain ⟨N, hN, hNK⟩ := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.2.2.1 _ hK
  have htriv := ((GlobalTheory.T.standard_adelic_character F).2 ψ hψ).2.1
  have key : ∀ x ∈ Oh F, opU ψ (hf F) (Bf B) ((N : A F) * x) φ = φ := by
    intro x hx
    funext u
    by_cases hu : u ∈ tsupport φ
    · have h1 := hNK _ (Set.mem_image_of_mem _ hu)
      have h2 : (N : A F) * x * qf (hf F) (Bf B) u ∈ Oh F := by
        have h3 := oh_mul hx h1
        have h4 : (N : A F) * x * qf (hf F) (Bf B) u = x * ((N : A F) * qf (hf F) (Bf B) u) := by
          ring
        rwa [h4]
      simp [opU, htriv _ h2]
    · have h0 : φ u = 0 := image_eq_zero_of_notMem_tsupport hu
      simp [opU, h0]
  refine ⟨N, hN, fun x hx => ⟨key x hx, fun y => ?_⟩⟩
  unfold fstar
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have h5 := congrFun (key x hx) u
  simp only [opU] at h5 ⊢
  rw [add_mul, AddChar.map_add_eq_mul, mul_assoc, h5]

end GlobalTheory.CompanionTheory.SW.FstarPer
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral

theorem thTerm_zero {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ) (φ : (ι → A F) → ℂ)
    (τ : InfinitePlace F → ℂ) : thTerm B ρ P gf gi φ τ 0 = φ 0 := by
  have h1 : (fun j : ι => algebraMap F (A F) ((0 : ι → F) j)) = 0 := by
    funext j; simp
  have h2 : ∀ w, (fun j : ι => ρ w ((0 : ι → F) j)) = 0 := by
    intro w; funext j; simp
  simp only [thTerm, gauss, h1, h2, mulVec_zero]
  simp

theorem main : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) (gf : Ω → Matrix ι ι (A F)) (gi : Ω → InfinitePlace F → Matrix ι ι ℝ), CountData M B ρ Pr gf gi → ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → Integrable (fun ω => theta B ρ P (gf ω) (gi ω) φ τ) Pr ∧ ENNReal.ofReal ‖(∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0‖ ≤ ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr := by
  intro F _ _ _ _ lf _ _ ψ _ ι _ _ M B ρ P hQ Ω _ Pr gf gi hC φ τ hφ hτ
  haveI : IsProbabilityMeasure Pr := hC.1
  have horth : ∀ ω, IsOrth B ρ (gf ω) (gi ω) := hC.2.2.2.1
  haveI : Countable F :=
    Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective
  obtain ⟨w0, -, h0⟩ := Finset.exists_min_image Finset.univ (fun w => (τ w).im) Finset.univ_nonempty
  obtain ⟨w1, -, h1⟩ := Finset.exists_max_image Finset.univ (fun w => (τ w).im) Finset.univ_nonempty
  have ht : 0 < (τ w0).im := hτ w0
  have hs : 0 < (τ w1).im := hτ w1
  obtain ⟨C, hCb⟩ := GlobalTheory.T.weighted_theta_average_le_of_countData F ι M B ρ P hQ Ω Pr gf gi hC φ hφ
    ((τ w0).im / (τ w1).im) (τ w0).im (div_pos ht hs) ht
  obtain ⟨hmeas, hbd⟩ := hCb τ (fun w => h0 w (Finset.mem_univ w)) (by
    intro v w
    have hw : (τ w).im ≤ (τ w1).im := h1 w (Finset.mem_univ w)
    have hv : (τ w0).im ≤ (τ v).im := h0 v (Finset.mem_univ v)
    calc (τ w0).im / (τ w1).im * (τ w).im ≤ (τ w0).im / (τ w1).im * (τ w1).im :=
          mul_le_mul_of_nonneg_left hw (div_pos ht hs).le
      _ = (τ w0).im := div_mul_cancel₀ _ hs.ne'
      _ ≤ (τ v).im := hv)
  have hwt : 0 < wt M τ := Finset.prod_pos fun w _ => pow_pos (Real.sqrt_pos.2 (hτ w)) M
  have hfin : (∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr) ≠ ∞ := by
    intro h
    rw [h, ENNReal.mul_top (by simpa using hwt)] at hbd
    simp at hbd
  have hsum : ∀ ω, Summable (thTerm B ρ P (gf ω) (gi ω) φ τ) := fun ω =>
    ((GlobalTheory.T.theta_series_summable F ι M B ρ P hQ (gf ω) (gi ω) (horth ω) τ hτ).1 φ hφ).of_norm
  have hsub : ∀ ω, Summable fun x : {x : ι → F // x ≠ 0} => thTerm B ρ P (gf ω) (gi ω) φ τ x.1 :=
    fun ω => (hsum ω).subtype _
  set g : Ω → ℂ := fun ω => ∑' x : {x : ι → F // x ≠ 0}, thTerm B ρ P (gf ω) (gi ω) φ τ x.1 with hg
  have hsplit : ∀ ω, theta B ρ P (gf ω) (gi ω) φ τ = φ 0 + g ω := by
    intro ω
    have h := (hsum ω).tsum_subtype_add_tsum_subtype_compl ({0} : Set (ι → F))
    rw [tsum_singleton, thTerm_zero] at h
    exact h.symm
  have hgm : Measurable g :=
    measurable_of_tendsto_metrizable' Filter.atTop
      (f := fun (s : Finset {x : ι → F // x ≠ 0}) ω => ∑ x ∈ s, thTerm B ρ P (gf ω) (gi ω) φ τ x.1)
      (fun s => Finset.measurable_sum _ fun x _ => hmeas x.1)
      (tendsto_pi_nhds.2 fun ω => (hsub ω).hasSum)
  have hgI : ∫⁻ ω, ‖g ω‖ₑ ∂Pr ≤
      ∫⁻ ω, ∑' x : {x : ι → F // x ≠ 0}, ‖thTerm B ρ P (gf ω) (gi ω) φ τ x.1‖ₑ ∂Pr :=
    lintegral_mono fun ω => enorm_tsum_le_tsum_enorm
  have hgint : Integrable g Pr := ⟨hgm.aestronglyMeasurable, lt_of_le_of_lt hgI hfin.lt_top⟩
  have hth : (fun ω => theta B ρ P (gf ω) (gi ω) φ τ) = fun ω => φ 0 + g ω := funext hsplit
  refine ⟨by rw [hth]; exact (integrable_const _).add hgint, ?_⟩
  have hint : (∫ ω, theta B ρ P (gf ω) (gi ω) φ τ ∂Pr) - φ 0 = ∫ ω, g ω ∂Pr := by
    rw [hth, integral_add (integrable_const _) hgint]
    simp
  rw [hint, ofReal_norm_eq_enorm]
  exact (enorm_integral_le_lintegral_enorm g).trans hgI

end GlobalTheory.CompanionTheory.SW.Core.ThetaIntegral
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.archimedean_gram_fiber_continuous_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ 1)) m, μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Ainf F) σ J 1 μ ν m → ∀ φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ, Continuous φ → (∀ X, 0 ≤ φ X) → RapidDecay b (fun X => (φ X : ℂ)) → ∀ D : HermR (Ainf F) σ 1 → ℝ, Continuous D → (∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (φ X) ∂μ = ∫⁻ S in U, ENNReal.ofReal (D S) ∂ν) → ∀ S : HermR (Ainf F) σ 1, IsUnit (S : Matrix (Fin 1) (Fin 1) (Ainf F ⊗[F] E)).det → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m S) = ENNReal.ofReal (D S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocGauss.fibre_rapid_eq_density | exact GlobalTheory.CompanionTheory.SW.LocGauss.fibre_rapid_eq_density | (intros; apply GlobalTheory.CompanionTheory.SW.LocGauss.fibre_rapid_eq_density <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ S : HermR R σ n, IsLocallyFiniteMeasure (m S) ∧ ∀ U : Set (Fin n → Fin M → R ⊗[F] E), IsOpen U → (∃ X ∈ U, gramR R σ J X = S ∧ IsUnit (gramR R σ J X).det) → m S U ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin | exact GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin | (intros; apply GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.primitive_vector_quadratic_level_measure : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → Valued.v (2 : Fv F v) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)), B.IsSymm → (∀ i j, B i j ∈ v.adicCompletionIntegers F) → Valued.v B.det = 1 → ∀ x₀ : ι → Fv F v, (∀ i, x₀ i ∈ v.adicCompletionIntegers F) → (∃ i, Valued.v (x₀ i) = 1) → ∀ A : Set (Fv F v), MeasurableSet A → (Measure.pi fun _ : ι => lam) {x | (∀ i, Valued.v (x i - x₀ i) < 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ^ (Fintype.card ι - 1) * lam (A ∩ {s | Valued.v (s - (2 : Fv F v)⁻¹ * (x₀ ⬝ᵥ (B *ᵥ x₀))) < 1}) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Hensel.measure_residue_class | exact GlobalTheory.CompanionTheory.SW.Hensel.measure_residue_class | (intros; apply GlobalTheory.CompanionTheory.SW.Hensel.measure_residue_class <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ProdFormula

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix Pointwise

section Infinite

variable {F : Type} [Field F] [NumberField F]

theorem map_mul_left_infinite {m : MeasurableSpace (InfiniteAdeleRing F)}
    (hm : @BorelSpace _ _ m) (b : (InfiniteAdeleRing F)ˣ) (μ : Measure (InfiniteAdeleRing F))
    (hμ : μ.IsAddHaarMeasure) :
    μ.map (fun y => (b : InfiniteAdeleRing F) * y) =
      ENNReal.ofReal ‖((b⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)‖ • μ := by
  obtain rfl : m = GroundTheory.Global.measurableSpace_infiniteAdeleRing F :=
    hm.measurable_eq.trans (GroundTheory.Global.borelSpace_infiniteAdeleRing (K := F)).measurable_eq.symm
  have h := Measure.isAddLeftInvariant_eq_smul μ (GroundTheory.Global.infiniteAdeleMeasure F)
  rw [h, Measure.map_smul, GroundTheory.Global.map_mul_left_infiniteAdeleMeasure, smul_comm]
  exact (continuous_const_mul (b : InfiniteAdeleRing F)).measurable.aemeasurable

theorem norm_algebraMap_infinite (a : F) :
    ‖algebraMap F (InfiniteAdeleRing F) a‖ = ∏ w : InfinitePlace F, w a ^ w.mult := by
  rw [InfiniteAdeleRing.norm_def]
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 1
  rw [InfiniteAdeleRing.algebraMap_apply]
  exact AbsoluteValue.Completion.norm_coe (WithAbs.toAbs w.1 a)

end Infinite

section Finite

open HeckeCharacterZeroLocus.SiegelWeilU

variable {F : Type} [Field F] [NumberField F]

theorem distribHaarChar_eq_nnnorm (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (ha : a ≠ 0) :
    distribHaarChar (Fv F v) (Units.mk0 a ha) = ‖a‖₊ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  let ϖ : Fv F v := (π : Fv F v)
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hva : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  set k : ℤ := WithZero.log (Valued.v a) with hk
  have hu0 : a * ϖ ^ k ≠ 0 := mul_ne_zero ha (zpow_ne_zero _ hϖ0)
  have hu : Valued.v (a * ϖ ^ k) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, ← WithZero.exp_log hva, ← WithZero.exp_zsmul, ← WithZero.exp_add,
      ← hk, ← WithZero.exp_zero]
    congr 1
    simp
  have hU : Units.mk0 (a * ϖ ^ k) hu0 = Units.mk0 a ha * (Units.mk0 ϖ hϖ0) ^ k := by
    ext; simp [Units.val_zpow_eq_zpow_val]
  have h1 := PI.UnitaryGroupMassFormula.LocJacTyp.BM.dhc_unit v _ hu hu0
  rw [hU, map_mul, map_zpow, PI.UnitaryGroupMassFormula.LocJacTyp.BM.dhc_unif v ϖ hϖ hϖ0, inv_zpow] at h1
  have hq : ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ k ≠ 0 :=
    zpow_ne_zero _ (by exact_mod_cast PI.UnitaryGroupMassFormula.LocJacTyp.BM.q_ne_zero v)
  have h2 : distribHaarChar (Fv F v) (Units.mk0 a ha) = ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ k :=
    (mul_inv_eq_one₀ hq).1 h1
  rw [h2]
  apply NNReal.coe_injective
  rw [coe_nnnorm, ← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow v ha, ← hk]
  simp

theorem map_mul_left_finite (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (ha : a ≠ 0)
    (μ : Measure (Fv F v)) (hμ : μ.IsAddHaarMeasure) :
    μ.map (fun x => a * x) = (‖a‖₊)⁻¹ • μ := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  haveI : μ.Regular := inferInstance
  ext S hS
  rw [Measure.map_apply (continuous_const_mul _).measurable hS, Measure.smul_apply]
  have h := distribHaarChar_mul μ (Units.mk0 a ha)⁻¹ S
  have e : (fun x => a * x) ⁻¹' S = (Units.mk0 a ha)⁻¹ • S :=
    Set.preimage_smul (Units.mk0 a ha) S
  rw [e, ← h, map_inv, distribHaarChar_eq_nnnorm]
  rfl

end Finite

section Main

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW

theorem unitProd_scalar : ∀ (F : Type) [Field F] [NumberField F] (a : F), a ≠ 0 →
    ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧
      (∀ μ : Measure (Ainf F), μ.IsAddHaarMeasure →
        μ.map (fun x => algebraMap F (Ainf F) a * x) = cinf • μ) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), ∀ μ : Measure (Fv F v), μ.IsAddHaarMeasure →
        μ.map (fun x => algebraMap F (Fv F v) a * x) = c v • μ := by
  intro F _ _ a ha
  have hA : 0 < ∏ w : InfinitePlace F, w a ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.2 ha) _
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖algebraMap F (Fv F v) a‖).Finite :=
    (FinitePlace.hasFiniteMulSupport ha).preimage
      (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn
  have hprod : (∏ w : InfinitePlace F, w a ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (Fv F v) a‖ = 1 := by
    rw [← prod_abs_eq_one ha, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    rfl
  refine ⟨((∏ w : InfinitePlace F, w a ^ w.mult)⁻¹).toNNReal,
    fun v => (‖algebraMap F (Fv F v) a‖₊)⁻¹, ⟨?_, ?_⟩, ?_, ?_⟩
  · filter_upwards [hfin.eventually_cofinite_notMem] with v hv
    have h1 : ‖algebraMap F (Fv F v) a‖ = 1 := by simpa using hv
    have h2 : ‖algebraMap F (Fv F v) a‖₊ = 1 := NNReal.coe_injective h1
    rw [h2, inv_one]
  · apply NNReal.coe_injective
    have e : ((∏ᶠ v : HeightOneSpectrum (𝓞 F), (‖algebraMap F (Fv F v) a‖₊)⁻¹ : ℝ≥0) : ℝ) =
        (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (Fv F v) a‖)⁻¹ := by
      rw [finprod_inv_distrib]
      rw [NNReal.coe_inv]
      congr 1
      exact NNReal.toRealHom.map_finprod_of_injective NNReal.coe_injective _
    rw [NNReal.coe_mul, e, NNReal.coe_one, Real.coe_toNNReal _ (inv_pos.2 hA).le, ← mul_inv, hprod, inv_one]
  · intro μ hμ
    have hb : (((Units.map (algebraMap F (Ainf F)).toMonoidHom (Units.mk0 a ha))⁻¹ : (Ainf F)ˣ) : Ainf F) =
        algebraMap F (Ainf F) a⁻¹ := by
      simp
    have h := map_mul_left_infinite (F := F) (m := measAinf) ⟨rfl⟩
      (Units.map (algebraMap F (Ainf F)).toMonoidHom (Units.mk0 a ha)) μ hμ
    rw [hb, norm_algebraMap_infinite] at h
    have e : ∏ w : InfinitePlace F, w a⁻¹ ^ w.mult = (∏ w : InfinitePlace F, w a ^ w.mult)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun w _ => by rw [map_inv₀, inv_pow]
    rw [e] at h
    exact h
  · intro v μ hμ
    exact map_mul_left_finite v _ ((map_ne_zero _).2 ha) μ hμ

end Main

end GlobalTheory.CompanionTheory.SW.ProdFormula
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem Bf_mulVec_toA {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (y : ι → F) : Bf B *ᵥ toA y = toA (B *ᵥ y) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap F (A F)) B y i).symm

theorem trace_int_of_basis {F : Type} [Field F] [NumberField F]
    (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ) (c : F)
    (h : ∀ v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * c) = m) (r : 𝓞 F) :
    ∃ n : ℤ, Algebra.trace ℚ F ((N : F) * c * (r : F)) = n := by
  choose m hm using h
  have hr : (r : F) = ∑ v, ((b.repr r v : ℤ) : F) * (b v : F) := by
    conv_lhs => rw [← b.sum_repr r]

    simp [map_sum]
  refine ⟨∑ v, b.repr r v * m v, ?_⟩

  rw [hr, Finset.mul_sum, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  have e : (N : F) * c * (((b.repr r v : ℤ) : F) * (b v : F)) =
      (((b.repr r v : ℤ) : ℚ) * (N : ℚ)) • ((b v : F) * c) := by
    rw [Algebra.smul_def]
    simp only [eq_ratCast, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast]
    ring
  rw [e, map_smul, smul_eq_mul, mul_assoc, hm v]

theorem toA_mem_perp_latN_iff : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ), IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), 0 < N → ∀ y : ι → F, toA y ∈ perp (chiB ψ (Bf B)) (latN F ι N : Set (ι → A F)) ↔ ∀ i v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m := by
  intro F _ _ ψ hψ ι _ _ B b N _ y
  obtain ⟨-, hall⟩ := GlobalTheory.T.standard_adelic_character F
  obtain ⟨-, -, hchar⟩ := hall ψ hψ
  have hBy := Bf_mulVec_toA B y
  constructor
  · intro h i v
    have h1 : ∀ x ∈ Oh F, ψ (algebraMap F (A F) ((N : F) * (B *ᵥ y) i) * x) = 1 := by
      intro x hx
      have hmem : (Pi.single i ((N : A F) * x) : ι → A F) ∈ latN F ι N := by
        refine fun j => ?_
        by_cases hj : j = i
        · subst hj
          exact ⟨x, hx, by simp⟩
        · exact ⟨0, oh_zero, by simp [Pi.single_eq_of_ne hj]⟩
      have h2 : ψ ((Pi.single i ((N : A F) * x) : ι → A F) ⬝ᵥ (Bf B *ᵥ toA y)) = 1 := h _ hmem
      rw [hBy, single_dotProduct] at h2
      rw [← h2, map_mul (algebraMap F (A F)), map_natCast (algebraMap F (A F))]
      congr 1
      simp only [toA]
      ring
    obtain ⟨n, hn⟩ := (hchar _).mp h1 (b v)
    refine ⟨n, ?_⟩
    rw [← hn]
    have e : (N : F) * (B *ᵥ y) i * (b v : F) = (N : ℚ) • ((b v : F) * (B *ᵥ y) i) := by
      rw [Algebra.smul_def]
      push_cast
      ring
    rw [e, map_smul, smul_eq_mul]
  · intro h x hx
    have h1 : ∀ i, ∀ x ∈ Oh F, ψ (algebraMap F (A F) ((N : F) * (B *ᵥ y) i) * x) = 1 :=
      fun i => (hchar _).mpr (trace_int_of_basis b N _ (h i))
    show ψ (x ⬝ᵥ (Bf B *ᵥ toA y)) = 1
    rw [hBy, dotProduct]
    have h2 : ∀ s : Finset ι, ψ (∑ i ∈ s, x i * toA (B *ᵥ y) i) = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, AddChar.map_add_eq_mul, ih, mul_one]
        obtain ⟨x', hx', e⟩ := hx i
        rw [e, ← h1 i x' hx', map_mul (algebraMap F (A F)), map_natCast (algebraMap F (A F))]
        congr 1
        simp only [toA]
        ring
    exact h2 Finset.univ

end GlobalTheory.CompanionTheory.SW.ThW
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.coordK_map_mul_eq_smul_continuous_modulus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ) (J₁ : Matrix (Fin N) (Fin N) E), IsHermND σ J₁ → ∀ t : F, t ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₁ : HermR R σ 1 → Measure (Fin 1 → Fin N → R ⊗[F] E), IsGramFib R σ J₁ 1 (coordW R b lam 1 N) (coordHerm R σ b lam 1) m₁ → ∃ κ₁ cm : Rˣ → ℝ≥0, Continuous κ₁ ∧ κ₁ 1 = 1 ∧ (∀ u : Rˣ, m₁ (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) = κ₁ u • (m₁ (hermScal R σ (algebraMap F R t))).map (scl ((u : R) ⊗ₜ[F] (1 : E)))) ∧ Continuous cm ∧ (∀ u : Rˣ, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = cm u • coordK R b lam) ∧ ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → cm 1 = c := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibre_scale_modulus_length_one | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibre_scale_modulus_length_one | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibre_scale_modulus_length_one <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.nonarchimedean_selfdual_measure_pi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (k : Measure (Fv F v)), SelfDual k (fun s t => psiV F ψ v (s * t)) → ∀ (ι : Type) [Fintype ι], SelfDual (Measure.pi fun _ : ι => k) (fun x y => psiV F ψ v (x ⬝ᵥ y)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiV.selfDual_pi_v | exact GlobalTheory.CompanionTheory.SW.PiV.selfDual_pi_v | (intros; apply GlobalTheory.CompanionTheory.SW.PiV.selfDual_pi_v <;> assumption)
end
