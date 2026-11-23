module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqThetaPartNondegenerate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle452
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle040
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle027
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle055
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle651
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBoundedAlmostAll
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle051
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle071
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle021
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HaarMeasureNonunitsNull
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle013
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle672
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle056
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle673
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle511
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSiegelWeilMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle490
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle676
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle039

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeMass

theorem lintegral_close {R : Type} [MeasurableSpace R] (ν : Measure R) (G : R → ℝ≥0∞) {S N : Set R}
    (hS : MeasurableSet S) (hfin : ν S ≠ ⊤) (hN : ν N = 0) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ s ∈ S, s ∉ N → G s ≠ ⊤ ∧ |(G s).toReal - 1| ≤ δ) :
    |(∫⁻ s in S, G s ∂ν).toReal - (ν S).toReal| ≤ δ * (ν S).toReal := by
  have hae : ∀ᵐ s ∂(ν.restrict S), G s ≠ ⊤ ∧ |(G s).toReal - 1| ≤ δ := by
    rw [ae_restrict_iff' hS]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with s hs hsS
    exact h s hsS hs
  have hup : ∫⁻ s in S, G s ∂ν ≤ ENNReal.ofReal (1 + δ) * ν S := by
    rw [← setLIntegral_const]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with s hs
    rw [← ENNReal.ofReal_toReal hs.1]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 hs.2).2])
  have hlo : ENNReal.ofReal (1 - δ) * ν S ≤ ∫⁻ s in S, G s ∂ν := by
    rw [← setLIntegral_const]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with s hs
    rw [← ENNReal.ofReal_toReal hs.1]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.1 hs.2).1])
  have hfinU : ENNReal.ofReal (1 + δ) * ν S ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hup' : (∫⁻ s in S, G s ∂ν).toReal ≤ (1 + δ) * (ν S).toReal := by
    have := ENNReal.toReal_mono hfinU hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  have hlo' : (1 - δ) * (ν S).toReal ≤ (∫⁻ s in S, G s ∂ν).toReal := by
    have := ENNReal.toReal_mono (ne_top_of_le_ne_top hfinU hup) hlo
    rw [ENNReal.toReal_mul] at this
    refine le_trans ?_ this
    refine mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  rw [abs_le]
  constructor <;> nlinarith

theorem density_close {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (hM : 3 ≤ M) {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (lv : Measure (Fv F v)) (hlv : IsStdV v lv)
    (mv : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (hmv : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lv 1 M) (coordHerm (Fv F v) σ b lv 1) mv)
    {x δ : ℝ} (hδ : 0 ≤ δ)
    (hB : ∀ s : Fv F v, s ∈ v.adicCompletionIntegers F → s ≠ 0 →
      |(mv (hermScal (Fv F v) σ s) (latV b v)).toReal - 1| ≤ δ)
    (hav : ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (0 : Fv F v), ∀ V : Set (Fv F v), MeasurableSet V → V ⊆ U →
      |(coordW (Fv F v) b lv 1 M (latV b v ∩ {X | algebraMap F (Fv F v) (1 / 2) *
        Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ V})).toReal -
        x * (lv V).toReal| ≤ ε * (lv V).toReal) :
    |x - 1| ≤ δ := by
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  haveI := hlv.1
  obtain ⟨-, hW, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hW 1 M
  obtain ⟨n1, n2⟩ := GlobalTheory.CompanionTheory.SW.NullV.null_nonunits F E σ hσ M J hJ (by omega) v
    (coordW (Fv F v) b lv 1 M) lv (hW 1 M) hlv.1
  have hmv' : IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lv 1 M)
      (lv.map (hermScal (Fv F v) σ)) mv := by
    rw [(GlobalTheory.CompanionTheory.SW.hermScal_main F E σ hσ (Fv F v) d b).2.2 lv hlv.1]
    exact hmv
  have FF := GlobalTheory.CompanionTheory.SW.isFibreFamily_length F E σ hσ M J hJ (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) _ lv
    (hW 1 M) hlv.1 n1 n2 mv hmv'
  have hqc : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0) :=
    GlobalTheory.CompanionTheory.SW.LenFib.continuous_qR (Fv F v) hσ J
  obtain ⟨hLc, hLo, -, -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b 1 M v
  have hLm : MeasurableSet (latV (M := M) (n := 1) b v) := hLo.measurableSet

  let φ : (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℝ := (latV b v).indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hLo.frontier_eq, hLc.isClosed.closure_eq]
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro hLc fun X hX => ?_
    exact Set.indicator_of_notMem hX _
  obtain ⟨hI, -⟩ := FF.2.2 φ hφc hφs (Set.subset_univ _)
  have hfinG : ∀ s : Fv F v, s ≠ 0 → mv (hermScal (Fv F v) σ s) (latV b v) ≠ ⊤ := by
    intro s hs
    have h := hI s (isUnit_iff_ne_zero.2 hs)
    rw [integrable_indicator_iff hLm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨U, hU, hUV⟩ := hav ε hε
  have hOo : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  set S : Set (Fv F v) := interior U ∩ (v.adicCompletionIntegers F : Set (Fv F v)) with hSdef
  have hSo : IsOpen S := isOpen_interior.inter hOo
  have h0S : (0 : Fv F v) ∈ S := ⟨mem_interior_iff_mem_nhds.2 hU, zero_mem _⟩
  have hSfin : lv S ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_right)
    rw [hlv.2]
    exact ENNReal.one_ne_top
  have hSpos : 0 < (lv S).toReal :=
    ENNReal.toReal_pos (hSo.measure_ne_zero lv ⟨0, h0S⟩) hSfin
  have h1 := hUV S hSo.measurableSet (Set.inter_subset_left.trans interior_subset)
  have h2 := lintegral_close lv (fun s => mv (hermScal (Fv F v) σ s) (latV b v)) hSo.measurableSet hSfin
    n1 hδ (fun s hs hs0 => ⟨hfinG s (not_not.1 hs0).ne_zero, hB s hs.2 (not_not.1 hs0).ne_zero⟩)
  rw [← GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV.fibre_mass_eq _ lv _ hqc.measurable _ _ FF hLm hSo.measurableSet] at h2
  have h3 : |x - 1| * (lv S).toReal ≤ (δ + ε) * (lv S).toReal := by
    have e : (x - 1) * (lv S).toReal = (x * (lv S).toReal -
        (coordW (Fv F v) b lv 1 M (latV b v ∩ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) ⁻¹' S)).toReal) +
        ((coordW (Fv F v) b lv 1 M (latV b v ∩ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) ⁻¹' S)).toReal -
        (lv S).toReal) := by ring
    rw [← abs_of_pos hSpos, ← abs_mul, abs_of_pos hSpos, e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_sub_comm]
    have h1' : |(coordW (Fv F v) b lv 1 M (latV b v ∩ (fun X => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.qR (Fv F v) σ J (X 0)) ⁻¹' S)).toReal -
        x * (lv S).toReal| ≤ ε * (lv S).toReal := h1
    linarith
  exact le_of_mul_le_mul_right h3 hSpos

end GlobalTheory.CompanionTheory.WeilSiegel.FreeMass

theorem GlobalTheory.CompanionTheory.WeilSiegel.FreeMass.mass_free_summable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → (∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v) < ⊤) ∧ Summable fun v => |(m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v)).toReal - 1| := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₀ d b lam hlam m hm
  have hL := fun v => GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b 1 M v
  have avg := fun v => GlobalTheory.T.local_volume_rank_one_isotropic F E σ hσ M J hJ hM h₀ d b v (lam v) (hlam v) (m v) (hm v)
    (latV b v) (hL v).1 (hL v).2.1
  refine ⟨fun v => (avg v).1, ?_⟩
  refine Summable.of_norm_bounded_eventually
    (g := fun v : HeightOneSpectrum (𝓞 F) => 2 * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2))
    ((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left 2) ?_
  filter_upwards [GlobalTheory.T.rank_one_local_density_almost_all F E σ hσ M J hJ hM d b] with v hv
  obtain ⟨m', hm'⟩ := GlobalTheory.CompanionTheory.SW.GoodMass.exists_family hσ hJ b v (lam v) (hlam v) 1
  have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := GlobalTheory.CompanionTheory.SW.GoodMass.absNorm_one_le v
  have hd := GlobalTheory.CompanionTheory.WeilSiegel.FreeMass.density_close hσ hJ hM b v (lam v) (hlam v) m' hm'
    (x := (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v)).toReal)
    (δ := 2 / (Ideal.absNorm v.asIdeal : ℝ) ^ (M - 1)) (by positivity)
    (hv (lam v) (hlam v) m' hm') (avg v).2
  rw [Real.norm_eq_abs, abs_abs]
  refine hd.trans ?_
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (pow_le_pow_right₀ hq (by omega))
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.frame_integral_theta_measure_formula : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 ν → ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ → ∀ β : HermE D r, Integrable (fun X => φ (trM X)) (GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) ∧ IfrB V ν φ β = ∫ X, φ (trM X) ∂(GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram ν 𝓕 (framesE D.sp.cm.sig V.gram β.1)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Frame.glue | exact GlobalTheory.CompanionTheory.WeilSiegel.Frame.glue | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Frame.glue <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frame_integral_eq_theta_part_nondegenerate : ∀ (D : D7) (r : ℕ) (V : HSp D) (θ : InfFam D), IsInfFam θ → ∀ ν : Measure (GA D V), ν.IsHaarMeasure →
  ∀ φ : Mx D V.rank r → ℂ, φ ∈ schwartzA θ V.rank r → GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ →
  ∀ (μH : Measure (GA D V)) (𝓕 : Set (GA D V)), μH.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μH →
  ∀ β : HermE D r, β.1.det ≠ 0 → IfrB V ν φ β = thetaPartD V μH 𝓕 φ β := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.ThetaGlue.ifrB_eq_thetaPartD | exact GlobalTheory.CompanionTheory.SiegelND.ThetaGlue.ifrB_eq_thetaPartD | (intros; apply GlobalTheory.CompanionTheory.SiegelND.ThetaGlue.ifrB_eq_thetaPartD <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf

theorem _root_.GlobalTheory.T.nondegenerate_character_cell_factorization : ∀ {D : D7} {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ (β : HermE D n), β.1.det ≠ 0 → ∀ (W : Submodule D.host.E (Fin n → D.host.E)), W ≠ ⊥ → ∃ ν : hermA D n, ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) ν.1 : Mx D n n))) ≠ 1 ∧ ∀ (γ u : G D n), γ ∈ GF D n → ∀ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) → cellKer x = W → mat u = blk4 1 ν.1 0 1 → ∃ p ∈ P D n, ∃ a : GL (Fin n) (AE D), blkA (mat p) = a.1 ∧ Matrix.GeneralLinearGroup.det a = 1 ∧ γ * u = p * γ := by
  first | exact @GlobalTheory.CompanionTheory.SwUnf.SmallCell.small_cell | exact GlobalTheory.CompanionTheory.SwUnf.SmallCell.small_cell | (intros; apply GlobalTheory.CompanionTheory.SwUnf.SmallCell.small_cell <;> assumption)
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF

theorem family_at_blockF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), hermOf R σ _ hT' ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))) ∧ fibSF σ J t m₁ m' s B₀ a κ₁ cm (hermOf R σ _ hT') = cm 1 ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D T hT hT'
  have hfr : Module.finrank F E = 2 := D.hCM.2.2.1
  have hs0 : s0 R ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = algebraMap F R t :=
    GlobalTheory.CompanionTheory.SW.StageValue.corner_half_trace_block_one R t hfr T
  have hsch := GlobalTheory.CompanionTheory.SW.StageValue.schur_block R σ t a T hT hT'
  have hmem : hermOf R σ _ hT' ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))) := by
    show s0 R _ ∈ B₀
    rw [hs0]; exact D.htB
  refine ⟨hmem, ?_⟩
  have hc : cvec R t a ((hermOf R σ _ hT' : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) = 0 := GlobalTheory.CompanionTheory.SW.StageValue.cvec_block R t a T
  unfold fibSF
  rw [Set.indicator_of_mem hmem]
  simp only [hs0, D.ha1, hsch, hc, D.hκ1, one_mul, Units.val_one, GlobalTheory.CompanionTheory.SW.StageValue.vec_one_zero]

theorem fibre_family_free_near_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₁ m', IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → ∀ s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J), Measurable s → (∀ y, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → actW R σ _ (s y) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = y) → (∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C → ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C') → ∃ B : Set (HermR R σ (n + 1)), IsOpen B ∧ hermOf R σ _ hT' ∈ B ∧ ∃ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam (n + 1) (M + 1)) (gramR R σ (blockOne (algebraMap F E t) J)) Subtype.val (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' B) ∩ {X | LinearIndependent (R ⊗[F] E) X}) (coordHerm R σ b lam (n + 1)) B fib ∧ fib (hermOf R σ _ hT') = c ^ n • ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (hermOf R σ T hT))).map (fun p => actW R σ _ (s p.1) (consTup p.2)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hT' R _ _ _ _ _ hR d b lam hlam m₁ m' hm₁ hm' c hc s hs hsec hcpt
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J hJ t ht
  obtain ⟨tu, htu⟩ : IsUnit (algebraMap F R t) := (isUnit_iff_ne_zero.mpr ht).map (algebraMap F R)
  obtain ⟨B₀, a, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.local_units_continuous_square_root R hR tu
  rw [htu] at h2 h5 h6
  obtain ⟨κ₁, cm, k1, k2, k3, k4, k5, k6⟩ := GlobalTheory.T.coordK_map_mul_eq_smul_continuous_modulus F E σ hCM (M + 1) _ hJ' t ht R hR d b lam hlam m₁ hm₁
  have D : HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm :=
    { hCM := hCM, hJ := hJ, ht := ht, hR := hR, hlam := hlam, hm₁ := hm₁, hm' := hm', hs := hs, hsec := hsec,
      hcpt := hcpt, hB₀ := h1, htB := h2, hac := h3, hoff := h4, hsq := h5, ha1 := h6, hκc := k1, hκ1 := k2,
      hscale := k3, hcmc := k4, hmod := k5 }
  obtain ⟨m₀, D₀⟩ := GlobalTheory.T.local_fibre_measure_extension_by_one F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨hs0, hacS, hcvc, hschc, -⟩ := GlobalTheory.T.continuousOn_schur_coordinates_and_isOpen_Bset F E σ M J t n R d b lam m₁ m₀ s B₀ a κ₁ cm D₀
  have hBo : IsOpen (BsetF R σ B₀ : Set (HermR R σ (n + 1))) := D.hB₀.preimage hs0
  have V := family_at_blockF F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D T hT hT'
  refine ⟨BsetF R σ B₀, hBo, V.1, fibSF σ J t m₁ m' s B₀ a κ₁ cm,
    ⟨GlobalTheory.T.fibre_measure_extension_by_one_formula F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D, ?_, ?_⟩, ?_⟩
  · intro φ hφ
    exact (GlobalTheory.T.fibre_measure_extension_integral F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ).trans
      (GlobalTheory.T.fibre_measure_extension_unique F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ).symm
  · intro φ hφ hφc hts
    have hfree : tsupport φ ⊆ {X | LinearIndependent (R ⊗[F] E) X} := hts.trans Set.inter_subset_right
    have i1 := GlobalTheory.T.fibre_measure_extension_haar F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc hfree
    have i2 := GlobalTheory.T.fibre_measure_extension_sigma_finite F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D φ hφ hφc hfree
    refine ⟨fun S hS => (i1 S hS).1, ?_⟩
    have hval := Units.continuous_val.comp_continuousOn hacS
    have hmap := hval.prodMk (hcvc.prodMk hschc)
    have hP := i2.comp hmap (fun S _ => ⟨(a _).isUnit, Set.mem_univ _, Set.mem_univ _⟩)
    have hk := NNReal.continuous_coe.comp_continuousOn
      ((D.hκc.comp_continuousOn hacS).mul ((D.hcmc.comp_continuousOn hacS).pow n))
    exact (hk.mul hP).congr (fun S hS => (i1 S hS).2)
  · rw [V.2, k6 c hc]

end GlobalTheory.CompanionTheory.SW.StageF
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.archimedean_siegel_weil_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → ∀ minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E), IsGramFibFree (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf → ∀ (c : HermR (Ainf F) σ n) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ), GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → Measurable φ ∧ Integrable φ (minf c) ∧ ∀ ρ : ℕ → HermR (Ainf F) σ n → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets → (∀ k, Integrable (fun X => φ X * (gramTest (Ainf F) σ J c (ρ k) X : ℂ)) (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) ∧ Filter.Tendsto (fun k => (∫ X, φ X * (gramTest (Ainf F) σ J c (ρ k) X : ℂ) ∂(GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)) / ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ)) Filter.atTop (nhds (∫ X, φ X ∂(minf c))) := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.avgInf_tendsto | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.avgInf_tendsto | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.avgInf_tendsto <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.SmallZ
open GlobalTheory.CompanionTheory.SwUnf.SmallCell

variable {D : D7} {n ρ p : ℕ}

theorem zinc_inl {K : Type} [Field K] (hn : ρ + p = n) (u : Fin ρ → K) (a : Fin ρ) :
    zinc hn u ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl a)) = u a := by
  change Sum.elim u (fun _ : Fin p => (0 : K)) ((finSumFinEquiv.trans (finCongr hn)).symm _) = u a
  rw [Equiv.symm_apply_apply, Sum.elim_inl]

theorem zinc_inr {K : Type} [Field K] (hn : ρ + p = n) (u : Fin ρ → K) (a : Fin p) :
    zinc hn u ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr a)) = 0 := by
  change Sum.elim u (fun _ : Fin p => (0 : K)) ((finSumFinEquiv.trans (finCongr hn)).symm _) = 0
  rw [Equiv.symm_apply_apply, Sum.elim_inr]

theorem blockMatrix_inl_inl {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i j : Fin ρ) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = a i j := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

theorem blockMatrix_inl_inr {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i : Fin ρ) (j : Fin p) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = 0 := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

theorem blockMatrix_inr_inl {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i : Fin p) (j : Fin ρ) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = 0 := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

theorem blockMatrix_inr_inr {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i j : Fin p) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = 0 := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]

def rk2 {m : ℕ} (τ : AE D) (v r : Fin m → D.host.E) : Mx D m m :=
  τ • ((rat (Matrix.replicateCol (Fin 1) v) : Mx D m 1) ⬝ (rat (Matrix.replicateRow (Fin 1) r) : Mx D 1 m) +
    adj (rat (Matrix.replicateRow (Fin 1) r) : Mx D 1 m) ⬝ adj (rat (Matrix.replicateCol (Fin 1) v) : Mx D m 1))

theorem rank_two_matrix_apply {m : ℕ} (τ : AE D) (v r : Fin m → D.host.E) (i j : Fin m) :
    rk2 τ v r i j = τ * (incA D (v i) * incA D (r j) + cA D (incA D (r i)) * cA D (incA D (v j))) := by
  simp only [rk2, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul]
  rfl

theorem rk_term (τ : AE D) (a b c d : D.host.E) (h1 : a = 0 ∨ b = 0) (h2 : c = 0 ∨ d = 0) :
    τ * (incA D a * incA D b + cA D (incA D c) * cA D (incA D d)) = 0 := by
  have e1 : incA D a * incA D b = 0 := by
    rcases h1 with rfl | rfl
    · rw [map_zero (incA D), zero_mul]
    · rw [map_zero (incA D), mul_zero]
  have e2 : cA D (incA D c) * cA D (incA D d) = 0 := by
    rcases h2 with rfl | rfl
    · rw [map_zero (incA D), map_zero (cA D), zero_mul]
    · rw [map_zero (incA D), map_zero (cA D), mul_zero]
  rw [e1, e2, add_zero, mul_zero]

theorem rank_two_embedding_small (hn : ρ + p = n) (τ : AE D) (v r : Fin ρ → D.host.E) :
    rk2 τ (zinc hn v) (zinc hn r) = bl hn (rk2 τ v r) 0 0 0 := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases i with i | i <;> rcases j with j | j
  · rw [blockMatrix_inl_inl, rank_two_matrix_apply, rank_two_matrix_apply, zinc_inl, zinc_inl, zinc_inl, zinc_inl]
  · rw [blockMatrix_inl_inr, rank_two_matrix_apply]
    exact rk_term _ _ _ _ _ (Or.inr (zinc_inr hn r j)) (Or.inr (zinc_inr hn v j))
  · rw [blockMatrix_inr_inl, rank_two_matrix_apply]
    exact rk_term _ _ _ _ _ (Or.inl (zinc_inr hn v i)) (Or.inl (zinc_inr hn r i))
  · rw [blockMatrix_inr_inr, rank_two_matrix_apply]
    exact rk_term _ _ _ _ _ (Or.inl (zinc_inr hn v i)) (Or.inl (zinc_inr hn r i))

theorem small : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ), b₀.1.det ≠ 0 →
    ∀ (W : Submodule D.host.E (Fin ρ → D.host.E)), W ≠ ⊥ → ∃ ν : hermA D ρ, chz ψ b₀ ν ≠ 1 ∧
    ∀ (γ u : G D n), γ ∈ GF D n → ∀ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) → zKer hn x = W →
      mat u = blk4 1 (bl hn ν.1 0 0 0) 0 1 →
      ∃ q ∈ P D n, ∃ a : GL (Fin n) (AE D), blkA (mat q) = a.1 ∧ Matrix.GeneralLinearGroup.det a = 1 ∧ γ * u = q * γ := by
  intro D n ρ p hn ψ hψ β hβ W hW
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hw : β.1 *ᵥ v ≠ 0 := fun h => hv0 (Matrix.eq_zero_of_mulVec_eq_zero hβ h)
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hw
  let r : Fin ρ → D.host.E := Pi.single i0 ((β.1 *ᵥ v) i0)⁻¹
  let V0 : Matrix (Fin ρ) (Fin 1) D.host.E := Matrix.replicateCol _ v
  let R0 : Matrix (Fin 1) (Fin ρ) D.host.E := Matrix.replicateRow _ r
  have hbV : β.1 ⬝ V0 = Matrix.replicateCol _ (β.1 *ᵥ v) := by
    ext i j
    simp [V0, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hS0 : R0 ⬝ β.1 ⬝ V0 = (1 : Matrix (Fin 1) (Fin 1) D.host.E) := by
    rw [Matrix.mul_assoc, hbV]
    ext a b
    obtain rfl : a = b := Subsingleton.elim _ _
    simp [R0, r, Matrix.mul_apply, Pi.single_apply, inv_mul_cancel₀ (show (β.1 *ᵥ v) i0 ≠ 0 from hi0)]
  have hS : (rat R0 : Mx D 1 ρ) ⬝ (rat β.1 : Mx D ρ ρ) ⬝ (rat V0 : Mx D ρ 1) = 1 := by
    rw [← rat_mul, ← rat_mul, hS0]
    ext a b
    obtain rfl : a = b := Subsingleton.elim _ _
    simp [rat]
  obtain ⟨x0, hx0⟩ := hψ.2.2.2
  obtain ⟨t, ht⟩ := exists_scalar (D := D) x0
  have hν : adj (rk2 (algebraMap (AF D.host.F) (AE D) t) v r) = rk2 (algebraMap (AF D.host.F) (AE D) t) v r := by
    unfold rk2
    rw [adj_smul, cA_algebraMap', adj_add, adj_mul, adj_mul, adj_adj, adj_adj, add_comm]
  refine ⟨⟨_, hν⟩, ?_, ?_⟩
  · have h := trace_val (rat β.1) (adj_rat_herm β) (rat V0) (rat R0) (algebraMap (AF D.host.F) (AE D) t) hS
    change ψ (halfTr (Matrix.trace ((rat β.1 : Mx D ρ ρ) ⬝ _))) ≠ 1
    change ψ (halfTr (Matrix.trace ((rat β.1 : Mx D ρ ρ) ⬝ (algebraMap (AF D.host.F) (AE D) t • _)))) ≠ 1
    rw [h, ht]
    exact hx0
  · intro γ u hγ x hx hW' hu
    refine cell_absorb (rat (Matrix.replicateCol (Fin 1) (zinc hn v))) (rat (Matrix.replicateRow (Fin 1) (zinc hn r)))
      (algebraMap (AF D.host.F) (AE D) t) ((rank_two_embedding_small hn _ v r).symm) γ u hu ?_
    have hv : lowerC x *ᵥ zinc hn v = 0 := by
      rw [← hW'] at hvW
      exact hvW
    have h0 : (HMul.hMul (lowerC x) (Matrix.replicateCol (Fin 1) (zinc hn v)) : Matrix (Fin n) (Fin 1) D.host.E) = 0 := by
      refine Matrix.ext fun i j => ?_
      have := congrFun hv i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    rw [hx, lowerC_map]
    change (rat (lowerC x) : Mx D n n) ⬝ (rat (Matrix.replicateCol (Fin 1) (zinc hn v)) : Mx D n 1) = 0
    rw [← rat_mul, h0]
    ext i j
    simp [rat]

end GlobalTheory.CompanionTheory.ZUnf.SmallZ
end
end

section

open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT

theorem _root_.GlobalTheory.T.matching_split_of : MatchSplitOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf | exact GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf | (intros; apply GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf <;> assumption)
end
