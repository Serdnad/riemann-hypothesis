module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle504
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
import Formalism.LocalRingCardinality.DataHost
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallySmall
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle495
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviCommuteUnipotentBoundary
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle496
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem pi_map_update_add {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd₂ V] {n : ℕ}
    (ν : Measure V) [SigmaFinite ν] [ν.IsAddRightInvariant] (a : Fin n) (T : (Fin n → V) → V)
    (hT : Measurable T) (hTa : ∀ x y, T (Function.update x a y) = T x) :
    (Measure.pi fun _ : Fin n => ν).map (fun x => Function.update x a (x a + T x)) =
      Measure.pi fun _ : Fin n => ν := by
  have hf : Measurable (fun x : Fin n → V => Function.update x a (x a + T x)) := by
    refine Measurable.of_eval fun j => ?_
    by_cases h : j = a
    · subst h
      simp only [Function.update_self]
      exact (measurable_pi_apply j).add hT
    · simpa [Function.update_of_ne h] using measurable_pi_apply j
  refine (Measure.pi_eq fun s hs => ?_).symm
  have h2s : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [← Measure.pi_pi, ← lintegral_indicator_one h2s, ← lintegral_indicator_one h2s,
    lintegral_map (measurable_one.indicator h2s) hf]
  refine lintegral_eq_of_lmarginal_eq {a} ((measurable_one.indicator h2s).comp hf)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  have key : ∀ y : V, Function.update (Function.update x a y) a (Function.update x a y a + T (Function.update x a y))
      = Function.update x a (y + T x) := by
    intro y
    simp [hTa]
  simp only [Function.comp_def, key]
  exact lintegral_add_right_eq_self
    (fun y => (Set.univ.pi s).indicator (1 : (Fin n → V) → ℝ≥0∞) (Function.update x a y)) (T x)

theorem coordW_map_shearK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n M d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)), lam.IsAddHaarMeasure → ∀ (a : Fin n) (s : Fin n → Ainf F ⊗[F] E), s a = 0 → (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M).map (GlobalTheory.CompanionTheory.WhitFree.AvgInf.shearK a s) = GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b lam n M := by
  intro F E _ _ _ _ _ σ hσ n M d b lam hlam a s hs
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Ainf F) d b lam hlam
  haveI := hK
  haveI : SigmaFinite (GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) := inferInstance
  haveI hν : (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam).IsAddHaarMeasure := inferInstance
  have hmul : ∀ c : Ainf F ⊗[F] E, Measurable (fun y : Ainf F ⊗[F] E => c * y) := fun c =>
    (continuous_const.mul continuous_id).measurable
  have hT : Measurable (fun (x : Fin n → Fin M → Ainf F ⊗[F] E) (i : Fin M) => ∑ c, s c * x c i) := by
    refine Measurable.of_eval fun i => ?_
    refine Finset.measurable_sum _ fun c _ => ?_
    exact (hmul (s c)).comp ((measurable_pi_apply i).comp (measurable_pi_apply c))
  have hTa : ∀ (x : Fin n → Fin M → Ainf F ⊗[F] E) (y : Fin M → Ainf F ⊗[F] E),
      (fun i => ∑ c, s c * Function.update x a y c i) = fun i => ∑ c, s c * x c i := by
    intro x y
    funext i
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : c = a
    · subst h; simp [hs]
    · simp [Function.update_of_ne h]
  exact pi_map_update_add (Measure.pi fun _ : Fin M => GlobalTheory.CompanionTheory.SW.coordK (Ainf F) b lam) a _ hT hTa

end GlobalTheory.CompanionTheory.WhitFree.AvgInf
end
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ResMu

open Set GlobalTheory.Eis

variable {D : D7} {p : ℕ}

theorem law_ratInv {n : ℕ} {z : ℂ} {s : G D n → ℂ} (hs : IsLaw 1 z s) : LeftInv (P D n ⊓ GF D n) s := fun γ hγ g => by
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hγ.1
  obtain ⟨u, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.det_rat hγ.2 a ha
  have h1 : absA D (Units.map (incA D).toMonoidHom u) = 1 := absE_inclR u
  rw [hs γ hγ.1 a ha g, hu, h1]
  simp

theorem rho_right {f : G D p → ℂ} (hf : IsRho f) (x : G D p) : IsRho fun g => f (g * x) :=
  ⟨hf.1.comp (continuous_id.mul continuous_const), law_right hf.2 x⟩

theorem fam_law_real {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : IsRho f) (σ : ℝ) :
    IsLaw 1 (σ : ℂ) (fam H f ((p : ℂ) / 2) (σ : ℂ)) := fam_law hH hf.2 σ

theorem fam_cont_at {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : Continuous f) (s₁ : ℂ) (σ : ℝ) :
    Continuous (fam H f s₁ (σ : ℂ)) :=
  (fam_cont hH hf s₁).comp (f := fun g : G D p => ((σ, g) : ℝ × G D p)) (by fun_prop)

theorem fam_at (H : G D p → ℝ≥0) (f : G D p → ℂ) : fam H f ((p : ℂ) / 2) (((p : ℝ) / 2 : ℝ) : ℂ) = f := by
  funext g
  have : ((((p : ℝ) / 2 : ℝ) : ℂ)) - (p : ℂ) / 2 = 0 := by push_cast; ring
  simp [fam, this]

theorem res_leftInv {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : IsRho f) (σ : ℝ) :
    LeftInv (GF D p) (res H f σ) := fun γ hγ g => by
  simp only [res, eisS]
  rw [leftInv_cosetSum (law_ratInv (fam_law_real hH hf σ)) γ hγ g]

theorem eis_right (s : G D p → ℂ) (x : G D p) : eisS s x = eisS (fun g => s (g * x)) 1 := by
  simp only [eisS]
  rw [cosetSum_mul_right, one_mul]

theorem res_equi (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (x : G D p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x' in 𝓝 x, ∀ σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1), ‖res H f σ x' - res H f σ x‖ ≤ ε := by
  obtain ⟨B, hB0, hB⟩ := eis_bound hS hp hH (isCompact_singleton (x := (1 : G D p)))
  have hK : IsCompact (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ C) := isCompact_Icc.prod hC
  have hε' : 0 < ε / (2 * (B + 1)) := by positivity
  have hfc := fam_cont hH hf.1 ((p : ℂ) / 2)
  have hev : ∀ᶠ x' in 𝓝 x, ∀ y ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ C,
      ‖fam H f ((p : ℂ) / 2) (y.1 : ℂ) (y.2 * x') - fam H f ((p : ℂ) / 2) (y.1 : ℂ) (y.2 * x)‖ <
        ε / (2 * (B + 1)) * (H y.2 : ℝ) ^ (y.1 + p / 2) := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have c1 : Continuous fun u : G D p × (ℝ × G D p) => fam H f ((p : ℂ) / 2) (u.2.1 : ℂ) (u.2.2 * u.1) :=
      hfc.comp (f := fun u : G D p × (ℝ × G D p) => ((u.2.1, u.2.2 * u.1) : ℝ × G D p)) (by fun_prop)
    have c2 : Continuous fun u : G D p × (ℝ × G D p) => fam H f ((p : ℂ) / 2) (u.2.1 : ℂ) (u.2.2 * x) :=
      hfc.comp (f := fun u : G D p × (ℝ × G D p) => ((u.2.1, u.2.2 * x) : ℝ × G D p)) (by fun_prop)
    have c3 : Continuous fun u : G D p × (ℝ × G D p) => ε / (2 * (B + 1)) * (H u.2.2 : ℝ) ^ (u.2.1 + p / 2) :=
      continuous_const.mul ((NNReal.continuous_coe.comp (hH.1.comp (continuous_snd.comp continuous_snd))).rpow
        ((continuous_fst.comp continuous_snd).add continuous_const) fun u => Or.inl (NNReal.coe_pos.2 (hH.2.1 _)).ne')
    refine ((c1.sub c2).norm.continuousAt.eventually_lt c3.continuousAt ?_)
    simp only [Pi.sub_apply, sub_self, norm_zero]
    exact mul_pos hε' (Real.rpow_pos_of_pos (NNReal.coe_pos.2 (hH.2.1 _)) _)
  filter_upwards [hev] with x' hx' σ hσ
  have hI' : σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) := ⟨hσ.1.le, hσ.2⟩
  have hl := fam_law_real hH hf σ
  have hc := fam_cont_at hH hf.1 ((p : ℂ) / 2) σ
  have hct : ∀ y : G D p, Continuous fun g => fam H f ((p : ℂ) / 2) (σ : ℂ) (g * y) := fun y =>
    hc.comp (continuous_id.mul continuous_const)
  have hb := law_bound hH hcov (law_sub (law_right hl x') (law_right hl x)) (δ := ε / (2 * (B + 1))) (fun c hc =>
    (hx' (σ, c) ⟨hI', hc⟩).le)
  have hf' := (hB σ hσ 1 rfl _ _ hb).2
  rw [eis_sub (conv_of_section hS hp hH hC hcov hσ (hct x') (law_right hl x') 1)
    (conv_of_section hS hp hH hC hcov hσ (hct x) (law_right hl x) 1), ← eis_right, ← eis_right] at hf'
  have e : res H f σ x' - res H f σ x =
      ((σ - p / 2 : ℝ) : ℂ) * (eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) x' - eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) x) := by
    simp only [res]; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [hσ.1])]
  have : ε / (2 * (B + 1)) * B ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem res_cont (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {σ : ℝ}
    (hσ : σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1)) : Continuous (res H f σ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [res_equi hS hp hH hC hcov hf x (half_pos hε)] with x' hx'
  rw [dist_eq_norm]
  linarith [hx' σ hσ]

theorem resA_near (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (x : G D p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x' in 𝓝 x, ‖resA H f x' - resA H f x‖ ≤ ε := by
  filter_upwards [res_equi hS hp hH hC hcov hf x hε] with x' hx'
  have h1 := ((res_tendsto hS hp hH hC hcov hf x').sub (res_tendsto hS hp hH hC hcov hf x)).norm
  refine le_of_tendsto h1 ?_
  refine ufil_le p ?_
  filter_upwards [ev_Ioc p] with σ hσ using hx' σ hσ

theorem resA_cont (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) : Continuous (resA H f) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [resA_near hS hp hH hC hcov hf x (half_pos hε)] with x' hx'
  rw [dist_eq_norm]
  linarith

theorem resA_leftInv (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) : LeftInv (GF D p) (resA H f) := fun γ hγ g => by
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov hf (γ * g)) ?_
  have := res_tendsto hS hp hH hC hcov hf g
  refine this.congr fun σ => ?_
  rw [res_leftInv hH hf σ γ hγ g]

theorem resA_unif (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {C' : Set (G D p)} (hC' : IsCompact C')
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), ∀ c ∈ C', ‖res H f σ c - resA H f c‖ ≤ ε := by
  refine hC'.induction_on (p := fun S => ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), ∀ c ∈ S, ‖res H f σ c - resA H f c‖ ≤ ε)
    (by simp) (fun s t hst h => h.mono fun σ hσ c hc => hσ c (hst hc))
    (fun s t hs ht => by
      filter_upwards [hs, ht] with σ h1 h2 c hc
      exact hc.elim (h1 c) (h2 c)) fun x _ => ?_
  have hε3 : 0 < ε / 3 := by positivity
  refine ⟨_, mem_nhdsWithin_of_mem_nhds ((res_equi hS hp hH hC hcov hf x hε3).and (resA_near hS hp hH hC hcov hf x hε3)), ?_⟩
  have h1 : ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), ‖res H f σ x - resA H f x‖ < ε / 3 := by
    have := (res_tendsto hS hp hH hC hcov hf x)
    rw [Metric.tendsto_nhds] at this
    filter_upwards [this _ hε3] with σ hσ
    rwa [dist_eq_norm] at hσ
  filter_upwards [h1, ufil_le p (ev_Ioc p)] with σ hσ hI c hc
  have a1 := hc.1 σ hI
  have a2 := hc.2
  calc ‖res H f σ c - resA H f c‖ = ‖(res H f σ c - res H f σ x) + (res H f σ x - resA H f x) - (resA H f c - resA H f x)‖ := by
        congr 1; ring
    _ ≤ ‖res H f σ c - res H f σ x‖ + ‖res H f σ x - resA H f x‖ + ‖resA H f c - resA H f x‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ε := by linarith

theorem resA_translate (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (x : G D p) :
    resA H f x = resA H (fun g => f (g * x)) 1 := by
  have hfx := rho_right hf x
  have hd := tendsto_diff hS hp hH hC hcov
    (S := fun σ g => fam H f ((p : ℂ) / 2) (σ : ℂ) (g * x)) (S' := fun σ => fam H (fun g => f (g * x)) ((p : ℂ) / 2) (σ : ℂ))
    ((fam_cont hH hf.1 _).comp (f := fun u : ℝ × G D p => ((u.1, u.2 * x) : ℝ × G D p)) (by fun_prop)).continuousOn
    (fam_cont hH hfx.1 _).continuousOn
    (fun σ _ => law_right (fam_law_real hH hf σ) x) (fun σ _ => fam_law_real hH hfx σ)
    (by simp only [fam_at])
  have h1 := (hd.mono_left (ufil_le p)).add (res_tendsto hS hp hH hC hcov hfx 1)
  rw [zero_add] at h1
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov hf x) (h1.congr fun σ => ?_)
  simp only [res]
  rw [eis_right (fam H f ((p : ℂ) / 2) (σ : ℂ)) x]
  ring

end GlobalTheory.CompanionTheory.ResMu
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ThTot
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot.ProductTheta

variable {D : D7} {r s p : ℕ}

theorem continuous_rowT : Continuous (rowT : Mx D (r + s) p → Mx D r p) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp (continuous_apply (Fin.castAdd s i))

theorem continuous_rowB : Continuous (rowB : Mx D (r + s) p → Mx D s p) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply j).comp (continuous_apply (Fin.natAdd r i))

theorem rowT_rowJ (x : Mx D r p) (z : Mx D s p) : rowT (rowJ x z) = x := by
  funext i j
  simp [rowT, rowJ]

theorem rowB_rowJ (x : Mx D r p) (z : Mx D s p) : rowB (rowJ x z) = z := by
  funext i j
  simp [rowB, rowJ]

theorem rowJ_rowT_rowB (y : Mx D (r + s) p) : rowJ (rowT y) (rowB y) = y := by
  funext i j
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp [rowT, rowB, rowJ]

theorem continuous_rowJ :
    Continuous fun z : Mx D r p × Mx D s p => rowJ z.1 z.2 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simpa [rowJ, Function.comp_def] using (continuous_apply j).comp ((continuous_apply a).comp continuous_fst)
  · simpa [rowJ, Function.comp_def] using (continuous_apply j).comp ((continuous_apply b).comp continuous_snd)

def rowHomeo : Mx D r p × Mx D s p ≃ₜ Mx D (r + s) p where
  toFun z := rowJ z.1 z.2
  invFun y := (rowT y, rowB y)
  left_inv z := by simp [rowT_rowJ, rowB_rowJ]
  right_inv y := rowJ_rowT_rowB y
  continuous_toFun := continuous_rowJ
  continuous_invFun := continuous_rowT.prodMk continuous_rowB

theorem rowT_mul (y : Mx D (r + s) p) (a : Mx D p p) :
    rowT (HMul.hMul y a : Mx D (r + s) p) = (HMul.hMul (rowT y) a : Mx D r p) := rfl

theorem rowB_mul (y : Mx D (r + s) p) (a : Mx D p p) :
    rowB (HMul.hMul y a : Mx D (r + s) p) = (HMul.hMul (rowB y) a : Mx D s p) := rfl

theorem pr_split {b : HermE D (r + s)} {br : HermE D r} {bs : HermE D s} (h : IsBlockSL2Embedding b br bs)
    (x y : Mx D (r + s) p) :
    pr b x y = pr br (rowT x) (rowT y) + pr bs (rowB x) (rowB y) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  funext i j
  simp only [pr, Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, Fin.sum_univ_add, h1, h2, h3, h4,
    map_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  rfl

theorem halfTr_add (u v : AE D) : halfTr (u + v) = halfTr u + halfTr v := by
  simp only [halfTr, trA, map_add (f := _), mul_add]

theorem npow_half_mul (x : ℝ≥0) (hx : x ≠ 0) :
    npow x ((r : ℂ) / 2) * npow x ((s : ℂ) / 2) = npow x (((r + s : ℕ) : ℂ) / 2) := by
  have hx' : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
  simp only [npow]
  rw [← Complex.cpow_add _ _ hx']
  congr 1
  push_cast
  ring

theorem absA_ne_zero (u : (AE D)ˣ) : absA D u ≠ 0 := by
  intro h
  have := map_mul (absA D) u u⁻¹
  rw [mul_inv_cancel, map_one, h, zero_mul] at this
  exact one_ne_zero this

theorem prodTh_of_schwTensor : SchwTensor → ProdTh := by
  intro hT D r s p μr 𝓕r μs 𝓕s hμr hμs ψ hψ χr χs θ hθ br bs b hb Ωr Ωs hr hs
  haveI : BorelSpace (Mx D r p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D s p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩
  haveI : SecondCountableTopology (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.2.1
  haveI : SecondCountableTopology (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.2.1
  refine ⟨fun h => hT D θ hθ r s p _ (hr.mem h) _ (hs.mem h), ?_, ?_, ?_, ?_, ?_⟩
  · have c1 : Continuous fun u : G D p × Mx D (r + s) p => ((u.1, rowT u.2) : G D p × Mx D r p) :=
      continuous_fst.prodMk (continuous_rowT.comp continuous_snd)
    have c2 : Continuous fun u : G D p × Mx D (r + s) p => ((u.1, rowB u.2) : G D p × Mx D s p) :=
      continuous_fst.prodMk (continuous_rowB.comp continuous_snd)
    exact (hr.cont.comp c1).mul (hs.cont.comp c2)
  · intro C hC
    obtain ⟨Mr, hMr, h1⟩ := hr.maj C hC
    obtain ⟨Ms, hMs, h2⟩ := hs.maj C hC
    refine ⟨_, hT D θ hθ r s p _ hMr _ hMs, fun h hh y => ?_⟩
    rw [norm_mul, norm_mul]
    exact mul_le_mul (h1 h hh _) (h2 h hh _) (norm_nonneg _) (norm_nonneg _)
  · intro g a hg h y
    have e := npow_half_mul (r := r) (s := s) (absA D (Matrix.GeneralLinearGroup.det a)) (absA_ne_zero _)
    rw [hr.levi g a hg h, hs.levi g a hg h, rowT_mul, rowB_mul, ← e]
    simp only [MonoidHom.mul_apply, Circle.coe_mul]
    ring
  · intro g c hg h y
    rw [hr.unip g c hg h, hs.unip g c hg h, pr_split hb, mul_add, Matrix.trace_add, halfTr_add,
      AddChar.map_add_eq_mul]
    ring
  · intro g hg h x
    haveI := hμr.1
    haveI := hμs.1
    haveI : LocallyCompactSpace (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.1
    haveI : LocallyCompactSpace (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.1
    have hemb : MeasurableEmbedding (fun z : Mx D r p × Mx D s p => rowJ z.1 z.2) :=
      (rowHomeo (D := D) (r := r) (s := s) (p := p)).measurableEmbedding
    rw [hemb.integral_map, hr.weyl g hg h, hs.weyl g hg h, ← integral_prod_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [rowT_rowJ, rowB_rowJ, pr_split hb, Matrix.trace_add, map_add (f := _), AddChar.map_add_eq_mul]
    ring

end GlobalTheory.CompanionTheory.ThTot.ProductTheta

end
end

section

open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.levi_raising_kills_top_chain : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V) (u : V),
    (∀ a b : Fin n, a < b → kA E1 E2 a b u = 0) → ∀ p q : Fin n, p < q → lev p = lev q →
      Lv lev E1 E2 p q (Pi.single (omU lev) u : Cq n V) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LvChain.Lv_single_omU | exact GlobalTheory.CompanionTheory.LvChain.Lv_single_omU | (intros; apply GlobalTheory.CompanionTheory.LvChain.Lv_single_omU <;> assumption)
end

section

open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.levi_adjoint_on_chains : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    (∀ a b (x y : V), ⟪kA E1 E2 a b x, y⟫_ℂ = ⟪x, kA E1 E2 b a y⟫_ℂ) → ∀ p q : Fin n, lev p = lev q → ∀ x z : Cq n V,
      ∑ A, ⟪Lv lev E1 E2 p q x A, z A⟫_ℂ = ∑ A, ⟪x A, Lv lev E1 E2 q p z A⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.LvChainAdj.Lv_adjoint | exact GlobalTheory.CompanionTheory.LvChainAdj.Lv_adjoint | (intros; apply GlobalTheory.CompanionTheory.LvChainAdj.Lv_adjoint <;> assumption)
end

section

open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.levi_commute_unipotent_boundary : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
    Monotone lev → IsPairA E1 E2 → ∀ p q : Fin n, lev p = lev q →
      (Lv lev E1 E2 p q * bdL (inUU lev) E1 E2 : Module.End ℂ (Cq n V)) = bdL (inUU lev) E1 E2 * Lv lev E1 E2 p q := by
  first | exact @GlobalTheory.CompanionTheory.LvComm.lv_bd_comm | exact GlobalTheory.CompanionTheory.LvComm.lv_bd_comm | (intros; apply GlobalTheory.CompanionTheory.LvComm.lv_bd_comm <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.acris_isAdicComplete_span_prime : ∀ {l : ℕ} [Fact l.Prime], IsAdicComplete (Ideal.span {(l : Acris l)}) (Acris l) := by
  first | exact @GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete | exact GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete | (intros; apply GlobalTheory.CompanionTheory.ACrisAdic.acris_isAdicComplete <;> assumption)
end
