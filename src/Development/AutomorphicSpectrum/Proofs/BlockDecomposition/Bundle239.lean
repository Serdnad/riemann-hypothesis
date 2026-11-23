module

import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle217
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ContinuousHermScal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle055
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle040
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle051
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle191
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle221
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle206
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK GlobalTheory.CompanionTheory.WaveK.Base
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveK.Lin

variable {n : ℕ}

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Eu_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) := by
  have h := fun X : Mat n => GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf
  unfold Eu
  exact ((h _).add (contDiffOn_const.smul (h _))).const_smul _

theorem Epow_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, ContDiffOn ℝ ∞ (Epow s m a b f) (GLs n) := by
  apply _root_.GlobalTheory.CompanionTheory.WaveK.Uniq.Epow_smooth <;> assumption

theorem Eu_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) (s : Bool)
    (a b : Fin n) : Set.EqOn (Eu s a b (f + f')) (Eu s a b f + Eu s a b f') (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, GlobalTheory.CompanionTheory.RCalc.Rd_add _ hf hf' hx, smul_add]
  abel

theorem Eu_smul (c : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b (c • f)) (c • Eu s a b f) (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, GlobalTheory.CompanionTheory.RCalc.Rd_smul c _ hf hx]
  module

theorem Epow_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : ∀ a b : Fin n, Set.EqOn (Epow s m a b (f + f')) (Epow s m a b f + Epow s m a b f') (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact Eu_add (Epow_smooth hf s m c b) (Epow_smooth hf' s m c b) s a c hx

theorem Epow_smul (k : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b (k • f)) (k • Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact Eu_smul k (Epow_smooth hf s m c b) s a c hx

theorem gel_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : Set.EqOn (gel s m (f + f')) (gel s m f + gel s m f') (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Epow_add hf hf' s m a a hx

theorem gel_smul (k : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (k • f)) (k • gel s m f) (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => Epow_smul k hf s m a a hx

theorem Om_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Om (f + f')) (Om f + Om f') (GLs n) := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_add hf hf' _ _ hx, smul_add]
  abel

theorem Om_smul (k : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Om (k • f)) (k • Om f) (GLs n) := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_smul k hf _ _ hx]
  module

theorem iterated_integral_add {w w' : ℝ → V} (hw : ContDiff ℝ ∞ w) (hw' : ContDiff ℝ ∞ w') (t : ℝ) :
    iteratedDeriv 2 (fun s => w s + w' s) t = iteratedDeriv 2 w t + iteratedDeriv 2 w' t := by
  have h2 : ∀ φ : ℝ → V, iteratedDeriv 2 φ = deriv (deriv φ) := fun φ => by
    rw [iteratedDeriv_eq_iterate]; rfl
  have hd : deriv (fun s => w s + w' s) = fun s => deriv w s + deriv w' s :=
    funext fun s => deriv_fun_add (hw.differentiable (by simp) s) (hw'.differentiable (by simp) s)
  have e1 : Differentiable ℝ (deriv w) := (contDiff_infty_iff_deriv.1 hw).2.differentiable (by simp)
  have e2 : Differentiable ℝ (deriv w') := (contDiff_infty_iff_deriv.1 hw').2.differentiable (by simp)
  rw [h2, h2, h2, hd]
  exact deriv_fun_add (e1 t) (e2 t)

theorem iteratedDeriv_two_smul (k : ℂ) {w : ℝ → V} (hw : ContDiff ℝ ∞ w) (t : ℝ) :
    iteratedDeriv 2 (fun s => k • w s) t = k • iteratedDeriv 2 w t := by
  have h2 : ∀ φ : ℝ → V, iteratedDeriv 2 φ = deriv (deriv φ) := fun φ => by
    rw [iteratedDeriv_eq_iterate]; rfl
  have hd : deriv (fun s => k • w s) = fun s => k • deriv w s :=
    funext fun s => deriv_fun_const_smul k (hw.differentiable (by simp) s)
  have e1 : Differentiable ℝ (deriv w) := (contDiff_infty_iff_deriv.1 hw).2.differentiable (by simp)
  rw [h2, h2, hd]
  exact deriv_fun_const_smul k (e1 t)

end Ops

theorem wave_add {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v) :
    IsWave E fun t y => u t y + v t y := by
  refine ⟨hu.1.add hv.1, fun t => ⟨(hu.2.1 t).1.add (hv.2.1 t).1, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · intro g hg k
    simp only [(hu.2.1 t).2 g hg k, (hv.2.1 t).2 g hg k, map_add (f := _)]
  · rw [iterated_integral_add (GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg) (GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg), hu.2.2.1 t g hg, hv.2.2.1 t g hg]
    exact (Om_add (hu.2.1 t).1 (hv.2.1 t).1 hg).symm
  · have h1 : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).differentiable (by simp)).differentiableAt
    have h2 : DifferentiableAt ℝ (fun s => v s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg).differentiable (by simp)).differentiableAt
    rw [deriv_fun_add h1 h2, hu.2.2.2 g hg, hv.2.2.2 g hg, add_zero]

theorem wave_smul (k : ℂ) {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) :
    IsWave E fun t y => k • u t y := by
  refine ⟨hu.1.const_smul k, fun t => ⟨(hu.2.1 t).1.const_smul k, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · intro g hg k'
    simp only [(hu.2.1 t).2 g hg k', map_smul]
  · rw [iteratedDeriv_two_smul k (GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg), hu.2.2.1 t g hg]
    exact (Om_smul k (hu.2.1 t).1 hg).symm
  · have h1 : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).differentiable (by simp)).differentiableAt
    rw [deriv_fun_const_smul k h1, hu.2.2.2 g hg, smul_zero]

end GlobalTheory.CompanionTheory.WaveK.Lin
end
end

section

open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FibreCpt

open GlobalTheory.CompanionTheory.SW.FibreRatio

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem masses_field (R : Type) [Field R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    [BorelSpace R] (hloc : IsLocR R) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hfib : IsGramFib R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m)
    (A : Set (Fin 1 → Fin M → R ⊗[F] E)) (hAc : IsCompact A) (hAo : IsOpen A)
    (hAU : A ⊆ {X | IsUnit (gramR R σ J X).det}) :
    Continuous (fun s : R => (m (hermScal R σ s) A).toReal) ∧
    HasCompactSupport (fun s : R => (m (hermScal R σ s) A).toReal) ∧
    ENNReal.ofReal (∫ s, (m (hermScal R σ s) A).toReal ∂lam) = coordW R b lam 1 M A := by
  obtain ⟨h1, h2, h3, h4, -⟩ := id hloc
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, hT2, -, htr, -, hBor, -, hgr⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h R
  haveI := hT2
  haveI := hBor 1 M
  haveI : BorelSpace (HermR R σ 1) := ⟨rfl⟩
  have hHaar := GlobalTheory.T.coordinate_haar_measure F E σ h R d b lam hlam
  have hμ := hHaar.2.1 1 M
  have hν := hHaar.2.2 1
  have hAm : MeasurableSet A := hAo.measurableSet
  set φ : (Fin 1 → Fin M → R ⊗[F] E) → ℂ := A.indicator fun _ => 1 with hφ
  have hAclopen : IsClopen A := ⟨hAc.isClosed, hAo⟩
  have hφc : Continuous φ :=
    continuous_indicator (by simp [hAclopen.frontier_eq]) continuousOn_const
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro hAc fun x hx => Set.indicator_of_notMem hx _
  obtain ⟨⟨hg, -⟩, -⟩ := GlobalTheory.T.gram_fiber_integral_isContDensityOn F E σ h M J hJ R hloc 1 _ _ m hμ hν hfib φ hφc hφs
  have hfin : ∀ S, m S A < ⊤ := fun S => by
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ h M J hJ R hloc 1 _ _ m hμ hν hfib S).1
    exact hAc.measure_lt_top
  have hint : ∀ S, ∫ X, φ X ∂(m S) = (((m S A).toReal : ℝ) : ℂ) := fun S => by
    rw [hφ, integral_indicator_const _ hAm]
    simp [Measure.real]
  have hcs : Continuous (hermScal R σ (F := F) (E := E)) := continuous_hermScal R

  have hqc : Continuous fun X : Fin 1 → Fin M → R ⊗[F] E =>
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) :=
    continuous_const.mul (htr.comp ((hgr 1 M J).matrix_elem 0 0))
  set K : Set R := (fun X : Fin 1 → Fin M → R ⊗[F] E =>
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0)) '' A with hKdef
  have hKc : IsCompact K := hAc.image hqc
  haveI : Nontrivial (R ⊗[F] E) := ⟨1, 0, fun e => by
    have h3 := GlobalTheory.CompanionTheory.SW.FibreRatio.half_trace_tmul (F := F) (E := E) R h (1 : R)
    rw [← Algebra.TensorProduct.one_def, e, map_zero, mul_zero] at h3
    exact zero_ne_one h3⟩
  have hK0 : (0 : R) ∉ K := by
    rintro ⟨X, hX, h0⟩
    have hu : IsUnit (gramR R σ J X).det := hAU hX
    rw [Matrix.det_fin_one, gram_entry R h hJ X] at hu
    simp only at h0
    rw [h0, TensorProduct.zero_tmul] at hu
    exact not_isUnit_zero hu
  have hzero : ∀ s, s ∉ K → m (hermScal R σ s) A = 0 := by
    intro s hs
    refine measure_mono_null ?_ (hfib.1 (hermScal R σ s))
    intro X hX hXG
    apply hs
    refine ⟨X, hX, ?_⟩
    have e : gramR R σ J X = (hermScal R σ s : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) := hXG.1
    show algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) = s
    rw [e]
    exact qS_hermScal R h s
  have hcont : Continuous (fun s : R => (m (hermScal R σ s) A).toReal) := by
    rw [continuous_iff_continuousAt]
    intro s
    by_cases hs : s = 0
    · subst hs
      have hev : (fun _ : R => (0 : ℝ)) =ᶠ[𝓝 0] fun t : R => (m (hermScal R σ t) A).toReal := by
        filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hK0] with t ht
        simp [hzero t ht]
      exact continuousAt_const.congr hev
    · have hunit : hermScal R σ s ∈
          {S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det} := by
        show IsUnit (Matrix.det _)
        rw [Matrix.det_fin_one]
        exact isUnit_tmul R hs
      have hne : ∀ᶠ t in 𝓝 s, t ≠ 0 := isOpen_ne.mem_nhds hs
      have htend : Filter.Tendsto (hermScal R σ) (𝓝 s)
          (𝓝[{S : HermR R σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)).det}]
            (hermScal R σ s)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨hcs.tendsto s, hne.mono fun t ht => ?_⟩
        show IsUnit (Matrix.det _)
        rw [Matrix.det_fin_one]
        exact isUnit_tmul R ht
      have := (Complex.continuous_re.tendsto _).comp ((hg _ hunit).tendsto.comp htend)
      simpa [ContinuousAt, Function.comp_def, hint] using this
  have hsupp : HasCompactSupport (fun s : R => (m (hermScal R σ s) A).toReal) :=
    HasCompactSupport.intro hKc fun s hs => by simp [hzero s hs]
  refine ⟨hcont, hsupp, ?_⟩
  have hνeq : coordHerm R σ b lam 1 = Measure.map (hermScal R σ) lam := by
    ext T hT
    rw [Measure.map_apply hcs.measurable hT,
      ← coordHerm_qS R h htr b lam (hcs.measurable hT : MeasurableSet (hermScal R σ ⁻¹' T))]
    congr 1
    ext S
    simp [hermScal_qS R h S]
  have hgS : ∀ S, m S A = ENNReal.ofReal ((m (hermScal R σ (qS R σ S)) A).toReal) := fun S => by
    rw [hermScal_qS R h S, ENNReal.ofReal_toReal (hfin S).ne]
  have hgm : Measurable fun S : HermR R σ 1 => m S A := by
    have e : (fun S : HermR R σ 1 => m S A) =
        fun S => ENNReal.ofReal ((m (hermScal R σ (qS R σ S)) A).toReal) := funext hgS
    rw [e]
    exact ENNReal.measurable_ofReal.comp (hcont.comp (continuous_qS R htr)).measurable
  have hV : MeasurableSet ({0}ᶜ : Set R) := (measurableSet_singleton 0).compl
  have hP : MeasurableSet {S : HermR R σ 1 | qS R σ S ∈ ({0}ᶜ : Set R)} :=
    (continuous_qS R htr).measurable hV
  have hQ : MeasurableSet {X : Fin 1 → Fin M → R ⊗[F] E |
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ ({0}ᶜ : Set R)} :=
    hqc.measurable hV
  have heq := mass_eq_lintegral R h hJ hfib hAm (V := {0}ᶜ) (by simp) hQ hP
  have hAQ : A ∩ {X : Fin 1 → Fin M → R ⊗[F] E |
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (gramR R σ J X 0 0) ∈ ({0}ᶜ : Set R)} = A := by
    refine Set.inter_eq_left.mpr fun X hX e => hK0 ⟨X, hX, e⟩
  rw [hAQ, ← lintegral_indicator hP] at heq
  have hind : {S : HermR R σ 1 | qS R σ S ∈ ({0}ᶜ : Set R)}.indicator (fun S => m S A) =
      fun S => m S A := by
    funext S
    by_cases hS : S ∈ {S : HermR R σ 1 | qS R σ S ∈ ({0}ᶜ : Set R)}
    · exact Set.indicator_of_mem hS _
    · rw [Set.indicator_of_notMem hS]
      have h0 : qS R σ S = 0 := by simpa using hS
      have e : S = hermScal R σ 0 := by rw [← h0, hermScal_qS R h S]
      rw [e, hzero 0 hK0]
  rw [hind, hνeq, lintegral_map hgm hcs.measurable] at heq
  rw [ofReal_integral_eq_lintegral_ofReal (hcont.integrable_of_hasCompactSupport hsupp)
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg), heq]
  exact lintegral_congr fun s => ENNReal.ofReal_toReal (hfin _).ne

theorem fibre_masses : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ∀ A : Set (Fin 1 → Fin 2 → Fv F v ⊗[F] E), IsCompact A → IsOpen A → A ⊆ {X | IsUnit (gramR (Fv F v) σ J X).det} →
  Continuous (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  HasCompactSupport (fun s : Fv F v => (m (hermScal (Fv F v) σ s) A).toReal) ∧
  ENNReal.ofReal (∫ s, (m (hermScal (Fv F v) σ s) A).toReal ∂lam) = coordW (Fv F v) b lam 1 2 A := by
  intro F E _ _ _ _ _ σ hσ J hJ d b v lam hlam m hfib A hAc hAo hAU
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  exact masses_field (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) hσ hJ b lam hlam.1 m hfib A hAc hAo hAU

end GlobalTheory.CompanionTheory.SW.FibreCpt
end
end

section

open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StdLat

theorem fibre_masses_standard_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ContinuousOn (fun s : Fv F v => (m (hermScal (Fv F v) σ s) (latV b v)).toReal) {0}ᶜ ∧
  ∫ s, (m (hermScal (Fv F v) σ s) (latV b v)).toReal ∂lam = 1 := by
  intro F E _ _ _ _ _ σ hCM J hJ d b v lam hlam m hm
  classical
  have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v) := hloc.1
  haveI : LocallyCompactSpace (Fv F v) := hloc.2.1
  haveI : SecondCountableTopology (Fv F v) := hloc.2.2.1
  haveI : T2Space (Fv F v) := hloc.2.2.2.1
  haveI := hlam.1
  obtain ⟨-, -, -, hT2K, -, htr, -, hBorW, -, hgr⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)
  haveI := hT2K
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b lam hlam.1
  obtain ⟨hLc, hLo, -, hL1⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b 1 2 v
  obtain ⟨hSh, -, hSm⟩ := GlobalTheory.CompanionTheory.SW.hermScal_main F E σ hCM (Fv F v) d b
  haveI : BorelSpace (Fin 1 → Fin 2 → Fv F v ⊗[F] E) := hBorW 1 2
  haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩
  have hLm : MeasurableSet (latV (M := 2) (n := 1) b v) := hLo.measurableSet
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin 1 → Fin 2 → Fv F v ⊗[F] E) → ℂ,
      φ = (latV b v).indicator (fun _ => (1 : ℂ)) := ⟨_, rfl⟩
  have hcl : IsClopen (latV (M := 2) (n := 1) b v) := ⟨hLc.isClosed, hLo⟩
  have hφc : Continuous φ := by
    rw [hφ]
    exact Continuous.indicator (fun a ha => by
      rw [hcl.frontier_eq] at ha; exact absurd ha (Set.notMem_empty a)) continuous_const
  have hφs : HasCompactSupport φ := by
    rw [hφ]
    exact HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨⟨hgc, -⟩, -⟩ := GlobalTheory.T.gram_fiber_integral_isContDensityOn F E σ hCM 2 J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m (hW 1 2) (hH 1) hm φ hφc hφs
  have hval : ∀ T, ∫ X, φ X ∂(m T) = (((m T (latV b v)).toReal : ℝ) : ℂ) := fun T => by
    rw [hφ, integral_indicator_const (1 : ℂ) hLm]
    simp [Measure.real]
  have hunit : ∀ z ∈ ({0}ᶜ : Set (Fv F v)),
      hermScal (Fv F v) σ z ∈
        {S : HermR (Fv F v) σ 1 | IsUnit (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)).det} := by
    intro z hz
    show IsUnit (Matrix.det _)
    rw [Matrix.det_fin_one]
    exact FibreRatio.isUnit_tmul (Fv F v) hz
  have hcont : ContinuousOn (fun z => (m (hermScal (Fv F v) σ z) (latV b v)).toReal) {0}ᶜ := by
    have h1 := hgc.comp hSh.continuous.continuousOn hunit
    have h2 := Complex.continuous_re.comp_continuousOn h1
    refine h2.congr fun z _ => ?_
    simp [hval]
  refine ⟨hcont, ?_⟩
  have hfin : ∀ S, m S (latV b v) < ⊤ := fun S => by
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM 2 J hJ (Fv F v) hloc 1 _ _ m (hW 1 2) (hH 1) hm S).1
    exact hLc.measure_lt_top
  obtain ⟨n1, n2⟩ := GlobalTheory.T.haar_measure_nonunits_null F E σ hCM 2 J hJ (by norm_num) v (coordW (Fv F v) b lam 1 2) lam (hW 1 2) hlam.1
  have n1' : lam ({0}ᶜ : Set (Fv F v))ᶜ = 0 := by
    refine measure_mono_null (fun c hc => ?_) n1
    have : c = 0 := by simpa using hc
    simp [this]
  have hres : lam.restrict ({0}ᶜ : Set (Fv F v)) = lam :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact n1')
  have hcq : Continuous fun X : Fin 1 → Fin 2 → Fv F v ⊗[F] E =>
      algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) :=
    continuous_const.mul (htr.comp ((hgr 1 2 J).matrix_elem 0 0))
  have hVm : MeasurableSet ({0}ᶜ : Set (Fv F v)) := (measurableSet_singleton 0).compl
  have hP : MeasurableSet {S | FibreRatio.qS (Fv F v) σ S ∈ ({0}ᶜ : Set (Fv F v))} :=
    (FibreRatio.continuous_qS (Fv F v) htr).measurable hVm
  have hmass := FibreRatio.mass_eq_lintegral (Fv F v) hCM hJ hm hLm (V := {0}ᶜ) (by simp) (hcq.measurable hVm) hP
  have hconull : coordW (Fv F v) b lam 1 2 {X : Fin 1 → Fin 2 → Fv F v ⊗[F] E | algebraMap F (Fv F v) (1 / 2) *
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ ({0}ᶜ : Set (Fv F v))}ᶜ = 0 := by
    refine measure_mono_null (fun X hX => ?_) n2
    have h0 : algebraMap F (Fv F v) (1 / 2) *
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) = 0 := by simpa using hX
    intro hu
    exact hu.ne_zero h0
  rw [measure_inter_conull hconull, hL1 lam hlam, ← hSm lam hlam.1] at hmass
  have hEmb : MeasurableEmbedding (hermScal (Fv F v) σ) :=
    (hSh.homeomorph _).isClosedEmbedding.measurableEmbedding
  rw [hEmb.restrict_map, hEmb.lintegral_map] at hmass
  have hpre : hermScal (Fv F v) σ ⁻¹' {S | FibreRatio.qS (Fv F v) σ S ∈ ({0}ᶜ : Set (Fv F v))} = {0}ᶜ := by
    ext s
    simp only [Set.mem_preimage, Set.mem_setOf_eq, FibreRatio.qS_hermScal (Fv F v) hCM s]
  rw [hpre, hres] at hmass
  have hae : AEMeasurable (fun s : Fv F v => m (hermScal (Fv F v) σ s) (latV b v)) lam := by
    have h1 : AEMeasurable (fun s : Fv F v => ENNReal.ofReal (m (hermScal (Fv F v) σ s) (latV b v)).toReal)
        (lam.restrict ({0}ᶜ : Set (Fv F v))) :=
      (ENNReal.continuous_ofReal.comp_continuousOn hcont).aemeasurable hVm
    rw [hres] at h1
    refine h1.congr (Eventually.of_forall fun s => ?_)
    exact ENNReal.ofReal_toReal (hfin _).ne
  rw [integral_toReal hae (Eventually.of_forall fun s => hfin _), ← hmass]
  simp

end GlobalTheory.CompanionTheory.SW.StdLat
end
end

section

set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing


theorem _root_.GlobalTheory.T.casimir_mem_center_enveloping : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  first | exact @GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg | exact GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg | (intros; apply GlobalTheory.CompanionTheory.Inh.CapelliCasimir.cas_mem_Zalg <;> assumption)
end
