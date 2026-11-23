module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import Mathlib.Probability.Kernel.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityContinuous
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle046
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle605
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle609
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle607
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle405
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushLF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.GramMapFibreExistence
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle009
import GroundTheory.AutomorphicForms.GLnLocal
import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle610
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle611
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitalSignAlmostEverywhere
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Probability.Kernel.Basic
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle452
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.IsTransl

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF

theorem isSFiniteKernel_of_compact_open {α β : Type} [MeasurableSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] [T2Space β] (κ : ProbabilityTheory.Kernel α β)
    {K : ℕ → Set β} (hK : ∀ k, IsCompact (K k)) {U : Set β} (hU : (⋃ k, K k) = U)
    (hc : ∀ a, κ a Uᶜ = 0) (hf : ∀ a k, κ a (K k) < ⊤) : ProbabilityTheory.IsSFiniteKernel κ := by
  let C : ℕ → Set β := disjointed K
  have hCm : ∀ k, MeasurableSet (C k) := fun k =>
    MeasurableSet.disjointed (fun i => (hK i).measurableSet) k
  have hCd : Pairwise (Function.onFun Disjoint C) := disjoint_disjointed _
  have hCu : ⋃ k, C k = U := by
    simp only [C, iUnion_disjointed]
    exact hU
  have hk : ∀ k, ProbabilityTheory.IsSFiniteKernel (ProbabilityTheory.Kernel.restrict κ (hCm k)) := fun k =>
    isSFiniteKernel_of_forall_univ_lt_top _ (fun a => by
      rw [ProbabilityTheory.Kernel.restrict_apply]
      simpa using (measure_mono (disjointed_subset _ k)).trans_lt (hf a k))
  have hsum : κ = ProbabilityTheory.Kernel.sum fun k => ProbabilityTheory.Kernel.restrict κ (hCm k) := by
    ext a s hs
    rw [ProbabilityTheory.Kernel.sum_apply]
    simp only [ProbabilityTheory.Kernel.restrict_apply]
    rw [← Measure.restrict_iUnion hCd hCm, hCu,
      Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 (hc a))]
  rw [hsum]
  infer_instance

theorem gramFibFree_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N n : ℕ) (J₂ : Matrix (Fin N) (Fin N) E), IsHermND σ J₂ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m : HermR R σ n → Measure (Fin n → Fin N → R ⊗[F] E), IsGramFibFree R σ J₂ n (coordW R b lam n N) (coordHerm R σ b lam n) m → (∀ S, SFinite (m S)) ∧ (∃ κ : ProbabilityTheory.Kernel (HermR R σ n) (Fin n → Fin N → R ⊗[F] E), ProbabilityTheory.IsSFiniteKernel κ ∧ ∀ S, κ S = m S) ∧ (∀ (C : Set (Fin n → Fin N → R ⊗[F] E)) (D : Set (HermR R σ n)), IsCompact C → C ⊆ {X | LinearIndependent (R ⊗[F] E) X} → IsCompact D → ∃ c : ℝ≥0, ∀ S ∈ D, m S C ≤ c) ∧ ∀ S : HermR R σ n, ∀ᵐ X ∂(m S), gramR R σ J₂ X = (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) ∧ LinearIndependent (R ⊗[F] E) X := by
  intro F E _ _ _ _ _ σ hCM N n J₂ hJ R _ _ _ _ _ hR d b lam hlam m hm
  obtain ⟨iTR, iLC, iSC, iT2, -⟩ := id hR
  haveI := iTR; haveI := iLC; haveI := iSC; haveI := iT2
  obtain ⟨kTR, kLC, kSC, kT2, -, -, -, kB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := kTR; haveI := kLC; haveI := kSC; haveI := kT2
  haveI := kB n N
  obtain ⟨hLC, hSC, hT2, hB, -⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hCM R n
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB
  have hU : IsOpen {X : Fin n → Fin N → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
    GlobalTheory.T.linearly_independent_frames_open F E σ hCM R hR n N
  obtain ⟨h1, -, h3⟩ := hm
  have hbf : GlobalTheory.CompanionTheory.SW.FibreFam.BumpFamily {X : Fin n → Fin N → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}
      (Set.univ : Set (HermR R σ n)) m :=
    ⟨fun S hS => absurd (Set.mem_univ S) hS, h3⟩
  have hUc : ∀ S, m S {X : Fin n → Fin N → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X}ᶜ = 0 := fun S =>
    measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_right) (h1 S)
  have hmeas : ∀ A : Set (Fin n → Fin N → R ⊗[F] E), MeasurableSet A → Measurable fun S => m S A :=
    fun A hA => hbf.measurable_apply isOpen_univ hU hUc hA
  let κ : ProbabilityTheory.Kernel (HermR R σ n) (Fin n → Fin N → R ⊗[F] E) :=
    ⟨m, Measure.measurable_of_measurable_coe _ hmeas⟩
  obtain ⟨K, W, hK, -, -, hKU, -, -, hKun, -⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_exhaustion hU
  haveI hκ : ProbabilityTheory.IsSFiniteKernel κ :=
    isSFiniteKernel_of_compact_open κ hK hKun hUc
      (fun S k => hbf.lt_top hU (hK k) (hKU k) S)
  refine ⟨fun S => (inferInstance : SFinite (κ S)), ⟨κ, hκ, fun _ => rfl⟩, ?_, fun S => ?_⟩
  · intro C D hC hCU hD
    obtain ⟨φ, hc, hcs, hs, h0, -, hone⟩ := GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump hC hU hCU
    obtain ⟨hi, hco⟩ := h3 φ hc hcs hs
    obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn (hco.mono (Set.subset_univ D))
    refine ⟨M.toNNReal, fun S hS => ?_⟩
    calc m S C ≤ ∫⁻ v, ENNReal.ofReal (φ v) ∂(m S) :=
          GlobalTheory.CompanionTheory.SW.FibreFam.le_lintegral_bump _ hC h0 hone
      _ = ENNReal.ofReal (∫ v, φ v ∂(m S)) :=
          (ofReal_integral_eq_lintegral_ofReal (hi S (Set.mem_univ S))
            (Filter.Eventually.of_forall h0)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM S hS))
      _ = (M.toNNReal : ℝ≥0∞) := rfl
  · have : ∀ᵐ X ∂(m S), X ∈ gramR R σ J₂ ⁻¹' {((S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E))} ∩
        {X : Fin n → Fin N → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} :=
      mem_ae_iff.2 (h1 S)
    filter_upwards [this] with X hX
    exact ⟨hX.1, hX.2⟩

end GlobalTheory.CompanionTheory.SW.StageF
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.schwartz_function_schwartz_bruhat : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m r : ℕ) (φ : Mx D m r → ℂ), φ ∈ schwartzA θ m r →
  GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) (fun X : Fin r → Fin m → AE D => φ (tupOf X)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.isSchwartzBruhat_tupOf_of_mem_schwartzA | exact GlobalTheory.CompanionTheory.SiegelND.isSchwartzBruhat_tupOf_of_mem_schwartzA | (intros; apply GlobalTheory.CompanionTheory.SiegelND.isSchwartzBruhat_tupOf_of_mem_schwartzA <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ} (d : HypDec B W t)

theorem mt_decomp_j0 (c : skewA D t) (b : Mx D t W.rank) (g : GA D W) (a : GL (Fin t) (AE D)) :
    mt B (d.nC c * d.nB b * (d.emb0 g * d.levi a)) ⬝ d.j0 = (d.j0 + d.jX ⬝ b) ⬝ mt W g := by
  have e : mt B (d.nC c * d.nB b * (d.emb0 g * d.levi a)) =
      mt B (d.nC c) ⬝ (mt B (d.nB b) ⬝ (mt B (d.emb0 g) ⬝ mt B (d.levi a))) := by
    simp only [mt_mul, Matrix.mul_assoc]
  have e₁ : mt B (d.emb0 g) ⬝ mt B (d.levi a) ⬝ d.j0 = d.j0 ⬝ mt W g := by
    rw [Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  have e₂ : mt B (d.nC c) ⬝ (d.j0 + d.jX ⬝ b) = d.j0 + d.jX ⬝ b := by
    rw [Matrix.mul_add, d.nC_j0, ← Matrix.mul_assoc, d.nC_jX]
  rw [e, Matrix.mul_assoc, Matrix.mul_assoc, e₁, ← Matrix.mul_assoc (mt B (d.nB b)), d.nB_j0,
    ← Matrix.mul_assoc, e₂]

theorem mt_decomp_jY (c : skewA D t) (g : GA D W) (a : GL (Fin t) (AE D)) :
    mt B (d.nC c * (d.emb0 g * d.levi a)) ⬝ d.jY = (d.jY + d.jX ⬝ c.1) ⬝ adj (a⁻¹).1 := by
  have e : mt B (d.nC c * (d.emb0 g * d.levi a)) = mt B (d.nC c) ⬝ (mt B (d.emb0 g) ⬝ mt B (d.levi a)) := by
    simp only [mt_mul]
  have e₁ : mt B (d.emb0 g) ⬝ mt B (d.levi a) ⬝ d.jY = d.jY ⬝ adj (a⁻¹).1 := by
    rw [Matrix.mul_assoc, d.levi_jY, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclY]
  rw [e, Matrix.mul_assoc, e₁, ← Matrix.mul_assoc, d.nC_jY]

theorem coordB_eq_zero (c : skewA D t) (b : Mx D t W.rank) (g : GA D W) (a : GL (Fin t) (AE D))
    (h : d.pX ⬝ mt B (d.nC c * d.nB b * (d.emb0 g * d.levi a)) ⬝ d.j0 = 0) : b = 0 := by
  rw [Matrix.mul_assoc, mt_decomp_j0, ← Matrix.mul_assoc, Matrix.mul_add, d.pX_j0, ← Matrix.mul_assoc,
    d.pX_jX, Matrix.one_mul, zero_add] at h
  have e : mt W g ⬝ mt W g⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  calc b = b ⬝ mt W g ⬝ mt W g⁻¹ := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
    _ = 0 := by rw [h, Matrix.zero_mul]

theorem coordC_eq_zero (c : skewA D t) (g : GA D W) (a : GL (Fin t) (AE D))
    (h : d.pX ⬝ mt B (d.nC c * (d.emb0 g * d.levi a)) ⬝ d.jY = 0) : c = 0 := by
  rw [Matrix.mul_assoc, mt_decomp_jY, ← Matrix.mul_assoc, Matrix.mul_add, d.pX_jY, ← Matrix.mul_assoc,
    d.pX_jX, Matrix.one_mul, zero_add] at h
  have e : adj (a⁻¹).1 ⬝ adj a.1 = 1 := by rw [← adj_mul, Units.mul_inv, adj_one]
  apply Subtype.ext
  calc c.1 = c.1 ⬝ adj (a⁻¹).1 ⬝ adj a.1 := by rw [Matrix.mul_assoc, e, Matrix.mul_one]
    _ = 0 := by rw [h, Matrix.zero_mul]

theorem pX_levM {q : GlobalTheory.RegSW.stab d} (hq : q ∈ levM d) :
    d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0 ∧ d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0 := by
  obtain ⟨g, a, h⟩ := hq
  rw [h, mt_mul]
  constructor
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_projX_anisotropicEmbedding, d.pX_j0]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, d.levi_jY, ← Matrix.mul_assoc (mt B (d.emb0 g)), d.wittDecomp_anisotropicEmbedding_inclY,
      ← Matrix.mul_assoc, d.pX_jY, Matrix.zero_mul]

theorem mem_levM_of_pX {q : GlobalTheory.RegSW.stab d} (h₀ : d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0)
    (hY : d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0) : q ∈ levM d := by
  obtain ⟨n, ⟨c, b, hn⟩, m, ⟨g, a, hm⟩, e⟩ := exists_radN_mul_levM d q
  have hq : (q : GA D B) = d.nC c * d.nB b * (d.emb0 g * d.levi a) := by
    rw [e, Subgroup.coe_mul, hn, hm]
  rw [hq] at h₀ hY
  have hb := coordB_eq_zero d c b g a h₀
  subst hb
  rw [d.nB_zero, mul_one] at hY
  have hc := coordC_eq_zero d c g a hY
  subst hc
  refine (mem_levM d).2 ⟨g, a, hq.trans ?_⟩
  rw [d.nC_zero, d.nB_zero, one_mul, one_mul]

theorem isClosed_levM (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) :
    IsClosed (levM d : Set (GlobalTheory.RegSW.stab d)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  haveI := t2Space_tensorProduct_finiteExtension (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hc : Continuous fun q : GlobalTheory.RegSW.stab d => mt B (q : GA D B) :=
    (continuous_mt B).comp continuous_subtype_val
  have h₀ : IsClosed {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0} :=
    isClosed_eq ((continuous_const.matrix_mul hc).matrix_mul continuous_const) continuous_const
  have hY : IsClosed {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0} :=
    isClosed_eq ((continuous_const.matrix_mul hc).matrix_mul continuous_const) continuous_const
  have e : (levM d : Set (GlobalTheory.RegSW.stab d)) = {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.j0 = 0} ∩
      {q : GlobalTheory.RegSW.stab d | d.pX ⬝ mt B (q : GA D B) ⬝ d.jY = 0} :=
    Set.ext fun q => ⟨fun h => pX_levM d h, fun h => mem_levM_of_pX d h.1 h.2⟩
  rw [e]
  exact h₀.inter hY

end GlobalTheory.CompanionTheory.QKAvg
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

variable {D : D7} {B W : HSp D} {t : ℕ}

theorem mt_mul_frame {k : ℕ} (x y : GA D B) (J : Mx D B.rank k) :
    mt B (x * y) ⬝ J = mt B x ⬝ (mt B y ⬝ J) := by
  rw [← Matrix.mul_assoc, GlobalTheory.MixModel.mt_mul]

theorem levi_part_eq_one (d : HypDec B W t) {c : skewA D t} {b : Mx D t W.rank} {g : GA D W}
    {a : GL (Fin t) (AE D)} (e : d.nC c * d.nB b = d.emb0 g * d.levi a) : a = 1 := by
  have h : mt B (d.nC c * d.nB b) ⬝ d.jX = mt B (d.emb0 g * d.levi a) ⬝ d.jX := by rw [e]
  rw [mt_mul_frame, mt_mul_frame, d.nB_jX, d.nC_jX, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX] at h
  apply Units.ext
  have h' : d.pX ⬝ d.jX = d.pX ⬝ (d.jX ⬝ a.1) := congrArg (fun M => d.pX ⬝ M) h
  rw [← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at h'
  exact h'.symm

theorem unitary_part_eq_one (d : HypDec B W t) {c : skewA D t} {b : Mx D t W.rank} {g : GA D W}
    (e : d.nC c * d.nB b = d.emb0 g * d.levi 1) : g = 1 := by
  have h : mt B (d.nC c * d.nB b) ⬝ d.j0 = mt B (d.emb0 g * d.levi 1) ⬝ d.j0 := by rw [e]
  rw [mt_mul_frame, mt_mul_frame, d.nB_j0, d.wittDecomp_levi_inclAnisotropic, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, Matrix.mul_add, d.nC_j0,
    ← Matrix.mul_assoc, d.nC_jX] at h
  have h' : d.p0 ⬝ (d.j0 + d.jX ⬝ b) = d.p0 ⬝ (d.j0 ⬝ mt W g) := congrArg (fun M => d.p0 ⬝ M) h
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d.p0_j0, d.p0_jX, Matrix.zero_mul,
    add_zero, Matrix.one_mul] at h'
  apply GlobalTheory.MixModel.mt_injective
  rw [← h', GlobalTheory.MixModel.mt_one]

theorem radN_disj_levM : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t),
    ∀ x, x ∈ radN d → x ∈ levM d → x = 1 := by
  intro D B W t d x hn hm
  obtain ⟨c, b, hx⟩ := (mem_radN d).1 hn
  obtain ⟨g, a, hy⟩ := (mem_levM d).1 hm
  have e : d.nC c * d.nB b = d.emb0 g * d.levi a := hx.symm.trans hy
  have ha := levi_part_eq_one d e
  subst ha
  have hg := unitary_part_eq_one d e
  subst hg
  have h1 : d.emb0 1 * d.levi 1 = 1 := by rw [map_one, map_one, mul_one]
  exact Subtype.ext (hy.trans h1)

end GlobalTheory.CompanionTheory.QKAvg
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt

open GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale

theorem exists_scale_cover {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (C : Set (Fin n → Fin M → Fv F v ⊗[F] E)) (hC : IsCompact C) :
    ∃ (c : F) (hc : c ≠ 0), C ⊆ latV (scaleB b c hc) v := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  set p : Fv F v := algebraMap F (Fv F v) π with hp
  have hval : Valued.v p = WithZero.exp (-1 : ℤ) := by
    have h0 : Valued.v (algebraMap F (Fv F v) π) = v.valuation F π :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v π
    rw [hp, h0, hπ]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hlt : Valued.v p < 1 := by
    rw [hval]
    decide
  have hpO : p ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hlt.le
  have hnorm : ‖p‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 hlt
  have hlim : Filter.Tendsto (fun k : ℕ => p ^ k) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
  have hOopen : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Valued.isOpen_valuationSubring _
  have hmem : ∀ (k : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E),
      X ∈ latV (scaleB b (π ^ k) (pow_ne_zero k hπ0)) v ↔
        ∀ a i l, p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l ∈
          v.adicCompletionIntegers F := by
    intro k X
    simp only [latV, Set.mem_setOf_eq, repr_scaleB, map_pow, hp]
  let U : ℕ → Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
    fun k => latV (scaleB b (π ^ k) (pow_ne_zero k hπ0)) v
  have hUo : ∀ k, IsOpen (U k) := fun k =>
    (((GlobalTheory.T.adelic_tuple_projections F E σ hcm d (scaleB b (π ^ k) (pow_ne_zero k hπ0)) n M).2.2.2.1 v).2)
  have hcov : C ⊆ ⋃ k, U k := by
    intro X _
    have h1 : ∀ a i l, ∀ᶠ k : ℕ in Filter.atTop,
        p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l ∈
          (v.adicCompletionIntegers F : Set (Fv F v)) := by
      intro a i l
      have h2 : Filter.Tendsto
          (fun k : ℕ => p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l)
          Filter.atTop (𝓝 0) := by
        simpa using hlim.mul_const ((Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l)
      exact h2 (hOopen.mem_nhds (zero_mem _))
    have h3 : ∀ᶠ k : ℕ in Filter.atTop, ∀ a i l,
        p ^ k * (Algebra.TensorProduct.basis (Fv F v) b).repr (X a i) l ∈
          (v.adicCompletionIntegers F : Set (Fv F v)) :=
      Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i =>
        Filter.eventually_all.2 fun l => h1 a i l
    obtain ⟨k, hk⟩ := h3.exists
    exact Set.mem_iUnion.2 ⟨k, (hmem k X).2 hk⟩
  have hmono : Monotone U := monotone_nat_of_le_succ fun k X hX => by
    refine (hmem (k + 1) X).2 fun a i l => ?_
    have h := (hmem k X).1 hX a i l
    rw [pow_succ', mul_assoc]
    exact mul_mem hpO h
  obtain ⟨k, hk⟩ := hC.elim_directed_cover U hUo hcov hmono.directed_le
  exact ⟨π ^ k, pow_ne_zero k hπ0, hk⟩

theorem fibre_compact_lt_top : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), SWFree σ J T hT → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (m : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) m → ∀ C : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact C → m (hermOf (Fv F v) σ T hT) C < ⊤ := by
  intro F E _ _ _ _ _ σ hcm M J hJ n T hT hSW d b laminf lam hinf hv v m hm C hC
  classical
  obtain ⟨c, hc, hCc⟩ := exists_scale_cover σ hcm b n M v C hC
  set b' := scaleB b c hc with hb'
  have hrV : ∀ w, IsLocR (Fv F w) := GlobalTheory.T.completion_is_local_ring F
  haveI : ∀ w, BorelSpace (Fv F w) := fun _ => ⟨rfl⟩
  obtain ⟨k, hk0, hk⟩ := coord_rescale σ hcm J (Fv F v) (hrV v) b b' (lam v) (hv v).1 n m hm
  have hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨-, hWi, hHi⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Ainf F) _ b' laminf hinf.1
  obtain ⟨minf, hminf⟩ := GlobalTheory.T.exists_fibreMeasures_archimedeanGramMap F E σ hcm M n J hJ (coordW (Ainf F) b' laminf n M)
    (coordHerm (Ainf F) σ b' laminf n) (hWi n M) (hHi n)
  have hfV : ∀ w : HeightOneSpectrum (𝓞 F), ∃ fib : HermR (Fv F w) σ n → Measure (Fin n → Fin M → Fv F w ⊗[F] E),
      IsGramFibFree (Fv F w) σ J n (coordW (Fv F w) b' (lam w) n M) (coordHerm (Fv F w) σ b' (lam w) n) fib := fun w => by
    have := PI.VolStabS.secondCountable_Fv F w
    have := PI.VolStabS.locallyCompact_Fv F w
    obtain ⟨-, hWv, hHv⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F w) _ b' (lam w) (hv w).1
    exact PI.OmFibreUniq.W.gram_map_fibre_existence σ J w n hcm hJ _ _ (hWv n M) (hHv n)
  choose m₀ hm₀ using hfV
  let m₂ : ∀ w : HeightOneSpectrum (𝓞 F), HermR (Fv F w) σ n → Measure (Fin n → Fin M → Fv F w ⊗[F] E) :=
    Function.update m₀ v (fun S => k • m S)
  have hm₂v : m₂ v = fun S => k • m S := Function.update_self _ _ _
  have hm₂ : ∀ w, IsGramFibFree (Fv F w) σ J n (coordW (Fv F w) b' (lam w) n M)
      (coordHerm (Fv F w) σ b' (lam w) n) (m₂ w) := fun w => by
    by_cases h : w = v
    · subst h
      rw [hm₂v]
      exact hk
    · have : m₂ w = m₀ w := Function.update_of_ne h _ _
      rw [this]
      exact hm₀ w
  obtain ⟨⟨μ₁, hμ₁⟩, hFV⟩ := GlobalTheory.T.unitary_group_finite_volume F E σ hcm M J hJ
  obtain ⟨⟨𝓕₁, h𝓕₁⟩, -⟩ := hFV μ₁ hμ₁
  have hE := hSW d b' laminf lam hinf hv μ₁ 𝓕₁ hμ₁ h𝓕₁ minf m₂ hminf hm₂
  have h1 : (k • m (hermOf (Fv F v) σ T hT)) (latV b' v) < ⊤ := by
    have h2 : m₂ v (hermOf (Fv F v) σ T hT) (latV b' v) < ⊤ := hE.1 v
    rwa [hm₂v] at h2
  have h3 : m (hermOf (Fv F v) σ T hT) (latV b' v) < ⊤ := by
    by_contra hx
    have hs : (k • m (hermOf (Fv F v) σ T hT)) (latV b' v) =
        (k : ℝ≥0∞) * m (hermOf (Fv F v) σ T hT) (latV b' v) := by
      rw [Measure.smul_apply]
      rfl
    rw [hs, not_lt_top_iff.1 hx, ENNReal.mul_top (by exact_mod_cast hk0)] at h1
    exact lt_irrefl _ h1
  exact (measure_mono hCc).trans_lt h3

end GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt
end
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coefficient_data_exists : PositivityTheory.PfSWUS.CoefDataExists := by
  first | exact @GlobalTheory.CompanionTheory.SWCoef.coefDataExists | exact GlobalTheory.CompanionTheory.SWCoef.coefDataExists | (intros; apply GlobalTheory.CompanionTheory.SWCoef.coefDataExists <;> assumption)
end
end

section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

theorem _root_.GlobalTheory.T.twisted_orbital_pair_convolution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (σ : H →* H) (K : Subgroup H),
  Continuous σ → (∀ g, σ (σ g) = g) → (∀ k ∈ K, σ k ∈ K) → IsOpen (K : Set H) → IsCompact (K : Set H) → ∀ (d d' : H) (f₁ f₂ : H → ℂ) (K' : Subgroup H),
  IsOpen (K' : Set H) → K' ≤ K → (∀ k ∈ K', σ k ∈ K') → IsHecke K' f₁ → IsHecke K' f₂ →
  Good (MonoidHom.id H) K (d * σ d') →
  (∀ C : Set H, IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) (d * σ d') : Set H) (K : Set H) |
    ∃ k ∈ K, (Quotient.out q * k)⁻¹ * (d * σ d') * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
  twOrb ((MonoidHom.prodMap σ σ).comp (MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (K.prod K) (d, d') (fun y => f₁ y.1 * f₂ (σ y.2)) =
    twOrb (MonoidHom.id H) K (d * σ d') (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  first | exact @GlobalTheory.CompanionTheory.SplitConvF.splitConv_of_finite | exact GlobalTheory.CompanionTheory.SplitConvF.splitConv_of_finite | (intros; apply GlobalTheory.CompanionTheory.SplitConvF.splitConv_of_finite <;> assumption)
end

section


theorem _root_.GlobalTheory.T.rational_finite_places : PositivityTheory.Rg.BcB.G8.Fin.RatFin := by
  first | exact @GlobalTheory.CompanionTheory.RatFinG.ratFin | exact GlobalTheory.CompanionTheory.RatFinG.ratFin | (intros; apply GlobalTheory.CompanionTheory.RatFinG.ratFin <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2

theorem _root_.GlobalTheory.T.orbital_sign_almost_everywhere : KapOrbAE := by
  first | exact @GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE | exact GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE | (intros; apply GlobalTheory.CompanionTheory.KapOrbAE.kapOrbAE <;> assumption)
end
