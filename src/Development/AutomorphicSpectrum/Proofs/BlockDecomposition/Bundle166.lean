module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle037
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramDensity
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ArchSliceUAction
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistedKernel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Mathlib.Algebra.Algebra.ZMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle153
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorNonscalarOffdiag
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle154
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.DensInt

theorem exists_cutoff (V : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] :
    ∃ χ : ℕ → V → ℝ, (∀ k, Continuous (χ k)) ∧ (∀ k, HasCompactSupport (χ k)) ∧
      (∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1) ∧ ∀ x, ∀ᶠ k in Filter.atTop, χ k x = 1 := by
  have h : ∀ k : ℕ, ∃ f : C(V, ℝ), Set.EqOn f 1 (compactCovering V k) ∧ Set.EqOn f 0 (∅ : Set V) ∧
      HasCompactSupport f ∧ ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := fun k =>
    exists_continuous_one_zero_of_isCompact (isCompact_compactCovering V k) isClosed_empty
      (Set.disjoint_empty _)
  choose f h1 _ h3 h4 using h
  refine ⟨fun k => f k, fun k => (f k).continuous, h3, fun k x => h4 k x, fun x => ?_⟩
  obtain ⟨k₀, hk₀⟩ := exists_mem_compactCovering x
  filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
  exact h1 k (compactCovering_subset V hk hk₀)

theorem density_limit {V X Y : Type} [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (f : V → Y) (ι : X → Y)
    (B : Set X) (m : X → Measure V)
    (H : ∀ ψ : V → ℂ, Continuous ψ → HasCompactSupport ψ →
      HeckeCharacterZeroLocus.SiegelWeilU.IsContDensityOn μ f ι ν B ψ (fun S => ∫ x, ψ x ∂(m S)) ∧ ∀ S, Integrable ψ (m S))
    (φ : V → ℂ) (hφc : Continuous φ) (hφ : Integrable φ μ) (hφS : ∀ S ∈ B, Integrable φ (m S))
    (hD : ContinuousOn (fun S => ∫ x, ‖φ x‖ ∂(m S)) B) (K : Set X) (hK : IsCompact K) (hKB : K ⊆ B) :
    ∫ v in f ⁻¹' (ι '' K), φ v ∂μ = ∫ b in K, (∫ x, φ x ∂(m b)) ∂ν := by
  obtain ⟨χ, hχc, hχs, hχb, hχ1⟩ := exists_cutoff V
  set ψ : ℕ → V → ℂ := fun k x => φ x * (χ k x : ℂ) with hψ
  have hψc : ∀ k, Continuous (ψ k) := fun k =>
    hφc.mul (Complex.continuous_ofReal.comp (hχc k))
  have hψs : ∀ k, HasCompactSupport (ψ k) := fun k => by
    have : HasCompactSupport (fun x => (χ k x : ℂ)) := (hχs k).comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    exact this.mul_left
  have hψn : ∀ k x, ‖ψ k x‖ ≤ ‖φ x‖ := fun k x => by
    simp only [hψ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχb k x).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hχb k x).2
  have hψl : ∀ x, Filter.Tendsto (fun k => ψ k x) Filter.atTop (𝓝 (φ x)) := fun x => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hχ1 x] with k hk
    simp [hψ, hk]
  have hmeas : ∀ k (ρ : Measure V), AEStronglyMeasurable (ψ k) ρ := fun k ρ =>
    (hψc k).aestronglyMeasurable

  have hL : Filter.Tendsto (fun k => ∫ v in f ⁻¹' (ι '' K), ψ k v ∂μ) Filter.atTop
      (𝓝 (∫ v in f ⁻¹' (ι '' K), φ v ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖φ x‖) (fun k => hmeas k _) hφ.norm.integrableOn
      (fun k => Filter.Eventually.of_forall (hψn k)) (Filter.Eventually.of_forall hψl)

  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ S ∈ K, ‖∫ x, ‖φ x‖ ∂(m S)‖ ≤ C :=
    hK.exists_bound_of_continuousOn (hD.mono hKB)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hR : Filter.Tendsto (fun k => ∫ b in K, (∫ x, ψ k x ∂(m b)) ∂ν) Filter.atTop
      (𝓝 (∫ b in K, (∫ x, φ x ∂(m b)) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun k => ?_) ?_ (fun k => ?_) ?_
    · exact ((H _ (hψc k) (hψs k)).1.1.mono hKB).aestronglyMeasurable hKm
    · haveI : IsFiniteMeasure (ν.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := ν)⟩
      exact integrable_const _
    · refine (ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun S hS => ?_)
      calc ‖∫ x, ψ k x ∂(m S)‖ ≤ ∫ x, ‖ψ k x‖ ∂(m S) := norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖φ x‖ ∂(m S) := integral_mono ((H _ (hψc k) (hψs k)).2 S).norm (hφS S (hKB hS)).norm (hψn k)
        _ ≤ ‖∫ x, ‖φ x‖ ∂(m S)‖ := Real.le_norm_self _
        _ ≤ C := hC S hS
    · refine (ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun S hS => ?_)
      exact tendsto_integral_of_dominated_convergence (fun x => ‖φ x‖) (fun k => hmeas k _)
        (hφS S (hKB hS)).norm (fun k => Filter.Eventually.of_forall (hψn k))
        (Filter.Eventually.of_forall hψl)
  refine tendsto_nhds_unique hL (hR.congr fun k => ?_)
  exact ((H _ (hψc k) (hψs k)).1.2 K hK hKB).symm



theorem density_identity_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)) (m : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Ainf F) σ J n μ ν m → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous φ → Integrable φ μ → (∀ S : HermR (Ainf F) σ n, IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → Integrable φ (m S)) → ContinuousOn (fun S => ∫ X, ‖φ X‖ ∂(m S)) {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} → ∀ K : Set (HermR (Ainf F) σ n), IsCompact K → K ⊆ {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} → ∫ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' K), φ X ∂μ = ∫ S in K, (∫ X, φ X ∂(m S)) ∂ν := by
  intro F E _ _ _ _ _ σ hσ M J hJ n μ ν m hμ hν hfib φ hφc hφ hφS hD K hK hKB
  have hR : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI := iB n M
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) n
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  exact density_limit μ ν (gramR (Ainf F) σ J) Subtype.val _ m
    (fun ψ h1 h2 => GlobalTheory.CompanionTheory.SW.GramDensity.isContDensityOn_gram F E σ hσ M J hJ (Ainf F) hR n μ ν m hμ hν hfib ψ h1 h2)
    φ hφc hφ hφS hD K hK hKB

end GlobalTheory.CompanionTheory.SW.DensInt
end

section

open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.archimedean_binary_gram_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)), IsStdInf li →
  ∀ (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 2 → Ainf F ⊗[F] E)),
  IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 2) (coordHerm (Ainf F) σ b li 1) mi →
  ∀ φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → (∀ X, 0 ≤ φ X) →
  tsupport φ ⊆ {X | IsUnit (gramR (Ainf F) σ J X).det} →
  Continuous (fun s : Ainf F => ∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) ∧
  HasCompactSupport (fun s : Ainf F => ∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) ∧
  (∀ s : Ainf F, ∫⁻ X, ENNReal.ofReal (φ X) ∂(mi (hermScal (Ainf F) σ s)) = ENNReal.ofReal (∫ X, φ X ∂(mi (hermScal (Ainf F) σ s)))) ∧
  ENNReal.ofReal (∫ s, (∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) ∂li) = ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 2) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral_test | exact GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral_test | (intros; apply GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral_test <;> assumption)
end

section

set_option maxSynthPendingDepth 1

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open IsDedekindDomain
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.ArchSmooth

open AutomorphicForm

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

def cMap : mixedEmbedding.mixedSpace E →ₗ[ℝ] Cinf E where
  toFun z := fun w => z.2 ⟨w, IsTotallyComplex.isComplex w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cMap_ringEquiv (x : InfiniteAdeleRing E) :
    cMap E (InfiniteAdeleRing.ringEquiv_mixedSpace E x) = (infEq E).symm x := by
  funext w
  change (InfiniteAdeleRing.ringEquiv_mixedSpace E x).2 ⟨w, IsTotallyComplex.isComplex w⟩ = _
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  rfl

def mMap : ArchMatrix E a →ₗ[ℝ] Lie E a where
  toFun x := fun i j => cMap E ((x : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)) i j)
  map_add' x y := by
    funext i j
    exact map_add (cMap E) _ _
  map_smul' c x := by
    funext i j
    exact map_smul (cMap E) c _

def toGL (u : archGroup E a) : GL (Fin a) (Cinf E) :=
  Matrix.GeneralLinearGroup.map (infEq E).symm.toRingHom ((archEquiv E a).symm u)

theorem toL_toGL (u : archGroup E a) :
    toL (toGL E a u).val = mMap E a ((u : (ArchMatrix E a)ˣ) : ArchMatrix E a) := by
  obtain ⟨b, rfl⟩ := (archEquiv E a).surjective u
  funext i j
  simp only [toGL, ContinuousMulEquiv.symm_apply_apply]
  exact (cMap_ringEquiv E (b i j)).symm

theorem infEmb_eq (u : archGroup E a) : infEmb E a u = infGL E a (toGL E a u) := by
  apply ga_ext
  · rw [pInf_infGL]
    ext i j : 2
    have h := congrArg (fun p => (p.1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j) (prodEquiv_infEmb u)
    exact congrArg (infEq E).symm h
  · rw [pFin_infGL]
    ext i j : 2
    exact congrArg (fun p => (p.2 : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)) i j) (prodEquiv_infEmb u)

theorem archSlice_eq (φ : GA E a → ℂ) (g : GA E a) (u : archGroup E a) :
    archSlice φ g u = chart φ g (mMap E a ((u : (ArchMatrix E a)ˣ) : ArchMatrix E a)) := by
  rw [← toL_toGL, chart_val, archSlice_apply, infEmb_eq]

theorem sm_mem_archSmooth (φ : Sm E a) : φ.1 ∈ AutomorphicForm.archSmooth E a := by
  intro g
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro g'
  let L : ArchMatrix E a →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap (mMap E a)
  let c : ArchMatrix E a := ((g' : (ArchMatrix E a)ˣ) : ArchMatrix E a)
  let F : archLie E a → ArchMatrix E a := fun Y => c * NormedSpace.exp (Y : ArchMatrix E a)
  have hF : ContDiff ℝ ∞ F :=
    contDiff_const.mul ((contDiff_exp ℝ (ArchMatrix E a)).comp (archLie E a).subtypeL.contDiff)
  have hs : ContDiff ℝ ∞ fun Y => L (F Y) := L.contDiff.comp hF
  have hmem : ∀ Y, L (F Y) ∈ invSet E a := fun Y => by
    have : L (F Y) = toL (toGL E a (g' * (isExpLieAlgebra E a).expG Y)).val := (toL_toGL E a (g' * (isExpLieAlgebra E a).expG Y)).symm
    rw [this]
    exact val_mem_invSet _
  have hc := (φ.2 g).comp_contDiff hs hmem
  have e : (fun Y : archLie E a => archSlice φ.1 g (g' * (isExpLieAlgebra E a).expG Y)) =
      chart φ.1 g ∘ fun Y => L (F Y) :=
    funext fun Y => archSlice_eq E a φ.1 g _
  change ContDiff ℝ ∞ (fun Y : archLie E a => archSlice φ.1 g (g' * (isExpLieAlgebra E a).expG Y))
  rw [e]
  exact hc

end GlobalTheory.CompanionTheory.ArchSmooth
end
end

section

open GlobalTheory.PRep

theorem _root_.GlobalTheory.T.compact_induction_twisted_kernel : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (H U : Subgroup G) [U.Normal], U ≤ H → (∀ O : Set G, O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) → ∀ (σ : Representation ℂ H W), IsSmooth σ → ∀ f : cIndSpace H σ, (∀ g, f.1.1.1 g ∈ twKer σ (U.subgroupOf H) 1) → f ∈ twKer (cInd H σ) U 1 := by
  first | exact @GlobalTheory.CompanionTheory.PRep.CIndKer.mem_twKer_cInd | exact GlobalTheory.CompanionTheory.PRep.CIndKer.mem_twKer_cInd | (intros; apply GlobalTheory.CompanionTheory.PRep.CIndKer.mem_twKer_cInd <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

variable {R : Type} [CommRing R] {X : Scheme.{0}}

abbrev ext (s : X ⟶ Sp R) (J : Ideal R) (U : X.Opens) : Ideal Γ(X, U) :=
  J.map (GlobalTheory.SmallExtLift.cst s U)

def tr (M : LB X) {A : Type} (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (a b : A) :
    Γ(X, V a ⊓ V b) :=
  rs X (inf_le_inf (hj a) (hj b)) (M.g (j a) (j b)).val

def trInv (M : LB X) {A : Type} (V : A → X.Opens) (j : A → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (a b : A) :
    Γ(X, V a ⊓ V b) :=
  rs X (inf_le_inf (hj a) (hj b)) (M.g (j a) (j b))⁻¹.val

theorem tr_mul_trInv (M : LB X) {A : Type} (V : A → X.Opens) (j : A → M.ι)
    (hj : ∀ a, V a ≤ M.U (j a)) (a b : A) : tr M V j hj a b * trInv M V j hj a b = 1 := by
  simp only [tr, trInv, ← map_mul, Units.mul_inv, map_one]

section Triple

variable {A : Type} (V : A → X.Opens) (a b d : A)

theorem le₁₂ : V a ⊓ V b ⊓ V d ≤ V a ⊓ V b := inf_le_left

theorem le₂₃ : V a ⊓ V b ⊓ V d ≤ V b ⊓ V d := le_inf (inf_le_left.trans inf_le_right) inf_le_right

theorem le₁₃ : V a ⊓ V b ⊓ V d ≤ V a ⊓ V d := le_inf (inf_le_left.trans inf_le_left) inf_le_right

end Triple

theorem tr_cocycle {M : LB X} (hM : M.IsLB) {A : Type} (V : A → X.Opens) (j : A → M.ι)
    (hj : ∀ a, V a ≤ M.U (j a)) (a b d : A) :
    rs X (le₁₂ V a b d) (tr M V j hj a b) * rs X (le₂₃ V a b d) (tr M V j hj b d) =
      rs X (le₁₃ V a b d) (tr M V j hj a d) := by
  have h := congrArg (fun u => rs X (le_inf (le_inf
    ((inf_le_left.trans inf_le_left).trans (hj a)) ((inf_le_left.trans inf_le_right).trans (hj b)))
    (inf_le_right.trans (hj d)) : V a ⊓ V b ⊓ V d ≤ M.U (j a) ⊓ M.U (j b) ⊓ M.U (j d)) u.val)
    (hM.cocycle (j a) (j b) (j d))
  have e : ∀ {U W : X.Opens} (h : W ≤ U) (u : Γ(X, U)ˣ), ((res h u : Γ(X, W)ˣ) : Γ(X, W)) = rs X h u :=
    fun _ _ => rfl
  simp only [Units.val_mul, map_mul, e, GlobalTheory.AbLaw.rs_rs] at h
  simp only [tr, GlobalTheory.AbLaw.rs_rs]
  exact h

def DepSt : Prop :=
  ∀ (k : Type) [Field k] (Y : Scheme.{0}) (s₀ : Y ⟶ Sp k), Y.IsSeparated → ∀ n r : ℕ,
    Module.Finite k (HO1 s₀) → Module.finrank k (HO1 s₀) ≤ n → n < r →
    ∀ (A : Type) (V : A → Y.Opens), ⨆ a, V a = ⊤ → (∀ a, IsAffineOpen (V a)) →
    ∀ α : Fin r → ∀ a b, Γ(Y, V a ⊓ V b),
      (∀ i a b d, rs Y (le₁₂ V a b d) (α i a b) + rs Y (le₂₃ V a b d) (α i b d) =
        rs Y (le₁₃ V a b d) (α i a d)) →
      ∃ (c : Fin r → k) (ψ : ∀ a, Γ(Y, V a)), c ≠ 0 ∧ ∀ a b,
        ∑ i, GlobalTheory.SmallExtLift.cst s₀ _ (c i) * α i a b =
          rs Y inf_le_left (ψ a) - rs Y inf_le_right (ψ b)

end GlobalTheory.CompanionTheory.FewEq
end
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

noncomputable section

namespace GlobalTheory.CompanionTheory.PTIso.Norm

theorem isNormalised_transfer : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eO : 𝓞 F ≃+* 𝓞 F') (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ x : 𝓞 F, ((eO x : 𝓞 F') : F') = e (x : F)) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ↔ eO x ∈ (eV v).asIdeal) → (∀ (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F), x ∈ v.asIdeal ^ 2 ↔ eO x ∈ (eV v).asIdeal ^ 2) → (∀ v : HeightOneSpectrum (𝓞 F), normV (eV v) = normV v) → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), (∀ σ : G F Ω, cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ) → ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → (∀ σ : G F Ω, (σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') ∧ (σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') ∧ ∀ q : ℕ, IsFrob (F := F) A q σ ↔ IsFrob (F := F') A' q (Φ σ)) → ∀ (ζ : Ω) (v : HeightOneSpectrum (𝓞 F)) (iA : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)) (iA' : H2 (muLoc F' l r A') →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), (∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F' l r A')), (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F') A'), (g' : G F' Ω') = Φ g → (h' : G F' Ω') = Φ h → z'.1 (g', h') = z.1 (g, h)) → iA' (Submodule.Quotient.mk z') = iA (Submodule.Quotient.mk z)) → IsNormalised ζ A v iA → IsNormalised (E ζ) A' (eV v) iA' := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ eO eV heO hI hI2 hN l _ r hc A A' hA hD ζ v iA iA'
    hrel hn ϖ' y' κ' χ' z' h1 h2 h3 h4 h5 h6 h7 h8
  let eD : Dec (F := F) A ≃ₜ* Dec (F := F') A' :=
    subgroupIso Φ (Dec (F := F) A) (Dec (F := F') A') (fun a => (hD a).1)
  have hcoe : ∀ g : Dec (F := F) A, ((eD g : Dec (F := F') A') : G F' Ω') = Φ g := fun _ => rfl
  let zz : Z2 (muLoc F l r A) :=
    compatiblePairCocycles2 (muLoc F' l r A') (muLoc F l r A) (eD : Dec (F := F) A →* Dec (F := F') A')
      eD.continuous LinearMap.id continuous_id
      (fun g m => by
        show ((cycMod F' Ω' l r (Φ g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * m =
          ((cycMod F Ω l r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) * m
        rw [hc]) z'
  have hEy : E (E.symm y') = y' := E.apply_symm_apply y'
  have hϖ : eO (eO.symm ϖ') = ϖ' := eO.apply_symm_apply ϖ'
  have key : iA (Submodule.Quotient.mk zz) = 1 := by
    refine hn (eO.symm ϖ') (E.symm y') (fun g => κ' (eD g)) (fun g => χ' (eD g)) zz
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hI, hϖ]; exact h1
    · rw [hI2, hϖ]; exact h2
    · apply E.injective
      rw [map_pow, hEy, h3, hE, ← heO, hϖ]
    · intro g
      apply E.injective
      have h := h4 (eD g)
      rw [← hΦ, hEy, ← hcoe, h, map_mul, map_pow, hEy]
    · intro g h
      show χ' (eD (g * h)) = χ' (eD g) + χ' (eD h)
      rw [map_mul, h5]
    · intro g hg
      exact h6 (eD g) ((hD (g : G F Ω)).2.1.1 hg)
    · intro g hg
      refine h7 (eD g) ?_
      rw [hN]
      exact ((hD (g : G F Ω)).2.2 _).1 hg
    · intro g h
      exact h8 (eD g) (eD h)
  rw [hrel zz z' ?_]
  · exact key
  · intro g h g' h' hg hh
    have e1 : g' = eD g := Subtype.ext hg
    have e2 : h' = eD h := Subtype.ext hh
    subst e1 e2
    rfl

end GlobalTheory.CompanionTheory.PTIso.Norm
end
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

noncomputable section

namespace GlobalTheory.CompanionTheory.PTIso.InvTransport

theorem exists_invFam : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Dec (F := F) A ↔ Φ σ ∈ Dec (F := F') A') → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), (∀ σ : G F Ω, cycMod F' Ω' l r (Φ σ) = cycMod F Ω l r σ) → ∀ inv : InvFam F Ω l r, ∃ inv' : InvFam F' Ω' l r, ∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → (Function.Bijective (inv A) → Function.Bijective (inv' A')) ∧ (∀ (z : Z2 (muLoc F l r A)) (z' : Z2 (muLoc F' l r A')), (∀ (g h : Dec (F := F) A) (g' h' : Dec (F := F') A'), (g' : G F' Ω') = Φ g → (h' : G F' Ω') = Φ h → z'.1 (g', h') = z.1 (g, h)) → inv' A' (Submodule.Quotient.mk z') = inv A (Submodule.Quotient.mk z)) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E hE Φ hΦ hDec l _ r hcyc inv
  have hcm : ∀ (A' : ValuationSubring Ω') (x : Ω), E x ∈ A' ↔ x ∈ A'.comap E.toRingHom :=
    fun A' x => Iff.rfl
  let eD : ∀ A' : ValuationSubring Ω',
      Dec (F := F) (A'.comap E.toRingHom) ≃ₜ* Dec (F := F') A' :=
    fun A' => subgroupIso Φ _ _ (hDec _ A' (hcm A'))
  have hc : ∀ (A' : ValuationSubring Ω') (h : Dec (F := F) (A'.comap E.toRingHom))
      (m : ZMod (l ^ r)),
      (muLoc F' l r A') (eD A' h) m = (muLoc F l r (A'.comap E.toRingHom)) h m := by
    intro A' h m
    have h1 : cycMod F' Ω' l r (Φ h.1) = cycMod F Ω l r h.1 := hcyc h.1
    show charRep ((cycMod F' Ω' l r).comp (Dec (F := F') A').subtype) (eD A' h) m =
      charRep ((cycMod F Ω l r).comp (Dec (F := F) (A'.comap E.toRingHom)).subtype) h m
    have h2 : ((cycMod F' Ω' l r).comp (Dec (F := F') A').subtype) (eD A' h) =
        ((cycMod F Ω l r).comp (Dec (F := F) (A'.comap E.toRingHom)).subtype) h := h1
    rw [charRep_apply, charRep_apply, h2]
  refine ⟨fun A' => inv (A'.comap E.toRingHom) ∘ₗ
    (ReciprocityTheory.Neutral.Bridge.equivH2OfIso (eD A') (muLoc F' l r A')
      (muLoc F l r (A'.comap E.toRingHom)) (hc A')).toLinearMap, ?_⟩
  intro A A' hA
  obtain rfl : A = A'.comap E.toRingHom := by
    ext x
    exact (hA x).symm.trans (hcm A' x)
  refine ⟨fun hb => hb.comp (LinearEquiv.bijective _), fun z z' hz => ?_⟩
  show inv (A'.comap E.toRingHom) (ReciprocityTheory.Neutral.Bridge.equivH2OfIso (eD A') (muLoc F' l r A')
      (muLoc F l r (A'.comap E.toRingHom)) (hc A') (Submodule.Quotient.mk z')) = _
  rw [ReciprocityTheory.Neutral.Bridge.equivH2OfIso_mk]
  congr 2
  apply Subtype.ext
  funext p
  exact hz p.1 p.2 (eD A' p.1) (eD A' p.2) rfl rfl

end GlobalTheory.CompanionTheory.PTIso.InvTransport
end
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

theorem _root_.GlobalTheory.T.poitou_tate_euler_characteristic : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), (∀ L : LocCond ρ (locFam S Av), Sel ρ (locFam S Av) (continuous_locFam S Av) L = (Submodule.pi Set.univ L).comap (loc1 S Av ρ)) ∧ Sha1 ρ (locFam S Av) (continuous_locFam S Av) = LinearMap.ker (loc1 S Av ρ) ∧ Sha2 ρ (locFam S Av) (continuous_locFam S Av) = LinearMap.ker (loc2 S Av ρ) := by
  first | exact @GlobalTheory.CompanionTheory.GaloisCoh.selmer_sha_eq_comap_ker | exact GlobalTheory.CompanionTheory.GaloisCoh.selmer_sha_eq_comap_ker | (intros; apply GlobalTheory.CompanionTheory.GaloisCoh.selmer_sha_eq_comap_ker <;> assumption)
end

section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

theorem _root_.GlobalTheory.T.galois_cohomology_localization_exact : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ hμ : μ.comp (toGS Ω _) = cycMod F Ω l r, LocalTateDuality → 0 < r → ∀ inv : InvFam F Ω l r, (∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → Function.Bijective (inv A)) → (∀ v : S, IsPlaceOver (Av v) v.1) → ∀ v : S, Function.Injective ((cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))).compr₂ (invAt S Av μ hμ inv v)) ∧ Function.Injective ((cupH1H1TwistedDual μ ρ (locFam S Av v) (hρ.comp' (continuous_locFam S Av v))).compr₂ (invAt S Av μ hμ inv v)).flip := by
  first | exact @GlobalTheory.CompanionTheory.LocalPerfect.locPerfect | exact GlobalTheory.CompanionTheory.LocalPerfect.locPerfect | (intros; apply GlobalTheory.CompanionTheory.LocalPerfect.locPerfect <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cell_functor_nonscalar_offdiag : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → ∀ (B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))) (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) i) (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin a) (Fin b) j), B.1 false true ≠ 0 → ∀ φ : (cellFunctor f g ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)).IntertwiningMap ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom), φ.toLinearMap = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CellOff.offCell_eq_zero | exact GlobalTheory.CompanionTheory.CellOff.offCell_eq_zero | (intros; apply GlobalTheory.CompanionTheory.CellOff.offCell_eq_zero <;> assumption)
end

section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.chart_base_change_map_unique : ∀ {K : Type} [Field K] {n d : ℕ} {A : Type} [CommRing A] [Algebra K A] (C : ChartRings K A n d) {S T : Finset (Fin d)} (θ₁ θ₂ : R0 K n d S →ₐ[K] C.R T), (∀ b, θ₁ (poly n K S b) = toR C T (phi C b)) → (∀ b, θ₂ (poly n K S b) = toR C T (phi C b)) → ∀ (θ' : R0 K n d T →ₐ[K] C.R T) (hθ' : ∀ b, θ' (poly n K T b) = toR C T (phi C b)), IsBaseChange (Aa C) (thetaLin C θ' hθ') → θ₁ = θ₂ := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.ThetaUnique.theta_unique <;> assumption)
end
