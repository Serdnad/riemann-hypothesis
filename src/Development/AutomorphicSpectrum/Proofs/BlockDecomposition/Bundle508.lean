module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.EopW
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle481
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle483
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle482
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
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.TotallySplit
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle452
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle456
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle003
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.compact_free_set_projects_compact : ∀ (K : Type) [CommRing K] [TopologicalSpace K] [T2Space K] (M n : ℕ) (Q : Set (Fin (n + 1) → Fin (M + 1) → K)), IsCompact Q → (∀ Y ∈ Q, LinearIndependent K Y) → ∃ C : Set (Fin n → Fin M → K), IsCompact C ∧ (∀ X ∈ C, LinearIndependent K X) ∧ ∀ (A : K) (c : Fin n → K) (X : Fin n → Fin M → K), vec A c X ∈ Q → X ∈ C := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.Tails.exists_compact_tails | exact GlobalTheory.CompanionTheory.SW.StageF.Tails.exists_compact_tails | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.Tails.exists_compact_tails <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.linearIndependent_extend_by_unit_vector : ∀ (K : Type) [CommRing K] (M n : ℕ) (α : K), IsUnit α → ∀ (c : Fin n → K) (X : Fin n → Fin M → K), LinearIndependent K (vec α c X : Fin (n + 1) → Fin (M + 1) → K) ↔ LinearIndependent K X := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

theorem _root_.GlobalTheory.T.global_unitary_moves_isotropic_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ q : Fin 1 → Fin (M + 2) → E, q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → ∃ g : UJ (σ : E →+* E) (hypOne J), gact σ g q = e0 E M := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0 | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0 | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0 <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

theorem _root_.GlobalTheory.T.hyperbolic_frames_unitary_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypOne J) ∧ e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) ∧ ∀ (g : UJ (σ : E →+* E) (hypOne J)) (q : Fin 1 → Fin (M + 2) → E), q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → gact σ g q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Basic.hypOne_basic | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Basic.hypOne_basic | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Basic.hypOne_basic <;> assumption)
end

section

noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

namespace GlobalTheory.CompanionTheory.TwY

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev UU (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ


open Classical in
def singleN (w : InfinitePlace E) : ℂ →ₙ+* Cinf E where
  toFun x := fun v => if v = w then x else 0
  map_mul' x y := by
    funext v
    by_cases hv : v = w <;> simp [hv]
  map_zero' := by
    funext v
    simp
  map_add' x y := by
    funext v
    by_cases hv : v = w <;> simp [hv]

def locInf (w : InfinitePlace E) : PositivityTheory.RgTw.G n →* GL (Fin n) (Cinf E) := cornerGL n (singleN w)

def gAt (w : InfinitePlace E) : PositivityTheory.RgTw.G n →* GA E n := (infGL E n).comp (locInf w)

def kAt (w : InfinitePlace E) : UU n →* GA E n := (gAt w).comp Unitary.toUnits

omit [NumberField E] [IsCMField E] in
theorem one_apply_pi (i j : Fin n) (v : InfinitePlace E) :
    (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j v = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

omit [NumberField E] [IsCMField E] in
open Classical in
theorem locInf_apply (w : InfinitePlace E) (g : PositivityTheory.RgTw.G n) (i j : Fin n) (v : InfinitePlace E) :
    ((locInf w g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j v =
      if v = w then (g : Matrix (Fin n) (Fin n) ℂ) i j else (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  have e : ((locInf w g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j v =
      (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j v - singleN w ((1 : Matrix (Fin n) (Fin n) ℂ) i j) v +
        singleN w ((g : Matrix (Fin n) (Fin n) ℂ) i j) v := rfl
  rw [e, one_apply_pi]
  change _ - (if v = w then _ else 0) + (if v = w then _ else 0) = _
  by_cases hv : v = w <;> simp [hv]

def kInfAt (w : InfinitePlace E) (c : UU n) : Kinf E n :=
  ⟨(locInf w (Unitary.toUnits c) : GL (Fin n) (Cinf E)).val, by
    classical
    refine Matrix.mem_unitaryGroup_iff'.2 ?_
    ext i j v
    have hc : star c.1 * c.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 c.2
    rw [Matrix.mul_apply, Finset.sum_apply, one_apply_pi]
    simp only [Matrix.star_apply, Pi.mul_apply, Pi.star_apply, locInf_apply]
    by_cases hv : v = w
    · simp only [hv, if_true]
      have := congrFun (congrFun hc i) j
      rw [Matrix.mul_apply] at this
      simp only [Matrix.star_apply] at this
      rw [← this]
      rfl
    · simp only [hv, if_false]
      simp [Matrix.one_apply, eq_comm]⟩

theorem infGL_kInfAt (w : InfinitePlace E) (c : UU n) :
    infGL E n (Unitary.toUnits (kInfAt w c)) = kAt w c := by
  unfold kAt gAt
  simp only [MonoidHom.comp_apply]
  congr 1
  exact Units.ext rfl

def sV (π : CuspSub E n) (w : InfinitePlace E) : UU n →* Module.End ℂ π.V where
  toFun c := (rt E n (kAt w c)).restrict fun ψ hψ => by
    have h := π.stable (.cpt (kInfAt w c)) ψ hψ
    have e : rt E n (kAt w c) ψ = cptRep E n (kInfAt w c) ψ := by
      rw [← infGL_kInfAt]; rfl
    rw [e]; exact h
  map_one' := by
    ext ψ; simp
  map_mul' a b := by
    ext ψ; simp

def stabAlg (π : CuspSub E n) : Subalgebra ℂ (Module.End ℂ (Sm E n)) where
  carrier := {T | ∀ ψ ∈ π.V, T ψ ∈ π.V}
  mul_mem' ha hb ψ hψ := ha _ (hb ψ hψ)
  add_mem' ha hb ψ hψ := π.V.add_mem (ha ψ hψ) (hb ψ hψ)
  algebraMap_mem' c ψ hψ := π.V.smul_mem c hψ

theorem Eop_mem_stabAlg (π : CuspSub E n) (τ : E →+* ℂ) (i j : Fin n) : Eop (a := n) τ i j ∈ stabAlg π := by
  have hL : ∀ X, lie E n X ∈ stabAlg π := fun X ψ hψ => π.stable (.lie X) ψ hψ
  exact (stabAlg π).smul_mem ((stabAlg π).sub_mem (hL _) ((stabAlg π).smul_mem (hL _) _)) _

theorem eopW_mem_stabAlg (π : CuspSub E n) (w : InfinitePlace E) (s : Bool) (i j : Fin n) :
    PositivityTheory.RgBcC.Bridge.eopW w s i j ∈ stabAlg π := by
  cases s
  · exact Eop_mem_stabAlg π _ i j
  · exact Eop_mem_stabAlg π _ i j

section Avg

variable [MeasurableSpace (UU n)] (κ : Measure (UU n)) (Em : PositivityTheory.RgBcC.KMod n) (T : Em.V →L[ℂ] Em.V)

end Avg

end GlobalTheory.CompanionTheory.TwY
end
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

section Abstract
open Set
open scoped ENNReal
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.FinChart

namespace GlobalTheory.CompanionTheory.ArchDom

theorem measurableSet_inter_preimage {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] {f : α → β} {s : Set α}
    {t : Set β} (hf : ContinuousOn f s) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    MeasurableSet (s ∩ f ⁻¹' t) := by
  have hm : Measurable (s.restrict f) := (continuousOn_iff_continuous_restrict.1 hf).measurable
  have := hs.subtype_image (hm ht)
  convert this using 1
  ext v
  exact ⟨fun hv => ⟨⟨v, hv.1⟩, hv.2, rfl⟩, by rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩⟩

theorem chartMeas_le_sum {D n : ℕ} {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (e : OpenPartialHomeomorph Y (V D)) (ρ : Y → ℝ≥0∞) {Z : Set Y}
    (hZ : MeasurableSet Z) (hnull : volume (e.target ∩ e.symm ⁻¹' Z) = 0)
    (P : Fin n → (Fin D → ℂ) → Y) (K : Fin n → Set (Fin D → ℂ)) (hK : ∀ j, MeasurableSet (K j))
    (hP : ∀ j, ContinuousOn (P j) (K j)) (w : Fin n → (Fin D → ℂ) → ℝ≥0∞)
    (hcov : ∀ y ∈ e.source, y ∉ Z → ∃ j, ∃ u ∈ K j, P j u = y)
    (hinj : ∀ j, ∀ u ∈ K j, ∀ u' ∈ K j, P j u ∉ Z → P j u = P j u' → u = u')
    (hdet : ∀ j, ∀ u ∈ K j, P j u ∈ e.source → P j u ∉ Z →
      DifferentiableAt ℝ ((toV D).symm ∘ e ∘ P j) u ∧
      ENNReal.ofReal |(fderiv ℝ ((toV D).symm ∘ e ∘ P j) u).det| * ρ (P j u) ≤ w j u) :
    GlobalTheory.ChartGlue.chartMeas e ρ ≤
      ∑ j, Measure.map (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) := by
  refine Measure.le_iff.2 fun S hS => ?_
  have hsrc := e.open_source.measurableSet
  let T : Fin n → Set (Fin D → ℂ) := fun j => K j ∩ P j ⁻¹' ((e.source ∩ S) \ Z)
  let G : Fin n → (Fin D → ℂ) → (Fin D → ℂ) := fun j => (toV D).symm ∘ e ∘ P j
  have hT : ∀ j, MeasurableSet (T j) := fun j =>
    measurableSet_inter_preimage (hP j) (hK j) ((hsrc.inter hS).diff hZ)
  have hM : ∀ j, MeasurableSet (K j \ P j ⁻¹' Z) := fun j =>
    measurableSet_inter_preimage (hP j) (hK j) hZ.compl
  have hcover : e '' (e.source ∩ S) ⊆
      (e.target ∩ e.symm ⁻¹' Z) ∪ ⋃ j, toV D '' (G j '' T j) := by
    rintro _ ⟨y, ⟨hy, hyS⟩, rfl⟩
    by_cases hyZ : y ∈ Z
    · exact Or.inl (GlobalTheory.ChartGlue.mem_over e hy hyZ)
    · obtain ⟨j, u, hu, rfl⟩ := hcov y hy hyZ
      refine Or.inr (mem_iUnion.2 ⟨j, _, ⟨u, ⟨hu, ⟨⟨hy, hyS⟩, hyZ⟩⟩, rfl⟩, ?_⟩)
      simp [G]
  have hterm : ∀ j, ∫⁻ v in toV D '' (G j '' T j), ρ (e.symm v) ≤
      Measure.map (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) S := by
    intro j
    have hinjG : InjOn (G j) (T j) := by
      rintro u ⟨hu, hR⟩ u' ⟨hu', hR'⟩ h
      have h1 : e (P j u) = e (P j u') := (toV D).symm.injective h
      exact hinj j u hu u' hu' hR.2 (e.injOn hR.1.1 hR'.1.1 h1)
    have hder : ∀ u ∈ T j, HasFDerivWithinAt (G j) (fderiv ℝ (G j) u) (T j) u := fun u hu =>
      (hdet j u hu.1 hu.2.1.1 hu.2.2).1.hasFDerivAt.hasFDerivWithinAt
    have hae : AEMeasurable (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) :=
      (((hP j).mono diff_subset).aemeasurable (hM j)).mono_ac
        (withDensity_absolutelyContinuous _ _)
    rw [← measurePreserving_toV.setLIntegral_comp_emb (toV D).toHomeomorph.measurableEmbedding,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hT j) hder hinjG,
      Measure.map_apply_of_aemeasurable hae hS, withDensity_apply',
      Measure.restrict_restrict' (hM j)]
    refine (setLIntegral_mono' (hT j) fun u hu => ?_).trans (lintegral_mono_set ?_)
    · have hv : toV D (G j u) = e (P j u) := (toV D).apply_symm_apply _
      have := (hdet j u hu.1 hu.2.1.1 hu.2.2).2
      rw [hv, e.left_inv hu.2.1.1]
      exact this
    · rintro u ⟨hu, hR⟩
      exact ⟨hR.1.2, hu, hR.2⟩
  calc GlobalTheory.ChartGlue.chartMeas e ρ S = ∫⁻ v in e '' (e.source ∩ S), ρ (e.symm v) :=
        GlobalTheory.ChartGlue.chartMeas_apply e ρ hS
    _ ≤ ∫⁻ v in (e.target ∩ e.symm ⁻¹' Z) ∪ ⋃ j, toV D '' (G j '' T j), ρ (e.symm v) :=
        lintegral_mono_set hcover
    _ ≤ (∫⁻ v in e.target ∩ e.symm ⁻¹' Z, ρ (e.symm v)) +
          ∫⁻ v in ⋃ j, toV D '' (G j '' T j), ρ (e.symm v) := lintegral_union_le _ _ _
    _ = ∫⁻ v in ⋃ j, toV D '' (G j '' T j), ρ (e.symm v) := by
        rw [setLIntegral_measure_zero _ _ hnull, zero_add]
    _ ≤ ∑' j, ∫⁻ v in toV D '' (G j '' T j), ρ (e.symm v) := lintegral_iUnion_le _ _
    _ = ∑ j, ∫⁻ v in toV D '' (G j '' T j), ρ (e.symm v) := tsum_fintype _
    _ ≤ ∑ j, Measure.map (P j) ((volume.restrict (K j \ P j ⁻¹' Z)).withDensity (w j)) S :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = _ := by rw [Measure.finsetSum_apply]

theorem ofReal_abs_norm_mul_le (d : ℂ) (x : ℝ) (ε : ℤˣ) :
    ENNReal.ofReal |Algebra.norm ℝ d| * ENNReal.ofReal ((ε : ℤ) * x) ≤
      ENNReal.ofReal |‖d‖ ^ 2 * x| := by
  rw [← ENNReal.ofReal_mul (abs_nonneg _), Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (by positivity), abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖d‖ ^ 2)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simpa using le_abs_self x
  · simpa using neg_le_abs x

end GlobalTheory.CompanionTheory.ArchDom
end Abstract


open GlobalTheory.FinChart in
theorem GlobalTheory.CompanionTheory.ArchDom.chernPart_le_sum_map : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ (Z : Set (GlobalTheory.CxPts q σ)), MeasurableSet Z →
    (∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) →
    (∀ y, y ∉ Z → ∃ x, F x = y) → (∀ x x', F x ∉ Z → F x = F x' → x = x') →
    ∀ {B : LB X} (φ : GlobalTheory.Weight q σ B), φ.IsCInf → ∀ (ε : ℤˣ) (K : Fin A.n → Set (Fin D → ℂ)),
    (∀ j, IsCompact (K j)) → (∀ j, K j ⊆ (A.chart j).target) →
    (∀ x, ∃ j, ∃ u ∈ K j, (A.chart j).symm u = x) →
    φ.chernPart D ε ≤ ∑ j, Measure.map (F ∘ (A.chart j).symm)
      ((volume.restrict (K j \ (F ∘ (A.chart j).symm) ⁻¹' Z)).withDensity fun u =>
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|) := by
  intro k _ X q σ D T _ A F hF hol Z hZ hnull hsurj hinj B φ hφ ε K hK hKt hKc
  refine iSup_le fun c => ?_
  refine GlobalTheory.CompanionTheory.ArchDom.chartMeas_le_sum c.e _ hZ (hnull c) (fun j => F ∘ (A.chart j).symm) K
    (fun j => (hK j).measurableSet)
    (fun j => hF.comp_continuousOn ((A.chart j).continuousOn_symm.mono (hKt j))) _ ?_ ?_ ?_
  · intro y _ hyZ
    obtain ⟨x, rfl⟩ := hsurj y hyZ
    obtain ⟨j, u, hu, rfl⟩ := hKc x
    exact ⟨j, u, hu, rfl⟩
  · intro j u hu u' hu' hZu h
    exact (A.chart j).symm.injOn (hKt j hu) (hKt j hu') (hinj _ _ hZu h)
  · intro j u hu hsrc _
    obtain ⟨han, hd⟩ := GlobalTheory.T.smooth_weight_pullback_chart_formula A F hF hol φ hφ c j u (hKt j hu) hsrc
    have hG : (toV D).symm ∘ c.e ∘ (F ∘ (A.chart j).symm) =
        c.finChart ∘ F ∘ (A.chart j).symm := rfl
    rw [hG]
    have hdiff := han.differentiableAt
    refine ⟨hdiff.restrictScalars ℝ, ?_⟩
    have hdet : (fderiv ℝ (c.finChart ∘ F ∘ (A.chart j).symm) u).det = Algebra.norm ℝ
        (LinearMap.det (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) := by
      rw [hdiff.fderiv_restrictScalars ℝ]
      exact LinearMap.det_restrictScalars
        (f := (fderiv ℂ (c.finChart ∘ F ∘ (A.chart j).symm) u : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))
    rw [hdet, hd]
    exact GlobalTheory.CompanionTheory.ArchDom.ofReal_abs_norm_mul_le _ _ ε
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

theorem _root_.GlobalTheory.T.lintegral_indicator_mul_locDens_pullback_lt_top : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B C : LB X} (φ : GlobalTheory.Weight q σ B) (_ : φ.IsCInf) (ψ : GlobalTheory.Weight q σ C) (_ : ψ.IsCInf)
      (g : GlobalTheory.CxPts q σ → ℝ) (S Z : Set (GlobalTheory.CxPts q σ)) {N : ℕ} (W : Fin N → X.Opens) (b : Fin N → C.ι)
      (a d : ∀ l, Γ(X, W l)),
    (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) → (∀ l, W l ≤ C.U (b l)) →
    (∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ S → y ∉ Z →
      g y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2) →
    IsOpen S → ContinuousOn g S → MeasurableSet Z →
    ∀ (j : Fin A.n) (K : Set (Fin D → ℂ)), K ⊆ (A.chart j).target → IsCompact K →
      ∫⁻ u in K \ (F ∘ (A.chart j).symm) ⁻¹' Z, S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.lintegral_logNorm_locDens_lt_top | exact GlobalTheory.CompanionTheory.MixZ.lintegral_logNorm_locDens_lt_top | (intros; apply GlobalTheory.CompanionTheory.MixZ.lintegral_logNorm_locDens_lt_top <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.iwahori_and_maximal_compact_criteria : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (g : GLw n w), (g ∈ iwGL n w ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ (∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) ∧ ∀ i j, j < i → Valued.v (g.val i j) < 1) ∧ (g ∈ GlobalTheory.LFun.KGL w (n := n) ↔ (∀ i j, Valued.v (g.val i j) ≤ 1) ∧ ∀ i j, Valued.v ((g⁻¹).val i j) ≤ 1) := by
  first | exact @GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries | exact GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries | (intros; apply GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.parabolic_element_block_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (p : parab (w.adicCompletion E) (two (stdSum h))), ∃ X, (p : GLw n w) = GlobalTheory.BCT.blk h w ((leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm (leviProj (w.adicCompletion E) (two (stdSum h)) p)) X := by
  first | exact @GlobalTheory.CompanionTheory.ParabBlock.parab_eq_blk | exact GlobalTheory.CompanionTheory.ParabBlock.parab_eq_blk | (intros; apply GlobalTheory.CompanionTheory.ParabBlock.parab_eq_blk <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.HintSmaller

theorem hint_eq_of_le : ∀ {H : Type} [Group H] (K S : Subgroup H) (u : H → ℂ), S ≤ K → S ≤ rStab u →
    S.relIndex K ≠ 0 → (Function.support fun q : H ⧸ S => u q.out).Finite →
    hint K u = ((S.relIndex K : ℂ))⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  intro H _ K S u hSK hSu hfin _
  exact GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K S u hSK hSu hfin

end GlobalTheory.CompanionTheory.HintSmaller
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.weight_exponent_strictly_antitone : ∀ (n : ℕ) (l : Fin (n / 2) → ℤ), Cone l → StrictAnti (wexp n l) ∧ ∀ i, wexp n l (Fin.rev i) = -wexp n l i := by
  first | exact @GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev | exact GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev | (intros; apply GlobalTheory.CompanionTheory.Wexp.wexp_strictAnti_rev <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgLevel

theorem avg_eq_level : ∀ {H : Type} [Group H] (S : Subgroup H) (u : H → ℂ), S ≤ rStab u →
    S.index ≠ 0 → avg u = ((S.index : ℂ))⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  intro H _ S u hS hfin
  have hmul := Subgroup.relIndex_mul_index hS
  have hm : S.relIndex (rStab u) ≠ 0 := fun h0 => hfin (by rw [← hmul, h0, zero_mul])
  have hmC : ((S.relIndex (rStab u) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [GlobalTheory.CompanionTheory.HintLevel.finsum_out_of_le u hS le_rfl hm, ← hmul, avg, Nat.cast_mul, mul_inv,
    mul_mul_mul_comm, inv_mul_cancel₀ hmC, one_mul]

end GlobalTheory.CompanionTheory.AvgLevel
end
end
