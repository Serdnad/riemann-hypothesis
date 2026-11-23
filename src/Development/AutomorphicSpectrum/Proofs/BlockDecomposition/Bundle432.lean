module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle084
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle419
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle417
public import GroundTheory.AutomorphicForms.ReductionMahler
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle420
import GroundTheory.AutomorphicForms.Reduction
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle006
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle403
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle401
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilTheta

theorem schwartzA_continuous_and_dominated : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (Φ : Mx D m n → ℂ),
    Φ ∈ schwartzA θ m n → Continuous Φ ∧ ∃ (k : ℕ) (f : Fin k → SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
      (g : Fin k → (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) ∧
      ∀ x, ‖Φ x‖ₑ ≤ ∑ i, ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ := by
  intro D θ hθ m n Φ hΦ
  have hy : Continuous fun x : Mx D m n => (fun τ i j => compAt θ τ x i j : D.what₂.Tau → Fin m → Fin n → ℂ) :=
    continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.RealWeil.continuous_compAt hθ τ m n).matrix_elem i j
  have hz : Continuous fun x : Mx D m n =>
      (fun i j => finPart D (x i j) : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    continuous_pi fun i => continuous_pi fun j =>
      (GlobalTheory.Member.continuous_finPart D).comp (continuous_id.matrix_elem i j)
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨(f.continuous.comp hy).mul (hg.1.continuous.comp hz), 1, fun _ => f, fun _ => g, fun _ => hg, fun x => ?_⟩
    simp
  | zero =>
    exact ⟨continuous_const, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun x => by simp⟩
  | add Φ₁ Φ₂ _ _ h₁ h₂ =>
    obtain ⟨c₁, k₁, f₁, g₁, hg₁, hb₁⟩ := h₁
    obtain ⟨c₂, k₂, f₂, g₂, hg₂, hb₂⟩ := h₂
    refine ⟨c₁.add c₂, k₁ + k₂, Fin.append f₁ f₂, Fin.append g₁ g₂, fun i => ?_, fun x => ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]; exact hg₁ i
      · rw [Fin.append_right]; exact hg₂ i
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      exact (enorm_add_le _ _).trans (add_le_add (hb₁ x) (hb₂ x))
  | smul c Φ _ h =>
    obtain ⟨hc, k, f, g, hg, hb⟩ := h
    refine ⟨hc.const_smul c, k, fun i => c • f i, g, hg, fun x => ?_⟩
    have e : ∀ i, ‖(c • f i) (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ =
        ‖c‖ₑ * ‖f i (fun τ i' j => compAt θ τ x i' j) * g i (fun i' j => finPart D (x i' j))‖ₑ := fun i => by
      rw [smul_apply, smul_eq_mul, mul_assoc, enorm_mul]
    simp only [e, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, enorm_mul]
    gcongr
    exact hb x

end GlobalTheory.CompanionTheory.WeilTheta

end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.LieSkew

theorem continuous_infGL_map (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E) :=
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  refine Continuous.units_map _ ?_
  exact continuous_const.add (continuous_id.matrix_map hs)

theorem inner_R_R {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (g : G) (F F' : L2 Γ μ) :
    inner ℂ (R Γ μ g F) (R Γ μ g F') = inner ℂ F F' :=
  (LinearIsometry.mk (R Γ μ g).toLinearMap (norm_R g)).inner_map_map F F'

theorem lie_skew : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : GlobalTheory.CuspRep.Lie E a) (φ ψ : Sm E a) (hφ : MemL2Quotient (latticeGL E a) μ φ.1) (hψ : MemL2Quotient (latticeGL E a) μ ψ.1) (hXφ : MemL2Quotient (latticeGL E a) μ (lie E a X φ).1) (hXψ : MemL2Quotient (latticeGL E a) μ (lie E a X ψ).1), Continuous φ.1 → Continuous ψ.1 → Continuous (lie E a X φ).1 → Continuous (lie E a X ψ).1 → inner ℂ hXφ.toL2 hψ.toL2 = - inner ℂ hφ.toL2 hXψ.toL2 := by
  intro E _ _ _ a μ _ _ X φ ψ hφ hψ hXφ hXψ cφ cψ cXφ cXψ
  obtain ⟨c, hc, h0, hadd, hd, -⟩ := GlobalTheory.T.one_parameter_subgroup_exists E a X
  have hγ : Continuous fun t => infGL E a (c t) := (continuous_infGL_map E a).comp hc
  have hγ0 : infGL E a (c 0) = 1 := by rw [h0, map_one]
  have hγa : ∀ s t, infGL E a (c (s + t)) = infGL E a (c s) * infGL E a (c t) := fun s t => by
    rw [hadd, map_mul]
  have d1 := GlobalTheory.T.hasDerivAt_right_translate_toL2 (GA E a) (latticeGL E a) μ φ.1 (lie E a X φ).1 hφ hXφ
    (fun t => infGL E a (c t)) cφ cXφ hγ hγ0 hγa (fun g => hasDerivAt_curve φ g c X h0 hd) 0
  have d2 := GlobalTheory.T.hasDerivAt_right_translate_toL2 (GA E a) (latticeGL E a) μ ψ.1 (lie E a X ψ).1 hψ hXψ
    (fun t => infGL E a (c t)) cψ cXψ hγ hγ0 hγa (fun g => hasDerivAt_curve ψ g c X h0 hd) 0
  have d3 := d1.inner ℂ d2
  have hconst : (fun t : ℝ => inner ℂ (R (latticeGL E a) μ (infGL E a (c t)) hφ.toL2)
      (R (latticeGL E a) μ (infGL E a (c t)) hψ.toL2)) = fun _ => inner ℂ hφ.toL2 hψ.toL2 :=
    funext fun t => inner_R_R _ μ _ _ _
  rw [hconst] at d3
  have h := d3.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [hγ0, map_one, ContinuousLinearMap.one_apply] at h
  exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans h)

end GlobalTheory.CompanionTheory.LieSkew
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

theorem _root_.GlobalTheory.T.cuspidal_convolution_split_centre_invariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ) (F : L2 (latticeGL E a) μ), F ∈ L2cusp μ → ∀ (t : ℝ) (x : GA E a), convR μ f (lift (latticeGL E a) F) (splitCentre E a t * x) = convR μ f (lift (latticeGL E a) F) x := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.convR_lift_splitCentre_mul | exact GlobalTheory.CompanionTheory.SmoothRep.convR_lift_splitCentre_mul | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.convR_lift_splitCentre_mul <;> assumption)
end

section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.CompanionTheory.CuspTransfer

namespace GlobalTheory.CompanionTheory.CuspTransfer.FubiniCentre

section Abstract

variable {X G : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]

theorem exists_fibreIntegral (F : X × ℝ → ℂ) (hF : Continuous F) (hs : HasCompactSupport F) (r : ℂ) :
    ∃ f₁ : CompactlySupportedContinuousMap X ℂ, ∀ x, f₁ x = r * ∫ t, F (x, t) := by
  have hK : IsCompact (Prod.snd '' tsupport F) := hs.isCompact.image continuous_snd
  have hK₁ : IsCompact (Prod.fst '' tsupport F) := hs.isCompact.image continuous_fst
  have hcont : Continuous fun x : X => ∫ t, F (x, t) := by
    rw [← continuousOn_univ]
    refine continuousOn_integral_of_compact_support (f := fun x t => F (x, t)) hK ?_ ?_
    · exact hF.continuousOn
    · intro p x _ hx
      by_contra h
      exact hx ⟨(p, x), subset_tsupport _ h, rfl⟩
  refine ⟨⟨⟨fun x => r * ∫ t, F (x, t), continuous_const.mul hcont⟩, ?_⟩, fun x => rfl⟩
  refine HasCompactSupport.intro hK₁ fun x hx => ?_
  have h0 : ∀ t, F (x, t) = 0 := by
    intro t
    by_contra h
    exact hx ⟨(x, t), subset_tsupport _ h, rfl⟩
  simp [h0]

theorem integral_eq_of_map (e : X × ℝ ≃ₜ G) (ν : Measure X) [SFinite ν] [IsFiniteMeasureOnCompacts ν]
    (μ : Measure G) (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map e (ν.prod volume) = c • μ) (f : G → ℂ) (hf : Continuous f) (hs : HasCompactSupport f)
    (f₁ : CompactlySupportedContinuousMap X ℂ)
    (hf₁ : ∀ x, f₁ x = (c.toReal : ℂ)⁻¹ * ∫ t, f (e (x, t)))
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K] (W : G → K) (w : X → K)
    (hW : Continuous W) (hw : ∀ x t, W (e (x, t)) = w x) :
    ∫ g, f g • W g ∂μ = ∫ x, f₁ x • w x ∂ν := by
  have hr : c.toReal ≠ 0 := (ENNReal.toReal_pos hc0 hct).ne'
  have hrC : (c.toReal : ℂ) ≠ 0 := by exact_mod_cast hr
  have hFc : Continuous fun p : X × ℝ => f (e p) := hf.comp e.continuous
  have hFs : HasCompactSupport fun p : X × ℝ => f (e p) := hs.comp_homeomorph e
  have hint : Integrable (fun p : X × ℝ => f (e p) • W (e p)) (ν.prod volume) :=
    (hFc.smul (hW.comp e.continuous)).integrable_of_hasCompactSupport hFs.smul_right
  have h1 : c.toReal • ∫ g, f g • W g ∂μ = ∫ p, f (e p) • W (e p) ∂(ν.prod volume) := by
    rw [← integral_smul_measure, ← hmap]
    exact e.measurableEmbedding.integral_map _
  have h2 : ∫ p, f (e p) • W (e p) ∂(ν.prod volume) = ∫ x, (∫ t, f (e (x, t))) • w x ∂ν := by
    rw [integral_prod _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hw]
    exact integral_smul_const _ _
  have h3 : ∫ x, f₁ x • w x ∂ν = (c.toReal : ℂ)⁻¹ • ∫ x, (∫ t, f (e (x, t))) • w x ∂ν := by
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf₁, mul_smul]
  rw [h3, ← h2, ← h1, ← Complex.coe_smul, smul_smul, inv_mul_cancel₀ hrC, one_smul]

end Abstract

theorem exists_normOne_integral : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 0 < a → ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ν : Measure (normOneGL (K := E) (n := a))) [ν.IsHaarMeasure] (c : ENNReal), c ≠ 0 → c ≠ ⊤ → Measure.map (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) (ν.prod volume) = c • μ → ∀ f : GA E a → ℂ, Continuous f → HasCompactSupport f → ∃ f₁ : CompactlySupportedContinuousMap (normOneGL (K := E) (n := a)) ℂ, ∀ (K : Type) [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K] (W : GA E a → K), Continuous W → (∀ t g, W (splitCentre E a t * g) = W g) → ∫ g, f g • W g ∂μ = ∫ x, f₁ x • W (x : GA E a) ∂ν := by
  intro E _ _ _ a ha μ _ ν _ c hc0 hct hmap f hf hs
  obtain ⟨e, he⟩ := GlobalTheory.T.adelic_GL_norm_one_split E a ha
  have hfun : (fun p : normOneGL (K := E) (n := a) × ℝ => splitCentre E a p.2 * (p.1 : GA E a)) = e := by
    funext p
    exact (he p.1 p.2).symm
  rw [hfun] at hmap
  obtain ⟨f₁, hf₁⟩ := exists_fibreIntegral (fun p : normOneGL (K := E) (n := a) × ℝ => f (e p))
    (hf.comp e.continuous) (hs.comp_homeomorph e) ((c.toReal : ℂ)⁻¹)
  refine ⟨f₁, fun K _ _ _ W hW hinv => ?_⟩
  set_option synthInstance.maxHeartbeats 200000 in
    exact integral_eq_of_map e ν μ c hc0 hct hmap f hf hs f₁ hf₁ W (fun x => W (x : GA E a)) hW
      (fun x t => by rw [he, hinv])

end GlobalTheory.CompanionTheory.CuspTransfer.FubiniCentre
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

section Join

variable {R : Type*} {m r s : ℕ}

def colJoin (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) : Matrix (Fin m) (Fin (r + s)) R :=
  Matrix.of fun i k => Sum.elim (y₁ i) (y₂ i) (finSumFinEquiv.symm k)

def colL (y : Matrix (Fin m) (Fin (r + s)) R) : Matrix (Fin m) (Fin r) R := Matrix.of fun i j => y i (Fin.castAdd s j)

def colR (y : Matrix (Fin m) (Fin (r + s)) R) : Matrix (Fin m) (Fin s) R := Matrix.of fun i j => y i (Fin.natAdd r j)

@[simp] theorem colJoin_castAdd (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) (i : Fin m) (j : Fin r) :
    colJoin y₁ y₂ i (Fin.castAdd s j) = y₁ i j := by
  simp [colJoin]

@[simp] theorem colJoin_natAdd (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) (i : Fin m) (j : Fin s) :
    colJoin y₁ y₂ i (Fin.natAdd r j) = y₂ i j := by
  simp [colJoin]

@[simp] theorem colL_colJoin (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    colL (colJoin y₁ y₂) = y₁ := by
  ext i j; simp [colL]

@[simp] theorem colR_colJoin (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    colR (colJoin y₁ y₂) = y₂ := by
  ext i j; simp [colR]

@[simp] theorem colJoin_colL_colR (y : Matrix (Fin m) (Fin (r + s)) R) : colJoin (colL y) (colR y) = y := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [colL]
  · simp [colR]

theorem colJoin_injective {y₁ y₁' : Matrix (Fin m) (Fin r) R} {y₂ y₂' : Matrix (Fin m) (Fin s) R}
    (h : colJoin y₁ y₂ = colJoin y₁' y₂') : y₁ = y₁' ∧ y₂ = y₂' :=
  ⟨by rw [← colL_colJoin y₁ y₂, h, colL_colJoin], by rw [← colR_colJoin y₁ y₂, h, colR_colJoin]⟩

def joinEquiv : Matrix (Fin m) (Fin r) R × Matrix (Fin m) (Fin s) R ≃ Matrix (Fin m) (Fin (r + s)) R where
  toFun z := colJoin z.1 z.2
  invFun y := (colL y, colR y)
  left_inv z := by simp
  right_inv y := by simp

theorem colJoin_map {R' : Type*} (f : R → R') (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    (colJoin y₁ y₂).map f = colJoin (y₁.map f) (y₂.map f) := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

theorem colJoin_add [Add R] (y₁ y₁' : Matrix (Fin m) (Fin r) R) (y₂ y₂' : Matrix (Fin m) (Fin s) R) :
    colJoin (y₁ + y₁') (y₂ + y₂') = colJoin y₁ y₂ + colJoin y₁' y₂' := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

theorem colJoin_neg [Neg R] (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    colJoin (-y₁) (-y₂) = -colJoin y₁ y₂ := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

theorem colJoin_sub [Sub R] (y₁ y₁' : Matrix (Fin m) (Fin r) R) (y₂ y₂' : Matrix (Fin m) (Fin s) R) :
    colJoin (y₁ - y₁') (y₂ - y₂') = colJoin y₁ y₂ - colJoin y₁' y₂' := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

end Join

variable {D : D7}

theorem rat_colJoin {m r s : ℕ} (p : Matrix (Fin m) (Fin r) D.host.E) (q : Matrix (Fin m) (Fin s) D.host.E) :
    rat (colJoin p q) = colJoin (rat p) (rat q) :=
  colJoin_map _ p q

def cellTerm (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) : ℂ :=
  ψ (trA (Matrix.trace (inner V (rat q) y₂))) *
    (ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V (y₁ - rat p) (y₁ - rat p)) : Mx D r r))) *
      Φ (HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a)))

end GlobalTheory.CompanionTheory.EisUnfold

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.GenTop

theorem appLE_fromSpecResidueField {X : Scheme.{0}} {U : X.Opens} (x : X) (hx : x ∈ U)
    (h : ⊤ ≤ X.fromSpecResidueField x ⁻¹ᵁ U) :
    (X.fromSpecResidueField x).appLE U ⊤ h = X.evaluation U x hx ≫ (Scheme.ΓSpecIso _).inv := by
  have h' : ⊤ ≤ Spec.map (X.residue x) ⁻¹ᵁ (X.fromSpecStalk x ⁻¹ᵁ U) := h
  have e : X.fromSpecResidueField x = Spec.map (X.residue x) ≫ X.fromSpecStalk x := rfl
  have := Scheme.Hom.appLE_comp_appLE (Spec.map (X.residue x)) (X.fromSpecStalk x) U (X.fromSpecStalk x ⁻¹ᵁ U) ⊤ le_rfl h'
  rw [appLE_of_eq e U ⊤ h (h'.trans le_rfl), ← this, ← Scheme.Hom.app_eq_appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, Scheme.Hom.map_appLE]
  rw [← Scheme.germ_residue, Category.assoc, Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem pullRatio_SpecMap_fromSpec {N : ℕ} (i : Fin (N + 1)) {R : CommRingCat.{0}}
    (ψ : Γ(PSpace ℤ N, chart ℤ N i) ⟶ R)
    (h : ⊤ ≤ (Spec.map ψ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ⁻¹ᵁ chart ℤ N i) (j : Fin (N + 1)) :
    pullRatio (Spec.map ψ ≫ (isAffineOpen_chart ℤ N i).fromSpec) ⊤ i h j =
      (Scheme.ΓSpecIso R).inv (ψ (ratio ℤ N i j)) := by
  have h1 : (isAffineOpen_chart ℤ N i).fromSpec.appLE (chart ℤ N i) ⊤
      (isAffineOpen_chart ℤ N i).fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have h3 := Scheme.Hom.appLE_comp_appLE (Spec.map ψ) (isAffineOpen_chart ℤ N i).fromSpec
    (chart ℤ N i) ⊤ ⊤ (isAffineOpen_chart ℤ N i).fromSpec_preimage_self.ge le_rfl
  unfold pullRatio
  rw [← h3, h1]
  have := congrArg (fun q => q.hom (ratio ℤ N i j)) (Scheme.ΓSpecIso_inv_naturality ψ)
  exact this.symm

theorem surjective_of_factor {X : Scheme.{0}} (x : X) {F : Type} [Field F]
    (ι : CommRingCat.of F ⟶ X.residueField x) (G : Spec (.of F) ⟶ X)
    (h : Spec.map ι ≫ G = X.fromSpecResidueField x) : Function.Surjective ι.hom := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField F X).symm.surjective G
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h
  have hz : z = x := by
    have e := congrArg (fun f : Spec (X.residueField x) ⟶ X => f default) h
    simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] at e
    exact e
  subst hz
  rw [← Category.assoc, ← Spec.map_comp] at h
  have h2 : Spec.map (φ ≫ ι) = Spec.map (𝟙 _) := by
    rw [← cancel_mono (X.fromSpecResidueField _), Spec.map_id, Category.id_comp]
    exact h
  have h3 : φ ≫ ι = 𝟙 _ := Spec.map_injective h2
  intro a
  refine ⟨φ.hom a, ?_⟩
  have := congrArg (fun q => q.hom a) h3
  simpa using this

theorem blockFnField_ptCoord_eq_top (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n)
    [CharZero ((MP ℤ m n).residueField x)] : blockFnField (ptCoord x) = ⊤ := by
  have hone : ∀ k, ptCoord x ⟨k, ptChart x k⟩ = 1 := fun k => by
    simp only [ptCoord, pullRatio_self, map_one]
  have hmem : ∀ p, ptCoord x p ∈ blockFnField (ptCoord x) := fun p =>
    IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, ptChart x p.1⟩, rfl, by rw [hone, div_one]⟩
  let F := blockFnField (ptCoord x)
  let r : ∀ k, Fin (n k + 1) → F := fun k j => ⟨ptCoord x ⟨k, j⟩, hmem _⟩
  have hr : ∀ k, r k (ptChart x k) = 1 := fun k => Subtype.ext (hone k)
  let ρ : ∀ k, Γ(PSpace ℤ (n k), chart ℤ (n k) (ptChart x k)) ⟶ CommRingCat.of F := fun k =>
    CommRingCat.ofHom (R := Γ(PSpace ℤ (n k), chart ℤ (n k) (ptChart x k))) (S := F)
      (chartLift (ptChart x k) (Int.castRingHom F) (r k))
  let g : ∀ k, Spec (CommRingCat.of F) ⟶ projectiveSpace ℤ (n k) := fun k =>
    Spec.map (ρ k) ≫ (isAffineOpen_chart ℤ (n k) (ptChart x k)).fromSpec
  let G : Spec (CommRingCat.of F) ⟶ MP ℤ m n :=
    GroundTheory.Arith.SchemeCoh.ProjSpace.lift m n (Spec.map (CommRingCat.ofHom (Int.castRingHom F))) g
      (fun _ => specZIsTerminal.hom_ext _ _)
  let ι : CommRingCat.of F ⟶ (MP ℤ m n).residueField x := CommRingCat.ofHom F.val.toRingHom
  have key : Spec.map ι ≫ G = (MP ℤ m n).fromSpecResidueField x := by
    refine GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k => ?_
    rw [Category.assoc, GroundTheory.Arith.SchemeCoh.ProjSpace.lift_pr]
    have hx := mem_ptChart x k
    have h₂' : ⊤ ≤ (MP ℤ m n).fromSpecResidueField x ⁻¹ᵁ blockChart n k (ptChart x k) := fun s _ => by
      rw [Scheme.Hom.mem_preimage, Scheme.fromSpecResidueField_apply]
      exact hx
    have e1 : Spec.map ι ≫ g k = Spec.map (ρ k ≫ ι) ≫ (isAffineOpen_chart ℤ (n k) (ptChart x k)).fromSpec := by
      rw [Spec.map_comp, Category.assoc]
    have h₁ : ⊤ ≤ (Spec.map (ρ k ≫ ι) ≫ (isAffineOpen_chart ℤ (n k) (ptChart x k)).fromSpec) ⁻¹ᵁ
        chart ℤ (n k) (ptChart x k) := by
      rw [Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self]
      exact le_top
    rw [e1]
    refine GlobalTheory.ProjSpace.hom_ext (specZIsTerminal.hom_ext _ _) fun _ =>
      ⟨⊤, trivial, ptChart x k, h₁, by rw [Scheme.Hom.comp_preimage]; exact h₂', fun j => ?_⟩
    rw [pullRatio_SpecMap_fromSpec]
    have e2 := appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k) (hi := le_rfl)
      (j := j) ((MP ℤ m n).fromSpecResidueField x) h₂'
    refine Eq.trans ?_ e2
    rw [appLE_fromSpecResidueField x hx]
    show _ = (Scheme.ΓSpecIso _).inv (ptCoord x ⟨k, j⟩)
    congr 1
    show F.val (chartLift (ptChart x k) (Int.castRingHom F) (r k) (ratio ℤ (n k) (ptChart x k) j)) = _
    rw [chartLift_ratio _ _ (hr k)]
    rfl
  have hs := surjective_of_factor x ι G key
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨b, rfl⟩ := hs a
  exact b.2

end GlobalTheory.CompanionTheory.MPDict.GenTop
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem mem_ptIdeal_iff_aeval_ptCoord : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (f : Geo.MRing (Bk n)) (a : Fin (m + 1) → ℕ), Geo.IsMultiHomog f a → (f ∈ ptIdeal x ↔ aeval (ptCoord x) f = 0) := by
  intro m n x f a hf
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse.mem_mCoordIdeal_iff (ptCoord x) hf

end GlobalTheory.CompanionTheory.MPDict
end
end
