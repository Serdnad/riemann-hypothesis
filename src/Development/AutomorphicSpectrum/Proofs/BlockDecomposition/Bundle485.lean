module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle106
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle453
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle455
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorExtendsHyperbolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnitScalingLatticeMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle208
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdeal
import Formalism.RealPlaceAnalysis.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle456
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle198
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle128
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelNM
open GlobalTheory.StdUnn.Model

theorem unip_mul_levi : ∀ (D : D7) (p : ℕ) (q : G D p), q ∈ P D p → ∀ a : GL (Fin p) (AE D), blkA (mat q) = a.1 →
    ∃ (g₁ g₂ : G D p) (b : Mx D p p), q = g₁ * g₂ ∧ mat g₁ = blk4 1 b 0 1 ∧ mat g₂ = blk4 a.1 0 0 (adj (a⁻¹).1) := by
  intro D p q hq a ha
  obtain ⟨m, u, b, e, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha
  obtain ⟨m', hm'⟩ := GlobalTheory.StdUnn.Model.exists_levi (D := D) (n := p) a⁻¹
  rw [inv_inv] at hm'
  have hmm : m * m' = 1 := GlobalTheory.StdUnn.LeftInvSect.mat_inj (by
    rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_one, hm, hm',
      GlobalTheory.StdUnn.LeftInvSect.levi_mul_inv])
  have hmm' : m' * m = 1 := by
    rw [eq_inv_of_mul_eq_one_right hmm, inv_mul_cancel]
  have h2 : (adj (a⁻¹).1 : Mx D p p) * adj a.1 = 1 := by
    rw [← adj_mul]; simp [adj_one]
  refine ⟨m * u * m', m, a.1 * b * adj a.1, ?_, ?_, hm⟩
  · rw [mul_assoc (m * u), hmm', mul_one, e]
  · rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, GlobalTheory.StdUnn.LeftInvSect.mat_mul, hm, hu, hm']
    simp [GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul, h2, -Matrix.coe_units_inv]

end GlobalTheory.CompanionTheory.SiegelNM
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.character_integral_orthogonality : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (s : ℕ)
    (μs : Measure (Mx D V.rank s)) (𝓕s : Set (Mx D V.rank s)), IsCovolOne (ratMx D V.rank s) μs 𝓕s →
    ∀ q : Matrix (Fin V.rank) (Fin s) D.host.E,
      (q = 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 1) ∧
      (q ≠ 0 → ∫ y in 𝓕s, ψ (trA (Matrix.trace (inner V (rat q) y))) ∂μs = 0) := by
  first | exact @GlobalTheory.CompanionTheory.EisUnfold.Orth.orthogonality | exact GlobalTheory.CompanionTheory.EisUnfold.Orth.orthogonality | (intros; apply GlobalTheory.CompanionTheory.EisUnfold.Orth.orthogonality <;> assumption)
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StabInv

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

section Alg

variable {K : Type} [CommRing K] {M : ℕ}

def lowerB (U : Matrix (Fin (M + 2)) (Fin (M + 2)) K) : Matrix (Fin M) (Fin M) K :=
  Matrix.of fun i j => U i.succ.succ j.succ.succ

theorem col_zero {U : Matrix (Fin (M + 2)) (Fin (M + 2)) K}
    (h : U.mulVec (Fin.cons 1 fun _ => 0) = Fin.cons 1 fun _ => 0) (i : Fin (M + 2)) :
    U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i := by
  have := congrFun h i
  rw [← this]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem row_one (s : K →+* K) (A : Matrix (Fin M) (Fin M) K)
    {U : Matrix (Fin (M + 2)) (Fin (M + 2)) K} (hU : cT s U * hypOne A * U = hypOne A)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i) (j : Fin M) :
    U 1 j.succ.succ = 0 := by
  have h := congrFun (congrFun hU 0) j.succ.succ
  have h1 : U 1 0 = 0 := h0 1
  have hr : ∀ i : Fin M, U i.succ.succ 0 = 0 := fun i => h0 i.succ.succ
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_succ] at h
  simpa [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, h0 0, h1, hr] using h

theorem lowerB_isometry (s : K →+* K) (A : Matrix (Fin M) (Fin M) K)
    {U : Matrix (Fin (M + 2)) (Fin (M + 2)) K} (hU : cT s U * hypOne A * U = hypOne A)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i) :
    cT s (lowerB U) * A * lowerB U = A := by
  ext i j
  have h := congrFun (congrFun hU i.succ.succ) j.succ.succ
  have h1 : ∀ j : Fin M, U 1 j.succ.succ = 0 := row_one s A hU h0
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_succ] at h ⊢
  simpa [lowerB, hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, h1] using h

theorem mulVec_cons (U : Matrix (Fin (M + 2)) (Fin (M + 2)) K)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i)
    (h1 : ∀ j : Fin M, U 1 j.succ.succ = 0) (a : K) (Y : Fin M → K) :
    U.mulVec (Fin.cons a (Fin.cons 0 Y)) =
      Fin.cons (a + ∑ i, U 0 i.succ.succ * Y i) (Fin.cons 0 ((lowerB U).mulVec Y)) := by
  have e1 : U 1 0 = 0 := h0 1
  have er : ∀ i : Fin M, U i.succ.succ 0 = 0 := fun i => h0 i.succ.succ
  have e0 : U 0 0 = 1 := h0 0
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, e0]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, e1, h1]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, er, lowerB]

theorem mulVec_consA {n : ℕ} (U : Matrix (Fin (M + 2)) (Fin (M + 2)) K)
    (hfix : U.mulVec (Fin.cons 1 fun _ => 0) = Fin.cons 1 fun _ => 0)
    (h0 : ∀ i, U i 0 = (Fin.cons 1 (fun _ => 0) : Fin (M + 2) → K) i)
    (h1 : ∀ j : Fin M, U 1 j.succ.succ = 0) (a : Fin 1 → Fin n → K) (Y : Fin n → Fin M → K) :
    (fun k => U.mulVec (consA a Y k)) =
      consA (a + fun _ j => ∑ i, U 0 i.succ.succ * Y j i) (fun j => (lowerB U).mulVec (Y j)) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simpa [consA] using hfix
  · simpa [consA] using mulVec_cons U h0 h1 (a 0 j) (Y j)

theorem map_hypOne {L : Type} [CommRing L] (f : K →+* L) (A : Matrix (Fin M) (Fin M) K) :
    (hypOne A).map f = hypOne (A.map f) := by
  ext i j
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  all_goals
    simp [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest]

end Alg

section Main

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem JR_hypOne (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    JR (F := F) R (hypOne J) = hypOne (JR (F := F) R J) :=
  map_hypOne (inclR R) J

theorem exists_HA (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : J.det ≠ 0) {κ : Matrix (Fin M) (Fin M) (R ⊗[F] E)}
    (hκ : cT (sigR R σ) κ * JR (F := F) R J * κ = JR (F := F) R J) :
    ∃ h : HA R σ J, ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = κ := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ
  have hi : (J⁻¹).map (inclR (F := F) R) * JR (F := F) R J = 1 := by
    have h1 := congrArg (fun A : Matrix (Fin M) (Fin M) E => A.map (inclR (F := F) R)) (Matrix.nonsing_inv_mul J hu)
    simpa [JR, Matrix.map_mul, Matrix.map_one] using h1
  have hl : ((J⁻¹).map (inclR (F := F) R) * cT (sigR R σ) κ * JR (F := F) R J) * κ = 1 := by
    calc ((J⁻¹).map (inclR (F := F) R) * cT (sigR R σ) κ * JR (F := F) R J) * κ
        = (J⁻¹).map (inclR (F := F) R) * (cT (sigR R σ) κ * JR (F := F) R J * κ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hκ, hi]
  have hr := mul_eq_one_comm.mp hl
  let G : GL (Fin M) (R ⊗[F] E) := ⟨κ, _, hr, hl⟩
  have hG : G ∈ HR R σ J := hκ
  exact ⟨(⟨G, hG⟩ : HR R σ J), rfl⟩

end Main

theorem stageInt_eq_of_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₀ : Measure (Fin n → Fin M → R ⊗[F] E), (∀ h : HA R σ J, m₀.map (actW R σ J h) = m₀) → ∀ φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ g g' : HA R σ (hypOne J), actW R σ (hypOne J) g (e0 _ M) = actW R σ (hypOne J) g' (e0 _ M) → stageInt R σ J b lam m₀ φ g = stageInt R σ J b lam m₀ φ g' := by
  intro F E _ _ _ _ _ σ hcm M J hJ R _ _ _ _ _ hL n d b lam hlam m₀ hm₀ φ hφ g g' hgg
  haveI : IsTopologicalRing R := hL.1
  haveI : LocallyCompactSpace R := hL.2.1
  haveI : SecondCountableTopology R := hL.2.2.1
  haveI : T2Space R := hL.2.2.2.1
  obtain ⟨tK1, tK2, tK3, tK4, -, -, -, tK8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  haveI := tK1
  haveI := tK2
  haveI := tK3
  haveI := tK4
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := tK8 n M
  haveI : BorelSpace (Fin 1 → Fin n → R ⊗[F] E) := tK8 1 n
  haveI : BorelSpace (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) := tK8 (n + 1) (M + 2)
  obtain ⟨-, hW, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm R d b lam hlam
  haveI := hW 1 n
  obtain ⟨-, -, -, -, -, hA⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm (M + 2) (hypOne J) (isHermND_hypOne σ hJ) R
  obtain ⟨-, -, -, -, -, hA'⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ R
  obtain ⟨-, e1, em, -⟩ := hA 1
  obtain ⟨hc, -, hm, -⟩ := hA (n + 1)
  obtain ⟨hc', -, -, -⟩ := hA' n

  set u : HA R σ (hypOne J) := g⁻¹ * g' with hu_def
  have hg' : g' = g * u := by simp [hu_def]
  have hfix : actW R σ (hypOne J) u (e0 _ M) = e0 _ M := by
    rw [hu_def, em, ← hgg, ← em, inv_mul_cancel, e1]
  set U : Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E) :=
    (HA.mat R σ (hypOne J) u).val with hU_def
  have hfixV : U.mulVec (Fin.cons 1 fun _ => 0) = Fin.cons 1 fun _ => 0 := congrFun hfix 0
  have h0 := col_zero hfixV
  have hUu : cT (sigR R σ) U * hypOne (JR (F := F) R J) * U = hypOne (JR (F := F) R J) := by
    rw [← JR_hypOne]
    exact (show HR R σ (hypOne J) from u).2
  have h1 := row_one _ _ hUu h0
  obtain ⟨k, hk⟩ := exists_HA R σ hJ.2 (lowerB_isometry _ _ hUu h0)

  have hact : ∀ (a : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E),
      actW R σ (hypOne J) u (consA a Y) =
        consA (a + fun _ j => ∑ i, U 0 i.succ.succ * Y j i) (actW R σ J k Y) := by
    intro a Y
    have := mulVec_consA U hfixV h0 h1 a Y
    have e : actW R σ J k Y = fun j => (lowerB U).mulVec (Y j) := by
      funext j
      simp only [actW, actTup, hk]
    rw [e, ← this]
    rfl

  let G : (Fin n → Fin M → R ⊗[F] E) → ℝ≥0∞ := fun Y =>
    ∫⁻ a, φ (actW R σ (hypOne J) g (consA a Y)) ∂(coordW R b lam 1 n)
  have hcons : Continuous fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
      (consA p.2 p.1 : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) := by
    refine continuous_pi fun k => continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) k
    · refine Fin.cases ?_ (fun i => ?_) i <;> simpa [consA] using continuous_const
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
      · simp only [consA, Fin.cons_succ, Fin.cons_zero]
        fun_prop
      · simpa [consA] using continuous_const
      · simp only [consA, Fin.cons_succ]
        fun_prop
  have hGm : Measurable G := by
    have hf : Measurable fun p : (Fin n → Fin M → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) =>
        φ (actW R σ (hypOne J) g (consA p.2 p.1)) :=
      hφ.comp (hc.comp (continuous_const.prodMk hcons)).measurable
    exact hf.lintegral_prod_right'
  have hkm : Measurable (actW R σ J k : (Fin n → Fin M → R ⊗[F] E) → _) :=
    (hc'.comp (continuous_const.prodMk continuous_id)).measurable
  have hinner : ∀ Y, (∫⁻ a, φ (actW R σ (hypOne J) g' (consA a Y)) ∂(coordW R b lam 1 n)) =
      G (actW R σ J k Y) := by
    intro Y
    have : ∀ a, actW R σ (hypOne J) g' (consA a Y) =
        actW R σ (hypOne J) g (consA (a + fun _ j => ∑ i, U 0 i.succ.succ * Y j i) (actW R σ J k Y)) := by
      intro a
      rw [hg', hm, hact]
    simp only [this]
    exact lintegral_add_right_eq_self
      (fun a => φ (actW R σ (hypOne J) g (consA a (actW R σ J k Y)))) _
  show (∫⁻ Y, G Y ∂m₀) = ∫⁻ Y, (∫⁻ a, φ (actW R σ (hypOne J) g' (consA a Y)) ∂(coordW R b lam 1 n)) ∂m₀
  simp only [hinner]
  rw [← lintegral_map hGm hkm, hm₀ k]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StabInv
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem _root_.GlobalTheory.T.euler_product_lintegral_limit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable Ψinf → (∀ v, Measurable (Ψ v)) → Measurable (purePr σ J b S Ψinf Ψ) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas.measurable_purePr | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas.measurable_purePr | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas.measurable_purePr <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas

theorem eventually_measurableSet_primV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, MeasurableSet (primV σ J b v) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b
  exact Filter.Eventually.of_forall fun v => measurableSet_primV F E σ hσ M J hJ d b v

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem _root_.GlobalTheory.T.primitive_vector_extends_hyperbolic : ∀ (T : Type) [CommRing T] (O : Subring T) (s : T →+* T), (∀ y ∈ O, s y ∈ O) → (∀ y, s (s y) = y) → IsUnit (2 : O) → (∃ δ : O, IsUnit δ ∧ s δ = -δ) → ∀ π₁ π₂ : O, (∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂}) → ∀ (M : ℕ) (J Ji : Matrix (Fin M) (Fin M) T), (∀ i j, J i j ∈ O) → (∀ i j, Ji i j ∈ O) → J * Ji = 1 → (∀ i j, s (J j i) = J i j) → ∀ x : Fin (M + 2) → O, (∀ P : Ideal O, P.IsMaximal → ∃ i, x i ∉ P) → hform s (hypOne J) (fun i => (x i : T)) (fun i => (x i : T)) = 0 → ∃ g ∈ UJ s (hypOne J), (g : Matrix (Fin (M + 2)) (Fin (M + 2)) T) *ᵥ (e0 T M 0) = (fun i => (x i : T)) ∧ (∀ i j, (g : Matrix (Fin (M + 2)) (Fin (M + 2)) T) i j ∈ O) ∧ ∀ i j, ((g⁻¹ : GL (Fin (M + 2)) T) : Matrix (Fin (M + 2)) (Fin (M + 2)) T) i j ∈ O := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans.trans_orbit | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans.trans_orbit | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans.trans_orbit <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

theorem _root_.GlobalTheory.T.local_unit_scaling_lattice_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m' : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (c : Fv F v ⊗[F] E) (a : ℝ≥0), IsUnit c → c ∈ intK b v → (coordK (Fv F v) b lam).map (fun x => c * x) = a • coordK (Fv F v) b lam → ∀ y ∈ primV σ J b v, ∃ g : HA (Fv F v) σ (hypOne J), actW (Fv F v) σ (hypOne J) g (e0 _ M) = scalT c y ∧ stageInt (Fv F v) σ J b lam m' ((latV b v).indicator 1) g = (a : ℝ≥0∞) ^ n * m' (latV b v) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.StageVal.stageInt_primV | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.StageVal.stageInt_primV | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypMass.StageVal.stageInt_primV <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.CapComm

open Formalism.REAL

theorem commute_qdet_of {A : Type} [Ring A] [Algebra ℂ A] {k : ℕ} {X : Fin k → Fin k → A} {x : A}
    (h : ∀ a b, Commute x (X a b)) (u : ℂ) : Commute x (qdet X u) := by
  have hm : ∀ a b, X a b ∈ Subalgebra.centralizer ℂ ({x} : Set A) := fun a b =>
    (Subalgebra.mem_centralizer_iff ℂ).2 fun _ hg => by rw [hg]; exact (h a b).eq
  have hq : qdet X u ∈ Subalgebra.centralizer ℂ ({x} : Set A) := by
    unfold qdet qminor
    refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ _) ?_
    refine Subalgebra.list_prod_mem _ fun y hy => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    unfold Tm
    refine Subalgebra.add_mem _ ?_ (hm _ _)
    split_ifs
    · exact Subalgebra.algebraMap_mem _ _
    · exact Subalgebra.zero_mem _
  exact (Subalgebra.mem_centralizer_iff ℂ).1 hq x rfl

theorem qdet_commute_self {A : Type} [Ring A] [Algebra ℂ A] {k : ℕ} {X : Fin k → Fin k → A}
    (hX : GlRel X) (u v : ℂ) : Commute (qdet X u) (qdet X v) :=
  commute_qdet_of (fun a b => qDetCentral A k X hX u a b) v

theorem capR_capS_commute (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ)
    (u v : ℂ) :
    Commute (capR r s τ u) (capR r s τ v) ∧ Commute (capR r s τ u) (capS r s τ v) ∧
      Commute (capS r s τ u) (capS r s τ v) := by
  have hE := glRel_Eop (E := E) (a := r + s) τ
  refine ⟨?_, ?_, ?_⟩
  · exact qdet_commute_self (GlobalTheory.CapHC.glRel_restrict hE _ (Fin.castAdd_injective _ _)) _ _
  · exact (GlobalTheory.CapHC.qdet_comm hE _ _).symm
  · exact qdet_commute_self (GlobalTheory.CapHC.glRel_restrict hE _ (Fin.natAdd_injective _ _)) _ _

end GlobalTheory.CompanionTheory.CTFin.CapComm

end
end

section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.DimVar

open _root_.Topology

theorem finiteType_of_chart {Y : Scheme.{0}} (f : Y ⟶ Spec (.of ℤ)) [LocallyOfFiniteType f] {C : Type} [CommRing C]
    [Algebra ℤ C] (j : Spec (.of C) ⟶ Y) [IsOpenImmersion j] (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℤ C))) :
    Algebra.FiniteType ℤ C :=
  RingHom.finiteType_algebraMap.mp <|
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)
      (φ := CommRingCat.ofHom (algebraMap ℤ C))).mp (hj ▸ inferInstance)

theorem topologicalKrullDim_closure_eq (Y : Scheme.{0}) (f : Y ⟶ Spec (.of ℤ)) [LocallyOfFiniteType f] (y : Y)
    [CharZero (Y.residueField y)] :
    topologicalKrullDim (closure ({y} : Set Y)) =
      (((Algebra.trdeg ℤ (Y.residueField y)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨B, _, _, j, _, q, hq, hj⟩ := exists_affine_chart_over f y
  subst hq
  have := finiteType_of_chart f j hj
  rw [← GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ Y B j q inferInstance, ← topologicalKrullDim_range_inter_closure_eq j q]
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun z ↦ ?_)
    (IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  obtain ⟨C, _, _, j', _, y', hy, hj'⟩ := exists_affine_chart_over f z.1
  have := finiteType_of_chart f j' hj'
  obtain ⟨q', hq'⟩ := (specializes_iff_mem_closure.mpr z.2).mem_open
    j'.isOpenEmbedding.isOpen_range ⟨y', hy⟩
  refine ⟨Subtype.val ⁻¹' Set.range j',
    j'.isOpenEmbedding.isOpen_range.preimage continuous_subtype_val, ⟨y', hy⟩, ?_⟩
  rw [← topologicalKrullDim_eq_of_isEmbedding (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    (Z := Set.range j' ∩ closure {j q})
    (by rw [Set.range_comp, Subtype.range_coe, Subtype.image_preimage_coe, Set.inter_comm])]
  rw [topologicalKrullDim_range_inter_closure_eq j q, GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ Y B j q inferInstance]
  conv_lhs => rw [← hq', topologicalKrullDim_range_inter_closure_eq j' q']
  have h0 : CharZero (Y.residueField (j' q')) := hq' ▸ inferInstance
  rw [GlobalTheory.T.krull_dim_quotient_eq_trdeg_succ Y C j' q' h0, hq']

theorem ptCoord_chart_ne_zero {m : ℕ} {n : Fin (m + 1) → ℕ} (x : MP ℤ m n) (k : Fin (m + 1)) :
    ptCoord x ⟨k, ptChart x k⟩ ≠ 0 := by
  simp [ptCoord, pullRatio_self]

theorem isArithVar_ptIdeal : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ), CharZero ((MP ℤ m n).residueField x) → topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) → Geo.IsArithVar (ptIdeal x) d := by
  intro m n x d hch hd
  have hdim := topologicalKrullDim_closure_eq (MP ℤ m n) (mpStr ℤ m n) x
  rw [hd] at hdim
  have h1 : ((d : ℕ∞)) = (Algebra.trdeg ℤ ((MP ℤ m n).residueField x)).toENat + 1 := WithBot.coe_injective hdim
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (Algebra.trdeg ℤ ((MP ℤ m n).residueField x)).toENat = t := by
    refine ⟨(Algebra.trdeg ℤ ((MP ℤ m n).residueField x)).toENat.toNat, (ENat.natCast_toNat ?_).symm⟩
    intro h
    rw [h] at h1
    simp at h1
  have hdt : d = t + 1 := by
    rw [ht] at h1
    exact_mod_cast h1
  subst hdt
  have htr : Algebra.trdeg ℤ (blockFnField (ptCoord x)) = t := by
    rw [GlobalTheory.T.function_field_of_point_coords_top m n x, GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.trdeg_top]
    exact Cardinal.toENat_eq_natCast.mp ht
  exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DimY.isArithVar_of_trdeg (ptCoord x) (ptChart x) (ptCoord_chart_ne_zero x) t htr

end GlobalTheory.CompanionTheory.MPDict.DimVar
end
