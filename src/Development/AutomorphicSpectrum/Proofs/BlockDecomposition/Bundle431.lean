module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle417
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle423
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle217
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle241
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle270
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle424
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle312
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle419
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle389
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwasawaBruhatDecomposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle403
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND

section Adelic

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def starN (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ)
    (b : HermR (AF F) σ n) : ℂ :=
  ∫ X, Φ X * ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X))) ∂dx

def coefN (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E) : ℂ :=
  ∫ b, starN σ J ψ dx Φ b * ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
    (Matrix.trace (T.map (inclR (AF F)) * (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))))) ∂db

end Adelic

section Glue

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def tupOf {D : D7} {m r : ℕ} (X : Fin r → Fin m → AE D) : Mx D m r := Matrix.of fun i a => X a i

def thetaPartD {D : D7} (V : HSp D) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) {r : ℕ}
    (φ : Mx D V.rank r → ℂ) (β : HermE D r) : ℂ :=
  ∫ X, φ (tupOf X) ∂(GlobalTheory.CompanionTheory.SW.thetaMeas D.sp.cm.sig V.gram μH 𝓕
    {X : Fin r → Fin V.rank → D.host.E | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1})

end Glue

end GlobalTheory.CompanionTheory.SiegelND
end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

theorem _root_.GlobalTheory.T.center_commutes_one_parameter_flow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ (g : GL (Fin a) (Cinf E)) (X : Lie E a), rt E a (infGL E a g) * lie E a X = lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g)) → ∀ z : Module.End ℂ (Sm E a), z ∈ Zalg E a → (∀ X : Lie E a, z * lie E a X = lie E a X * z) → ∀ (c : ℝ → GL (Fin a) (Cinf E)) (Y : Lie E a), c 0 = 1 → (∀ s, HasDerivAt (fun t => toL (c t).val) (toL ((c s).val * Matrix.of Y)) s) → (∀ s, HasDerivAt (fun t => toL ((c t)⁻¹).val) (toL (-(Matrix.of Y * ((c s)⁻¹).val))) s) → z * rt E a (infGL E a (c 1)) = rt E a (infGL E a (c 1)) * z := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.Flow.zalg_comm_rt_curve | exact GlobalTheory.CompanionTheory.SmoothRep.Flow.zalg_comm_rt_curve | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.Flow.zalg_comm_rt_curve <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

theorem _root_.GlobalTheory.T.center_enveloping_commutes_lie : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (z : Module.End ℂ (Sm E a)), z ∈ Zalg E a → ∀ X : Lie E a, z * lie E a X = lie E a X * z := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.Zalg_comm_lie | exact GlobalTheory.CompanionTheory.SmoothRep.Zalg_comm_lie | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.Zalg_comm_lie <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

theorem _root_.GlobalTheory.T.right_translation_lie_conjugate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (g : GL (Fin a) (Cinf E)) (X : Lie E a), rt E a (infGL E a g) * lie E a X = lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.rt_infGL_mul_lie | exact GlobalTheory.CompanionTheory.SmoothRep.rt_infGL_mul_lie | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.rt_infGL_mul_lie <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.skew_hermitian_lie_preserves_stable : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : Submodule ℂ (Sm E a)), FiniteDimensional ℂ F → (∀ k, ∀ φ ∈ F, cptRep E a k φ ∈ F) → ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ φ ∈ F, lie E a X φ ∈ F := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.lie_skew_mem_of_cpt_stable | exact GlobalTheory.CompanionTheory.Dblock.lie_skew_mem_of_cpt_stable | (intros; apply GlobalTheory.CompanionTheory.Dblock.lie_skew_mem_of_cpt_stable <;> assumption)
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

theorem _root_.GlobalTheory.T.unitary_exponential_path_exists : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (k : Kinf E a), ∃ (c : ℝ → GL (Fin a) (Cinf E)) (Y : Lie E a), c 0 = 1 ∧ c 1 = Unitary.toUnits k ∧ (∀ s, HasDerivAt (fun t => toL (c t).val) (toL ((c s).val * Matrix.of Y)) s) ∧ (∀ s, HasDerivAt (fun t => toL ((c t)⁻¹).val) (toL (-(Matrix.of Y * ((c s)⁻¹).val))) s) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.KCurve.exists_curve | exact GlobalTheory.CompanionTheory.SmoothRep.KCurve.exists_curve | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.KCurve.exists_curve <;> assumption)
end

section

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn

namespace GlobalTheory.CompanionTheory.SwUnf

def lowerC {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁

variable {D : D7} {n : ℕ}

def cellKer (x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) : Submodule D.host.E (Fin n → D.host.E) :=
  LinearMap.ker (lowerC x).mulVecLin

def ratOf (γ : GF D n) : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E :=
  Classical.choose (GlobalTheory.StdUnn.LeftInvSect.rat_mat γ.2)

theorem mat_ratOf (γ : GF D n) : mat (γ : G D n) = (ratOf γ).map (incA D) :=
  Classical.choose_spec (GlobalTheory.StdUnn.LeftInvSect.rat_mat γ.2)

def cosetCell (q : GlobalTheory.Eis.Cosets (P D n) (GF D n)) : Submodule D.host.E (Fin n → D.host.E) :=
  cellKer (ratOf (q.out))

end GlobalTheory.CompanionTheory.SwUnf
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_sub_fun (X : Mat n) {u v : Mat n → V} (hu : ContDiffOn ℝ ∞ u (GLs n)) (hv : ContDiffOn ℝ ∞ v (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (fun y => u y - v y) g = Rd X u g - Rd X v g := by
  have h1 := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hu hg
  have h2 := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hv hg
  exact DFunLike.congr_fun (h1.hasFDerivAt.sub h2.hasFDerivAt).fderiv (g * X)

theorem Rd_add_fun (X : Mat n) {u v : Mat n → V} (hu : ContDiffOn ℝ ∞ u (GLs n)) (hv : ContDiffOn ℝ ∞ v (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (fun y => u y + v y) g = Rd X u g + Rd X v g := by
  have h1 := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hu hg
  have h2 := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hv hg
  exact DFunLike.congr_fun (h1.hasFDerivAt.add h2.hasFDerivAt).fderiv (g * X)

theorem Rd_sq_sub (X X' : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd (X - X') (Rd (X - X') f) g =
      Rd X (Rd X f) g - Rd X (Rd X' f) g - (Rd X' (Rd X f) g - Rd X' (Rd X' f) g) := by
  have e : Rd (X - X') f = fun y => Rd X f y - Rd X' f y := funext fun y => GlobalTheory.CompanionTheory.SecBd.Rd_sub X X' f y
  have h1 := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf
  have h2 := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X' hf
  rw [e, GlobalTheory.CompanionTheory.SecBd.Rd_sub, Rd_sub_fun X h1 h2 hg, Rd_sub_fun X' h1 h2 hg]

theorem Rd_sq_add (X X' : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd (X + X') (Rd (X + X') f) g =
      Rd X (Rd X f) g + Rd X (Rd X' f) g + (Rd X' (Rd X f) g + Rd X' (Rd X' f) g) := by
  have e : Rd (X + X') f = fun y => Rd X f y + Rd X' f y := funext fun y => GlobalTheory.CompanionTheory.SecBd.Rd_add X X' f y
  have h1 := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf
  have h2 := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X' hf
  rw [e, GlobalTheory.CompanionTheory.SecBd.Rd_add, Rd_add_fun X h1 h2 hg, Rd_add_fun X' h1 h2 hg]

abbrev skY (a c : Fin n) : Mat n := Matrix.single a c (1 : ℂ) - Matrix.single c a (1 : ℂ)

abbrev skZ (a c : Fin n) : Mat n := Matrix.single a c Complex.I + Matrix.single c a Complex.I

theorem Lap_eq (hO : OmFormula) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Lap f g = -Om f g + (-(1 / 2 : ℂ)) • ∑ a, ∑ c,
      (Rd (skY a c) (Rd (skY a c) f) g + Rd (skZ a c) (Rd (skZ a c) f) g) := by
  set P : Fin n → Fin n → V := fun a c =>
    Rd (Matrix.single a c (1 : ℂ)) (Rd (Matrix.single a c (1 : ℂ)) f) g with hP
  set Q : Fin n → Fin n → V := fun a c =>
    Rd (Matrix.single a c Complex.I) (Rd (Matrix.single a c Complex.I) f) g with hQ
  set M : Fin n → Fin n → V := fun a c =>
    Rd (Matrix.single a c (1 : ℂ)) (Rd (Matrix.single c a (1 : ℂ)) f) g with hM
  set N : Fin n → Fin n → V := fun a c =>
    Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a Complex.I) f) g with hN
  have hY : ∀ a c, Rd (skY a c) (Rd (skY a c) f) g = P a c - M a c - (M c a - P c a) := fun a c =>
    Rd_sq_sub _ _ hf hg
  have hZ : ∀ a c, Rd (skZ a c) (Rd (skZ a c) f) g = Q a c + N a c + (N c a + Q c a) := fun a c =>
    Rd_sq_add _ _ hf hg
  have hS : ∑ p, Rd (bs p) (Rd (bs p) f) g = ∑ a, ∑ c, P a c + ∑ a, ∑ c, Q a c := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, GlobalTheory.CompanionTheory.SecBd.basis_true_eq_single, GlobalTheory.CompanionTheory.SecBd.bs_f,
      Finset.sum_add_distrib, hP, hQ]
  have hOm : Om f g = ∑ a, ∑ c, M a c - ∑ a, ∑ c, N a c := by
    rw [hO n V f hf g hg]
    simp only [Finset.sum_sub_distrib, hM, hN]
  have swap : ∀ F : Fin n → Fin n → V, ∑ a, ∑ c, F c a = ∑ a, ∑ c, F a c := fun F => Finset.sum_comm
  have hT : ∑ a, ∑ c, (Rd (skY a c) (Rd (skY a c) f) g + Rd (skZ a c) (Rd (skZ a c) f) g) =
      (2 : ℂ) • (∑ a, ∑ c, P a c) - (2 : ℂ) • (∑ a, ∑ c, M a c) +
        ((2 : ℂ) • (∑ a, ∑ c, Q a c) + (2 : ℂ) • (∑ a, ∑ c, N a c)) := by
    simp only [hY, hZ, Finset.sum_add_distrib, Finset.sum_sub_distrib, swap M, swap P, swap N, swap Q]
    module
  show -∑ p, Rd (bs p) (Rd (bs p) f) g = _
  rw [hS, hOm, hT]
  module

theorem lap_sec : ∀ (n : ℕ) (E : KMod n), RCalc → OmFormula → ∃ Q : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n,
    GlobalTheory.CompanionTheory.FcSmooth.Lap f g = -Om f g + Q (f g) := by
  intro n E _ hO
  choose BY hBY using fun a c : Fin n => GlobalTheory.CompanionTheory.WaveSpd.rd_skew_eq_const E _ (GlobalTheory.CompanionTheory.SecBd.skewY a c)
  choose BZ hBZ using fun a c : Fin n => GlobalTheory.CompanionTheory.WaveSpd.rd_skew_eq_const E _ (GlobalTheory.CompanionTheory.SecBd.skewZ a c)
  have sq : ∀ (Y : Mat n) (B : E.V →L[ℂ] E.V), (∀ f ∈ CE E, ∀ g ∈ GLs n, Rd Y f g = B (f g)) →
      ∀ f ∈ CE E, ∀ g ∈ GLs n, Rd Y (Rd Y f) g = (B * B) (f g) := by
    intro Y B h f hf g hg
    have e : Set.EqOn (Rd Y f) (fun y => B (f y)) (GLs n) := fun y hy => h f hf y hy
    rw [GlobalTheory.CompanionTheory.RCalc.Rd_congr Y e hg, GlobalTheory.CompanionTheory.SobOpsPf.Rd_post Y B hf.1 hg, h f hf g hg]
    rfl
  refine ⟨(-(1 / 2 : ℂ)) • ∑ a, ∑ c, (BY a c * BY a c + BZ a c * BZ a c), fun f hf g hg => ?_⟩
  rw [Lap_eq hO hf.1 hg]
  congr 1
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [sq _ _ (hBY a c) f hf g hg, sq _ _ (hBZ a c) f hf g hg]

end GlobalTheory.CompanionTheory.FcSmooth
end
end

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.LapSec

open GlobalTheory.CompanionTheory.FcSmooth (Lap)
open GlobalTheory.CompanionTheory.SobSecK (Rw_congr Rw_smooth)
open GlobalTheory.CompanionTheory.SobOpsPf (Rw_add Rw_post sob_congr sob_smul sob_sum sob_bs sob_Om sob_post Om_smooth)

variable {n : ℕ}

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Lap_eq (f : Mat n → V) (g : Mat n) : Lap f g = -∑ p, Rw [p, p] f g := rfl

theorem Lap_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (Lap f) (GLs n) := by
  have h : ContDiffOn ℝ ∞ (fun g => ∑ p, Rw [p, p] f g) (GLs n) :=
    ContDiffOn.sum fun p _ => Rw_smooth [p, p] hf
  exact h.neg

theorem Lap_congr {f f' : Mat n → V} (e : Set.EqOn f f' (GLs n)) : Set.EqOn (Lap f) (Lap f') (GLs n) := by
  intro g hg
  simp only [Lap_eq]
  exact congrArg Neg.neg (Finset.sum_congr rfl fun p _ => Rw_congr [p, p] e hg)

theorem Lap_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Lap (f + f')) (Lap f + Lap f') (GLs n) := by
  intro g hg
  simp only [Lap_eq, Pi.add_apply]
  rw [← neg_add, ← Finset.sum_add_distrib]
  exact congrArg Neg.neg (Finset.sum_congr rfl fun p _ => Rw_add [p, p] hf hf' hg)

theorem Lap_post (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Lap fun y => A (f y)) (fun y => A (Lap f y)) (GLs n) := by
  intro g hg

  simp only [Lap_eq, map_neg, map_sum]
  exact congrArg Neg.neg (Finset.sum_congr rfl fun p _ => Rw_post [p, p] A hf hg)

theorem iter_congr (j : ℕ) {f f' : Mat n → V} (e : Set.EqOn f f' (GLs n)) :
    Set.EqOn (Lap^[j] f) (Lap^[j] f') (GLs n) := by
  induction j generalizing f f' with
  | zero => exact e
  | succ j ih => exact ih (Lap_congr e)

theorem iter_add (j : ℕ) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Lap^[j] (f + f')) (Lap^[j] f + Lap^[j] f') (GLs n) := by
  induction j generalizing f f' with
  | zero => intro x _; rfl
  | succ j ih =>
    intro x hx
    exact (iter_congr j (Lap_add hf hf') hx).trans (ih (Lap_smooth hf) (Lap_smooth hf') hx)

end Words

section Sob

variable [MeasurableSpace (G n)] {μ : Measure (G n)} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem sob_Lap {f : Mat n → V} (hf : Sob μ f) : Sob μ (Lap f) :=
  sob_congr (f := (-1 : ℂ) • ∑ p, Rd (bs p) (Rd (bs p) f))
    (sob_smul _ (sob_sum _ hf fun p => sob_bs p (sob_bs p hf))) fun g _ => by
      simp [Lap]

theorem sob_iter (j : ℕ) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Lap^[j] f) := by
  induction j generalizing f with
  | zero => exact hf
  | succ j ih => exact ih (sob_Lap hf)

theorem cls_add {F F' : Mat n → V} (h : MemLp (fun y : G n => F y.val) 2 μ)
    (h' : MemLp (fun y : G n => F' y.val) 2 μ) : cls μ (F + F') = cls μ F + cls μ F' := by
  rw [GlobalTheory.CompanionTheory.SecBd.cls_eq μ h, GlobalTheory.CompanionTheory.SecBd.cls_eq μ h', GlobalTheory.CompanionTheory.SecBd.cls_eq μ (f := F + F') (h.add h')]
  exact MemLp.toLp_add h h'

end Sob

theorem om_mem (hR : RCalc) (E : KMod n) {f : Mat n → E.V} (hf : f ∈ CE E) : Om f ∈ CE E := by
  have h1 := (hR n).2.1 E f hf true 2
  have h2 := (hR n).2.1 E f hf false 2
  refine ⟨Om_smooth hf.1, fun g hg k => ?_⟩
  simp only [Om, Pi.smul_apply, Pi.add_apply, h1.2 g hg k, h2.2 g hg k, map_add (f := _), map_smul]

theorem strong [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (Q : E.V →L[ℂ] E.V) (hR : RCalc)
    (hL : ∀ f ∈ CE E, ∀ g ∈ GLs n, Lap f g = -Om f g + Q (f g)) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Mat n → E.V, Sob μ f → IsSec E f → ∀ B : E.V →L[ℂ] E.V,
      ‖cls μ (Lap^[j] fun y => B (f y))‖ ≤ C * ‖B‖ * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ := by
  induction j with
  | zero =>
    refine ⟨1, zero_le_one, fun f hS _ B => ?_⟩
    have hm : MemLp (fun y : G n => B (f y.val)) 2 μ := (sob_post B hS).2 []
    have h := GlobalTheory.CompanionTheory.SecBd.norm_le_of_ae μ (f := f) (hS.2 []) (cls μ fun y => B (f y)) B
      (GlobalTheory.CompanionTheory.SecBd.cls_ae μ hm)
    simpa using h
  | succ j ih =>
    obtain ⟨C, hC, ih⟩ := ih
    refine ⟨C * (1 + ‖Q‖), by positivity, fun f hS hsec B => ?_⟩
    have hCE : f ∈ CE E := ⟨hS.1, hsec⟩
    have hOS := sob_Om hS
    have hOC := om_mem hR E hCE
    let a : Mat n → E.V := fun y => (-B) (Om f y)
    let b : Mat n → E.V := fun y => (B * Q) (f y)
    have ha : Sob μ a := sob_post _ hOS
    have hb : Sob μ b := sob_post _ hS
    have e1 : Set.EqOn (Lap fun y => B (f y)) (a + b) (GLs n) := fun g hg => by
      refine (Lap_post B hS.1 hg).trans ?_
      show B (Lap f g) = (-B) (Om f g) + (B * Q) (f g)
      rw [hL f hCE g hg]
      simp
    have e2 : Set.EqOn (Lap^[j + 1] fun y => B (f y)) (Lap^[j] a + Lap^[j] b) (GLs n) := fun g hg =>
      (iter_congr j e1 hg).trans (iter_add j ha.1 hb.1 hg)
    have mA : MemLp (fun y : G n => (Lap^[j] a) y.val) 2 μ := (sob_iter j ha).2 []
    have mB : MemLp (fun y : G n => (Lap^[j] b) y.val) 2 μ := (sob_iter j hb).2 []
    have e3 : cls μ (Lap^[j + 1] fun y => B (f y)) = cls μ (Lap^[j] a) + cls μ (Lap^[j] b) := by
      rw [← cls_add mA mB]
      exact (GlobalTheory.CompanionTheory.SecBd.cls_congr μ (f := Lap^[j] a + Lap^[j] b) (mA.add mB)
        fun g hg => (e2 hg).symm).symm
    have b1 : ‖cls μ (Lap^[j] a)‖ ≤ C * ‖-B‖ * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] (Om f))‖ :=
      ih (Om f) hOS hOC.2 (-B)
    have b2 : ‖cls μ (Lap^[j] b)‖ ≤ C * ‖B * Q‖ * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ :=
      ih f hS hsec (B * Q)
    set S := ∑ i ∈ range (j + 1 + 1), ‖cls μ (Om^[i] f)‖ with hSdef
    have s1 : ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] (Om f))‖ ≤ S := by
      have e := Finset.sum_range_succ' (fun i => ‖cls μ (Om^[i] f)‖) (j + 1)
      rw [hSdef, e]
      exact le_add_of_nonneg_right (norm_nonneg _)
    have s2 : ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ ≤ S := by
      rw [hSdef, Finset.sum_range_succ _ (j + 1)]
      exact le_add_of_nonneg_right (norm_nonneg _)
    have hBQ : ‖B * Q‖ ≤ ‖B‖ * ‖Q‖ := norm_mul_le _ _
    have c1 : C * ‖-B‖ * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] (Om f))‖ ≤ C * ‖B‖ * S := by
      rw [norm_neg]
      exact mul_le_mul_of_nonneg_left s1 (by positivity)
    have c2 : C * ‖B * Q‖ * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ ≤ C * (‖B‖ * ‖Q‖) * S := by
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
      exact mul_le_mul (mul_le_mul_of_nonneg_left hBQ hC) s2
        (Finset.sum_nonneg fun _ _ => norm_nonneg _) (by positivity)
    rw [e3]
    calc _ ≤ ‖cls μ (Lap^[j] a)‖ + ‖cls μ (Lap^[j] b)‖ := norm_add_le _ _
      _ ≤ C * ‖B‖ * S + C * (‖B‖ * ‖Q‖) * S := add_le_add (b1.trans c1) (b2.trans c2)
      _ = C * (1 + ‖Q‖) * ‖B‖ * S := by ring

theorem sectionBound : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (Q : E.V →L[ℂ] E.V), LgFacts → Unimod → RCalc → ClsFacts →
    (∀ f ∈ CE E, ∀ g ∈ GLs n, GlobalTheory.CompanionTheory.FcSmooth.Lap f g = -Om f g + Q (f g)) →
    ∀ j : ℕ, ∃ C : ℝ, ∀ f : Mat n → E.V, Sob μ f → IsSec E f →
      ‖cls μ (GlobalTheory.CompanionTheory.FcSmooth.Lap^[j] f)‖ ≤ C * ∑ i ∈ range (j + 1), ‖cls μ (Om^[i] f)‖ := by
  intro n _ _ μ _ E Q _ _ hR _ hL j
  obtain ⟨C, -, h⟩ := strong μ E Q hR hL j
  refine ⟨C * ‖(1 : E.V →L[ℂ] E.V)‖, fun f hS hs => ?_⟩
  simpa only [ContinuousLinearMap.one_apply] using h f hS hs 1

end GlobalTheory.CompanionTheory.LapSec
end
end

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.mirabolic_pairing_conductor_extension : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ (v' : V') (A : ℂ), EvVal ν ψ T B v v' A ∧ A ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.exists_evVal_ne_zero | exact GlobalTheory.CompanionTheory.MirPair.exists_evVal_ne_zero | (intros; apply GlobalTheory.CompanionTheory.MirPair.exists_evVal_ne_zero <;> assumption)
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

theorem _root_.GlobalTheory.T.unitary_iwasawa_bruhat_decomposition : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ g : GU σ n, ∃ (b w i : GU σ n) (π : Equiv.Perm (Fin n)), IsBorelU b ∧ IsPermW w π ∧ i ∈ IwU σ n ∧ g = b * w * i := by
  first | exact @GlobalTheory.CompanionTheory.BruhatIw.bruhat_iwasawa | exact GlobalTheory.CompanionTheory.BruhatIw.bruhat_iwasawa | (intros; apply GlobalTheory.CompanionTheory.BruhatIw.bruhat_iwasawa <;> assumption)
end
