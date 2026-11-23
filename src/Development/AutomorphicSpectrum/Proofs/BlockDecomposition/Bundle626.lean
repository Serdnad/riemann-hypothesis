module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle616
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProduct
public import Mathlib.Probability.Kernel.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle617
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle056
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle619
public import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle620
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle618
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle452
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import GroundTheory.PAdicHodge.Bundle004

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.CompanionTheory.RegInt

variable {D : D7} {V : HSp D} {r : ℕ}

def firstCols (X : Matrix (Fin V.rank) (Fin r) D.host.E) (j : Fin r) :
    Matrix (Fin V.rank) (Fin (j.val + 1)) D.host.E := X.submatrix id (Fin.castLE j.2)

def root (t : Fin r → ℝ) (j : Fin r) : ℝ := if h : j.val + 1 < r then t j / t ⟨j.val + 1, h⟩ else t j

theorem isIsoFrame_firstCols {X Y : Matrix (Fin V.rank) (Fin r) D.host.E}
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r) : IsIsoFrame V (firstCols X j) := by
  refine ⟨Nat.succ_pos _, ?_, ?_⟩
  · have h1 : LinearIndependent D.host.E (fun i : Fin r => fun a : Fin V.rank => X a i) := by
      refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
      have h3 : ∀ a, ∑ l, g l * X a l = 0 := fun a => by
        have := congrFun hg a
        simpa [Finset.sum_apply, mul_comm] using this
      have h4 : (fun l => (D.sp.cm.sig : D.host.E →+* D.host.E) (g l)) ᵥ*
          Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X = 0 := by
        funext a
        have := congrArg (D.sp.cm.sig : D.host.E →+* D.host.E) (h3 a)

        simp only [map_sum, map_mul, map_zero] at this
        simpa [Matrix.vecMul, dotProduct, Formalism.UG.cT] using this
      have h5 := congrArg (fun v => v ᵥ* (V.gram * Y)) h4
      simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul, ← Matrix.mul_assoc, hW.xy, Matrix.vecMul_one] at h5
      have h6 := congrFun h5 i
      simpa using h6
    have h2 : (firstCols X j).transpose = (fun i : Fin r => fun a : Fin V.rank => X a i) ∘ Fin.castLE j.2 := by
      funext i a; rfl
    change LinearIndependent D.host.E (firstCols X j).transpose
    rw [h2]
    exact h1.comp _ (Fin.castLE_injective _)
  · have h := hW.xx
    refine Matrix.ext fun a b => ?_
    have := congrFun (congrFun h (Fin.castLE j.2 a)) (Fin.castLE j.2 b)
    simpa [Matrix.mul_apply, Formalism.UG.cT, firstCols] using this

end GlobalTheory.CompanionTheory.RegInt
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_tamagawa_measure_normalization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ n : ℕ, ∃ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v)) (minf : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ n → Measure (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ n → Measure (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf ∧ (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) ∧ IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) σ b laminf n) minf ∧ ∀ v, IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b (lam v) n M) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) σ b (lam v) n) (m v) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Frame.exists_coord_fibres | exact GlobalTheory.CompanionTheory.WeilSiegel.Frame.exists_coord_fibres | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Frame.exists_coord_fibres <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.local_gram_fibration_disintegration : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree R σ J n μ ν m → ∀ (h : HA R σ J) (S : HermR R σ n), (m S).map (actW R σ J h) = m S := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv.map_actW_fibre_free | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv.map_actW_fibre_free | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv.map_actW_fibre_free <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.siegel_weil_product_of_local_identities : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), SWFree σ J T hT → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (m : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) m → ∀ C : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact C → m (hermOf (Fv F v) σ T hT) C < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt.fibre_compact_lt_top | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt.fibre_compact_lt_top | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt.fibre_compact_lt_top <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.global_volume_rank_one_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), IsGramFibFree (Ainf F) σ J 1 (coordW (Ainf F) b laminf 1 M) (coordHerm (Ainf F) σ b laminf 1) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 M) (coordHerm (Fv F v) σ b (lam v) 1) (m v)) → SigmaFinite (minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) ∧ (∀ v, SigmaFinite (m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀))) ∧ ((framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)).Nonempty → minf (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0 ∧ ∀ v, m v (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.free_fibre_zero | exact GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.free_fibre_zero | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.free_fibre_zero <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.local_fibre_measure_orthogonal_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N n : ℕ) (J₂ : Matrix (Fin N) (Fin N) E), IsHermND σ J₂ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m : HermR R σ n → Measure (Fin n → Fin N → R ⊗[F] E), IsGramFibFree R σ J₂ n (coordW R b lam n N) (coordHerm R σ b lam n) m → (∀ S, SFinite (m S)) ∧ (∃ κ : ProbabilityTheory.Kernel (HermR R σ n) (Fin n → Fin N → R ⊗[F] E), ProbabilityTheory.IsSFiniteKernel κ ∧ ∀ S, κ S = m S) ∧ (∀ (C : Set (Fin n → Fin N → R ⊗[F] E)) (D : Set (HermR R σ n)), IsCompact C → C ⊆ {X | LinearIndependent (R ⊗[F] E) X} → IsCompact D → ∃ c : ℝ≥0, ∀ S ∈ D, m S C ≤ c) ∧ ∀ S : HermR R σ n, ∀ᵐ X ∂(m S), gramR R σ J₂ X = (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) ∧ LinearIndependent (R ⊗[F] E) X := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic | exact GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV

theorem ae_lift_eq {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure V} {ν : Measure X} {q : V → Y} {ι : X → Y} {W : Set V} {B : Set X} {fib : X → Measure V}
    (h : IsFibreFamily μ q ι W ν B fib) {g : V → X} (hg : ∀ x, q x = ι (g x)) (hι : Function.Injective ι)
    (b : X) : ∀ᵐ x ∂(fib b), g x = b := by
  refine measure_mono_null ?_ (h.1 b)
  intro x hx hx'
  exact hx (hι ((hg x).symm.trans hx'.1))

theorem fibre_mass_on {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {q : V → Y} {ι : X → Y} {W : Set V} {B : Set X}
    {fib : X → Measure V} (h : IsFibreFamily μ q ι W ν B fib) {g : V → X} (hg : ∀ x, q x = ι (g x))
    (hι : Function.Injective ι) (hgm : Measurable g) {A : Set V} {S : Set X} (hA : MeasurableSet A)
    (hS : MeasurableSet S) (hW : A ∩ g ⁻¹' S ⊆ W) :
    μ (A ∩ g ⁻¹' S) = ∫⁻ s in S, fib s A ∂ν := by
  have hT : MeasurableSet (A ∩ g ⁻¹' S) := hA.inter (hgm hS)
  have e := h.2.1 ((A ∩ g ⁻¹' S).indicator 1) (measurable_one.indicator hT)
  simp only [lintegral_indicator_one hT] at e
  rw [Measure.restrict_apply hT, Set.inter_eq_left.2 hW] at e
  rw [e, ← lintegral_indicator hS]
  refine lintegral_congr fun b => ?_
  have hae := ae_lift_eq h hg hι b
  by_cases hb : b ∈ S
  · rw [Set.indicator_of_mem hb]
    refine measure_congr ?_
    filter_upwards [hae] with x hx
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    show g x ∈ S
    rwa [hx]
  · rw [Set.indicator_of_notMem hb]
    refine measure_mono_null (t := {x | ¬ g x = b}) ?_ hae
    intro x hx hxb
    apply hb
    rw [← hxb]
    exact hx.2

theorem avg_gen {V X Y : Type} {_ : TopologicalSpace V} {_ : MeasurableSpace V} {_ : TopologicalSpace X}
    {_ : MeasurableSpace X} {_ : AddCommGroup X} {μ : Measure V} {ν : Measure X} {q : V → Y} {ι : X → Y}
    {W : Set V} {B : Set X} {fib : X → Measure V} (h : IsFibreFamily μ q ι W ν B fib) {g : V → X}
    (hg : ∀ x, q x = ι (g x)) (hι : Function.Injective ι) (hgc : Continuous g) (hV2 : T2Space V)
    (hVb : BorelSpace V) (hX2 : T2Space X) (hXb : BorelSpace X) (hXg : IsTopologicalAddGroup X)
    (hXl : LocallyCompactSpace X) (hXs : SecondCountableTopology X) (hμ : IsFiniteMeasureOnCompacts μ)
    (hν : ν.IsAddHaarMeasure) (hB : IsOpen B) (hWB : ∀ x, g x ∈ B → x ∈ W) {c : X} (hc : c ∈ B) {A : Set V}
    (hAc : IsCompact A) (hAo : IsOpen A) {U : ℕ → Set X} (hU : ∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : X) ∈ U k)
    (hUt : Filter.Tendsto U Filter.atTop (nhds (0 : X)).smallSets) :
    (∀ k, MeasurableSet (A ∩ {x | c - g x ∈ U k}) ∧ μ (A ∩ {x | c - g x ∈ U k}) ≠ ⊤) ∧
      Filter.Tendsto (fun k => (μ (A ∩ {x | c - g x ∈ U k})).toReal / (ν (U k)).toReal) Filter.atTop
        (nhds (fib c A).toReal) := by
  haveI : ν.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  have hBc := hB.mem_nhds hc

  let S : ℕ → Set X := fun k => {s | c - s ∈ U k}
  have hSo : ∀ k, IsOpen (S k) := fun k => (hU k).2.1.preimage (continuous_const.sub continuous_id)
  have hSm : ∀ k, MeasurableSet (S k) := fun k => (hSo k).measurableSet
  have hSc : ∀ k, c ∈ S k := fun k => by
    show c - c ∈ U k
    rw [sub_self]
    exact (hU k).2.2
  have hSU : ∀ k, ν (S k) = ν (U k) := fun k =>
    (Measure.measurePreserving_sub_left _ c).measure_preimage (hU k).2.1.measurableSet.nullMeasurableSet
  have hpos : ∀ k, ν (S k) ≠ 0 := fun k => (hSo k).measure_ne_zero _ ⟨c, hSc k⟩
  have htop : ∀ k, ν (S k) ≠ ⊤ := fun k => by
    rw [hSU]
    exact (hU k).1.measure_lt_top.ne
  have hl : Filter.Tendsto S Filter.atTop (nhds c).smallSets := by
    rw [Filter.tendsto_smallSets_iff]
    intro t ht
    have hcont : Filter.Tendsto (fun u : X => c - u) (nhds 0) (nhds c) := by
      have : Continuous fun u : X => c - u := continuous_const.sub continuous_id
      simpa using this.tendsto 0
    have h0 := (Filter.tendsto_smallSets_iff.1 hUt) _ (hcont ht)
    filter_upwards [h0] with k hk s hs
    have := hk (show c - s ∈ U k from hs)
    simpa using this

  obtain ⟨k0, hk0⟩ := (hl.eventually (Filter.eventually_smallSets_subset.2 hBc)).exists
  have hNc : IsCompact (S k0) := (Homeomorph.subLeft c).isCompact_preimage.2 (hU k0).1
  let A' : Set V := A ∩ g ⁻¹' S k0
  have hA'c : IsCompact A' := hAc.inter_right (hNc.isClosed.preimage hgc)
  have hA'o : IsOpen A' := hAo.inter ((hSo k0).preimage hgc)
  have hA'm : MeasurableSet A' := hA'o.measurableSet
  have hA'W : A' ⊆ W := fun x hx => hWB x (hk0 hx.2)

  let φ : V → ℝ := A'.indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hA'o.frontier_eq, hA'c.isClosed.closure_eq]
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro hA'c fun x hx => ?_
    exact Set.indicator_of_notMem hx _
  have hts : tsupport φ ⊆ W := by
    refine subset_trans (closure_minimal (fun x hx => ?_) hA'c.isClosed) hA'W
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  obtain ⟨hI, hC⟩ := h.2.2 φ hφc hφs hts
  have hint : ∀ s, ∫ x, φ x ∂(fib s) = (fib s A').toReal := fun s => by
    simp [φ, integral_indicator hA'm, Measure.real]
  have hG : ContinuousAt (fun s => (fib s A').toReal) c := by
    have h := hC.continuousAt hBc
    simpa only [hint] using h
  have hfin : ∀ᶠ s in nhds c, fib s A' ≠ ⊤ := by
    filter_upwards [hBc] with s hs
    have h := hI s hs
    rw [integrable_indicator_iff hA'm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  have hcv : fib c A' = fib c A := by
    refine measure_congr ?_
    filter_upwards [ae_lift_eq h hg hι c] with x hx
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    show g x ∈ S k0
    rw [hx]
    exact hSc k0
  refine ⟨fun k => ?_, ?_⟩
  · have hO : IsOpen (A ∩ {x | c - g x ∈ U k}) := hAo.inter ((hSo k).preimage hgc)
    exact ⟨hO.measurableSet, ne_top_of_le_ne_top hAc.measure_lt_top.ne (measure_mono Set.inter_subset_left)⟩
  · have key := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV.tendsto_mean ν (fun s => fib s A') c hG hfin S hSm hl hpos htop
    simp only [hcv] at key
    refine key.congr' ?_
    filter_upwards [hl.eventually (Filter.eventually_smallSets_subset.2 ((hSo k0).mem_nhds (hSc k0)))] with k hk
    have e : A ∩ {x | c - g x ∈ U k} = A' ∩ g ⁻¹' S k := by
      ext x
      exact ⟨fun h => ⟨⟨h.1, hk h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [hSU k, e, fibre_mass_on h hg hι hgc.measurable hA'm (hSm k) (fun x hx => hA'W hx.1)]

end GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV

theorem GlobalTheory.CompanionTheory.SiegelND.Coef.avgV_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ c : HermR (Fv F v) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det → ∀ A : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → ∀ U : ℕ → Set (HermR (Fv F v) σ n), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : HermR (Fv F v) σ n) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets → (∀ k, MeasurableSet (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k}) ∧ GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k}) ≠ ⊤) ∧ Filter.Tendsto (fun k => (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k})).toReal / (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal) Filter.atTop (nhds (mv c A).toReal) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ d b v lv hlv mv hmv c hc A hAc hAo U hU hUt
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  obtain ⟨-, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Fv F v) d b lv hlv.1
  obtain ⟨e1, e2, e3, e4, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Fv F v) n
  have hgc : Continuous (gramH hCM hJ (Fv F v) : (Fin n → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ n) :=
    Continuous.subtype_mk (a10 n M J) _
  have hUo : IsOpen {r : Fv F v | IsUnit r} := by
    have : {r : Fv F v | IsUnit r} = {r | r ≠ 0} := by
      ext r
      simp [isUnit_iff_ne_zero]
    rw [this]
    exact isOpen_ne
  have hB : IsOpen {S : HermR (Fv F v) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} :=
    PI.VolStabS.isOpen_unitHerm (Fv F v) hUo σ n
  exact AvgV.avg_gen (q := gramR (Fv F v) σ J) (ι := Subtype.val) (g := gramH hCM hJ (Fv F v)) hmv
    (fun _ => rfl) Subtype.val_injective hgc inferInstance (a8 n M) e3 e4 inferInstance e1 e2
    (hW n M).toIsFiniteMeasureOnCompacts (hH n) hB (fun _ h => h) hc hAc hAo hU hUt
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.hermitian_coordinates_natural_in_ring : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (R R' : Type) [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ) (S : HermR R σ n) (i : Idx n d), hCo R' σ b (hermMap f σ S) i = f (hCo R σ b S i) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_hermMap | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_hermMap | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.hCo_hermMap <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.continuous_fourier_character_of_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ T : Matrix (Fin n) (Fin n) E, Continuous (chiT σ ψ T) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.continuous_chiT | exact GlobalTheory.CompanionTheory.SiegelND.Coef.continuous_chiT | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.continuous_chiT <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.siegel_weil_integral_normalised : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, Integrable Φ dx → ∀ τ : HermR (AF F) σ n → ℂ, Integrable (fouH σ ψ db τ) db → (∀ z, ∫ y, fouH σ ψ db τ y * ψ (pairHerm (AF F) σ n y z) ∂db = τ (-z)) → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∫ y, fouH σ ψ db τ y * (starN σ J ψ dx Φ y * chiT σ ψ T y) ∂db = ∫ x, Φ x * τ (hermOf (AF F) σ T hT - gramH hCM hJ (AF F) x) ∂dx := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.fubini_starN | exact GlobalTheory.CompanionTheory.SiegelND.Coef.fubini_starN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.fubini_starN <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain
open Neutral.B1 hiding G
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms


theorem _root_.GlobalTheory.T.local_global_artin_compatible : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) {Ωv : Type} [Field Ωv] [Algebra (w.adicCompletion E) Ωv]
    [IsSepClosure (w.adicCompletion E) Ωv] (j : Ω →+* Ωv),
    (∀ y : E, j (algebraMap E Ω y) = algebraMap (w.adicCompletion E) Ωv (algebraMap E (w.adicCompletion E) y)) →
    ∀ (a : (w.adicCompletion E)ˣ) (σ : G E Ω) (g : Ωv ≃ₐ[w.adicCompletion E] Ωv),
    (∀ x : Ω, g (j x) = j (σ x)) →
    (∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension (w.adicCompletion E) Ωv),
      ((localArtinMap (w.adicCompletion E) Ωv a ⟨y, hy⟩ : maximalAbelianExtension (w.adicCompletion E) Ωv) : Ωv) = g y) →
    ∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L],
    PositivityTheory.FamInh.res L (toAb E Ω σ) = PositivityTheory.FamInh.res L (PositivityTheory.FamInh.art0 E Ω (localIdele E w a)) := by
  first | exact @GlobalTheory.CompanionTheory.LTLink.local_restriction_abelianization_artin | exact GlobalTheory.CompanionTheory.LTLink.local_restriction_abelianization_artin | (intros; apply GlobalTheory.CompanionTheory.LTLink.local_restriction_abelianization_artin <;> assumption)
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms


theorem _root_.GlobalTheory.T.global_artin_map_unique : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art → art = (PositivityTheory.FamInh.art0 E Ω)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.ArtinMapUniq.eq_inv_arithmetic_artin_map | exact GlobalTheory.CompanionTheory.ArtinMapUniq.eq_inv_arithmetic_artin_map | (intros; apply GlobalTheory.CompanionTheory.ArtinMapUniq.eq_inv_arithmetic_artin_map <;> assumption)
end
end
