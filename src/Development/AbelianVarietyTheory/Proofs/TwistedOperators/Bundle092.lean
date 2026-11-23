module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle084
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValTwoBlockParahoricInfTorusConjBlockwise
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle086
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle087
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledLatticePrimitiveIsotropicFrameCompletion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

@[expose] public section

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.pairwise_disjoint_parahoricTorusDoubleCoset_antitone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k → ∀ (r l t : ℕ),
    Pairwise (Function.onFun Disjoint fun e : {e : Fin (l * t) → ℤ // Antitone e} =>
      (dcell ϖ (e.1 ∘ (blkEquiv l t).symm) : Set (GL (Fin r ⊕ Blocks l t) k))) := by
  first | exact @GlobalTheory.CellDisjoint.dcell_pairwise_disjoint | exact GlobalTheory.CellDisjoint.dcell_pairwise_disjoint | (intros; apply GlobalTheory.CellDisjoint.dcell_pairwise_disjoint <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.parahoricDatum_torus_integrand_eq_indicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
    ∀ (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ : kˣ →* ℂˣ), IsUnitaryChar ξ → ∀ (e : D → ℤ) (x : Matrix (A ⊕ E) (A ⊕ D) k),
    datum ξ (x * (mtor ϖ e : GL (A ⊕ D) k).val) * starRingEnd ℂ (datum ξ x) =
      Set.indicator {y : Matrix (A ⊕ E) (A ⊕ D) k | InSupp (y * (mtor ϖ (fun i => -max 0 (-e i)) : GL (A ⊕ D) k).val)}
        (fun _ => (1 : ℂ)) x := by
  first | exact @GlobalTheory.TorusIntegrand.integrand | exact GlobalTheory.TorusIntegrand.integrand | (intros; apply GlobalTheory.TorusIntegrand.integrand <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.val_twoBlockParahoric_inf_torusConj_blockwise : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ),
    Units.val '' (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom ⊓ parahoric k A D :
        Subgroup (GL (A ⊕ D) k)) : Set (GL (A ⊕ D) k)) =
      {x | x.toBlocks₁₁ ∈ Units.val '' (KO k A : Set (GL A k)) ∧
        x.toBlocks₁₂ ∈ {y : Matrix A D k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ max 0 (-e j))} ∧
        x.toBlocks₂₁ ∈ {y : Matrix D A k | ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ (1 + max 0 (e i)))} ∧
        x.toBlocks₂₂ ∈ Units.val '' (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom ⊓ KO k D :
          Subgroup (GL D k)) : Set (GL D k))} := by
  first | exact @GlobalTheory.ParahoricConjBlocks.blockset | exact GlobalTheory.ParahoricConjBlocks.blockset | (intros; apply GlobalTheory.ParahoricConjBlocks.blockset <;> assumption)
end

section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJetCalc

section General

variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedAddCommGroup B] [NormedSpace ℂ B]
  [CompleteSpace B]

theorem analyticAt_linField {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (L : A →L[ℂ] A) :
    AnalyticAt ℂ (fun w => fderiv ℂ f w (L w)) z := by

  have hd : AnalyticAt ℂ (fderiv ℂ f) z := hf.fderiv
  have hp : AnalyticAt ℂ (fun w => (fderiv ℂ f w, L w)) z := hd.prod (L.analyticAt z)
  have hev : AnalyticAt ℂ (fun q : (A →L[ℂ] B) × A => q.1 q.2) (fderiv ℂ f z, L z) :=
    (ContinuousLinearMap.id ℂ (A →L[ℂ] B)).analyticAt_bilinear _
  exact AnalyticAt.comp (g := fun q : (A →L[ℂ] B) × A => q.1 q.2)
    (f := fun w => (fderiv ℂ f w, L w)) hev hp

theorem fderiv_linField {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (L : A →L[ℂ] A) (M : A) :
    fderiv ℂ (fun w => fderiv ℂ f w (L w)) z M
      = fderiv ℂ (fderiv ℂ f) z M (L z) + fderiv ℂ f z (L M) := by

  have hD : HasFDerivAt (fderiv ℂ f) (fderiv ℂ (fderiv ℂ f) z) z :=
    hf.fderiv.differentiableAt.hasFDerivAt
  have hP := hD.clm_apply L.hasFDerivAt
  rw [hP.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

theorem snd_symm {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (M N : A) :
    fderiv ℂ (fderiv ℂ f) z M N = fderiv ℂ (fderiv ℂ f) z N M := by

  have hS : IsSymmSndFDerivAt ℂ f z := hf.contDiffAt.isSymmSndFDerivAt_of_omega
  exact hS M N

theorem comm_linField {f : A → B} {z : A} (hf : AnalyticAt ℂ f z) (L K : A →L[ℂ] A) :
    fderiv ℂ (fun w => fderiv ℂ f w (L w)) z (K z) - fderiv ℂ (fun w => fderiv ℂ f w (K w)) z (L z)
      = fderiv ℂ f z (L (K z) - K (L z)) := by

  rw [fderiv_linField hf L, fderiv_linField hf K, snd_symm hf (K z) (L z), map_sub]
  abel

end General

theorem leftInvariant_calculus (n : ℕ) (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (f : Matrix (Fin n) (Fin n) ℂ → B) (hf : AnalyticAt ℂ f 1) :
    (∀ Z, AnalyticAt ℂ (Rz Z f) 1) ∧
    (∀ A Z, (fun z => Rz A (Rz Z f) z - Rz Z (Rz A f) z) =ᶠ[𝓝 1] Rz (A * Z - Z * A) f) ∧
    ∀ Y Z : Matrix (Fin n) (Fin n) ℂ, (fun z => fderiv ℂ (Rz Z f) z (Y * z)) =ᶠ[𝓝 1]
      Rz Z (fun z => fderiv ℂ f z (Y * z)) := by

  let RM : Matrix (Fin n) (Fin n) ℂ → (Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) :=
    fun Z => LinearMap.toContinuousLinearMap (LinearMap.mulRight ℂ Z)
  let LM : Matrix (Fin n) (Fin n) ℂ → (Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) :=
    fun Y => LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ Y)
  have hRz : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (g : Matrix (Fin n) (Fin n) ℂ → B),
      Rz Z g = fun w => fderiv ℂ g w (RM Z w) := fun Z g => rfl
  have hev : ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), AnalyticAt ℂ f z :=
    hf.eventually_analyticAt
  refine ⟨fun Z => ?_, fun A Z => ?_, fun Y Z => ?_⟩
  · rw [hRz]
    exact analyticAt_linField hf (RM Z)
  · filter_upwards [hev] with z hz
    have hc := comm_linField hz (RM Z) (RM A)
    have hb : (RM Z) ((RM A) z) - (RM A) ((RM Z) z) = z * (A * Z - Z * A) := by
      show z * A * Z - z * Z * A = z * (A * Z - Z * A)
      rw [mul_sub, mul_assoc, mul_assoc]
    rw [hb] at hc
    exact hc
  · filter_upwards [hev] with z hz
    have hc := comm_linField hz (RM Z) (LM Y)
    have hb : (RM Z) ((LM Y) z) - (LM Y) ((RM Z) z) = 0 := by
      show Y * z * Z - Y * (z * Z) = 0
      rw [mul_assoc, sub_self]
    rw [hb, map_zero, sub_eq_zero] at hc
    exact hc

end GlobalTheory.SphJetCalc
end
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.exists_unitary_block_diagonal_levi_element : LeviExists := by
  first | exact @GlobalTheory.InertZeta.leviExists | exact GlobalTheory.InertZeta.leviExists | (intros; apply GlobalTheory.InertZeta.leviExists <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.traceZero_integers_index_in_uniformizer_multiples : TraceIndex := by
  first | exact @GlobalTheory.InertZeta.traceIndex | exact GlobalTheory.InertZeta.traceIndex | (intros; apply GlobalTheory.InertZeta.traceIndex <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.unitary_iwasawa_cells_disjoint : CosetInj := by
  first | exact @GlobalTheory.InertZeta.cosetInj | exact GlobalTheory.InertZeta.cosetInj | (intros; apply GlobalTheory.InertZeta.cosetInj <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.unitaryIwasawaCosetSurj_of_leviElementExists : LeviExists → CosetSurj := by
  first | exact @GlobalTheory.InertZeta.cosetSurj_of_leviExists | exact GlobalTheory.InertZeta.cosetSurj_of_leviExists | (intros; apply GlobalTheory.InertZeta.cosetSurj_of_leviExists <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.unitary_rank_le_one_integral_points : SmallRank := by
  first | exact @GlobalTheory.InertZeta.smallRank | exact GlobalTheory.InertZeta.smallRank | (intros; apply GlobalTheory.InertZeta.smallRank <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.integralLatticeInverseIndex_of_elementaryDivisors : Smith → LatIndex := by
  first | exact @GlobalTheory.InertZeta.latIndex_of_smith | exact GlobalTheory.InertZeta.latIndex_of_smith | (intros; apply GlobalTheory.InertZeta.latIndex_of_smith <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.sphericalInductionTransitivity_of_leviExists : LeviExists → SphTrans := by
  first | exact @GlobalTheory.InertZeta.sphTrans | exact GlobalTheory.InertZeta.sphTrans | (intros; apply GlobalTheory.InertZeta.sphTrans <;> assumption)
end

section

open GlobalTheory.InertZeta

theorem _root_.GlobalTheory.T.doubledLattice_primitive_isotropic_frame_completion : Completion := by
  first | exact @GlobalTheory.FrameCompletion.completion | exact GlobalTheory.FrameCompletion.completion | (intros; apply GlobalTheory.FrameCompletion.completion <;> assumption)
end
