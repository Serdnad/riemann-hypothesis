module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle270
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff
import GroundTheory.AutomorphicForms.Bundle004
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle271
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle261
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

@[expose] public section

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.wave_kernel_composition : RCalc → WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (w w' : List (Bool × ℕ)) (g g' : ℝ → ℝ) (T T' : ℝ), IsWave E u → IsBump g T → IsBump g' T' → ∃ v : ℝ → Mat n → E.V, IsWave E v ∧ (∀ x ∈ GLs n, v 0 x = zOp w' (fun x' => ∫ t, (g' t : ℂ) • u t x') x) ∧ ∀ x ∈ GLs n, zOp w (fun x' => ∫ t, (g t : ℂ) • v t x') x = zOp (w ++ w') (fun x' => ∫ t, (gconv g g' t : ℂ) • u t x') x := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.wave_compose | exact GlobalTheory.CompanionTheory.WaveMult.wave_compose | (intros; apply GlobalTheory.CompanionTheory.WaveMult.wave_compose <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem exists_gal_extending_embedding : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l),
    ∃ g : GQ l, ∀ x : ↥K.1, g (x : Om l) = μ x := by
  intro l _ K μ
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits (F := ℚ_[l]) (E := Om l) (K := Om l)
    (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) (L := K.1) μ
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun x => ?_⟩
  exact DFunLike.congr_fun hφ x

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

section

set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep.ConvLap

open Set Filter Topology MeasureTheory

section General

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} {h : IsExpLieAlgebra G 𝔤}

open IsExpLieAlgebra

theorem isSmoothFun_convDeriv {κ : G → ℂ}
    (hκ : h.IsSmoothFun κ) (X : 𝔤) :
    h.IsSmoothFun (h.convDeriv X κ) :=
  isSmoothFun_comp_inv (h := h) (κ := h.rightDeriv X fun z : G => κ z⁻¹)
    (h.isSmoothFun_rightDeriv (isSmoothFun_comp_inv hκ) X)

theorem rightDeriv_eq_integral_convDeriv_of_conv [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] {κ : G → ℂ}
    (hκ : h.IsSmoothFun κ) (hκc : HasCompactSupport κ)
    {f F : G → ℂ} (hfc : Continuous f) (hF : h.IsSmoothFun F)
    (hconv : ∀ x, F x = ∫ y, f (x * y) * κ y ∂μ) (X : 𝔤) (g : G) :
    h.rightDeriv X F g = ∫ y, f (g * y) * h.convDeriv X κ y ∂μ := by
  have hec : Continuous fun t : ℝ => h.expG (t • X) :=
    h.continuous_expG.comp (continuous_id.smul continuous_const)
  have hfg : Continuous fun y : G => f (g * y) := hfc.comp (continuous_const.mul continuous_id)
  have hκ'c : Continuous fun z : G => κ z⁻¹ := continuous_of_isSmoothFun (isSmoothFun_comp_inv hκ)
  have hDc := continuous_rightDeriv_comp_inv hκ X
  have hshift : ∀ t : ℝ, F (g * h.expG (t • X)) =
      ∫ y, f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹ ∂μ := by
    intro t
    rw [hconv (g * h.expG (t • X))]
    have := integral_mul_left_eq_self (μ := μ)
      (fun y => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹) (h.expG (t • X))
    rw [← this]
    congr 1
    funext y
    simp [mul_assoc, mul_inv_rev]
  have hderiv : ∀ (y : G) (t : ℝ), HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (s • X))⁻¹)
      (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) t := by
    intro y t
    have h1 := h.hasDerivAt_rightDeriv (isSmoothFun_comp_inv hκ) X (y⁻¹ * h.expG (t • X))
    have h1' : HasDerivAt (fun s : ℝ => κ (y⁻¹ * h.expG (t • X) * h.expG (s • X))⁻¹)
        (h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X))) (t - t) := by
      rw [sub_self]; exact h1
    refine (h1'.comp_sub_const t t).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only [mul_assoc, ← h.expG_add_smul, add_sub_cancel]
  set S : Set G := (fun p : ℝ × G => h.expG (p.1 • X) * p.2) ''
    (Metric.closedBall (0 : ℝ) 1 ×ˢ tsupport κ) with hSdef
  have hS : IsCompact S :=
    ((isCompact_closedBall 0 1).prod hκc).image
      ((hec.comp continuous_fst).mul continuous_snd)
  have hvanish : ∀ (y : G) (t : ℝ), t ∈ Metric.closedBall (0 : ℝ) 1 → y ∉ S →
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)) = 0 := by
    intro y t ht hy
    refine rightDeriv_comp_inv_eq_zero (fun hk => hy ⟨(t, (h.expG (t • X))⁻¹ * y), ⟨ht, ?_⟩, ?_⟩) X
    · simpa [mul_inv_rev] using hk
    · simp
  obtain ⟨M, hM⟩ := exists_bound_rightDeriv_comp_inv hκ hκc X
  have hbound : Integrable (S.indicator fun y => ‖f (g * y)‖ * M) μ := by
    refine IntegrableOn.integrable_indicator ?_ hS.measurableSet
    exact (hfg.norm.mul continuous_const).continuousOn.integrableOn_compact hS
  have hint0 : Integrable (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) μ := by
    have : (fun y => f (g * y) * κ (y⁻¹ * h.expG ((0 : ℝ) • X))⁻¹) = fun y => f (g * y) * κ y := by
      funext y; simp
    rw [this]
    exact Continuous.integrable_of_hasCompactSupport (hfg.mul (continuous_of_isSmoothFun (f := κ) hκ))
      (hκc.mono' fun y hy => subset_tsupport κ (right_ne_zero_of_mul hy))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (t : ℝ) (y : G) => f (g * y) * κ (y⁻¹ * h.expG (t • X))⁻¹)
    (F' := fun (t : ℝ) (y : G) => f (g * y) *
      h.rightDeriv X (fun w : G => κ w⁻¹) (y⁻¹ * h.expG (t • X)))
    (x₀ := (0 : ℝ)) (s := Metric.ball (0 : ℝ) 1)
    (bound := S.indicator fun y => ‖f (g * y)‖ * M)
    (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun t =>
      (hfg.mul (hκ'c.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable) hint0
    (hfg.mul (hDc.comp (continuous_inv.mul continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun y t ht => by
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy, norm_mul]
        exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      · rw [indicator_of_notMem hy, hvanish y t (Metric.ball_subset_closedBall ht) hy, mul_zero,
          norm_zero])
    hbound
    (Eventually.of_forall fun y t _ => (hderiv y t).const_mul (f (g * y)))
  have hd1 : HasDerivAt (fun t : ℝ => F (g * h.expG (t • X))) (h.rightDeriv X F g) 0 :=
    h.hasDerivAt_rightDeriv hF X g
  have hd2 := key.2.congr_of_eventuallyEq (Eventually.of_forall hshift)
  rw [hd1.unique hd2]
  congr 1
  funext y
  simp [convDeriv]

end General

section Adelic

open AutomorphicForm

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem uAction_ι_eq_integral_convDeriv [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] {μ : MeasureTheory.Measure (archGroup K n)} [μ.IsHaarMeasure]
    (ψ u : archSmooth K n) {κ : archGroup K n → ℂ}
    (hκ : (isExpLieAlgebra K n).IsSmoothFun κ) (hκc : HasCompactSupport κ)
    (hu : ∀ g, (u : AdelicGLn.AdelicGL K n → ℂ) g =
      ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * κ y ∂μ)
    (X : (isExpLieAlgebra K n).lieSubalgebra) (g : AdelicGLn.AdelicGL K n) :
    (uAction (UniversalEnvelopingAlgebra.ι ℝ X) u : AdelicGLn.AdelicGL K n → ℂ) g =
      ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) *
        (isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ y ∂μ := by
  rw [uAction_ι_apply]
  have hconv : ∀ x, archSlice (u : AdelicGLn.AdelicGL K n → ℂ) g x =
      ∫ y, archSlice (ψ : AdelicGLn.AdelicGL K n → ℂ) g (x * y) * κ y ∂μ := by
    intro x
    simp only [archSlice_apply, map_mul, ← mul_assoc]
    exact hu _
  rw [rightDeriv_eq_integral_convDeriv_of_conv hκ hκc
    (IsExpLieAlgebra.continuous_of_isSmoothFun (ψ.2 g)) (u.2 g) hconv]
  simp only [archSlice_apply, one_mul]

theorem exists_kernel_uAction_uJ [MeasurableSpace (archGroup K n)]
    [BorelSpace (archGroup K n)] (μ : MeasureTheory.Measure (archGroup K n)) [μ.IsHaarMeasure]
    (ψ : archSmooth K n) (k : ℕ) :
    ∀ (J : Fin k → Fin (CuspidalSpectrum.archDim K n)) (u : archSmooth K n)
      (κ : archGroup K n → ℂ), (isExpLieAlgebra K n).IsSmoothFun κ → HasCompactSupport κ →
      (∀ g, (u : AdelicGLn.AdelicGL K n → ℂ) g =
        ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * κ y ∂μ) →
      ∃ D : archGroup K n → ℂ, (isExpLieAlgebra K n).IsSmoothFun D ∧ HasCompactSupport D ∧
        ∀ g : AdelicGLn.AdelicGL K n,
          ((uAction (CuspidalSpectrum.uJ (K := K) (n := n) k J) u :
            ↥(archSmooth K n)) : AdelicGLn.AdelicGL K n → ℂ) g =
            ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * D y ∂μ := by
  induction k with
  | zero =>
    intro J u κ hκ hκc hu
    refine ⟨κ, hκ, hκc, fun g => ?_⟩
    simpa [CuspidalSpectrum.uJ] using hu g
  | succ k ih =>
    intro J u κ hκ hκc hu
    set X := CuspidalSpectrum.lieOf (CuspidalSpectrum.archBasis K n (J 0)) with hX
    obtain ⟨D, hD, hDc, hrep⟩ := ih (Fin.tail J)
      (uAction (UniversalEnvelopingAlgebra.ι ℝ X) u)
      ((isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ)
      (isSmoothFun_convDeriv hκ _) (IsExpLieAlgebra.hasCompactSupport_convDeriv hκc _)
      (fun g => uAction_ι_eq_integral_convDeriv ψ u hκ hκc hu X g)
    refine ⟨D, hD, hDc, fun g => ?_⟩
    rw [CuspidalSpectrum.uAction_uJ_succ]
    exact hrep g

theorem exists_conv_uJ_of_aeval_laplacian : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ψ : AutomorphicForm.archSmooth K n) (d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra K n).lieSubalgebra) (P : Polynomial ℂ),
    P.Monic → 0 < P.natDegree →
    (∀ g, Polynomial.aeval ((AutomorphicForm.isExpLieAlgebra K n).laplacian (F := ℂ) b) P
      (AutomorphicForm.sliceL g ψ) = 0) →
    ∀ [MeasurableSpace (AutomorphicForm.archGroup K n)] [BorelSpace (AutomorphicForm.archGroup K n)]
      (μ : MeasureTheory.Measure (AutomorphicForm.archGroup K n)) [μ.IsHaarMeasure]
      (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim K n)),
      ∃ D : AutomorphicForm.archGroup K n → ℂ, Continuous D ∧ HasCompactSupport D ∧
        ∀ g : AdelicGLn.AdelicGL K n,
          ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := K) (n := n) k J) ψ :
            ↥(AutomorphicForm.archSmooth K n)) : AdelicGLn.AdelicGL K n → ℂ) g =
            ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * AutomorphicForm.infEmb K n y) * D y ∂μ := by
  intro K _ _ n ψ d b P hPm hPd hP _ _ μ _ k J
  obtain ⟨κ, hκs, hκc, -, hκ⟩ := (isExpLieAlgebra K n).exists_kernel_eq_conv_of_aeval_laplacian μ b P
    hPm hPd Filter.univ_mem
  have h1 : ∀ g, (ψ : AdelicGLn.AdelicGL K n → ℂ) g =
      ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n y) * κ y ∂μ := by
    intro g
    have := hκ (sliceL g ψ) (hP g) 1
    simpa [archSlice_apply] using this
  obtain ⟨D, hD, hDc, hrep⟩ := exists_kernel_uAction_uJ μ ψ k J ψ κ hκs hκc h1
  exact ⟨D, IsExpLieAlgebra.continuous_of_isSmoothFun hD, hDc, hrep⟩

end Adelic

end GlobalTheory.CompanionTheory.HCRep.ConvLap
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

theorem _root_.GlobalTheory.T.lp_integral_ae_pointwise : ∀ (A Y V : Type) [MeasurableSpace A] [MeasurableSpace Y] (α : Measure A) [SFinite α] (ν : Measure Y) [SigmaFinite ν] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (c : A → Lp V 2 ν) (F : A → Y → V), Integrable c α → AEStronglyMeasurable (Function.uncurry F) (α.prod ν) → (∀ᵐ a ∂α, c a =ᵐ[ν] F a) → (⇑(∫ a, c a ∂α) : Y → V) =ᵐ[ν] fun y => ∫ a, F a y ∂α := by
  first | exact @GlobalTheory.CompanionTheory.LpBochner.coe_integral_ae_eq | exact GlobalTheory.CompanionTheory.LpBochner.coe_integral_ae_eq | (intros; apply GlobalTheory.CompanionTheory.LpBochner.coe_integral_ae_eq <;> assumption)
end
end
