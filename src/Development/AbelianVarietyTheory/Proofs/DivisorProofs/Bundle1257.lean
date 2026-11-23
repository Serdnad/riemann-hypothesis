module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle568
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.Order.Chebyshev
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Words

open MeasureTheory

theorem enorm_sum_mul_sq_le {m : ℕ} (a b : Fin m → ℂ) :
    ‖∑ i, a i * b i‖ₑ ^ 2 ≤ (∑ i, ‖b i‖ₑ ^ 2) * ∑ i, ‖a i‖ₑ ^ 2 := by
  have h1 : ‖∑ i, a i * b i‖₊ ≤ ∑ i, ‖b i‖₊ * ‖a i‖₊ := by
    refine (nnnorm_sum_le _ _).trans (le_of_eq ?_)
    simp [nnnorm_mul, mul_comm]
  have h2 : ‖∑ i, a i * b i‖₊ ^ 2 ≤ (∑ i, ‖b i‖₊ ^ 2) * ∑ i, ‖a i‖₊ ^ 2 :=
    (pow_le_pow_left₀ (by positivity) h1 2).trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  simp only [enorm_eq_nnnorm]
  exact_mod_cast h2

theorem slice_le_l2A (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (m : ℕ)
    (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (yy : Fin m → (κ → FiniteAdeleRing (𝓞 F) F))
    (hg : ∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (hyy : ∀ i j, g i (yy j) = if i = j then 1 else 0)
    (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _))
    (hμ : @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (y : κ → FiniteAdeleRing (𝓞 F) F) : ∃ C : ENNReal, C ≠ ⊤ ∧
      ∀ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2 ≤
        C * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
  have hmeas : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Measurable fun x => ‖f x‖ₑ ^ 2 :=
    fun f => by
      haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
      exact (f.continuous.measurable.enorm).pow_const 2
  letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI := hμ
  have hev : ∀ (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) x y',
      (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y') = ∑ i, f i x * g i y' := by
    intro f x y'
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => GlobalTheory.WeilCont.pureA_adeleJoin F _ _ x y'

  let U : Fin m → Set (κ → FiniteAdeleRing (𝓞 F) F) := fun j => ⋂ i, {y' | g i y' = g i (yy j)}
  have hUo : ∀ j, IsOpen (U j) := fun j => isOpen_iInter_of_finite fun i => (hg i).1.isOpen_fiber _
  have hUm : ∀ j, yy j ∈ U j := fun j => Set.mem_iInter.2 fun i => rfl
  have hUv : ∀ j, ∀ y' ∈ U j, ∀ i, g i y' = if i = j then 1 else 0 := fun j y' hy' i => by
    rw [← hyy]; exact Set.mem_iInter.1 hy' i
  have hU0 : ∀ j, μ (U j) ≠ 0 := fun j => (hUo j).measure_ne_zero μ ⟨_, hUm j⟩
  have hUt : ∀ j, μ (U j) ≠ ⊤ := by
    intro j
    refine ne_top_of_le_ne_top ((hg j).2.isCompact.measure_lt_top).ne (measure_mono ?_)
    intro y' hy'
    apply subset_tsupport
    rw [Function.mem_support, hUv j y' hy' j, if_pos rfl]
    exact one_ne_zero
  have hB : (∑ i, ‖g i y‖ₑ ^ 2) ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ => ENNReal.pow_ne_top enorm_ne_top
  refine ⟨(∑ i, ‖g i y‖ₑ ^ 2) * ∑ j, (μ (U j))⁻¹, ENNReal.mul_ne_top hB
    (ENNReal.sum_ne_top.2 fun j _ => ENNReal.inv_ne_top.2 (hU0 j)), ?_⟩
  intro f
  have hA : ∀ j, ∫⁻ x, ‖f j x‖ₑ ^ 2 ≤ (μ (U j))⁻¹ * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
    intro j
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl (hU0 j)) (Or.inl (hUt j))]
    have e : ∫⁻ y' in U j, (∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y')‖ₑ ^ 2) ∂μ
        = ∫⁻ y' in U j, (∫⁻ x, ‖f j x‖ₑ ^ 2) ∂μ := by
      refine setLIntegral_congr_fun (hUo j).measurableSet (fun y' hy' => ?_)
      refine lintegral_congr fun x => ?_
      rw [hev, Finset.sum_eq_single j]
      · rw [hUv j y' hy' j, if_pos rfl, mul_one]
      · intro i _ hij
        rw [hUv j y' hy' i, if_neg hij, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [setLIntegral_const] at e
    rw [← e]
    exact setLIntegral_le_lintegral _ _
  calc ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2
      ≤ ∫⁻ x, (∑ i, ‖g i y‖ₑ ^ 2) * ∑ i, ‖f i x‖ₑ ^ 2 := by
        refine lintegral_mono fun x => ?_
        rw [hev]
        exact enorm_sum_mul_sq_le _ _
    _ = (∑ i, ‖g i y‖ₑ ^ 2) * ∑ i, ∫⁻ x, ‖f i x‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ hB, lintegral_finsetSum]
        intro i _
        exact hmeas (f i)
    _ ≤ (∑ i, ‖g i y‖ₑ ^ 2) * ∑ j, (μ (U j))⁻¹ * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
        gcongr with j
        exact hA j
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

end GlobalTheory.WeilL2Words

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
namespace GlobalTheory.WeilL2Words
open NumberField IsDedekindDomain

theorem adeleOfMixedSpaceComponent_add (F : Type) [Field F] [NumberField F] (z w : mixedEmbedding.mixedSpace F) :
    arch1 F (z + w) = arch1 F z + arch1 F w :=
  Prod.ext (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z w) (add_zero (0 : FiniteAdeleRing (𝓞 F) F)).symm

theorem mul_arch1' (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) (z : mixedEmbedding.mixedSpace F) :
    a * arch1 F z = arch1 F (InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 * z) := by
  refine Prod.ext ?_ ?_
  · change a.1 * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _
    rw [map_mul, RingEquiv.symm_apply_apply]
  · exact mul_zero (a.2 : FiniteAdeleRing (𝓞 F) F)

theorem adeleOfMixedSpaceComponent_zero (F : Type) [Field F] [NumberField F] : arch1 F 0 = 0 :=
  Prod.ext (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm) rfl

theorem add_arch1' (F : Type) [Field F] [NumberField F] (a : AdeleRing (𝓞 F) F) (z : mixedEmbedding.mixedSpace F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (a + arch1 F z).1 = InfiniteAdeleRing.ringEquiv_mixedSpace F a.1 + z ∧
    (a + arch1 F z).2 = a.2 := by
  constructor
  · change InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z) = _
    rw [map_add (f := _), RingEquiv.apply_symm_apply]
  · exact add_zero (a.2 : FiniteAdeleRing (𝓞 F) F)

def arch1Hom (F : Type) [Field F] [NumberField F] : mixedEmbedding.mixedSpace F →+ AdeleRing (𝓞 F) F where
  toFun := arch1 F
  map_zero' := adeleOfMixedSpaceComponent_zero F
  map_add' := adeleOfMixedSpaceComponent_add F

theorem adeleOfMixedSpaceComponent_finsetSum (F : Type) [Field F] [NumberField F] {ι : Type} (s : Finset ι) (z : ι → mixedEmbedding.mixedSpace F) :
    arch1 F (∑ i ∈ s, z i) = ∑ i ∈ s, arch1 F (z i) :=
  map_sum (arch1Hom F) z s

theorem dotProduct_arch (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (a : κ → AdeleRing (𝓞 F) F)
    (y : κ → mixedEmbedding.mixedSpace F) :
    a ⬝ᵥ arch F y = arch1 F (∑ k, InfiniteAdeleRing.ringEquiv_mixedSpace F (a k).1 * y k) := by
  rw [adeleOfMixedSpaceComponent_finsetSum]
  exact Finset.sum_congr rfl fun k _ => mul_arch1' F (a k) (y k)

theorem fst_arch1 (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (arch1 F z).1 = z :=
  RingEquiv.apply_symm_apply _ z

theorem dS_sum_pureA : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      ∃ f' : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        GlobalTheory.WeilL2Words.dS F ψ h (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by
  intro F _ _ _ κ _ ψ hψ m g f h
  obtain ⟨ℓ, -, hℓ⟩ := hψ
  let M : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F :=
    ∑ k, (LinearMap.mulRight ℝ (h.2 k)).comp (LinearMap.proj k)
  let L : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Complex.ofRealCLM.toLinearMap.comp (ℓ.comp M))
  have hL : ∀ X, L X = ((ℓ (∑ k, X k * h.2 k) : ℝ) : ℂ) := by
    intro X
    simp [L, M]
  have hg : (fun X => (2 * Real.pi * Complex.I) * L X).HasTemperateGrowth :=
    ((2 * Real.pi * Complex.I) • L).hasTemperateGrowth
  refine ⟨fun i => SchwartzMap.smulLeftCLM ℂ (fun X => (2 * Real.pi * Complex.I) * L X) (f i) +
    LineDeriv.lineDerivOp h.1 (f i), ?_⟩
  funext a
  set X : κ → mixedEmbedding.mixedSpace F := fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (a k).1 with hX
  set Y : κ → FiniteAdeleRing (𝓞 F) F := fun k => (a k).2 with hY
  set c : mixedEmbedding.mixedSpace F := InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 with hc
  set A : ℝ := ℓ (∑ k, X k * h.2 k) with hA
  set B : ℝ := ℓ (c * ∑ k, h.1 k * h.2 k) with hB
  have key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) a) =
      fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((t * A + t ^ 2 * B : ℝ) : ℂ)) *
        ∑ i, f i (X + t • h.1) * g i Y := by
    funext t
    unfold GlobalTheory.WeilM.schr
    congr 1
    · have e0 : (archPair F (t • h)).1 ⬝ᵥ (archPair F (t • h)).2 =
          arch1 F (∑ k, (t • h.1) k * (t • h.2) k) := by
        rw [archPair, dotProduct_arch]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        exact congrArg (· * (t • h).2 k) (fst_arch1 F ((t • h).1 k))
      have e1 : a ⬝ᵥ (archPair F (t • h)).2 + ⅟(2 : AdeleRing (𝓞 F) F) * ((archPair F (t • h)).1 ⬝ᵥ (archPair F (t • h)).2)
          = arch1 F (t • (∑ k, X k * h.2 k) + t ^ 2 • (c * ∑ k, h.1 k * h.2 k)) := by
        rw [e0, mul_arch1', archPair, dotProduct_arch, ← adeleOfMixedSpaceComponent_add]
        congr 1
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, mul_smul_comm, smul_mul_assoc, Finset.smul_sum,
          Finset.mul_sum, smul_smul, pow_two]
        rfl
      rw [e1, hℓ, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    · rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hx : (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F ((a + (archPair F (t • h)).1) k).1) = X + t • h.1 :=
        funext fun k => (add_arch1' F (a k) ((t • h.1) k)).1
      have hy : (fun k => ((a + (archPair F (t • h)).1) k).2) = Y :=
        funext fun k => (add_arch1' F (a k) ((t • h.1) k)).2
      unfold GlobalTheory.WeilM.pureA
      rw [hx, hy]

  have hφ := ((((hasDerivAt_id (0:ℝ)).mul_const A).fun_add ((hasDerivAt_pow 2 (0:ℝ)).mul_const B)).ofReal_comp).const_mul
    (2 * (Real.pi : ℂ) * Complex.I)
  have hS := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (((f i).hasFDerivAt (X + (0:ℝ) • h.1)).comp_hasDerivAt (0:ℝ)
      (((hasDerivAt_id (0:ℝ)).smul_const h.1).const_add X)).mul_const (g i Y))
  have hT := hφ.cexp.fun_mul hS
  unfold dS
  rw [key]
  refine (HasDerivAt.deriv hT).trans ?_
  simp only [Finset.sum_apply, GlobalTheory.WeilM.pureA, SchwartzMap.add_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  simp only [hL, ← hA]
  simp only [← hX, ← hY, ← hA, id, zero_smul, add_zero, one_smul, mul_zero, zero_mul, Complex.ofReal_zero, Complex.exp_zero,
    one_mul, Function.comp, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_add,
    Complex.ofReal_mul, Complex.ofReal_one]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [show ((0:ℝ) ^ (2 - 1)) = 0 by norm_num, Complex.ofReal_zero, mul_zero, zero_mul, add_zero]
  ring
end GlobalTheory.WeilL2Words
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.WeilL2Words

theorem adelic_schwartz_slice_l2_word_bound : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ → ∀ i j : ℕ,
    ∃ (L : List (List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))) (C : ℝ), ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : (κ → FiniteAdeleRing (𝓞 F) F),
      ENNReal.ofReal (∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2) ≤
        ENNReal.ofReal C * (L.map fun w => ∫⁻ x, ‖GlobalTheory.WeilL2Words.word F ψ w Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2).sum := by
  intro F _ _ _ κ _ ψ hψ i j
  obtain ⟨ℓ, hnd, hℓ⟩ := hψ
  obtain ⟨n, ⟨b⟩⟩ : ∃ n, Nonempty (Module.Basis (Fin n) ℝ (κ → mixedEmbedding.mixedSpace F)) :=
    ⟨_, ⟨Module.finBasis ℝ _⟩⟩
  obtain ⟨K4, hK4, hb4⟩ := GlobalTheory.T.continuousMultilinearMap_norm_le_sum_basis_values (κ → mixedEmbedding.mixedSpace F) _ b j
  obtain ⟨K5, hK5, hb5⟩ := GlobalTheory.T.norm_pow_le_const_mul_one_add_sum_abs_basisCoord_pow (κ → mixedEmbedding.mixedSpace F) _ b i
  choose u hu using fun c => GlobalTheory.T.exists_mixedSpace_dual_vector_traceForm F κ ℓ hnd (b.coord c)
  let ia : Option (Fin n) → ℕ := fun a => a.elim 0 (fun _ => i)
  let ua : Option (Fin n) → (κ → mixedEmbedding.mixedSpace F) := fun a => a.elim 0 u
  let wd : Option (Fin n) × (Fin j → Fin n) →
      List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :=
    fun p => List.replicate (ia p.1) (0, ua p.1) ++ (List.ofFn fun r => b (p.2 r)).map fun v => (v, 0)
  refine ⟨Finset.univ.toList.map wd, (K5 * K4) ^ 2 * (Fintype.card (Option (Fin n) × (Fin j → Fin n)) : ℝ),
    fun Φ hΦ y => ?_⟩
  obtain ⟨s, hs⟩ := GlobalTheory.WeilCont.exists_slice F hΦ y
  have hsf : (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) = s := funext fun x => (hs x).symm
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) := hsf ▸ s.smooth ⊤
  have hℓc : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  have key : ∀ p x, GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
      (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * ua p.1 k) : ℂ)) ^ (ia p.1) *
        iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x (fun r => b (p.2 r)) := by
    intro p x
    rw [GlobalTheory.T.slice_multiplicationDerivativeWord_iteratedFDeriv F κ ψ ℓ hℓ Φ y hsm, GlobalTheory.T.iteratedFDeriv_apply_eq_foldr_directional_fderiv _ _ hsm]
  have hcont : ∀ p, Continuous fun x => GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y) := by
    intro p
    simp_rw [key]
    have h1 : Continuous fun x : κ → mixedEmbedding.mixedSpace F => ∑ k, x k * ua p.1 k := by fun_prop
    have h2 : Continuous fun x => iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x :=
      hsm.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    exact ((continuous_const.mul (Complex.continuous_ofReal.comp (hℓc.comp h1))).pow _).mul
      ((ContinuousMultilinearMap.apply ℝ _ ℂ (fun r => b (p.2 r))).continuous.comp h2)
  rw [List.map_map, Finset.sum_map_toList]
  refine GlobalTheory.T.integral_sq_le_sum_lintegral_enorm_sq_of_pointwise _ MeasureTheory.volume _ _ _ _ hcont fun x => ?_
  have hterm : ∀ p : Option (Fin n) × (Fin j → Fin n),
      p.1.elim 1 (fun c => |b.coord c x| ^ i) *
          ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x (fun r => b (p.2 r))‖ ≤
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ := by
    intro p
    rw [key, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rcases p with ⟨_ | c, cs⟩
    · simp [ia]
    · simp only [Option.elim, ia, ua, hu, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Complex.norm_I, Real.norm_eq_abs, mul_one]
      rw [mul_pow]
      refine le_mul_of_one_le_left (by positivity) (one_le_pow₀ ?_)
      rw [abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_gt_three]
  have h1 : ‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖ ≤
      K5 * K4 * ∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ := by
    calc _ ≤ (K5 * (1 + ∑ c, |b.coord c x| ^ i)) *
          (K4 * ∑ cs : Fin j → Fin n, ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x
            (fun r => b (cs r))‖) :=
          mul_le_mul (hb5 x) (hb4 _) (norm_nonneg _) (by positivity)
      _ = K5 * K4 * ∑ p : Option (Fin n) × (Fin j → Fin n), p.1.elim 1 (fun c => |b.coord c x| ^ i) *
          ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x (fun r => b (p.2 r))‖ := by
          rw [Fintype.sum_prod_type, Fintype.sum_option]
          simp only [Option.elim, one_mul, ← Finset.mul_sum, ← Finset.sum_mul]
          ring
      _ ≤ _ := by
          gcongr with p
          exact hterm p
  have h0 : 0 ≤ ‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖ := by positivity
  calc _ ≤ (K5 * K4 * ∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = (K5 * K4) ^ 2 * (∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖) ^ 2 := by ring
    _ ≤ (K5 * K4) ^ 2 * ((Fintype.card (Option (Fin n) × (Fin j → Fin n)) : ℝ) * ∑ p : Option (Fin n) × (Fin j → Fin n),
        ‖GlobalTheory.WeilL2Words.word F ψ (wd p) Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ ^ 2) := by
          gcongr
          exact sq_sum_le_card_mul_sum_sq
    _ = _ := by ring

end GlobalTheory.WeilL2Words
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.HTLift

open GlobalTheory.SiegelPull

theorem push_comp' {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) {α : A' ⟶ A'} {β : A ⟶ A}
    (hab : α.left ≫ φ = φ ≫ β.left) (T : Over S') (x : T ⟶ A') : pushHom h T (x ≫ α) = pushHom h T x ≫ β :=
  Over.OverMorphism.ext (by
    show (x.left ≫ α.left) ≫ φ = (x.left ≫ φ) ≫ β.left
    rw [Category.assoc, hab, Category.assoc])

theorem exists_obj_of_isLift : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (T : Over S)
    (lv : D.La → (T ⟶ o.A)), IsLift o N' T lv → ∃ (o'' : Obj b N' (T.hom ≫ s))
    (mm : ObjMap (o''.forget N hd hc) o T.hom), ∀ a, (o''.eta a).left ≫ mm.φ = (lv a).left := by
  intro p _ D R _ b N N' hd hc S s o T lv hL
  obtain ⟨hadd, hker, hlin, hlev, hgeom⟩ := hL
  obtain ⟨oT, ⟨mT⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N S T.left s T.hom o
  have pb := mT.cart
  let eta : D.La → (𝟙_ (Over T.left) ⟶ oT.A) := fun a =>
    Over.homMk (pb.1.lift (lv a).left (𝟙 _) (by rw [Over.w, Category.id_comp])) (pb.1.lift_snd _ _ _)
  have etaφ : ∀ a, (eta a).left ≫ mT.φ = (lv a).left := fun a => pb.1.lift_fst _ _ _
  let u : Over.mk ((𝟙_ (Over T.left)).hom ≫ T.hom) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have key : ∀ a, pushHom pb _ (eta a) = u ≫ lv a := fun a => Over.OverMorphism.ext (by
    show (eta a).left ≫ mT.φ = 𝟙 T.left ≫ (lv a).left
    rw [Category.id_comp]; exact etaφ a)
  let o'' : Obj b N' (T.hom ≫ s) :=
    { A := oT.A
      ab := oT.ab
      act := oT.act
      P := oT.P
      isLB := oT.isLB
      rig₁ := oT.rig₁
      rig₂ := oT.rig₂
      symm := oT.symm
      ample := oT.ample
      kerP := oT.kerP
      rosati := oT.rosati
      lie := oT.lie
      lieRank := oT.lieRank
      eta := eta
      eta_add := fun y z => push_injective pb _ (by
        rw [map_mul, key, key, key, hadd, MonObj.comp_mul])
      eta_lin := fun c y => push_injective pb _ (by
        rw [push_comp' pb (mT.act c), key, key, hlin, Category.assoc])
      eta_ker := fun y => push_injective pb _ (by
        rw [key, hker, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        obtain ⟨I, hI⟩ := hgeom k x
        let e : (Over.mk x ⟶ oT.A) ≃* (Over.mk (x ≫ T.hom) ⟶ o.A) := MulEquiv.ofBijective (pushHom pb (Over.mk x))
          ⟨push_injective pb _, push_surjective pb _⟩
        have ea : ∀ c g, e (g ≫ oT.act.act c) = e g ≫ o.act.act c := fun c g => push_comp' pb (mT.act c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ mT.φ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        have dg := diag_iso mT.sq mT.pol
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn hp y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn hp y
                  onto := fun n hn hp q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn hp (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp]
                  isom := fun n hn hp y z => (weilIs_grpPullback_of_comm S T.left o.A oT.A T.hom mT.φ _ _
                    (pull_isLB o.isLB _) (pull_isLB oT.isLB _) pb dg (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _
                    (ex _) (ex _)).2 (I.isom n hn hp y z) }, fun y => ?_⟩
        show toUnit _ ≫ eta y = e.symm (I.ev N' y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        apply Over.OverMorphism.ext
        show x ≫ (lv y).left = ((toUnit (Over.mk x)).left ≫ (eta y).left) ≫ mT.φ
        rw [Category.assoc, etaφ, Over.toUnit_left]
        rfl }
  let mm : ObjMap (o''.forget N hd hc) o T.hom :=
    { φ := mT.φ, φ₂ := mT.φ₂, cart := mT.cart, sq := mT.sq, act := mT.act, pol := mT.pol,
      eta := fun y => by
        show (eta ((N' / N) • y)).left ≫ mT.φ = T.hom ≫ (o.eta y).left
        rw [etaφ, hlev, Over.comp_left, Over.toUnit_left] }
  exact ⟨o'', mm, fun a => etaφ a⟩

end GlobalTheory.HTLift
end
end
