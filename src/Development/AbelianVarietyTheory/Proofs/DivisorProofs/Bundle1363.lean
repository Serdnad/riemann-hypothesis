module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle265
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle359
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.periodic_adelicSchwartz_finite_coset_decomposition : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    IsCompact (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ K : Set (κ → FiniteAdeleRing (𝓞 F) F), IsCompact K →
    ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ, (∀ x ∈ L, ∀ z, Ψ (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = Ψ z) →
        (∀ z, Ψ z ≠ 0 → (fun i => (z i).2) ∈ K) →
        ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Ψ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  first | exact @GlobalTheory.WeilCont.schA_periodic_finite_cosets | exact GlobalTheory.WeilCont.schA_periodic_finite_cosets | (intros; apply GlobalTheory.WeilCont.schA_periodic_finite_cosets <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.adelic_schwartz_l2_word_bound_exists : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ → ∀ i j : ℕ,
    ∃ (L : List (List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))) (C : ℝ), ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ y : (κ → FiniteAdeleRing (𝓞 F) F),
      ENNReal.ofReal (∫ x, (‖x‖ ^ i * ‖iteratedFDeriv ℝ j (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x‖) ^ 2) ≤
        ENNReal.ofReal C * (L.map fun w => ∫⁻ x, ‖GlobalTheory.WeilL2Words.word F ψ w Φ (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2).sum := by
  first | exact @GlobalTheory.WeilL2Words.adelic_schwartz_slice_l2_word_bound | exact GlobalTheory.WeilL2Words.adelic_schwartz_slice_l2_word_bound | (intros; apply GlobalTheory.WeilL2Words.adelic_schwartz_slice_l2_word_bound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.archDerivative_keeps_sums_fixed_finite_parts : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ →
    ∀ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      ∃ f' : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        GlobalTheory.WeilL2Words.dS F ψ h (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) = ∑ i, GlobalTheory.WeilM.pureA F (f' i) (g i) := by
  first | exact @GlobalTheory.WeilL2Words.dS_sum_pureA | exact GlobalTheory.WeilL2Words.dS_sum_pureA | (intros; apply GlobalTheory.WeilL2Words.dS_sum_pureA <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


theorem _root_.GlobalTheory.T.finite_adelic_dual_basis_integral : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (yy : Fin m → (κ → FiniteAdeleRing (𝓞 F) F)), (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) → (∀ i j, g i (yy j) = if i = j then 1 else 0) →
    ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ y : (κ → FiniteAdeleRing (𝓞 F) F), ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ∫⁻ x, ‖(∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2 ≤
        C * GlobalTheory.WeilL2Words.l2A F μ (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) := by
  first | exact @GlobalTheory.WeilL2Words.slice_le_l2A | exact GlobalTheory.WeilL2Words.slice_le_l2A | (intros; apply GlobalTheory.WeilL2Words.slice_le_l2A <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
open MeasureTheory
namespace GlobalTheory.WeilL2Words
variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem adeleJoin_archPart (a : κ → AdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F (archPart F a) (fun i => (a i).2) = a := by
  funext i
  simp only [GlobalTheory.WeilCont.adeleJoin, archPart, RingEquiv.symm_apply_apply]
  rfl

theorem adeleJoin_add_arch (x v : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y + arch F v = GlobalTheory.WeilCont.adeleJoin F (x + v) y := by
  funext i
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i) + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i + v i)
    rw [map_add (f := _)]
  · exact add_zero (y i)

theorem adeleJoin_dot_arch (x u : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y ⬝ᵥ arch F u = arch1 F (∑ i, x i * u i) := by
  rw [dotProduct, adeleOfMixedSpaceComponent_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [arch, mul_arch1']
  congr 2
  exact RingEquiv.apply_symm_apply _ _

theorem arch_dot_arch (v u : κ → mixedEmbedding.mixedSpace F) :
    arch F v ⬝ᵥ arch F u = arch1 F (∑ i, v i * u i) := by
  rw [dotProduct, adeleOfMixedSpaceComponent_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [arch, arch, mul_arch1']
  congr 2
  exact RingEquiv.apply_symm_apply _ _

theorem schA_exists_sum {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    ∃ (n : ℕ) (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  rw [GlobalTheory.WeilM.schA, Submodule.mem_span_set'] at hΦ
  obtain ⟨n, c, s, rfl⟩ := hΦ
  choose f g hg hfg using fun i => (s i).2
  refine ⟨n, fun i => c i • f i, g, hg, Finset.sum_congr rfl fun i _ => ?_⟩
  rw [hfg i]
  ext a
  simp [GlobalTheory.WeilM.pureA, mul_assoc]

variable [Invertible (2 : AdeleRing (𝓞 F) F)]

theorem ell_half (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (z : mixedEmbedding.mixedSpace F) :
    ℓ (InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * z) = ℓ z / 2 := by
  set c := InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1
  have hc : c + c = 1 := by
    rw [← map_add (f := _)]
    have : (⅟(2 : AdeleRing (𝓞 F) F)).1 + (⅟(2 : AdeleRing (𝓞 F) F)).1 = (⅟(2 : AdeleRing (𝓞 F) F) + ⅟2).1 := rfl
    rw [this, invOf_two_add_invOf_two]
    exact map_one _
  have h2 : ℓ (c * z) + ℓ (c * z) = ℓ z := by rw [← map_add (f := _), ← add_mul, hc, one_mul]
  linarith

theorem schr_archPair_adeleJoin (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.schr ψ (archPair F h) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
      Complex.exp (2 * Real.pi * Complex.I * ((ℓ (∑ i, x i * h.2 i) : ℂ) + (ℓ (∑ i, h.1 i * h.2 i) : ℂ) / 2)) *
        Φ (GlobalTheory.WeilCont.adeleJoin F (x + h.1) y) := by
  simp only [GlobalTheory.WeilM.schr, archPair]
  rw [adeleJoin_add_arch, adeleJoin_dot_arch, arch_dot_arch, mul_arch1', ← adeleOfMixedSpaceComponent_add, hℓ, map_add (f := _), ell_half]
  congr 2
  push_cast
  ring

theorem hasDerivAt_schr_pureA (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (GlobalTheory.WeilM.pureA F f g) (GlobalTheory.WeilCont.adeleJoin F x y))
      ((2 * Real.pi * Complex.I * (ℓ (∑ i, x i * h.2 i) : ℂ) * f x + fderiv ℝ f x h.1) * g y) 0 := by
  set A : ℝ := ℓ (∑ i, x i * h.2 i)
  set B : ℝ := ℓ (∑ i, h.1 i * h.2 i) / 2
  have key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (GlobalTheory.WeilM.pureA F f g) (GlobalTheory.WeilCont.adeleJoin F x y)) =
      fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((t * A + t ^ 2 * B : ℝ) : ℂ)) * (f (x + t • h.1) * g y) := by
    funext t
    rw [schr_archPair_adeleJoin F ψ ℓ hℓ, GlobalTheory.WeilCont.pureA_adeleJoin]
    congr 2
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, A, B]
    have e1 : ∑ i, x i * (t • h.2 i) = t • ∑ i, x i * h.2 i := by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
    have e2 : ∑ i, (t • h.1 i) * (t • h.2 i) = (t ^ 2) • ∑ i, h.1 i * h.2 i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
    rw [e1, e2, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  rw [key]
  have hφ := ((((hasDerivAt_id (0:ℝ)).mul_const A).fun_add ((hasDerivAt_pow 2 (0:ℝ)).mul_const B)).ofReal_comp).const_mul
    (2 * (Real.pi : ℂ) * Complex.I)
  have hS := ((f.hasFDerivAt (x + (0:ℝ) • h.1)).comp_hasDerivAt (0:ℝ)
      (((hasDerivAt_id (0:ℝ)).smul_const h.1).const_add x)).mul_const (g y)
  have hT := hφ.cexp.fun_mul hS
  refine hT.congr_deriv ?_
  simp only [id, Function.comp, zero_smul, add_zero, one_smul, zero_mul, mul_zero, Complex.ofReal_zero, Complex.exp_zero,
    one_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_pow]
  ring

omit [Invertible (2 : AdeleRing (𝓞 F) F)] in
theorem schr_sum' [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) {n : ℕ} (Φ : Fin n → (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (∑ i, Φ i) = ∑ i, GlobalTheory.WeilM.schr ψ w (Φ i) := by
  funext x
  simp [GlobalTheory.WeilM.schr, Finset.sum_apply, Finset.mul_sum]

theorem hasDerivAt_schr_sum (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {n : ℕ}
    (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
        (GlobalTheory.WeilCont.adeleJoin F x y))
      (∑ i, (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * f i x + fderiv ℝ (f i) x h.1) * g i y) 0 := by
  have e : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
      (GlobalTheory.WeilCont.adeleJoin F x y)) = fun t => ∑ i, GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (GlobalTheory.WeilM.pureA F (f i) (g i))
      (GlobalTheory.WeilCont.adeleJoin F x y) := by
    funext t
    rw [schr_sum', Finset.sum_apply]
  rw [e]
  exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hasDerivAt_schr_pureA F ψ ℓ hℓ h (f i) (g i) x y

theorem differentiableAt_schr {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsStdInf F ψ)
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (a : κ → AdeleRing (𝓞 F) F) :
    DifferentiableAt ℝ (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) Φ a) 0 := by
  obtain ⟨ℓ, -, hℓ⟩ := hψ
  obtain ⟨n, f, g, -, rfl⟩ := schA_exists_sum F hΦ
  rw [← adeleJoin_archPart F a]
  exact (hasDerivAt_schr_sum F ψ ℓ hℓ h f g _ _).differentiableAt

theorem dS_sum_adeleJoin (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {n : ℕ}
    (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    dS F ψ h (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y) =
      ∑ i, (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * f i x + fderiv ℝ (f i) x h.1) * g i y :=
  (hasDerivAt_schr_sum F ψ ℓ hℓ h f g x y).deriv

theorem dS_mem_schA {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsStdInf F ψ)
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) : dS F ψ h Φ ∈ GlobalTheory.WeilM.schA F κ := by
  obtain ⟨n, f, g, hg, rfl⟩ := schA_exists_sum F hΦ
  obtain ⟨f', hf'⟩ := dS_sum_pureA F κ ψ hψ n g f h
  rw [hf']
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, g i, hg i, rfl⟩

end GlobalTheory.WeilL2Words
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (incM)
open GlobalTheory.ThetaTransform

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adelicLinearCoordinates_continuous_keep_parts : ∀ (D : D7) (m n N : ℕ) (e : Matrix (Fin m) (Fin n) (AE D) ≃ₗ[AF D.host.F] VA D.host.F N), Continuous e ∧ Continuous e.symm ∧ (∀ x, x.map (finPart D) = 0 ↔ GlobalTheory.SWQ.fin (e x).1 = 0 ∧ GlobalTheory.SWQ.fin (e x).2 = 0) ∧ (∀ x, x.map (infPart D) = 0 ↔ GlobalTheory.SWQ.inf (e x).1 = 0 ∧ GlobalTheory.SWQ.inf (e x).2 = 0) := by
  first | exact @GlobalTheory.AdelicCoord.coord | exact GlobalTheory.AdelicCoord.coord | (intros; apply GlobalTheory.AdelicCoord.coord <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TorusVals

variable {R : Type} [CommRing R]

theorem dual_mul (a b : R) : ((1 : DualNumber R) + TrivSqZeroExt.inr a) * (1 + TrivSqZeroExt.inr b) = 1 + TrivSqZeroExt.inr (a + b) := by
  ext <;> simp [add_comm]

theorem epsScaleR_one_add (c a : R) : epsScaleR c (1 + TrivSqZeroExt.inr a) = 1 + TrivSqZeroExt.inr (c * a) := by
  ext <;> simp [epsScaleR, mul_comm]

section Gs

variable {Z : Scheme.{0}} (q : Z ⟶ (epsR R).left) (z : Z)

theorem gs_one_add_zero : gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr 0)) = 1 := by
  rw [gs_eq q z ⊤ trivial, TrivSqZeroExt.inr_zero, add_zero, map_one, map_one, map_one]

theorem gs_dual_mul (a b : R) :
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a)) *
      gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr b)) =
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a + b))) := by
  rw [← gs_mul q z ⊤ trivial, ← map_mul, dual_mul]

theorem gs_scale (c a : R) :
    gs (q ≫ (epsScale R c).left) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr a)) =
    gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (c * a))) := by
  rw [← gs_pull q (epsScale R c).left z ⊤ trivial, ← epsScaleR_one_add]
  have e := congrArg (fun f => f.hom (1 + TrivSqZeroExt.inr a : DualNumber R))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (epsScaleR c)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  rw [e]
  rfl

end Gs

variable [IsDomain R] {D : DegPre R} {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H] {Φ : ∀ T, (T ⟶ H) ≃ GtPt D T}

def HasVals (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T) (y : epsR R ⟶ H) (a : D.X → R) : Prop :=
  (Φ _ y).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z)
    (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    (val ((Φ _ y).s χ) q z J).val = gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a χ)))

theorem hasVals_one (hΦ : TorusModel.Represents Φ) : HasVals Φ 1 (fun _ => 0) := by
  have hz : (Φ (epsR R) 1).IsZero := GtVec.isZero_of_isAdd (by simpa using hΦ.2 (epsR R) 1 1)
  refine ⟨hz.1, fun χ Z q z J hJ => ?_⟩
  rw [val_corr hJ (hz.2 χ) q, val_one, gs_one_add_zero]
  rfl

theorem hasVals_scale (hΦ : TorusModel.Represents Φ) {y : epsR R ⟶ H} {a : D.X → R} (h : HasVals Φ y a) (c : R) :
    HasVals Φ (epsScale R c ≫ y) (fun χ => c * a χ) := by
  have hp := hΦ.1 (epsR R) (epsR R) (epsScale R c) y
  refine ⟨?_, fun χ Z q z J hJ => ?_⟩
  · rw [((TorusModel.isPull_iff _ _ _).1 hp).1, h.1]
    simp only [DegPre.zeroT, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  · rw [val_corr hJ (hp.2 χ) q, val_pull hJ, h.2 χ Z _ z J hJ, gs_scale]

theorem hasVals_mul (hΦ : TorusModel.Represents Φ) {y y' : epsR R ⟶ H} {a a' : D.X → R} (h : HasVals Φ y a)
    (h' : HasVals Φ y' a') : HasVals Φ (y * y') (fun χ => a χ + a' χ) := by
  have hs := hΦ.2 (epsR R) y y'
  refine ⟨?_, fun χ Z q z J hJ => ?_⟩
  · rw [((TorusModel.isAdd_iff _ _ _).1 hs).1, h.1, h'.1]
    exact _root_.mul_one _
  · have e := (val_mul hJ _ _ q).symm.trans ((val_corr hJ (hs.2 χ) q).trans (val_mul hJ _ _ q))
    let T' : Over (Sp R) := Over.mk (q ≫ (epsR R).hom)
    let ρ : T' ⟶ epsR R := Over.homMk q rfl
    have hc : val (DegPre.cubAtT D (epsR R) (DegPre.cT D (epsR R) χ) (Φ _ y).b (Φ _ y').b) q z J = 1 := by
      have := val_cub D.cub ρ hJ (DegPre.cT D (epsR R) χ) (Φ _ y).b (Φ _ y').b
      refine this.trans ?_
      rw [h'.1]
      have e1 : ρ ≫ DegPre.zeroT D (epsR R) = (1 : T' ⟶ D.P.A) := by
        simp only [DegPre.zeroT, ← Category.assoc]
        rw [Hom.one_def]
        congr 1
      rw [e1]
      exact (isCub_cubV D.cub hJ).face₃ _ _
    rw [hc, _root_.mul_one] at e
    rw [e, Units.val_mul, h.2 χ Z q z J hJ, h'.2 χ Z q z J hJ, gs_dual_mul]

end GlobalTheory.MBLow.TorusVals

namespace GlobalTheory.MBLow.TorusVals

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {H : Over (Sp R)} [GrpObj H] [IsCommMonObj H]
  {Φ : ∀ T, (T ⟶ H) ≃ GtPt D T}

theorem hasVals_tanComb (hΦ : TorusModel.Represents Φ) : ∀ (r : ℕ) (a : Fin r → D.X → R) (x : Fin r → (epsR R ⟶ H)),
    (∀ l, HasVals Φ (x l) (a l)) → ∀ d : Fin r → R, HasVals Φ (tanComb d x) (fun χ => ∑ l, d l * a l χ)
  | 0, a, x, _, d => by
    have e : tanComb d x = 1 := by simp [tanComb]
    have ef : (fun χ => ∑ l : Fin 0, d l * a l χ) = fun _ => 0 := funext fun _ => by simp
    rw [e, ef]
    exact hasVals_one hΦ
  | r + 1, a, x, hx, d => by
    have e : tanComb d x = (epsScale R (d 0) ≫ x 0) * tanComb (fun i => d i.succ) (fun i => x i.succ) := by
      simp only [tanComb, List.ofFn_succ, List.prod_cons]
    have key := hasVals_mul hΦ (hasVals_scale hΦ (hx 0) (d 0))
      (hasVals_tanComb hΦ r (fun i => a i.succ) (fun i => x i.succ) (fun l => hx l.succ) (fun i => d i.succ))
    have ef : (fun χ => ∑ l, d l * a l χ) = fun χ => d 0 * a 0 χ + ∑ l : Fin r, d l.succ * a l.succ χ :=
      funext fun χ => Fin.sum_univ_succ _
    rw [e, ef]
    exact key

theorem tanComb_vals : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (H : Over (Sp R)) [GrpObj H] [IsCommMonObj H] (Φ : ∀ T, (T ⟶ H) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ → ∀ (r : ℕ) (a : Fin r → D.X → R) (x : Fin r → (epsR R ⟶ H)), (∀ l, (Φ _ (x l)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (x l)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (a l χ)))) → ∀ d : Fin r → R, (Φ _ (tanComb d x)).b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val ((Φ _ (tanComb d x)).s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (∑ l, d l * a l χ))) :=
  fun _ _ _ _ _ _ _ _ hΦ r a x hx d => hasVals_tanComb hΦ r a x hx d

end GlobalTheory.MBLow.TorusVals

end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem levSetInf_closed_subgroup : ∀ (E : Type) [Field E] [NumberField E] (n r : ℕ),
    (∀ g ∈ levSetInf E n r, ∀ h ∈ levSetInf E n r, g * h ∈ levSetInf E n r) ∧
    (∀ g ∈ levSetInf E n r, g⁻¹ ∈ levSetInf E n r) ∧
    (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), u ∈ levSetInf E n r) ∧ IsClosed (levSetInf E n r) := by
  intro E _ _ n r
  refine ⟨fun g hg h hh w => ?_, fun g hg w => ?_, fun u hu => ?_, ?_⟩
  · rw [map_mul]
    exact (levSet_closed_subgroup n r).1 _ (hg w) _ (hh w)
  · rw [map_inv]
    exact (levSet_closed_subgroup n r).2.1 _ (hg w)
  · obtain ⟨h0, h1⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
    exact mem_levSetInf.2 fun i _ => ⟨fun j hj => h0 i j hj, h1 i⟩
  · have hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) (Cinf E) =>
        (g : Matrix (Fin n) (Fin n) (Cinf E)) i j :=
      fun i j => (Units.continuous_val (M := Matrix (Fin n) (Fin n) (Cinf E))).matrix_elem i j
    have hs : levSetInf E n r = {g : GL (Fin n) (Cinf E) | ∀ i : Fin n, r ≤ (i : ℕ) →
        (∀ j, j < i → (g : Matrix (Fin n) (Fin n) (Cinf E)) i j = 0) ∧
          (g : Matrix (Fin n) (Fin n) (Cinf E)) i i = 1} := Set.ext fun g => mem_levSetInf
    rw [hs]
    simp only [Set.setOf_forall, Set.setOf_and]
    refine isClosed_iInter fun i => isClosed_iInter fun _ => IsClosed.inter ?_ ?_
    · exact isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (hc i j) continuous_const
    · exact isClosed_eq (hc i i) continuous_const

end GlobalTheory.JSW.MirCinf
end
