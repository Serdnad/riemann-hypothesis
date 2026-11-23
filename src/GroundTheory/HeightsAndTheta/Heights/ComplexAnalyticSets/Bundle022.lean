module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle007
public import Mathlib.Analysis.Complex.Norm
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle005
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.RingTheory.Support
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Spectrum
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Matrix Complex

noncomputable section

namespace UnitaryZariskiDense

theorem eval_aeval_subst {σ τ : Type*} (F : σ → MvPolynomial τ ℂ) (p : MvPolynomial σ ℂ)
    (x : τ → ℂ) : eval x (aeval F p) = eval (fun i => eval x (F i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p i hp => rw [map_mul, map_mul, hp, aeval_X, map_mul, eval_X]

theorem polyEval_aeval_subst {σ : Type*} (F : σ → Polynomial ℂ) (p : MvPolynomial σ ℂ) (z : ℂ) :
    (aeval F p).eval z = eval (fun i => (F i).eval z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem unit_circle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  intro hfin
  have hsub : Polynomial.nthRootsFinset (hfin.toFinset.card + 1) (1 : ℂ) ⊆ hfin.toFinset := by
    intro z hz
    rw [Polynomial.mem_nthRootsFinset (Nat.succ_pos _)] at hz
    rw [Set.Finite.mem_toFinset]
    exact Complex.norm_eq_one_of_pow_eq_one hz (Nat.succ_ne_zero _)
  have hc := Finset.card_le_card hsub
  rw [(Complex.isPrimitiveRoot_exp (hfin.toFinset.card + 1) (Nat.succ_ne_zero _)).card_nthRootsFinset]
    at hc
  omega

theorem conj_diagonal_mem {n : ℕ} {V : Matrix (Fin n) (Fin n) ℂ} (hV : V ∈ unitaryGroup (Fin n) ℂ)
    {d : Fin n → ℂ} (hd : ∀ k, ‖d k‖ = 1) : V * diagonal d * star V ∈ unitaryGroup (Fin n) ℂ := by
  have hD : diagonal d ∈ unitaryGroup (Fin n) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one]
    congr 1
    funext k
    simpa [Complex.mul_conj', hd k]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hV hD) (Unitary.star_mem hV)

end UnitaryZariskiDense


open UnitaryZariskiDense in
theorem UnitaryZariskiDense.proof : UnitaryZariskiDense.Statement := by
  intro n p hp
  by_contra hall
  push Not at hall
  apply hp

  have herm : ∀ H : Matrix (Fin n) (Fin n) ℂ, H.IsHermitian →
      eval (fun ij : Fin n × Fin n => H ij.1 ij.2) p = 0 := by
    intro H hH
    have hspec := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    set V : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hVdef
    have hV : V ∈ unitaryGroup (Fin n) ℂ := hH.eigenvectorUnitary.2
    have hentry : ∀ d : Fin n → ℂ,
        eval d (aeval (fun ij : Fin n × Fin n => ∑ k, C (V ij.1 k * star V k ij.2) * X k) p) =
          eval (fun ij : Fin n × Fin n => (V * diagonal d * star V) ij.1 ij.2) p := by
      intro d
      rw [eval_aeval_subst]
      refine congrArg (fun f => eval f p) (funext fun ij => ?_)
      rw [Matrix.mul_apply]

      simp only [map_sum, map_mul, eval_C, eval_X, Matrix.mul_diagonal]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hr : aeval (fun ij : Fin n × Fin n => ∑ k, C (V ij.1 k * star V k ij.2) * X k) p = 0 :=
      funext_set (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => unit_circle_infinite) fun d hd => by
        rw [hentry, map_zero]
        exact hall _ (conj_diagonal_mem hV fun k => hd k trivial)
    have h0 := hentry (RCLike.ofReal ∘ hH.eigenvalues)
    rw [hr, map_zero] at h0
    rw [h0]
    refine congrArg (fun f => eval f p) (funext fun ij => ?_)
    exact congrFun (congrFun hspec ij.1) ij.2

  have all : ∀ A : Matrix (Fin n) (Fin n) ℂ, eval (fun ij : Fin n × Fin n => A ij.1 ij.2) p = 0 := by
    intro A
    set g : Polynomial ℂ := aeval (fun ij : Fin n × Fin n =>
      Polynomial.C (A ij.1 ij.2) * (Polynomial.C (1 / 2) - Polynomial.C (I / 2) * Polynomial.X) +
        Polynomial.C (Aᴴ ij.1 ij.2) * (Polynomial.C (1 / 2) + Polynomial.C (I / 2) * Polynomial.X)) p
      with hgdef
    have hg : ∀ z : ℂ, g.eval z = eval (fun ij : Fin n × Fin n =>
        A ij.1 ij.2 * (1 / 2 - I / 2 * z) + Aᴴ ij.1 ij.2 * (1 / 2 + I / 2 * z)) p := by
      intro z
      rw [hgdef, polyEval_aeval_subst]
      refine congrArg (fun f => eval f p) (funext fun ij => ?_)
      simp
    have g0 : g = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
      rintro _ ⟨t, rfl⟩
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, hg]
      have hstar : star (1 / 2 - I / 2 * (t : ℂ)) = 1 / 2 + I / 2 * (t : ℂ) := by
        apply Complex.ext <;> (simp; try ring)
      have hM : ((1 / 2 - I / 2 * (t : ℂ)) • A + (1 / 2 + I / 2 * (t : ℂ)) • Aᴴ).IsHermitian := by
        unfold IsHermitian
        rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_conjTranspose,
          hstar, ← hstar, star_star, add_comm]
      have h := herm _ hM
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at h
      rw [← h]
      refine congrArg (fun f => eval f p) (funext fun ij => ?_)
      ring
    have h := hg I
    rw [g0, Polynomial.eval_zero] at h
    rw [h]
    refine congrArg (fun f => eval f p) (funext fun ij => ?_)
    have h1 : (1 / 2 - I / 2 * I : ℂ) = 1 := by
      ring_nf
      rw [I_sq]
      norm_num
    have h2 : (1 / 2 + I / 2 * I : ℂ) = 0 := by
      ring_nf
      rw [I_sq]
      norm_num
    rw [h1, h2]
    ring

  exact MvPolynomial.funext fun x => by
    simpa using all (Matrix.of fun i j => x (i, j))

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def RegularOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)), I.IsPrime →
    ∃ h : MvPolynomial σ ℂ, h ∉ I ∧
      ∀ z ∈ zeroSetIn I, eval z h ≠ 0 → IsRegularPointOf (zeroSetIn I) z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def BranchInverseHolomorphic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ)
    (k : ℕ) (r : ℝ) (φ : (Fin k → ℂ) → σ → ℂ) (B : Set (σ → ℂ)),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → h ∉ I → w ∈ zeroSetIn I →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (zeroSetIn I) → B ∈ 𝓝 w →
    (zeroSetIn I ∩ B) \ {z | eval z h = 0} ⊆ φ '' Metric.ball 0 r →
    ∃ ψ : (σ → ℂ) → Fin k → ℂ, HolomorphicOnSubset ψ (φ '' Metric.ball 0 r) ∧
      ∀ t ∈ Metric.ball 0 r, ψ (φ t) = t

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def LocalTrace.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (U : Set (σ → ℂ))
    (g : (σ → ℂ) → ℂ),
    I.IsPrime → w ∈ zeroSetIn I → U ∈ 𝓝 w → HolomorphicOnSubset g (zeroSetIn I ∩ U) →
    ∃ (k : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (B : Set (σ → ℂ)) (D : Set (Fin k → ℂ)) (m : ℕ)
      (T : (Fin k → ℂ) → ℂ),
      IsOpen B ∧ w ∈ B ∧ B ⊆ U ∧ IsOpen D ∧ A w ∈ D ∧
      (∀ z ∈ zeroSetIn I ∩ B, A z = A w → z = w) ∧ DifferentiableOn ℂ T D ∧
      ∀ y ∈ D, ∃ x : Fin m → σ → ℂ, (∀ j, x j ∈ zeroSetIn I ∩ B ∧ A (x j) = y) ∧
        (∀ z ∈ zeroSetIn I ∩ B, A z = y → z ∈ Set.range x) ∧ T y = ∑ j, g (x j)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def LocalUniversalDenominator.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ)
    (U : Set (σ → ℂ)) (f : (σ → ℂ) → ℂ),
    I.IsPrime → h ∉ I → w ∈ zeroSetIn I → U ∈ 𝓝 w →
    HolomorphicOnSubset f ((zeroSetIn I ∩ U) \ {z | eval z h = 0}) →
    Bornology.IsBounded (f '' ((zeroSetIn I ∩ U) \ {z | eval z h = 0})) →
    ∃ g : MvPolynomial σ ℂ, g ∉ I ∧ ∃ N : Set (σ → ℂ), IsOpen N ∧ w ∈ N ∧ N ⊆ U ∧
      ∃ F : (σ → ℂ) → ℂ, DifferentiableOn ℂ F N ∧
        ∀ z ∈ (zeroSetIn I ∩ N) \ {z | eval z h = 0}, eval z g * f z = F z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalMaximumPrinciple.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (U : Set (σ → ℂ))
    (g : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → U ∈ 𝓝 w →
    HolomorphicOnSubset g (zeroSetIn I ∩ U) → (∀ z ∈ zeroSetIn I ∩ U, ‖g z‖ ≤ ‖g w‖) →
    ∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → g z = g w

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def NormalRiemannExtension.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (U : Set (σ → ℂ))
    (f : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → h ∉ I → IsOpen U →
    HolomorphicOnSubset f ((zeroSetIn I ∩ U) \ {z | eval z h = 0}) →
    Bornology.IsBounded (f '' ((zeroSetIn I ∩ U) \ {z | eval z h = 0})) →
    ∃ g : (σ → ℂ) → ℂ, HolomorphicOnSubset g (zeroSetIn I ∩ U) ∧
      Set.EqOn g f ((zeroSetIn I ∩ U) \ {z | eval z h = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def NormalRiemannExtensionLocal.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ)
    (U : Set (σ → ℂ)) (f : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → h ∉ I → w ∈ zeroSetIn I → U ∈ 𝓝 w →
    HolomorphicOnSubset f ((zeroSetIn I ∩ U) \ {z | eval z h = 0}) →
    Bornology.IsBounded (f '' ((zeroSetIn I ∩ U) \ {z | eval z h = 0})) →
    ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ V ⊆ U ∧ ∃ F : (σ → ℂ) → ℂ, DifferentiableOn ℂ F V ∧
      Set.EqOn F f ((zeroSetIn I ∩ V) \ {z | eval z h = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

def WeaklyHolomorphicIntegral.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (N : Set (σ → ℂ))
    (G f : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → IsOpen N → w ∈ N →
    DifferentiableOn ℂ G N → ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → G z = 0) →
    HolomorphicOnSubset f ((zeroSetIn I ∩ N) \ {z | G z = 0}) →
    Bornology.IsBounded (f '' ((zeroSetIn I ∩ N) \ {z | G z = 0})) →
    ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ V ⊆ N ∧ ∃ (d : ℕ) (a : Fin d → (σ → ℂ) → ℂ),
      (∀ j, DifferentiableOn ℂ (a j) V) ∧
      ∀ z ∈ (zeroSetIn I ∩ V) \ {z | G z = 0}, f z ^ d + ∑ j, a j z * f z ^ (j : ℕ) = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def BranchInverseOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (k : ℕ),
    I.IsPrime → ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (k : ℕ) →
    ∃ h' : MvPolynomial σ ℂ, h' ∉ I ∧
      ∀ (U : Set (Fin k → ℂ)) (φ : (Fin k → ℂ) → σ → ℂ) (ψ : (σ → ℂ) → Fin k → ℂ),
        IsOpen U → DifferentiableOn ℂ φ U → Set.InjOn φ U → Set.MapsTo φ U (zeroSetIn I) →
        (∀ t ∈ U, ψ (φ t) = t) →
        HolomorphicOnSubset ψ ((φ '' U) \ {z | eval z h' = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory Limits Abelian RingTheory.Sequence

universe u

namespace AuslanderBuchsbaumDepthLower

variable {R : Type u} [CommRing R] [IsLocalRing R]

noncomputable abbrev residueModule (R : Type u) [CommRing R] [IsLocalRing R] : ModuleCat.{u} R :=
  ModuleCat.of R (Shrink.{u} (R ⧸ maximalIdeal R))

instance (R : Type u) [CommRing R] [IsLocalRing R] : Module.Finite R (residueModule R) :=
  Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ maximalIdeal R)).symm

theorem support_residueModule :
    Module.support R (residueModule R) = PrimeSpectrum.zeroLocus (maximalIdeal R) := by
  rw [(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus, Ideal.annihilator_quotient]

theorem maximalIdeal_smul_top_lt_top (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Nontrivial M] : maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by
  refine (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator ?_).symm.lt_top
  have H : Module.annihilator R M ≠ ⊤ := fun h =>
    not_subsingleton M (Module.annihilator_eq_top_iff.mp h)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ H]

theorem subsingleton_ext_of_flat [IsNoetherianRing R] (rs : List R) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (hrs : IsWeaklyRegular R rs) (P : ModuleCat.{u} R) [Module.Finite R P] [Module.Flat R P] :
    ∀ i < rs.length, Subsingleton (Ext (residueModule R) P i) := by
  intro i hi
  rcases subsingleton_or_nontrivial P with hP | hP
  · have hZ : IsZero P := ModuleCat.isZero_of_subsingleton P
    have : Injective P := hZ.injective
    cases i with
    | zero => exact Ext.addEquiv₀.subsingleton_congr.mpr ⟨fun a b => hZ.eq_of_tgt a b⟩
    | succ j => exact Ext.subsingleton_of_injective _ _ j
  · have hreg : IsWeaklyRegular P rs :=
      (LinearEquiv.isWeaklyRegular_congr (TensorProduct.rid R P) rs).mp
        (hrs.isWeaklyRegular_lTensor (M₂ := P))
    have hreg' : IsRegular P rs :=
      (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr hreg
    exact ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) (residueModule R)
      support_residueModule.le P (maximalIdeal_smul_top_lt_top P) rs hmem hreg' i hi

theorem subsingleton_ext_of_hasProjectiveDimensionLE [IsNoetherianRing R] (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R) (hrs : IsWeaklyRegular R rs) (ℓ : ℕ) :
    ∀ (M : ModuleCat.{u} R) [Module.Finite R M], HasProjectiveDimensionLE M ℓ →
      ∀ i, i + ℓ < rs.length → Subsingleton (Ext (residueModule R) M i) := by
  induction ℓ with
  | zero =>
    intro M _ hM i hi
    have : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).mpr hM
    exact subsingleton_ext_of_flat rs hmem hrs M i (by omega)
  | succ ℓ ih =>
    intro M _ hM i hi
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
    have hS : f.shortComplexKer.ShortExact := LinearMap.shortExact_shortComplexKer hf
    have h₂ : HasProjectiveDimensionLT f.shortComplexKer.X₂ (ℓ + 1) :=
      hasProjectiveDimensionLT_of_ge _ 1 (ℓ + 1) (by omega)
    have hK : HasProjectiveDimensionLE f.shortComplexKer.X₁ ℓ :=
      hS.hasProjectiveDimensionLT_X₁ (ℓ + 1) h₂ hM
    have e₂ : Subsingleton (Ext (residueModule R) f.shortComplexKer.X₂ i) :=
      subsingleton_ext_of_flat rs hmem hrs _ i (by omega)
    have e₁ : Subsingleton (Ext (residueModule R) f.shortComplexKer.X₁ (i + 1)) :=
      ih _ hK (i + 1) (by omega)
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      ((Ext.covariant_sequence_exact₃' (residueModule R) hS) i (i + 1) rfl)
      ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr e₂).eq_zero_of_src _)
      ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr e₁).eq_zero_of_tgt _)

end AuslanderBuchsbaumDepthLower

theorem AuslanderBuchsbaumDepthLower.proof : AuslanderBuchsbaumDepthLower.Statement.{u} := by
  intro R _ _ _ M _ _ _ _ ℓ rs hpd hmem hrs
  obtain ⟨ms, hlen, hms, hreg⟩ := ModuleCat.exists_isRegular_of_exists_subsingleton_ext
    (maximalIdeal R) (rs.length - ℓ) (ModuleCat.of R M)
    (AuslanderBuchsbaumDepthLower.maximalIdeal_smul_top_lt_top M)
    (AuslanderBuchsbaumDepthLower.residueModule R)
    AuslanderBuchsbaumDepthLower.support_residueModule
    (fun i hi => AuslanderBuchsbaumDepthLower.subsingleton_ext_of_hasProjectiveDimensionLE rs hmem hrs ℓ
      (ModuleCat.of R M) hpd i (by omega))
  exact ⟨ms, hms, hreg.toIsWeaklyRegular, hlen⟩

end GroundTheory.Heights₂.Heights
end
