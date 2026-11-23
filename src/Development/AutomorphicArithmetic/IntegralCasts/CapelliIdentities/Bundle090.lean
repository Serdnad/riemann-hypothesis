module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle070
public import Formalism.LocalToGlobal.KernelLattices.ColumnData
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle039
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle028
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

theorem UpperTheory.Reformulated.B.InfiniteNormOneField.infinite_norm_one_k {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {nS nT : ℕ}
    {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
    {θ : NumberField.InfinitePlace F → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf F) E →+* ℂ}
    {ι : (NumberField.InfinitePlace F → ℂ) →+ Formalism.IndefR.DatumF.AEF F E}
    (h : PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) : {t | t * σ t = 1}.Infinite :=
  have hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ := h.1.cm
  UpperTheory.Reformulated.B.CapelliAbsoluteValue.abs σ hcm.2.1 hcm.2.2.2
end

section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private lemma conj_eq_neg_of_sq {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ 2 = -(n : ℂ)) :
    (starRingEnd ℂ) z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hz : z.re = 0 := by
    have h2 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact h1
    · exfalso; rw [h1] at hre; nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [hz]

theorem UpperTheory.Reformulated.B.StarSqrtNeg.star_sqrt_neg :
    ∀ {D : Formalism.L2.Ker.Car} (x : D.host.E) (n : ℕ),
    (0 : ℕ) < n →
      x ^ (2 : ℕ) = -(↑n : D.host.E) →
        Star.star x =
          -x := by
  intro D x n hn h
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  apply φ.injective
  have key : φ (Star.star x) = (starRingEnd ℂ) (φ x) :=
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E φ x
  have hsq : (φ x) ^ 2 = -(n : ℂ) := by
    have := congrArg φ h
    simpa using this
  rw [key, map_neg]
  exact conj_eq_neg_of_sq hn hsq
end

section

theorem UpperTheory.Reformulated.B.ExportFamilies.K_repr :
    ∀ (D : Formalism.L2.Ker.Car),
    ∀ x ∈ D.host.K,
      ∃ (p : ℚ) (q : ℚ),
        x =
          (↑p : D.host.E) +
            (↑q : D.host.E) *
              D.host.sqd := by
  intro D x hx
  have hs := D.host.sqd_sq
  have hx' : x ∈ Algebra.adjoin ℚ {D.host.sqd} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) D.host.sqd)]
    exact hx
  refine Algebra.adjoin_induction (p := fun x _ => ∃ p q : ℚ, x = (p : D.host.E) + q * D.host.sqd)
    (fun y hy => ⟨0, 1, by simpa using hy⟩) (fun r => ⟨r, 0, by simp⟩) ?_ ?_ hx'
  · rintro _ _ _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    exact ⟨a + c, b + e, by push_cast; ring⟩
  · rintro _ _ _ _ ⟨a, b, rfl⟩ ⟨c, e, rfl⟩
    exact ⟨a * c - D.host.d * (b * e), a * e + b * c, by
      push_cast; linear_combination ((b : D.host.E) * e) * hs⟩
end

section

private theorem UpperTheory.Reformulated.B.WeightThresholdDefs.core {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {L : Submodule (NumberField.RingOfIntegers K) V} (h : Submodule.span K (L : Set V) = ⊤) (x : V) :
    ∃ n : NumberField.RingOfIntegers K, n ≠ 0 ∧ (n : K) • x ∈ L := by
  have hx : x ∈ Submodule.span K (L : Set V) := h ▸ Submodule.mem_top
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (nonZeroDivisors (NumberField.RingOfIntegers K)) K (L : Set V) x hx
  refine ⟨t, nonZeroDivisors.coe_ne_zero t, ?_⟩
  rw [Submodule.span_eq, Submonoid.smul_def] at ht
  have : ((t : NumberField.RingOfIntegers K) : K) • x = (t : NumberField.RingOfIntegers K) • x :=
    algebraMap_smul K (t : NumberField.RingOfIntegers K) x
  rw [this]
  exact ht

theorem UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem :
    ∀ {D : Formalism.L2.Ker.Car} {N : ℕ}
    {L₁ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E)},
    Submodule.span D.host.E (↑L₁ : Set (Fin N → D.host.E)) = ⊤ →
      ∀ (x : Fin N → D.host.E),
        ∃ (n : NumberField.RingOfIntegers D.host.E),
          n ≠ (0 : NumberField.RingOfIntegers D.host.E) ∧
            (↑n : D.host.E) • x ∈
              L₁ := by
  intro D N L₁ h x
  exact UpperTheory.Reformulated.B.WeightThresholdDefs.core h x
end

section

@[reducible] noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterion.be :
    Formalism.L2.Ker.Car → ℂ :=
    fun (D : Formalism.L2.Ker.Car) ↦ Complex.I * (↑√(↑D.host.d : ℝ) : ℂ)

noncomputable def UpperTheory.Reformulated.B.IntegralClosureCriterion.OKc :
    Formalism.L2.Ker.Car → ℂ → Prop :=
    fun (D : Formalism.L2.Ker.Car) (z : ℂ) ↦
      ∃ (x : ℤ) (y : ℤ), Even (x - y) ∧ z = ((↑x : ℂ) + (↑y : ℂ) * UpperTheory.Reformulated.B.IntegralClosureCriterion.be D) / (2 : ℂ)

theorem UpperTheory.Reformulated.B.IntegralClosureCriterion.okc_of :
    ∀ (D : Formalism.L2.Ker.Car) (u : NumberField.RingOfIntegers ↥D.host.K),
      UpperTheory.Reformulated.B.IntegralClosureCriterion.OKc D ((D.host.φ₀ : D.host.E → ℂ) (↑(↑u : ↥D.host.K) : D.host.E)) := by
  intro D u
  have hφ : D.host.φ₀ D.host.sqd = Complex.I * ((Real.sqrt (D.host.d : ℝ) : ℝ) : ℂ) := D.host.φ₀_mem
  obtain ⟨a, b, hab⟩ := UpperTheory.adjoin_sqrt_eq_rat_span D.host.E D.host.d D.host.sqd D.host.sqd_sq
    ((u : D.host.K) : D.host.E) (u : D.host.K).2
  have hval : D.host.φ₀ ((u : D.host.K) : D.host.E)
      = (a : ℂ) + (b : ℂ) * (Complex.I * ((Real.sqrt (D.host.d : ℝ) : ℝ) : ℂ)) := by
    rw [hab, map_add (f := _), map_mul, map_ratCast, map_ratCast, hφ]
  have hint : IsIntegral ℤ (D.host.φ₀ ((u : D.host.K) : D.host.E)) :=
    (u.isIntegral_coe).map
      (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
  rw [hval] at hint
  obtain ⟨x, y, hxy, h⟩ := UpperTheory.integral_quadratic_half_int D.host.d D.host.hyp.2.1 a b hint
  exact ⟨x, y, hxy, hval.trans h⟩
end
