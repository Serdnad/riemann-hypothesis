module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SfDefs
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.CartanBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Spectrum
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.Bundle003
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf
open scoped InnerProductSpace

theorem UpperTheory.integralOperator_fixed_invariant_of_left_invariant_kernel :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (π : UnitaryRep G H) (τ : Representation ℂ G S) (m : Measure G) [m.IsMulLeftInvariant] (φ : G → ℂ) (T : H →L[ℂ] H) (A : S →ₗ[ℂ] S) (U : Subgroup G), IsOp π m φ T → IsIntegralOp m τ φ A → (∀ u ∈ U, ∀ g, φ (u * g) = φ g) → (∀ v, T v ∈ fixU π U) ∧ (∀ x, A x ∈ fixedVectors τ U) ∧ (∀ D : Submodule ℂ H, IsClosed (D : Set H) → π.IsInvariant D → ∀ v ∈ D, T v ∈ D) ∧ (∀ B : H →L[ℂ] H, (∀ g v, π g (B v) = B (π g v)) → (∀ g v, π g (ContinuousLinearMap.adjoint B v) = ContinuousLinearMap.adjoint B (π g v)) → ∀ v, T (B v) = B (T v)) ∧ ∀ f : S →ₗ[ℂ] H, Eqv τ π ⊤ f → ∀ x, T (f x) = f (A x) := by
  intro G H S _ _ _ _ _ _ _ _ _ _ π τ m _ φ T A U hT hA hφ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v u hu
    refine ext_inner_left ℂ fun y => ?_
    rw [UnitaryRep.inner_map_right, hT, hT]
    rw [← integral_mul_left_eq_self (fun g => φ g * ⟪y, π g v⟫_ℂ) u]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show φ g * ⟪π u⁻¹ y, π g v⟫_ℂ = φ (u * g) * ⟪y, π (u * g) v⟫_ℂ
    rw [hφ u hu g, UnitaryRep.map_mul_apply, UnitaryRep.inner_map_right π u]
  · intro x u hu
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro l
    have h1 : l (τ u (A x)) = (l ∘ₗ τ u) (A x) := rfl
    rw [map_sub, h1, (hA x (l ∘ₗ τ u)).2, (hA x l).2, sub_eq_zero]
    rw [← integral_mul_left_eq_self (fun g => φ g * l (τ g x)) u]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show φ g * l (τ u (τ g x)) = φ (u * g) * l (τ (u * g) x)
    rw [hφ u hu g, map_mul, Module.End.mul_apply]
  · intro D hD hinv v hv
    have hc : D.topologicalClosure = D := hD.submodule_topologicalClosure_eq
    rw [← hc, ← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
    intro y hy
    rw [hT]
    have : ∀ g, φ g * ⟪y, π g v⟫_ℂ = 0 := fun g => by
      rw [(Submodule.mem_orthogonal' D y).1 hy _ (hinv g v hv), mul_zero]
    simp [this]
  · intro B hB _ v
    refine ext_inner_left ℂ fun y => ?_
    rw [hT, ← ContinuousLinearMap.adjoint_inner_left, hT]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show φ g * ⟪y, π g (B v)⟫_ℂ = φ g * ⟪ContinuousLinearMap.adjoint B y, π g v⟫_ℂ
    rw [hB, ContinuousLinearMap.adjoint_inner_left]
  · intro f hf x
    refine ext_inner_left ℂ fun y => ?_
    have h1 : ⟪y, f (A x)⟫_ℂ = ((innerSL ℂ y).toLinearMap ∘ₗ f) (A x) := rfl
    rw [hT, h1, (hA x _).2]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    show φ g * ⟪y, π g (f x)⟫_ℂ = φ g * ⟪y, f (τ g x)⟫_ℂ
    rw [hf.map]
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_apply_le_of_laplacian_lower_bound :
    ∀ (d : ℕ) (c C : ℝ) (ε : Fin d → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) → ∃ C' : ℝ, ∀ (M H : Type) [AddCommGroup M] [Module ℂ M] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : M →ₗ[ℂ] H) (V : Submodule ℂ M) (A : Fin d → Module.End ℂ M), (∀ i, ∀ x ∈ V, A i x ∈ V) → (∀ i, ∀ x ∈ V, ∀ y ∈ V, inner ℂ (j (A i x)) (j y) + inner ℂ (j x) (j (A i y)) = 0) → ∀ v ∈ V, -c * ‖j v‖ ^ 2 ≤ (inner ℂ (j v) (j (∑ i, (ε i : ℂ) • A i (A i v)))).re → (∀ i, ε i = -1 → ‖j (A i v)‖ ≤ C * ‖j v‖) → ∀ i, ‖j (A i v)‖ ≤ C' * ‖j v‖ := by
  intro d c C ε hε
  refine ⟨Real.sqrt (|c| + (d + 1) * C ^ 2), ?_⟩
  intro M H _ _ _ _ j V A hA hskew v hv hcas hC i
  have h1 : ∀ k, inner ℂ (j v) (j (A k (A k v))) = -((‖j (A k v)‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    have h := hskew k v hv (A k v) (hA k v hv)
    rw [inner_self_eq_norm_sq_to_K] at h
    push_cast
    exact eq_neg_of_add_eq_zero_right h
  have h2 : (inner ℂ (j v) (j (∑ i, (ε i : ℂ) • A i (A i v)))).re
      = -∑ k, ε k * ‖j (A k v)‖ ^ 2 := by

    rw [map_sum, inner_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, inner_smul_right, h1 k, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    ring
  rw [h2] at hcas
  have h3 : ∀ k, ε k = -1 → ‖j (A k v)‖ ^ 2 ≤ C ^ 2 * ‖j v‖ ^ 2 := by
    intro k hk
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC k hk) 2
  have hCN : 0 ≤ C ^ 2 * ‖j v‖ ^ 2 := by positivity
  have h4 : ∀ k, 0 ≤ ε k * ‖j (A k v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2 := by
    intro k
    rcases hε k with hk | hk
    · rw [hk]; positivity
    · have := h3 k hk
      rw [hk]; linarith
  have h5 : ε i * ‖j (A i v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2
      ≤ ∑ k, (ε k * ‖j (A k v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2) :=
    Finset.single_le_sum (f := fun k => ε k * ‖j (A k v)‖ ^ 2 + C ^ 2 * ‖j v‖ ^ 2)
      (fun k _ => h4 k) (Finset.mem_univ i)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h5
  have hc : c * ‖j v‖ ^ 2 ≤ |c| * ‖j v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
  have hc0 : 0 ≤ |c| * ‖j v‖ ^ 2 := by positivity
  have hd : 0 ≤ (d : ℝ) * (C ^ 2 * ‖j v‖ ^ 2) := by positivity
  have h6 : ‖j (A i v)‖ ^ 2 ≤ (|c| + (d + 1) * C ^ 2) * ‖j v‖ ^ 2 := by
    have e : (|c| + (d + 1) * C ^ 2) * ‖j v‖ ^ 2
        = |c| * ‖j v‖ ^ 2 + (d : ℝ) * (C ^ 2 * ‖j v‖ ^ 2) + C ^ 2 * ‖j v‖ ^ 2 := by ring
    rw [e]
    rcases hε i with hk | hk
    · rw [hk] at h5; linarith
    · have := h3 i hk
      linarith
  have h7 := Real.le_sqrt_of_sq_le h6
  rwa [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)] at h7
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_skewAdjoint_le_of_eigenvalue_bound :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (D : Module.End ℂ E) (M : ℝ), (∀ x y, inner ℂ (D x) y + inner ℂ x (D y) = 0) → (∀ z : ℂ, D.HasEigenvalue z → ‖z‖ ≤ M) → ∀ x, ‖D x‖ ≤ M * ‖x‖ := by
  intro E _ _ _ D M hskew hev x
  have hT : (Complex.I • D : E →ₗ[ℂ] E).IsSymmetric := by
    intro x y
    have h := hskew x y
    simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_I]
    linear_combination (-Complex.I) * h
  have hn : Module.finrank ℂ E = Module.finrank ℂ E := rfl
  have hb : ∀ i, |hT.eigenvalues hn i| ≤ M := by
    intro i
    have h1 := hT.apply_eigenvectorBasis hn i
    have h2 : D (hT.eigenvectorBasis hn i) = (-Complex.I * (hT.eigenvalues hn i : ℂ)) • hT.eigenvectorBasis hn i := by
      have h3 : D (hT.eigenvectorBasis hn i) = (-Complex.I) • ((Complex.I • D : E →ₗ[ℂ] E) (hT.eigenvectorBasis hn i)) := by
        rw [LinearMap.smul_apply, smul_smul]; simp
      rw [h3, h1, smul_smul]; rfl
    have h4 : D.HasEigenvalue (-Complex.I * (hT.eigenvalues hn i : ℂ)) :=
      Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.2 h2, (hT.eigenvectorBasis hn).orthonormal.ne_zero i⟩
    have h5 := hev _ h4
    simpa using h5
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : x = 0 := Subsingleton.elim _ _
    subst this
    simp
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb ⟨0, Module.finrank_pos⟩)
  have hDx : ‖D x‖ = ‖(Complex.I • D : E →ₗ[ℂ] E) x‖ := by
    simp [norm_smul]
  rw [hDx, ← (hT.eigenvectorBasis hn).repr.norm_map ((Complex.I • D : E →ₗ[ℂ] E) x),
    ← (hT.eigenvectorBasis hn).repr.norm_map x]
  apply abs_le_of_sq_le_sq' _ (by positivity) |>.2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h6 := hT.eigenvectorBasis_apply_self_apply hn x i
  rw [h6, norm_mul, mul_pow]
  gcongr
  simpa using hb i
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.finiteDimensional_of_compact_near_identity :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (S : Submodule ℂ H), IsCompactOperator T → (∀ v ∈ S, ‖T v - v‖ ≤ 1 / 2 * ‖v‖) → FiniteDimensional ℂ S := by
  intro H _ _ _ T S hT hS
  have hcl : IsClosed {v : H | ‖T v - v‖ ≤ 1 / 2 * ‖v‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hS' : ∀ v ∈ S.topologicalClosure, ‖T v - v‖ ≤ 1 / 2 * ‖v‖ := by
    intro v hv
    have : closure (S : Set H) ⊆ {v : H | ‖T v - v‖ ≤ 1 / 2 * ‖v‖} :=
      closure_minimal (fun w hw => hS w hw) hcl
    exact this hv
  haveI : CompleteSpace S.topologicalClosure :=
    S.isClosed_topologicalClosure.completeSpace_coe
  let f : S.topologicalClosure →L[ℂ] H := T.comp S.topologicalClosure.subtypeL
  have hf : ∀ x : S.topologicalClosure, ‖x‖ ≤ ((2 : NNReal) : ℝ) * ‖f x‖ := by
    intro x
    have h1 := hS' x.1 x.2
    have h2 : ‖(x : H)‖ ≤ ‖T x‖ + ‖T x - x‖ := by
      have : (x : H) = T x - (T x - x) := by abel
      calc ‖(x : H)‖ = ‖T x - (T x - x)‖ := congrArg norm this
        _ ≤ _ := norm_sub_le _ _
    have h3 : ‖x‖ = ‖(x : H)‖ := rfl
    have h4 : f x = T x := rfl
    rw [h3, h4]
    push_cast
    linarith
  have hanti : AntilipschitzWith 2 f := f.antilipschitz_of_bound hf
  have hemb : IsClosedEmbedding f := hanti.isClosedEmbedding f.uniformContinuous
  obtain ⟨K, hK, hKsub⟩ := IsCompactOperator.image_closedBall_subset_compact (f := (T : H →ₗ[ℂ] H)) hT 1
  have hc : IsCompact (Metric.closedBall (0 : S.topologicalClosure) 1) := by
    refine (hemb.isCompact_preimage hK).of_isClosed_subset Metric.isClosed_closedBall ?_
    intro x hx
    apply hKsub
    refine ⟨(x : H), ?_, rfl⟩
    rw [mem_closedBall_zero_iff] at hx ⊢
    exact hx
  haveI : FiniteDimensional ℂ S.topologicalClosure :=
    FiniteDimensional.of_isCompact_closedBall₀ ℂ one_pos hc
  exact Submodule.finiteDimensional_of_le S.le_topologicalClosure
end

section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.exists_signed_orthonormal_basis_of_isCompl :
    ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V) (k p : Submodule ℝ V), IsCompl k p → (∀ X Y, B X Y = B Y X) → (∀ X ∈ k, X ≠ 0 → B X X < 0) → (∀ X ∈ p, X ≠ 0 → 0 < B X X) → (∀ X ∈ k, ∀ Y ∈ p, B X Y = 0) → ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ V) (ε : Fin d → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) ∧ (∀ i j, B (b i) (b j) = if i = j then ε i else 0) ∧ ∀ i, ε i = -1 → b i ∈ k := by
  intro V _ _ _ B k p hc hsymm hneg hpos hzero
  classical
  obtain ⟨bk, hbk⟩ := exists_signed_basis (B.restrict k)
    (fun x y => hsymm (x : V) y) (s := -1)
    (by norm_num) (fun v hv => by
      have h0 : (v : V) ≠ 0 := fun e => hv (Subtype.ext e)
      have := hneg v v.2 h0
      change 0 < _ * B (v : V) v
      linarith)
  obtain ⟨bp, hbp⟩ := exists_signed_basis (B.restrict p)
    (fun x y => hsymm (x : V) y) (s := 1)
    (by norm_num) (fun v hv => by
      have h0 : (v : V) ≠ 0 := fun e => hv (Subtype.ext e)
      have := hpos v v.2 h0
      change 0 < _ * B (v : V) v
      linarith)
  set e := Submodule.prodEquivOfIsCompl k p hc
  set b0 := (bk.prod bp).map e
  set f : Fin (Module.finrank ℝ k) ⊕ Fin (Module.finrank ℝ p) → V :=
    Sum.elim (fun i => (bk i : V)) (fun j => (bp j : V))
  have hb0 : ∀ x, b0 x = f x := by
    rintro (i | j)
    · simp [b0, e, f, Submodule.coe_prodEquivOfIsCompl']
    · simp [b0, e, f, Submodule.coe_prodEquivOfIsCompl']
  set ε0 : Fin (Module.finrank ℝ k) ⊕ Fin (Module.finrank ℝ p) → ℝ :=
    Sum.elim (fun _ => -1) (fun _ => 1)
  have horth : ∀ x y, B (b0 x) (b0 y) = if x = y then ε0 x else 0 := by
    intro x y
    rw [hb0, hb0]
    rcases x with i | i <;> rcases y with j | j
    · have := hbk i j
      change B _ _ = _ at this
      simp only [f, ε0, Sum.elim_inl, Sum.inl.injEq]
      exact this
    · simp only [f, ε0, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      exact hzero _ (bk i).2 _ (bp j).2
    · simp only [f, ε0, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      rw [hsymm]
      exact hzero _ (bk j).2 _ (bp i).2
    · have := hbp i j
      change B _ _ = _ at this
      simp only [f, ε0, Sum.elim_inr, Sum.inr.injEq]
      exact this
  set σ := finSumFinEquiv (m := Module.finrank ℝ k) (n := Module.finrank ℝ p)
  refine ⟨_, b0.reindex σ, ε0 ∘ σ.symm, fun i => ?_, fun i j => ?_, fun i hi => ?_⟩
  · rcases hx : σ.symm i with a | a <;> simp [ε0, hx]
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, horth]
    simp only [Function.comp_apply, σ.symm.injective.eq_iff]
  · rw [Module.Basis.reindex_apply, hb0]
    simp only [Function.comp_apply] at hi
    rcases hx : σ.symm i with a | a
    · simp only [f, Sum.elim_inl]
      exact (bk a).2
    · rw [hx] at hi
      simp [ε0] at hi
      norm_num at hi
end
