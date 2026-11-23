module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle145
public import Mathlib.RingTheory.WittVector.Frobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittVectorExistsUniqueSubMatrixFrobeniusEq
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle146
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle001
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
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
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.tensor_centralizer_injective_commutant_eq : ∀ (K : Type) [Field K] [Algebra ℚ K] (C : Type) [Ring C] [Algebra ℚ C] (y : C),
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val) ∧
    ∀ w : K ⊗[ℚ] C, Commute w ((1 : K) ⊗ₜ[ℚ] y) → ∃ w' : K ⊗[ℚ] (Subalgebra.centralizer ℚ ({y} : Set C)),
      Algebra.TensorProduct.map (AlgHom.id K K) (Subalgebra.centralizer ℚ ({y} : Set C)).val w' = w := by
  first | (exact @GlobalTheory.tensor_centralizer_flat) | (exact GlobalTheory.tensor_centralizer_flat) | (intros; apply GlobalTheory.tensor_centralizer_flat <;> assumption)
end

section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.algebra_trace_map_of_cokernel_killed_by_scalar : ∀ (S A B : Type) [CommRing S] [IsDomain S] [CommRing A] [Algebra S A] [Module.Free S A] [Module.Finite S A] [CommRing B] [Algebra S B] [Module.Free S B] [Module.Finite S B] (φ : A →ₐ[S] B), Function.Injective φ → ∀ s : S, s ≠ 0 → (∀ b : B, s • b ∈ φ.range) → ∀ x : A, Algebra.trace S B (φ x) = Algebra.trace S A x := by
  first | exact @GlobalTheory.algebraTrace_map_of_cokernel_killed | exact GlobalTheory.algebraTrace_map_of_cokernel_killed | (intros; apply GlobalTheory.algebraTrace_map_of_cokernel_killed <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified' : ∀ (P D : Type) [CommRing P] [IsDomain P] [CommRing D] [IsDomain D] [Algebra P D] [Algebra.FiniteType P D] [Algebra.FormallyUnramified P D] (f : D), f ≠ 0 → ∃ Q : P, Q ≠ 0 ∧ ∃ d : D, algebraMap P D Q = f * d := by
  first | exact @GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified | exact GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified | (intros; apply GlobalTheory.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified <;> assumption)
end

section


theorem _root_.GlobalTheory.T.map_comap_maximalIdeal_eq_of_formallyUnramified' : ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B], ((IsLocalRing.maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) = IsLocalRing.maximalIdeal B := by
  first | exact @GlobalTheory.map_comap_maximalIdeal_eq_of_formallyUnramified | exact GlobalTheory.map_comap_maximalIdeal_eq_of_formallyUnramified | (intros; apply GlobalTheory.map_comap_maximalIdeal_eq_of_formallyUnramified <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual
open scoped Pointwise

namespace GlobalTheory.QuadSplit

theorem mem_decompositionSubgroup_iff' {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : ValuationSubring Ω)
    (g : Ω ≃ₐ[K] Ω) : g ∈ A.decompositionSubgroup K ↔ ∀ x, g x ∈ A ↔ x ∈ A := by
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  constructor
  · intro h x
    rw [← ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (S := A) (x := x), h]
    rfl
  · intro h
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h]
    simp [AlgEquiv.smul_def]

end GlobalTheory.QuadSplit
end
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.exists_integral_relation_C_mul_X_pow_of_valuationSubring : ∀ (F K : Type) [Field F] [Field K] (φ : F →+* K) (r e : ℕ) (w : Fin r → K) (τ : K), (∀ V : ValuationSubring K, (∀ c, φ c ∈ V) → ∃ i, w i ≠ 0 ∧ τ / w i ^ e ∈ V) → ∃ (m : ℕ) (b : Fin m → MvPolynomial (Fin r) F), (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) (b k) * (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0 := by
  first | exact @GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring | exact GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring | (intros; apply GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring <;> assumption)
end

section


theorem _root_.GlobalTheory.T.wittVector_existsUnique_sub_matrix_frobenius_eq : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p] [PerfectRing R p] (ι : Type) [Fintype ι] (M : Matrix ι ι (WittVector p R)), (∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec (fun k => frobenius R p (x k)) = c) → ∀ c : ι → WittVector p R, ∃! v : ι → WittVector p R, v - M.mulVec (fun k => WittVector.frobenius (v k)) = c := by
  first | exact @GlobalTheory.wittSolve_unique | exact GlobalTheory.wittSolve_unique | (intros; apply GlobalTheory.wittSolve_unique <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.exists_compact_mod_normOneKernel_involution : ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [LocallyCompactSpace Z] [SigmaCompactSpace Z] [T2Space Z], (∀ a b : Z, a * b = b * a) → ∀ τ : Z →* Z, Continuous τ → (∀ z, τ (τ z) = z) → (∃ W ∈ nhds (1 : Z), ∀ s ∈ W, τ s = s → ∃ r : Z, τ r = r ∧ r * r = s) → ∀ D : Set Z, IsCompact D → ∃ B : Set Z, IsCompact B ∧ ∀ z : Z, τ z * z ∈ D → ∃ t : Z, τ t * t = 1 ∧ ∃ b ∈ B, z = t * b := by
  first | exact @GlobalTheory.InvolutionNorm.exists_compact_mod_kernel | exact GlobalTheory.InvolutionNorm.exists_compact_mod_kernel | (intros; apply GlobalTheory.InvolutionNorm.exists_compact_mod_kernel <;> assumption)
end

section

open TopologicalSpace

theorem _root_.GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero : ∀ (S : Type) [TopologicalSpace S] [NoetherianSpace S], (∀ (C : Set S) (d : ℕ), IsClosed C → topologicalKrullDim S ≤ d → (∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) → topologicalKrullDim C < d) ∧ (T0Space S → topologicalKrullDim S ≤ 0 → Finite S) := by
  first | exact @GlobalTheory.DimDrop.dim_drop | exact GlobalTheory.DimDrop.dim_drop | (intros; apply GlobalTheory.DimDrop.dim_drop <;> assumption)
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.tendsto_div_pow_of_choose_bounds : ∀ (D e δ : ℕ) (r : ℕ → ℕ), 0 < e → (∀ s : ℕ, s < e → ∃ c c' : ℕ, ∀ q : ℕ, δ * (q + D).choose D ≤ r (e * (q + c) + s) ∧ r (e * q + s) ≤ δ * (q + c' + D).choose D) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by
  first | exact @GlobalTheory.tendsto_rank_div_pow_of_choose_bounds | exact GlobalTheory.tendsto_rank_div_pow_of_choose_bounds | (intros; apply GlobalTheory.tendsto_rank_div_pow_of_choose_bounds <;> assumption)
end

section

open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem geomRegFib_of_isRegularRing_essFiniteType :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B],
      (∀ (K : Type) [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (B ⊗[R] K)) →
        FinalTheorems.GeomRegFib R B := by
  intro R B _ _ _ h P _ K _ _ _ _ hfg
  haveI : Algebra.EssFiniteType P.ResidueField K := IntermediateField.fg_top_iff.mp hfg
  haveI : Algebra.EssFiniteType R K := Algebra.EssFiniteType.comp R P.ResidueField K
  haveI hr : IsRegularRing (B ⊗[R] K) := h K
  exact ⟨inferInstance, fun Q _ => hr.isRegularLocalRing_localization Q⟩

end GlobalTheory
end

section

open IsLocalRing TensorProduct Pointwise

namespace GlobalTheory

theorem modDepthGE_two_of_isSMulRegular_of_quotSMulTop :
    ∀ (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (M : Type) [AddCommGroup M]
      [Module S M] [Module.Finite S M] [Nontrivial M] (x : S), x ∈ maximalIdeal S →
      IsSMulRegular M x →
      (∀ u : M, (∀ a ∈ maximalIdeal S, a • u ∈ x • (⊤ : Submodule S M)) →
        u ∈ x • (⊤ : Submodule S M)) →
      ReciprocityTheory.CA.ModDepthGE S M 2 := by
  intro S _ _ _ M _ _ _ _ x hxm hreg hsoc
  obtain ⟨y, hym, hyreg⟩ : ∃ y ∈ maximalIdeal S, IsSMulRegular (QuotSMulTop x M) y := by
    by_contra hno
    push_neg at hno
    have hfin := associatedPrimes.finite S (QuotSMulTop x M)
    have hsub : (maximalIdeal S : Set S) ⊆
        ⋃ p ∈ associatedPrimes S (QuotSMulTop x M), (p : Set S) := by
      intro y hy
      rw [biUnion_associatedPrimes_eq_compl_regular]
      exact hno y hy
    obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥
      (fun p hp _ _ => (hfin.mem_toFinset.mp hp).isPrime)).mp (by simpa using hsub)
    rw [hfin.mem_toFinset] at hp
    have hpm : p = maximalIdeal S :=
      (le_antisymm (le_maximalIdeal (hp.isPrime.ne_top)) hmp)
    rw [hpm] at hp
    obtain ⟨-, w, hw⟩ := isAssociatedPrime_iff.mp hp
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hu : ∀ a ∈ maximalIdeal S, a • u ∈ x • (⊤ : Submodule S M) := by
      intro a ha
      rw [hw, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero] at ha
      exact ha
    apply (maximalIdeal.isMaximal S).ne_top
    rw [hw, Ideal.eq_top_iff_one, Submodule.mem_colon_singleton, Submodule.mem_bot, one_smul,
      Submodule.Quotient.mk_eq_zero]
    exact hsoc u hu
  refine ⟨[x, y], rfl, (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption), ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption),
    RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff]
  exact ⟨hreg, hyreg, RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩

end GlobalTheory
end
