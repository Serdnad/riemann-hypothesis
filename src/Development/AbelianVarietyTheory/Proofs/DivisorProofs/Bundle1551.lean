module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
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
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import ReciprocityTheory.SemistableReduction.Bundle002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem isIntegral_smul_of_charpoly_coeff_mul_int
    (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (x : A) (M : ℕ)
    (h : ∀ i, ∃ a : ℤ, (M : ℚ) * (LinearMap.mulLeft ℚ x).charpoly.coeff i = a) :
    IsIntegral ℤ ((M : ℤ) • x) := by
  set χ := (LinearMap.mulLeft ℚ x).charpoly with hχ
  have hmon : χ.Monic := LinearMap.charpoly_monic _

  have hx : Polynomial.aeval x χ = 0 := by
    have h1 : Polynomial.aeval (LinearMap.mulLeft ℚ x) χ = 0 := LinearMap.aeval_self_charpoly _
    have h2 : Polynomial.aeval (Algebra.lmul ℚ A x) χ = Algebra.lmul ℚ A (Polynomial.aeval x χ) :=
      Polynomial.aeval_algHom_apply _ _ _
    have h3 : Algebra.lmul ℚ A x = LinearMap.mulLeft ℚ x := rfl
    rw [h3, h1] at h2
    have := congrArg (fun f : A →ₗ[ℚ] A => f 1) h2
    simpa using this.symm
  have hs : Polynomial.aeval (algebraMap ℚ A (M : ℚ) * x) (χ.scaleRoots (M : ℚ)) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero hx
  have hsmon : (χ.scaleRoots (M : ℚ)).Monic := by
    unfold Polynomial.Monic Polynomial.leadingCoeff
    rw [Polynomial.natDegree_scaleRoots, Polynomial.coeff_scaleRoots, Nat.sub_self, pow_zero,
      mul_one]
    exact hmon
  have hlift : χ.scaleRoots (M : ℚ) ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy n χ.natDegree with hn | hn | hn
    · obtain ⟨a, ha⟩ := h n
      refine ⟨a * (M : ℤ) ^ (χ.natDegree - n - 1), ?_⟩
      have he : χ.natDegree - n = (χ.natDegree - n - 1) + 1 := by omega
      rw [he, pow_succ, map_mul, map_pow, eq_intCast, eq_intCast, ← ha]
      push_cast
      ring
    · subst hn
      rw [Nat.sub_self, pow_zero, mul_one]
      exact ⟨1, by simpa using hmon.coeff_natDegree.symm⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn, zero_mul]
      exact ⟨0, by simp⟩
  obtain ⟨q, hq, -, hqmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hsmon
  refine ⟨q, hqmon, ?_⟩
  have : Polynomial.aeval ((M : ℤ) • x) q = 0 := by
    rw [← Polynomial.aeval_map_algebraMap ℚ, hq]
    convert hs using 2
    rw [Algebra.smul_def]
    simp
  simpa [Polynomial.aeval_def] using this

end GlobalTheory
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.DetCoeff

theorem prod_monomial_eq {τ R ι : Type} [CommSemiring R] (s : Finset ι) (f : ι → τ →₀ ℕ) (a : ι → R) :
    ∏ i ∈ s, monomial (f i) (a i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, ih, monomial_mul, Finset.sum_insert hj, Finset.prod_insert hj]

open Classical in
theorem coeff_det_eq {F τ : Type} [Field F] {d : ℕ} (P : Matrix (Fin d) (Fin d) (MvPolynomial τ F))
    (s : Finset (τ →₀ ℕ)) (hs : ∀ i k, (P i k).support ⊆ s) (m : τ →₀ ℕ) :
    AddMonoidAlgebra.coeff P.det m = ∑ g ∈ Fintype.piFinset (fun _ : Fin d => s),
      if ∑ k, g k = m then (Matrix.of fun i k => AddMonoidAlgebra.coeff (P i k) (g k)).det else 0 := by
  classical
  have hP : ∀ i k, P i k = ∑ n ∈ s, monomial n (AddMonoidAlgebra.coeff (P i k) n) := by
    intro i k
    conv_lhs => rw [(P i k).as_sum]
    exact Finset.sum_subset (hs i k) (fun n _ hn => by simp [MvPolynomial.notMem_support_iff.mp hn])
  have hprod : ∀ σ : Equiv.Perm (Fin d), ∏ k, P (σ k) k = ∑ g ∈ Fintype.piFinset (fun _ : Fin d => s),
      monomial (∑ k, g k) (∏ k, AddMonoidAlgebra.coeff (P (σ k) k) (g k)) := by
    intro σ
    rw [Finset.prod_congr rfl (fun k _ => hP (σ k) k), Finset.prod_univ_sum]
    exact Finset.sum_congr rfl (fun g _ => prod_monomial_eq _ _ _)
  rw [Matrix.det_apply]
  simp_rw [hprod, Finset.smul_sum, coeff_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [Matrix.det_apply]
  split_ifs with h
  · subst h
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [Units.smul_def, MvPolynomial.coeff_smul, coeff_monomial, if_pos rfl]
    rfl
  · refine Finset.sum_eq_zero (fun σ _ => ?_)
    simp only [Units.smul_def, MvPolynomial.coeff_smul, coeff_monomial, if_neg h, smul_zero]

end GlobalTheory.DetCoeff

namespace GlobalTheory.DetCoeff

theorem coeff_det_mem_span_det : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (M : Submodule (𝓞 F) V) (d : ℕ) (b : Module.Basis (Fin d) F V) (τ : Type) (P : Matrix (Fin d) (Fin d) (MvPolynomial τ F)), (∀ k m, ∑ i, AddMonoidAlgebra.coeff (P i k) m • b i ∈ M) → ∀ m, AddMonoidAlgebra.coeff P.det m ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ M) ∧ y = b.det v} := by
  intro F V _ _ _ _ _ _ M d b τ P hP m
  classical
  have hs : ∀ i k, (P i k).support ⊆ Finset.univ.biUnion (fun ik : Fin d × Fin d => (P ik.1 ik.2).support) :=
    fun i k => Finset.subset_biUnion_of_mem (fun ik : Fin d × Fin d => (P ik.1 ik.2).support) (Finset.mem_univ (i, k))
  rw [coeff_det_eq P _ hs m]
  refine Submodule.sum_mem _ (fun g _ => ?_)
  split_ifs
  · apply Submodule.subset_span
    refine ⟨fun k => ∑ i, AddMonoidAlgebra.coeff (P i k) (g k) • b i, fun k => hP k (g k), ?_⟩
    rw [Module.Basis.det_apply]
    congr 1
    ext i k
    simp [Module.Basis.toMatrix_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
  · exact Submodule.zero_mem _

end GlobalTheory.DetCoeff
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.DetColon

variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ}

open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in
private lemma exterior_form_eq_zero_of_two_mem_span_singleton {ι : Type*} [DecidableEq ι]
    (f : V [⋀^ι]→ₗ[F] F) (u : V) (w : ι → V) {i k : ι} (hik : i ≠ k)
    (hi : w i ∈ Submodule.span (𝓞 F) {u}) (hk : w k ∈ Submodule.span (𝓞 F) {u}) :
    f w = 0 := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hi
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hk
  by_cases hb0 : algebraMap (𝓞 F) F b = 0
  · have hwk : w k = 0 := by
      rw [← hb, ← algebraMap_smul F b u, hb0, zero_smul]
    exact f.map_coord_zero k hwk
  · have hwi : w i = (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) • w k := by
      rw [← ha, ← hb, ← algebraMap_smul F a u, ← algebraMap_smul F b u, smul_smul,
        div_mul_cancel₀ _ hb0]
    have hfw : f w = f (Function.update w i
        ((algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F b) • w k)) := by
      rw [← hwi, Function.update_eq_self]
    rw [hfw, f.map_update_smul]
    have h0 : f (Function.update w i (w k)) = 0 :=
      f.map_eq_zero_of_eq (Function.update w i (w k)) (i := i) (j := k)
        (by simp [Function.update_of_ne hik.symm]) hik
    rw [h0, smul_zero]

open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in
private lemma multilinear_mem_span_of_entry_mem_span_singleton {ι : Type*} [DecidableEq ι]
    (f : V [⋀^ι]→ₗ[F] F) (N : Submodule (𝓞 F) V) (u : V) (s : Finset ι) :
    ∀ (i : ι) (w : ι → V), i ∉ s → w i ∈ Submodule.span (𝓞 F) {u} → (∀ j ∉ s, w j ∈ N) →
      (∀ j ∈ s, w j ∈ N ⊔ Submodule.span (𝓞 F) {u}) →
      f w ∈ Submodule.span (𝓞 F) {y | ∃ v : ι → V, (∀ j, v j ∈ N) ∧ y = f v} := by
  induction s using Finset.induction_on with
  | empty =>
    intro i w _ _ hN _
    exact Submodule.subset_span ⟨w, fun j => hN j (by simp), rfl⟩
  | @insert k s hks ih =>
    intro i w his hi hN hs
    have hik : i ≠ k := fun h => his (h ▸ Finset.mem_insert_self k s)
    have his' : i ∉ s := fun h => his (Finset.mem_insert_of_mem h)
    obtain ⟨n, hn, z, hz, hnz⟩ := Submodule.mem_sup.mp (hs k (Finset.mem_insert_self k s))
    have hsplit : f w = f (Function.update w k n) + f (Function.update w k z) := by
      rw [← f.map_update_add, hnz, Function.update_eq_self]
    rw [hsplit]
    refine Submodule.add_mem _ ?_ ?_
    · refine ih i _ his' ?_ ?_ ?_
      · rwa [Function.update_of_ne hik]
      · intro j hj
        by_cases hjk : j = k
        · rw [hjk, Function.update_self]
          exact hn
        · rw [Function.update_of_ne hjk]
          exact hN j (by simp [hjk, hj])
      · intro j hj
        have hjk : j ≠ k := fun h => hks (h ▸ hj)
        rw [Function.update_of_ne hjk]
        exact hs j (Finset.mem_insert_of_mem hj)
    · rw [exterior_form_eq_zero_of_two_mem_span_singleton f u _ hik
        (by rwa [Function.update_of_ne hik]) (by rw [Function.update_self]; exact hz)]
      exact Submodule.zero_mem _

open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in
private lemma smul_multilinear_mem_span {ι : Type*} [DecidableEq ι] (f : V [⋀^ι]→ₗ[F] F)
    (N : Submodule (𝓞 F) V) (u : V) (π : 𝓞 F) (hπ : π • u ∈ N) (s : Finset ι) :
    ∀ w : ι → V, (∀ j ∉ s, w j ∈ N) → (∀ j ∈ s, w j ∈ N ⊔ Submodule.span (𝓞 F) {u}) →
      π • f w ∈ Submodule.span (𝓞 F) {y | ∃ v : ι → V, (∀ j, v j ∈ N) ∧ y = f v} := by
  induction s using Finset.induction_on with
  | empty =>
    intro w hN _
    exact Submodule.smul_mem _ π (Submodule.subset_span ⟨w, fun j => hN j (by simp), rfl⟩)
  | @insert k s hks ih =>
    intro w hN hs
    obtain ⟨n, hn, z, hz, hnz⟩ := Submodule.mem_sup.mp (hs k (Finset.mem_insert_self k s))
    have hsplit : f w = f (Function.update w k n) + f (Function.update w k z) := by
      rw [← f.map_update_add, hnz, Function.update_eq_self]
    rw [hsplit, smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · refine ih _ ?_ ?_
      · intro j hj
        by_cases hjk : j = k
        · rw [hjk, Function.update_self]
          exact hn
        · rw [Function.update_of_ne hjk]
          exact hN j (by simp [hjk, hj])
      · intro j hj
        have hjk : j ≠ k := fun h => hks (h ▸ hj)
        rw [Function.update_of_ne hjk]
        exact hs j (Finset.mem_insert_of_mem hj)
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have key : π • f (Function.update w k (a • u)) = f (Function.update w k ((π * a) • u)) := by
        rw [mul_smul, ← algebraMap_smul F π (a • u), f.map_update_smul, algebraMap_smul]
      rw [key]
      refine multilinear_mem_span_of_entry_mem_span_singleton f N u s k _ hks ?_ ?_ ?_
      · rw [Function.update_self]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
      · intro j hj
        by_cases hjk : j = k
        · rw [hjk, Function.update_self, mul_comm, mul_smul]
          exact N.smul_mem a hπ
        · rw [Function.update_of_ne hjk]
          exact hN j (by simp [hjk, hj])
      · intro j hj
        have hjk : j ≠ k := fun h => hks (h ▸ hj)
        rw [Function.update_of_ne hjk]
        exact hs j (Finset.mem_insert_of_mem hj)


open NumberField MvPolynomial in
variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
  [IsScalarTower (𝓞 F) F V] {d : ℕ} in
theorem _root_.GlobalTheory.DetColon.smul_detSpan_sup_le :
    ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
      [IsScalarTower (𝓞 F) F V] (d : ℕ) (b : Module.Basis (Fin d) F V) (N : Submodule (𝓞 F) V)
      (u : V) (π : 𝓞 F), π • u ∈ N →
      ∀ y ∈ Submodule.span (𝓞 F)
          {y | ∃ v : Fin d → V, (∀ i, v i ∈ N ⊔ Submodule.span (𝓞 F) {u}) ∧ y = b.det v},
        π • y ∈ Submodule.span (𝓞 F) {y | ∃ v : Fin d → V, (∀ i, v i ∈ N) ∧ y = b.det v} := by
  intro F V _ _ _ _ _ _ d b N u π hπ y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact smul_multilinear_mem_span b.det N u π hπ Finset.univ v
      (fun j hj => absurd (Finset.mem_univ j) hj) (fun j _ => hv j)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hx

end GlobalTheory.DetColon
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort


open NumberField MvPolynomial in
theorem _root_.GlobalTheory.det_span_common_denominator : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (β : Module.Basis (Fin d) F V) (M : Submodule (𝓞 F) V), M.FG → ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ M) ∧ y = β.det w}, c • y ∈ (1 : Submodule (𝓞 F) F) := by
  intro F V _ _ _ _ _ _ d β M hM
  obtain ⟨S, hS⟩ := hM
  obtain ⟨c₀, hc₀⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 F))
    (Finset.univ ×ˢ S) (fun p : Fin d × V => β.repr p.2 p.1)
  have hcoord : ∀ x ∈ M, ∀ i, (c₀ : 𝓞 F) • β.repr x i ∈ (1 : Submodule (𝓞 F) F) := by
    intro x hx i
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨r, hr⟩ := hc₀ (i, g) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hg⟩)
      exact Submodule.mem_one.mpr ⟨r, hr⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _), Finsupp.add_apply, smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      convert Submodule.smul_mem _ a hx using 1
      rw [← algebraMap_smul F a x, map_smul, Finsupp.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def]
      ring
  refine ⟨(c₀ : 𝓞 F) ^ d, pow_ne_zero _ (nonZeroDivisors.ne_zero c₀.2), ?_⟩
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    choose B hB using fun i j => Submodule.mem_one.mp (hcoord (w j) (hw j) i)
    rw [Submodule.mem_one]
    refine ⟨(Matrix.of B).det, ?_⟩
    have hmat : (algebraMap (𝓞 F) F).mapMatrix (Matrix.of B) =
        algebraMap (𝓞 F) F (c₀ : 𝓞 F) • β.toMatrix w := by
      ext i j
      simp [Module.Basis.toMatrix_apply, hB, Algebra.smul_def]
    rw [RingHom.map_det, hmat, Matrix.det_smul, Fintype.card_fin, Module.Basis.det_apply,
      Algebra.smul_def, map_pow]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hx
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem basis_det_integral_span_eq_one : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (β : Module.Basis (Fin d) F V), Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ Submodule.span (𝓞 F) (Set.range β)) ∧ y = β.det w} = 1 := by
  intro F V _ _ _ _ _ _ d β
  have key : ∀ v ∈ Submodule.span (𝓞 F) (Set.range β), ∀ i, ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = β.repr v i := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro i
      refine ⟨if j = i then 1 else 0, ?_⟩
      rw [Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> simp
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i
      obtain ⟨a, ha⟩ := hx i
      obtain ⟨b, hb⟩ := hy i
      exact ⟨a + b, by simp [ha, hb]⟩
    | smul r x _ hx =>
      intro i
      obtain ⟨a, ha⟩ := hx i
      refine ⟨r * a, ?_⟩
      rw [← algebraMap_smul F r x, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, ha]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨w, hw, rfl⟩
    choose a ha using fun i => key (w i) (hw i)
    rw [SetLike.mem_coe, Submodule.mem_one, Module.Basis.det_apply]
    have hm : β.toMatrix w = (Matrix.of fun j i => a i j).map (algebraMap (𝓞 F) F) := by
      ext j i
      simp [Module.Basis.toMatrix_apply, ha]
    rw [hm]
    exact ⟨(Matrix.of fun j i => a i j).det, by rw [RingHom.map_det]; rfl⟩
  · rw [Submodule.one_le]
    exact Submodule.subset_span ⟨β, fun i => Submodule.subset_span ⟨i, rfl⟩, (β.det_self).symm⟩

end GlobalTheory
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem exists_maxIdeal_smul_mem_of_lt_of_relIndex_ne_zero (F V : Type) [Field F] [NumberField F]
    [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
    (N₀ N : Submodule (𝓞 F) V) (hlt : N₀ < N)
    (hidx : N₀.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0) :
    ∃ (u : V) (p : Ideal (𝓞 F)), p.IsMaximal ∧ u ∈ N ∧ u ∉ N₀ ∧ ∀ π ∈ p, π • u ∈ N₀ := by
  classical
  set P : Submodule (𝓞 F) N := N₀.comap N.subtype with hP
  have hPne : P ≠ ⊤ := by
    intro h
    obtain ⟨v, hvN, hvN₀⟩ := SetLike.exists_of_lt hlt
    have hv : (⟨v, hvN⟩ : N) ∈ P := h ▸ Submodule.mem_top
    exact hvN₀ hv
  haveI : Nontrivial (N ⧸ P) := Submodule.Quotient.nontrivial_iff.2 hPne
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty (𝓞 F) (N ⧸ P)
  obtain ⟨hprime, x, hx⟩ := (isAssociatedPrime_iff (R := 𝓞 F) (M := N ⧸ P)).1 hp
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P x
  have hmem : ∀ r : 𝓞 F, r ∈ p ↔ r • (y : V) ∈ N₀ := by
    intro r
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, hP, Submodule.mem_comap]
    rfl
  set n := N₀.toAddSubgroup.relIndex N.toAddSubgroup with hn
  have hkill : n • (y : V) ∈ N₀ := by
    have h := AddSubgroup.nsmul_index_mem (N₀.toAddSubgroup.addSubgroupOf N.toAddSubgroup)
      (⟨y.1, y.2⟩ : N.toAddSubgroup)
    exact AddSubgroup.mem_addSubgroupOf.1 h
  have hnp : ((n : ℕ) : 𝓞 F) ∈ p := by
    rw [hmem, Nat.cast_smul_eq_nsmul]
    exact hkill
  have hp0 : p ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hnp
    exact hidx (by exact_mod_cast hnp)
  refine ⟨(y : V), p, Ideal.IsPrime.isMaximal hprime hp0, y.2, ?_, fun π hπ => (hmem π).1 hπ⟩
  intro hy
  apply hprime.ne_top
  rw [eq_top_iff]
  intro r _
  rw [hmem]
  exact N₀.smul_mem r hy

end GlobalTheory
end

section

open Filter Topology MvPolynomial GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_finite_homogeneous_generators_graded_subgroup : ∀ (K : Type) [CommRing K] (D c : ℕ) (x : Fin (D + 1) → K) (ι : Type) [Fintype ι] (w : ι → K) (Λ : ℕ → AddSubgroup K), (∀ q l, ∀ f ∈ Λ q, x l * f ∈ Λ (q + 1)) → (∀ q, ∀ f ∈ Λ q, ∃ T : ι → MvPolynomial (Fin (D + 1)) ℤ, (∀ i, (T i).IsHomogeneous (q + c)) ∧ f = ∑ i, aeval x (T i) * w i) → ∃ G : Finset (ℕ × K), (∀ g ∈ G, g.2 ∈ Λ g.1) ∧ ∀ q, Λ q ≤ AddSubgroup.closure {f | ∃ g ∈ G, ∃ α : Fin (D + 1) → ℕ, ∑ l, α l + g.1 = q ∧ f = (∏ l, x l ^ α l) * g.2} := by
  first | exact @GlobalTheory.HSAmpGen.exists_finite_homogeneous_generators | exact GlobalTheory.HSAmpGen.exists_finite_homogeneous_generators | (intros; apply GlobalTheory.HSAmpGen.exists_finite_homogeneous_generators <;> assumption)
end
