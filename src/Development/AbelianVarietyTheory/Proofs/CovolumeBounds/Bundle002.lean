module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Nullstellensatz
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

open Set Metric Filter Topology
open scoped Nat

namespace GlobalTheory

section Periodic

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem entire_apply_eq_of_isZLattice_periodic [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → V} (hF : Differentiable ℂ F) (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hper : ∀ x, ∀ g ∈ L, F (x + g) = F x) (z w : E) : F z = F w :=
  hF.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L F hF.continuous hper).isBounded z w


omit [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V] in
theorem periodic_of_mem_span_int {F : E → V} {S : Set E}
    (hper : ∀ x, ∀ g ∈ S, F (x + g) = F x) :
    ∀ x, ∀ g ∈ Submodule.span ℤ S, F (x + g) = F x := by
  let P : AddSubgroup E :=
    { carrier := {g | ∀ x, F (x + g) = F x}
      zero_mem' := fun x => by simp
      add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by rw [← ha (x + -a)]; simp }
  intro x g hg
  have : Submodule.span ℤ S ≤ AddSubgroup.toIntSubmodule P :=
    Submodule.span_le.2 fun s hs y => hper y s hs
  exact this hg x

theorem entire_apply_eq_of_periodic_of_span_real [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → V} (hF : Differentiable ℂ F) {S : Set E} (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ x, ∀ g ∈ S, F (x + g) = F x) (z w : E) : F z = F w := by
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent ℝ S
  let b : Module.Basis t ℝ E := Module.Basis.mk hli (by simp [hspan, hS])
  haveI : Finite t := Module.Finite.finite_basis b
  refine entire_apply_eq_of_isZLattice_periodic hF (Submodule.span ℤ (range b))
    (periodic_of_mem_span_int ?_) z w
  rintro x _ ⟨i, rfl⟩
  exact hper x _ (by simpa [b] using htS i.2)

end Periodic

section Polynomial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem iteratedDeriv_zero_eq_zero_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) {n : ℕ} (hn : m < n) :
    iteratedDeriv n F 0 = 0 := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hb 0)
  have key : ∀ R : ℝ, 1 ≤ R → ‖iteratedDeriv n F 0‖ ≤ (n ! * C * 2 ^ m) / R := by
    intro R hR
    have hR0 : 0 < R := by linarith
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := R)
      (C := C * (2 ^ m * R ^ m)) n hR0 hF.diffContOnCl (fun z hz => by
        have hz' : ‖z‖ = R := by simpa using hz
        refine (hb z).trans ?_
        rw [hz', ← mul_pow]
        gcongr
        linarith)
    refine h.trans ?_
    rw [div_le_div_iff₀ (by positivity) hR0]
    have : R ^ m * R ≤ R ^ n := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hR hn
    calc (n ! : ℝ) * (C * (2 ^ m * R ^ m)) * R = (n ! * C * 2 ^ m) * (R ^ m * R) := by ring
      _ ≤ _ := by gcongr
  have lim : Tendsto (fun R : ℝ => (n ! * C * 2 ^ m) / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact norm_le_zero_iff.1 (ge_of_tendsto lim ((eventually_ge_atTop 1).mono key))

theorem entire_eq_taylor_sum_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) (z : ℂ) :
    F z = ∑ k ∈ Finset.range (m + 1), z ^ k • ((k ! : ℂ)⁻¹ • iteratedDeriv k F 0) := by
  have h := Complex.hasSum_taylorSeries_of_entire hF 0 z
  have h2 := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (f := fun n : ℕ => (n ! : ℂ)⁻¹ • (z - 0) ^ n • iteratedDeriv n F 0)
    (s := Finset.range (m + 1)) (fun n hn => by
      have : m < n := by simpa using hn
      simp [iteratedDeriv_zero_eq_zero_of_poly_bound hF hb this])
  rw [h.unique h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sub_zero, smul_comm]

theorem entire_exists_coeff_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ a : ℕ → V, ∀ z, F z = ∑ k ∈ Finset.range (m + 1), z ^ k • a k :=
  ⟨_, entire_eq_taylor_sum_of_poly_bound hF hb⟩

theorem entire_exists_polynomial_of_poly_bound {F : ℂ → ℂ} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ m ∧ ∀ z, F z = p.eval z := by
  obtain ⟨a, ha⟩ := entire_exists_coeff_of_poly_bound hF hb
  refine ⟨∑ k ∈ Finset.range (m + 1), Polynomial.monomial k (a k), ?_, fun z => ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    exact (Polynomial.natDegree_monomial_le _).trans (by simpa [Nat.lt_succ_iff] using hk)
  · rw [ha z, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]

end Polynomial

end GlobalTheory
end

section

open scoped BigOperators
open Module

namespace GlobalTheory

section PolynomialFunction

variable (K : Type*) [CommSemiring K] {M : Type*} [AddCommMonoid M] [Module K M]

variable {K}

end PolynomialFunction

section Frames

variable {ι : Type*} {K : Type*} {V : ι → Type*}

section Semiring

variable [CommSemiring K] [∀ s, AddCommMonoid (V s)] [∀ s, Module K (V s)]
  {l m n : ι → Type*} [∀ s, Fintype (l s)] [∀ s, Fintype (m s)]

abbrev EntryIndex (m n : ι → Type*) : Type _ := Σ s, m s × n s

def entries {α : Type*} (b : ∀ s, Matrix (m s) (n s) α) : EntryIndex m n → α :=
  fun k => b k.1 k.2.1 k.2.2

def ofEntries {α : Type*} (ξ : EntryIndex m n → α) : ∀ s, Matrix (m s) (n s) α :=
  fun s => Matrix.of fun i j => ξ ⟨s, i, j⟩

omit [∀ s, Fintype (m s)] in
@[simp] theorem entries_apply {α : Type*} (b : ∀ s, Matrix (m s) (n s) α) (s : ι) (i : m s)
    (j : n s) : entries b ⟨s, i, j⟩ = b s i j := rfl




end Semiring

variable [Fintype ι] {r : ι → ℕ} [Field K] [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)]
  {W : Type*} [AddCommGroup W] [Module K W]


end Frames

section Hadamard

variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜] {V : ι → Type*}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

section Inner

variable [∀ s, NormedAddCommGroup (V s)] [∀ s, InnerProductSpace 𝕜 (V s)]
  [∀ s, FiniteDimensional 𝕜 (V s)]

end Inner

end Hadamard

section PolynomialWeight

variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {K : Type*} [Field K]

noncomputable def detProdPoly (R : Type*) [CommRing R] (n : ι → Type*) [∀ s, Fintype (n s)]
    [∀ s, DecidableEq (n s)] : MvPolynomial (EntryIndex n n) R :=
  ∏ s, (ofEntries MvPolynomial.X s).det

end PolynomialWeight

section HadamardPolynomial

variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜]

end HadamardPolynomial

section Gauss

open MvPolynomial IsLocalRing

variable {K Γ O : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ}
  [CommRing O] [Algebra O K]

variable [IsLocalRing O] [Infinite (ResidueField O)]

variable {ι : Type*} [Fintype ι]

section Matrices

variable {n : ι → Type*} [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)]

end Matrices

section Lattices

variable {V : ι → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)] [∀ s, Module O (V s)]
  [∀ s, IsScalarTower O K (V s)] {Λ : ∀ s, Submodule O (V s)}

variable {r : ι → ℕ}

end Lattices

end Gauss

end GlobalTheory
end

section

namespace GlobalTheory

open MvPolynomial

section Vanishing

variable {σ R : Type*} [Finite σ] [CommRing R] [IsDomain R] [CharZero R]

theorem eq_zero_of_eval_box_eq_zero (d : σ → ℕ) (P : MvPolynomial σ R)
    (hdeg : ∀ i, P.degreeOf i ≤ d i)
    (hP : ∀ x : σ → ℕ, (∀ i, x i ≤ d i) → eval (fun i => (x i : R)) P = 0) : P = 0 := by
  classical
  refine eq_zero_of_eval_zero_at_prod_finset P
    (fun i => (Finset.range (d i + 1)).image (Nat.cast : ℕ → R)) (fun i => ?_) (fun x hx => ?_)
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact Nat.lt_succ_of_le (hdeg i)
  · choose n hn hnx using fun i => Finset.mem_image.1 (hx i)
    have : x = fun i => (n i : R) := funext fun i => (hnx i).symm
    rw [this]
    exact hP n fun i => Nat.lt_succ_iff.1 (Finset.mem_range.1 (hn i))

theorem eq_zero_of_eval_grid_eq_zero (d : ℕ) (P : MvPolynomial σ R)
    (hdeg : ∀ i, P.degreeOf i ≤ d)
    (hP : ∀ x : σ → ℕ, (∀ i, x i ≤ d) → eval (fun i => (x i : R)) P = 0) : P = 0 :=
  eq_zero_of_eval_box_eq_zero (fun _ => d) P hdeg hP

end Vanishing

section Span

variable {σ A K V : Type*} [Finite σ] [Field K] [CharZero K] [CommSemiring A] [Algebra A K]
  [AddCommGroup V] [Module K V]

theorem mem_of_grid_mem (d : ℕ) (Φ : (σ → A) → V)
    (hΦ : ∀ l : Module.Dual K V, ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧
      ∀ x, l (Φ x) = eval (fun i => algebraMap A K (x i)) P)
    (U : Submodule K V)
    (hU : ∀ x : σ → ℕ, (∀ i, x i ≤ d) → Φ (fun i => (x i : A)) ∈ U) (y : σ → A) :
    Φ y ∈ U := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U]
  intro l hl
  obtain ⟨P, hdeg, hP⟩ := hΦ l
  have h0 : P = 0 := by
    refine eq_zero_of_eval_grid_eq_zero d P hdeg fun x hx => ?_
    have := (Submodule.mem_dualAnnihilator l).1 hl _ (hU x hx)
    rw [hP] at this
    simpa using this
  rw [hP, h0, map_zero]

theorem span_grid_eq_span_range (d : ℕ) (Φ : (σ → A) → V)
    (hΦ : ∀ l : Module.Dual K V, ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧
      ∀ x, l (Φ x) = eval (fun i => algebraMap A K (x i)) P) :
    Submodule.span K ((fun x : σ → ℕ => Φ fun i => (x i : A)) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range Φ) := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨x, -, rfl⟩
    exact ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    refine mem_of_grid_mem d Φ hΦ _ (fun x hx => ?_) y
    apply Submodule.subset_span
    exact ⟨x, hx, rfl⟩


omit [Finite σ] [CharZero K] in
theorem exists_poly_dual_sum_monomial_smul (d : ℕ) (s : Finset (σ →₀ ℕ)) (v : (σ →₀ ℕ) → V)
    (hs : ∀ a ∈ s, ∀ i, a i ≤ d) (l : Module.Dual K V) :
    ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧ ∀ x : σ → A,
      l (∑ a ∈ s, (a.prod fun i n => algebraMap A K (x i) ^ n) • v a) =
        eval (fun i => algebraMap A K (x i)) P := by
  classical
  refine ⟨∑ a ∈ s, monomial a (l (v a)), fun i => ?_, fun x => ?_⟩
  · rw [degreeOf_le_iff]
    intro m hm
    obtain ⟨a, ha, hma⟩ := Finset.mem_biUnion.1 (support_sum hm)
    have := Finset.mem_singleton.1 (support_monomial_subset hma)
    rw [this]
    exact hs a ha i

  · simp only [map_sum, map_smul, eval_monomial, smul_eq_mul, mul_comm]

theorem span_grid_eq_span_range_of_eq_sum (d : ℕ) (Φ : (σ → A) → V)
    (s : Finset (σ →₀ ℕ)) (v : (σ →₀ ℕ) → V) (hs : ∀ a ∈ s, ∀ i, a i ≤ d)
    (hΦ : ∀ x, Φ x = ∑ a ∈ s, (a.prod fun i n => algebraMap A K (x i) ^ n) • v a) :
    Submodule.span K ((fun x : σ → ℕ => Φ fun i => (x i : A)) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range Φ) := by
  refine span_grid_eq_span_range d Φ fun l => ?_
  simp only [hΦ]
  exact exists_poly_dual_sum_monomial_smul d s v hs l

theorem span_grid_eval_eq_span_range {B : Type*} [CommRing B] [Algebra K B] (d : ℕ)
    (F : MvPolynomial σ B) (hF : ∀ i, F.degreeOf i ≤ d) :
    Submodule.span K ((fun x : σ → ℕ => eval (fun i => (x i : B)) F) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range fun x : σ → A =>
        eval (fun i => algebraMap K B (algebraMap A K (x i))) F) := by
  have h := span_grid_eq_span_range_of_eq_sum (K := K) d
    (fun x : σ → A => eval (fun i => algebraMap K B (algebraMap A K (x i))) F)
    F.support (fun a => F.coeff a) (fun a ha i => (degreeOf_le_iff.1 (hF i)) a ha)
    (fun x => by
      rw [eval_eq]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Algebra.smul_def, Finsupp.prod, map_prod, mul_comm]
      simp only [map_pow])
  simpa only [map_natCast] using h

end Span

section Combination

variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] {W : ι → Type*}
  [∀ j, AddCommGroup (W j)]

theorem exists_nsmul_add_apply_ne_zero [∀ j, IsAddTorsionFree (W j)] (l : ∀ j, V →+ W j)
    (v w : V) :
    ∃ c : ℕ, c ≤ Fintype.card ι ∧ ∀ j, l j v ≠ 0 ∨ l j w ≠ 0 → l j (c • w + v) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  choose f hf hf0 using h
  have hinj : Function.Injective fun a : Fin (Fintype.card ι + 1) =>
      f a (Nat.lt_succ_iff.1 a.2) := by
    intro a b hab
    have h1 := hf0 a (Nat.lt_succ_iff.1 a.2)
    have h2 := hf0 b (Nat.lt_succ_iff.1 b.2)
    have h3 := hf a (Nat.lt_succ_iff.1 a.2)
    simp only at hab
    rw [← hab] at h2
    generalize f a _ = j at h1 h2 h3
    rw [map_add (f := _), map_nsmul] at h1 h2
    have hw : l j w ≠ 0 := by
      intro hw
      rw [hw, nsmul_zero, zero_add] at h1
      exact h3.elim (· h1) (· hw)
    have h4 : (a : ℕ) • l j w = (b : ℕ) • l j w := add_right_cancel (h1.trans h2.symm)
    have h5 : ((a : ℤ) - (b : ℤ)) • l j w = 0 := by
      rw [sub_smul, natCast_zsmul, natCast_zsmul, h4, sub_self]
    have h6 := (IsAddTorsionFree.zsmul_eq_zero_iff_left hw).1 h5
    exact Fin.ext (by omega)
  have := Fintype.card_le_of_injective _ hinj
  simp at this

theorem exists_sum_nsmul_apply_ne_zero_finset [∀ j, IsAddTorsionFree (W j)]
    (l : ∀ j, V →+ W j) (s : κ → V) (t : Finset κ) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧
      ∀ j, (∃ k ∈ t, l j (s k) ≠ 0) → l j (∑ k ∈ t, c k • s k) ≠ 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, fun _ => Nat.zero_le _, fun j ⟨k, hk, _⟩ => absurd hk (by simp)⟩
  | insert a t ha ih =>
    obtain ⟨c, hc, hl⟩ := ih
    obtain ⟨n, hn, hln⟩ := exists_nsmul_add_apply_ne_zero l (∑ k ∈ t, c k • s k) (s a)
    refine ⟨Function.update c a n, fun k => ?_, fun j ⟨k, hk, hjk⟩ => ?_⟩
    · by_cases hk : k = a
      · subst hk; simpa using hn
      · simpa [hk] using hc k
    · rw [Finset.sum_insert ha, Function.update_self,
        Finset.sum_congr rfl (g := fun k => c k • s k) fun k hk => by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hk ha)]]
      apply hln
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact Or.inr hjk
      · exact Or.inl (hl j ⟨k, hk, hjk⟩)

theorem exists_sum_nsmul_apply_ne_zero [∀ j, IsAddTorsionFree (W j)] [Fintype κ]
    (l : ∀ j, V →+ W j) (s : κ → V) (h : ∀ j, ∃ k, l j (s k) ≠ 0) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧ ∀ j, l j (∑ k, c k • s k) ≠ 0 := by
  obtain ⟨c, hc, hl⟩ := exists_sum_nsmul_apply_ne_zero_finset l s Finset.univ
  exact ⟨c, hc, fun j => hl j ((h j).imp fun k hk => ⟨Finset.mem_univ k, hk⟩)⟩

variable {K : Type*} [Field K] [CharZero K] [Module K V] [∀ j, Module K (W j)]

theorem exists_sum_natCast_smul_apply_ne_zero [Fintype κ]
    (l : ∀ j, V →ₗ[K] W j) (s : κ → V) (h : ∀ j, ∃ k, l j (s k) ≠ 0) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧ ∀ j, l j (∑ k, (c k : K) • s k) ≠ 0 := by
  have : ∀ j, IsAddTorsionFree (W j) := fun j => by
    letI : HasUniqueDiv (W j) := HasUniqueDiv.of_isTorsionFree K (W j)
    infer_instance
  simp only [Nat.cast_smul_eq_nsmul]
  exact exists_sum_nsmul_apply_ne_zero (fun j => (l j).toAddMonoidHom) s h

end Combination

end GlobalTheory
end
