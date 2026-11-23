module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

@[expose] public section

section

namespace UpperTheory.Reformulated.B.StringRepresentationDecomposition

open Matrix

section

variable {K : Type*} [NormedField K]

private def Small {a b : Type*} (A : Matrix a b K) : Prop := ∀ i j, ‖A i j‖ ≤ 1

private def Good {a : Type*} [Fintype a] [DecidableEq a] (A : Matrix a a K) : Prop :=
  Small A ∧ ∃ B : Matrix a a K, Small B ∧ A * B = 1

private def Smith {a : Type*} [Fintype a] [DecidableEq a] (M : Matrix a a K) : Prop :=
  ∃ (U V : Matrix a a K) (d : a → K), Good U ∧ Good V ∧ M = U * diagonal d * V

private lemma small_zero {a b : Type*} : Small (0 : Matrix a b K) := by
  intro i j; simp

private lemma small_one {a : Type*} [DecidableEq a] : Small (1 : Matrix a a K) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

private lemma small_neg {a b : Type*} {A : Matrix a b K} (h : Small A) : Small (-A) := by
  intro i j; simpa using h i j

private lemma small_blocks {a b : Type*} {A : Matrix a a K} {B : Matrix a b K}
    {C : Matrix b a K} {D : Matrix b b K} (hA : Small A) (hB : Small B) (hC : Small C)
    (hD : Small D) : Small (fromBlocks A B C D) := by
  rintro (i | i) (j | j)
  exacts [hA i j, hB i j, hC i j, hD i j]

private lemma small_mul [IsUltrametricDist K] {a : Type*} [Fintype a] {A B : Matrix a a K}
    (hA : Small A) (hB : Small B) : Small (A * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro k _
  rw [norm_mul]
  exact mul_le_one₀ (hA i k) (norm_nonneg _) (hB k j)

private lemma good_one {a : Type*} [Fintype a] [DecidableEq a] : Good (1 : Matrix a a K) :=
  ⟨small_one, 1, small_one, Matrix.mul_one _⟩

private lemma good_mul [IsUltrametricDist K] {a : Type*} [Fintype a] [DecidableEq a]
    {A B : Matrix a a K} (hA : Good A) (hB : Good B) : Good (A * B) := by
  obtain ⟨h1, A', h2, h3⟩ := hA
  obtain ⟨h4, B', h5, h6⟩ := hB
  refine ⟨small_mul h1 h4, B' * A', small_mul h5 h2, ?_⟩
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, h6, Matrix.one_mul, h3]

private lemma good_submatrix {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] {A : Matrix a a K} (hA : Good A) (f g : b ≃ a) :
    Good (A.submatrix f g) := by
  obtain ⟨h1, A', h2, h3⟩ := hA
  refine ⟨fun i j => h1 _ _, A'.submatrix g f, fun i j => h2 _ _, ?_⟩
  rw [Matrix.submatrix_mul_equiv, h3, Matrix.submatrix_one_equiv]

private lemma smith_submatrix {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] {M : Matrix a a K} (hM : Smith M) (f g : b ≃ a) :
    Smith (M.submatrix f g) := by
  obtain ⟨U, V, d, hU, hV, rfl⟩ := hM
  refine ⟨U.submatrix f f, V.submatrix f g, d ∘ f, good_submatrix hU f f,
    good_submatrix hV f g, ?_⟩
  rw [← Matrix.submatrix_diagonal_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

private lemma smith_mul [IsUltrametricDist K] {a : Type*} [Fintype a] [DecidableEq a]
    {L M R : Matrix a a K} (hL : Good L) (hM : Smith M) (hR : Good R) :
    Smith (L * M * R) := by
  obtain ⟨U, V, d, hU, hV, rfl⟩ := hM
  exact ⟨L * U, V * R, d, good_mul hL hU, good_mul hV hR, by simp only [Matrix.mul_assoc]⟩

private lemma good_lower {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] {C : Matrix b a K} (hC : Small C) :
    Good (fromBlocks (1 : Matrix a a K) 0 C (1 : Matrix b b K)) := by
  refine ⟨small_blocks small_one small_zero hC small_one, fromBlocks 1 0 (-C) 1,
    small_blocks small_one small_zero (small_neg hC) small_one, ?_⟩
  simp [Matrix.fromBlocks_multiply]

private lemma good_upper {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] {C : Matrix a b K} (hC : Small C) :
    Good (fromBlocks (1 : Matrix a a K) C 0 (1 : Matrix b b K)) := by
  refine ⟨small_blocks small_one hC small_zero small_one, fromBlocks 1 (-C) 0 1,
    small_blocks small_one (small_neg hC) small_zero small_one, ?_⟩
  simp [Matrix.fromBlocks_multiply]

private lemma good_diag {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] {U : Matrix b b K} (hU : Good U) :
    Good (fromBlocks (1 : Matrix a a K) 0 0 U) := by
  obtain ⟨h1, U', h2, h3⟩ := hU
  refine ⟨small_blocks small_one small_zero small_zero h1, fromBlocks 1 0 0 U',
    small_blocks small_one small_zero small_zero h2, ?_⟩
  simp [Matrix.fromBlocks_multiply, h3]

private lemma smith_diag {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (c : a → K) {D : Matrix b b K} (hD : Smith D) :
    Smith (fromBlocks (diagonal c) 0 0 D) := by
  obtain ⟨U, V, d, hU, hV, rfl⟩ := hD
  refine ⟨fromBlocks 1 0 0 U, fromBlocks 1 0 0 V, Sum.elim c d, good_diag hU, good_diag hV, ?_⟩
  rw [← Matrix.fromBlocks_diagonal]
  simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add]

private lemma smith_step [IsUltrametricDist K] {b : Type*} [Fintype b] [DecidableEq b]
    (ih : ∀ D : Matrix b b K, Smith D) (N : Matrix (Unit ⊕ b) (Unit ⊕ b) K)
    (hN : ∀ i j, ‖N i j‖ ≤ ‖N (Sum.inl ()) (Sum.inl ())‖) : Smith N := by
  set x := N (Sum.inl ()) (Sum.inl ()) with hx
  by_cases h0 : x = 0
  · refine ⟨1, 1, 0, good_one, good_one, ?_⟩
    ext i j
    have := hN i j
    rw [h0, norm_zero] at this
    simp [norm_le_zero_iff.mp this, Matrix.diagonal_apply]
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr h0
  let C : Matrix b Unit K := Matrix.of fun i _ => N (Sum.inr i) (Sum.inl ()) / x
  let B : Matrix Unit b K := Matrix.of fun _ j => N (Sum.inl ()) (Sum.inr j) / x
  let D : Matrix b b K := Matrix.of fun i j => N (Sum.inr i) (Sum.inr j) -
    N (Sum.inr i) (Sum.inl ()) * N (Sum.inl ()) (Sum.inr j) / x
  have hC : Small C := fun i j => by
    simp only [C, Matrix.of_apply, norm_div]
    exact (div_le_one hpos).mpr (hN _ _)
  have hB : Small B := fun i j => by
    simp only [B, Matrix.of_apply, norm_div]
    exact (div_le_one hpos).mpr (hN _ _)
  have key : N = fromBlocks 1 0 C 1 * fromBlocks (diagonal fun _ => x) 0 0 D
      * fromBlocks 1 B 0 1 := by
    simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
    ext (i | i) (j | j)
    · simp [hx]
    · simp [B, Matrix.mul_apply]
      field_simp
    · simp [C, Matrix.mul_apply, h0]
    · simp [B, C, D, Matrix.mul_apply]
      field_simp
      ring
  rw [key]
  exact smith_mul (good_lower hC) (smith_diag _ (ih D)) (good_upper hB)

private lemma smith_fin [IsUltrametricDist K] (n : ℕ) :
    ∀ M : Matrix (Fin n) (Fin n) K, Smith M := by
  induction n with
  | zero => exact fun M => ⟨1, 1, 0, good_one, good_one, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro M
    obtain ⟨⟨p, q⟩, hpq⟩ := Finite.exists_max (fun x : Fin (n + 1) × Fin (n + 1) => ‖M x.1 x.2‖)
    let e : Fin (n + 1) ≃ Unit ⊕ Fin n := Fintype.equivOfCardEq (by simp [add_comm])
    let f : Fin (n + 1) ≃ Unit ⊕ Fin n := e.trans (Equiv.swap (e p) (Sum.inl ()))
    let g : Fin (n + 1) ≃ Unit ⊕ Fin n := e.trans (Equiv.swap (e q) (Sum.inl ()))
    have hf : f.symm (Sum.inl ()) = p := by simp [f]
    have hg : g.symm (Sum.inl ()) = q := by simp [g]
    have h := smith_step ih (M.submatrix f.symm g.symm) (fun i j => by
      simp only [Matrix.submatrix_apply, hf, hg]
      exact hpq (_, _))
    have h2 := smith_submatrix h f g
    simpa using h2

private lemma good_gl {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : Good A) :
    ∃ U : GL (Fin n) K, (↑U : Matrix (Fin n) (Fin n) K) = A ∧
      Small (↑U⁻¹ : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨_, B, h2, h3⟩ := hA
  exact ⟨⟨A, B, h3, mul_eq_one_comm.mp h3⟩, rfl, h2⟩

end

end UpperTheory.Reformulated.B.StringRepresentationDecomposition

theorem UpperTheory.Reformulated.B.StringRepresentationDecomposition.smith_gen.{u_1} :
    ∀ {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K] {n : ℕ} (P : GL (Fin n) K),
      ∃ (U : GL (Fin n) K) (V : GL (Fin n) K) (d : Fin n → K),
        (∀ (i j : Fin n), ‖(↑U : Matrix (Fin n) (Fin n) K) i j‖ ≤ (1 : ℝ)) ∧
          (∀ (i j : Fin n), ‖(↑U⁻¹ : Matrix (Fin n) (Fin n) K) i j‖ ≤ (1 : ℝ)) ∧
            (∀ (i j : Fin n), ‖(↑V : Matrix (Fin n) (Fin n) K) i j‖ ≤ (1 : ℝ)) ∧
              (∀ (i j : Fin n), ‖(↑V⁻¹ : Matrix (Fin n) (Fin n) K) i j‖ ≤ (1 : ℝ)) ∧
                (∀ (i : Fin n), d i ≠ (0 : K)) ∧
                  (↑P : Matrix (Fin n) (Fin n) K) =
                    (↑U : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d * (↑V : Matrix (Fin n) (Fin n) K) := by
  intro K _ _ n P
  obtain ⟨A, B, d, hA, hB, h⟩ := smith_fin n (↑P : Matrix (Fin n) (Fin n) K)
  obtain ⟨U, rfl, hU⟩ := good_gl hA
  obtain ⟨V, rfl, hV⟩ := good_gl hB
  refine ⟨U, V, d, hA.1, hU, hB.1, hV, ?_, h⟩
  have hdet : (↑P : Matrix (Fin n) (Fin n) K).det ≠ 0 := P.det_ne_zero
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  intro i
  exact Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul (left_ne_zero_of_mul hdet)) i
    (Finset.mem_univ i)
end

section

noncomputable def UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight.{u_1} :
    {E : Type u_1} → [inst : NormedField E] → {n : ℕ} → GL (Fin n) E → ℝ :=
    fun {E : Type u_1} [NormedField E] {n : ℕ} (g : GL (Fin n) E) ↦
      Max.max (1 : ℝ)
        (↑(Finset.univ.sup fun (p : Fin n × Fin n) ↦
              Max.max ‖(↑g : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊ ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊) :
          ℝ)

theorem UpperTheory.Reformulated.B.LocalHeightDeterminant.norm_det_le_pow.{u_1} :
    ∀ {R : Type u_1} [inst : NormedField R] [IsUltrametricDist R] {n : ℕ} (g : GL (Fin n) R),
      ‖(↑g : Matrix (Fin n) (Fin n) R).det‖ ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g ^ n := by
  intro R _ _ n g
  have h1 : (1 : ℝ) ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g := le_max_left _ _
  have h0 : (0 : ℝ) ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g := zero_le_one.trans h1
  have hent : ∀ i j, ‖(↑g : Matrix (Fin n) (Fin n) R) i j‖ ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g := by
    intro i j
    refine le_trans ?_ (le_max_right _ _)
    rw [← coe_nnnorm, NNReal.coe_le_coe]
    exact (le_max_left _ _).trans (Finset.le_sup (f := fun (p : Fin n × Fin n) ↦
      Max.max ‖(↑g : Matrix (Fin n) (Fin n) R) p.1 p.2‖₊
        ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) R) p.1 p.2‖₊) (Finset.mem_univ (i, j)))
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg h0 n) ?_
  intro σ _
  have hs : ‖Equiv.Perm.sign σ • ∏ i, (↑g : Matrix (Fin n) (Fin n) R) (σ i) i‖
      = ‖∏ i, (↑g : Matrix (Fin n) (Fin n) R) (σ i) i‖ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, norm_prod]
  calc ∏ i, ‖(↑g : Matrix (Fin n) (Fin n) R) (σ i) i‖
      ≤ ∏ _i : Fin n, UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g :=
        Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hent _ _)
    _ = UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g ^ n := by simp
end

section

open IsLocalRing

theorem UpperTheory.digit_expansion_lattice :
    ∀ {O Ω : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [NormedField Ω] [IsUltrametricDist Ω] [Algebra O Ω]
        (hO : ∀ a : O, ‖algebraMap O Ω a‖ ≤ 1) (ϖ : O) (hϖ : Irreducible ϖ) (hlt : ‖algebraMap O Ω ϖ‖ < 1)
        (S : Submodule O Ω) (hS : ∀ s ∈ S, ‖s‖ ≤ 1) (E : Finset Ω) (hE : ∀ e ∈ E, e ∈ S)
        (hdig : ∀ s ∈ S, ∃ e ∈ E, ∃ s' ∈ S, s = e + ϖ • s'),
        Module.Finite O S := by
  intro O Ω _ _ _ _ _ _ _ hO ϖ hϖ hlt S hS E hE hdig
  classical
  have hI : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hhaus : IsHausdorff (maximalIdeal O) S := by
    refine ⟨fun x hx => ?_⟩
    have hb : ∀ n : ℕ, ‖(x : Ω)‖ ≤ ‖algebraMap O Ω ϖ‖ ^ n := by
      intro n
      have h := hx n
      rw [SModEq.zero, hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at h
      obtain ⟨t, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
      have : (((ϖ ^ n) • t : S) : Ω) = algebraMap O Ω ϖ ^ n * (t : Ω) := by
        simp [Algebra.smul_def]
      rw [this, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hS _ t.2)
    have hlim : Filter.Tendsto (fun n : ℕ => ‖algebraMap O Ω ϖ‖ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt
    have h0 : ‖(x : Ω)‖ ≤ 0 := ge_of_tendsto' hlim hb
    exact Subtype.ext (norm_le_zero_iff.1 h0)
  have hpre : IsPrecomplete (maximalIdeal O) (E → O) := by
    refine ⟨fun g hg => ?_⟩
    have hcoord : ∀ {m : ℕ} (x : E → O),
        x ∈ (maximalIdeal O ^ m • ⊤ : Submodule O (E → O)) → ∀ i, x i ∈ maximalIdeal O ^ m := by
      intro m x hx i
      have h := Submodule.mem_map_of_mem (f := (LinearMap.proj i : (E → O) →ₗ[O] O)) hx
      rw [Submodule.map_smul''] at h
      have h2 : x i ∈ (maximalIdeal O ^ m • ⊤ : Submodule O O) :=
        Submodule.smul_mono le_rfl le_top h
      simpa using h2
    have hc : ∀ i : E, ∃ L : O, ∀ n, g n i ≡ L [SMOD (maximalIdeal O ^ n • ⊤ : Submodule O O)] := by
      intro i
      refine IsPrecomplete.prec (I := maximalIdeal O) (M := O) inferInstance (f := fun n => g n i) ?_
      intro m n hmn
      have h := (SModEq.sub_mem.1 (hg hmn))
      refine SModEq.sub_mem.2 ?_
      have h2 := hcoord _ h i
      simpa using h2
    choose L hL using hc
    refine ⟨L, fun n => ?_⟩
    refine SModEq.sub_mem.2 ?_
    have hsum : g n - L = ∑ i : E, (g n i - L i) • (Pi.single i 1 : E → O) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
    have h := SModEq.sub_mem.1 (hL i n)
    simpa using h
  let v : E → S := fun e => ⟨e, hE e e.2⟩
  let f : (E → O) →ₗ[O] S := Fintype.linearCombination O v
  have hsurj : Function.Surjective f := by
    refine surjective_of_mkQ_comp_surjective (I := maximalIdeal O) ?_
    intro y
    obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨e, he, s', hs', hs⟩ := hdig s s.2
    refine ⟨Pi.single ⟨e, he⟩ 1, ?_⟩
    have hf : f (Pi.single ⟨e, he⟩ 1) = ⟨e, hE e he⟩ := by
      simp [f, v, Fintype.linearCombination_apply_single]
    simp only [LinearMap.comp_apply, hf]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hI,
      Submodule.ideal_span_singleton_smul]
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨-⟨s', hs'⟩, trivial, ?_⟩
    apply Subtype.ext
    simp [hs]
  exact Module.Finite.of_surjective f hsurj
end

section

theorem UpperTheory.residue_hom_norm :
    ∀ {O R Ω : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [NormedField Ω]
        [IsUltrametricDist Ω] [Algebra O Ω]
        (hres : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ IsLocalRing.maximalIdeal R)
        (hO : ∀ a : O, ‖algebraMap O Ω a‖ ≤ 1) (hint : ∀ x : Ω, ‖x‖ ≤ 1 → IsIntegral O x)
        (y : R →ₐ[O] Ω),
        (∀ a, ‖y a‖ ≤ 1) ∧ ∀ a ∈ IsLocalRing.maximalIdeal R, ‖y a‖ < 1 := by
  intro O R Ω _ _ _ _ _ _ _ hres hO hint y
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal R, ‖y a‖ < 1 := by
    intro m hmem
    by_contra hge
    have hge' : 1 ≤ ‖y m‖ := not_lt.mp hge
    have hne : y m ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hge'
      linarith
    have hu : ‖(y m)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hge'
    obtain ⟨p, hp, hev⟩ := hint _ hu
    have hrev : Polynomial.eval₂ (algebraMap O Ω) (y m) p.reverse = 0 := by
      haveI : Invertible (y m)⁻¹ := invertibleOfNonzero (inv_ne_zero hne)
      have h := Polynomial.eval₂_reverse_mul_pow (algebraMap O Ω) (y m)⁻¹ p
      rw [invOf_eq_inv, inv_inv, hev] at h
      exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (inv_ne_zero hne))
    have hq : y (Polynomial.aeval m p.reverse) = 0 := by
      rw [Polynomial.aeval_algHom_apply y m p.reverse |>.symm]
      simpa [Polynomial.aeval_def] using hrev
    have hdvd : m ∣ Polynomial.aeval m p.reverse - 1 := by
      have h := Polynomial.sub_dvd_eval_sub m 0 (p.reverse.map (algebraMap O R))
      have h0 : (p.reverse.map (algebraMap O R)).eval 0 = 1 := by
        rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
          Polynomial.coeff_zero_reverse, hp.leadingCoeff, map_one]
      rw [h0, sub_zero, Polynomial.eval_map_algebraMap] at h
      exact h
    have hunit : IsUnit (Polynomial.aeval m p.reverse : R) := by
      by_contra hnu
      have h1 : (Polynomial.aeval m p.reverse : R) ∈ IsLocalRing.maximalIdeal R :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have h2 : Polynomial.aeval m p.reverse - 1 ∈ IsLocalRing.maximalIdeal R :=
        Ideal.mem_of_dvd _ hdvd hmem
      have h3 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
        have := Ideal.sub_mem _ h1 h2
        simpa using this
      exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3
    have := hunit.map y
    rw [hq] at this
    exact not_isUnit_zero this
  refine ⟨fun x => ?_, hm⟩
  obtain ⟨a, ha⟩ := hres x
  have hx : y x = algebraMap O Ω a + y (x - algebraMap O R a) := by
    rw [map_sub, AlgHom.commutes]
    ring
  rw [hx]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (hO a) (hm _ ha).le)
end

section

noncomputable def UpperTheory.Reformulated.B.Qi22.wsum.{v} :
    {ι : Type v} → (ι → ℤ) → (ι →₀ ℕ) → ℤ :=
    fun {ι : Type v} (w : ι → ℤ) (n : ι →₀ ℕ) ↦ n.sum fun (x : ι) (k : ℕ) ↦ (↑k : ℤ) * w x

noncomputable def UpperTheory.Reformulated.B.Qi22.HomW.{u, v} :
    {K : Type u} → [NormedField K] → {ι : Type v} → (ι → ℤ) → ℤ → MvPowerSeries ι K → Prop :=
    fun {K : Type u} [NormedField K] {ι : Type v} (w : ι → ℤ) (c : ℤ) (f : MvPowerSeries ι K) ↦
      ∀ (n : ι →₀ ℕ), (MvPowerSeries.coeff n : MvPowerSeries ι K → K) f ≠ (0 : K) → UpperTheory.Reformulated.B.Qi22.wsum w n = c

private theorem UpperTheory.Reformulated.B.Qi22.wsum_add {ι : Type*} (w : ι → ℤ) (a b : ι →₀ ℕ) :
    UpperTheory.Reformulated.B.Qi22.wsum w (a + b) = UpperTheory.Reformulated.B.Qi22.wsum w a + UpperTheory.Reformulated.B.Qi22.wsum w b := by
  unfold UpperTheory.Reformulated.B.Qi22.wsum
  apply Finsupp.sum_add_index'
  · intro x; simp
  · intro x p q; push_cast; ring

private theorem UpperTheory.Reformulated.B.Qi22.homW_one {K : Type*} [NormedField K] {ι : Type*} (w : ι → ℤ) :
    UpperTheory.Reformulated.B.Qi22.HomW w 0 (1 : MvPowerSeries ι K) := by
  classical
  intro n hn
  have h0 : n = 0 := by
    by_contra h
    exact hn (by rw [MvPowerSeries.coeff_one, if_neg h])
  subst h0
  simp [UpperTheory.Reformulated.B.Qi22.wsum]

private theorem UpperTheory.Reformulated.B.Qi22.homW_mul {K : Type*} [NormedField K] {ι : Type*} {w : ι → ℤ}
    {c d : ℤ} {f g : MvPowerSeries ι K} (hf : UpperTheory.Reformulated.B.Qi22.HomW w c f)
    (hg : UpperTheory.Reformulated.B.Qi22.HomW w d g) : UpperTheory.Reformulated.B.Qi22.HomW w (c + d) (f * g) := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul] at hn
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hsum : p.1 + p.2 = n := by simpa using hp
  rw [← hsum, UpperTheory.Reformulated.B.Qi22.wsum_add, hf p.1 (left_ne_zero_of_mul hne),
    hg p.2 (right_ne_zero_of_mul hne)]

theorem UpperTheory.Reformulated.B.Qi22.homW_prod.{u, v, w} :
    ∀ {K : Type u} [inst : NormedField K] {ι : Type v} {w : ι → ℤ} {α : Type w} (s : Finset α) (c : α → ℤ)
      (F : α → MvPowerSeries ι K),
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qi22.HomW w (c i) (F i)) → UpperTheory.Reformulated.B.Qi22.HomW w (∑ i ∈ s, c i) (∏ i ∈ s, F i) := by
  intro K inst ι w α s c F
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using UpperTheory.Reformulated.B.Qi22.homW_one (K := K) w
  | insert a s ha ih =>
    intro h
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact UpperTheory.Reformulated.B.Qi22.homW_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end
