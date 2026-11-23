module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Complex
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
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.WuDec

section Tens

variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
  {Vπ : Type} [NormedAddCommGroup Vπ] [InnerProductSpace ℂ Vπ] {tens : (∀ v, V v) → Vπ}

theorem norm_tens (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (x : ∀ v, V v) :
    ‖tens x‖ = ∏ v, ‖x v‖ := by
  have h := hi x x
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖tens x‖ ^ 2 = (∏ v, ‖x v‖) ^ 2 := by
    rw [← Finset.prod_pow]
    exact_mod_cast h
  rw [← Real.sqrt_sq (norm_nonneg (tens x)), h2,
    Real.sqrt_sq (Finset.prod_nonneg fun v _ => norm_nonneg (x v))]

theorem norm_sub_tens_sq (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (x y : ∀ v, V v) :
    ‖tens x - tens y‖ ^ 2 = RCLike.re ((∏ v, ⟪x v, x v⟫_ℂ) - (∏ v, ⟪x v, y v⟫_ℂ) - (∏ v, ⟪y v, x v⟫_ℂ) +
      (∏ v, ⟪y v, y v⟫_ℂ)) := by
  have e := inner_self_eq_norm_sq (𝕜 := ℂ) (tens x - tens y)
  rw [← e, inner_sub_left, inner_sub_right, inner_sub_right, hi, hi, hi, hi]
  congr 1
  ring

theorem continuous_tens [∀ v, FiniteDimensional ℂ (V v)] (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) :
    Continuous tens := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have p : ∀ v, Continuous fun y : (∀ v, V v) => y v := fun v => _root_.continuous_apply v
  have hF : Continuous fun y : (∀ v, V v) => RCLike.re ((∏ v, ⟪y v, y v⟫_ℂ) - (∏ v, ⟪y v, x v⟫_ℂ) -
      (∏ v, ⟪x v, y v⟫_ℂ) + (∏ v, ⟪x v, x v⟫_ℂ)) := by
    refine RCLike.continuous_re.comp
      (Continuous.add (Continuous.sub (Continuous.sub ?_ ?_) ?_) continuous_const)
    · exact continuous_finsetProd _ fun v _ => (p v).inner (p v)
    · exact continuous_finsetProd _ fun v _ => (p v).inner continuous_const
    · exact continuous_finsetProd _ fun v _ => continuous_const.inner (p v)
  have h2 : Filter.Tendsto (fun y => ‖tens y - tens x‖ ^ 2) (nhds x) (nhds 0) := by
    have e : (fun y => ‖tens y - tens x‖ ^ 2) = fun y : (∀ v, V v) =>
        RCLike.re ((∏ v, ⟪y v, y v⟫_ℂ) - (∏ v, ⟪y v, x v⟫_ℂ) - (∏ v, ⟪x v, y v⟫_ℂ) +
          (∏ v, ⟪x v, x v⟫_ℂ)) :=
      funext fun y => norm_sub_tens_sq hi y x
    rw [e]
    convert hF.tendsto x using 2
    simp
  have h3 := h2.sqrt
  simp only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at h3
  exact h3

theorem tens_smul (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (c : ι → ℂ) (x : ∀ v, V v) :
    tens (fun v => c v • x v) = (∏ v, c v) • tens x := by
  have key : ⟪tens (fun v => c v • x v) - (∏ v, c v) • tens x,
      tens (fun v => c v • x v) - (∏ v, c v) • tens x⟫_ℂ = 0 := by
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hi,
      Finset.prod_mul_distrib, map_prod]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp key)

theorem inner_tens_update [DecidableEq ι] (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (ξ : ∀ v, V v)
    (v : ι) (a b : V v) :
    ⟪tens (Function.update ξ v a), tens (Function.update ξ v b)⟫_ℂ =
      ⟪a, b⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ := by
  rw [hi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw), Function.update_of_ne (Finset.ne_of_mem_erase hw)]

theorem tens_update_inj [DecidableEq ι] (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (ξ : ∀ v, V v)
    (v : ι) (hne : ∀ w, w ≠ v → ξ w ≠ 0) (a b : V v)
    (h : tens (Function.update ξ v a) = tens (Function.update ξ v b)) : a = b := by
  have hP : ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro w hw
    exact inner_self_ne_zero.mpr (hne w (Finset.ne_of_mem_erase hw))
  have e : ∀ p q : V v, ⟪tens (Function.update ξ v p), tens (Function.update ξ v q)⟫_ℂ =
      ⟪p, q⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ :=
    fun p q => inner_tens_update hi ξ v p q
  have h0 : ⟪tens (Function.update ξ v a) - tens (Function.update ξ v b),
      tens (Function.update ξ v a) - tens (Function.update ξ v b)⟫_ℂ = 0 := by
    rw [h, sub_self, inner_zero_left]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, e, e, e, e] at h0
  have key : ⟪a - b, a - b⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    linear_combination h0
  exact sub_eq_zero.mp (inner_self_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hP))

end Tens

theorem integrable_and_integral_pi_apply :
  ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ v, MeasurableSpace (X v)] (μ : ∀ v, Measure (X v))
    [∀ v, SigmaFinite (μ v)] (V : ι → Type) [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
    [∀ v, FiniteDimensional ℂ (V v)] (Vπ : Type) [NormedAddCommGroup Vπ] [InnerProductSpace ℂ Vπ]
    [FiniteDimensional ℂ Vπ] (tens : (∀ v, V v) → Vπ),
    (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) → Submodule.span ℂ (Set.range tens) = ⊤ →
    ∀ G : ∀ v, X v → V v, (∀ v, Integrable (G v) (μ v)) →
      Integrable (fun y : ∀ v, X v => tens (fun v => G v (y v))) (Measure.pi μ) ∧
        ∫ y, tens (fun v => G v (y v)) ∂(Measure.pi μ) = tens (fun v => ∫ t, G v t ∂(μ v)) := by
  intro ι _ X _ μ _ V _ _ _ Vπ _ _ _ tens hi hspan G hG
  have hcoord : ∀ w : Vπ, Integrable (fun y : ∀ v, X v => ⟪w, tens fun v => G v (y v)⟫_ℂ)
      (Measure.pi μ) := by
    intro w
    have hw : w ∈ Submodule.span ℂ (Set.range tens) := by rw [hspan]; exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      simp_rw [hi]
      exact Integrable.fintype_prod_dep (fun v => (hG v).const_inner (z v))
    | zero =>
      simp only [inner_zero_left]
      exact integrable_zero _ _ _
    | add x y _ _ hx hy =>
      simp only [inner_add_left]
      exact hx.add hy
    | smul a x _ hx =>
      simp only [inner_smul_left]
      exact hx.const_mul _
  have hFint : Integrable (fun y : ∀ v, X v => tens fun v => G v (y v)) (Measure.pi μ) := by
    have e : (fun y : ∀ v, X v => tens fun v => G v (y v)) = fun y =>
        ∑ i, ⟪stdOrthonormalBasis ℂ Vπ i, tens fun v => G v (y v)⟫_ℂ • stdOrthonormalBasis ℂ Vπ i :=
      funext fun y => ((stdOrthonormalBasis ℂ Vπ).sum_repr' _).symm
    rw [e]
    exact MeasureTheory.integrable_finsetSum _ fun i _ => (hcoord _).smul_const _
  refine ⟨hFint, ?_⟩
  refine ext_inner_left ℂ fun w => ?_
  have hw : w ∈ Submodule.span ℂ (Set.range tens) := by rw [hspan]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    rw [← integral_inner hFint]
    simp_rw [hi]
    refine (integral_fintype_prod_eq_prod (fun v t => ⟪z v, G v t⟫_ℂ)).trans ?_
    exact Finset.prod_congr rfl fun v _ => integral_inner (hG v) (z v)
  | zero => simp only [inner_zero_left]
  | add x y _ _ hx hy => rw [inner_add_left, inner_add_left, hx, hy]
  | smul a x _ hx => rw [inner_smul_left, inner_smul_left, hx]

end Formalism.L2.SG.Pf.WuDec
end
end

section

noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

variable {m : ℕ}

def IsUB (blk : Fin m → ℕ) (C : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  (∀ i, C i i = 1) ∧ ∀ i j, C i j ≠ 0 → i ≤ j ∧ blk i = blk j

theorem IsUB.zero_of_lt {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) {i j : Fin m} (hij : j < i) :
    C i j = 0 := by
  by_contra hne
  exact absurd hij (not_lt.mpr (h.2 i j hne).1)

theorem IsUB.zero_of_blk {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) {i j : Fin m}
    (hij : blk i ≠ blk j) : C i j = 0 := by
  by_contra hne
  exact hij (h.2 i j hne).2

theorem IsUB.det_eq_one {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) : C.det = 1 := by
  have hup : C.BlockTriangular id := by
    intro i j hij
    exact h.zero_of_lt hij
  rw [Matrix.det_of_upperTriangular hup]
  exact Finset.prod_eq_one fun i _ => h.1 i

theorem IsUB.inv {blk : Fin m → ℕ} {C : Matrix (Fin m) (Fin m) ℂ} (h : IsUB blk C) : IsUB blk C⁻¹ := by
  have hup : C.BlockTriangular id := by
    intro i j hij
    exact h.zero_of_lt hij
  have hb1 : C.BlockTriangular blk := by
    intro i j hij
    exact h.zero_of_blk hij.ne'
  have hb2 : C.BlockTriangular (fun i => OrderDual.toDual (blk i)) := by
    intro i j hij
    exact h.zero_of_blk (OrderDual.toDual_lt_toDual.mp hij).ne
  have hdet : IsUnit C.det := by
    rw [h.det_eq_one]
    exact isUnit_one
  letI : Invertible C := C.invertibleOfIsUnitDet hdet
  have iup := Matrix.blockTriangular_inv_of_blockTriangular hup
  have ib1 := Matrix.blockTriangular_inv_of_blockTriangular hb1
  have ib2 := Matrix.blockTriangular_inv_of_blockTriangular hb2
  refine ⟨fun i => ?_, fun i j hij => ⟨?_, ?_⟩⟩
  · have h1 : (C * C⁻¹) i i = 1 := by
      rw [Matrix.mul_nonsing_inv _ hdet, one_apply_eq]
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · rwa [h.1, one_mul] at h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · rw [h.zero_of_lt hlt, zero_mul]
      · rw [iup hlt, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · by_contra hlt
    exact hij (iup (not_le.mp hlt))
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hij (ib2 (OrderDual.toDual_lt_toDual.mpr hlt))
    · exact hij (ib1 hlt)

section Mono

variable (π : Fin m → Fin m) (hπ : ∀ a, π (π a) = a) (Z : Matrix (Fin m) (Fin m) ℂ)
  (hZ : ∀ c b, Z c b ≠ 0 ↔ c = π b)
include hπ hZ

theorem Z_ne' (i : Fin m) : Z i (π i) ≠ 0 := (hZ i (π i)).mpr (hπ i).symm

def Zi : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun b c => if b = π c then (Z c b)⁻¹ else 0

theorem Z_mul_Zi : Z * Zi π Z = 1 := by
  refine Matrix.ext fun i k => ?_
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Zi, of_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl]
    exact mul_inv_cancel₀ (Z_ne' π hπ Z hZ i)
  · rw [if_neg hik]
    have h0 : Z i (π k) = 0 := by
      by_contra hne
      have h1 := (hZ i (π k)).mp hne
      rw [hπ] at h1
      exact hik h1
    rw [h0, zero_mul]

theorem Z_inv_eq : Z⁻¹ = Zi π Z := Matrix.inv_eq_right_inv (Z_mul_Zi π hπ Z hZ)

theorem isUnit_Z : IsUnit Z.det := Matrix.isUnit_det_of_right_inverse (Z_mul_Zi π hπ Z hZ)

theorem conj_apply (X : Matrix (Fin m) (Fin m) ℂ) (j i : Fin m) :
    (Z * X * Z⁻¹) j i = Z j (π j) * X (π j) (π i) * (Z i (π i))⁻¹ := by
  rw [Z_inv_eq π hπ Z hZ]
  simp only [Matrix.mul_apply, Zi, of_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  rw [Finset.sum_eq_single (π j)]
  · intro l _ hl
    have h0 : Z j l = 0 := by
      by_contra hne
      apply hl
      rw [(hZ j l).mp hne, hπ]
    rw [h0, zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ _) hj

end Mono

section Pair

variable {blk : Fin m → ℕ} (π : Fin m → Fin m) (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a)
  (hanti : ∀ a b, blk a = blk b → a < b → π b < π a) (Z : Matrix (Fin m) (Fin m) ℂ)
  (hZ : ∀ c b, Z c b ≠ 0 ↔ c = π b)
include hπ hblk hanti hZ

theorem isUB_A {C : Matrix (Fin m) (Fin m) ℂ} (hC : IsUB blk C) : IsUB blk (Z * C⁻¹ * Z⁻¹)ᴴ := by
  have hD := hC.inv
  have hM : ∀ j i, (Z * C⁻¹ * Z⁻¹) j i = Z j (π j) * C⁻¹ (π j) (π i) * (Z i (π i))⁻¹ :=
    fun j i => conj_apply π hπ Z hZ _ j i
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [conjTranspose_apply, hM, hD.1, mul_one, mul_inv_cancel₀ (Z_ne' π hπ Z hZ i),
      star_one]
  · rw [conjTranspose_apply, hM] at hij
    have h1 : C⁻¹ (π j) (π i) ≠ 0 := by
      intro h0
      apply hij
      rw [h0]
      simp
    obtain ⟨hle, hb⟩ := hD.2 _ _ h1
    refine ⟨?_, by simpa [hblk] using hb.symm⟩
    rcases hle.lt_or_eq with hlt | heq
    · have h2 := hanti _ _ hb hlt
      rw [hπ, hπ] at h2
      exact h2.le
    · have h2 := congrArg π heq
      rw [hπ, hπ] at h2
      exact h2.symm.le

theorem A_Z_C {C : Matrix (Fin m) (Fin m) ℂ} (hC : IsUB blk C) : (Z * C⁻¹ * Z⁻¹)ᴴᴴ * Z * C = Z := by
  rw [conjTranspose_conjTranspose]
  have hZu := isUnit_Z π hπ Z hZ
  have hCu : IsUnit C.det := by
    rw [hC.det_eq_one]
    exact isUnit_one
  rw [mul_assoc (Z * C⁻¹) Z⁻¹ Z, Matrix.nonsing_inv_mul _ hZu, mul_one, mul_assoc,
    Matrix.nonsing_inv_mul _ hCu, mul_one]

end Pair

theorem gram_last {blk : Fin (m + 1) → ℕ} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ} (hA : IsUB blk A)
    (Γ : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hΓ : ∀ i j, (i ≠ Fin.last m ∨ j ≠ Fin.last m) → Γ i j = 0) :
    Aᴴ * Γ * A = Γ := by
  have hrow : ∀ j, A (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
    intro j
    by_cases hj : j = Fin.last m
    · rw [if_pos hj, hj]
      exact hA.1 _
    · rw [if_neg hj]
      exact hA.zero_of_lt (lt_of_le_of_ne (Fin.le_last j) hj)
  ext i j
  simp only [Matrix.mul_apply, conjTranspose_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [Finset.sum_eq_single (Fin.last m)]
    · rw [hrow i, hrow j]
      by_cases hi : i = Fin.last m
      · by_cases hj : j = Fin.last m
        · subst hi
          subst hj
          simp
        · rw [if_neg hj, hΓ i j (Or.inr hj)]
          simp
      · rw [if_neg hi, hΓ i j (Or.inl hi)]
        simp
    · intro k _ hk
      rw [hΓ k (Fin.last m) (Or.inl hk), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro l _ hl
    rw [Finset.sum_eq_zero (fun k _ => by rw [hΓ k l (Or.inr hl), mul_zero]), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.PiMeasureScaling

theorem sf_smul (c : ℝ≥0∞) (hc : c ≠ ⊤) : SigmaFinite (c • (volume : Measure ℂ)) := by
  lift c to NNReal using hc
  first
  | exact (inferInstance : SigmaFinite (c • (volume : Measure ℂ)))
  | (rw [← ENNReal.smul_def]; infer_instance)

theorem pi_smul_vol {ι : Type*} [Fintype ι] (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • (volume : Measure ℂ)) = (∏ i, c i) • (volume : Measure (ι → ℂ)) := by
  haveI : ∀ i, SigmaFinite (c i • (volume : Measure ℂ)) := fun i => sf_smul (c i) (hc i)
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, volume_pi_pi, ← Finset.prod_mul_distrib]
  simp only [Measure.smul_apply, smul_eq_mul]

theorem map_scale (s : ℂ) (hs : s ≠ 0) :
    (volume : Measure ℂ).map (fun z => s * z) = ENNReal.ofReal (Complex.normSq s)⁻¹ • volume := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ s) = Complex.normSq s := by
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have hpos : 0 < Complex.normSq s := Complex.normSq_pos.mpr hs
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := LinearMap.mulLeft ℝ s) (by rw [hdet]; exact hpos.ne')
  rw [hdet, abs_of_pos (inv_pos.mpr hpos)] at h
  exact h

theorem reindex_mp {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    MeasurePreserving (fun (y : κ → ℂ) (i : ι) => y (e i)) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : ι => ℂ) e.symm
  have hf : (⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => ℂ) e.symm)) =
      fun (y : κ → ℂ) (i : ι) => y (e i) := by
    funext y i
    have h1 := MeasurableEquiv.piCongrLeft_apply_apply e.symm (β := fun _ : ι => ℂ) y (e i)
    simpa using h1
  rw [hf] at h
  exact h

theorem pi_reindex_scale {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (a : ℝ≥0∞) (ha : a ≠ ⊤) (s : ι → ℂ) (hs : ∀ i, s i ≠ 0) :
    (Measure.pi (fun _ : κ => a • (volume : Measure ℂ))).map (fun y i => s i * y (e i)) =
      (∏ i, a * ENNReal.ofReal (Complex.normSq (s i))⁻¹) • (volume : Measure (ι → ℂ)) := by
  classical
  have hk : Measure.pi (fun _ : κ => a • (volume : Measure ℂ)) =
      (∏ _k : κ, a) • (volume : Measure (κ → ℂ)) := pi_smul_vol (fun _ => a) (fun _ => ha)
  have hsc : (volume : Measure (ι → ℂ)).map (fun x i => s i * x i) =
      (∏ i, ENNReal.ofReal (Complex.normSq (s i))⁻¹) • (volume : Measure (ι → ℂ)) := by
    haveI : ∀ i, SigmaFinite (Measure.map (fun x => s i * x) (volume : Measure ℂ)) := fun i => by
      rw [map_scale _ (hs i)]
      exact sf_smul _ ENNReal.ofReal_ne_top
    rw [volume_pi, Measure.pi_map_pi (fun i => (measurable_const_mul (s i)).aemeasurable)]
    simp_rw [map_scale _ (hs _)]
    rw [pi_smul_vol _ (fun i => ENNReal.ofReal_ne_top), volume_pi]
  have hscale : Measurable (fun (x : ι → ℂ) (i : ι) => s i * x i) :=
    Measurable.of_eval fun i => by fun_prop
  have htotal : AEMeasurable (fun (y : κ → ℂ) (i : ι) => s i * y (e i)) volume := by
    exact (hscale.comp (reindex_mp e).measurable).aemeasurable
  have hcomp : (fun (y : κ → ℂ) (i : ι) => s i * y (e i)) =
      (fun (x : ι → ℂ) i => s i * x i) ∘ (fun (y : κ → ℂ) (i : ι) => y (e i)) := rfl
  rw [hk, Measure.map_smul _ htotal, hcomp,
    ← Measure.map_map (Measurable.of_eval fun i => (measurable_pi_apply i).const_mul (s i))
      (reindex_mp e).measurable, (reindex_mp e).map_eq, hsc, smul_smul]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Finset.card_univ,
    Finset.card_univ, Fintype.card_congr e]

end Formalism.L2.SG.PiMeasureScaling

end
end
