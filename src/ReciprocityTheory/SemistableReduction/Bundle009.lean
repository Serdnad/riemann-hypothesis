module

public import ReciprocityTheory.SemistableReduction.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section

section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix InnerProductSpace

theorem exists_unitary_mul_upper {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) :
    ∃ k b : Matrix (Fin n) (Fin n) ℂ, k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ b.BlockTriangular id ∧
      x = k * b ∧ ∀ j, ‖b j j‖ ^ 2 ≤ colNormSq x j := by
  classical
  let std := EuclideanSpace.basisFun (Fin n) ℂ
  let f : Fin n → EuclideanSpace ℂ (Fin n) := fun j => (EuclideanSpace.equiv (Fin n) ℂ).symm (fun i => x i j)
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by simp
  let e := gramSchmidtOrthonormalBasis hdim f
  have hstd : std.toBasis.toMatrix f = x := by
    ext i j
    simp [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, f, std]
  have hnorm : ∀ j, ‖f j‖ ^ 2 = colNormSq x j := by
    intro j
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [colNormSq, f]
  refine ⟨std.toBasis.toMatrix e.toBasis, e.toBasis.toMatrix f, ?_, ?_, ?_, ?_⟩
  · simpa [OrthonormalBasis.coe_toBasis] using OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary std e
  · exact gramSchmidtOrthonormalBasis_inv_blockTriangular hdim f
  · rw [Module.Basis.toMatrix_mul_toMatrix, hstd]
  · intro j
    rw [← hnorm j, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    have h1 : ‖inner ℂ (e j) (f j)‖ ≤ ‖f j‖ := by
      calc ‖inner ℂ (e j) (f j)‖ ≤ ‖e j‖ * ‖f j‖ := norm_inner_le_norm _ _
        _ = ‖f j‖ := by rw [e.orthonormal.1 j, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2

private theorem P_ite_mul_eq_prod_triChar_mul {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → ℕ)
    (a : ∀ s, Fin (p s) → ℕ) (P : (∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) → ℂ)
    (hP : ∀ (x : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (s : ι) (b : Matrix (Fin (p s)) (Fin (p s)) ℂ),
      (∀ t, (x t).det ≠ 0) → b.det ≠ 0 → b.BlockTriangular id →
      P (Function.update x s (x s * b)) = triChar (a s) b * P x)
    (k b : ∀ s, Matrix (Fin (p s)) (Fin (p s)) ℂ) (hk : ∀ s, (k s).det ≠ 0)
    (hb : ∀ s, (b s).det ≠ 0) (hbt : ∀ s, (b s).BlockTriangular id) (S : Finset ι) :
    P (fun t => if t ∈ S then k t * b t else k t) =
      (∏ s ∈ S, triChar (a s) (b s)) * P k := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert s S hs ih =>
    have hy : ∀ t, ((fun t => if t ∈ S then k t * b t else k t) t).det ≠ 0 := by
      intro t
      by_cases ht : t ∈ S
      · simp only [ht, if_true, Matrix.det_mul]
        exact mul_ne_zero (hk t) (hb t)
      · simp only [ht, if_false]
        exact hk t
    have heq : (fun t => if t ∈ insert s S then k t * b t else k t) =
        Function.update (fun t => if t ∈ S then k t * b t else k t) s
          ((fun t => if t ∈ S then k t * b t else k t) s * b s) := by
      funext t
      by_cases hts : t = s
      · subst hts
        simp [hs]
      · simp [hts]
    rw [heq, hP _ s (b s) hy (hb s) (hbt s), ih, Finset.prod_insert hs, mul_assoc]

theorem lemmaH_holds : LemmaHStatement := by
  intro ι _ _ p a P C R hP hC hR x hx hcol
  classical
  choose k b hk hbt hkb hdiag using fun s => exists_unitary_mul_upper (x s)
  have hkdet : ∀ s, (k s).det ≠ 0 := by
    intro s
    exact (Matrix.UnitaryGroup.det_isUnit ⟨k s, hk s⟩).ne_zero
  have hbdet : ∀ s, (b s).det ≠ 0 := by
    intro s h
    apply hx s
    rw [hkb s, Matrix.det_mul, h, mul_zero]
  have hxk : x = fun t => if t ∈ (Finset.univ : Finset ι) then k t * b t else k t := by
    funext t
    simp [← hkb t]
  have hmain := P_ite_mul_eq_prod_triChar_mul p a P hP k b hkdet hbdet hbt Finset.univ
  rw [← hxk] at hmain
  have hbR : ∀ s i, ‖b s i i‖ ≤ R := by
    intro s i
    have h1 := (hdiag s i).trans (hcol s i)
    nlinarith [norm_nonneg (b s i i)]
  have hprod : ‖∏ s, triChar (a s) (b s)‖ ≤ R ^ (∑ s, ∑ i, a s i) := by
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro s _
    rw [triChar, norm_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro i _
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbR s i) _
  rw [hmain, norm_mul, mul_comm C]
  exact mul_le_mul hprod (hC k hk) (norm_nonneg _) (pow_nonneg hR _)

end ReciprocityTheory.MultiplicativeHeights
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Module

def waR {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) (x : Fin r → K) :
    (Fin r → K) →ₗ[K] K where
  toFun y := S.h x y
  map_add' y z := by
    simp only [HermForm.h, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a y := by
    simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem waR_apply {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : waR S x y = S.h x y := rfl

theorem wa_symm {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : S.h y x = S.c (S.h x y) := by
  unfold HermForm.h

  simp only [map_sum, map_mul, S.c_invol, S.G_herm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem wa_sub_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y z : Fin r → K) : S.h x (y - z) = S.h x y - S.h x z := by
  simp only [HermForm.h, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem wa_smul_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (x y : Fin r → K) : S.h x (a • y) = a * S.h x y := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem wa_zero_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x : Fin r → K) : S.h x 0 = 0 := by
  simp [HermForm.h]

theorem wa_sub_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y z : Fin r → K) : S.h (x - y) z = S.h x z - S.h y z := by
  simp only [HermForm.h, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem wa_smul_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (x y : Fin r → K) : S.h (a • x) y = S.c a * S.h x y := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem wa_sum_right {K : Type} [Field K] [NumberField K] {r n : ℕ} (S : HermForm K r)
    (x : Fin r → K) (t : Fin n → K) (b : Fin n → Fin r → K) :
    S.h x (∑ i, t i • b i) = ∑ i, t i * S.h x (b i) := by

  rw [← waR_apply S x, map_sum]
  simp only [map_smul, smul_eq_mul, waR_apply]

theorem wa_sum_left {K : Type} [Field K] [NumberField K] {r n : ℕ} (S : HermForm K r)
    (y : Fin r → K) (t : Fin n → K) (b : Fin n → Fin r → K) :
    S.h (∑ i, t i • b i) y = ∑ i, S.c (t i) * S.h (b i) y := by

  rw [wa_symm S y, wa_sum_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← wa_symm S y (b i)]

theorem wa_finrank_inf_ker {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V) (f : V →ₗ[K] K) (z : V) (hz : z ∈ W)
    (hfz : f z ≠ 0) : finrank K ↥(W ⊓ LinearMap.ker f) + 1 = finrank K W := by
  have hsup : W ⊔ LinearMap.ker f = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = (f v / f z) • z + (v - (f v / f z) • z) := by abel
    rw [hv]
    refine Submodule.add_mem_sup (W.smul_mem _ hz) ?_
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hfz, sub_self]
  have hker : finrank K (LinearMap.ker f) + 1 = finrank K V := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    have hr : LinearMap.range f = ⊤ := by
      rw [eq_top_iff]
      intro a _
      exact ⟨(a / f z) • z, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hfz]⟩
    rw [hr, finrank_top, Module.finrank_self] at h
    omega
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker f)
  rw [hsup, finrank_top] at h
  omega

theorem wa_diag {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) :
    ∀ (n : ℕ) (W : Submodule K (Fin r → K)), finrank K W = n →
      (∀ x ∈ W, S.h x x = 0 → x = 0) →
      ∃ b : Fin n → Fin r → K, (∀ i, b i ∈ W) ∧ (∀ i, b i ≠ 0) ∧
        ∀ i j, i ≠ j → S.h (b i) (b j) = 0 := by
  intro n
  induction n with
  | zero =>
    intro W _ _
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro W hW han
    have hne : W ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hW
      omega
    obtain ⟨z, hzW, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hzz : S.h z z ≠ 0 := fun h => hz0 (han z hzW h)
    have hW' : finrank K ↥(W ⊓ LinearMap.ker (waR S z)) = n := by
      have h := wa_finrank_inf_ker W (waR S z) z hzW (by rw [waR_apply]; exact hzz)
      omega
    obtain ⟨b, hbW, hb0, hbo⟩ := ih (W ⊓ LinearMap.ker (waR S z)) hW' (fun x hx hxx => han x hx.1 hxx)
    have hk : ∀ k, S.h z (b k) = 0 := fun k => (hbW k).2
    refine ⟨Fin.cons z b, fun i => ?_, fun i => ?_, fun i j hij => ?_⟩
    · cases i using Fin.cases with
      | zero => simpa using hzW
      | succ i => simpa using (hbW i).1
    · cases i using Fin.cases with
      | zero => simpa using hz0
      | succ i => simpa using hb0 i
    · cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using hk j
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.cons_succ, Fin.cons_zero]
          rw [wa_symm S z (b i), hk i, map_zero]
        | succ j =>
          simp only [Fin.cons_succ]
          exact hbo i j fun h => hij (by rw [h])

theorem wa_hyp {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (W : Submodule K (Fin r → K)) (hnd : ∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0)
    (x : Fin r → K) (hxW : x ∈ W) (hx0 : x ≠ 0) (hxx : S.h x x = 0) :
    ∃ y ∈ W, S.h x y = 1 ∧ S.h y y = 0 := by
  obtain ⟨w, hwW, hw⟩ : ∃ w ∈ W, S.h x w ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hx0 (hnd x hxW hc)
  obtain ⟨u, hu⟩ : ∃ u, u = (S.h x w)⁻¹ • w := ⟨_, rfl⟩
  have huW : u ∈ W := hu ▸ W.smul_mem _ hwW
  have hxu : S.h x u = 1 := by rw [hu, wa_smul_right, inv_mul_cancel₀ hw]
  have hux : S.h u x = 1 := by rw [wa_symm S x u, hxu, map_one]
  have hcuu : S.c (S.h u u) = S.h u u := (wa_symm S u u).symm
  obtain ⟨t, ht⟩ : ∃ t, t = S.h u u / 2 := ⟨_, rfl⟩
  have hct : S.c t = t := by rw [ht, map_div₀, hcuu, map_ofNat]
  refine ⟨u - t • x, W.sub_mem huW (W.smul_mem _ hxW), ?_, ?_⟩
  · rw [wa_sub_right, hxu, wa_smul_right, hxx, mul_zero, sub_zero]
  · simp only [wa_sub_left, wa_sub_right, wa_smul_left, wa_smul_right, hux, hxu, hxx, hct]
    rw [ht]
    ring

theorem wa_perp_nondeg {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (W : Submodule K (Fin r → K)) (hnd : ∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0)
    (x y : Fin r → K) (hxW : x ∈ W) (hyW : y ∈ W) (hxx : S.h x x = 0) (hxy : S.h x y = 1)
    (hyy : S.h y y = 0) :
    ∀ z ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y),
      (∀ w ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y), S.h z w = 0) → z = 0 := by
  intro z hz hzo
  obtain ⟨⟨hzW, hzx⟩, hzy⟩ := hz
  have hzx : S.h x z = 0 := hzx
  have hzy : S.h y z = 0 := hzy
  apply hnd z hzW
  intro w hwW
  have hyx : S.h y x = 1 := by rw [wa_symm S x y, hxy, map_one]
  have hw' : w - S.h y w • x - S.h x w • y ∈ W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y) := by
    refine ⟨⟨W.sub_mem (W.sub_mem hwW (W.smul_mem _ hxW)) (W.smul_mem _ hyW), ?_⟩, ?_⟩
    · show S.h x _ = 0
      simp only [wa_sub_right, wa_smul_right, hxx, hxy]
      ring
    · show S.h y _ = 0
      simp only [wa_sub_right, wa_smul_right, hyx, hyy]
      ring
  have h1 := hzo _ hw'
  have hzx' : S.h z x = 0 := by rw [wa_symm S x z, hzx, map_zero]
  have hzy' : S.h z y = 0 := by rw [wa_symm S y z, hzy, map_zero]
  simp only [wa_sub_right, wa_smul_right, hzx', hzy', mul_zero, sub_zero] at h1
  exact h1

end ReciprocityTheory.MultiplicativeHeights
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem half_not_integral {K : Type} [Field K] [NumberField K] : ¬ IsIntegralElt ((2 : K)⁻¹) := by
  rintro ⟨z, hz⟩
  have hint : IsIntegral ℤ ((2 : K)⁻¹) := by
    rw [← hz]
    exact NumberField.RingOfIntegers.isIntegral_coe z
  have e : ((2 : K)⁻¹) = algebraMap ℚ K ((2 : ℚ)⁻¹) := by simp
  rw [e, isIntegral_algebraMap_iff ] at hint
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hm' : (m : ℚ) = 2⁻¹ := by simpa using hm
  have h2 : ((m * 2 : ℤ) : ℚ) = 1 := by
    push_cast
    rw [hm']
    norm_num
  have h3 : m * 2 = 1 := by exact_mod_cast h2
  omega

theorem no_line {K : Type} [Field K] [NumberField K] {r : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (hL : L.FG) (x : Fin r → K) (hx : x ≠ 0) (hline : ∀ t : K, t • x ∈ L) : False := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨⟨b, hb⟩, hbint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (S.biUnion fun v => Finset.univ.image v)
  have hb0 : (b : K) ≠ 0 := by
    intro h0
    have : b = 0 := by exact_mod_cast h0
    exact nonZeroDivisors.ne_zero hb this
  have hgen : ∀ v ∈ S, ∀ j, IsIntegralElt ((b : K) * v j) := by
    intro v hv j
    obtain ⟨z, hz⟩ := hbint (v j) (Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩)
    refine ⟨z, ?_⟩
    show algebraMap (𝓞 K) K z = _
    rw [hz, Algebra.smul_def]
  have hall : ∀ w ∈ L, ∀ j, IsIntegralElt ((b : K) * w j) := by
    intro w hw
    rw [← hS] at hw
    induction hw using Submodule.span_induction with
    | mem v hv => exact hgen v hv
    | zero => intro j; exact ⟨0, by simp⟩
    | add v w _ _ hv hw =>
      intro j
      obtain ⟨z1, hz1⟩ := hv j
      obtain ⟨z2, hz2⟩ := hw j
      refine ⟨z1 + z2, ?_⟩
      push_cast
      rw [Pi.add_apply, mul_add]
      exact congrArg₂ (· + ·) hz1 hz2
    | smul a v _ hv =>
      intro j
      obtain ⟨z, hz⟩ := hv j
      refine ⟨a * z, ?_⟩
      push_cast
      rw [Pi.smul_apply, Algebra.smul_def]
      calc (a : K) * (z : K) = (a : K) * ((b : K) * v j) := congrArg (fun q => (a : K) * q) hz
        _ = (b : K) * (algebraMap (𝓞 K) K a * v j) := by
          show (a : K) * ((b : K) * v j) = (b : K) * ((a : K) * v j)
          ring
  have h1 := hall _ (hline ((2 * (b : K) * x i)⁻¹)) i
  apply half_not_integral (K := K)
  convert h1 using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

theorem hermForm_smul_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (t : K) (x y : Fin r → K) : S.h (t • x) y = S.c t * S.h x y := by
  rw [HermForm.h, HermForm.h, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem detG_ne_zero {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : IsLattice L) (hSD : IsSelfDual S L) :
    S.G.det ≠ 0 := by
  intro hdet
  have hdetT : S.Gᵀ.det = 0 := by rw [Matrix.det_transpose]; exact hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  have hw0 : (fun a => S.c (v a)) ≠ 0 := by
    intro h
    apply hv0
    funext a
    have h1 := congrArg S.c (congrFun h a)
    simpa [S.c_invol] using h1
  have hzero : ∀ y, S.h (fun a => S.c (v a)) y = 0 := by
    intro y
    simp only [HermForm.h, S.c_invol]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro b _
    have hb := congrFun hv b
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at hb
    rw [← Finset.sum_mul]
    have h2 : ∑ a, v a * S.G a b = 0 := by
      rw [← hb]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    rw [h2, zero_mul]
  apply no_line L hL.1 _ hw0
  intro t
  apply hSD.2
  intro y _
  rw [hermForm_smul_left, hzero, mul_zero]
  exact ⟨0, by simp⟩

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end
