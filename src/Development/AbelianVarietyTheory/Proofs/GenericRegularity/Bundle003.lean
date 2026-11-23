module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.Nontrivial
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
public import Mathlib.RingTheory.Flat.TorsionFree

@[expose] public section

section

namespace GlobalTheory

open Matrix

section Cell
variable {R : Type} [CommRing R]

theorem det_eq_one_of_lower_unitriangular {r : ℕ} (l : Matrix (Fin r) (Fin r) R)
    (h0 : ∀ i j : Fin r, i < j → l i j = 0) (h1 : ∀ i, l i i = 1) : l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular l (fun i j h => h0 i j h)]
  simp [h1]

theorem exists_lower_mul_upper_of_leading_minors (r : ℕ) (h : Matrix (Fin r) (Fin r) R)
    (hm : ∀ k (hk : k ≤ r), IsUnit (h.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) :
    ∃ l b : Matrix (Fin r) (Fin r) R, (∀ i j : Fin r, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧
      b.BlockTriangular id ∧ h = l * b := by
  induction r with
  | zero => exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, Subsingleton.elim _ _⟩
  | succ r ih =>
    obtain ⟨L, B, hL0, hL1, hB, hA⟩ := ih (h.submatrix Fin.castSucc Fin.castSucc)
      (fun k hk => hm k (hk.trans (Nat.le_succ r)))
    have hLd : L.det = 1 := det_eq_one_of_lower_unitriangular L hL0 hL1
    have hAu : IsUnit (h.submatrix Fin.castSucc Fin.castSucc).det := hm r (Nat.le_succ r)
    have hBu : IsUnit B.det := by
      rw [hA, Matrix.det_mul, hLd, one_mul] at hAu; exact hAu
    have hLu : IsUnit L.det := by rw [hLd]; exact isUnit_one
    set x : Fin r → R := (fun j => h (Fin.last r) j.castSucc) ᵥ* B⁻¹ with hx
    set y : Fin r → R := L⁻¹ *ᵥ (fun i => h i.castSucc (Fin.last r)) with hy
    have hxB : x ᵥ* B = fun j => h (Fin.last r) j.castSucc := by
      rw [hx, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hBu, Matrix.vecMul_one]
    have hLy : L *ᵥ y = fun i => h i.castSucc (Fin.last r) := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hLu, Matrix.one_mulVec]
    refine ⟨Matrix.of fun i j => Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) 1 x j)
        (fun i => Fin.lastCases (motive := fun _ => R) 0 (L i) j) i,
      Matrix.of fun i j => Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) (h (Fin.last r) (Fin.last r) - x ⬝ᵥ y) (fun _ => 0) j)
        (fun i => Fin.lastCases (motive := fun _ => R) (y i) (B i) j) i, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last j))
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simpa using hL0 i j (by simpa using hij)
    · intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using hL1 i
    · intro i j hij
      induction j using Fin.lastCases with
      | last => exact absurd hij (not_lt.2 (Fin.le_last i))
      | cast j =>
        induction i using Fin.lastCases with
        | last => simp
        | cast i => simpa using hB (i := i) (j := j) (by simpa using hij)
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp [dotProduct]
        | cast j => simpa [Matrix.vecMul, dotProduct] using (congrFun hxB j).symm
      | cast i =>
        induction j using Fin.lastCases with
        | last => simpa [Matrix.mulVec, dotProduct] using (congrFun hLy i).symm
        | cast j => simpa [Matrix.mul_apply] using congrFun (congrFun hA i) j

theorem eq_one_of_lower_unitriangular_eq_mul {r : ℕ} (l l' c : Matrix (Fin r) (Fin r) R)
    (h0 : ∀ i j : Fin r, i < j → l i j = 0) (h1 : ∀ i, l i i = 1)
    (h0' : ∀ i j : Fin r, i < j → l' i j = 0) (h1' : ∀ i, l' i i = 1)
    (hc : c.BlockTriangular id) (h : l = l' * c) : c = 1 := by
  have key : ∀ i : Fin r, ∀ j, c i j = (1 : Matrix (Fin r) (Fin r) R) i j := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      intro j
      rcases lt_or_ge j i with hji | hij
      · rw [hc hji, Matrix.one_apply_ne hji.ne']
      · have e : l i j = c i j := by
          rw [h, Matrix.mul_apply, Finset.sum_eq_single i, h1', one_mul]
          · intro k _ hk
            rcases lt_or_gt_of_ne hk with hk | hk
            · rw [ih k hk, Matrix.one_apply_ne (hk.trans_le hij).ne, mul_zero]
            · rw [h0' i k hk, zero_mul]
          · simp
        rw [← e]
        rcases hij.eq_or_lt with rfl | hij
        · simp [h1]
        · rw [h0 i j hij, Matrix.one_apply_ne hij.ne]
  ext i j
  exact key i j

theorem isUnit_det_of_upper_of_isUnit_diag {r : ℕ} (b : Matrix (Fin r) (Fin r) R)
    (hb : b.BlockTriangular id) (hu : ∀ i, IsUnit (b i i)) : IsUnit b.det := by
  rw [Matrix.det_of_upperTriangular hb]
  exact IsUnit.prod_iff.2 fun i _ => hu i

end Cell

theorem cell_coordinates_exists_unique :
    ∀ (R : Type) [CommRing R] (n r : ℕ) (ι : Fin r ↪ Fin n) (g : Matrix (Fin n) (Fin r) R), ((∀ k (hk : k ≤ r), IsUnit (g.submatrix (fun i : Fin k => ι (Fin.castLE hk i)) (Fin.castLE hk)).det) ↔ ∃ (u : Matrix (Fin n) (Fin r) R) (b : Matrix (Fin r) (Fin r) R), (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧ (∀ i : Fin r, u (ι i) i = 1) ∧ b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ g = u * b) ∧ ∀ (u u' : Matrix (Fin n) (Fin r) R) (b b' : Matrix (Fin r) (Fin r) R), (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧ (∀ i : Fin r, u (ι i) i = 1) → (∀ i j : Fin r, i < j → u' (ι i) j = 0) ∧ (∀ i : Fin r, u' (ι i) i = 1) → b.BlockTriangular id → b'.BlockTriangular id → (∀ i, IsUnit (b i i)) → u * b = u' * b' → u = u' ∧ b = b' := by
  intro R _ n r ι g
  refine ⟨⟨fun hm => ?_, ?_⟩, ?_⟩
  · obtain ⟨l, b, hl0, hl1, hb, hh⟩ :=
      exists_lower_mul_upper_of_leading_minors r (g.submatrix ι id) hm
    have hbu : IsUnit b.det := by
      have h1 : IsUnit (g.submatrix ι id).det := hm r le_rfl
      rwa [hh, Matrix.det_mul, det_eq_one_of_lower_unitriangular l hl0 hl1, one_mul] at h1
    have hu : ∀ i j, (g * b⁻¹) (ι i) j = l i j := by
      intro i j
      have : l = g.submatrix ι id * b⁻¹ := by
        rw [hh, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hbu, Matrix.mul_one]
      rw [this]; simp [Matrix.mul_apply]
    refine ⟨g * b⁻¹, b, fun i j hij => by rw [hu, hl0 i j hij], fun i => by rw [hu, hl1], hb, ?_, ?_⟩
    · intro i
      rw [Matrix.det_of_upperTriangular hb] at hbu
      exact IsUnit.prod_iff.1 hbu i (Finset.mem_univ _)
    · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hbu, Matrix.mul_one]
  · rintro ⟨u, b, hu0, hu1, hb, hbu, rfl⟩ k hk
    have e : (u * b).submatrix (fun i : Fin k => ι (Fin.castLE hk i)) (Fin.castLE hk) =
        u.submatrix (fun i : Fin k => ι (Fin.castLE hk i)) (Fin.castLE hk) *
          b.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      symm
      refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ ?_ (fun _ => rfl)
      intro m hm
      have hkm : k ≤ m.val := by
        by_contra hlt
        exact hm ⟨⟨m.val, not_le.1 hlt⟩, rfl⟩
      have : Fin.castLE hk j < m := by
        rw [Fin.lt_def]; exact lt_of_lt_of_le j.2 hkm
      have h0 : b m (Fin.castLE hk j) = 0 := hb this
      rw [h0, mul_zero]
    rw [e, Matrix.det_mul, det_eq_one_of_lower_unitriangular, one_mul]
    · exact isUnit_det_of_upper_of_isUnit_diag _ (fun i j hij => hb hij) (fun i => hbu _)
    · intro i j hij; exact hu0 _ _ hij
    · intro i; exact hu1 _
  · rintro u u' b b' ⟨hu0, hu1⟩ ⟨hu0', hu1'⟩ hb hb' hbu h
    have hd := isUnit_det_of_upper_of_isUnit_diag b hb hbu
    have hu : u = u' * (b' * b⁻¹) := by
      rw [← Matrix.mul_assoc, ← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    have hbi : b⁻¹.BlockTriangular id := by
      let _ := Matrix.invertibleOfIsUnitDet b hd
      exact Matrix.blockTriangular_inv_of_blockTriangular hb
    have hc : b' * b⁻¹ = 1 := by
      refine eq_one_of_lower_unitriangular_eq_mul (u.submatrix ι id) (u'.submatrix ι id) _
        hu0 hu1 hu0' hu1' (hb'.mul hbi) ?_
      ext i j
      rw [Matrix.submatrix_apply, hu]; simp [Matrix.mul_apply]
    refine ⟨by rw [hu, hc, Matrix.mul_one], ?_⟩
    calc b = b' * b⁻¹ * b := by rw [hc, Matrix.one_mul]
      _ = b' := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]

end GlobalTheory
end

section

namespace GlobalTheory

open Matrix

theorem mem_span_first_columns_iff {R : Type} [CommRing R] {n r : ℕ}
    (M : Matrix (Fin n) (Fin r) R) (k : ℕ) (x : Fin n → R) :
    x ∈ Submodule.span R {y : Fin n → R | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => M i j} ↔
      ∃ c : Fin r → R, (∀ j : Fin r, k ≤ (j : ℕ) → c j = 0) ∧ x = M *ᵥ c := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      refine ⟨Pi.single j 1, fun j' hj' => ?_, ?_⟩
      · have : j' ≠ j := by rintro rfl; omega
        simp [this]
      · ext i
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨d, hd, rfl⟩ := hz
      exact ⟨c + d, fun j hj => by simp [hc j hj, hd j hj], by rw [Matrix.mulVec_add]⟩
    | smul a y _ hy =>
      obtain ⟨c, hc, rfl⟩ := hy
      exact ⟨a • c, fun j hj => by simp [hc j hj], by rw [Matrix.mulVec_smul]⟩
  · rintro ⟨c, hc, rfl⟩
    have : M *ᵥ c = ∑ j, c j • (fun i => M i j) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [this]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < k
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [hc j (not_lt.mp hj), zero_smul]
      exact Submodule.zero_mem _

theorem exists_triangular_of_span_first_columns_le {R : Type} [CommRing R] {n r : ℕ}
    (u u' : Matrix (Fin n) (Fin r) R)
    (h : ∀ k : ℕ,
      Submodule.span R {y : Fin n → R | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u' i j} ≤
      Submodule.span R {y : Fin n → R | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u i j}) :
    ∃ b : Matrix (Fin r) (Fin r) R, b.BlockTriangular id ∧ u' = u * b := by
  have key : ∀ j : Fin r, ∃ c : Fin r → R, (∀ j' : Fin r, (j : ℕ) + 1 ≤ (j' : ℕ) → c j' = 0) ∧
      (fun i => u' i j) = u *ᵥ c := fun j =>
    (mem_span_first_columns_iff u _ _).mp
      (h (j + 1) (Submodule.subset_span ⟨j, Nat.lt_succ_self _, rfl⟩))
  choose c hc hc' using key
  refine ⟨Matrix.of fun i j => c j i, fun i j hij => hc j i hij, ?_⟩
  ext i j
  have := congrFun (hc' j) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem cell_columns_saturated_and_triangular :
    ∀ (V L : Type) [CommRing V] [IsDomain V] [Field L] [Algebra V L] [IsFractionRing V L] (n r : ℕ) (ι : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) V), (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧ (∀ i : Fin r, u (ι i) i = 1) → (∀ (k : ℕ) (x : Fin n → V), (fun i => algebraMap V L (x i)) ∈ Submodule.span L {y : Fin n → L | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => algebraMap V L (u i j)} ↔ x ∈ Submodule.span V {y : Fin n → V | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u i j}) ∧ ∀ u' : Matrix (Fin n) (Fin r) V, (∀ k : ℕ, Submodule.span V {y : Fin n → V | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u' i j} = Submodule.span V {y : Fin n → V | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u i j}) → ∃ b : Matrix (Fin r) (Fin r) V, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ u' = u * b := by
  intro V L _ _ _ _ _ n r ι u ⟨h0, h1⟩
  set A : Matrix (Fin r) (Fin r) V := u.submatrix ι id with hA
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_lowerTriangular A (fun i j hij => h0 i j hij)]
    simp [hA, h1]
  have hAu : IsUnit A.det := hdet ▸ isUnit_one
  have hinj : Function.Injective (algebraMap V L) := IsFractionRing.injective V L
  have hmap : ∀ {m : ℕ} (M : Matrix (Fin m) (Fin r) V) (c : Fin r → V) (i : Fin m),
      algebraMap V L ((M *ᵥ c) i) =
        ((M.map (algebraMap V L)) *ᵥ (fun j => algebraMap V L (c j))) i := by
    intro m M c i
    simp [Matrix.mulVec, dotProduct]
  refine ⟨fun k x => ?_, fun u' hu' => ?_⟩
  · have e := mem_span_first_columns_iff (u.map (algebraMap V L)) k
      (fun i => algebraMap V L (x i))
    simp only [Matrix.map_apply] at e
    rw [e, mem_span_first_columns_iff]
    constructor
    · rintro ⟨c, hc, hx⟩
      set c₀ : Fin r → V := A⁻¹ *ᵥ (fun i => x (ι i)) with hc₀
      have hAc : A *ᵥ c₀ = fun i => x (ι i) := by
        rw [hc₀, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hAu, Matrix.one_mulVec]
      have hAL : IsUnit (A.map (algebraMap V L)) := by
        rw [Matrix.isUnit_iff_isUnit_det]
        have := (algebraMap V L).map_det A
        rw [hdet, map_one] at this
        exact (show (1 : L) = (A.map (algebraMap V L)).det from this) ▸ isUnit_one
      have hcc : (fun j => algebraMap V L (c₀ j)) = c := by
        apply Matrix.mulVec_injective_iff_isUnit.mpr hAL
        ext i
        rw [← hmap, hAc]
        exact congrFun hx (ι i)
      refine ⟨c₀, fun j hj => hinj ?_, ?_⟩
      · rw [map_zero, ← hc j hj, ← hcc]
      · ext i
        apply hinj
        rw [hmap, hcc]
        exact congrFun hx i
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun j => algebraMap V L (c j), fun j hj => by simp [hc j hj], ?_⟩
      ext i
      exact hmap u c i
  · obtain ⟨b, hb, hub⟩ := exists_triangular_of_span_first_columns_le u u' fun k => (hu' k).le
    obtain ⟨b', hb', hub'⟩ := exists_triangular_of_span_first_columns_le u' u fun k => (hu' k).ge
    have h2 : u = u * (b * b') := by rw [← Matrix.mul_assoc, ← hub, ← hub']
    have h3 : A = A * (b * b') := by
      ext i j
      exact congrFun (congrFun h2 (ι i)) j
    have h4 : b * b' = 1 := by
      have := congrArg (fun M => A⁻¹ * M) h3
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hAu, Matrix.one_mul] at this
      exact this.symm
    refine ⟨b, hb, fun i => ?_, hub⟩
    have h5 : (b * b') i i = b i i * b' i i := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
      rcases lt_or_gt_of_ne hj with h | h
      · rw [hb h, zero_mul]
      · rw [hb' h, mul_zero]
    rw [h4, Matrix.one_apply_eq] at h5
    exact IsUnit.of_mul_eq_one _ h5.symm

end GlobalTheory
end

section

open TensorProduct

namespace GlobalTheory

theorem flat_of_injective_algebraMap_of_isDomain (O A : Type*) [CommRing O] [IsDomain O]
    [IsPrincipalIdealRing O] [CommRing A] [IsDomain A] [Algebra O A]
    (h : Function.Injective (algebraMap O A)) : Module.Flat O A := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro m ⟨⟨r, hr⟩, hm⟩
  rw [Submodule.mem_bot]
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  have hmul : algebraMap O A r * m = 0 := by rw [← Algebra.smul_def]; exact hm
  exact (mul_eq_zero.mp hmul).resolve_left ((map_ne_zero_iff _ h).mpr hr0)

theorem one_tmul_mem_nonZeroDivisors_of_flat (O A B : Type*) [CommRing O] [CommRing A]
    [CommRing B] [IsDomain B] [Algebra O A] [Algebra O B] [Module.Flat O A] {b : B} (hb : b ≠ 0) :
    ((1 : A) ⊗ₜ[O] b) ∈ nonZeroDivisors (A ⊗[O] B) := by
  have hinj : Function.Injective (LinearMap.lTensor A (LinearMap.mulRight O b)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (mul_left_injective₀ hb)
  have key : ∀ x : A ⊗[O] B, LinearMap.lTensor A (LinearMap.mulRight O b) x = x * (1 ⊗ₜ[O] b) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add (f := _), hx, hy, add_mul]
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact hinj (by rw [key, map_zero, hx])

theorem tmul_one_mem_nonZeroDivisors_of_flat (O A B : Type*) [CommRing O] [CommRing A]
    [CommRing B] [IsDomain A] [Algebra O A] [Algebra O B] [Module.Flat O B] {a : A} (ha : a ≠ 0) :
    (a ⊗ₜ[O] (1 : B)) ∈ nonZeroDivisors (A ⊗[O] B) := by
  have hinj : Function.Injective (LinearMap.rTensor B (LinearMap.mulRight O a)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (mul_left_injective₀ ha)
  have key : ∀ x : A ⊗[O] B, LinearMap.rTensor B (LinearMap.mulRight O a) x = x * (a ⊗ₜ[O] (1 : B)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c d => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add (f := _), hx, hy, add_mul]
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  exact hinj (by rw [key, map_zero, hx])

theorem exists_isMaximal_tensorProduct_of_isLocalHom (O O' B : Type*) [CommRing O] [IsLocalRing O]
    [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')]
    [CommRing B] [Algebra O B] (I : Ideal B) (hI : I ≠ ⊤)
    (hm : Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I) :
    ∃ M : Ideal (O' ⊗[O] B), M.IsMaximal ∧
      (∀ a ∈ IsLocalRing.maximalIdeal O', a ⊗ₜ[O] (1 : B) ∈ M) ∧
      ∀ b ∈ I, (1 : O') ⊗ₜ[O] b ∈ M := by
  obtain ⟨N, hN, hIN⟩ := Ideal.exists_le_maximal I hI
  have hle : IsLocalRing.maximalIdeal O ≤ N.comap (algebraMap O B) :=
    Ideal.map_le_iff_le_comap.mp (hm.trans hIN)
  letI : Algebra (IsLocalRing.ResidueField O) (B ⧸ N) :=
    Ideal.Quotient.algebraQuotientOfLEComap hle
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) (B ⧸ N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Nontrivial (IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _
      (RingHom.injective (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O'))) (RingHom.injective (algebraMap (IsLocalRing.ResidueField O) (B ⧸ N)))
  let f : O' →ₐ[O] IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N) :=
    (Algebra.TensorProduct.includeLeft).comp (IsScalarTower.toAlgHom O O' (IsLocalRing.ResidueField O'))
  let g : B →ₐ[O] IsLocalRing.ResidueField O' ⊗[IsLocalRing.ResidueField O] (B ⧸ N) :=
    ((Algebra.TensorProduct.includeRight).restrictScalars O).comp (IsScalarTower.toAlgHom O B (B ⧸ N))
  let ψ := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  obtain ⟨M, hM, hkM⟩ := Ideal.exists_le_maximal (RingHom.ker ψ.toRingHom) (RingHom.ker_ne_top _)
  refine ⟨M, hM, fun a ha => hkM ?_, fun b hb => hkM ?_⟩
  · rw [RingHom.mem_ker]
    have h0 : IsLocalRing.residue O' a = 0 :=
      (IsLocalRing.residue_eq_zero_iff a).mpr ha
    simp [ψ, f, g, Algebra.TensorProduct.lift_tmul, h0]
  · rw [RingHom.mem_ker]
    have h0 : Ideal.Quotient.mk N b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hIN hb)
    simp [ψ, f, g, Algebra.TensorProduct.lift_tmul, h0]

theorem exists_integral_point_of_complete_case :
    (∀ (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O] [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B] (M : Ideal B), M.IsMaximal → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ M → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V) (_ : Module.Finite O V) (φ : B →ₐ[O] V), φ e ≠ 0 ∧ ∀ x ∈ M, φ x ∈ IsLocalRing.maximalIdeal V) → ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsAdicComplete (IsLocalRing.maximalIdeal O') O'] [CharZero O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B], Function.Injective (algebraMap O B) → ∀ I : Ideal B, I ≠ ⊤ → Ideal.map (algebraMap O B) (IsLocalRing.maximalIdeal O) ≤ I → ∀ e : B, e ≠ 0 → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O' V) (_ : Module.Finite O' V) (φ : B →+* V), φ.comp (algebraMap O B) = (algebraMap O' V).comp (algebraMap O O') ∧ φ e ≠ 0 ∧ ∀ x ∈ I, φ x ∈ IsLocalRing.maximalIdeal V := by
  intro H O O' _ _ _ _ _ _ _ _ _ _ hOO' B _ _ _ _ hOB I hI hmI e he
  haveI : Module.Flat O O' := flat_of_injective_algebraMap_of_isDomain O O' hOO'
  haveI : Module.Flat O B := flat_of_injective_algebraMap_of_isDomain O B hOB
  obtain ⟨M, hM, hM1, hM2⟩ := exists_isMaximal_tensorProduct_of_isLocalHom O O' B I hI hmI
  obtain ⟨P, hPmin, hPM⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal (O' ⊗[O] B)) ≤ M)
  haveI : P.IsPrime := hPmin.isPrime
  haveI : IsDomain (O' ⊗[O] B ⧸ P) := Ideal.Quotient.isDomain P
  have hinj : Function.Injective (algebraMap O' (O' ⊗[O] B ⧸ P)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    have ha' : Ideal.Quotient.mk P (a ⊗ₜ[O] (1 : B)) = 0 := ha
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.Quotient.eq_zero_iff_mem.mp ha')
      hPmin (tmul_one_mem_nonZeroDivisors_of_flat O O' B ha0)
  haveI : Module.Flat O' (O' ⊗[O] B ⧸ P) := flat_of_injective_algebraMap_of_isDomain _ _ hinj
  haveI : Algebra.FiniteType O' (O' ⊗[O] B ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ O' P)
      (Ideal.Quotient.mkₐ_surjective O' P)
  have hM' : (M.map (Ideal.Quotient.mk P)).IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hM).resolve_left ?_
    intro htop
    have h1 : (1 : O' ⊗[O] B ⧸ P) ∈ M.map (Ideal.Quotient.mk P) := by rw [htop]; exact Submodule.mem_top
    obtain ⟨m, hm, hm1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp h1
    have hmP : m - 1 ∈ P := Ideal.Quotient.eq.mp (by rw [hm1, map_one])
    exact hM.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using M.sub_mem hm (hPM hmP)))
  have hmap : Ideal.map (algebraMap O' (O' ⊗[O] B ⧸ P)) (IsLocalRing.maximalIdeal O') ≤
      M.map (Ideal.Quotient.mk P) :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => Ideal.mem_map_of_mem (Ideal.Quotient.mk P) (hM1 a ha)
  have he' : Ideal.Quotient.mk P ((1 : O') ⊗ₜ[O] e) ≠ 0 := by
    intro h0
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (Ideal.Quotient.eq_zero_iff_mem.mp h0)
      hPmin (one_tmul_mem_nonZeroDivisors_of_flat O O' B he)
  obtain ⟨V, i₁, i₂, i₃, i₄, i₅, φ, hφe, hφM⟩ :=
    H O' (O' ⊗[O] B ⧸ P) (M.map (Ideal.Quotient.mk P)) hM' hmap _ he'
  refine ⟨V, i₁, i₂, i₃, i₄, i₅,
    φ.toRingHom.comp ((Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B).toRingHom), ?_, hφe, ?_⟩
  · ext o
    have h1 : (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) (algebraMap O B o) =
        algebraMap O' (O' ⊗[O] B) (algebraMap O O' o) := by
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply O O' (O' ⊗[O] B)]
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1]
    exact φ.commutes _
  · intro x hx
    exact hφM _ (Ideal.mem_map_of_mem (Ideal.Quotient.mk P) (hM2 x hx))

end GlobalTheory
end
