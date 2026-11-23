module

public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

section

open Filter Topology

namespace GlobalTheory

theorem linearIndependent_of_distinct_valuationLike :
    ∀ (C V Γ ι : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ),
      (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) →
      (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) →
      ∀ f : ι → V, (∀ i, f i ≠ 0) → Function.Injective (fun i => ν (f i)) →
        LinearIndependent C f := by
  intro C V Γ ι _ _ _ _ ν hsm hadd f hf hinj
  classical
  have key : ∀ (g : ι → C) (s : Finset ι), s.Nonempty → (∀ i ∈ s, g i ≠ 0) →
      (∑ i ∈ s, g i • f i) ≠ 0 ∧ ∃ j ∈ s, ν (∑ i ∈ s, g i • f i) = ν (f j) := by
    intro g s
    induction s using Finset.induction_on with
    | empty => intro h; exact absurd h Finset.not_nonempty_empty
    | @insert a s ha ih =>
      intro _ hg
      have hga : g a ≠ 0 := hg a (Finset.mem_insert_self a s)
      have hx : g a • f a ≠ 0 := smul_ne_zero hga (hf a)
      have hνx : ν (g a • f a) = ν (f a) := hsm _ _ hga
      rw [Finset.sum_insert ha]
      rcases s.eq_empty_or_nonempty with hs | hs
      · subst hs
        simp only [Finset.sum_empty, add_zero]
        exact ⟨hx, a, Finset.mem_insert_self a _, hνx⟩
      · obtain ⟨hy, j, hj, hνy⟩ := ih hs (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        have hne : ν (f a) ≠ ν (f j) := by
          intro h
          have : a = j := hinj h
          exact ha (this ▸ hj)
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · obtain ⟨h1, h2⟩ := hadd _ _ hx hy (by rw [hνx, hνy]; exact hlt)
          exact ⟨h1, a, Finset.mem_insert_self a s, by rw [h2, hνx]⟩
        · obtain ⟨h1, h2⟩ := hadd _ _ hy hx (by rw [hνx, hνy]; exact hlt)
          refine ⟨by rw [add_comm]; exact h1, j, Finset.mem_insert_of_mem hj, ?_⟩
          rw [add_comm, h2, hνy]
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  have hsum' : ∑ k ∈ s.filter (fun k => g k ≠ 0), g k • f k = 0 := by
    rw [Finset.sum_filter_of_ne]
    · exact hsum
    · intro x _ hx h
      apply hx
      simp [h]
  have hne : (s.filter (fun k => g k ≠ 0)).Nonempty := ⟨i, Finset.mem_filter.2 ⟨hi, hgi⟩⟩
  exact (key g _ hne (fun j hj => (Finset.mem_filter.1 hj).2)).1 hsum'

end GlobalTheory
end

section

open Matrix Polynomial

namespace GlobalTheory

theorem poly_eval_eq_eval_zero_of_eq_inv {k : Type} [Field k] [Infinite k] (p q : k[X]) (c : k)
    (h : ∀ x : k, x ≠ 0 → p.eval x = c * q.eval x⁻¹) : ∀ x : k, p.eval x = p.eval 0 := by
  set N := q.natDegree
  have key : X ^ N * p = C c * reflect N q := by
    apply eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := ({0}ᶜ : Set k))
    · intro x hx
      have hx0 : x ≠ 0 := hx
      letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx0)
      have hr := eval₂_reflect_mul_pow (RingHom.id k) x⁻¹ N q le_rfl
      rw [invOf_eq_inv, inv_inv] at hr
      simp only [Set.mem_setOf_eq, eval_mul, eval_pow, eval_X, eval_C, h x hx0]
      rw [← eval₂_id, ← eval₂_id, ← hr, inv_pow]
      field_simp
    · exact (Set.finite_singleton (0 : k)).infinite_compl
  by_cases hp : p = 0
  · intro x; simp [hp]
  have hdeg : (X ^ N * p).natDegree = N + p.natDegree := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hp, natDegree_X_pow]
  have hle : (C c * reflect N q).natDegree ≤ N :=
    (natDegree_C_mul_le _ _).trans (natDegree_reflect_le.trans (by simp [N]))
  rw [key] at hdeg
  have h0 : p.natDegree = 0 := by omega
  intro x
  rw [eq_C_of_natDegree_eq_zero h0]
  simp

section Lower
variable {k : Type} [Field k] {m : ℕ}

def swapLine (i j : Fin m) (t : k) : Matrix (Fin m) (Fin m) k :=
  (1 - single j j 1 - single i i 1 + single j i 1 + single i j 1) + t • single j j 1

def upperFactor (i j : Fin m) (x : k) : Matrix (Fin m) (Fin m) k :=
  diagonal (Function.update (Function.update (1 : Fin m → k) j x⁻¹) i (-x)) * transvection j i x

theorem transvection_isUpper {i j : Fin m} (hji : j < i) (x : k) :
    (transvection j i x).BlockTriangular id := by
  intro a b hba
  simp only [id] at hba
  simp only [transvection, Matrix.add_apply, one_apply_ne (ne_of_gt hba), single_apply, zero_add]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact absurd hba (not_lt.mpr hji.le)
  · rfl

theorem upperFactor_isUpper {i j : Fin m} (hji : j < i) (x : k) :
    (upperFactor i j x).BlockTriangular id :=
  (blockTriangular_diagonal _).mul (transvection_isUpper hji x)

theorem upperFactor_det {i j : Fin m} (hji : j < i) {x : k} (hx : x ≠ 0) :
    (upperFactor i j x).det = -1 := by
  have hij : i ≠ j := ne_of_gt hji
  rw [upperFactor, det_mul, det_transvection_of_ne j i (ne_of_lt hji), det_diagonal,
    Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_update_of_mem (by simp [hij.symm] : j ∈ Finset.univ \ {i})]
  simp [hx]

theorem transvection_mul_upperFactor {i j : Fin m} (hji : j < i) {x : k} (hx : x ≠ 0) :
    transvection i j x * upperFactor i j x = swapLine i j x⁻¹ := by
  have hij : i ≠ j := ne_of_gt hji
  ext a b
  rw [transvection, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
  by_cases ha : a = i
  · subst ha
    rw [single_mul_apply_same]
    by_cases hb : b = a
    · subst hb
      simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
        Function.update_apply, hij, hij.symm, hx]
    · by_cases hbj : b = j
      · subst hbj
        simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
          Function.update_apply, hij, hij.symm, hx]
      · simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
          Function.update_apply, hij, hij.symm, hx, hb, hbj, Ne.symm hb, Ne.symm hbj]
  · rw [single_mul_apply_of_ne _ _ _ _ _ ha, add_zero]
    by_cases haj : a = j
    · subst haj
      by_cases hb : b = a
      · subst hb
        simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
          Function.update_apply, hij, hij.symm, hx]
      · by_cases hbi : b = i
        · subst hbi
          simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
            Function.update_apply, hij, hij.symm, hx]
        · simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
            Function.update_apply, hij, hij.symm, hx, hb, hbi, Ne.symm hb, Ne.symm hbi]
    · simp [upperFactor, swapLine, transvection, diagonal_mul, single_apply, one_apply,
        Function.update_apply, hij, hij.symm, hx, ha, haj, Ne.symm ha, Ne.symm haj]

end Lower

section Main
variable {k : Type} [Field k] [Infinite k] {m : ℕ}

theorem rightInv_lower_transvection (ψ Φ : Matrix (Fin m) (Fin m) k → k) (r : k → k)
    (hΦ : ∀ A₀ D : Matrix (Fin m) (Fin m) k, ∃ p : Polynomial k, ∀ x : k, Φ (A₀ + x • D) = p.eval x)
    (hψ : ∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ A = r A.det * Φ A)
    (hT : ∀ A T : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id →
      ψ (A * T) = ψ A)
    (A : Matrix (Fin m) (Fin m) k) (hA : A.det ≠ 0) {i j : Fin m} (hji : j < i) (x : k) :
    ψ (A * transvection i j x) = ψ A := by
  have hij : i ≠ j := ne_of_gt hji
  have hl : ∀ y : k, (transvection i j y).det = 1 := fun y => det_transvection_of_ne i j hij y
  have hAl : ∀ y : k, (A * transvection i j y).det = A.det := fun y => by
    rw [det_mul, hl, mul_one]
  obtain ⟨p, hp⟩ := hΦ A (A * single i j 1)
  obtain ⟨q, hq⟩ := hΦ (A * (1 - single j j 1 - single i i 1 + single j i 1 + single i j 1))
    (A * single j j 1)
  have e1 : ∀ y : k, ψ (A * transvection i j y) = r A.det * p.eval y := by
    intro y
    rw [hψ _ (by rw [hAl]; exact hA), hAl, ← hp]
    congr 2
    rw [transvection, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_smul, smul_single, smul_eq_mul,
      mul_one]
  have e2 : ∀ y : k, y ≠ 0 → r A.det * p.eval y = r (-A.det) * q.eval y⁻¹ := by
    intro y hy
    have hdT : (upperFactor i j y).det ≠ 0 := by rw [upperFactor_det hji hy]; norm_num
    rw [← e1, ← hT _ _ (by rw [hAl]; exact hA) hdT (upperFactor_isUpper hji y), Matrix.mul_assoc,
      transvection_mul_upperFactor hji hy]
    have hdM : (A * swapLine i j y⁻¹).det = -A.det := by
      rw [← transvection_mul_upperFactor hji hy, ← Matrix.mul_assoc, det_mul, hAl,
        upperFactor_det hji hy, mul_neg_one]
    rw [hψ _ (by rw [hdM]; exact neg_ne_zero.mpr hA), hdM, ← hq, swapLine, Matrix.mul_add,
      Matrix.mul_smul]
  by_cases hr : r A.det = 0
  · rw [e1, hr, zero_mul, hψ A hA, hr, zero_mul]
  have hconst := poly_eval_eq_eval_zero_of_eq_inv p q (r (-A.det) / r A.det) (fun y hy => by
    rw [div_mul_eq_mul_div, eq_div_iff hr, mul_comm, e2 y hy])
  rw [e1, hconst x, hψ A hA, ← hp, zero_smul, add_zero]

theorem rightInv_of_upperTriangular_rightInv :
    ∀ {k : Type} [Field k] [Infinite k] {m : ℕ} (ψ Φ : Matrix (Fin m) (Fin m) k → k) (r : k → k),
      (∀ A₀ D : Matrix (Fin m) (Fin m) k, ∃ p : Polynomial k, ∀ x : k, Φ (A₀ + x • D) = p.eval x) →
      (∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ A = r A.det * Φ A) →
      (∀ A T : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id →
        ψ (A * T) = ψ A) →
      ∀ A B : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → B.det ≠ 0 → ψ (A * B) = ψ A := by
  intro k _ _ m ψ Φ r hΦ hψ hT A B hA hB
  refine diagonal_transvection_induction_of_det_ne_zero
    (fun B => ∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ (A * B) = ψ A) B hB ?_ ?_ ?_ A hA
  · intro D hD A hA
    exact hT A _ hA hD (blockTriangular_diagonal D)
  · intro t A hA
    rcases lt_or_gt_of_ne t.hij with h | h
    · have hdet : (t.toMatrix).det ≠ 0 := by
        rw [TransvectionStruct.toMatrix, det_transvection_of_ne _ _ t.hij]; exact one_ne_zero
      exact hT A _ hA hdet (transvection_isUpper h t.c)
    · exact rightInv_lower_transvection ψ Φ r hΦ hψ hT A hA h t.c
  · intro B₁ B₂ h₁ h₂ P₁ P₂ A hA
    rw [← Matrix.mul_assoc, P₂ _ (by rw [det_mul]; exact mul_ne_zero hA h₁), P₁ _ hA]

end Main

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

theorem lowerUnitriangular_mul_upperTriangular_of_isUnit_leadingMinors :
    ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R),
      (∀ (k : ℕ) (hk : k ≤ n), IsUnit (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) →
      ∃ L U : Matrix (Fin n) (Fin n) R, (∀ i j : Fin n, i < j → L i j = 0) ∧ (∀ i, L i i = 1) ∧
        U.BlockTriangular id ∧ (∀ i, IsUnit (U i i)) ∧ M = L * U := by
  intro R _ n
  induction n with
  | zero =>
    intro M _
    exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      Subsingleton.elim _ _⟩
  | succ n ih =>
    intro M hM
    set M' : Matrix (Fin n) (Fin n) R := M.submatrix Fin.castSucc Fin.castSucc with hM'
    have hM'min : ∀ (k : ℕ) (hk : k ≤ n),
        IsUnit (M'.submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
      intro k hk
      have := hM k (hk.trans n.le_succ)
      convert this using 2
      ext i j; rfl
    obtain ⟨L', U', hL'0, hL'1, hU't, hU'd, hLU'⟩ := ih M' hM'min
    have hL'det : L'.det = 1 := by
      rw [Matrix.det_of_lowerTriangular L' (fun i j hij => hL'0 i j hij)]
      simp [hL'1]
    have hL'u : IsUnit L'.det := by rw [hL'det]; exact isUnit_one
    have hM'u : IsUnit M'.det := by
      have := hM'min n le_rfl
      convert this using 2
      ext i j; rfl
    have hU'u : IsUnit U'.det := by
      rw [hLU', det_mul, hL'det, one_mul] at hM'u; exact hM'u
    let v : Fin n → R := fun i => M (Fin.castSucc i) (Fin.last n)
    let u : Fin n → R := fun j => M (Fin.last n) (Fin.castSucc j)
    let a : Fin n → R := u ᵥ* U'⁻¹
    let b : Fin n → R := L'⁻¹ *ᵥ v
    let e : R := M (Fin.last n) (Fin.last n) - a ⬝ᵥ b
    let L : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) 1 (fun j' => a j') j)
        (fun i' => Fin.lastCases (motive := fun _ => R) 0 (fun j' => L' i' j') j) i
    let U : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) e (fun _ => 0) j)
        (fun i' => Fin.lastCases (motive := fun _ => R) (b i') (fun j' => U' i' j') j) i
    have ha : a ᵥ* U' = u := by
      simp only [a]; rw [vecMul_vecMul, nonsing_inv_mul _ hU'u, vecMul_one]
    have hb : L' *ᵥ b = v := by
      simp only [b]; rw [mulVec_mulVec, mul_nonsing_inv _ hL'u, one_mulVec]
    have hL0 : ∀ i j : Fin (n+1), i < j → L i j = 0 := by
      intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [L] at *
      all_goals first
        | exact absurd hij (not_lt.2 (Fin.castSucc_lt_last _).le)
        | exact hL'0 _ _ hij
    have hL1 : ∀ i, L i i = 1 := by
      intro i
      induction i using Fin.lastCases <;> simp [L, hL'1]
    have hUt : U.BlockTriangular id := by
      intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [U] at *
      all_goals first
        | exact absurd hij (not_lt.2 (Fin.castSucc_lt_last _).le)
        | exact hU't hij
    have hLU : M = L * U := by
      ext i j
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          simp only [L, U, e, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, dotProduct]
          ring
        | cast j =>
          have hj := congrFun ha j
          simp only [vecMul, dotProduct, u] at hj
          simp only [L, U, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, hj]
          ring
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          have hi := congrFun hb i
          simp only [mulVec, dotProduct, v] at hi
          simp only [L, U, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, hi]
          ring
        | cast j =>
          have hij := congrFun (congrFun hLU' i) j
          simp only [M', Matrix.submatrix_apply, Matrix.mul_apply] at hij
          simp only [L, U, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, hij]
          ring
    have hdetL : L.det = 1 := by
      rw [Matrix.det_of_lowerTriangular L (fun i j hij => hL0 i j hij)]
      simp [hL1]
    have hMu : IsUnit M.det := by
      have := hM (n+1) le_rfl
      convert this using 2
      ext i j; rfl
    have he : IsUnit e := by
      rw [hLU, det_mul, hdetL, one_mul, Matrix.det_of_upperTriangular hUt,
        Fin.prod_univ_castSucc] at hMu
      have := isUnit_of_mul_isUnit_right hMu
      simpa [U] using this
    refine ⟨L, U, hL0, hL1, hUt, ?_, hLU⟩
    intro i
    induction i using Fin.lastCases with
    | last => simpa [U] using he
    | cast i => simpa [U] using hU'd i
end GlobalTheory
end

section

open Matrix Polynomial

namespace GlobalTheory

theorem irreducible_dvd_of_dvd_charpoly_of_aeval_matrix {K : Type} [Field K] {h : ℕ}
    (M : Matrix (Fin h) (Fin h) K) (p q : K[X]) (hp : Irreducible p)
    (hd : p ∣ M.charpoly) (hq : aeval M q = 0) : p ∣ q := by
  classical
  have : Fact (Irreducible p) := ⟨hp⟩
  let L := AdjoinRoot p
  let M' := M.map (algebraMap K L)
  have hM' : aeval M' q = 0 := by
    have := Polynomial.aeval_algHom_apply ((Algebra.ofId K L).mapMatrix (m := Fin h)) M q
    rw [hq, map_zero] at this
    exact this
  have hroot : M'.charpoly.IsRoot (AdjoinRoot.root p) := by
    rw [Matrix.charpoly_map, IsRoot.def, eval_map, ← aeval_def,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact hd
  have hs : AdjoinRoot.root p ∈ spectrum L M' := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  have h2 := spectrum.subset_polynomial_aeval M' (q.map (algebraMap K L)) ⟨_, hs, rfl⟩
  rw [aeval_map_algebraMap, hM'] at h2
  have hnt : Nontrivial (Matrix (Fin h) (Fin h) L) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact (spectrum.mem_iff.1 hs) (isUnit_of_subsingleton _)
  rw [spectrum.zero_eq, Set.mem_singleton_iff] at h2
  simp only [eval_map, ← aeval_def] at h2
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h2
  exact h2

theorem charpoly_eq_pow_of_aeval_irreducible_eq_zero :
    ∀ (K : Type) [Field K] (h N : ℕ) (M : Matrix (Fin h) (Fin h) K) (f : K[X]), f.Monic →
      Irreducible f → Polynomial.aeval M f = 0 → h = f.natDegree * N → M.charpoly = f ^ N := by
  intro K _ h N M f hfm hfi hf hh
  classical
  have hc0 : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hmem : ∀ b ∈ UniqueFactorizationMonoid.normalizedFactors M.charpoly, b = f := by
    intro b hb
    have hbi := UniqueFactorizationMonoid.irreducible_of_normalized_factor b hb
    have hbd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hb
    have hbn := UniqueFactorizationMonoid.normalize_normalized_factor b hb
    have hbm : b.Monic := by
      rw [← hbn]; exact Polynomial.monic_normalize hbi.ne_zero
    have hbf := irreducible_dvd_of_dvd_charpoly_of_aeval_matrix M b f hbi hbd hf
    exact eq_of_monic_of_associated hbm hfm (hbi.associated_of_dvd hfi hbf)
  set n := Multiset.card (UniqueFactorizationMonoid.normalizedFactors M.charpoly)
  have hrep : UniqueFactorizationMonoid.normalizedFactors M.charpoly = Multiset.replicate n f :=
    Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hass := UniqueFactorizationMonoid.prod_normalizedFactors hc0
  rw [hrep, Multiset.prod_replicate] at hass
  have hcp : M.charpoly = f ^ n :=
    (eq_of_monic_of_associated (hfm.pow n) (Matrix.charpoly_monic M) hass).symm
  have hdeg : f.natDegree * n = f.natDegree * N := by
    have := congrArg Polynomial.natDegree hcp
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hfm.natDegree_pow] at this
    rw [← hh]; linarith
  have hpos : 0 < f.natDegree := Irreducible.natDegree_pos hfi
  rw [hcp, Nat.eq_of_mul_eq_mul_left hpos hdeg]

end GlobalTheory
end

section

namespace GlobalTheory.AlternatingLinearCombination

theorem alternating_map_linear_combination {L M N : Type} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup N] [Module L N] {n : ℕ} (f : M [⋀^Fin n]→ₗ[L] N) (g : Fin n → M)
    (a : Fin n → Fin n → L) :
    (f fun i => ∑ l : Fin n, a i l • g l) = Matrix.det (Matrix.of a) • f g := by
  classical
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff L]
  intro φ
  let ψ : (Fin n → L) →ₗ[L] M := Fintype.linearCombination L g
  let F : (Fin n → L) [⋀^Fin n]→ₗ[L] L := (φ.compAlternatingMap f).compLinearMap ψ
  have h := F.eq_smul_basis_det (Pi.basisFun L (Fin n))
  have h1 : F a = φ (f fun i => ∑ l : Fin n, a i l • g l) := by
    simp [F, ψ, Fintype.linearCombination_apply]
  have h2 : F (Pi.basisFun L (Fin n)) = φ (f g) := by
    have : (fun i => ψ (Pi.basisFun L (Fin n) i)) = g := by
      funext i
      simp [ψ]
    change φ (f fun i => ψ (Pi.basisFun L (Fin n) i)) = _
    rw [this]
  have h3 : F a = φ (f g) * Matrix.det (Matrix.of a) := by
    rw [h, AlternatingMap.smul_apply, h2, Pi.basisFun_det_apply, smul_eq_mul]
  rw [map_sub, map_smul, ← h1, h3, smul_eq_mul, mul_comm, sub_self]

end GlobalTheory.AlternatingLinearCombination
end
