module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
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
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

section

open scoped InnerProductSpace

namespace GlobalTheory

theorem annihilation_pow_vacuum {T : Type} [AddCommGroup T] [Module ℂ T]
    (a c : Module.End ℂ T) (s : ℝ) (v : T)
    (hcomm : a * c - c * a = (s : ℂ) • 1) (hv : a v = 0) (k : ℕ) :
    a (((c - a) ^ (k + 1)) v) = (((k : ℂ) + 1) * (s : ℂ)) • ((c - a) ^ k) v := by
  have hc : ∀ w, a (c w) = c (a w) + (s : ℂ) • w := by
    intro w
    have h := congrArg (fun f : Module.End ℂ T => f w) hcomm
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply] at h
    rw [← h]; abel
  have hD : ∀ w, a ((c - a) w) = (c - a) (a w) + (s : ℂ) • w := by
    intro w
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, hc]; abel

  have key : ∀ (k : ℕ) (w : T), a (((c - a) ^ (k + 1)) w) =
      ((c - a) ^ (k + 1)) (a w) + (((k : ℂ) + 1) * (s : ℂ)) • ((c - a) ^ k) w := by
    intro k
    induction k with
    | zero =>
      intro w
      simp only [Nat.cast_zero, zero_add, pow_one, pow_zero, Module.End.one_apply, one_mul]
      exact hD w
    | succ k ih =>
      intro w
      have e1 : ((c - a) ^ (k + 1 + 1)) w = ((c - a) ^ (k + 1)) ((c - a) w) := by
        rw [pow_succ, Module.End.mul_apply]
      have e2 : ((c - a) ^ (k + 1)) w = ((c - a) ^ k) ((c - a) w) := by
        rw [pow_succ, Module.End.mul_apply]
      have e3 : ((c - a) ^ (k + 1 + 1)) (a w) = ((c - a) ^ (k + 1)) ((c - a) (a w)) := by
        rw [pow_succ, Module.End.mul_apply]
      have e4 : (s : ℂ) + ((k : ℂ) + 1) * (s : ℂ) = (((k + 1 : ℕ) : ℂ) + 1) * (s : ℂ) := by
        push_cast; ring
      rw [e1, ih, e3, hD, map_add (f := _), map_smul, ← e2, add_assoc, ← add_smul, e4]
  have := key k v
  rw [hv, map_zero, zero_add] at this
  exact this

theorem pow_vacuum_mem {T : Type} [AddCommGroup T] [Module ℂ T]
    (a c : Module.End ℂ T) (s : ℝ) (v : T)
    (hcomm : a * c - c * a = (s : ℂ) • 1) (hv : a v = 0)
    (K : Submodule ℂ T) (hvK : v ∈ K) (hcK : ∀ x ∈ K, c x ∈ K) (k : ℕ) :
    ((c - a) ^ k) v ∈ K ∧ ((c - a) ^ (k + 1)) v ∈ K := by
  induction k with
  | zero =>
    refine ⟨by simpa using hvK, ?_⟩
    simpa [hv] using hcK v hvK
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply,
      annihilation_pow_vacuum a c s v hcomm hv k]
    exact K.sub_mem (hcK _ h2) (K.smul_mem _ h1)

theorem pow_vacuum_fock_bound (T H : Type) [AddCommGroup T] [Module ℂ T]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Φ : T →ₗ[ℂ] H)
    (a c : Module.End ℂ T) (s : ℝ) (v : T) (hs : 0 ≤ s)
    (hadj : ∀ x y, inner ℂ (Φ (c x)) (Φ y) = inner ℂ (Φ x) (Φ (a y)))
    (hcomm : a * c - c * a = (s : ℂ) • 1) (hv : a v = 0) :
    (∀ K : Submodule ℂ T, v ∈ K → (∀ x ∈ K, c x ∈ K) → ∀ k : ℕ, ((c - a) ^ k) v ∈ K) ∧
      ∀ k : ℕ, ‖Φ (((c - a) ^ k) v)‖ ^ 2 ≤ ‖Φ v‖ ^ 2 * (2 * s) ^ k * k.factorial := by
  have hc : ∀ w, a (c w) = c (a w) + (s : ℂ) • w := by
    intro w
    have h := congrArg (fun f : Module.End ℂ T => f w) hcomm
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply] at h
    rw [← h]; abel
  refine ⟨fun K hvK hcK k => (pow_vacuum_mem a c s v hcomm hv K hvK hcK k).1, ?_⟩
  have hcn : ∀ y, ‖Φ (c y)‖ ^ 2 = ‖Φ (a y)‖ ^ 2 + s * ‖Φ y‖ ^ 2 := by
    intro y
    have e : inner ℂ (Φ (c y)) (Φ (c y)) =
        inner ℂ (Φ (a y)) (Φ (a y)) + (s : ℂ) * inner ℂ (Φ y) (Φ y) := by
      rw [hadj, hc, map_add (f := _), map_smul, inner_add_right, inner_smul_right]
      congr 1
      rw [← inner_conj_symm (Φ y) (Φ (c (a y))), hadj]
      exact inner_conj_symm _ _
    simp only [inner_self_eq_norm_sq_to_K] at e
    apply Complex.ofReal_injective
    push_cast
    linear_combination e
  have hDn : ∀ y, ‖Φ ((c - a) y)‖ ^ 2 ≤ 2 * ‖Φ (c y)‖ ^ 2 + 2 * ‖Φ (a y)‖ ^ 2 := by
    intro y
    rw [LinearMap.sub_apply, map_sub]
    have h := norm_sub_le (Φ (c y)) (Φ (a y))
    have h2 : ‖Φ (c y) - Φ (a y)‖ ^ 2 ≤ (‖Φ (c y)‖ + ‖Φ (a y)‖) ^ 2 := by gcongr
    nlinarith [sq_nonneg (‖Φ (c y)‖ - ‖Φ (a y)‖)]
  have hsm : ∀ k : ℕ, ‖Φ (a (((c - a) ^ (k + 1)) v))‖ =
      ((k : ℝ) + 1) * s * ‖Φ (((c - a) ^ k) v)‖ := by
    intro k
    rw [annihilation_pow_vacuum a c s v hcomm hv k, map_smul, norm_smul]
    congr 1
    have e : ((k : ℂ) + 1) * (s : ℂ) = ((((k : ℝ) + 1) * s : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by positivity) hs)]

  have main : ∀ k : ℕ, ‖Φ (((c - a) ^ k) v)‖ ^ 2 ≤ ‖Φ v‖ ^ 2 * (2 * s) ^ k * k.factorial ∧
      ‖Φ (((c - a) ^ (k + 1)) v)‖ ^ 2 ≤
        ‖Φ v‖ ^ 2 * (2 * s) ^ (k + 1) * (k + 1).factorial := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simp, ?_⟩
      have h := hcn v
      rw [hv, map_zero, norm_zero] at h
      simp only [zero_add, pow_one, LinearMap.sub_apply, hv, sub_zero, Nat.factorial_one,
        Nat.cast_one, mul_one]
      rw [h]
      nlinarith [mul_nonneg hs (sq_nonneg ‖Φ v‖)]
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨h2, ?_⟩
      rw [pow_succ' (c - a) (k + 1), Module.End.mul_apply]
      have hA := mul_le_mul_of_nonneg_left h1
        (show (0 : ℝ) ≤ 4 * (((k : ℝ) + 1) * s) ^ 2 by positivity)
      have hB := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 2 * s by linarith)
      calc ‖Φ ((c - a) (((c - a) ^ (k + 1)) v))‖ ^ 2
          ≤ 2 * ‖Φ (c (((c - a) ^ (k + 1)) v))‖ ^ 2
              + 2 * ‖Φ (a (((c - a) ^ (k + 1)) v))‖ ^ 2 := hDn _
        _ = 4 * (((k : ℝ) + 1) * s) ^ 2 * ‖Φ (((c - a) ^ k) v)‖ ^ 2
              + 2 * s * ‖Φ (((c - a) ^ (k + 1)) v)‖ ^ 2 := by
          rw [hcn, hsm]; ring
        _ ≤ 4 * (((k : ℝ) + 1) * s) ^ 2 * (‖Φ v‖ ^ 2 * (2 * s) ^ k * k.factorial)
              + 2 * s * (‖Φ v‖ ^ 2 * (2 * s) ^ (k + 1) * (k + 1).factorial) := add_le_add hA hB
        _ = ‖Φ v‖ ^ 2 * (2 * s) ^ (k + 1 + 1) * (k + 1 + 1).factorial := by
          rw [Nat.factorial_succ (k + 1), Nat.factorial_succ k]; push_cast; ring
  exact fun k => (main k).1

end GlobalTheory
end

section

open Matrix Module

namespace GlobalTheory.RectSVD

theorem exists_orthonormalBasis_singularValues {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {p q : ℕ} (hp : finrank ℂ F = p) (hq : finrank ℂ E = q) (T : E →ₗ[ℂ] F) :
    ∃ (u : OrthonormalBasis (Fin p) ℂ F) (v : OrthonormalBasis (Fin q) ℂ E), ∀ i j,
      inner ℂ (u i) (T (v j)) =
        if (i : ℕ) = (j : ℕ) then ((T.singularValues i : ℝ) : ℂ) else 0 := by
  classical
  set v := T.isSymmetric_adjoint_comp_self.eigenvectorBasis hq with hv
  set σ : ℕ → ℝ := fun i => T.singularValues i with hσ
  have key : ∀ j k : Fin q, inner ℂ (T (v j)) (T (v k)) =
      if j = k then ((σ k : ℝ) : ℂ) ^ 2 else 0 := by
    intro j k
    have h1 := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hq k
    rw [← T.sq_singularValues_fin hq k] at h1
    rw [← LinearMap.adjoint_inner_right]
    change inner ℂ (v j) ((LinearMap.adjoint T ∘ₗ T) (v k)) = _
    rw [hv, h1, inner_smul_right, orthonormal_iff_ite.mp (OrthonormalBasis.orthonormal _)]
    split_ifs <;> simp [hσ]
  have hlt : ∀ i : ℕ, σ i ≠ 0 → i < p ∧ i < q := by
    intro i hi
    have h1 : i ∈ T.singularValues.support := Finsupp.mem_support_iff.mpr hi
    rw [T.support_singularValues, Finset.mem_range] at h1
    refine ⟨h1.trans_le (hp ▸ Submodule.finrank_le _), h1.trans_le (hq ▸ LinearMap.finrank_range_le T)⟩
  let w : Fin p → F := fun i =>
    if h : (i : ℕ) < q then ((σ i : ℂ))⁻¹ • T (v ⟨i, h⟩) else 0
  have hw : Orthonormal ℂ (({i : Fin p | σ i ≠ 0} : Set (Fin p)).domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨k, hk⟩
    have hi' : σ i ≠ 0 := hi
    have hk' : σ k ≠ 0 := hk
    have hkc : (σ k : ℂ) ≠ 0 := by exact_mod_cast hk'
    simp only [Set.domRestrict_apply, w, dif_pos (hlt _ hi').2, dif_pos (hlt _ hk').2,
      inner_smul_left, inner_smul_right, key, Subtype.mk.injEq, Fin.mk.injEq, Fin.ext_iff]
    split_ifs with h
    · rw [h]
      simp only [map_inv₀, Complex.conj_ofReal]
      field_simp
    · simp
  obtain ⟨u, hu⟩ := hw.exists_orthonormalBasis_extension_of_card_eq
    (by rw [hp, Fintype.card_fin])
  refine ⟨u, v, fun i j => ?_⟩
  by_cases hj : σ j = 0
  · have h0 : T (v j) = 0 := by
      have := key j j
      rw [if_pos rfl, hj] at this
      simpa using this
    rw [h0, inner_zero_right]
    split_ifs with h
    · have : T.singularValues i = 0 := by rw [h]; exact hj
      simp [this]
    · rfl
  · have hjc : (σ j : ℂ) ≠ 0 := by exact_mod_cast hj
    have h1 := hu ⟨j, (hlt _ hj).1⟩ hj
    have h2 : T (v j) = (σ j : ℂ) • u ⟨j, (hlt _ hj).1⟩ := by
      rw [h1]
      simp only [w, dif_pos j.isLt, Fin.eta, smul_smul, mul_inv_cancel₀ hjc, one_smul]
    rw [h2, inner_smul_right, orthonormal_iff_ite.mp u.orthonormal]
    simp only [Fin.ext_iff]
    split_ifs with h
    · simp [h, hσ]
    · simp

theorem exists_svd_singularValues (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ) :
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ,
      B = U * (Matrix.of fun (i : Fin p) (j : Fin q) =>
        if (i : ℕ) = (j : ℕ) then (((Matrix.toEuclideanLin B).singularValues i : ℝ) : ℂ) else 0)
          * Vᴴ := by
  obtain ⟨u, v, h⟩ := exists_orthonormalBasis_singularValues
    (E := EuclideanSpace ℂ (Fin q)) (F := EuclideanSpace ℂ (Fin p)) (p := p) (q := q)
    (by simp) (by simp) (Matrix.toEuclideanLin B)
  have hU := (EuclideanSpace.basisFun (Fin p) ℂ).toMatrix_orthonormalBasis_mem_unitary u
  have hV := (EuclideanSpace.basisFun (Fin q) ℂ).toMatrix_orthonormalBasis_mem_unitary v
  refine ⟨_, hU, _, hV, ?_⟩
  set U := (EuclideanSpace.basisFun (Fin p) ℂ).toBasis.toMatrix u with hUd
  set V := (EuclideanSpace.basisFun (Fin q) ℂ).toBasis.toMatrix v with hVd
  have hD : (Matrix.of fun (i : Fin p) (j : Fin q) =>
      if (i : ℕ) = (j : ℕ) then (((Matrix.toEuclideanLin B).singularValues i : ℝ) : ℂ) else 0)
        = Uᴴ * B * V := by
    ext i j
    rw [Matrix.of_apply, ← h, Matrix.mul_assoc]
    simp [hUd, hVd, Matrix.mul_apply, Basis.toMatrix_apply, PiLp.inner_apply, Matrix.mulVec,
      dotProduct, mul_comm]
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h2 : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  rw [hD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h2,
    Matrix.mul_one]

theorem exists_svd : ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ),
    ∃ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∃ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∃ h : ℕ → ℝ,
      B = U * (Matrix.of fun (i : Fin p) (j : Fin q) =>
        if (i : ℕ) = (j : ℕ) then ((h i : ℝ) : ℂ) else 0) * Vᴴ := by
  intro p q B
  obtain ⟨U, hU, V, hV, h⟩ := exists_svd_singularValues p q B
  exact ⟨U, hU, V, hV, fun i => (Matrix.toEuclideanLin B).singularValues i, h⟩

end GlobalTheory.RectSVD
end

section

open scoped InnerProductSpace

namespace GlobalTheory

namespace IrreducibleUnitaryDensity

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}

noncomputable def diag (n : ℕ) (T : H →L[ℂ] H) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => T.comp (PiLp.proj 2 (fun _ : Fin n => H) j))

@[simp] lemma diag_apply (T : H →L[ℂ] H) (x : PiLp 2 (fun _ : Fin n => H)) (j : Fin n) :
    diag n T x j = T (x j) := rfl

noncomputable def incl (j : Fin n) : H →L[ℂ] PiLp 2 (fun _ : Fin n => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) j)

lemma incl_apply (j : Fin n) (x : H) (i : Fin n) :
    (incl j x : PiLp 2 (fun _ : Fin n => H)) i = (Pi.single j x : Fin n → H) i := rfl

lemma diag_incl (T : H →L[ℂ] H) (j : Fin n) (x : H) :
    diag n T (incl j x) = incl j (T x) := by
  ext i
  simp only [diag_apply, incl_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

lemma sum_incl (x : PiLp 2 (fun _ : Fin n => H)) : ∑ j, incl j (x j) = x := by
  ext i
  simp [incl_apply, Finset.sum_apply]

lemma comm_diag (P : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H))
    (c : Fin n → Fin n → ℂ) (hc : ∀ i j x, P (incl j x) i = c i j • x) (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : Fin n => H)) : P (diag n T x) = diag n T (P x) := by
  rw [← sum_incl x]

  simp only [map_sum, diag_incl]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext i
  simp [hc]

end IrreducibleUnitaryDensity


open IrreducibleUnitaryDensity in
theorem irreducibleUnitary_density (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (G : Type) [Group G] (π : G →* (H →L[ℂ] H)) (hu : ∀ g x, ‖π g x‖ = ‖x‖)
    (hs : ∀ B : H →L[ℂ] H, (∀ g, B.comp (π g) = (π g).comp B) →
      ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ H)
    (n : ℕ) (a : Fin n → H) (Λ : Fin n → (H →L[ℂ] ℂ)) (h : ∀ g, ∑ j, Λ j (π g (a j)) = 0)
    (φ u : H) : ∑ j, ⟪φ, a j⟫_ℂ * Λ j u = 0 := open IrreducibleUnitaryDensity in by
  let a' : PiLp 2 (fun _ : Fin n => H) := WithLp.toLp 2 a
  let S : Submodule ℂ (PiLp 2 (fun _ : Fin n => H)) :=
    Submodule.span ℂ (Set.range fun g => diag n (π g) a')
  let W := S.topologicalClosure
  have hmul : ∀ g g' x, diag n (π g) (diag n (π g') x) = diag n (π (g * g')) x := by
    intro g g' x; ext i; simp
  have hone : ∀ x, diag n (π 1) x = x := by
    intro x; ext i; simp
  have hclos : ∀ (K : Submodule ℂ (PiLp 2 (fun _ : Fin n => H))), IsClosed (K : Set (PiLp 2 (fun _ : Fin n => H))) →
      (∀ g, diag n (π g) a' ∈ K) → W ≤ K := by
    intro K hK hg
    refine Submodule.topologicalClosure_minimal S ?_ hK
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    exact hg g
  have hgen : ∀ g, diag n (π g) a' ∈ W := fun g =>
    S.le_topologicalClosure (Submodule.subset_span ⟨g, rfl⟩)
  have hinv : ∀ g, ∀ x ∈ W, diag n (π g) x ∈ W := by
    intro g x hx
    have := hclos (W.comap (diag n (π g)).toLinearMap)
      (S.isClosed_topologicalClosure.preimage (diag n (π g)).continuous)
      (fun g' => by
        change diag n (π g) (diag n (π g') a') ∈ W
        rw [hmul]; exact hgen _) hx
    exact this
  have hinner : ∀ g (x y : H), ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    (LinearIsometry.mk (π g).toLinearMap (hu g)).inner_map_map x y
  have hinner' : ∀ g x y, ⟪diag n (π g) x, diag n (π g) y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro g x y
    simp [PiLp.inner_apply, hinner]
  have hinv' : ∀ g, ∀ x ∈ Wᗮ, diag n (π g) x ∈ Wᗮ := by
    intro g x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro w hw
    have h1 : w = diag n (π g) (diag n (π g⁻¹) w) := by rw [hmul, mul_inv_cancel, hone]
    rw [h1, hinner']
    exact hx _ (hinv _ _ hw)
  haveI : CompleteSpace W := S.isClosed_topologicalClosure.completeSpace_coe
  let P := W.starProjection
  have hP : ∀ g x, P (diag n (π g) x) = diag n (π g) (P x) := by
    intro g x
    refine Submodule.eq_starProjection_of_mem_orthogonal (hinv g _ (W.starProjection_apply_mem x)) ?_
    rw [← map_sub]
    exact hinv' g _ (W.sub_starProjection_mem_orthogonal x)
  have hblock : ∀ i j : Fin n, ∃ c : ℂ, ∀ x, P (incl j x) i = c • x := by
    intro i j
    obtain ⟨c, hc⟩ := hs ((PiLp.proj 2 (fun _ : Fin n => H) i).comp (P.comp (incl j))) (by
      intro g
      ext x
      change P (incl j (π g x)) i = π g (P (incl j x) i)
      rw [← diag_incl, hP, diag_apply])
    exact ⟨c, fun x => by simpa using congrArg (fun B : H →L[ℂ] H => B x) hc⟩
  choose c hc using hblock
  let R : H →L[ℂ] H := (innerSL ℂ φ).smulRight u
  have ha : a' ∈ W := hone a' ▸ hgen 1
  have hRa : diag n R a' ∈ W := by
    have h1 : P a' = a' := Submodule.starProjection_eq_self_iff.2 ha
    rw [← h1, ← comm_diag P c hc]
    exact W.starProjection_apply_mem _
  let L : PiLp 2 (fun _ : Fin n => H) →L[ℂ] ℂ :=
    ∑ j, (Λ j).comp (PiLp.proj 2 (fun _ : Fin n => H) j)
  have hL : ∀ x, L x = ∑ j, Λ j (x j) := by
    intro x; simp [L]
  have hker : W ≤ LinearMap.ker L.toLinearMap := by
    refine hclos _ (ContinuousLinearMap.isClosed_ker L) fun g => ?_
    change L _ = 0
    rw [hL]
    exact h g
  have h0 : L (diag n R a') = 0 := hker hRa
  rw [hL] at h0
  simpa [R, a'] using h0

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem exists_piTensor_shuffle_equiv (ι : Type) [Fintype ι] (F V : ι → Type)
    [∀ τ, AddCommGroup (F τ)] [∀ τ, Module ℂ (F τ)] [∀ τ, AddCommGroup (V τ)]
    [∀ τ, Module ℂ (V τ)] :
    ∃ e : ((⨂[ℂ] τ, F τ) ⊗[ℂ] (⨂[ℂ] τ, V τ)) ≃ₗ[ℂ] (⨂[ℂ] τ, (F τ ⊗[ℂ] V τ)),
      ∀ (f : ∀ τ, F τ) (v : ∀ τ, V τ),
        e (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ v)
          = PiTensorProduct.tprod ℂ (fun τ => f τ ⊗ₜ[ℂ] v τ) := by
  classical

  let bF := fun τ => Module.Basis.ofVectorSpace ℂ (F τ)
  let bV := fun τ => Module.Basis.ofVectorSpace ℂ (V τ)
  let b₁ := (Basis.piTensorProduct bF).tensorProduct (Basis.piTensorProduct bV)
  let b₂ := Basis.piTensorProduct (fun τ => (bF τ).tensorProduct (bV τ))

  let Φ : ((⨂[ℂ] τ, F τ) ⊗[ℂ] (⨂[ℂ] τ, V τ)) →ₗ[ℂ] (⨂[ℂ] τ, (F τ ⊗[ℂ] V τ)) :=
    TensorProduct.lift (PiTensorProduct.map₂ (fun τ => TensorProduct.mk ℂ (F τ) (V τ)))
  have hΦ : ∀ (f : ∀ τ, F τ) (v : ∀ τ, V τ),
      Φ (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ v)
        = PiTensorProduct.tprod ℂ (fun τ => f τ ⊗ₜ[ℂ] v τ) := by
    intro f v
    simp only [Φ, TensorProduct.lift.tmul, PiTensorProduct.map₂_tprod_tprod, TensorProduct.mk_apply]

  let e := b₁.equiv b₂ (Equiv.arrowProdEquivProdArrow ι _ _).symm

  have he : (e : _ →ₗ[ℂ] _) = Φ := by
    refine b₁.ext (fun i => ?_)
    obtain ⟨p, q⟩ := i
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
    simp only [b₁, b₂, Module.Basis.tensorProduct_apply, Basis.piTensorProduct_apply, hΦ]
    congr 1
    funext τ
    exact Module.Basis.tensorProduct_apply' (bF τ) (bV τ) (p τ, q τ)
  exact ⟨e, fun f v => (LinearMap.congr_fun he _).trans (hΦ f v)⟩

end GlobalTheory
end
