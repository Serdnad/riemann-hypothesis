module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Invariant.Defs
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Unramified.Finite

@[expose] public section

section

open scoped TensorProduct

namespace GlobalTheory

open MvPowerSeries Finsupp in
theorem coeff_mul_X_ite {k : Type} [CommRing k] {g : ℕ} (f : MvPowerSeries (Fin g) k)
    (j : Fin g) (m : Fin g →₀ ℕ) :
    coeff m (f * X j) = if m j ≠ 0 then coeff (m - single j 1) f else 0 := by
  classical
  rw [X_def, coeff_mul_monomial, mul_one]
  congr 1
  simp [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]

open MvPowerSeries Finsupp in
theorem mvPowerSeries_X_syzygy {k : Type} [CommRing k] {g : ℕ}
    (r : Fin g → MvPowerSeries (Fin g) k) (hr : ∑ i, r i * X i = 0) :
    ∃ s : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k), s.transpose = -s ∧ (∀ i, s i i = 0) ∧
      r = s.mulVec (fun i => X i) := by
  classical
  let t : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k) := fun i j n =>
    if j < i ∧ ∀ l < j, n l = 0 then coeff (n + single j 1) (r i) else 0
  have ht : ∀ i j n, coeff n (t i j) =
      if j < i ∧ ∀ l < j, n l = 0 then coeff (n + single j 1) (r i) else 0 := fun _ _ _ => rfl
  refine ⟨t - t.transpose, by simp [Matrix.transpose_sub], fun i => by simp, ?_⟩
  funext i
  ext m
  have h1 : ∀ j, coeff m (t i j * X j) =
      if m j ≠ 0 ∧ j < i ∧ ∀ l < j, m l = 0 then coeff m (r i) else 0 := by
    intro j
    rw [coeff_mul_X_ite, ht]
    by_cases hj : m j = 0
    · simp [hj]
    · have e : m - single j 1 + single j 1 = m :=
        tsub_add_cancel_of_le (by simpa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero] using hj)
      have e2 : (∀ l < j, (m - single j 1 : Fin g →₀ ℕ) l = 0) ↔ ∀ l < j, m l = 0 := by
        refine forall_congr' fun l => forall_congr' fun hl => ?_
        simp [Finsupp.single_apply, hl.ne']
      simp only [e, e2, hj, ne_eq, not_false_eq_true, if_true, true_and]
  have h2 : ∀ j, coeff m (t j i * X j) =
      if (∀ l < i, m l = 0) ∧ j ≠ i then coeff (m + single i 1) (r j * X j) else 0 := by
    intro j
    rw [coeff_mul_X_ite, ht, coeff_mul_X_ite]
    by_cases hji : j = i
    · simp [hji]
    have e0 : (m + single i 1 : Fin g →₀ ℕ) j = m j := by
      simp [Finsupp.single_apply, Ne.symm hji]
    rw [e0]
    by_cases hj : m j = 0
    · simp [hj]
    have e : m - single j 1 + single i 1 = m + single i 1 - single j 1 :=
      tsub_add_eq_add_tsub (by simpa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero] using hj)
    rw [e]
    rcases lt_or_gt_of_ne hji with h | h
    · have : ¬ ∀ l < i, m l = 0 := fun H => hj (H j h)
      simp [this, h.not_gt]
    · have e2 : (∀ l < i, (m - single j 1 : Fin g →₀ ℕ) l = 0) ↔ ∀ l < i, m l = 0 := by
        refine forall_congr' fun l => forall_congr' fun hl => ?_
        simp [Finsupp.single_apply, (hl.trans h).ne']
      simp only [e2, hj, h, hji, ne_eq, not_false_eq_true, if_true, true_and, and_true]

  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.transpose_apply, sub_mul,
  map_sum, map_sub, h1, h2, Finset.sum_sub_distrib]
  by_cases hi : ∀ l < i, m l = 0
  · rw [Finset.sum_eq_zero (fun j _ => if_neg (fun H => H.1 (hi j H.2.1)))]
    have h3 := congrArg (coeff (m + single i 1)) hr

    rw [map_sum, map_zero, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), coeff_mul_X_ite] at h3
    simp only [iff_true_intro hi, true_and]
    rw [← Finset.sum_filter, Finset.filter_ne']
    simp only [Finsupp.add_apply, single_eq_same, add_tsub_cancel_right] at h3
    rw [if_pos (by omega)] at h3
    linear_combination h3
  · simp only [hi, false_and, if_false, Finset.sum_const_zero, sub_zero]
    push_neg at hi
    obtain ⟨l, hl, hml⟩ := hi
    obtain ⟨j, hj, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Fin g)) {j | m j ≠ 0} ⟨l, hml⟩
    have hj0 : ∀ a < j, m a = 0 := fun a ha => by
      by_contra h; exact hmin a h ha
    rw [Finset.sum_eq_single j]
    · rw [if_pos ⟨hj, lt_of_le_of_lt (not_lt.1 (hmin l hml)) hl, hj0⟩]
    · intro b _ hb
      refine if_neg fun H => ?_
      rcases lt_or_gt_of_ne hb with h | h
      · exact H.1 (hj0 b h)
      · exact hj (H.2.2 j h)
    · simp

open MvPowerSeries Finsupp in
theorem mvPowerSeries_prod_X_pow_notMem {k : Type} [CommRing k] [Nontrivial k] {g : ℕ} (N : ℕ) :
    ∏ i, (X i : MvPowerSeries (Fin g) k) ^ N ∉
      Ideal.span (Set.range fun i => (X i : MvPowerSeries (Fin g) k) ^ (N + 1)) := by
  classical
  intro h
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  have hp : ∀ s : Finset (Fin g), ∏ i ∈ s, (X i : MvPowerSeries (Fin g) k) ^ N =
      monomial (∑ i ∈ s, single i N) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, one_mul]
  have := congrArg (coeff (∑ i : Fin g, single i N)) hc

  rw [hp, coeff_monomial_same, map_sum, Finset.sum_eq_zero] at this
  · exact zero_ne_one this
  · intro i _
    refine X_pow_dvd_iff.1 (dvd_mul_left _ _) _ ?_
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem mvPowerSeries_variables_syzygy_socle :
    ∀ (k : Type) [Field k] (g : ℕ) (x : Fin g → MvPowerSeries (Fin g) k), (∀ i, x i = MvPowerSeries.X i) → (∀ r : Fin g → _, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) _, s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x) ∧ ∀ N : ℕ, ∏ i, x i ^ N ∉ Ideal.span (Set.range fun i => x i ^ (N + 1)) := by
  intro k _ g x hx
  obtain rfl : x = fun i => MvPowerSeries.X i := funext hx
  exact ⟨fun r hr => mvPowerSeries_X_syzygy r hr, fun N => mvPowerSeries_prod_X_pow_notMem N⟩

end GlobalTheory
end

section

namespace GlobalTheory.CommonAlgClosedExtension

open scoped TensorProduct

theorem exists_common_algClosed_extension (K₀ K K' : Type) [Field K₀] [Field K] [Field K']
    (i : K₀ →+* K) (i' : K₀ →+* K') :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (j : K →+* Ω) (j' : K' →+* Ω),
      RingHom.comp j i = RingHom.comp j' i' := by
  letI : Algebra K₀ K := i.toAlgebra
  letI : Algebra K₀ K' := i'.toAlgebra
  haveI : Nontrivial (K ⊗[K₀] K') := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[K₀] K')
  letI : Field ((K ⊗[K₀] K') ⧸ m) := Ideal.Quotient.field m
  let φ : (K ⊗[K₀] K') →+* AlgebraicClosure ((K ⊗[K₀] K') ⧸ m) :=
    (algebraMap ((K ⊗[K₀] K') ⧸ m) _).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure ((K ⊗[K₀] K') ⧸ m), inferInstance, inferInstance,
    φ.comp (Algebra.TensorProduct.includeLeft (R := K₀) (S := K₀) (A := K) (B := K')).toRingHom,
    φ.comp (Algebra.TensorProduct.includeRight (R := K₀) (A := K) (B := K')).toRingHom, ?_⟩
  ext x
  have h1 := (Algebra.TensorProduct.includeLeft (R := K₀) (S := K₀) (A := K) (B := K')).commutes x
  have h2 := (Algebra.TensorProduct.includeRight (R := K₀) (A := K) (B := K')).commutes x
  exact congrArg φ (h1.trans h2.symm)

end GlobalTheory.CommonAlgClosedExtension
end

section

open scoped TensorProduct

namespace GlobalTheory

private theorem sum_pairing_eq_card_ite_one {Γ K : Type} [CommGroup Γ] [Fintype Γ] [DecidableEq Γ] [Field K]
    (X : Γ → Γ → K) (h0 : ∀ a b, X a b ≠ 0) (hl : ∀ a a' b, X (a * a') b = X a b * X a' b)
    (hr : ∀ a b b', X a (b * b') = X a b * X a b')
    (hnd : ∀ a, (∀ b, X a b = 1) → a = 1) (c : Γ) :
    (∑ b, X c b) = if c = 1 then (Fintype.card Γ : K) else 0 := by
  split_ifs with hc
  · subst hc
    have h1 : ∀ b, X 1 b = 1 := by
      intro b
      have h := hl 1 1 b
      rw [one_mul] at h
      have hb := h0 1 b
      have : X 1 b * (X 1 b - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hb
      · exact sub_eq_zero.mp h'
    simp [h1]
  · obtain ⟨b₀, hb₀⟩ : ∃ b₀, X c b₀ ≠ 1 := by
      by_contra hne
      simp only [not_exists, ne_eq, not_not] at hne
      exact hc (hnd c hne)
    have hshift : (∑ b, X c b) = X c b₀ * ∑ b, X c b := by
      rw [Finset.mul_sum]
      simp_rw [← hr]
      exact (Equiv.sum_comp (Equiv.mulLeft b₀) (fun b => X c b)).symm
    have : (X c b₀ - 1) * ∑ b, X c b = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') hb₀
    · exact h'

theorem det_bicharacter_pow_four :
    ∀ (Γ K : Type) [CommGroup Γ] [Fintype Γ] [DecidableEq Γ] [Field K] (X : Γ → Γ → K), (∀ a b, X a b ≠ 0) → (∀ a a' b, X (a * a') b = X a b * X a' b) → (∀ a b b', X a (b * b') = X a b * X a b') → (∀ a, (∀ b, X a b = 1) → a = 1) → (Matrix.of X).det ^ 4 = (Fintype.card Γ : K) ^ (2 * Fintype.card Γ) := by
  intro Γ K _ _ _ _ X h0 hl hr hnd
  set M : Matrix Γ Γ K := Matrix.of X with hM
  have hMP : M * Matrix.transpose (M.submatrix (Equiv.inv Γ) id) = (Fintype.card Γ : K) • (1 : Matrix Γ Γ K) := by
    ext a a'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq, hM,
      Matrix.of_apply, Equiv.inv_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    simp_rw [← hl]
    rw [sum_pairing_eq_card_ite_one X h0 hl hr hnd]
    by_cases h : a = a'
    · subst h; simp
    · have : a * a'⁻¹ ≠ 1 := fun e => h (mul_inv_eq_one.mp e)
      simp [h, this]
  have hdet := congrArg Matrix.det hMP
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_permute, Matrix.det_smul, Matrix.det_one,
    mul_one] at hdet
  have hs : ((Equiv.Perm.sign (Equiv.inv Γ) : ℤ) : K) ^ 2 = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.inv Γ)) with e | e <;> simp [e]
  calc M.det ^ 4 = (M.det * (((Equiv.Perm.sign (Equiv.inv Γ) : ℤ) : K) * M.det)) ^ 2 := by
        rw [mul_pow, mul_pow, hs]; ring
    _ = (Fintype.card Γ : K) ^ (2 * Fintype.card Γ) := by rw [hdet, ← pow_mul, mul_comm]

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

namespace TameFlat

open TensorProduct

theorem flat_of_retraction {A B R : Type} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup R] [Module A R] (e : B →ₗ[A] A) (he : e 1 = 1)
    [Module.Flat B (B ⊗[A] R)] : Module.Flat A R := by
  classical
  rw [Module.Flat.iff_rTensor_injective']
  intro I

  have hmem : ∀ z ∈ I.map (algebraMap A B), ∀ c : B, e (c * z) ∈ I := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      intro c
      rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
      exact I.mul_mem_right _ ha
    | zero => intro c; simp
    | add x y _ _ hx hy => intro c; rw [mul_add, map_add (f := _)]; exact I.add_mem (hx c) (hy c)
    | smul d x _ hx => intro c; rw [smul_eq_mul, ← mul_assoc]; exact hx (c * d)
  set J : Ideal B := I.map (algebraMap A B)

  let eJ : J →ₗ[A] I := LinearMap.codRestrict (I.restrictScalars A)
    (e ∘ₗ J.subtype.restrictScalars A) (fun z => by simpa using hmem z z.2 1)
  have heJ : eJ ∘ₗ Algebra.idealMap B I = LinearMap.id := by
    ext i
    change e (algebraMap A B (i : A)) = (i : A)
    rw [Algebra.algebraMap_eq_smul_one, map_smul, he, smul_eq_mul, mul_one]

  let Φ : I ⊗[A] R →ₗ[A] J ⊗[B] (B ⊗[A] R) :=
    (AlgebraTensorModule.cancelBaseChange A B B J R).symm.toLinearMap.restrictScalars A ∘ₗ
      TensorProduct.map (Algebra.idealMap B I) LinearMap.id
  let Ψ : J ⊗[B] (B ⊗[A] R) →ₗ[A] I ⊗[A] R :=
    TensorProduct.map eJ LinearMap.id ∘ₗ
      (AlgebraTensorModule.cancelBaseChange A B B J R).toLinearMap.restrictScalars A
  have hΨΦ : ∀ x, Ψ (Φ x) = x := by
    intro x
    have : Ψ ∘ₗ Φ = LinearMap.id := by
      apply TensorProduct.ext'
      intro i r
      simp only [Ψ, Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [← LinearMap.comp_apply eJ, heJ, LinearMap.id_apply]
    exact congrArg (fun f => f x) this
  have hinc : Function.Injective (LinearMap.rTensor (B ⊗[A] R) J.subtype) :=
    Module.Flat.iff_rTensor_injective'.mp inferInstance J

  have hkey : ∀ x, TensorProduct.lid B (B ⊗[A] R) (LinearMap.rTensor (B ⊗[A] R) J.subtype (Φ x)) =
      (1 : B) ⊗ₜ[A] TensorProduct.lid A R (LinearMap.rTensor R I.subtype x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul i r =>
      simp only [Φ, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
        AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.rTensor_tmul,
        Submodule.subtype_apply, TensorProduct.lid_tmul]
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      change algebraMap A B (i : A) ⊗ₜ[A] r = _
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, TensorProduct.tmul_add]
  intro x y hxy
  have h1 : Φ x = Φ y := by
    apply hinc
    apply (TensorProduct.lid B (B ⊗[A] R)).injective
    rw [hkey, hkey, hxy]
  rw [← hΨΦ x, ← hΨΦ y, h1]

theorem exists_retraction {Γ A B : Type} [Group Γ] [Finite Γ] [CommRing A] [CommRing B]
    [MulSemiringAction Γ B] [Algebra A B] [SMulCommClass Γ A B] [Algebra.IsInvariant A B Γ]
    (hinj : Function.Injective (algebraMap A B)) (b : B) (hb : ∑ᶠ g : Γ, g • b = 1) :
    ∃ e : B →ₗ[A] A, e 1 = 1 := by
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  rw [finsum_eq_sum_of_fintype] at hb
  have hfix : ∀ x : B, ∃ a : A, algebraMap A B a = ∑ g : Γ, g • (b * x) := by
    intro x
    apply Algebra.IsInvariant.isInvariant (G := Γ)
    intro h
    rw [Finset.smul_sum]
    simp_rw [← mul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft h) (fun g => g • (b * x))
  choose f hf using hfix
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply hinj
    rw [map_add (f := _), hf, hf, hf, ← Finset.sum_add_distrib]
    simp_rw [mul_add, smul_add]
  · intro a x
    apply hinj
    rw [RingHom.id_apply, smul_eq_mul, map_mul, hf, hf, ← Algebra.smul_def, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [mul_smul_comm, smul_comm]
  · show f 1 = 1
    apply hinj
    rw [hf, mul_one, map_one, hb]

end TameFlat

theorem flat_of_tame_descent :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B R C : Type) [CommRing A] [CommRing B] [CommRing R]
      [CommRing C] [MulSemiringAction Γ B] [MulSemiringAction Γ C] [Algebra A B] [Algebra A R]
      [Algebra B C] [Algebra R C] [Algebra A C] [IsScalarTower A B C] [IsScalarTower A R C]
      [SMulCommClass Γ A B] [SMulCommClass Γ R C] [Algebra.IsInvariant A B Γ]
      [Algebra.IsInvariant R C Γ], Function.Injective (algebraMap A B) →
      Function.Injective (algebraMap R C) →
      (∀ (g : Γ) (b : B), g • algebraMap B C b = algebraMap B C (g • b)) →
      Algebra.IsPushout A B R C → Module.Flat B C → (∃ b : B, ∑ᶠ g : Γ, g • b = 1) →
      Module.Flat A R := by
  intro Γ _ _ A B R C
  intros
  rename_i hAB _ _ hpo hflat htr
  obtain ⟨b, hb⟩ := htr
  obtain ⟨e, he⟩ := TameFlat.exists_retraction (Γ := Γ) (A := A) hAB b hb
  have : Module.Flat B (B ⊗[A] R) := Module.Flat.of_linearEquiv hpo.out.equiv
  exact TameFlat.flat_of_retraction e he

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem isBezout_of_flat_of_formallyUnramified (W B : Type) [CommRing W] [IsDomain W] [IsBezout W]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra W B] [Module.Flat W B]
    [Algebra.EssFiniteType W B] [Algebra.FormallyUnramified W B] : IsBezout B := by
  refine ⟨fun J hJ => ?_⟩
  have hfin : Module.Finite B J := Module.Finite.iff_fg.2 hJ
  have htB : Submodule.torsion W B = ⊥ :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.1 inferInstance
  have hW : Module.Flat W J := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨a, ha⟩
    have hx : (x : B) ∈ Submodule.torsion W B := ⟨a, congrArg Subtype.val ha⟩
    rw [htB, Submodule.mem_bot] at hx
    exact (Submodule.mem_bot W).2 (Subtype.ext hx)
  have hB : Module.Flat B J := Algebra.FormallyUnramified.flat_of_restrictScalars W B J
  have hfree : Module.Free B J := Module.free_of_flat_of_isLocalRing
  rw [← Submodule.rank_le_one_iff_isPrincipal]
  exact (Submodule.rank_le J).trans (Module.rank_self B).le

theorem isAlgebraic_of_flat_of_formallyUnramified (W B : Type) [CommRing W] [IsDomain W]
    [CommRing B] [Algebra W B] [Module.Flat W B]
    [Algebra.EssFiniteType W B] [Algebra.FormallyUnramified W B] : Algebra.IsAlgebraic W B := by
  let K := FractionRing W
  have hfin : Module.Finite K (K ⊗[W] B) := Algebra.FormallyUnramified.finite_of_free K _
  have halg : Algebra.IsAlgebraic K (K ⊗[W] B) := inferInstance
  have hK : Algebra.IsAlgebraic W K := IsLocalization.isAlgebraic K (nonZeroDivisors W)
  have halgW : Algebra.IsAlgebraic W (K ⊗[W] B) := Algebra.IsAlgebraic.trans W K _
  exact Algebra.IsAlgebraic.of_injective
    (Algebra.TensorProduct.includeRight (R := W) (A := K) (B := B))
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective W K))

theorem valuationRing_of_flat_of_formallyUnramified :
    ∀ (W B : Type) [CommRing W] [IsDomain W] [ValuationRing W] [CommRing B] [IsDomain B]
      [IsLocalRing B] [Algebra W B] [Module.Flat W B] [Algebra.EssFiniteType W B]
      [Algebra.FormallyUnramified W B], ValuationRing B ∧ Algebra.IsAlgebraic W B := by
  intro W B _ _ _ _ _ _ _ _ _ _
  have := isBezout_of_flat_of_formallyUnramified W B
  exact ⟨inferInstance, isAlgebraic_of_flat_of_formallyUnramified W B⟩

end GlobalTheory
end
