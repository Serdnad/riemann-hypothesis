module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem sum_char_dot_eq_zero {B : Type} [CommRing B] [Fintype B] (χ : AddChar B ℂ)
    (hχ : χ.IsPrimitive) {m : ℕ} (t : Fin m → B) (ht : t ≠ 0) :
    ∑ s : Fin m → B, χ (∑ a, s a * t a) = 0 := by
  let f : (Fin m → B) →+ B :=
    { toFun := fun s => ∑ a, s a * t a
      map_zero' := by simp
      map_add' := fun s s' => by simp [add_mul, Finset.sum_add_distrib] }
  have h : χ.compAddMonoidHom f ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := Function.ne_iff.1 ht
    refine hχ ha ?_
    ext r
    have h1 := DFunLike.congr_fun h0 (Pi.single a r)
    simpa [f, Pi.single_apply, mul_comm] using h1
  exact AddChar.sum_eq_zero_iff_ne_zero.2 h

theorem exists_dot_eq_of_indep {B : Type} [CommRing B] [Fintype B] (χ : AddChar B ℂ)
    (hχ : χ.IsPrimitive) {k n : ℕ} (x : Fin k → Fin n → B)
    (hx : ∀ s : Fin k → B, ∑ a, s a • x a = 0 → s = 0) (u : Fin k → B) :
    ∃ z : Fin n → B, ∀ a, ∑ i, x a i * z i = u a := by
  by_contra hne
  push_neg at hne
  have h1 : ∑ z : Fin n → B, ∑ s : Fin k → B, χ (∑ a, s a * (∑ i, x a i * z i - u a)) = 0 := by
    refine Finset.sum_eq_zero fun z _ => ?_
    refine sum_char_dot_eq_zero χ hχ (fun a => ∑ i, x a i * z i - u a) ?_
    obtain ⟨a, ha⟩ := hne z
    intro h0
    exact ha (sub_eq_zero.1 (congrFun h0 a))
  rw [Finset.sum_comm, Finset.sum_eq_single (0 : Fin k → B)] at h1
  · simp at h1
  · intro s _ hs
    have h2 : ∀ z : Fin n → B, χ (∑ a, s a * (∑ i, x a i * z i - u a)) =
        χ (∑ i, z i * (∑ a, s a • x a) i) * χ (-∑ a, s a * u a) := by
      intro z
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, sub_eq_add_neg, mul_add, Finset.sum_add_distrib, mul_neg,
        Finset.sum_neg_distrib]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
      ring
    simp only [h2]
    rw [← Finset.sum_mul, sum_char_dot_eq_zero χ hχ _ (fun h => hs (hx s h)), zero_mul]
  · simp

theorem prim_of_indep_of_isPrimitive : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B),
    (∀ u, c (c u) = u) → ∀ (χ : AddChar B ℂ), χ.IsPrimitive →
    ∀ (k n : ℕ) (x : Fin k → Fin n → B),
      (∀ s : Fin k → B, ∑ a, s a • x a = 0 → s = 0) → Prim c x := by
  intro B _ _ c hc χ hχ k n x hx
  choose z hz using fun b : Fin k => exists_dot_eq_of_indep χ hχ x hx (Pi.single b 1)
  refine ⟨fun b i => c (z b i), fun a b => ?_⟩
  simp only [ip, hc]
  rw [hz, Pi.single_apply]

end GlobalTheory.GramCount
end

section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem sum_char_unit_mul_ip_eq_zero {B : Type} [CommRing B] [Fintype B] (c : B →+* B)
    (hc : ∀ u, c (c u) = u) (χ : AddChar B ℂ) (hχ : χ.IsPrimitive) {n : ℕ} {s : B}
    (hs : IsUnit s) {z : Fin n → B} (hz : z ≠ 0) :
    ∑ y : Fin n → B, χ (s * ip c y z) = 0 := by
  let ψ : AddChar (Fin n → B) ℂ :=
    { toFun := fun y => χ (s * ip c y z)
      map_zero_eq_one' := by simp [ip_zero_left]
      map_add_eq_mul' := fun x y => by rw [ip_add_left, mul_add, AddChar.map_add_eq_mul] }
  have hψ : ψ ≠ 1 := by
    intro h
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
    have hne : s * c (z i) ≠ 0 := by
      intro h0
      have h1 : c (z i) = 0 := (hs.mul_right_eq_zero).1 h0
      apply hi
      have := congrArg c h1
      simpa [hc] using this
    apply hχ hne
    ext u
    have h2 : χ (s * ip c (Pi.single i u) z) = 1 := DFunLike.congr_fun h (Pi.single i u)
    have h3 : ip c (Pi.single i u) z = u * c (z i) := by
      unfold ip
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    rw [h3] at h2
    rw [AddChar.mulShift_apply, AddChar.one_apply, ← h2]
    congr 1
    ring
  exact AddChar.sum_eq_zero_of_ne_one hψ

theorem norm_gauss_sum_ip_le {B : Type} [CommRing B] [Fintype B] (c : B →+* B)
    (hc : ∀ u, c (c u) = u) (q : ℕ) (_hq : 2 ≤ q) (hB : Fintype.card B = q ^ 2)
    (χ : AddChar B ℂ) (hχ : χ.IsPrimitive) (hinv : ∀ u, χ (c u) = χ u) (n : ℕ) (a : B)
    (ha : IsUnit (a + c a)) (v : Fin n → B) :
    ‖∑ y : Fin n → B, χ (a * ip c y y + ip c y v)‖ ≤ (q : ℝ) ^ n := by
  set Q : (Fin n → B) → B := fun y => a * ip c y y + ip c y v with hQ
  set S : ℂ := ∑ y : Fin n → B, χ (Q y) with hS
  have key : ∀ y z : Fin n → B,
      χ (Q (y + z)) * (starRingEnd ℂ) (χ (Q y)) = χ (Q z) * χ ((a + c a) * ip c y z) := by
    intro y z
    have h1 : χ (a * ip c z y) = χ (c a * ip c y z) := by
      rw [← hinv, map_mul, cj_ip c hc]
    have h2 : Q (y + z) + -Q y = Q z + a * ip c y z + a * ip c z y := by
      simp only [hQ, ip_add_left, ip_add_right]
      ring
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, h2, AddChar.map_add_eq_mul, h1,
      add_mul, AddChar.map_add_eq_mul χ (Q z), AddChar.map_add_eq_mul χ (a * ip c y z), mul_assoc]
  have hsq : S * (starRingEnd ℂ) S = (((q : ℝ) ^ n) ^ 2 : ℝ) := by
    calc S * (starRingEnd ℂ) S
        = ∑ y : Fin n → B, S * (starRingEnd ℂ) (χ (Q y)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            conv_lhs => rw [hS, map_sum, ← hS, Finset.mul_sum]
      _ = ∑ y : Fin n → B, ∑ z : Fin n → B, χ (Q z) * χ ((a + c a) * ip c y z) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hS, ← Equiv.sum_comp (Equiv.addLeft y), Finset.sum_mul]
          exact Finset.sum_congr rfl fun z _ => key y z
      _ = ∑ z : Fin n → B, χ (Q z) * ∑ y : Fin n → B, χ ((a + c a) * ip c y z) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ = (((q : ℝ) ^ n) ^ 2 : ℝ) := by
          rw [Finset.sum_eq_single (0 : Fin n → B)]
          · simp [hQ, ip_zero_left, ip_zero_right, hB, ← pow_mul, mul_comm]
          · intro z _ hz
            rw [sum_char_unit_mul_ip_eq_zero c hc χ hχ ha hz, mul_zero]
          · simp
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hsq
  have h3 : ‖S‖ ^ 2 = ((q : ℝ) ^ n) ^ 2 := by exact_mod_cast hsq
  exact ((pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3).le

end GlobalTheory.GramCount
end

section

open Matrix

namespace GlobalTheory

theorem dual_vectors_in_second_flag : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {r j : ℕ} (hj : j ≤ r) (e e' s : Fin r → V),
    (Matrix.of fun a b : Fin j => H.B (e (Fin.castLE hj a)) (e' (Fin.castLE hj b))).det ≠ 0 →
    (∀ a b, H.B (e' a) (e' b) = 0) →
    (∀ a b : Fin r, j ≤ a.val → b.val < j → H.B (e a) (e' b) = 0) →
    (∀ a b : Fin r, j ≤ b.val → H.B (e a) (s b) = if a = b then 1 else 0) →
    (∀ a b : Fin r, a.val < j → j ≤ b.val → H.B (e' a) (s b) = 0) →
    (∀ a b : Fin r, j ≤ a.val → j ≤ b.val → H.B (s a) (s b) = 0) →
    ∃ f : Fin r → V, (∀ a, j ≤ a.val → f a = s a) ∧
      (∀ a, a.val < j → f a ∈ Submodule.span K (e' '' {b | b.val < j})) ∧
      (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) ∧ (∀ a b, H.B (f a) (f b) = 0) ∧
      (∀ a, a.val < j → e' a ∈ Submodule.span K (f '' {b | b.val < j})) := by
  intro K V _ _ _ _ H r j hj e e' s hdet he' hz hs he's hss
  set P : Matrix (Fin j) (Fin j) K := Matrix.of fun a b : Fin j => H.B (e (Fin.castLE hj a)) (e' (Fin.castLE hj b)) with hPdef
  have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
  have hPQ : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hu
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hu
  have hR : ∀ (x : V) (g : Fin j → K), H.B x (∑ c, g c • e' (Fin.castLE hj c)) = ∑ c, star (g c) * H.B x (e' (Fin.castLE hj c)) := by
    intro x g; simp [map_sum, map_smulₛₗ, starRingEnd_apply]
  have hL : ∀ (y : V) (g : Fin j → K), H.B (∑ c, g c • e' (Fin.castLE hj c)) y = ∑ c, g c * H.B (e' (Fin.castLE hj c)) y := by
    intro y g; simp [map_sum, LinearMap.sum_apply]
  let f : Fin r → V := fun b => if h : b.val < j then ∑ c : Fin j, star (P⁻¹ c ⟨b.val, h⟩) • e' (Fin.castLE hj c) else s b
  have hf : ∀ b : Fin j, f (Fin.castLE hj b) = ∑ c, star (P⁻¹ c b) • e' (Fin.castLE hj c) := fun b => by
    simp [f]
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha; simp [f, Nat.not_lt.mpr ha]
  · intro a ha
    simp only [f, dif_pos ha]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castLE hj c, c.isLt, rfl⟩)
  · intro a b
    by_cases hb : b.val < j
    · simp only [f, dif_pos hb, hR, star_star]
      by_cases ha : a.val < j
      · calc ∑ c, P⁻¹ c ⟨b.val, hb⟩ * H.B (e a) (e' (Fin.castLE hj c))
            = ∑ c, P ⟨a.val, ha⟩ c * P⁻¹ c ⟨b.val, hb⟩ := by
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [mul_comm]; rfl
          _ = (P * P⁻¹) ⟨a.val, ha⟩ ⟨b.val, hb⟩ := by rw [Matrix.mul_apply]
          _ = if a = b then 1 else 0 := by rw [hPQ, Matrix.one_apply]; simp [Fin.ext_iff]
      · rw [Finset.sum_eq_zero]
        · have : a ≠ b := fun h => ha (h ▸ hb)
          simp [this]
        intro c _
        rw [hz a (Fin.castLE hj c) (Nat.not_lt.mp ha) (by simp), mul_zero]
    · simp only [f, dif_neg hb]; exact hs a b (Nat.not_lt.mp hb)
  · intro a b
    by_cases ha : a.val < j <;> by_cases hb : b.val < j
    · simp only [f, dif_pos ha, dif_pos hb, hL, hR, he', mul_zero, Finset.sum_const_zero]
    · simp only [f, dif_pos ha, dif_neg hb, hL]
      exact Finset.sum_eq_zero fun c _ => by rw [he's _ _ (by simp) (Nat.not_lt.mp hb), mul_zero]
    · simp only [f, dif_neg ha, dif_pos hb, hR]
      exact Finset.sum_eq_zero fun c _ => by rw [← H.herm, he's _ _ (by simp) (Nat.not_lt.mp ha), star_zero, mul_zero]
    · simp only [f, dif_neg ha, dif_neg hb]; exact hss a b (Nat.not_lt.mp ha) (Nat.not_lt.mp hb)
  · intro a ha
    have key : e' a = ∑ b : Fin j, star (P b ⟨a.val, ha⟩) • f (Fin.castLE hj b) := by
      calc e' a = ∑ c, star ((1 : Matrix (Fin j) (Fin j) K) c ⟨a.val, ha⟩) • e' (Fin.castLE hj c) := by
              simp [Matrix.one_apply, apply_ite star]
        _ = ∑ c, star ((P⁻¹ * P) c ⟨a.val, ha⟩) • e' (Fin.castLE hj c) := by rw [hQP]
        _ = ∑ b, star (P b ⟨a.val, ha⟩) • ∑ c, star (P⁻¹ c b) • e' (Fin.castLE hj c) := by
              simp_rw [Matrix.mul_apply, star_sum, Finset.sum_smul, Finset.smul_sum, smul_smul, star_mul]
              rw [Finset.sum_comm]
        _ = ∑ b, star (P b ⟨a.val, ha⟩) • f (Fin.castLE hj b) := by simp_rw [hf]
    rw [key]
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castLE hj b, b.isLt, rfl⟩)

end GlobalTheory
end

section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory

namespace NearUnitaryExp

open scoped Matrix.Norms.Frobenius

theorem norm_exp_sub_one_le_exp_norm {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (x : A) : ‖NormedSpace.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have hx := (hasSum_nat_add_iff' 1).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x)
  have hr := (hasSum_nat_add_iff' 1).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  rw [← Real.exp_eq_exp_ℝ] at hr
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_smul] at hx hr
  refine hx.norm_le_of_bounded hr fun m => ?_
  rw [norm_smul, smul_eq_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' x (Nat.succ_pos m)) (by positivity)

variable {n : ℕ}

theorem sqrt_hs_eq_norm (A : Matrix (Fin n) (Fin n) ℂ) : Real.sqrt (hs A) = ‖A‖ := by
  rw [frobenius_norm_def, Real.sqrt_eq_rpow, hs]
  simp only [Real.rpow_two]

theorem hs_nonneg' (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm_sq_eq_hs (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ ^ 2 = hs A := by
  rw [← sqrt_hs_eq_norm, Real.sq_sqrt (hs_nonneg' A)]

private lemma re_star_mul_self_eq_norm_sq (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

theorem hs_eq_re_trace (g : Matrix (Fin n) (Fin n) ℂ) : hs g = (trace (gᴴ * g)).re := by
  simp only [hs, trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum,
    re_star_mul_self_eq_norm_sq]
  exact Finset.sum_comm

theorem norm_unitary_mul {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) : ‖k * A‖ = ‖A‖ := by
  have hk' : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  rw [← sqrt_hs_eq_norm, ← sqrt_hs_eq_norm, hs_eq_re_trace, hs_eq_re_trace, conjTranspose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k A, hk', Matrix.one_mul]

theorem norm_one_eq : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = Real.sqrt n := by
  rw [← sqrt_hs_eq_norm, hs_eq_re_trace]
  simp

theorem norm_trace_le (A : Matrix (Fin n) (Fin n) ℂ) : ‖A.trace‖ ≤ Real.sqrt n * ‖A‖ := by
  have hdiag : ∑ i, ‖A i i‖ ^ 2 ≤ hs A :=
    Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hsq : (∑ i, ‖A i i‖) ^ 2 ≤ (Real.sqrt n * ‖A‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), norm_sq_eq_hs]
    calc (∑ i, ‖A i i‖) ^ 2 ≤ (Finset.univ.card : ℝ) * ∑ i, ‖A i i‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ n * hs A := by
          rw [Finset.card_univ, Fintype.card_fin]
          exact mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg n)
  have h1 : ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
  have h2 : 0 ≤ ∑ i, ‖A i i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h3 : 0 ≤ Real.sqrt n * ‖A‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith

theorem hs_unitary_sub_one {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) : hs (k - 1) = 2 * n - 2 * k.trace.re := by
  have hk' : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  have hprod : (k - 1)ᴴ * (k - 1) = 1 + 1 - kᴴ - k := by
    rw [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hk',
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [hs_eq_re_trace, hprod, trace_sub, trace_sub, trace_add, trace_one, trace_conjTranspose,
    Complex.sub_re, Complex.sub_re, Complex.add_re, Complex.star_def, Complex.conj_re,
    Fintype.card_fin, Complex.natCast_re]
  ring

theorem norm_pow_le_of_unitary {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (E : Matrix (Fin n) (Fin n) ℂ) {c : ℝ}
    (hE : ‖E - 1‖ ≤ c - 1) (j : ℕ) : ‖(k * E) ^ j‖ ≤ c ^ j * Real.sqrt n := by
  induction j with
  | zero => rw [pow_zero, pow_zero, one_mul, norm_one_eq]
  | succ j ih =>
    have hsplit : E * (k * E) ^ j = (k * E) ^ j + (E - 1) * (k * E) ^ j := by
      rw [Matrix.sub_mul, Matrix.one_mul]
      abel
    rw [pow_succ', Matrix.mul_assoc, norm_unitary_mul hk, hsplit]
    have hm := frobenius_norm_mul (E - 1) ((k * E) ^ j)
    have hn0 := norm_nonneg ((k * E) ^ j)
    have hE0 := norm_nonneg (E - 1)
    calc ‖(k * E) ^ j + (E - 1) * (k * E) ^ j‖
        ≤ ‖(k * E) ^ j‖ + ‖(E - 1) * (k * E) ^ j‖ := norm_add_le _ _
      _ ≤ (1 + ‖E - 1‖) * ‖(k * E) ^ j‖ := by linarith
      _ ≤ c * (c ^ j * Real.sqrt n) := by
          apply mul_le_mul (by linarith) ih hn0 (by linarith)
      _ = c ^ (j + 1) * Real.sqrt n := by ring

theorem near_arch : ∀ (n : ℕ) (k X : Matrix (Fin n) (Fin n) ℂ) (ep : ℝ), k ∈ Matrix.unitaryGroup (Fin n) ℂ → X.IsHermitian → 0 ≤ ep → Real.sqrt (hs X) ≤ ep → n * ep ≤ 1 / 4 → (∀ j : ℕ, j ≤ n → ‖((k * NormedSpace.exp X) ^ j).trace - n‖ ≤ 3 * n) ∧ ((k * NormedSpace.exp X).trace = n → Real.sqrt (hs (k * NormedSpace.exp X - 1)) ≤ 3 * Real.sqrt (n * ep)) := by
  intro n k X ep hk _ hep hXe hne
  have hXn : ‖X‖ ≤ ep := by rwa [sqrt_hs_eq_norm] at hXe
  have hE1 : ‖NormedSpace.exp X - 1‖ ≤ Real.exp ep - 1 := by
    have h1 := norm_exp_sub_one_le_exp_norm X
    have h2 := Real.exp_le_exp.mpr hXn
    exact le_trans h1 (by linarith)
  generalize NormedSpace.exp X = E at hE1 ⊢
  have hpow := norm_pow_le_of_unitary hk E hE1
  have hq : Real.exp (1 / 4) ≤ 3 / 2 := by
    have h := Real.abs_exp_sub_one_le (x := 1 / 4) (by norm_num [abs_of_pos])
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at h
    linarith [le_abs_self (Real.exp (1 / 4) - 1)]
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  refine ⟨fun j hj => ?_, fun htr => ?_⟩
  · have hje : (j : ℝ) * ep ≤ 1 / 4 := by
      have : (j : ℝ) ≤ n := by exact_mod_cast hj
      nlinarith
    have hcj : Real.exp ep ^ j ≤ 3 / 2 := by
      rw [← Real.exp_nat_mul]
      exact (Real.exp_le_exp.mpr hje).trans hq
    have htr := norm_trace_le ((k * E) ^ j)
    have hb := hpow j
    have hs0 := Real.sqrt_nonneg (n : ℝ)
    have hbound : ‖((k * E) ^ j).trace‖ ≤ n * (3 / 2) := by
      calc ‖((k * E) ^ j).trace‖ ≤ Real.sqrt n * ‖(k * E) ^ j‖ := htr
        _ ≤ Real.sqrt n * (Real.exp ep ^ j * Real.sqrt n) := mul_le_mul_of_nonneg_left hb hs0
        _ = (Real.sqrt n * Real.sqrt n) * Real.exp ep ^ j := by ring
        _ = n * Real.exp ep ^ j := by rw [hsn]
        _ ≤ n * (3 / 2) := mul_le_mul_of_nonneg_left hcj (Nat.cast_nonneg n)
    calc ‖((k * E) ^ j).trace - n‖ ≤ ‖((k * E) ^ j).trace‖ + ‖(n : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 * n := by rw [Complex.norm_natCast]; linarith
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hs]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hs1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
    set s := Real.sqrt n with hs_def
    set t := Real.sqrt ep with ht_def
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have htt : t * t = ep := Real.mul_self_sqrt hep
    have hst : s * t ≤ 1 / 2 := by
      have : (s * t) * (s * t) ≤ 1 / 4 := by
        calc (s * t) * (s * t) = (s * s) * (t * t) := by ring
          _ = n * ep := by rw [hsn, htt]
          _ ≤ 1 / 4 := hne
      nlinarith
    have hep1 : ep ≤ 1 := by nlinarith
    have hdel : ‖E - 1‖ ≤ 2 * ep := by
      have h := Real.abs_exp_sub_one_le (x := ep) (by rw [abs_of_nonneg hep]; exact hep1)
      rw [abs_of_nonneg hep] at h
      linarith [le_abs_self (Real.exp ep - 1)]
    have hsplit : k * E = k + k * (E - 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
      abel
    have htrk : k.trace = n - (k * (E - 1)).trace := by
      rw [← htr, hsplit, trace_add]
      ring
    have hre : (n : ℝ) - s * ‖E - 1‖ ≤ k.trace.re := by
      have h1 := norm_trace_le (k * (E - 1))
      rw [norm_unitary_mul hk, ← hs_def] at h1
      have h2 := Complex.abs_re_le_norm (k * (E - 1)).trace
      rw [htrk, Complex.sub_re, Complex.natCast_re]
      linarith [le_abs_self (k * (E - 1)).trace.re]
    have hk1 : ‖k - 1‖ ^ 2 ≤ 4 * (s * t) ^ 2 := by
      rw [norm_sq_eq_hs, hs_unitary_sub_one hk]
      have hE0 := norm_nonneg (E - 1)
      have : s * ‖E - 1‖ ≤ s * (2 * (t * t)) := by
        rw [htt]; exact mul_le_mul_of_nonneg_left hdel (by linarith)
      nlinarith
    have hk1' : ‖k - 1‖ ≤ 2 * (s * t) := by
      have := norm_nonneg (k - 1)
      have hst0 : 0 ≤ s * t := mul_nonneg (by linarith) ht0
      nlinarith
    have hsum : k * E - 1 = (k - 1) + k * (E - 1) := by
      rw [hsplit]
      abel
    rw [sqrt_hs_eq_norm, Real.sqrt_mul (Nat.cast_nonneg n), hsum]
    calc ‖(k - 1) + k * (E - 1)‖ ≤ ‖k - 1‖ + ‖k * (E - 1)‖ := norm_add_le _ _
      _ ≤ 2 * (s * t) + 2 * (t * t) := by rw [norm_unitary_mul hk, htt]; linarith
      _ ≤ 3 * (s * t) := by nlinarith

end NearUnitaryExp

end GlobalTheory
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.ae_eq_of_dense_of_local_sq_bound_alt : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (K : ℕ → Set X),
    (∀ n, MeasurableSet (K n)) → ⋃ n, K n = Set.univ →
    ∀ {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : Set H), Dense D → ∀ P Q : H → X → E,
    (∀ u u', (fun x => P u x - P u' x) =ᵐ[μ] P (u - u')) →
    (∀ u u', (fun x => Q u x - Q u' x) =ᵐ[μ] Q (u - u')) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (P u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖P u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ n, ∃ C : ℝ, ∀ u, AEStronglyMeasurable (Q u) (μ.restrict (K n)) ∧
      ∫⁻ x in K n, (‖Q u x‖₊ : ENNReal) ^ 2 ∂μ ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ u ∈ D, P u =ᵐ[μ] Q u) → ∀ u, P u =ᵐ[μ] Q u := by
  first | exact @GlobalTheory.ae_eq_of_dense_of_local_sq_bound | exact GlobalTheory.ae_eq_of_dense_of_local_sq_bound | (intros; apply GlobalTheory.ae_eq_of_dense_of_local_sq_bound <;> assumption)
end
