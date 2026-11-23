module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle050
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ToMKExpKEqMatrixExpReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle052
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum.CasBasis

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem frame_Dw_sum (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {q : ℕ}
    (c : Fin q → ℂ) {x : Fin q → H} (hx : ∀ i, Sm ε σ (x i)) :
    Dw σ l (∑ i, c i • x i) = ∑ i, c i • Dw σ l (x i) := by
  obtain ⟨L, hL⟩ := exists_word (isUnit_Jm ε) hσ l hl
  have h := congrArg Subtype.val (map_sum L (fun i => c i • (⟨x i, hx i⟩ : smooth (Jm ε) σ)) Finset.univ)
  simp only [map_smul, hL, Submodule.coe_sum, Submodule.coe_smul] at h
  exact h

theorem frame_sm_sum {q : ℕ} (c : Fin q → ℂ) {x : Fin q → H} (hx : ∀ i, Sm ε σ (x i)) :
    Sm ε σ (∑ i, c i • x i) :=
  (smooth (Jm ε) σ).sum_mem fun i _ => (smooth (Jm ε) σ).smul_mem (c i) (hx i)

theorem frame_dRep2_sum (hσ : IsURepOn (UJset ε) σ) {X : Mx n} (hX : X ∈ lieSet ε) {q : ℕ}
    (c : Fin q → ℂ) {x : Fin q → H} (hx : ∀ i, Sm ε σ (x i)) :
    dRep σ X (dRep σ X (∑ i, c i • x i)) = ∑ i, c i • dRep σ X (dRep σ X (x i)) := by
  have := frame_Dw_sum hσ (l := [X, X]) (by simp [hX]) c hx
  simpa [Dw] using this

theorem frame_lapOne_sum (hσ : IsURepOn (UJset ε) σ) (hk : ∀ i, kB ε i ∈ lieSet ε) (hp : ∀ b, pB ε b ∈ lieSet ε)
    {q : ℕ} (c : Fin q → ℂ) {x : Fin q → H} (hx : ∀ i, Sm ε σ (x i)) :
    lapOne ε σ (∑ i, c i • x i) = ∑ i, c i • lapOne ε σ (x i) := by
  simp only [lapOne, onePlusCas, frame_dRep2_sum hσ (hk _) c hx, frame_dRep2_sum hσ (hp _) c hx,
    smul_sub, Finset.smul_sum, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (γ := Fin q), Finset.sum_comm (γ := Fin q)]

theorem frame_lapOne_eig {χ : ℂ}
    (hcas : ∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v))
    {e : H} (he : Sm ε σ e) {μ : ℝ} (h : onePlusCas σ (kB ε) e = (μ : ℂ) • e) :
    lapOne ε σ e = (((2 * μ : ℝ) : ℂ) - (1 + χ)) • e := by
  have hs : ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) e) = e - (μ : ℂ) • e := by
    rw [← h, onePlusCas]; abel
  rw [lapOne, hcas e he, hs, h]
  push_cast
  module

end GlobalTheory.TypeSum.CasBasis

namespace GlobalTheory.TypeSum.CasBasis

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem frame_iterate (hσ : IsURepOn (UJset ε) σ) (hk : ∀ i, kB ε i ∈ lieSet ε) (hp : ∀ b, pB ε b ∈ lieSet ε)
    {q : ℕ} {e : Fin q → H} (he : ∀ j, Sm ε σ (e j)) (c : Fin q → ℂ) (hc : ∀ j, lapOne ε σ (e j) = c j • e j)
    (r : ℕ) (b : Fin q → ℂ) :
    (lapOne ε σ)^[r] (∑ j, b j • e j) = ∑ j, (b j * c j ^ r) • e j := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, frame_lapOne_sum hσ hk hp _ he]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc, smul_smul, pow_succ, mul_assoc]

theorem frame_norm_sq {q : ℕ} {e : Fin q → H} (ho : Orthonormal ℂ e) (d : Fin q → ℂ) :
    ‖∑ j, d j • e j‖ ^ 2 = ∑ j, ‖d j‖ ^ 2 := by
  have h := ho.inner_sum d d Finset.univ
  rw [@norm_sq_eq_re_inner ℂ, h]

  simp only [Complex.conj_mul', map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.re_to_complex]
  norm_cast

end GlobalTheory.TypeSum.CasBasis

namespace GlobalTheory.TypeSum.CasBasis

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem frame_coef_bound (χ : ℂ) {μ : ℝ} (hμ : 1 ≤ μ) {s₀ s : ℕ} (hs : s₀ ≤ s) (z : ℂ) :
    ‖((((μ ^ s)⁻¹ : ℝ) : ℂ) * z) * (((2 * μ : ℝ) : ℂ) - (1 + χ)) ^ s₀‖ ≤ (2 + ‖1 + χ‖) ^ s₀ * ‖z‖ := by
  have hc : ‖((2 * μ : ℝ) : ℂ) - (1 + χ)‖ ≤ (2 + ‖1 + χ‖) * μ := by
    calc ‖((2 * μ : ℝ) : ℂ) - (1 + χ)‖ ≤ ‖((2 * μ : ℝ) : ℂ)‖ + ‖1 + χ‖ := norm_sub_le _ _
      _ = 2 * μ + ‖1 + χ‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      _ ≤ _ := by nlinarith [norm_nonneg (1 + χ)]
  have hμs : 0 < μ ^ s := pow_pos (by linarith) _
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 hμs.le)]
  have h1 : ‖((2 * μ : ℝ) : ℂ) - (1 + χ)‖ ^ s₀ ≤ ((2 + ‖1 + χ‖) * μ) ^ s₀ := pow_le_pow_left₀ (norm_nonneg _) hc s₀
  have h2 : μ ^ s₀ ≤ μ ^ s := pow_le_pow_right₀ hμ hs
  have hK : 0 ≤ (2 + ‖1 + χ‖) ^ s₀ := by positivity
  rw [mul_pow] at h1
  calc (μ ^ s)⁻¹ * ‖z‖ * ‖((2 * μ : ℝ) : ℂ) - (1 + χ)‖ ^ s₀
      ≤ (μ ^ s)⁻¹ * ‖z‖ * ((2 + ‖1 + χ‖) ^ s₀ * μ ^ s₀) := by gcongr
    _ ≤ (μ ^ s)⁻¹ * ‖z‖ * ((2 + ‖1 + χ‖) ^ s₀ * μ ^ s) := by gcongr
    _ = (2 + ‖1 + χ‖) ^ s₀ * ‖z‖ := by field_simp

theorem frame_word (hσ : IsURepOn (UJset ε) σ) (hKS : ∀ v, IsKFin ε σ v → Sm ε σ v)
    (hk : ∀ i, kB ε i ∈ lieSet ε) (hp : ∀ b, pB ε b ∈ lieSet ε) {χ : ℂ}
    (hcas : ∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v))
    {m : List (Mx n)} (hm : ∀ X ∈ m, X ∈ lieSet ε) {s₀ : ℕ} {C₀ : ℝ}
    (hest : ∀ v, Sm ε σ v → ‖Dw σ m v‖ ≤ C₀ * ‖(lapOne ε σ)^[s₀] v‖) {s : ℕ} (hs : s₀ ≤ s)
    {q : ℕ} {e : Fin q → H} {μ : Fin q → ℝ} (ho : Orthonormal ℂ e) (hkf : ∀ i, IsKFin ε σ (e i))
    (hμ : ∀ i, 1 ≤ μ i) (heig : ∀ i, onePlusCas σ (kB ε) (e i) = (μ i : ℂ) • e i) (z : Fin q → ℂ) :
    ‖∑ j, ((((μ j ^ s)⁻¹ : ℝ) : ℂ) * z j) • Dw σ m (e j)‖ ^ 2 ≤
      (max C₀ 0 ^ 2 * (2 + ‖1 + χ‖) ^ (2 * s₀)) * ∑ j, ‖z j‖ ^ 2 := by
  have he : ∀ j, Sm ε σ (e j) := fun j => hKS _ (hkf j)
  have hc : ∀ j, lapOne ε σ (e j) = (fun j => ((2 * μ j : ℝ) : ℂ) - (1 + χ)) j • e j := fun j =>
    frame_lapOne_eig hcas (he j) (heig j)
  rw [← frame_Dw_sum hσ hm _ he]
  have h1 := hest _ (frame_sm_sum (fun j => (((μ j ^ s)⁻¹ : ℝ) : ℂ) * z j) he)
  rw [frame_iterate hσ hk hp he _ hc s₀] at h1
  have h2 := h1.trans (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (norm_nonneg _))
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow, frame_norm_sq ho] at h3
  refine h3.trans ?_
  rw [mul_assoc (max C₀ 0 ^ 2), Finset.mul_sum Finset.univ (fun j => ‖z j‖ ^ 2) ((2 + ‖1 + χ‖) ^ (2 * s₀))]
  gcongr with j
  have := frame_coef_bound χ (hμ j) hs (z j)
  calc _ ≤ ((2 + ‖1 + χ‖) ^ s₀ * ‖z j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = _ := by ring

end GlobalTheory.TypeSum.CasBasis

namespace GlobalTheory.TypeSum.CasBasis

theorem frame_bounded : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → (∀ i, kB ε i ∈ lieSet ε) → (∀ b, pB ε b ∈ lieSet ε) → ∀ χ : ℂ, (∀ v, Sm ε σ v → ∑ b, dRep σ (pB ε b) (dRep σ (pB ε b) v) = χ • v + ∑ i, dRep σ (kB ε i) (dRep σ (kB ε i) v)) → (∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∃ (s : ℕ) (C : ℝ), ∀ v, Sm ε σ v → ‖Dw σ l v‖ ≤ C * ‖(lapOne ε σ)^[s] v‖) → ∀ T : List (List (Mx n)), Words (lieSet ε) T → ∃ (s : ℕ) (C : ℝ), ∀ m ∈ T, ∀ (q : ℕ) (e : Fin q → H) (μ : Fin q → ℝ), Orthonormal ℂ e → (∀ i, IsKFin ε σ (e i)) → (∀ i, 1 ≤ μ i) → (∀ i, onePlusCas σ (kB ε) (e i) = (μ i : ℂ) • e i) → ∀ z : Fin q → ℂ, ‖∑ j, ((((μ j ^ s)⁻¹ : ℝ) : ℂ) * z j) • Dw σ m (e j)‖ ^ 2 ≤ C * ∑ j, ‖z j‖ ^ 2 := by
  intro n ε H _ _ _ σ hstd hk hp χ hcas hell T hT
  have hσ := hstd.1
  have hKS := hstd.2.2.1
  have key : ∀ T : List (List (Mx n)), Words (lieSet ε) T → ∃ (s : ℕ) (C : ℝ), ∀ m ∈ T, ∃ (s₀ : ℕ) (C₀ : ℝ),
      s₀ ≤ s ∧ (∀ v, Sm ε σ v → ‖Dw σ m v‖ ≤ C₀ * ‖(lapOne ε σ)^[s₀] v‖) ∧
        max C₀ 0 ^ 2 * (2 + ‖1 + χ‖) ^ (2 * s₀) ≤ C := by
    intro T
    induction T with
    | nil => intro _; exact ⟨0, 0, by simp⟩
    | cons m T ih =>
      intro hT
      obtain ⟨s₁, C₁, h₁⟩ := ih (fun l hl => hT l (List.mem_cons_of_mem _ hl))
      obtain ⟨s₀, C₀, h₀⟩ := hell m (hT m List.mem_cons_self)
      refine ⟨max s₀ s₁, max (max C₀ 0 ^ 2 * (2 + ‖1 + χ‖) ^ (2 * s₀)) C₁, fun l hl => ?_⟩
      rcases List.mem_cons.1 hl with rfl | hl
      · exact ⟨s₀, C₀, le_max_left _ _, h₀, le_max_left _ _⟩
      · obtain ⟨s', C', hs', he', hC'⟩ := h₁ l hl
        exact ⟨s', C', hs'.trans (le_max_right _ _), he', hC'.trans (le_max_right _ _)⟩
  obtain ⟨s, C, hsC⟩ := key T hT
  refine ⟨s, C, fun m hm q e μ ho hkf hμ heig z => ?_⟩
  obtain ⟨s₀, C₀, hs, hest, hC⟩ := hsC m hm
  exact (frame_word hσ hKS hk hp hcas (hT m hm) hest hs ho hkf hμ heig z).trans
    (mul_le_mul_of_nonneg_right hC (Finset.sum_nonneg fun j _ => by positivity))

end GlobalTheory.TypeSum.CasBasis

end
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined

noncomputable section

namespace GlobalTheory.TypeSum.CasBasis.KOrth

theorem trE {n : ℕ} (a b c d : Fin n) : trace (unitE a b * unitE c d) = if b = c ∧ a = d then 1 else 0 := by
  simp only [unitE]
  by_cases h : b = c
  · subst h; rw [Matrix.single_mul_single_same]
    by_cases h2 : a = d
    · subst h2; simp
    · simp [h2, Matrix.trace_single_eq_of_ne _ _ _ h2]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ h]; simp [h]

theorem s2 : invSqrtTwo * invSqrtTwo = 1/2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

theorem mem_pairs_lt {n : ℕ} {ε : Fin n → Bool} {s : Bool} {p : Fin n × Fin n} (h : p ∈ pairs ε s) : p.1 < p.2 := by
  simp only [pairs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.1

theorem nodup_pairs {n : ℕ} (ε : Fin n → Bool) (s : Bool) : (pairs ε s).Nodup :=
  ((List.nodup_finRange n).product (List.nodup_finRange n)).filter _

section
variable {n : ℕ}

theorem d_self (a : Fin n) : trace ((Complex.I • unitE a a) * (Complex.I • unitE a a)) = -1 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, trE]; simp

theorem d_ne {a b : Fin n} (h : a ≠ b) : trace ((Complex.I • unitE a a) * (Complex.I • unitE b b)) = 0 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, trE]; simp [h]

theorem trace_casimirAntisymPair_mul_self {a b : Fin n} (h : a < b) :
    trace ((invSqrtTwo • (unitE a b - unitE b a)) * (invSqrtTwo • (unitE a b - unitE b a))) = -1 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.trace_sub, trE]
  simp only [h.ne, h.ne', and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
  linear_combination (-2 : ℂ) * s2

theorem trace_casimirSymPairI_mul_self {a b : Fin n} (h : a < b) :
    trace (((invSqrtTwo * Complex.I) • (unitE a b + unitE b a)) * ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a))) = -1 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.trace_add, trE]
  simp only [h.ne, h.ne', and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
  linear_combination (2 * invSqrtTwo * invSqrtTwo) * Complex.I_mul_I - (2 : ℂ) * s2

theorem p12 {a b : Fin n} (h : a < b) :
    trace ((invSqrtTwo • (unitE a b - unitE b a)) * ((invSqrtTwo * Complex.I) • (unitE a b + unitE b a))) = 0 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.sub_mul,
    Matrix.trace_add, Matrix.trace_sub, trE]
  simp only [h.ne, h.ne', and_self, and_false, false_and, if_true, if_false, smul_eq_mul]
  ring

theorem dp1 (a : Fin n) {b c : Fin n} (h : b < c) :
    trace ((Complex.I • unitE a a) * (invSqrtTwo • (unitE b c - unitE c b))) = 0 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sub, Matrix.trace_sub, trE]
  have h1 : ¬ (a = b ∧ a = c) := fun ⟨h1, h2⟩ => h.ne (h1 ▸ h2)
  have h2 : ¬ (a = c ∧ a = b) := fun ⟨h1, h2⟩ => h.ne (h2 ▸ h1)
  simp [h1, h2]

theorem dp2 (a : Fin n) {b c : Fin n} (h : b < c) :
    trace ((Complex.I • unitE a a) * ((invSqrtTwo * Complex.I) • (unitE b c + unitE c b))) = 0 := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add, trE]
  have h1 : ¬ (a = b ∧ a = c) := fun ⟨h1, h2⟩ => h.ne (h1 ▸ h2)
  have h2 : ¬ (a = c ∧ a = b) := fun ⟨h1, h2⟩ => h.ne (h2 ▸ h1)
  simp [h1, h2]

theorem pq_facts {p q : Fin n × Fin n} (hp : p.1 < p.2) (hq : q.1 < q.2) (hpq : p ≠ q) :
    ¬ (p.2 = q.1 ∧ p.1 = q.2) ∧ ¬ (p.2 = q.2 ∧ p.1 = q.1) ∧ ¬ (p.1 = q.1 ∧ p.2 = q.2) ∧
      ¬ (p.1 = q.2 ∧ p.2 = q.1) := by
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => hpq (Prod.ext h2 h1), fun ⟨h1, h2⟩ => hpq (Prod.ext h1 h2),
    fun ⟨h1, h2⟩ => ?_⟩
  · have := hp.trans_eq h1; have := hq.trans_eq h2.symm; exact absurd (hp.trans (h1 ▸ h2 ▸ hq)) (lt_irrefl _)
  · exact absurd (hp.trans (h2 ▸ h1 ▸ hq)) (lt_irrefl _)

end
end GlobalTheory.TypeSum.CasBasis.KOrth

namespace GlobalTheory.TypeSum.CasBasis.KOrth
variable {n : ℕ}

theorem pq_zero {p q : Fin n × Fin n} (hp : p.1 < p.2) (hq : q.1 < q.2) (hpq : p ≠ q) :
    ∀ X ∈ [invSqrtTwo • (unitE p.1 p.2 - unitE p.2 p.1), (invSqrtTwo * Complex.I) • (unitE p.1 p.2 + unitE p.2 p.1)],
    ∀ Y ∈ [invSqrtTwo • (unitE q.1 q.2 - unitE q.2 q.1), (invSqrtTwo * Complex.I) • (unitE q.1 q.2 + unitE q.2 q.1)],
    trace (X * Y) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := pq_facts hp hq hpq
  have e1 : trace (unitE p.1 p.2 * unitE q.1 q.2) = 0 := by rw [trE, if_neg h1]
  have e2 : trace (unitE p.1 p.2 * unitE q.2 q.1) = 0 := by rw [trE, if_neg h2]
  have e3 : trace (unitE p.2 p.1 * unitE q.1 q.2) = 0 := by rw [trE, if_neg h3]
  have e4 : trace (unitE p.2 p.1 * unitE q.2 q.1) = 0 := by rw [trE, if_neg h4]
  intro X hX Y hY
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hX hY
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl <;>
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub, e1, e2, e3, e4] <;> simp

theorem kList_self (ε : Fin n → Bool) : ∀ X ∈ kList ε, trace (X * X) = -1 := by
  intro X hX
  simp only [kList, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false] at hX
  rcases hX with ⟨a, -, rfl⟩ | ⟨p, hp, rfl | rfl⟩
  · exact d_self a
  · exact trace_casimirAntisymPair_mul_self (mem_pairs_lt hp)
  · exact trace_casimirSymPairI_mul_self (mem_pairs_lt hp)

theorem kList_pairwise (ε : Fin n → Bool) : (kList ε).Pairwise (fun X Y => trace (X * Y) = 0) := by
  rw [kList, List.pairwise_append, List.pairwise_map, List.pairwise_flatMap]
  refine ⟨(List.nodup_finRange n).imp fun h => d_ne h, ⟨fun p hp => ?_, ?_⟩, ?_⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true, List.forall_mem_nil]
    exact ⟨p12 (mem_pairs_lt hp), fun _ h => h.elim⟩
  · exact (nodup_pairs ε true).imp_of_mem fun hp hq hpq => pq_zero (mem_pairs_lt hp) (mem_pairs_lt hq) hpq
  · intro X hX Y hY
    simp only [List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hX hY
    obtain ⟨a, -, rfl⟩ := hX
    obtain ⟨p, hp, rfl | rfl⟩ := hY
    · exact dp1 a (mem_pairs_lt hp)
    · exact dp2 a (mem_pairs_lt hp)

end GlobalTheory.TypeSum.CasBasis.KOrth

namespace GlobalTheory.TypeSum.CasBasis

theorem kB_trace_orthonormal : ∀ (n : ℕ) (ε : Fin n → Bool) (i j : Fin (kList ε).length),
    (trace (kB ε i * kB ε j)).re = if i = j then -1 else 0 := by
  intro n ε i j
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, kB, KOrth.kList_self ε _ (List.get_mem _ _)]; simp
  · rw [if_neg hij]
    have hP := List.pairwise_iff_get.mp (KOrth.kList_pairwise ε)
    rcases lt_or_gt_of_ne hij with h | h
    · rw [kB, hP i j h]; simp
    · rw [kB, Matrix.trace_mul_comm, hP j i h]; simp

end GlobalTheory.TypeSum.CasBasis

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.compactUnitary_fourierKernel_conj_invariant : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), GlobalTheory.KFourier.IsKer ε i e → ∀ a k : KG ε, e (a * k * a⁻¹) = e k := by
  first | exact @GlobalTheory.KFourier.isKer_class | exact GlobalTheory.KFourier.isKer_class | (intros; apply GlobalTheory.KFourier.isKer_class <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.compactUnitaryRightDeriv_conjInvariantAverage_eq : ∀ {n : ℕ} (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F → ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → (∀ g ∈ UJset ε, F [] g = f g) → ∀ e : KG ε → ℂ, Continuous e → (∀ a k : KG ε, e (a * k * a⁻¹) = e k) → ∀ u : List (Mx n), (∀ X ∈ u, inK ε X) → ∀ y ∈ UJset ε, GlobalTheory.KFourier.rder ε u (GlobalTheory.KFourier.avgK ε e f y) 1 = ∫ k, e k * F u (y * toMK k) ∂(muK ε) := by
  first | exact @GlobalTheory.KAvgDeriv.rder_avgK_one | exact GlobalTheory.KAvgDeriv.rder_avgK_one | (intros; apply GlobalTheory.KAvgDeriv.rder_avgK_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

theorem exists_orthProj_polyV {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (p : KG ε → ℂ) (hp : Continuous p) :
    ∃ p' ∈ GlobalTheory.KFourier.polyV ε d, ∀ q ∈ GlobalTheory.KFourier.polyV ε d,
      ∫ k, star (q k) * (p k - p' k) ∂(muK ε) = 0 := by
  first
  | exact @_root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV
  | exact _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV
  | (apply _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthogonalProjectionPoly.exists_proj_polyV ..)

end GlobalTheory.KFourier

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.compactUnitaryAverage_mem_polyV : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), e ∈ GlobalTheory.KFourier.polyV ε i → ∀ f : Mx n → ℂ, ContinuousOn f (UJset ε) → ∀ y ∈ UJset ε, GlobalTheory.KFourier.avgK ε e f y ∈ GlobalTheory.KFourier.polyV ε i := by
  first | exact @GlobalTheory.KFourier.avgK_mem | exact GlobalTheory.KFourier.avgK_mem | (intros; apply GlobalTheory.KFourier.avgK_mem <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_compactUnitary_fourierKernel : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ), ∃ e, GlobalTheory.KFourier.IsKer ε i e := by
  first | exact @GlobalTheory.KFourier.exists_isKer | exact GlobalTheory.KFourier.exists_isKer | (intros; apply GlobalTheory.KFourier.exists_isKer <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.contDiff_matrixRightInvariantDerivative : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ), φ ∈ GlobalTheory.KFourier.polyV ε d → ∀ X : Mx n, inK ε X → GlobalTheory.KFourier.rder ε [X] φ ∈ GlobalTheory.KFourier.polyV ε d ∧ ∀ k : KG ε, HasDerivAt (fun t : ℝ => φ (k * expK ε X t)) (GlobalTheory.KFourier.rder ε [X] φ k) 0 := by
  first | exact @GlobalTheory.KFourier.rder_mem_and_hasDerivAt | exact GlobalTheory.KFourier.rder_mem_and_hasDerivAt | (intros; apply GlobalTheory.KFourier.rder_mem_and_hasDerivAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.finrank_compactUnitaryPolyFunDegLE_le : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ), Module.finrank ℂ (polyV ε d) ≤ (d + 1) ^ (2 * n ^ 2) := by
  first | exact @GlobalTheory.KFourier.finrank_polyV_le | exact GlobalTheory.KFourier.finrank_polyV_le | (intros; apply GlobalTheory.KFourier.finrank_polyV_le <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory


theorem _root_.GlobalTheory.T.orthogonal_lowerDegree_kernel_translates : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (p κ : KG ε → ℂ), κ ∈ lowV ε i → (∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) → ∀ k : KG ε, ∫ x, star (p x) * κ (x⁻¹ * k) ∂(muK ε) = 0 := by
  first | exact @GlobalTheory.KFourier.orth_translate_lowV | exact GlobalTheory.KFourier.orth_translate_lowV | (intros; apply GlobalTheory.KFourier.orth_translate_lowV <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.rightDeriv_norm_le_finite_words_bound : ∀ {n : ℕ} (ε : Fin n → Bool) (m : ℕ), ∃ (U : List (List (Mx n))) (C : ℝ), 0 ≤ C ∧ (∀ u ∈ U, ∀ X ∈ u, inK ε X) ∧ ∀ (d : ℕ) (φ : KG ε → ℂ), φ ∈ GlobalTheory.KFourier.polyV ε d → ∀ w : List (Mx n), w.length ≤ m → (∀ X ∈ w, inK ε X ∧ hs X ≤ 1) → ‖GlobalTheory.KFourier.rder ε w φ 1‖ ≤ C * (U.map fun u => ‖GlobalTheory.KFourier.rder ε u φ 1‖).sum := by
  first | exact @GlobalTheory.KFourier.rder_bound_basisWords | exact GlobalTheory.KFourier.rder_bound_basisWords | (intros; apply GlobalTheory.KFourier.rder_bound_basisWords <;> assumption)
end

section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

theorem _root_.GlobalTheory.T.exists_compactFinite_approxIdentity : ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [TopologicalSpace X] (F : X → KG ε → ℂ), (Continuous fun p : X × KG ε => F p.1 p.2) → ∀ C : Set X, IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ e : KG ε → ℂ, KFinFun ε e ∧ ∀ x ∈ C, ‖F x 1 - ∫ k, e k * F x k ∂(muK ε)‖ < δ := by
  first | exact @GlobalTheory.KFinApprox.approx_identity | exact GlobalTheory.KFinApprox.approx_identity | (intros; apply GlobalTheory.KFinApprox.approx_identity <;> assumption)
end
