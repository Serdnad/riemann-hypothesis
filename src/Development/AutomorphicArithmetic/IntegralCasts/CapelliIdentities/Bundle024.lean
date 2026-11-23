module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.Data.Matrix.Basis
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

section

theorem UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near :
    ∀ (z : ℂ),
    (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have step : ∀ n : ℕ, (3 / 2 : ℝ) * ‖z ^ n - 1‖ ≤ ‖z ^ (n * 2) - 1‖ := by
    intro n
    have e : z ^ (n * 2) - 1 = (z ^ n + 1) * (z ^ n - 1) := by ring
    have h1 : ‖(2 : ℂ)‖ ≤ ‖z ^ n + 1‖ + ‖z ^ n - 1‖ := by
      have e2 : (2 : ℂ) = (z ^ n + 1) - (z ^ n - 1) := by ring
      calc ‖(2 : ℂ)‖ = ‖(z ^ n + 1) - (z ^ n - 1)‖ := congrArg _ e2
        _ ≤ _ := norm_sub_le _ _
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have h3 := h n
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have grow : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have s := step (2 ^ k)
      rw [pow_succ, pow_succ]
      linarith
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ hpos] at hk
  have g := grow k
  have h4 := h (2 ^ k)
  linarith
end

section

theorem UpperTheory.Reformulated.B.Ue24.eq_one_of_pow_near :
    ∀ {z : ℂ},
    (∀ (k : ℕ), ‖z ^ (2 : ℕ) ^ k - (1 : ℂ)‖ ≤ (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 : ℕ) ^ k - (1 : ℂ)‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : z ^ (2 : ℕ) ^ (k + 1) - 1 = (z ^ (2 : ℕ) ^ k - 1) * (z ^ (2 : ℕ) ^ k + 1) := by
        rw [pow_succ, pow_mul]; ring
      have h2 : (3 / 2 : ℝ) ≤ ‖z ^ (2 : ℕ) ^ k + 1‖ := by
        have h3 := norm_sub_le (z ^ (2 : ℕ) ^ k + 1) (z ^ (2 : ℕ) ^ k - 1)
        have h4 : (z ^ (2 : ℕ) ^ k + 1) - (z ^ (2 : ℕ) ^ k - 1) = 2 := by ring
        rw [h4] at h3
        have h5 : ‖(2 : ℂ)‖ = 2 := by simp
        have h6 := h k
        linarith
      rw [e, norm_mul]
      calc (3 / 2 : ℝ) ^ (k + 1) * ‖z - 1‖ = ((3 / 2 : ℝ) ^ k * ‖z - 1‖) * (3 / 2) := by ring
        _ ≤ _ := mul_le_mul ih h2 (by norm_num) (norm_nonneg _)
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ hpos] at hk
  have h7 := key k
  have h8 := h k
  linarith
end

section

private theorem UpperTheory.Reformulated.B.Qk23.half_le_re {w : ℂ} (h : ‖w⁻¹ - 1‖ < 1) : (1 / 2 : ℝ) ≤ w.re := by
  have hw : w ≠ 0 := by
    rintro rfl
    simp at h
  have e : w⁻¹ - 1 = (1 - w) / w := by field_simp
  rw [e, norm_div, div_lt_one (norm_pos_iff.mpr hw)] at h
  have h2 : ‖1 - w‖ ^ 2 < ‖w‖ ^ 2 := by
    have := norm_nonneg (1 - w)
    nlinarith
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h2
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at h2
  nlinarith

theorem UpperTheory.Reformulated.B.Qk23.eq_one_of_forall_zpow :
    ∀ {z : ℂ}, (∀ (k : ℤ), ‖z ^ k - (1 : ℂ)‖ < (1 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hz
  have hd : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hre : ∀ k : ℕ, (1 / 2 : ℝ) ≤ (z ^ k).re := by
    intro k
    apply UpperTheory.Reformulated.B.Qk23.half_le_re
    have := h (-(k : ℤ))
    rwa [zpow_neg, zpow_natCast] at this
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / ‖z - 1‖)
  rw [div_lt_iff₀ hd] at hn
  have h1 : (n : ℝ) * (1 / 2) ≤ ‖∑ k ∈ Finset.range n, z ^ k‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have := Finset.card_nsmul_le_sum (Finset.range n) (fun k => (z ^ k).re) (1 / 2 : ℝ)
      (fun k _ => hre k)
    rwa [Finset.card_range, nsmul_eq_mul] at this
  have h2 : ‖∑ k ∈ Finset.range n, z ^ k‖ * ‖z - 1‖ < 1 := by
    rw [← norm_mul, geom_sum_mul]
    have := h (n : ℤ)
    rwa [zpow_natCast] at this
  have h3 := mul_le_mul_of_nonneg_right h1 hd.le
  linarith
end

section

theorem UpperTheory.moderate_growth_add_smul :
    ∀ {Y : Type} (h : Y → ℝ) (f g : Y → ℂ) (z : ℂ), (∀ y, 1 ≤ h y) →
        (∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * h y ^ N) → (∃ (C : ℝ) (N : ℕ), ∀ y, ‖g y‖ ≤ C * h y ^ N) →
        ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y + z * g y‖ ≤ C * h y ^ N := by
  intro Y h f g z hh ⟨C, N, hf⟩ ⟨D, M, hg⟩
  refine ⟨|C| + ‖z‖ * |D|, N + M, fun y => ?_⟩
  have h0 : 0 ≤ h y := zero_le_one.trans (hh y)
  have h1 : ‖f y‖ ≤ |C| * h y ^ (N + M) :=
    (hf y).trans (mul_le_mul (le_abs_self C)
      (pow_le_pow_right₀ (hh y) (Nat.le_add_right N M)) (pow_nonneg h0 _) (abs_nonneg C))
  have h2 : ‖g y‖ ≤ |D| * h y ^ (N + M) :=
    (hg y).trans (mul_le_mul (le_abs_self D)
      (pow_le_pow_right₀ (hh y) (Nat.le_add_left M N)) (pow_nonneg h0 _) (abs_nonneg D))
  calc ‖f y + z * g y‖ ≤ ‖f y‖ + ‖z * g y‖ := norm_add_le _ _
    _ = ‖f y‖ + ‖z‖ * ‖g y‖ := by rw [norm_mul]
    _ ≤ |C| * h y ^ (N + M) + ‖z‖ * (|D| * h y ^ (N + M)) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg z))
    _ = (|C| + ‖z‖ * |D|) * h y ^ (N + M) := by ring
end

section

theorem UpperTheory.Reformulated.B.Yla6.main :
    ∀ {a b c d : Type} [inst : Fintype b] [inst_1 : Fintype c] (A : Matrix a b ℂ) (M : Matrix b c ℂ) (B : Matrix c d ℂ)
      {α μ β : ℝ},
      (∀ (i : a) (j : b), ‖A i j‖ ≤ α) →
        (∀ (i : b) (j : c), ‖M i j‖ ≤ μ) →
          (∀ (i : c) (j : d), ‖B i j‖ ≤ β) →
            ∀ (i : a) (j : d), ‖(A * M * B) i j‖ ≤ (↑(Fintype.card b) : ℝ) * (↑(Fintype.card c) : ℝ) * (α * μ * β) := by
  intro a b c d _ _ A M B α μ β hA hM hB i j
  have h1 : ‖(A * M * B) i j‖ ≤ ∑ l : c, ∑ k : b, ‖A i k‖ * ‖M k l‖ * ‖B l j‖ := by
    simp_rw [Matrix.mul_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => (norm_sum_le _ _).trans ?_)
    simp [norm_mul]
  have h2 : ∀ l : c, ∀ k : b, ‖A i k‖ * ‖M k l‖ * ‖B l j‖ ≤ α * μ * β := by
    intro l k
    have ha : 0 ≤ α := (norm_nonneg _).trans (hA i k)
    have hm : 0 ≤ μ := (norm_nonneg _).trans (hM k l)
    exact mul_le_mul (mul_le_mul (hA i k) (hM k l) (norm_nonneg _) ha) (hB l j) (norm_nonneg _)
      (mul_nonneg ha hm)
  calc ‖(A * M * B) i j‖ ≤ ∑ l : c, ∑ k : b, ‖A i k‖ * ‖M k l‖ * ‖B l j‖ := h1
    _ ≤ ∑ _l : c, ∑ _k : b, α * μ * β :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => h2 l k
    _ = (↑(Fintype.card b) : ℝ) * (↑(Fintype.card c) : ℝ) * (α * μ * β) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
end

section

theorem UpperTheory.Reformulated.B.Qj19.lin_bound.{u_1} :
    ∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι] (L : Matrix ι ι ℂ →ₗ[ℂ] ℂ),
    ∃ (K : ℝ),
      (0 : ℝ) ≤ K ∧ ∀ (B : Matrix ι ι ℂ) (C : ℝ), (∀ (i j : ι), ‖B i j‖ ≤ C) → ‖(L : Matrix ι ι ℂ → ℂ) B‖ ≤ K * C := by
  intro ι _ _ L
  refine ⟨∑ i, ∑ j, ‖L (Matrix.single i j 1)‖, by positivity, fun B C hB => ?_⟩
  have h : L B = ∑ i, ∑ j, B i j * L (Matrix.single i j 1) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single B]

    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (hB i j) (norm_nonneg _)
end

section

noncomputable def UpperTheory.Reformulated.B.Qi39.EB.{u_1, u_2} :
    {m : Type u_1} → {n : Type u_2} → Matrix m n ℂ → ℝ → Prop :=
    fun {m : Type u_1} {n : Type u_2} (A : Matrix m n ℂ) (c : ℝ) ↦ ∀ (i : m) (j : n), ‖A i j‖ ≤ c

theorem UpperTheory.Reformulated.B.Qi39.det_norm_le.{u_1} :
    ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] (A : Matrix n n ℂ) {m : ℝ},
      UpperTheory.Reformulated.B.Qi39.EB A m → ‖A.det‖ ≤ (↑(Fintype.card n).factorial : ℝ) * m ^ Fintype.card n := by
  intro n _ _ A m h
  have hterm : ∀ σ : Equiv.Perm n,
      ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ ≤ m ^ Fintype.card n := by
    intro σ
    have hs : ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ = ‖∏ i, A (σ i) i‖ := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
      · rw [h1, one_smul]
      · rw [h1, Units.neg_smul, one_smul, norm_neg]
    rw [hs, norm_prod]
    calc ∏ i, ‖A (σ i) i‖ ≤ ∏ _i : n, m :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => h (σ i) i)
      _ = m ^ Fintype.card n := by rw [Finset.prod_const, Finset.card_univ]
  rw [Matrix.det_apply]
  calc ‖∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, A (σ i) i‖
      ≤ ∑ σ : Equiv.Perm n, ‖Equiv.Perm.sign σ • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm n, m ^ Fintype.card n := Finset.sum_le_sum fun σ _ => hterm σ
    _ = (↑(Fintype.card n).factorial : ℝ) * m ^ Fintype.card n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
end

section

open scoped ComplexOrder in
theorem UpperTheory.Reformulated.B.CoerciveOfPositiveDefinite.exists_coercive_of_posDef.{u_1} :
    ∀ {ι : Type u_1} [inst : Fintype ι] {P : Matrix ι ι ℂ},
      P.PosDef → ∃ (c : ℝ), 0 < c ∧
        ∀ (z : ι → ℂ) (j : ι), c * ‖z j‖ ^ 2 ≤ (star z ⬝ᵥ P.mulVec z).re := by
  intro ι _ P hP
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun _ j => (hι.false j).elim⟩
  have hcont : Continuous fun z : ι → ℂ => (star z ⬝ᵥ P.mulVec z).re := by
    unfold dotProduct Matrix.mulVec dotProduct
    fun_prop
  have hne : (Metric.sphere (0 : ι → ℂ) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : ι → ℂ) 1).exists_isMinOn hne hcont.continuousOn
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hc : 0 < (star u ⬝ᵥ P.mulVec u).re := hP.re_dotProduct_pos hu0
  refine ⟨_, hc, fun z j => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hw : (‖z‖⁻¹ • z) ∈ Metric.sphere (0 : ι → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  have h1 : (star u ⬝ᵥ P.mulVec u).re ≤ (star (‖z‖⁻¹ • z) ⬝ᵥ P.mulVec (‖z‖⁻¹ • z)).re := hmin hw
  have h2 : (star (‖z‖⁻¹ • z) ⬝ᵥ P.mulVec (‖z‖⁻¹ • z)).re
      = ‖z‖⁻¹ * (‖z‖⁻¹ * (star z ⬝ᵥ P.mulVec z).re) := by
    rw [star_smul, star_trivial, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
      Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
  have h3 : (star u ⬝ᵥ P.mulVec u).re * ‖z‖ ^ 2 ≤ (star z ⬝ᵥ P.mulVec z).re := by
    rw [h2] at h1
    calc (star u ⬝ᵥ P.mulVec u).re * ‖z‖ ^ 2
        ≤ ‖z‖⁻¹ * (‖z‖⁻¹ * (star z ⬝ᵥ P.mulVec z).re) * ‖z‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = (star z ⬝ᵥ P.mulVec z).re := by field_simp
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm z j) 2) hc.le).trans h3
end

section

theorem UpperTheory.Reformulated.B.Qk59.sq_shift :
    ∀ {G : Type} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G]
    {μ : MeasureTheory.Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable ↥Γ] {D : Set G},
    MeasureTheory.IsFundamentalDomain (↥Γ) D μ →
      ∀ {f : G → ℝ},
        (∀ γ ∈ Γ, ∀ (y : G), f (γ * y) = f y) → ∀ (g : G), ∫ (y : G) in D, f (y * g) ∂μ = ∫ (y : G) in D, f y ∂μ := by
  intro G _ _ _ _ _ μ _ _ Γ _ D hD f hf g
  have hD' : MeasureTheory.IsFundamentalDomain (↥Γ) ((fun y : G => y * g⁻¹) ⁻¹' D) μ :=
    hD.preimage_of_equiv
      (MeasureTheory.measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id
      (fun γ y => by
        show ((γ : G) * y) * g⁻¹ = (γ : G) * (y * g⁻¹)
        exact mul_assoc _ _ _)
  have h1 := (MeasureTheory.measurePreserving_mul_right μ g).setIntegral_preimage_emb
    (measurableEmbedding_mulRight g) f ((fun y : G => y * g⁻¹) ⁻¹' D)
  have h2 : (fun y : G => y * g) ⁻¹' ((fun y : G => y * g⁻¹) ⁻¹' D) = D := by
    ext y
    simp
  rw [h2] at h1
  rw [h1]
  exact hD'.setIntegral_eq hD (fun γ y => hf γ γ.2 y)
end

section

theorem UpperTheory.Reformulated.B.Qg3.exists_sum.{u_1} :
    ∀ {G : Type u_1} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [MeasureTheory.IsFiniteMeasureOnCompacts μ] (K : Subgroup G),
    IsOpen (↑K : Set G) →
      IsCompact (↑K : Set G) →
        ∀ {S : Set G},
          IsCompact S →
            ∃ (T : Finset (G ⧸ K)) (r : G ⧸ K → G) (c : G ⧸ K → ℂ),
              ∀ (F : G → ℂ),
                (∀ (g k : G), k ∈ K → F (g * k) = F g) →
                  (∀ g ∉ S, F g = (0 : ℂ)) → ∫ (g : G), F g ∂μ = ∑ x ∈ T, c x * F (r x) := by
  intro G _ _ _ _ _ μ _ K hKo hKc S hS
  classical
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have hcont : Continuous (QuotientGroup.mk : G → G ⧸ K) := QuotientGroup.continuous_mk
  have hfin : ((QuotientGroup.mk : G → G ⧸ K) '' S).Finite :=
    (hS.image hcont).finite_of_discrete
  let C : G ⧸ K → Set G := fun x => (QuotientGroup.mk : G → G ⧸ K) ⁻¹' {x}
  have hmem : ∀ (x : G ⧸ K) (g : G), g ∈ C x ↔ (x.out)⁻¹ * g ∈ K := by
    intro x g
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  have hmeas : ∀ x, MeasurableSet (C x) := fun x =>
    ((isOpen_discrete {x}).preimage hcont).measurableSet
  have hcomp : ∀ x, IsCompact (C x) := by
    intro x
    have h : C x = (fun k => x.out * k) '' (K : Set G) := by
      ext g
      rw [hmem]
      constructor
      · intro h
        exact ⟨_, h, by simp⟩
      · rintro ⟨k, hk, rfl⟩
        simpa using hk
    rw [h]
    exact hKc.image (continuous_const.mul continuous_id)
  refine ⟨hfin.toFinset, fun x => x.out, fun x => (μ.real (C x) : ℂ), ?_⟩
  intro F hF h0
  have hout : ∀ g : G, F (QuotientGroup.mk g : G ⧸ K).out = F g := by
    intro g
    have h := hF (QuotientGroup.mk g : G ⧸ K).out _ ((hmem _ g).1 rfl)
    rw [mul_inv_cancel_left] at h
    exact h.symm
  have hdec : ∀ g, F g = ∑ x ∈ hfin.toFinset, (C x).indicator (fun _ => F x.out) g := by
    intro g
    rw [Finset.sum_eq_single (QuotientGroup.mk g : G ⧸ K)]
    · rw [Set.indicator_of_mem (show g ∈ C (QuotientGroup.mk g) from rfl), hout]
    · intro x _ hx
      have hg : g ∉ C x := fun h => hx (Eq.symm h)
      rw [Set.indicator_of_notMem hg]
    · intro hg
      rw [Set.indicator_of_mem (show g ∈ C (QuotientGroup.mk g) from rfl), hout]
      exact h0 g fun hgS => hg (hfin.mem_toFinset.2 ⟨g, hgS, rfl⟩)
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hdec),
    MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [MeasureTheory.integral_indicator_const _ (hmeas x), Complex.real_smul]
  · intro x _
    rw [MeasureTheory.integrable_indicator_iff (hmeas x)]
    exact MeasureTheory.integrableOn_const (hcomp x).measure_lt_top.ne
end

section

theorem UpperTheory.Reformulated.B.SumRightInverse.sum_rightInv :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G]
    [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G)
    [μ.IsMulLeftInvariant] (K : Subgroup G),
    IsOpen (↑K : Set G) →
      (μ : Set G → ENNReal) (↑K : Set G) ≠ ⊤ →
        ∀ {S : Set G},
          IsCompact S →
            (∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) →
              ∃ (t : Finset (G ⧸ K)),
                (∀ Q ∈ t, Quotient.out Q ∈ S) ∧
                  ∀ (f : G → ℂ),
                    (∀ s ∈ S, ∀ k ∈ K, f (s * k) = f s) →
                      ∫ (g : G) in S, f g ∂μ = ∑ Q ∈ t, f (Quotient.out Q) * (↑(μ.real (↑K : Set G)) : ℂ) := by
  intro G _ _ _ _ _ μ _ K hK hμ S hS hSK
  classical
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hK
  have hfin : ((QuotientGroup.mk : G → G ⧸ K) '' S).Finite :=
    (hS.image QuotientGroup.continuous_mk).finite_of_discrete
  let C : G ⧸ K → Set G := fun Q => (fun g => (Quotient.out Q)⁻¹ * g) ⁻¹' (K : Set G)
  have hC : ∀ Q g, g ∈ C Q ↔ (QuotientGroup.mk g : G ⧸ K) = Q := by
    intro Q g
    have h := QuotientGroup.eq (s := K) (a := Quotient.out Q) (b := g)
    rw [QuotientGroup.out_eq'] at h
    rw [eq_comm, h]
    rfl
  have hout : ∀ Q ∈ hfin.toFinset, Quotient.out Q ∈ S := by
    intro Q hQ
    obtain ⟨s, hs, rfl⟩ := hfin.mem_toFinset.1 hQ
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K s
    rw [hk]
    exact hSK s hs k k.2
  have hmeas : ∀ Q, MeasurableSet (C Q) := fun Q =>
    (hK.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμC : ∀ Q, μ (C Q) = μ K := fun Q => MeasureTheory.measure_preimage_mul μ _ _
  have hU : S = ⋃ Q ∈ hfin.toFinset, C Q := by
    ext g
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hg
      exact ⟨_, hfin.mem_toFinset.2 ⟨g, hg, rfl⟩, (hC _ g).2 rfl⟩
    · rintro ⟨Q, hQ, hg⟩
      have := hSK _ (hout Q hQ) _ hg
      simpa using this
  refine ⟨hfin.toFinset, hout, fun f hf => ?_⟩
  have hconst : ∀ Q ∈ hfin.toFinset, Set.EqOn f (fun _ => f (Quotient.out Q)) (C Q) := by
    intro Q hQ g hg
    have := hf _ (hout Q hQ) _ hg
    simpa using this
  have hsplit : ∫ g in ⋃ Q ∈ hfin.toFinset, C Q, f g ∂μ
      = ∑ Q ∈ hfin.toFinset, ∫ g in C Q, f g ∂μ := by
    refine MeasureTheory.integral_biUnion_finset _ (fun Q _ => hmeas Q) ?_ ?_
    · intro Q _ R _ hQR
      refine Set.disjoint_left.2 fun g h1 h2 => hQR ?_
      rw [← (hC Q g).1 h1, (hC R g).1 h2]
    · intro Q hQ
      refine (MeasureTheory.integrableOn_congr_fun (hconst Q hQ) (hmeas Q)).2 ?_
      exact MeasureTheory.integrableOn_const (by rw [hμC]; exact hμ)
  rw [← hU] at hsplit
  rw [hsplit]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [MeasureTheory.setIntegral_congr_fun (hmeas Q) (hconst Q hQ),
    MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, hμC,
    MeasureTheory.measureReal_def, Complex.real_smul, mul_comm]
end
