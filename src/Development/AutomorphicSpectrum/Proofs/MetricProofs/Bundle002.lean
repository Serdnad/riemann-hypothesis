module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.ExponentialBounds
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
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

@[expose] public section

section

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.ChartBlockLower

private theorem dotProduct_sum' {g a : ℕ} (v : Fin g → ℝ) (w : Fin a → Fin g → ℝ) :
    v ⬝ᵥ (∑ j, w j) = ∑ j, v ⬝ᵥ w j := by
  simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem quad_im_add_sum {a g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (s : Fin a → ℂ) (v : Fin g → ℝ) :
    v ⬝ᵥ (((τ + ∑ j, s j • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im) *ᵥ v)
      = v ⬝ᵥ ((τ.map Complex.im) *ᵥ v)
        + ∑ j, (s j).im * (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) := by
  have h : ((τ + ∑ j, s j • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im)
      = τ.map Complex.im + ∑ j, (s j).im • (B j).map (fun x : ℤ => (x : ℝ)) := by
    ext i k
    simp [Matrix.sum_apply, Complex.im_sum]
  rw [h, Matrix.add_mulVec, dotProduct_add, Matrix.sum_mulVec, dotProduct_sum']
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem im_lower_on_kernel : ∀ (n a g : ℕ) (ha : a ≤ n) (U : Set (Fin n → ℂ)) (τ0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c : ℝ), IsOpen U → ContinuousOn τ0 U → (∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) → 0 < c → (∀ z ∈ U, ∀ l : Fin a → ℂ, (∀ j, Complex.exp (l j) = z (Fin.castLE ha j)) → ((τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) → ∀ z ∈ U, ∀ l : Fin a → ℂ, (∀ j, z (Fin.castLE ha j) ≠ 0 → Complex.exp (l j) = z (Fin.castLE ha j)) → (∀ j, z (Fin.castLE ha j) = 0 → l j = 0) → ∀ v : Fin g → ℝ, (∀ j, z (Fin.castLE ha j) = 0 → (B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0) → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (((τ0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map Complex.im) *ᵥ v) := by
  intro n a g ha U τ0 B c hU hτ _ _ H z hz l hl _ v hv
  classical
  let l' : ℝ → Fin a → ℂ := fun t j => if z (Fin.castLE ha j) = 0 then -(t : ℂ) else l j
  let z' : ℝ → Fin n → ℂ := fun t i => if z i = 0 then Complex.exp (-(t : ℂ)) else z i
  have hT : Filter.Tendsto z' Filter.atTop (𝓝 z) := by
    rw [tendsto_pi_nhds]
    intro i
    by_cases hzi : z i = 0
    · have h1 : Filter.Tendsto (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) Filter.atTop
          (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
      have h2 : (fun t : ℝ => z' t i) = fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ) := by
        funext t
        simp [z', hzi, Complex.ofReal_exp]
      rw [h2, hzi]
      simpa using h1
    · have h2 : (fun t : ℝ => z' t i) = fun _ : ℝ => z i := by
        funext t
        simp [z', hzi]
      rw [h2]
      exact tendsto_const_nhds
  have hτc : ContinuousAt τ0 z := hτ.continuousAt (hU.mem_nhds hz)
  let φ : Matrix (Fin g) (Fin g) ℂ → ℝ := fun M => v ⬝ᵥ ((M.map Complex.im) *ᵥ v)
  have hφ : Continuous φ :=
    continuous_const.dotProduct
      ((continuous_id.matrix_map Complex.continuous_im).matrix_mulVec continuous_const)
  have hsplit : ∀ (w : Fin n → ℂ) (m : Fin a → ℂ),
      v ⬝ᵥ (((τ0 w + ∑ j, (m j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map
          Complex.im) *ᵥ v)
        = φ (τ0 w) + ∑ j, (m j / (2 * Real.pi * Complex.I)).im *
            (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) :=
    fun w m => quad_im_add_sum (τ0 w) B (fun j => m j / (2 * Real.pi * Complex.I)) v
  have hsum : ∀ t : ℝ, ∑ j, (l' t j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v))
      = ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) := by
    intro t
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hzj : z (Fin.castLE ha j) = 0
    · rw [hv j hzj]
      simp
    · simp [l', hzj]
  have hev : ∀ᶠ t in Filter.atTop, c * (v ⬝ᵥ v) ≤ φ (τ0 (z' t)) +
      ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)) := by
    filter_upwards [hT.eventually_mem (hU.mem_nhds hz)] with t ht
    have hexp : ∀ j, Complex.exp (l' t j) = z' t (Fin.castLE ha j) := by
      intro j
      by_cases hzj : z (Fin.castLE ha j) = 0
      · simp [l', z', hzj]
      · simp [l', z', hzj, hl j hzj]
    have h0 := (H (z' t) ht (l' t) hexp).dotProduct_mulVec_nonneg v
    have hstar : star v = v := by
      funext i
      exact TrivialStar.star_trivial _
    rw [hstar, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, hsplit, hsum] at h0
    linarith
  have hlim : Filter.Tendsto (fun t => φ (τ0 (z' t)) +
      ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v))) Filter.atTop
      (𝓝 (φ (τ0 z) + ∑ j, (l j / (2 * Real.pi * Complex.I)).im *
        (v ⬝ᵥ ((B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v)))) :=
    ((hφ.tendsto _).comp (hτc.tendsto.comp hT)).add tendsto_const_nhds
  rw [hsplit]
  exact ge_of_tendsto hlim hev

end GlobalTheory.CompanionTheory.ChartBlockLower
end

section

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.GramCompact

private theorem exists_sum_norm_sq_eq_one_and_eq_sqrt_smul {m : Type} [Fintype m] (w : m → ℂ)
    (hw : 0 < ∑ k, ‖w k‖ ^ 2) :
    ∃ v : m → ℂ, ∑ k, ‖v k‖ ^ 2 = 1 ∧
      w = ((Real.sqrt (∑ k, ‖w k‖ ^ 2) : ℝ) : ℂ) • v := by
  have ht : 0 < Real.sqrt (∑ k, ‖w k‖ ^ 2) := Real.sqrt_pos.mpr hw
  have ht2 : Real.sqrt (∑ k, ‖w k‖ ^ 2) ^ 2 = ∑ k, ‖w k‖ ^ 2 := Real.sq_sqrt hw.le
  refine ⟨(((Real.sqrt (∑ k, ‖w k‖ ^ 2))⁻¹ : ℝ) : ℂ) • w, ?_, ?_⟩
  · have h : ∀ k, ‖((((Real.sqrt (∑ j, ‖w j‖ ^ 2))⁻¹ : ℝ) : ℂ) • w) k‖ ^ 2 =
        (Real.sqrt (∑ j, ‖w j‖ ^ 2) ^ 2)⁻¹ * ‖w k‖ ^ 2 := by
      intro k
      rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
    simp only [h]
    rw [← Finset.mul_sum, ht2, inv_mul_cancel₀ hw.ne']
  · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one, one_smul]

private theorem continuousOn_re_star_dotProduct_mulVec {X : Type} [TopologicalSpace X] {K : Set X}
    {m : Type} [Fintype m] {H : X → Matrix m m ℂ} (hH : ContinuousOn H K) (T : Set (m → ℂ)) :
    ContinuousOn (fun p : X × (m → ℂ) => (star p.2 ⬝ᵥ (H p.1 *ᵥ p.2)).re) (K ×ˢ T) := by
  have hd : Continuous (fun q : Matrix m m ℂ × (m → ℂ) => star q.2 ⬝ᵥ (q.1 *ᵥ q.2)) := by
    apply Continuous.dotProduct
    · exact continuous_snd.star
    · exact Continuous.matrix_mulVec continuous_fst continuous_snd
  have hfst : ContinuousOn (H ∘ Prod.fst) (K ×ˢ T) :=
    ContinuousOn.comp hH continuousOn_fst (fun p hp => (Set.mem_prod.mp hp).1)
  have h2 : ContinuousOn (fun p : X × (m → ℂ) => ((H ∘ Prod.fst) p, p.2)) (K ×ˢ T) :=
    ContinuousOn.prodMk hfst continuousOn_snd
  have h3 := Continuous.comp_continuousOn (Continuous.comp Complex.continuous_re hd) h2
  exact h3

theorem isCompact_sphere (m : Type) [Fintype m] :
    IsCompact {w : m → ℂ | ∑ k, ‖w k‖ ^ 2 = 1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq (by fun_prop) continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : m → ℂ)) (r := 1)).subset ?_
    intro w hw
    have hw' : ∑ k, ‖w k‖ ^ 2 = 1 := hw
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    have h1 : ‖w k‖ ^ 2 ≤ 1 := by
      calc ‖w k‖ ^ 2 ≤ ∑ j, ‖w j‖ ^ 2 :=
            Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => by positivity)
              (Finset.mem_univ k)
        _ = 1 := hw'
    nlinarith [norm_nonneg (w k)]

theorem form_smul {m : Type} [Fintype m] (A : Matrix m m ℂ) (r : ℝ) (w : m → ℂ) :
    (star ((r : ℂ) • w) ⬝ᵥ (A *ᵥ ((r : ℂ) • w))).re = r ^ 2 * (star w ⬝ᵥ (A *ᵥ w)).re := by
  have hs : star ((r : ℂ) • w) = (r : ℂ) • star w := by
    ext k
    simp
  rw [hs, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem exists_bounds (X : Type) [TopologicalSpace X] (K : Set X) (m : Type) [Fintype m]
    [DecidableEq m] (H : X → Matrix m m ℂ) (hK : IsCompact K) (hH : ContinuousOn H K)
    (hpos : ∀ x ∈ K, (H x).PosDef) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ K, ∀ w : m → ℂ,
      C⁻¹ * ∑ k, ‖w k‖ ^ 2 ≤ (star w ⬝ᵥ (H x *ᵥ w)).re ∧
        (star w ⬝ᵥ (H x *ᵥ w)).re ≤ C * ∑ k, ‖w k‖ ^ 2 := by
  obtain ⟨T, hT⟩ : ∃ T : Set (m → ℂ), T = {w : m → ℂ | ∑ k, ‖w k‖ ^ 2 = 1} := ⟨_, rfl⟩
  have hKS : IsCompact (K ×ˢ T) := hT ▸ hK.prod (GlobalTheory.CompanionTheory.GramCompact.isCompact_sphere m)
  have hfc := continuousOn_re_star_dotProduct_mulVec hH T
  have hfpos : ∀ x ∈ K, ∀ w ∈ T, 0 < (star w ⬝ᵥ (H x *ᵥ w)).re := by
    intro x hx w hw
    rw [hT, Set.mem_setOf_eq] at hw
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    exact (Complex.pos_iff.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp (hpos x hx)).2 hw0)).1
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ w ∈ T,
      c ≤ (star w ⬝ᵥ (H x *ᵥ w)).re := by
    rcases (K ×ˢ T).eq_empty_or_nonempty with h | h
    · refine ⟨1, one_pos, fun x hx w hw => ?_⟩
      have hm : (x, w) ∈ K ×ˢ T := Set.mk_mem_prod hx hw
      rw [h] at hm
      exact absurd hm (Set.notMem_empty _)
    · obtain ⟨p₀, hp₀, hmin⟩ := hKS.exists_isMinOn h hfc
      refine ⟨_, hfpos p₀.1 (Set.mem_prod.mp hp₀).1 p₀.2 (Set.mem_prod.mp hp₀).2,
        fun x hx w hw => ?_⟩
      exact hmin (Set.mk_mem_prod hx hw)
  obtain ⟨M, hM⟩ := hKS.exists_bound_of_continuousOn hfc
  have hC1 : c⁻¹ ≤ max 1 (max c⁻¹ M) := (le_max_left _ _).trans (le_max_right _ _)
  have hCM : M ≤ max 1 (max c⁻¹ M) := (le_max_right _ _).trans (le_max_right _ _)
  have hCc : (max 1 (max c⁻¹ M))⁻¹ ≤ c := inv_le_of_inv_le₀ hc0 hC1
  refine ⟨max 1 (max c⁻¹ M), le_max_left _ _, ?_⟩
  intro x hx w
  have hs0 : 0 ≤ ∑ k, ‖w k‖ ^ 2 := Finset.sum_nonneg (fun k _ => by positivity)
  rcases hs0.eq_or_lt with hs | hspos
  · have hw : w = 0 := by
      funext k
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp hs.symm k
        (Finset.mem_univ k)
      simpa using this
    subst hw
    simp
  · obtain ⟨v, hv1, hwv⟩ := exists_sum_norm_sq_eq_one_and_eq_sqrt_smul w hspos
    have hvT : v ∈ T := by
      rw [hT]
      exact hv1
    have hq : (star w ⬝ᵥ (H x *ᵥ w)).re =
        (∑ k, ‖w k‖ ^ 2) * (star v ⬝ᵥ (H x *ᵥ v)).re := by
      conv_lhs => rw [hwv]
      rw [GlobalTheory.CompanionTheory.GramCompact.form_smul, Real.sq_sqrt hs0]
    have h1 : c ≤ (star v ⬝ᵥ (H x *ᵥ v)).re := hc x hx v hvT
    have h2 : (star v ⬝ᵥ (H x *ᵥ v)).re ≤ M := by
      have h3 : ‖(star v ⬝ᵥ (H x *ᵥ v)).re‖ ≤ M := hM (x, v) (Set.mk_mem_prod hx hvT)
      rw [Real.norm_eq_abs] at h3
      exact (le_abs_self _).trans h3
    rw [hq]
    have h4 := mul_le_mul_of_nonneg_right hCc hspos.le
    have h5 := mul_le_mul_of_nonneg_right h1 hspos.le
    have h6 := mul_le_mul_of_nonneg_right (h2.trans hCM) hspos.le
    constructor
    · linarith
    · linarith

end GlobalTheory.CompanionTheory.GramCompact
end

section

open Set Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LocalLog

noncomputable def iter {B V : Type} (h : B × V → V) : ℕ → B × V → V
  | 0, p => p.2
  | k + 1, p => h (p.1, iter h k p)

@[simp] theorem iter_zero {B V : Type} (h : B × V → V) (p : B × V) : iter h 0 p = p.2 := rfl

theorem iter_succ {B V : Type} (h : B × V → V) (k : ℕ) (p : B × V) :
    iter h (k + 1) p = h (p.1, iter h k p) := rfl

section Norms

variable {B V : Type} [NormedAddCommGroup B] [NormedAddCommGroup V]

theorem norm_iter_le (b₀ : B) (h : B × V → V) (ρ : ℝ)
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖)
    {b : B} (hb : b ∈ ball b₀ ρ) {s : V} (hs : s ∈ ball (0 : V) ρ) (k : ℕ) :
    ‖iter h k (b, s)‖ ≤ (3 / 5) ^ k * ‖s‖ := by
  have key : ∀ k : ℕ, ‖iter h k (b, s)‖ ≤ (3 / 5) ^ k * ‖s‖ ∧ iter h k (b, s) ∈ ball (0 : V) ρ := by
    intro k
    induction k with
    | zero =>
      refine ⟨by simp, ?_⟩
      simpa using hs
    | succ k ih =>
      have hk := hcontr b hb _ ih.2
      have e : iter h (k + 1) (b, s) = h (b, iter h k (b, s)) := rfl
      rw [e]
      refine ⟨?_, ?_⟩
      · calc ‖h (b, iter h k (b, s))‖ ≤ 3 / 5 * ‖iter h k (b, s)‖ := hk
          _ ≤ 3 / 5 * ((3 / 5) ^ k * ‖s‖) := by gcongr; exact ih.1
          _ = (3 / 5) ^ (k + 1) * ‖s‖ := by ring
      · have h2 := mem_ball_zero_iff.mp ih.2
        rw [mem_ball_zero_iff]
        nlinarith [norm_nonneg (iter h k (b, s))]
  exact (key k).1

theorem iter_mem_ball (b₀ : B) (h : B × V → V) (ρ : ℝ)
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖)
    {b : B} (hb : b ∈ ball b₀ ρ) {s : V} (hs : s ∈ ball (0 : V) ρ) (k : ℕ) :
    iter h k (b, s) ∈ ball (0 : V) ρ := by
  rw [mem_ball_zero_iff]
  have h1 := norm_iter_le b₀ h ρ hcontr hb hs k
  have h2 : (3 / 5 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h3 : ‖s‖ < ρ := mem_ball_zero_iff.mp hs
  nlinarith [norm_nonneg s]

end Norms

theorem iter_differentiableOn {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup V] [NormedSpace ℂ V] (b₀ : B) (h : B × V → V) (ρ : ℝ)
    (hd : DifferentiableOn ℂ h (ball b₀ ρ ×ˢ ball (0 : V) ρ))
    (hcontr : ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) (k : ℕ) :
    DifferentiableOn ℂ (iter h k) (ball b₀ ρ ×ˢ ball (0 : V) ρ) := by
  induction k with
  | zero =>
    have e : iter h 0 = Prod.snd := funext fun p => rfl
    rw [e]
    exact differentiableOn_snd
  | succ k ih =>
    have e : iter h (k + 1) = h ∘ fun p => (p.1, iter h k p) := funext fun p => rfl
    rw [e]
    refine hd.comp (differentiableOn_fst.prodMk ih) ?_
    intro p hp
    exact Set.mk_mem_prod hp.1 (iter_mem_ball b₀ h ρ hcontr hp.1 hp.2 k)

theorem medial_eventually {B V : Type} [TopologicalSpace B] [Zero V] [TopologicalSpace V] (b₀ : B)
    (μ : B × V × V → V) (hc : ContinuousAt μ (b₀, 0, 0)) (h0 : μ (b₀, 0, 0) = 0)
    (hcomm : ∀ᶠ p : B × V × V in 𝓝 (b₀, 0, 0), μ (p.1, p.2.1, p.2.2) = μ (p.1, p.2.2, p.2.1))
    (hassoc : ∀ᶠ p : B × V × V × V in 𝓝 (b₀, 0, 0, 0),
      μ (p.1, μ (p.1, p.2.1, p.2.2.1), p.2.2.2) = μ (p.1, p.2.1, μ (p.1, p.2.2.1, p.2.2.2))) :
    ∀ᶠ p : B × V × V in 𝓝 (b₀, 0, 0),
      μ (p.1, μ (p.1, p.2.1, p.2.1), μ (p.1, p.2.2, p.2.2)) = μ (p.1, μ p, μ p) := by
  have hfst : Tendsto (fun p : B × V × V => p.1) (𝓝 (b₀, 0, 0)) (𝓝 b₀) := continuous_fst.tendsto _
  have hs : Tendsto (fun p : B × V × V => p.2.1) (𝓝 (b₀, 0, 0)) (𝓝 0) :=
    (continuous_fst.comp continuous_snd).tendsto _
  have ht : Tendsto (fun p : B × V × V => p.2.2) (𝓝 (b₀, 0, 0)) (𝓝 0) :=
    (continuous_snd.comp continuous_snd).tendsto _
  have hμ : Tendsto μ (𝓝 (b₀, 0, 0)) (𝓝 0) := by
    have := hc.tendsto
    rwa [h0] at this
  have htt : Tendsto (fun p : B × V × V => μ (p.1, p.2.2, p.2.2)) (𝓝 (b₀, 0, 0)) (𝓝 0) :=
    hμ.comp (hfst.prodMk_nhds (ht.prodMk_nhds ht))
  have orbitMap_conj_smul_one := (hfst.prodMk_nhds (hs.prodMk_nhds (hs.prodMk_nhds htt))).eventually hassoc
  have orbitMap_conj_smul_two := (hfst.prodMk_nhds (hs.prodMk_nhds (ht.prodMk_nhds ht))).eventually hassoc
  have selfLieBasisVector := (hfst.prodMk_nhds (ht.prodMk_nhds (hs.prodMk_nhds ht))).eventually hassoc
  have eA4 := (hfst.prodMk_nhds (hs.prodMk_nhds (ht.prodMk_nhds hμ))).eventually hassoc
  filter_upwards [orbitMap_conj_smul_one, orbitMap_conj_smul_two, selfLieBasisVector, eA4, hcomm] with ⟨b, s, t⟩ a1 a2 a3 a4 c
  dsimp only at a1 a2 a3 a4 c ⊢
  calc μ (b, μ (b, s, s), μ (b, t, t)) = μ (b, s, μ (b, s, μ (b, t, t))) := a1
    _ = μ (b, s, μ (b, μ (b, s, t), t)) := by rw [a2]
    _ = μ (b, s, μ (b, μ (b, t, s), t)) := by rw [c]
    _ = μ (b, s, μ (b, t, μ (b, s, t))) := by rw [a3]
    _ = μ (b, μ (b, s, t), μ (b, s, t)) := a4.symm

end GlobalTheory.CompanionTheory.Ar.Flat.LocalLog
end

section

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.LogLin

theorem exists_log_affine_le : ∀ C n K : ℝ, 0 ≤ C → 0 ≤ n → 0 ≤ K → ∃ C₁ : ℝ, 1 ≤ C₁ ∧ K ≤ C₁ ∧ ∀ x y : ℝ, -K ≤ x → y ≤ n * x + C → C * Real.log (2 + C + max y 0) + C ≤ C₁ * Real.log (2 + C₁ + x) := by
  intro C n K hC hn hK
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 + 2 * C + n := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; linarith
  have hCA : 0 ≤ C * A := mul_nonneg hC hA0.le
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 1 + K + C + 2 * (C * A + C) := ⟨_, rfl⟩
  refine ⟨D, by rw [hD]; linarith, by rw [hD]; linarith, ?_⟩
  intro x y hx hy
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 2 + D + x := ⟨_, rfl⟩
  rw [← hu]
  have ht : 0 ≤ x + K := by linarith
  have hut : 2 + (x + K) ≤ u := by rw [hu, hD]; linarith
  have hu2 : 2 ≤ u := by linarith
  have hnK : 0 ≤ n * K := mul_nonneg hn hK
  have hnt : 0 ≤ n * (x + K) := mul_nonneg hn ht
  have hmax : max y 0 ≤ n * (x + K) + C := max_le (by nlinarith) (by linarith)
  have hm0 : 0 ≤ max y 0 := le_max_right _ _
  have h1 : n * (x + K) ≤ n * u := mul_le_mul_of_nonneg_left (by linarith) hn
  have h2 : C * 1 ≤ C * u := mul_le_mul_of_nonneg_left (by linarith) hC
  have hle : 2 + C + max y 0 ≤ A * u := by rw [hA]; nlinarith
  have hlog : Real.log (2 + C + max y 0) ≤ Real.log A + Real.log u := by
    rw [← Real.log_mul hA0.ne' (by linarith)]
    exact Real.log_le_log (by linarith) hle
  have hlA : Real.log A ≤ A := (Real.log_le_sub_one_of_pos hA0).trans (by linarith)
  have hlu : 1 / 2 ≤ Real.log u := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 2) hu2
    have h' := Real.log_two_gt_d9
    linarith
  have h3 : C * Real.log (2 + C + max y 0) ≤ C * (A + Real.log u) :=
    mul_le_mul_of_nonneg_left (by linarith) hC
  have h4 : 2 * (C * A + C) * (1 / 2) ≤ 2 * (C * A + C) * Real.log u :=
    mul_le_mul_of_nonneg_left hlu (by linarith)
  have h5 : 0 ≤ (1 + K) * Real.log u := mul_nonneg (by linarith) (by linarith)
  rw [hD]
  nlinarith

end GlobalTheory.CompanionTheory.LogLin
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

def selM {N : ℕ} (S : Finset (Fin N)) : Matrix (Fin N) (Fin S.card) ℂ :=
  Matrix.of fun a b => if a = S.orderEmbOfFin rfl b then 1 else 0

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end
end

section

open Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem tendsto_limUnder_of_cauchy_rate :
    ∀ (f δ : ℝ → ℝ) (t₁ : ℝ), 0 < t₁ → Filter.Tendsto δ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      (∀ t t', 0 < t' → t' ≤ t → t ≤ t₁ → |f t - f t'| ≤ δ t) →
      Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Filter.limUnder (nhdsWithin 0 (Set.Ioi 0)) f)) ∧
        ∀ t, 0 < t → t ≤ t₁ → |f t - Filter.limUnder (nhdsWithin 0 (Set.Ioi 0)) f| ≤ δ t := by
  intro f δ t₁ ht₁ hδ hrate
  set F : Filter ℝ := nhdsWithin 0 (Set.Ioi 0) with hF

  have hS : ∀ ε > 0, {t | δ t < ε ∧ 0 < t ∧ t ≤ t₁} ∈ F := by
    intro ε hε
    filter_upwards [hδ (Iio_mem_nhds hε),
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ F),
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht₁) : Set.Iic t₁ ∈ F)] with t hδt ht ht₁t
    exact ⟨hδt, ht, ht₁t⟩
  have hC : Cauchy (Filter.map f F) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ⟨f '' {t | δ t < ε ∧ 0 < t ∧ t ≤ t₁}, Filter.image_mem_map (hS ε hε), ?_⟩⟩
    rintro _ ⟨t, ⟨h1, h2, h3⟩, rfl⟩ _ ⟨t', ⟨h1', h2', h3'⟩, rfl⟩
    rw [Real.dist_eq]
    rcases le_total t' t with h | h
    · exact (hrate t t' h2' h h3).trans_lt h1
    · rw [abs_sub_comm]; exact (hrate t' t h2 h h3').trans_lt h1'
  obtain ⟨L, hL⟩ := CompleteSpace.complete hC
  have hlim : Filter.Tendsto f F (nhds (Filter.limUnder F f)) := tendsto_nhds_limUnder ⟨L, hL⟩
  refine ⟨hlim, fun t ht htt => ?_⟩

  have hev : ∀ᶠ t' in F, |f t - f t'| ≤ δ t := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht)] with t' h0 h1
    exact hrate t t' h0 h1 htt
  exact le_of_tendsto (tendsto_const_nhds.sub hlim).abs hev

end GlobalTheory.CompanionTheory.Ar.PB
end
