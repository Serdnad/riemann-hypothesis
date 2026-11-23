module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.Analytic.IteratedFDeriv
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

section

open Matrix WithLp
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace GlobalTheory
namespace MatrixBall

section general

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
lemma norm_toEuclideanLin_le (M : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ‖toEuclideanLin M x‖ ≤ ‖M‖ * ‖x‖ :=
  M.l2_opNorm_mulVec x

lemma dotProduct_mulVec_eq_inner (M : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ M *ᵥ v = ⟪(toLp 2 v : EuclideanSpace ℂ n), toEuclideanLin M (toLp 2 v)⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

lemma inner_conjTranspose_mul (M N : Matrix m n ℂ) (x y : EuclideanSpace ℂ n) :
    ⟪x, toEuclideanLin (Mᴴ * N) y⟫_ℂ = ⟪toEuclideanLin M x, toEuclideanLin N y⟫_ℂ := by
  rw [toLpLin_mul (q := 2), LinearMap.comp_apply, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]

lemma inner_one_sub (M : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ⟪x, toEuclideanLin (1 - Mᴴ * M) x⟫_ℂ = ((‖x‖ ^ 2 - ‖toEuclideanLin M x‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_sub, LinearMap.sub_apply, inner_sub_right, inner_conjTranspose_mul, toLpLin_one,
    LinearMap.id_apply, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp

omit [DecidableEq n] in
lemma isHermitian_one_sub [DecidableEq n] (M : Matrix m n ℂ) : (1 - Mᴴ * M).IsHermitian :=
  isHermitian_one.sub (isHermitian_conjTranspose_mul_self M)

lemma posDef_one_sub_conjTranspose_mul {Z : Matrix m n ℂ} (hZ : ‖Z‖ < 1) :
    (1 - Zᴴ * Z).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (isHermitian_one_sub Z) fun v hv => ?_
  rw [dotProduct_mulVec_eq_inner, inner_one_sub]
  have hx : 0 < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ := by
    rw [norm_pos_iff]; intro h; exact hv (by simpa using h)
  have h1 := norm_toEuclideanLin_le Z (toLp 2 v)
  have h2 : ‖toEuclideanLin Z (toLp 2 v)‖ < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ := by nlinarith
  have h3 := norm_nonneg (toEuclideanLin Z (toLp 2 v))
  exact_mod_cast (by nlinarith : (0 : ℝ) < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 -
    ‖toEuclideanLin Z (toLp 2 v)‖ ^ 2)

theorem norm_lt_one_of_posDef {Z : Matrix m n ℂ} (hP : (1 - Zᴴ * Z).PosDef) : ‖Z‖ < 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have : Z = 0 := by ext i j; exact hn.elim j
    simp [this]
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ n) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 zero_le_one)
    (f := fun x => ‖toEuclideanLin Z x‖)
    ((toEuclideanLin Z).continuous_of_finiteDimensional.norm.continuousOn)
  have hx1 : ‖x‖ = 1 := by simpa using hx
  have hx0 : ofLp x ≠ 0 := by
    intro h
    have : x = 0 := by simpa using h
    simp [this] at hx1
  have h1 := hP.dotProduct_mulVec_pos hx0
  rw [dotProduct_mulVec_eq_inner, inner_one_sub, toLp_ofLp, hx1] at h1
  have h2 : (0 : ℝ) < 1 ^ 2 - ‖toEuclideanLin Z x‖ ^ 2 := by exact_mod_cast h1
  have h3 := norm_nonneg (toEuclideanLin Z x)
  have h4 : ‖toEuclideanLin Z x‖ < 1 := by nlinarith
  refine lt_of_le_of_lt ?_ h4
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm h3 fun y hy => ?_
  exact hmax (by simpa using hy)

theorem posDef_iff_norm_lt_one (Z : Matrix m n ℂ) : (1 - Zᴴ * Z).PosDef ↔ ‖Z‖ < 1 :=
  ⟨norm_lt_one_of_posDef, posDef_one_sub_conjTranspose_mul⟩

end general

section hermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

end hermitian

section boost

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

def invSqrt {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (CFC.sqrt M)⁻¹

def boost (Z : Matrix p q ℂ) : Matrix (p ⊕ q) (p ⊕ q) ℂ :=
  fromBlocks (invSqrt (1 - Z * Zᴴ)) (Z * invSqrt (1 - Zᴴ * Z))
    (Zᴴ * invSqrt (1 - Z * Zᴴ)) (invSqrt (1 - Zᴴ * Z))

section invSqrt

variable {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}

end invSqrt

variable {Z : Matrix p q ℂ}

end boost

end MatrixBall

end GlobalTheory
end
end

section

open Filter Topology
open scoped ContDiff

namespace GlobalTheory

section Def

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

noncomputable def lineDerivList : List E → (E → V) → E → V
  | [], F => F
  | v :: l, F => fun z => lineDeriv 𝕜 (lineDerivList l F) z v

variable {𝕜}

theorem lineDerivList_cons (v : E) (l : List E) (F : E → V) :
    lineDerivList 𝕜 (v :: l) F = fun z => lineDeriv 𝕜 (lineDerivList 𝕜 l F) z v := rfl

theorem lineDerivList_append (l₁ l₂ : List E) (F : E → V) :
    lineDerivList 𝕜 (l₁ ++ l₂) F = lineDerivList 𝕜 l₁ (lineDerivList 𝕜 l₂ F) := by
  induction l₁ with
  | nil => rfl
  | cons v l ih => simp only [List.cons_append, lineDerivList_cons, ih]

theorem lineDerivList_const_smul (l : List E) (c : 𝕜) (F : E → V) :
    lineDerivList 𝕜 l (fun z => c • F z) = fun z => c • lineDerivList 𝕜 l F z := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    simp only [lineDerivList_cons, ih, lineDeriv]
    exact deriv_fun_const_smul_field c _

@[simp] theorem lineDerivList_zero (l : List E) :
    lineDerivList 𝕜 l (fun _ => (0 : V)) = fun _ => 0 := by
  simpa using lineDerivList_const_smul l (0 : 𝕜) (fun _ => (0 : V))

theorem lineDerivList_comp_linearMap {E' : Type*} [AddCommGroup E'] [Module 𝕜 E']
    (L : E' →ₗ[𝕜] E) (l : List E') (F : E → V) :
    lineDerivList 𝕜 l (fun z => F (L z)) = fun z => lineDerivList 𝕜 (l.map L) F (L z) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    simp only [lineDerivList_cons, ih, lineDeriv, List.map_cons, map_add (f := _), map_smul]

theorem lineDerivList_comp_add_const (c : E) (l : List E) (F : E → V) :
    lineDerivList 𝕜 l (fun z => F (z + c)) = fun z => lineDerivList 𝕜 l F (z + c) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    simp only [lineDerivList_cons, ih, lineDeriv, add_right_comm]

theorem lineDerivList_map_smul {κ : Type*} (c : κ → 𝕜) (e : κ → E) (l : List κ) (F : E → V) :
    lineDerivList 𝕜 (l.map fun k => c k • e k) F
      = fun z => (l.map c).prod • lineDerivList 𝕜 (l.map e) F z := by
  induction l with
  | nil => simp
  | cons v l ih =>
    funext z
    simp only [List.map_cons, lineDerivList_cons, ih, lineDeriv_smul, List.prod_cons, mul_smul]
    congr 1
    simp only [lineDeriv]
    exact deriv_fun_const_smul_field _ _

theorem lineDerivList_replicate (n : ℕ) (v : E) (F : E → V) (z : E) (t : 𝕜) :
    lineDerivList 𝕜 (List.replicate n v) F (z + t • v)
      = iteratedDeriv n (fun s : 𝕜 => F (z + s • v)) t := by
  induction n generalizing t with
  | zero => simp [lineDerivList]
  | succ n ih =>
    rw [List.replicate_succ, lineDerivList_cons, iteratedDeriv_succ]
    simp only [lineDeriv, add_assoc, ← add_smul, ih]
    rw [deriv_comp_const_add (f := iteratedDeriv n (fun s : 𝕜 => F (z + s • v))), add_zero]

end Def

section Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

theorem lineDerivList_congr {F G : E → V} {a : E} (h : F =ᶠ[𝓝 a] G) (l : List E) :
    lineDerivList 𝕜 l F =ᶠ[𝓝 a] lineDerivList 𝕜 l G := by
  induction l with
  | nil => exact h
  | cons v l ih =>
    filter_upwards [ih.eventuallyEq_nhds] with z hz
    exact hz.lineDeriv_eq

variable [CompleteSpace V]

theorem analyticAt_lineDeriv {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (v : E) :
    AnalyticAt 𝕜 (fun z => lineDeriv 𝕜 F z v) a := by
  have h1 : AnalyticAt 𝕜 (fun z => fderiv 𝕜 F z v) a :=
    ((ContinuousLinearMap.apply 𝕜 V v).analyticAt _).comp h.fderiv
  refine h1.congr ?_
  filter_upwards [h.eventually_analyticAt] with z hz
  exact hz.differentiableAt.lineDeriv_eq_fderiv.symm

theorem analyticAt_lineDerivList {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (l : List E) :
    AnalyticAt 𝕜 (lineDerivList 𝕜 l F) a := by
  induction l with
  | nil => exact h
  | cons v l ih => exact analyticAt_lineDeriv ih v

theorem lineDerivList_ofFn {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) {n : ℕ} (m : Fin n → E) :
    lineDerivList 𝕜 (List.ofFn m) F a = iteratedFDeriv 𝕜 n F a m := by
  induction n generalizing a with
  | zero => simp [lineDerivList]
  | succ n ih =>
    have hev : lineDerivList 𝕜 (List.ofFn fun i => m i.succ) F
        =ᶠ[𝓝 a] fun z => iteratedFDeriv 𝕜 n F z (Fin.tail m) := by
      filter_upwards [h.eventually_analyticAt] with z hz
      exact ih hz _
    have hd : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n F) a :=
      (h.contDiffAt (n := ω)).differentiableAt_iteratedFDeriv (by simp)
    rw [List.ofFn_succ, lineDerivList_cons, iteratedFDeriv_succ_apply_left]
    dsimp only
    rw [(analyticAt_lineDerivList h _).differentiableAt.lineDeriv_eq_fderiv, hev.fderiv_eq,
      fderiv_continuousMultilinear_apply_const_apply hd]

theorem lineDerivList_eq_iteratedFDeriv {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (l : List E) :
    lineDerivList 𝕜 l F a = iteratedFDeriv 𝕜 l.length F a l.get := by
  rw [← lineDerivList_ofFn h, List.ofFn_get]

theorem lineDerivList_swap {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) (v w : E) :
    lineDerivList 𝕜 [v, w] F a = lineDerivList 𝕜 [w, v] F a := by
  have h1 := lineDerivList_ofFn h ![v, w]
  have h2 := lineDerivList_ofFn h ![w, v]
  have h3 := (h.contDiffAt (n := ω)).iteratedFDeriv_comp_perm ![v, w] (Equiv.swap 0 1)
  have h4 : ![v, w] ∘ (Equiv.swap (0 : Fin 2) 1) = ![w, v] := by
    funext i; fin_cases i <;> simp
  rw [h4] at h3
  simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] at h1 h2
  rw [h1, h2, h3]

theorem lineDerivList_perm {F : E → V} {a : E} (h : AnalyticAt 𝕜 F a) {l₁ l₂ : List E}
    (hl : l₁.Perm l₂) : lineDerivList 𝕜 l₁ F a = lineDerivList 𝕜 l₂ F a := by
  induction hl generalizing a with
  | nil => rfl
  | cons v _ ih =>
    refine Filter.EventuallyEq.lineDeriv_eq ?_
    filter_upwards [h.eventually_analyticAt] with z hz
    exact ih hz
  | swap v w l => exact lineDerivList_swap (analyticAt_lineDerivList h l) w v
  | trans _ _ ih₁ ih₂ => exact (ih₁ h).trans (ih₂ h)

theorem lineDerivList_add {F G : E → V} {a : E} (hF : AnalyticAt 𝕜 F a) (hG : AnalyticAt 𝕜 G a)
    (l : List E) :
    lineDerivList 𝕜 l (fun z => F z + G z) a
      = lineDerivList 𝕜 l F a + lineDerivList 𝕜 l G a := by
  have hFG : AnalyticAt 𝕜 (fun z => F z + G z) a := hF.add hG
  rw [lineDerivList_eq_iteratedFDeriv hFG, lineDerivList_eq_iteratedFDeriv hF,
    lineDerivList_eq_iteratedFDeriv hG,
    fun_iteratedFDeriv_add_apply (hF.contDiffAt) (hG.contDiffAt)]
  rfl

theorem lineDerivList_sum {κ : Type*} (s : Finset κ) {F : κ → E → V} {a : E}
    (hF : ∀ k ∈ s, AnalyticAt 𝕜 (F k) a) (l : List E) :
    lineDerivList 𝕜 l (fun z => ∑ k ∈ s, F k z) a = ∑ k ∈ s, lineDerivList 𝕜 l (F k) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hs : ∀ k ∈ s, AnalyticAt 𝕜 (F k) a := fun k hk => hF k (Finset.mem_insert_of_mem hk)
    simp only [Finset.sum_insert hj]
    rw [lineDerivList_add (hF j (Finset.mem_insert_self _ _)) (Finset.analyticAt_fun_sum _ hs),
      ih hs]

end Analytic

end GlobalTheory
end

section

noncomputable section

open Module Submodule
open scoped InnerProductSpace

namespace GlobalTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_int_comb_norm_sub_sq_le (k : ℕ) (v : Fin k → E) {x : E}
    (hx : x ∈ span ℝ (Set.range v)) :
    ∃ w ∈ span ℤ (Set.range v), ‖x - w‖ ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) / 4 := by
  induction k generalizing x with
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    have : x = 0 := by simpa using hx
    simp [this]
  | succ k ih =>
    set U : Submodule ℝ E := span ℝ (Set.range (Fin.init v)) with hU
    have : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℝ).1 hx
    set a := c (Fin.last k)
    set u := v (Fin.last k)
    set y := ∑ i : Fin k, c i.castSucc • v i.castSucc with hy
    have hyU : y ∈ U := sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
    set p := U.starProjection u
    have hpU : p ∈ U := U.starProjection_apply_mem u
    have hq : u - p ∈ Uᗮ := U.sub_starProjection_mem_orthogonal u
    set t : ℝ := a - round a
    have ht : |t| ≤ 1 / 2 := abs_sub_round a
    obtain ⟨w, hw, hle⟩ := ih (Fin.init v) (x := y + t • p) (add_mem hyU (smul_mem _ _ hpU))
    have hwU : w ∈ U := span_subset_span ℤ ℝ _ hw
    refine ⟨w + round a • u, add_mem (span_mono ?_ hw) (smul_mem _ _ (subset_span ⟨_, rfl⟩)), ?_⟩
    · rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩
    have e : ∑ i, c i • v i - (w + round a • u) = (y + t • p - w) + t • (u - p) := by
      rw [Fin.sum_univ_castSucc, ← Int.cast_smul_eq_zsmul ℝ]
      simp only [t]; module
    have hz : y + t • p - w ∈ U := sub_mem (add_mem hyU (smul_mem _ _ hpU)) hwU
    have horth : ⟪y + t • p - w, t • (u - p)⟫_ℝ = 0 :=
      U.inner_right_of_mem_orthogonal hz (smul_mem _ _ hq)
    have hup : ‖u - p‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      have h1 : ⟪p, u - p⟫_ℝ = 0 := U.inner_right_of_mem_orthogonal hpU hq
      have h2 := norm_add_sq_real p (u - p)
      rw [add_sub_cancel, h1] at h2
      nlinarith [sq_nonneg ‖p‖]
    have ht2 : t ^ 2 ≤ 1 / 4 := by
      rw [← sq_abs]; nlinarith [abs_nonneg t]
    rw [e, norm_add_sq_real, horth, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Fin.sum_univ_castSucc]
    have : t ^ 2 * ‖u - p‖ ^ 2 ≤ 1 / 4 * ‖u‖ ^ 2 :=
      mul_le_mul ht2 hup (sq_nonneg _) (by norm_num)
    have hle' : ‖y + t • p - w‖ ^ 2 ≤ (∑ i : Fin k, ‖v i.castSucc‖ ^ 2) / 4 := hle
    linarith

variable {L : Submodule ℤ E}

end GlobalTheory
end
end

section

open Metric MeasureTheory Module Set

namespace GlobalTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem finset_card_le_of_separated (s : Finset E) {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) (x : E)
    (hs : ∀ a ∈ s, dist a x ≤ R) (hsep : (s : Set E).Pairwise fun a b => d ≤ dist a b) :
    (s.card : ℝ) ≤ (1 + 2 * R / d) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have hδ : 0 < d / 2 := by positivity
  have hρ : 0 < R + d / 2 := by positivity
  have D : Set.Pairwise (s : Set E) (Function.onFun Disjoint fun c => ball (c : E) (d / 2)) := by
    intro a ha b hb hab
    exact ball_disjoint_ball (by have := hsep ha hb hab; linarith)
  have hsub : (⋃ c ∈ s, ball (c : E) (d / 2)) ⊆ ball x (R + d / 2) := by
    refine iUnion₂_subset fun a ha => ball_subset_ball' ?_
    have := hs a ha
    linarith
  have I : (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((R + d / 2) ^ finrank ℝ E) * μ (ball 0 1) := by
    calc (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) * μ (ball 0 1)
        = μ (⋃ c ∈ s, ball (c : E) (d / 2)) := by
          rw [measure_biUnion_finset D fun c _ => measurableSet_ball]
          simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball x (R + d / 2)) := measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have J : (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) ≤
      ENNReal.ofReal ((R + d / 2) ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) * (d / 2) ^ finrank ℝ E ≤ (R + d / 2) ^ finrank ℝ E := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top J
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at this
  have e : 1 + 2 * R / d = (R + d / 2) / (d / 2) := by field_simp; ring
  rw [e, div_pow, le_div_iff₀ (by positivity)]
  exact K

theorem one_add_two_mul_div_pow_le {d R : ℝ} (hd : 0 < d) (hR : d ≤ R) (n : ℕ) :
    (1 + 2 * R / d) ^ n ≤ (3 * R / d) ^ n := by
  have hR0 : 0 ≤ R := hd.le.trans hR
  refine pow_le_pow_left₀ (by positivity) ?_ n
  have h1 : 1 ≤ R / d := (one_le_div hd).2 hR
  have : 3 * R / d = R / d + 2 * R / d := by ring
  linarith

end GlobalTheory
end
