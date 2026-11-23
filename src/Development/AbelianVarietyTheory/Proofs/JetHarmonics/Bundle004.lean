module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Spectrum
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Vandermonde
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

section

namespace GlobalTheory

open scoped InnerProductSpace

theorem norm_sq_adjoint_add_ge_of_joint_eigenspaces (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] (Vm : Type) [NormedAddCommGroup Vm] [InnerProductSpace ℂ Vm] [FiniteDimensional ℂ Vm] (ι : Type) (S : ι → Submodule ℂ V) (A : Vp →L[ℂ] V) (B : Vm →L[ℂ] V) (wp wm : ι → ℝ) (c : ℝ) (hS : (⨆ i, S i) = ⊤)
    (hw : ∀ i, ∀ v ∈ S i, A (ContinuousLinearMap.adjoint A v) = (wp i : ℂ) • v ∧ B (ContinuousLinearMap.adjoint B v) = (wm i : ℂ) • v)
    (hc : ∀ i, c ≤ wp i ∨ c ≤ wm i) (v : V) :
    c * ‖v‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint A v‖ ^ 2 + ‖ContinuousLinearMap.adjoint B v‖ ^ 2 := by
  have hA : ∀ x : V, (⟪A (ContinuousLinearMap.adjoint A x), x⟫_ℂ).re = ‖ContinuousLinearMap.adjoint A x‖ ^ 2 := by
    intro x
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hB : ∀ x : V, (⟪B (ContinuousLinearMap.adjoint B x), x⟫_ℂ).re = ‖ContinuousLinearMap.adjoint B x‖ ^ 2 := by
    intro x
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hsm : ∀ (r : ℝ) (x : V), (⟪(r : ℂ) • x, x⟫_ℂ).re = r * ‖x‖ ^ 2 := by
    intro r x
    rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]
    congr 1
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  let X : V →ₗ[ℂ] V := (A ∘L ContinuousLinearMap.adjoint A + B ∘L ContinuousLinearMap.adjoint B : V →L[ℂ] V).toLinearMap
  have hX : ∀ x, X x = A (ContinuousLinearMap.adjoint A x) + B (ContinuousLinearMap.adjoint B x) := fun x => rfl
  have hsym : X.IsSymmetric := by
    intro x y
    rw [hX, hX, inner_add_left, inner_add_right]
    rw [← ContinuousLinearMap.adjoint_inner_right A, ← ContinuousLinearMap.adjoint_inner_right B,
      ← ContinuousLinearMap.adjoint_inner_left A, ← ContinuousLinearMap.adjoint_inner_left B]
  have hge : ∀ i, ∀ x ∈ S i, x ≠ 0 → c ≤ wp i + wm i := by
    intro i x hx hx0
    have hn : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx0) 2
    have h1 := hA x
    have h2 := hB x
    rw [(hw i x hx).1, hsm] at h1
    rw [(hw i x hx).2, hsm] at h2
    have p1 : 0 ≤ wp i := by
      have : 0 ≤ wp i * ‖x‖ ^ 2 := by rw [h1]; positivity
      exact nonneg_of_mul_nonneg_left this hn
    have p2 : 0 ≤ wm i := by
      have : 0 ≤ wm i * ‖x‖ ^ 2 := by rw [h2]; positivity
      exact nonneg_of_mul_nonneg_left this hn
    rcases hc i with h | h <;> linarith
  have hev : ∀ (μ : ℝ) (e : V), X e = (μ : ℂ) • e → e ≠ 0 → c ≤ μ := by
    intro μ e he he0
    by_contra hlt
    apply he0
    have hmem : e ∈ (⨆ i, S i)ᗮ := by
      rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
      intro i
      rw [Submodule.mem_orthogonal]
      intro x hx
      by_cases hx0 : x = 0
      · simp [hx0]
      have hle := hge i x hx hx0
      have hXx : X x = ((wp i + wm i : ℝ) : ℂ) • x := by
        rw [hX, (hw i x hx).1, (hw i x hx).2, ← add_smul]; push_cast; rfl
      have h := hsym x e
      rw [hXx, he, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h
      have hne : ((wp i + wm i : ℝ) : ℂ) ≠ (μ : ℂ) := by
        intro h'
        have := Complex.ofReal_injective h'
        apply hlt; linarith
      by_contra h0
      exact hne (mul_right_cancel₀ h0 h)
    rw [hS, Submodule.top_orthogonal_eq_bot] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  have hn : Module.finrank ℂ V = Module.finrank ℂ V := rfl
  set b := hsym.eigenvectorBasis hn with hb
  have hμ : ∀ j, c ≤ hsym.eigenvalues hn j := fun j =>
    hev _ (b j) (hsym.apply_eigenvectorBasis hn j) (b.orthonormal.ne_zero j)
  rw [← hA, ← hB, ← Complex.add_re, ← inner_add_left, ← hX]
  rw [← b.sum_inner_mul_inner (X v) v, Complex.re_sum, ← b.sum_sq_norm_inner_right v, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : ⟪X v, b j⟫_ℂ = (hsym.eigenvalues hn j : ℂ) * ⟪v, b j⟫_ℂ := by
    rw [hsym v (b j), hb, hsym.apply_eigenvectorBasis hn j, inner_smul_right]; rfl
  rw [h1, mul_assoc, Complex.re_ofReal_mul, ← inner_conj_symm v (b j), Complex.conj_mul']
  have : ((‖⟪b j, v⟫_ℂ‖ : ℂ) ^ 2).re = ‖⟪b j, v⟫_ℂ‖ ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [this]
  exact mul_le_mul_of_nonneg_right (hμ j) (sq_nonneg _)

end GlobalTheory
end

section

open Filter
open scoped BigOperators Topology

namespace GlobalTheory.MultiMahler

variable {q : ℕ} [Fact q.Prime]

theorem fwdDiff_tendsto_zero' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[q] E]
    [IsUltrametricDist E] (f : C(ℤ_[q], E)) :
    Tendsto (fun n => (fwdDiff (1 : ℤ_[q]))^[n] f 0) atTop (𝓝 0) := by
  letI : Module ℤ_[q] E := Module.compHom E (algebraMap ℤ_[q] ℚ_[q])
  haveI : IsBoundedSMul ℤ_[q] E := IsBoundedSMul.of_norm_smul_le fun r x =>
    norm_smul_le (r : ℚ_[q]) x
  exact PadicInt.fwdDiff_tendsto_zero f

noncomputable def curryFirst {g : ℕ} (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) :
    C(ℤ_[q], C(Fin g → ℤ_[q], ℂ_[q])) :=
  ContinuousMap.curry (F.comp ⟨fun x : ℤ_[q] × (Fin g → ℤ_[q]) => Fin.cons x.1 x.2,
    Continuous.finCons continuous_fst continuous_snd⟩)

theorem curryFirst_apply {g : ℕ} (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) (t : ℤ_[q])
    (a : Fin g → ℤ_[q]) : curryFirst F t a = F (Fin.cons t a) := rfl

theorem norm_curryFirst_le {g : ℕ} (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) :
    ‖curryFirst F‖ ≤ ‖F‖ := by
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  intro t
  rw [ContinuousMap.norm_le _ (norm_nonneg _)]
  intro a
  exact F.norm_coe_le_norm _

noncomputable def diffFirst {g : ℕ} (m : ℕ) :
    C(Fin (g + 1) → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] C(Fin g → ℤ_[q], ℂ_[q]) where
  toFun F := (fwdDiff (1 : ℤ_[q]))^[m] (curryFirst F) 0
  map_add' F G := by
    have : (curryFirst (F + G) : ℤ_[q] → _) = curryFirst F + curryFirst G := by
      ext t a; simp [curryFirst_apply]
    rw [this, fwdDiff_iter_add]; rfl
  map_smul' r F := by
    have : (curryFirst (r • F) : ℤ_[q] → _) = r • (curryFirst F : ℤ_[q] → _) := by
      ext t a; simp [curryFirst_apply]
    rw [this, fwdDiff_iter_const_smul]; rfl

theorem diffFirst_apply {g : ℕ} (m : ℕ) (F : C(Fin (g + 1) → ℤ_[q], ℂ_[q])) :
    diffFirst m F = (fwdDiff (1 : ℤ_[q]))^[m] (curryFirst F) 0 := rfl

theorem exists_multiDiff (g : ℕ) :
    ∃ D : (Fin g → ℕ) → C(Fin g → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] ℂ_[q],
      (∀ n F, ‖D n F‖ ≤ ‖F‖) ∧
      (∀ n (f : Fin g → C(ℤ_[q], ℂ_[q])) (F : C(Fin g → ℤ_[q], ℂ_[q])),
        (∀ a, F a = ∏ i, f i (a i)) → D n F = ∏ i, (fwdDiff (1 : ℤ_[q]))^[n i] (f i) 0) ∧
      (∀ F, Tendsto (fun n => D n F) cofinite (𝓝 0)) := by
  induction g with
  | zero =>
    refine ⟨fun _ => { toFun := fun F => F 0, map_add' := fun _ _ => rfl,
                       map_smul' := fun _ _ => rfl }, fun n F => F.norm_coe_le_norm _,
      fun n f F hF => by simpa using hF 0, fun F => ?_⟩
    rw [Filter.cofinite_eq_bot]
    exact tendsto_bot
  | succ g ih =>
    obtain ⟨D, h1, h2, h3⟩ := ih
    refine ⟨fun n => (D (Fin.tail n)).comp (diffFirst (n 0)), fun n F => ?_,
      fun n f F hF => ?_, fun F => ?_⟩
    · exact (h1 _ _).trans ((IsUltrametricDist.norm_fwdDiff_iter_apply_le 1 _ 0 _).trans
        (norm_curryFirst_le F))
    · let P : C(Fin g → ℤ_[q], ℂ_[q]) := ⟨fun a => ∏ i, f i.succ (a i), by fun_prop⟩
      have hP : diffFirst (n 0) F = (fwdDiff (1 : ℤ_[q]))^[n 0] (f 0) 0 • P := by
        rw [diffFirst_apply, fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift,
          Finset.sum_smul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_assoc]
        congr 1
        ext a
        simp [curryFirst_apply, hF, Fin.prod_univ_succ, P]
      rw [LinearMap.comp_apply, hP, map_smul, h2 _ (fun i => f i.succ) P (fun _ => rfl),
        Fin.prod_univ_succ]
      rfl
    · refine NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε => ?_
      have hA := NormedAddGroup.tendsto_nhds_zero.mp (fwdDiff_tendsto_zero' (curryFirst F)) ε hε
      rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at hA
      have hB : ∀ m, {n' : Fin g → ℕ | ¬ ‖D n' (diffFirst m F)‖ < ε}.Finite := fun m =>
        Filter.eventually_cofinite.mp (NormedAddGroup.tendsto_nhds_zero.mp (h3 _) ε hε)
      rw [Filter.eventually_cofinite]
      refine (hA.biUnion fun m _ => (hB m).image
        (fun n' => (Fin.cons m n' : Fin (g + 1) → ℕ))).subset fun n hn => ?_
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_image, not_lt] at hn ⊢
      exact ⟨n 0, hn.trans (h1 _ _), Fin.tail n, hn, Fin.cons_self_tail n⟩

noncomputable def binomC (k : ℕ) : C(ℤ_[q], ℂ_[q]) :=
  ⟨fun x => algebraMap ℚ_[q] ℂ_[q] ((mahler k x : ℤ_[q]) : ℚ_[q]),
    (continuous_algebraMap _ _).comp (continuous_subtype_val.comp (mahler k).continuous)⟩

theorem norm_binomC_le (k : ℕ) (x : ℤ_[q]) : ‖binomC k x‖ ≤ 1 := by
  change ‖algebraMap ℚ_[q] ℂ_[q] ((mahler k x : ℤ_[q]) : ℚ_[q])‖ ≤ 1
  rw [norm_algebraMap']
  exact PadicInt.norm_le_one _

theorem binomC_natCast (k n : ℕ) : binomC k (n : ℤ_[q]) = (n.choose k : ℂ_[q]) := by
  change algebraMap ℚ_[q] ℂ_[q] ((mahler k (n : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) = _
  rw [mahler_natCast_eq, PadicInt.coe_natCast, map_natCast]

theorem fwdDiff_binomC (k m : ℕ) :
    (fwdDiff (1 : ℤ_[q]))^[m] (binomC (q := q) k) 0 = if m = k then 1 else 0 := by
  have h := fwdDiff_iter_choose_zero (R := ℤ) k m
  rw [fwdDiff_iter_eq_sum_shift] at h ⊢
  have h' := congrArg (Int.cast : ℤ → ℂ_[q]) h
  simp only [zero_add, nsmul_one, binomC_natCast] at h' ⊢
  simpa using h'

theorem exists_measure_of_bounded_moments :
    ∀ (q : ℕ) [Fact q.Prime] (g : ℕ) (c : (Fin g → ℕ) → ℂ_[q]), (∃ B : ℝ, ∀ n, ‖c n‖ ≤ B) →
      ∃ μ : C(Fin g → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q],
        (∀ B : ℝ, 0 ≤ B → (‖μ‖ ≤ B ↔ ∀ n, ‖c n‖ ≤ B)) ∧
        ∀ (f : Fin g → C(ℤ_[q], ℂ_[q])) (F : C(Fin g → ℤ_[q], ℂ_[q])),
          (∀ a, F a = ∏ i, f i (a i)) →
          HasSum (fun n : Fin g → ℕ => c n * ∏ i, (fwdDiff (1 : ℤ_[q]))^[n i] (f i) 0) (μ F) := by
  intro q _ g c ⟨B₀, hB₀⟩
  obtain ⟨D, h1, h2, h3⟩ := exists_multiDiff (q := q) g
  have hs : ∀ F, Summable fun n => c n * D n F := fun F => by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := (tendsto_zero_iff_norm_tendsto_zero.mp (h3 F)).const_mul B₀
    rw [mul_zero] at this
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) this
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB₀ n) (norm_nonneg _)
  let L : C(Fin g → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] ℂ_[q] :=
    { toFun := fun F => ∑' n, c n * D n F
      map_add' := fun F G => by
        simp only [map_add (f := _), mul_add]
        exact (hs F).tsum_add (hs G)
      map_smul' := fun r F => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        rw [← tsum_mul_left]
        exact tsum_congr fun n => by ring }
  have hL : ∀ B : ℝ, (∀ n, ‖c n‖ ≤ B) → ∀ F, ‖L F‖ ≤ B * ‖F‖ := fun B hB F => by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le fun n => ?_
    rw [norm_mul]
    exact mul_le_mul (hB n) (h1 n F) (norm_nonneg _) ((norm_nonneg _).trans (hB n))
  have hsum : ∀ (f : Fin g → C(ℤ_[q], ℂ_[q])) (F : C(Fin g → ℤ_[q], ℂ_[q])),
      (∀ a, F a = ∏ i, f i (a i)) →
      HasSum (fun n : Fin g → ℕ => c n * ∏ i, (fwdDiff (1 : ℤ_[q]))^[n i] (f i) 0) (L F) := by
    intro f F hF
    have := (hs F).hasSum
    simp only [fun n => h2 n f F hF] at this
    convert this using 1
    exact tsum_congr fun n => by rw [h2 n f F hF]
  refine ⟨L.mkContinuous B₀ (hL B₀ hB₀), fun B hB => ⟨fun hμ n => ?_, fun h => ?_⟩, hsum⟩
  · let P : C(Fin g → ℤ_[q], ℂ_[q]) := ⟨fun a => ∏ i, binomC (n i) (a i), by fun_prop⟩
    have hP : ‖P‖ ≤ 1 := by
      rw [ContinuousMap.norm_le _ zero_le_one]
      intro a
      change ‖∏ i, binomC (n i) (a i)‖ ≤ 1
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun _ _ => norm_binomC_le _ _
    have hv : L P = c n := by
      refine (hsum (fun i => binomC (n i)) P fun _ => rfl).unique ?_
      convert hasSum_single (f := fun m : Fin g → ℕ =>
        c m * ∏ i, (fwdDiff (1 : ℤ_[q]))^[m i] (binomC (q := q) (n i)) 0) n ?_ using 1
      · simp [fwdDiff_binomC]
      · intro m hm
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hm
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [fwdDiff_binomC, if_neg hi]), mul_zero]
    calc ‖c n‖ = ‖L.mkContinuous B₀ (hL B₀ hB₀) P‖ := by rw [← hv]; rfl
      _ ≤ _ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ B * 1 := mul_le_mul hμ hP (norm_nonneg _) hB
      _ = B := mul_one _
  · exact ContinuousLinearMap.opNorm_le_bound _ hB (hL B h)

end GlobalTheory.MultiMahler
end

section

open Finset

namespace GlobalTheory.LamSize

theorem main : ∀ (C b T T' : ℝ) (r N : ℕ), 0 ≤ C → 3 ≤ b → (N : ℝ) ≤ b → b ^ (-(C * ((2 * r + 2 : ℕ) : ℝ))) ≤ T → b ^ (-(C * ((2 * r + 2 : ℕ) : ℝ))) ≤ T' → 1 ≤ b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ)) ∧ (N : ℝ) * b ^ (11 * (2 * r + 2)) ≤ (b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 * (T * T') := by
  intro C b T T' r N hC hb hN hT hT'
  have hm1 : 1 ≤ 2 * r + 2 := by omega
  generalize 2 * r + 2 = m at *
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine ⟨Real.one_le_rpow hb1 (by positivity), ?_⟩
  have hp : 0 < b ^ (-(C * (m : ℝ))) := Real.rpow_pos_of_pos hb0 _
  have hTT : b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ))) ≤ T * T' :=
    mul_le_mul hT hT' hp.le (hp.le.trans hT)
  have key : (b ^ ((6 + C) * (m : ℝ))) ^ 2 * (b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ))))
      = b ^ (12 * m) := by
    rw [sq, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  calc (N : ℝ) * b ^ (11 * m) ≤ b * b ^ (11 * m) := by gcongr
    _ = b ^ (11 * m + 1) := by ring
    _ ≤ b ^ (12 * m) := pow_le_pow_right₀ hb1 (by omega)
    _ = _ := key.symm
    _ ≤ _ := by gcongr

end GlobalTheory.LamSize
end

section

namespace GlobalTheory

theorem vecPoly_mem_span_values (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (Z : ℂ → V)
    (X : ℕ → V) (ν : Fin n → ℂ) (hν : Function.Injective ν)
    (hZ : ∀ s : ℂ, Z s = ∑ j ∈ Finset.range n, s ^ j • X j) :
    (∀ j, j < n → X j ∈ Submodule.span ℂ (Set.range fun i => Z (ν i))) ∧
      ∀ s : ℂ, Z s ∈ Submodule.span ℂ (Set.range fun i => Z (ν i)) := by
  classical
  set W := Submodule.span ℂ (Set.range fun i => Z (ν i)) with hW
  set M : Matrix (Fin n) (Fin n) ℂ := Matrix.vandermonde ν with hM
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hν)
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  have hZν : ∀ i, Z (ν i) = ∑ l : Fin n, M i l • X l := by
    intro i
    rw [hZ, ← Fin.sum_univ_eq_sum_range (fun j => ν i ^ j • X j) n]
    simp [hM, Matrix.vandermonde_apply]
  have hX : ∀ k : Fin n, X k ∈ W := by
    intro k
    have key : ∀ l, ∑ i, M⁻¹ k i * M i l = (1 : Matrix (Fin n) (Fin n) ℂ) k l := fun l => by
      rw [← hinv, Matrix.mul_apply]
    have hsum : ∑ i : Fin n, M⁻¹ k i • Z (ν i) = X k := by
      simp_rw [hZν, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, key, Matrix.one_apply, ite_smul, one_smul, zero_smul]
      simp
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨fun j hj => hX ⟨j, hj⟩, fun s => ?_⟩
  rw [hZ]
  exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hX ⟨j, Finset.mem_range.mp hj⟩)

end GlobalTheory
end

section

namespace GlobalTheory

theorem exists_int_coords_of_regular_param (n : ℕ) (u : ℕ → ℝ)
    (h : ∀ i ∈ Finset.Icc 1 n, ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) :
    ∃ (β : ℂ) (L : Fin (n + 1) → ℤ), StrictAnti L ∧
      (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) ∧
      ∀ i j : Fin (n + 1), (L i : ℝ) - (L j : ℝ) = u ((i : ℕ) + 1) - u ((j : ℕ) + 1) := by
  have key : ∀ j : ℕ, j ≤ n → ∃ z : ℤ, (z : ℝ) = u (j + 1) - u 1 := by
    intro j
    induction j with
    | zero => intro _; exact ⟨0, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨z, hz⟩ := ih (by omega)
      obtain ⟨N, hN⟩ := h (k + 1) (Finset.mem_Icc.2 ⟨by omega, hk⟩)
      refine ⟨z - N - 1, ?_⟩
      push_cast
      linarith
  choose z hz using key
  refine ⟨(u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2, fun j => z j (Nat.lt_succ_iff.1 j.2), ?_, ?_, ?_⟩
  · rw [Fin.strictAnti_iff_succ_lt]
    intro i
    obtain ⟨N, hN⟩ := h (i + 1) (Finset.mem_Icc.2 ⟨by omega, i.2⟩)
    have h1 := hz (i.succ : Fin (n + 1)) (Nat.lt_succ_iff.1 i.succ.2)
    have h2 := hz (i.castSucc : Fin (n + 1)) (Nat.lt_succ_iff.1 i.castSucc.2)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : ((z (i.succ : Fin (n + 1)) (Nat.lt_succ_iff.1 i.succ.2) : ℤ) : ℝ)
        < (z (i.castSucc : Fin (n + 1)) (Nat.lt_succ_iff.1 i.castSucc.2) : ℤ) := by
      rw [h1, h2]
      simp only [Fin.val_succ, Fin.val_castSucc]
      linarith
    exact_mod_cast this
  · intro j
    have h1 := congrArg (fun x : ℝ => (x : ℂ)) (hz j (Nat.lt_succ_iff.1 j.2))
    simp only [Complex.ofReal_intCast, Complex.ofReal_sub] at h1
    simp only [h1]
    ring
  · intro i j
    simp only [hz]
    ring

end GlobalTheory
end

section

open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem card_filter_le_succ_and_sq_sum_le_pow : ∀ (n kk : ℕ) (bv : ℝ), 1 ≤ kk → kk + 1 ≤ n → (n : ℝ) ≤ bv → (univ.filter fun a : Fin n => kk ≤ a.val + 1).card = n + 1 - kk ∧ (18 / 13 : ℝ) ^ 2 + ((n + 1 - kk : ℕ) : ℝ) * (3 * (6 * bv) ^ (n - kk)) ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) := by
  intro n kk bv h1 h2 h3
  refine ⟨?_, ?_⟩
  · have hlt : kk - 1 < n := by omega
    have : (univ.filter fun a : Fin n => kk ≤ a.val + 1) = Finset.Ici (⟨kk - 1, hlt⟩ : Fin n) := by
      ext a
      simp only [mem_filter, mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
      omega
    rw [this, Fin.card_Ici]
    simp only
    omega
  · have e1 : n + 1 - kk = (n - kk) + 1 := by omega
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hM : ((n + 1 - kk : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n + 1 - kk ≤ n)
    have hb : (2 : ℝ) ≤ bv := hn2.trans h3
    have hX : (1 : ℝ) ≤ (6 * bv) ^ (n - kk) := one_le_pow₀ (by linarith)
    have e2 : (6 * bv) ^ (2 * (n + 1 - kk)) = 36 * bv ^ 2 * ((6 * bv) ^ (n - kk)) ^ 2 := by
      rw [e1]; ring
    rw [e2]
    set X := (6 * bv) ^ (n - kk)
    set c := ((n + 1 - kk : ℕ) : ℝ)
    have hX2 : (1 : ℝ) ≤ X ^ 2 := one_le_pow₀ hX
    have hc : c ≤ bv := hM.trans h3
    have h4 : c * X ^ 2 ≤ bv * X ^ 2 := mul_le_mul_of_nonneg_right hc (by positivity)
    have h5 : (9 * bv + 2) * X ^ 2 ≤ 36 * bv ^ 2 * X ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    nlinarith

end GlobalTheory
end
