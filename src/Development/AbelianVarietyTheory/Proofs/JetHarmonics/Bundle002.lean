module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.Topology.MetricSpace.Perfect

@[expose] public section

section

namespace GlobalTheory

open Module


open Module in
theorem _root_.GlobalTheory.ev_starProjection_eigenspace_eq_residue :
    ∀ (Y : Type) [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (t : ℕ) (m : Fin t → ℂ) (s : ℂ) (Om : Module.End ℂ Y) (ev : Y →ₗ[ℂ] V) (K : ℂ → (Y →ₗ[ℂ] V)) (q : ℂ → ℂ) (y : Y) (v : V) (l : Fin t), Function.Injective m → Om.IsSymmetric → (∀ (lam : ℂ) (x : Y), x ≠ 0 → Om x = lam • x → ∃ j, lam = m j + s) → (∀ (u : ℂ) (x : Y), K u ((u - s) • x + Om x) = (∏ j, (u + m j)) • ev x) → Continuous q → (∀ u, K u y = q u • v) → ev ((Module.End.eigenspace Om (m l + s)).starProjection y) = (q (-m l) / ∏ j ∈ Finset.univ.erase l, (m j - m l)) • v := by
  intro Y _ _ _ V _ _ t m s Om ev K q y v l hm hOm hspec hK hq hKy
  set P : Fin t → Y → Y := fun j x => (Module.End.eigenspace Om (m j + s)).starProjection x with hP
  set c : Fin t → ℂ → ℂ := fun j u => ∏ k ∈ Finset.univ.erase j, (u + m k) with hc
  have key : ∀ x : Y, ∀ u : ℂ, (∏ k, (u + m k)) • K u x = (∏ k, (u + m k)) • ∑ j, c j u • ev (P j x) := by
    intro x u
    have hx : x ∈ ⨆ μ, Module.End.eigenspace Om μ := by
      rw [Submodule.orthogonal_eq_bot_iff.mp hOm.orthogonalComplement_iSup_eigenspaces_eq_bot]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (fun μ => Module.End.eigenspace Om μ) (motive := fun x => (∏ k, (u + m k)) • K u x = (∏ k, (u + m k)) • ∑ j, c j u • ev (P j x)) hx ?_ ?_ ?_
    · intro μ x hxμ
      by_cases hx0 : x = 0
      · subst hx0; simp [hP]
      have hOmx : Om x = μ • x := Module.End.mem_eigenspace_iff.mp hxμ
      obtain ⟨i, rfl⟩ := hspec μ x hx0 hOmx
      have hPx : ∀ j, P j x = if j = i then x else 0 := by
        intro j
        split_ifs with hji
        · subst hji; exact Submodule.starProjection_eq_self_iff.mpr hxμ
        · have hne : m j + s ≠ m i + s := fun h => hji (hm (add_right_cancel h))
          have hortho := hOm.orthogonalFamily_eigenspaces.isOrtho hne
          exact (Submodule.starProjection_apply_eq_zero_iff _).mpr (hortho.symm hxμ)
      have hsum : ∑ j, c j u • ev (P j x) = c i u • ev x := by
        rw [Finset.sum_eq_single i (fun j _ hji => by rw [hPx, if_neg hji, map_zero, smul_zero]) (by simp), hPx, if_pos rfl]
      have hKx : (u + m i) • K u x = (∏ k, (u + m k)) • ev x := by
        rw [← hK u x, hOmx, ← map_smul]
        congr 1
        rw [← add_smul]; congr 1; ring
      have hprod : ∏ k, (u + m k) = c i u * (u + m i) := by
        simp only [hc]; exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
      rw [hsum, smul_comm (∏ k, (u + m k)) (c i u), ← hKx, hprod, mul_smul]
    · simp [hP]
    · intro x₁ x₂ h₁ h₂
      simp only [hP] at h₁ h₂ ⊢
      simp only [map_add (f := _), smul_add, Finset.sum_add_distrib, h₁, h₂]
  have hgen : ∀ u, ∏ k, (u + m k) ≠ 0 → q u • v = ∑ j, c j u • ev (P j y) := by
    intro u hu
    rw [← hKy]
    exact smul_right_injective V hu (key y u)
  have hdense : Dense {u : ℂ | ∏ k, (u + m k) ≠ 0} := by
    have hfin : {u : ℂ | ∏ k, (u + m k) = 0}.Countable := by
      apply Set.Finite.countable
      apply (Set.finite_range (fun k => -m k)).subset
      intro u hu
      simp only [Set.mem_setOf_eq, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and] at hu
      obtain ⟨k, hk⟩ := hu
      exact ⟨k, by linear_combination -hk⟩
    simpa [Set.compl_setOf] using hfin.dense_compl ℝ
  have hcont : Continuous fun u => ∑ j, c j u • ev (P j y) := by
    simp only [hc]; fun_prop
  have hf : Continuous fun u => q u • v := hq.smul continuous_const
  have hl := congrFun (Continuous.ext_on hdense hf hcont hgen) (-m l)
  rw [Finset.sum_eq_single l (fun j _ hjl => by
    simp only [hc]
    rw [Finset.prod_eq_zero (i := l) (Finset.mem_erase.mpr ⟨Ne.symm hjl, Finset.mem_univ l⟩) (by ring), zero_smul]) (by simp)] at hl
  have hcl : c l (-m l) = ∏ j ∈ Finset.univ.erase l, (m j - m l) :=
    Finset.prod_congr rfl (fun k _ => by ring)
  have hD : ∏ j ∈ Finset.univ.erase l, (m j - m l) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j hj => sub_ne_zero.mpr (hm.ne (Finset.ne_of_mem_erase hj)))
  rw [hcl] at hl
  change ev (P l y) = _
  rw [div_eq_inv_mul, mul_smul, hl, smul_smul, inv_mul_cancel₀ hD, one_smul]

end GlobalTheory
end

section

open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem re_inner_sum_eigen_le {N ι : Type} [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    [Fintype ι] (B : N →ₗ[ℂ] N) (hB : B.IsSymmetric) (C : ℝ) (v : ι → N) (l : ι → ℝ)
    (hv : ∀ i, B (v i) = (l i : ℂ) • v i) (hl : ∀ i, l i ≤ C) :
    (⟪∑ i, v i, B (∑ i, v i)⟫_ℂ).re ≤ C * ‖∑ i, v i‖ ^ 2 := by
  have key : ∀ i j, ((C : ℂ) - l j) * ⟪v i, v j⟫_ℂ =
      ⟪((√(C - l i) : ℝ) : ℂ) • v i, ((√(C - l j) : ℝ) : ℂ) • v j⟫_ℂ := by
    intro i j
    rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc]
    by_cases h : l i = l j
    · rw [h, ← Complex.ofReal_mul, Real.mul_self_sqrt (sub_nonneg.2 (hl j))]
      push_cast
      rfl
    · have h1 := hB (v i) (v j)
      rw [hv, hv, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
      have h2 : ((l i : ℂ) - l j) * ⟪v i, v j⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
      have h3 : ((l i : ℂ) - l j) ≠ 0 := by
        rw [sub_ne_zero]; exact_mod_cast h
      have h4 : ⟪v i, v j⟫_ℂ = 0 := (mul_eq_zero.1 h2).resolve_left h3
      rw [h4, mul_zero, mul_zero]
  have hsum : (C : ℂ) * ⟪∑ i, v i, ∑ i, v i⟫_ℂ - ⟪∑ i, v i, B (∑ i, v i)⟫_ℂ =
      ⟪∑ i, ((√(C - l i) : ℝ) : ℂ) • v i, ∑ i, ((√(C - l i) : ℝ) : ℂ) • v i⟫_ℂ := by

    rw [map_sum]
    simp only [sum_inner, inner_sum, ← key, hv, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right, sub_mul]
  have hre := congrArg Complex.re hsum
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hre
  simp only [Complex.coe_algebraMap, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.sub_re, Complex.ofReal_re] at hre
  nlinarith [sq_nonneg ‖∑ i, ((√(C - l i) : ℝ) : ℂ) • v i‖]

theorem re_inner_le_on_image_of_intertwining :
    ∀ (T N : Type) [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]
      [NormedAddCommGroup N] [InnerProductSpace ℂ N] (Φ : T →ₗ[ℂ] N) (A : T →ₗ[ℂ] T)
      (B : N →ₗ[ℂ] N) (C : ℝ), A.IsSymmetric → B.IsSymmetric → (∀ x, Φ (A x) = B (Φ x)) →
      (∀ x, (⟪x, A x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) →
      ∀ x, (⟪Φ x, B (Φ x)⟫_ℂ).re ≤ C * ‖Φ x‖ ^ 2 := by
  intro T N _ _ _ _ _ Φ A B C hA hB hΦ hC x
  set b := hA.eigenvectorBasis (n := Module.finrank ℂ T) rfl with hb
  set l := hA.eigenvalues (n := Module.finrank ℂ T) rfl with hl
  have hAb : ∀ i, A (b i) = (l i : ℂ) • b i := fun i => hA.apply_eigenvectorBasis rfl i
  have hle : ∀ i, l i ≤ C := by
    intro i
    have h := hC (b i)
    rw [hAb, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i] at h
    simpa using h
  have hx : Φ x = ∑ i, Φ (b.repr x i • b i) := by

    rw [← map_sum, b.sum_repr]
  rw [hx]
  refine re_inner_sum_eigen_le B hB C _ l (fun i => ?_) hle
  rw [← hΦ, map_smul A, hAb, smul_comm, map_smul]

end GlobalTheory
end

section

open MeasureTheory Filter Topology

namespace GlobalTheory

theorem memLp_and_tendsto_integral_inner_of_eventually_eq : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (a : ℝ → X → E) (u : X → E) (h : X → ℝ), Integrable h μ → (∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (a ε) μ) → (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂μ, ‖a ε x‖ ^ 2 ≤ h x) → (∀ᵐ x ∂μ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), a ε x = u x) → MemLp u 2 μ ∧ Tendsto (fun ε : ℝ => ∫ x, inner ℂ (a ε x) (u x) ∂μ) (𝓝[>] 0) (𝓝 (((∫ x, ‖u x‖ ^ 2 ∂μ : ℝ) : ℂ))) := by
  intro X _ μ E _ _ a u h hh hm hb he

  obtain ⟨s, hs⟩ := (𝓝[>] (0 : ℝ)).exists_seq_tendsto
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hs.eventually (hm.and hb))
  have hs' : Tendsto (fun n => s (n + N)) atTop (𝓝[>] (0 : ℝ)) :=
    hs.comp (tendsto_add_atTop_nat N)
  have hev : ∀ᵐ x ∂μ, ∀ᶠ n in atTop, a (s (n + N)) x = u x := by
    filter_upwards [he] with x hx
    exact hs'.eventually hx
  have hu : AEStronglyMeasurable u μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n => a (s (n + N)))
      (fun n => (hN (n + N) (Nat.le_add_left _ _)).1) ?_
    filter_upwards [hev] with x hx
    exact tendsto_const_nhds.congr' (hx.mono fun n hn => hn.symm)
  have hub : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ h x := by
    have h1 : ∀ᵐ x ∂μ, ∀ n, ‖a (s (n + N)) x‖ ^ 2 ≤ h x :=
      ae_all_iff.2 fun n => (hN (n + N) (Nat.le_add_left _ _)).2
    filter_upwards [hev, h1] with x hx h1x
    obtain ⟨n, hn⟩ := hx.exists
    rw [← hn]; exact h1x n
  refine ⟨?_, ?_⟩
  · rw [memLp_two_iff_integrable_sq_norm hu]
    refine hh.mono' (hu.norm.pow 2) ?_
    filter_upwards [hub] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact hx
  · have key : (((∫ x, ‖u x‖ ^ 2 ∂μ : ℝ) : ℂ)) = ∫ x, inner ℂ (u x) (u x) ∂μ := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [key]
    refine tendsto_integral_filter_of_dominated_convergence h ?_ ?_ hh ?_
    · filter_upwards [hm] with ε hε
      exact hε.inner hu
    · filter_upwards [hb] with ε hε
      filter_upwards [hε, hub] with x h1 h2
      have := norm_inner_le_norm (𝕜 := ℂ) (a ε x) (u x)
      nlinarith [sq_nonneg (‖a ε x‖ - ‖u x‖)]
    · filter_upwards [he] with x hx
      exact tendsto_const_nhds.congr' (hx.mono fun ε hε => by simp only [hε])

end GlobalTheory
end

section

open MeasureTheory Filter Topology

namespace GlobalTheory

theorem tendsto_integral_inner_of_tendsto_eLpNorm_two :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v v' : ℕ → X → E) (u u' : X → E), (∀ n, MemLp (v n) 2 μ) → (∀ n, MemLp (v' n) 2 μ) → MemLp u 2 μ → MemLp u' 2 μ → Tendsto (fun n => eLpNorm (v n - u) 2 μ) atTop (𝓝 0) → Tendsto (fun n => eLpNorm (v' n - u') 2 μ) atTop (𝓝 0) → Tendsto (fun n => ∫ x, inner ℂ (v' n x) (v n x) ∂μ) atTop (𝓝 (∫ x, inner ℂ (u' x) (u x) ∂μ)) := by
  intro X _ μ E _ _ v v' u u' hv hv' hu hu' h h'
  have key : ∀ (f g : X → E) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ),
      ∫ x, inner ℂ (f x) (g x) ∂μ = inner ℂ (hf.toLp f) (hg.toLp g) := by
    intro f g hf hg
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  have h1 : Tendsto (fun n => (hv n).toLp (v n)) atTop (𝓝 (hu.toLp u)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv u hu).2 h
  have h2 : Tendsto (fun n => (hv' n).toLp (v' n)) atTop (𝓝 (hu'.toLp u')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v' hv' u' hu').2 h'
  rw [key u' u hu' hu]
  simp_rw [fun n => key (v' n) (v n) (hv' n) (hv n)]
  exact h2.inner h1

end GlobalTheory
end

section

open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem norm_eigen_le_pow_mul_norm_sum {H κ : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [DecidableEq κ] (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (lam : κ → ℂ) (s : κ) (Bd : ℝ)
    (hBd : 0 ≤ Bd) (E : Finset κ) :
    (∀ j ∈ E, 1 ≤ ‖lam s - lam j‖) → (∀ j ∈ E, ∀ x ∈ VV, ‖T x - lam j • x‖ ≤ Bd * ‖x‖) →
    ∀ v : κ → H, (∀ i, v i ∈ VV ∧ T (v i) = lam i • v i) →
      ‖v s‖ ≤ Bd ^ E.card * ‖v s + ∑ i ∈ E, v i‖ := by
  induction E using Finset.induction_on with
  | empty => intro _ _ v _; simp
  | insert j E hj ih =>
    intro h1 h2 v hv
    have hw : ∀ i, (lam i - lam j) • v i ∈ VV ∧
        T ((lam i - lam j) • v i) = lam i • (lam i - lam j) • v i := fun i =>
      ⟨VV.smul_mem _ (hv i).1, by rw [map_smul, (hv i).2, smul_comm]⟩
    have hih := ih (fun k hk => h1 k (mem_insert_of_mem hk))
      (fun k hk => h2 k (mem_insert_of_mem hk)) (fun i => (lam i - lam j) • v i) hw
    have hy : v s + ∑ i ∈ insert j E, v i ∈ VV :=
      VV.add_mem (hv s).1 (VV.sum_mem fun i _ => (hv i).1)
    have hT := h2 j (mem_insert_self j E) _ hy
    have heq : T (v s + ∑ i ∈ insert j E, v i) - lam j • (v s + ∑ i ∈ insert j E, v i)
        = (lam s - lam j) • v s + ∑ i ∈ E, (lam i - lam j) • v i := by
      rw [sum_insert hj]

      simp only [map_add (f := _), map_sum, (hv _).2, smul_add, smul_sum, sub_smul, sum_sub_distrib]
      abel
    rw [heq] at hT
    have hs : ‖v s‖ ≤ ‖(lam s - lam j) • v s‖ := by
      rw [norm_smul]
      exact le_mul_of_one_le_left (norm_nonneg _) (h1 j (mem_insert_self j E))
    rw [card_insert_of_notMem hj, pow_succ, mul_assoc]
    exact hs.trans (hih.trans (mul_le_mul_of_nonneg_left hT (pow_nonneg hBd _)))

theorem norm_node_projector_le :
    ∀ (H κ : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [Fintype κ] [DecidableEq κ] (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (p : κ → H →ₗ[ℂ] H) (lam : κ → ℂ) (Nd : Finset κ) (s : κ) (Bd Cn : ℝ), s ∈ Nd → 0 ≤ Bd → (∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ T (p i x) = lam i • p i x) → (∀ x ∈ VV, T x ∈ VV) → (∀ j ∈ Nd.erase s, 1 ≤ ‖lam s - lam j‖) → (∀ j ∈ Nd.erase s, ∀ x ∈ VV, ‖T x - lam j • x‖ ≤ Bd * ‖x‖) → (∀ x ∈ VV, ‖∑ i ∈ Nd, p i x‖ ≤ Cn * ‖x‖) → ∀ x ∈ VV, ‖p s x‖ ≤ Cn * Bd ^ (Nd.erase s).card * ‖x‖ := by
  intro H κ _ _ _ _ VV T p lam Nd s Bd Cn hs hBd hp _ h1 h2 hC x hx
  have h := norm_eigen_le_pow_mul_norm_sum VV T lam s Bd hBd (Nd.erase s) h1 h2
    (fun i => p i x) (fun i => hp i x hx)
  have hsum : p s x + ∑ i ∈ Nd.erase s, p i x = ∑ i ∈ Nd, p i x :=
    add_sum_erase Nd (fun i => p i x) hs
  rw [hsum] at h
  calc ‖p s x‖ ≤ Bd ^ (Nd.erase s).card * ‖∑ i ∈ Nd, p i x‖ := h
    _ ≤ Bd ^ (Nd.erase s).card * (Cn * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hC x hx) (pow_nonneg hBd _)
    _ = Cn * Bd ^ (Nd.erase s).card * ‖x‖ := by ring

end GlobalTheory
end

section

open MeasureTheory Filter Topology

namespace GlobalTheory

theorem eLpNorm_two_le_ofReal_sqrt_of_integral_le {X : Type} [MeasurableSpace X] {μ : Measure X} {E : Type}
    [NormedAddCommGroup E] {f : X → E} (hf : MemLp f 2 μ) {c : ℝ}
    (h : ∫ x, ‖f x‖ ^ 2 ∂μ ≤ c) : eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt c) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  have h2 : (2 : ENNReal).toReal = (2 : ℝ) := by norm_num
  rw [h2]
  have h3 : ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
    simp only [Real.rpow_two]
  rw [h3, Real.sqrt_eq_rpow, one_div]
  exact Real.rpow_le_rpow (integral_nonneg fun x => by positivity) h (by norm_num)

theorem memLp_two_and_tendsto_of_cauchy_of_ae_tendsto :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] (v : ℕ → X → E) (u : X → E) (K : ℝ), (∀ n, MemLp (v n) 2 μ) → (∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 (u x))) → (∀ n m : ℕ, n ≤ m → ∫ x, ‖v n x - v m x‖ ^ 2 ∂μ ≤ K / ((n : ℝ) + 1)) → MemLp u 2 μ ∧ Tendsto (fun n => eLpNorm (v n - u) 2 μ) atTop (𝓝 0) := by
  intro X _ μ E _ v u K hv hlim hC
  have hu : AEStronglyMeasurable u μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hv n).aestronglyMeasurable) hlim
  have hb : ∀ n, eLpNorm (v n - u) 2 μ ≤ ENNReal.ofReal (Real.sqrt (K / ((n : ℝ) + 1))) := by
    intro n
    have hF := Lp.eLpNorm_lim_le_liminf_eLpNorm (μ := μ) (p := 2) (f := fun m => v n - v m)
      (fun m => ((hv n).sub (hv m)).aestronglyMeasurable) (v n - u)
      ((hv n).aestronglyMeasurable.sub hu)
      (by
        filter_upwards [hlim] with x hx
        exact tendsto_const_nhds.sub hx)
    refine hF.trans (liminf_le_of_frequently_le' (Eventually.frequently ?_))
    filter_upwards [eventually_ge_atTop n] with m hm
    exact eLpNorm_two_le_ofReal_sqrt_of_integral_le ((hv n).sub (hv m)) (hC n m hm)
  refine ⟨?_, ?_⟩
  · have h0 : MemLp (v 0 - u) 2 μ :=
      memLp_iff.mpr ((hb 0).trans_lt ENNReal.ofReal_lt_top)
    have := (hv 0).sub h0
    simpa using this
  · have h1 : Tendsto (fun n : ℕ => K / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt (K / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (h1.sqrt)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
      (fun _ => bot_le) hb

end GlobalTheory
end

section

set_option autoImplicit false

open Cardinal

namespace GlobalTheory.PadicComplexIso

theorem exists_ringEquiv_over (R K L : Type) [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] [Algebra R K] [Algebra R L] (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ e : K ≃+* L, ∀ x : R, e (algebraMap R K x) = algebraMap R L x := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have hL : ℵ₀ < #L := hKL ▸ hK
  have hsK : #K = #s := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK
  have htL : #L = #t := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR hL
  obtain ⟨e⟩ : Nonempty (s ≃ t) := Cardinal.eq.1 (hsK.symm.trans (hKL.trans htL))
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e0 : Algebra.adjoin R (Set.range ((↑) : s → K)) ≃ₐ[R] Algebra.adjoin R (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L e0.toRingEquiv, fun x => ?_⟩
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

theorem mk_le_continuum_of_denseRange {X Y : Type} [MetricSpace Y] (f : X → Y)
    (hf : DenseRange f) (hX : #X ≤ 𝔠) : #Y ≤ 𝔠 := by
  have hex : ∀ (y : Y) (n : ℕ), ∃ x, dist (f x) y < 1 / ((n : ℝ) + 1) := by
    intro y n
    obtain ⟨x, hx⟩ := Metric.denseRange_iff.1 hf y (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    exact ⟨x, by rw [dist_comm]; exact hx⟩
  choose g hg using hex
  have hlim : ∀ y, Filter.Tendsto (fun n => f (g y n)) Filter.atTop (nhds y) := by
    intro y
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hg y n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hinj : Function.Injective g := by
    intro y y' h
    have h2 := hlim y'
    rw [← h] at h2
    exact tendsto_nhds_unique (hlim y) h2
  calc #Y ≤ #(ℕ → X) := Cardinal.mk_le_of_injective hinj
    _ = #X ^ ℵ₀ := by rw [← Cardinal.mk_nat, Cardinal.power_def]
    _ ≤ 𝔠 ^ ℵ₀ := Cardinal.power_le_power_right hX
    _ = 𝔠 := Cardinal.continuum_power_aleph0

theorem mk_padicComplex (q : ℕ) [Fact q.Prime] : #ℂ_[q] = 𝔠 := by
  apply le_antisymm
  · have hQp : #ℚ_[q] ≤ 𝔠 :=
      mk_le_continuum_of_denseRange _ (Padic.denseRange_ratCast q)
        (by rw [Cardinal.mkRat]; exact Cardinal.aleph0_le_continuum)
    have hAl : #(PadicAlgCl q) ≤ 𝔠 :=
      (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[q] (PadicAlgCl q)).trans
        (max_le hQp Cardinal.aleph0_le_continuum)
    exact mk_le_continuum_of_denseRange _ (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl q)) hAl
  · obtain ⟨g, -, -, hg⟩ :=
      (PerfectSpace.univ_perfect (α := ℂ_[q])).exists_nat_bool_injection Set.univ_nonempty
    calc 𝔠 = #(ℕ → Bool) := by
          rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]
      _ ≤ #ℂ_[q] := Cardinal.mk_le_of_injective hg

theorem exists_ringEquiv_extending : ∀ (q : ℕ) [Fact q.Prime]
    (lam : algebraicClosure ℚ ℂ →+* ℂ_[q]),
    ∃ ι : ℂ ≃+* ℂ_[q], ∀ x : algebraicClosure ℚ ℂ, ι (x : ℂ) = lam x := by
  intro q _ lam
  let _ : Algebra (algebraicClosure ℚ ℂ) ℂ_[q] := lam.toAlgebra
  have _ : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hR : #(algebraicClosure ℚ ℂ) ≤ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ (algebraicClosure ℚ ℂ)).trans
      (by rw [Cardinal.mkRat, max_self])
  have hK : ℵ₀ < #ℂ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  obtain ⟨e, he⟩ := exists_ringEquiv_over (algebraicClosure ℚ ℂ) ℂ ℂ_[q] hR hK
    (by rw [Cardinal.mk_complex, mk_padicComplex])
  exact ⟨e, fun x => he x⟩

end GlobalTheory.PadicComplexIso
end
