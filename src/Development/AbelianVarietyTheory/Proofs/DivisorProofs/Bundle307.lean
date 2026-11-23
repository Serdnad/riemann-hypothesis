module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle206
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsMulEqPolynomialWeierstrassP
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassPAddOfNeOfDerivNeZero
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle204
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle147
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.RingTheory.FiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle202
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle205
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Topology.Algebra.Polynomial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Mathlib.NumberTheory.ModularForms.SlashActions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle042

@[expose] public section

section

open scoped Matrix Nat

namespace GlobalTheory.GaussComplexForm

theorem exists_schwartz_cexp_neg_form : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ),
    0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∃ g : SchwartzMap V ℂ, (∀ x, g x = Complex.exp (-(Q x x))) ∧ ∀ x p, fderiv ℝ (⇑g) x p = -(Q x p + Q p x) * g x := by
  intro V _ _ _ Q c hc hQ
  set B : V →L[ℝ] V →L[ℝ] ℂ := -Q with hBdef
  have hBapp : ∀ x y, B x y = -(Q x y) := fun x y => rfl
  have hB : ∀ x, (B x x).re ≤ -(c * ‖x‖ ^ 2) := by
    intro x; rw [hBapp, Complex.neg_re]; linarith [hQ x]
  have hq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : V => B y y) := B.contDiff.clm_apply contDiff_id
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : V => Complex.exp (B y y)) :=
    Complex.contDiff_exp.comp hq
  refine ⟨⟨fun y => Complex.exp (B y y), hg, ?_⟩, fun x => ?_, fun x p => ?_⟩
  · intro k n
    obtain ⟨C, hC⟩ := GlobalTheory.GaussExpSeries.exists_bound_poly_mul_exp c hc (k + 2 * n)
    refine ⟨n ! * (2 * (‖B‖ + 1)) ^ n * C, fun x => ?_⟩
    have hx0 := norm_nonneg x
    have hB0 := norm_nonneg B
    have hfb := GlobalTheory.GaussExpSeries.norm_iteratedFDeriv_gauss_le B c hB n x
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : V => Complex.exp (B y y)) x‖
        ≤ (1 + ‖x‖) ^ k * (n ! * Real.exp (-(c * ‖x‖ ^ 2)) * (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n) := by
          gcongr
          linarith
      _ = n ! * (2 * (‖B‖ + 1)) ^ n * ((1 + ‖x‖) ^ (k + 2 * n) * Real.exp (-(c * ‖x‖ ^ 2))) := by
          rw [show (2 * (‖B‖ + 1) * (1 + ‖x‖) ^ 2) ^ n = (2 * (‖B‖ + 1)) ^ n * (1 + ‖x‖) ^ (2 * n) by
            rw [mul_pow, pow_mul], pow_add]; ring
      _ ≤ n ! * (2 * (‖B‖ + 1)) ^ n * C := by gcongr; exact hC ‖x‖ hx0
  · show Complex.exp (B x x) = _
    rw [hBapp]
  · have h1 := (B.hasFDerivAt (x := x)).clm_apply (hasFDerivAt_id x)
    have h2 : HasFDerivAt (fun y : V => Complex.exp (B y y)) _ x := h1.cexp
    show fderiv ℝ (fun y : V => Complex.exp (B y y)) x p = -(Q x p + Q p x) * Complex.exp (B x x)
    rw [h2.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply, id, smul_eq_mul, hBapp]
    ring

end GlobalTheory.GaussComplexForm
end

section

namespace GlobalTheory.CharInvForm

theorem iteratedDeriv_exp_I (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (Complex.I * y)) =
      fun y : ℝ => Complex.I ^ n * Complex.exp (Complex.I * y) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h : HasDerivAt (fun y : ℝ => Complex.I ^ n * Complex.exp (Complex.I * y))
        (Complex.I ^ n * (Complex.exp (Complex.I * y) * (Complex.I * 1))) y :=
      ((h1.const_mul Complex.I).cexp).const_mul (Complex.I ^ n)
    rw [h.deriv]; ring

theorem temperate_exp_I : Function.HasTemperateGrowth (fun y : ℝ => Complex.exp (Complex.I * y)) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (Complex.I * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨hc, fun n => ⟨0, 1, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_I, pow_zero, mul_one, norm_mul, norm_pow,
    mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
  simp

theorem kills_linear_mul : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →ₗ[ℂ] ℂ),
    (∀ (L : V →L[ℝ] ℝ) (f f' : SchwartzMap V ℂ), (∀ x, f' x = Complex.exp (Complex.I * (L x : ℂ)) * f x) → T f' = T f) →
    ∀ (L : V →L[ℝ] ℝ) (h g : SchwartzMap V ℂ), (∀ x, g x = (L x : ℂ) * h x) → T g = 0 := by
  intro V _ _ _ T hT L h g hg
  obtain ⟨n, a, A, hA, hdiv⟩ := GlobalTheory.T.identity_as_sum_exp_minus_one
  have hAL : ∀ j, Function.HasTemperateGrowth (fun x : V => A j (L x)) := fun j =>
    (hA j).comp L.hasTemperateGrowth
  have hE : ∀ j, Function.HasTemperateGrowth
      (fun x : V => Complex.exp (Complex.I * (((a j • L) x : ℝ) : ℂ))) := fun j =>
    temperate_exp_I.comp (a j • L).hasTemperateGrowth
  let k : Fin n → SchwartzMap V ℂ := fun j => SchwartzMap.smulLeftCLM ℂ (fun x : V => A j (L x)) h
  let f' : Fin n → SchwartzMap V ℂ := fun j =>
    SchwartzMap.smulLeftCLM ℂ (fun x : V => Complex.exp (Complex.I * (((a j • L) x : ℝ) : ℂ))) (k j)
  have hk : ∀ j x, k j x = A j (L x) * h x := fun j x => by
    simp only [k]
    rw [SchwartzMap.smulLeftCLM_apply_apply (hAL j), smul_eq_mul]
  have hf : ∀ j x, f' j x = Complex.exp (Complex.I * (((a j • L) x : ℝ) : ℂ)) * k j x := fun j x => by
    simp only [f']
    rw [SchwartzMap.smulLeftCLM_apply_apply (hE j), smul_eq_mul]
  have hsum : g = ∑ j, (f' j - k j) := by
    ext x
    rw [SchwartzMap.sum_apply, hg x]
    conv_lhs => rw [hdiv (L x)]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [SchwartzMap.sub_apply, hf, hk, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_sub, hT (a j • L) (k j) (f' j) (hf j), sub_self]

end GlobalTheory.CharInvForm
end

section

open MeasureTheory
open scoped ContDiff

theorem _root_.GlobalTheory.T.exists_evaluation_extension_closure_representatives : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (ι : K → G → ℂ), (∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖) → (∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x) → ∀ (A : K →L[ℂ] K) (E : Submodule ℂ K), (∀ v ∈ E, ∃ φ : G → ℂ, Continuous φ ∧ ι (A v) =ᵐ[μ] φ) → (∀ B, IsCompact B → ∃ C : ℝ, ∀ v ∈ E, ∀ φ : G → ℂ, Continuous φ → ι (A v) =ᵐ[μ] φ → ∀ x ∈ B, ‖φ x‖ ≤ C * ‖v‖) → ∃ Λ : G → (K →L[ℂ] ℂ), ∀ v ∈ closure (E : Set K), (Continuous fun x => Λ x v) ∧ ι (A v) =ᵐ[μ] fun x => Λ x v := by
  first | exact @GlobalTheory.LocRep.exists_eval_closure | exact GlobalTheory.LocRep.exists_eval_closure | (intros; apply GlobalTheory.LocRep.exists_eval_closure <;> assumption)
end

section


theorem _root_.GlobalTheory.T.matrix_oneParameterGroup_eq_exp_of_continuous : ∀ {n : Type} [Fintype n] [DecidableEq n] (N : ℝ → Matrix n n ℂ), Continuous N → N 0 = 1 → (∀ s t, N (s + t) = N s * N t) → ∃ Y : Matrix n n ℂ, ∀ t : ℝ, N t = NormedSpace.exp (t • Y) := by
  first | exact @GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter | exact GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter | (intros; apply GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter <;> assumption)
end

section

open Filter PeriodPair Polynomial
open scoped Topology

namespace GlobalTheory

private lemma eq_zero_of_tendsto_eval_cobounded {B : ℂ[X]} {l : Filter ℂ} [l.NeBot] {u : ℂ → ℂ}
    (hu : Tendsto u l (Bornology.cobounded ℂ))
    (h : Tendsto (fun z ↦ B.eval (u z)) l (𝓝 0)) : B = 0 := by
  by_cases hd : 0 < B.degree
  · exfalso
    have h1 := B.tendsto_norm_atTop hd (tendsto_norm_atTop_iff_cobounded.mpr hu)
    have h2 := h.norm
    exact h1.not_tendsto (disjoint_nhds_atTop _).symm h2
  · rw [eq_C_of_degree_le_zero (not_lt.mp hd)] at h ⊢
    simp only [eval_C] at h
    rw [tendsto_nhds_unique tendsto_const_nhds h, C_0]

private lemma exists_eq_mul_of_three_roots {A : ℂ[X]} {a b c : ℂ} (hab : b ≠ a) (hac : c ≠ a)
    (hbc : c ≠ b) (ha : A.eval a = 0) (hb : A.eval b = 0) (hc : A.eval c = 0) :
    ∃ B : ℂ[X], A = (X - C a) * ((X - C b) * ((X - C c) * B)) := by
  obtain ⟨A₁, rfl⟩ := dvd_iff_isRoot.mpr ha
  have hb₁ : A₁.eval b = 0 := by simpa [sub_eq_zero, hab] using hb
  obtain ⟨A₂, rfl⟩ := dvd_iff_isRoot.mpr hb₁
  have hc₂ : A₂.eval c = 0 := by simpa [sub_eq_zero, hac, hbc] using hc
  obtain ⟨B, rfl⟩ := dvd_iff_isRoot.mpr hc₂
  exact ⟨B, rfl⟩

theorem eq_zero_of_odd_elliptic_of_tendsto : ∀ (L : PeriodPair) (f : ℂ → ℂ), (∀ z, z ∉ L.lattice → DifferentiableAt ℂ f z) → (∀ z l, z ∉ L.lattice → l ∈ L.lattice → f (z + l) = f z) → (∀ z, z ∉ L.lattice → f (-z) = -f z) → Filter.Tendsto (fun z : ℂ => z ^ 3 * f z) (𝓝[≠] 0) (𝓝 0) → ∀ z, z ∉ L.lattice → f z = 0 := by
  classical
  intro L f hd hp ho ht
  let g : ℂ → ℂ := fun z ↦ if z ∈ L.lattice then 0 else f z ^ 2
  have hgd : ∀ z ∉ L.lattice, DifferentiableAt ℂ g z := fun z hz ↦ by
    refine ((hd z hz).pow 2).congr_of_eventuallyEq ?_
    filter_upwards [eventually_notMem_periodLattice L hz] with w hw
    simp [g, hw]
  have hgp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z := fun z l hl ↦ by
    by_cases hz : z ∈ L.lattice
    · simp [g, hz, add_mem hz hl]
    · simp [g, hz, L.lattice.add_mem_iff_left hl, hp z l hz hl]
  have hge : ∀ z, g (-z) = g z := fun z ↦ by
    by_cases hz : z ∈ L.lattice
    · simp [g, hz]
    · simp [g, hz, ho z hz]
  have hgt : Tendsto (fun z : ℂ ↦ z ^ 6 * g z) (𝓝[≠] 0) (𝓝 0) := by
    have h1 := ht.pow 2
    rw [zero_pow two_ne_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ne_notMem_periodLattice L 0] with w hw
    simp only [g, hw, if_false]
    ring
  have hgm : MeromorphicAt g 0 := by
    refine ⟨6, Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_⟩
    · filter_upwards [eventually_ne_notMem_periodLattice L 0] with w hw
      have := hgd w hw
      fun_prop
    · rw [continuousAt_iff_punctured_nhds]
      simpa using hgt
  obtain ⟨A, hA⟩ := exists_eq_polynomial_weierstrassP L hgm hgd hgp hge
  have hhalf : ∀ z ∉ L.lattice, z + z ∈ L.lattice → A.eval (℘[L] z) = 0 := fun z hz h2 ↦ by
    have h1 := hp (-z) (z + z) (by simpa using hz) h2
    rw [ho z hz, show -z + (z + z) = z by ring, CharZero.eq_neg_self_iff] at h1
    rw [← hA z hz]
    simp [g, h1]
  have key : ∀ a b : ℚ, (a * L.ω₁ + b * L.ω₂ : ℂ) ∈ L.lattice ↔ a.den = 1 ∧ b.den = 1 :=
    fun a b ↦ L.mul_ω₁_add_mul_ω₂_mem_lattice
  let p : ℚ → ℚ → ℂ := fun a b ↦ a * L.ω₁ + b * L.ω₂
  have padd : ∀ a b c d, p a b + p c d = p (a + c) (b + d) := fun a b c d ↦ by
    simp only [p]; push_cast; ring
  have psub : ∀ a b c d, p a b - p c d = p (a - c) (b - d) := fun a b c d ↦ by
    simp only [p]; push_cast; ring
  have pm : ∀ a b, p a b ∈ L.lattice ↔ a.den = 1 ∧ b.den = 1 := key
  have n1 : p (1 / 2) 0 ∉ L.lattice := by rw [pm]; norm_num
  have n2 : p 0 (1 / 2) ∉ L.lattice := by rw [pm]; norm_num
  have n3 : p (1 / 2) (1 / 2) ∉ L.lattice := by rw [pm]; norm_num
  obtain ⟨B, hB⟩ := exists_eq_mul_of_three_roots (A := A) (a := ℘[L] (p (1 / 2) 0))
    (b := ℘[L] (p 0 (1 / 2))) (c := ℘[L] (p (1 / 2) (1 / 2)))
    (by rw [Ne, weierstrassP_eq_iff L n2 n1, padd, psub, pm, pm]; norm_num)
    (by rw [Ne, weierstrassP_eq_iff L n3 n1, padd, psub, pm, pm]; norm_num)
    (by rw [Ne, weierstrassP_eq_iff L n3 n2, padd, psub, pm, pm]; norm_num)
    (hhalf _ n1 (by rw [padd, pm]; norm_num))
    (hhalf _ n2 (by rw [padd, pm]; norm_num))
    (hhalf _ n3 (by rw [padd, pm]; norm_num))
  set a := ℘[L] (p (1 / 2) 0)
  set b := ℘[L] (p 0 (1 / 2))
  set c := ℘[L] (p (1 / 2) (1 / 2))
  let w : ℂ → ℂ := fun z ↦ z ^ 2 * L.weierstrassPExcept 0 z + 1
  have hw : AnalyticAt ℂ w 0 := by fun_prop
  have hw' : ∀ z ≠ 0, w z = z ^ 2 * ℘[L] z := fun z hz ↦ by
    simpa [hz, w] using (L.ite_eq_one_sub_sq_mul_weierstrassP 0 (zero_mem _) z).symm
  let q : ℂ → ℂ := fun z ↦ (w z - z ^ 2 * a) * ((w z - z ^ 2 * b) * (w z - z ^ 2 * c))
  have hq : ContinuousAt q 0 := by
    have := hw.continuousAt
    fun_prop
  have hq0 : q 0 = 1 := by simp [q, w]
  have hq1 : Tendsto q (𝓝[≠] 0) (𝓝 1) := hq0 ▸ hq.tendsto.mono_left nhdsWithin_le_nhds
  have hB0 : B = 0 := by
    refine eq_zero_of_tendsto_eval_cobounded (tendsto_weierstrassP_cobounded L (zero_mem _)) ?_
    have h1 := hgt.div hq1 one_ne_zero
    rw [zero_div] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ne_notMem_periodLattice L 0, self_mem_nhdsWithin,
      hq1.eventually_ne one_ne_zero] with z hz hz0 hqz
    rw [Pi.div_apply, div_eq_iff hqz, hA z hz, hB]
    simp only [q, hw' z hz0, eval_mul, eval_sub, eval_X, eval_C]
    ring
  intro z hz
  have h1 := hA z hz
  rw [hB, hB0] at h1
  simpa [g, hz] using h1

end GlobalTheory
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem tsum_residue_class_split : ∀ (N : ℕ) [NeZero N] (r : ZMod N) (R : ℤ → ℂ), Summable (fun n : ℤ => R ((r.val : ℤ) + n * N)) → ∑' n : ℤ, R ((r.val : ℤ) + n * N) = (if r = 0 then R 0 else 0) + ∑' d : ℕ+, (if ((d : ℕ) : ZMod N) = r then R ((d : ℕ) : ℤ) else 0) + ∑' d : ℕ+, (if ((d : ℕ) : ZMod N) = -r then R (-((d : ℕ) : ℤ)) else 0) := by
  intro N _ r R hs
  classical
  let F : ℤ → ℂ := fun t => if (t : ZMod N) = r then R t else 0
  let g : ℤ → ℤ := fun n => (r.val : ℤ) + n * N
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hg : Function.Injective g := by
    intro a b h
    simp only [g] at h
    exact mul_right_cancel₀ hN (add_left_cancel h)
  have hz : ∀ t ∉ Set.range g, F t = 0 := by
    intro t ht
    simp only [F]
    rw [if_neg]
    intro h
    apply ht
    have h2 : ((t - (r.val : ℤ) : ℤ) : ZMod N) = 0 := by
      push_cast
      rw [h, ZMod.natCast_zmod_val, sub_self]
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h2
    exact ⟨k, by simp only [g]; linear_combination -hk⟩
  have hFg : F ∘ g = fun n : ℤ => R ((r.val : ℤ) + n * N) := by
    funext n
    simp [F, g]
  have hH : HasSum F (∑' n : ℤ, R ((r.val : ℤ) + n * N)) := by
    rw [← hg.hasSum_iff hz, hFg]
    exact hs.hasSum
  rw [← hH.tsum_eq, tsum_int_eq_zero_add_tsum_pnat hH.summable]
  congr 1
  · congr 1
    · simp only [F, Int.cast_zero, eq_comm]
    · refine tsum_congr fun d => ?_
      simp only [F, Int.cast_natCast]
  · refine tsum_congr fun d => ?_
    simp only [F, Int.cast_neg, Int.cast_natCast, neg_eq_iff_eq_neg]

end GlobalTheory.WpFam
end

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

theorem _root_.GlobalTheory.T.integral_complexGaussian_posDef_hermitian_part : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ), (A + Aᴴ).PosDef → A.det ≠ 0 ∧ Integrable (fun z : ι → ℂ => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z))) ∧ ∫ z : ι → ℂ, cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) = A.det⁻¹ := by
  first | exact @GlobalTheory.MatrixGaussian.integral_gaussian | exact GlobalTheory.MatrixGaussian.integral_gaussian | (intros; apply GlobalTheory.MatrixGaussian.integral_gaussian <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.mean_zero_comp_smul_periodic_fundamentalDomain : ∀ (n : Type) [Fintype n] (L : AddSubgroup (n → ℝ)) [Countable L] (D : Set (n → ℝ)) (k : (n → ℝ) → ℂ) (q : ℝ), 0 < q → MeasureTheory.IsAddFundamentalDomain L D MeasureTheory.volume → 0 < MeasureTheory.volume D → MeasureTheory.volume D < ⊤ → Continuous k → (∃ C : ℝ, ∀ s, ‖k s‖ ≤ C) → (∀ p ∈ L, ∀ s, k (s + p) = k s) → ∫ s in D, k s = 0 → ∀ (L₁ : AddSubgroup (n → ℝ)) [Countable L₁] (D₁ : Set (n → ℝ)), MeasureTheory.IsAddFundamentalDomain L₁ D₁ MeasureTheory.volume → MeasureTheory.volume D₁ < ⊤ → (∀ p ∈ L₁, ∀ s, k (q • (s + p)) = k (q • s)) → ∫ s in D₁, k (q • s) = 0 := by
  first | exact @GlobalTheory.mean_zero_comp_smul_of_periodic | exact GlobalTheory.mean_zero_comp_smul_of_periodic | (intros; apply GlobalTheory.mean_zero_comp_smul_of_periodic <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CocycleChar

theorem pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.InductiveNormBound.main
  | exact _root_.GlobalTheory.InductiveNormBound.main
  | (apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.InductiveNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InductiveNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InductiveNormBound.main ..)

theorem cocycle_char_trivial_near_zero :
    ∀ {A V : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A]
    [NonarchimedeanAddGroup A] [AddCommGroup V] [TopologicalSpace V] [T2Space V] (lam : A →+ V), Continuous lam →
    ∀ (ε : V → V → ℂ), (∃ N ∈ nhds (0 : V), ∀ x ∈ N, ∀ y ∈ N, ε x y = 1) → (∀ x, ε x 0 = 1) →
    ∀ (χ : A → ℂ), Continuous χ → (∀ a, lam a = 0 → χ a = 1) →
    (∀ a b, χ (a + b) = χ a * χ b * ε (lam a) (lam b)) → ∃ U ∈ nhds (0 : V), ∀ a, lam a ∈ U → χ a = 1 := by
  intro A V _ _ _ _ _ _ _ _ lam hlam ε ⟨N, hN, hεN⟩ hε0 χ hχ hker hmul
  have hχ0 : χ 0 = 1 := hker 0 (map_zero lam)

  have hW : lam ⁻¹' N ∩ {a : A | ‖χ a - 1‖ < 1 / 2} ∈ nhds (0 : A) := by
    refine Filter.inter_mem ?_ ?_
    · exact hlam.continuousAt.preimage_mem_nhds (by simpa using hN)
    · exact (isOpen_lt (hχ.sub continuous_const).norm continuous_const).mem_nhds (by simp [hχ0])
  obtain ⟨K₀, hK₀⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hW
  have hpow : ∀ a ∈ K₀, ∀ n : ℕ, χ (n • a) = χ a ^ n := by
    intro a ha n
    induction n with
    | zero => simp [hχ0]
    | succ n ih =>
      have h1 : n • a ∈ K₀ := K₀.toAddSubgroup.nsmul_mem ha n
      rw [succ_nsmul, hmul, ih, hεN _ (hK₀ h1).1 _ (hK₀ ha).1, pow_succ, mul_one]
  have hK₀one : ∀ a ∈ K₀, χ a = 1 := by
    intro a ha
    refine pow_near_one fun n => ?_
    rw [← hpow a ha n]
    exact (hK₀ (K₀.toAddSubgroup.nsmul_mem ha n)).2

  set S : AddSubgroup A := K₀.toAddSubgroup ⊔ lam.ker with hSdef
  have hSopen : IsOpen (S : Set A) :=
    AddSubgroup.isOpen_mono (le_sup_left : K₀.toAddSubgroup ≤ S) K₀.isOpen
  set C : Set A := (S : Set A)ᶜ
  have hCc : IsCompact C := hSopen.isClosed_compl.isCompact
  have hLc : IsClosed (lam '' C) := (hCc.image hlam).isClosed
  have h0 : (0 : V) ∉ lam '' C := by
    rintro ⟨c, hc, hc0⟩
    exact hc (le_sup_right (a := K₀.toAddSubgroup) (AddMonoidHom.mem_ker.2 hc0))
  refine ⟨(lam '' C)ᶜ, hLc.isOpen_compl.mem_nhds h0, fun a ha => ?_⟩
  have haS : a ∈ S := by
    by_contra h
    exact ha ⟨a, h, rfl⟩
  obtain ⟨k, hk, n, hn, rfl⟩ := AddSubgroup.mem_sup.1 haS
  rw [AddMonoidHom.mem_ker] at hn
  rw [hmul, hK₀one k hk, hker n hn, hn, hε0, mul_one, mul_one]

end GlobalTheory.CocycleChar
end
end

section


theorem _root_.GlobalTheory.T.exists_complex_point_norm_lt_of_not_isUnit' : ∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] [Algebra.FiniteType K B] (σ : K →+* ℂ) (n : ℕ) (w : Fin n → B) (u q : B), ¬ IsUnit u → q ≠ 0 → ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ∃ φ : B →+* ℂ, φ.comp (algebraMap K B) = σ ∧ φ q ≠ 0 ∧ ‖φ u‖ < ε ∧ ∀ i, ‖φ (w i)‖ ≤ M := by
  first | exact @GlobalTheory.exists_complex_point_norm_lt_of_not_isUnit | exact GlobalTheory.exists_complex_point_norm_lt_of_not_isUnit | (intros; apply GlobalTheory.exists_complex_point_norm_lt_of_not_isUnit <;> assumption)
end

section


theorem _root_.GlobalTheory.T.norm_root_le_card_mul_bound_of_esymm_norm_le : ∀ (n : ℕ) (B : Multiset ℂˣ) (M : ℝ), B.card = n → 1 ≤ M → (∀ j, 1 ≤ j → j ≤ n → ‖(B.map fun b : ℂˣ => (b : ℂ)).esymm j‖ ≤ M) → ∀ b ∈ B, ‖(b : ℂ)‖ ≤ n * M := by
  first | exact @GlobalTheory.cauchy_roots_bound | exact GlobalTheory.cauchy_roots_bound | (intros; apply GlobalTheory.cauchy_roots_bound <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace GlobalTheory

theorem schwartz_mem_closure_hasCompactSupport :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ),
    f ∈ closure {g : SchwartzMap V ℂ | HasCompactSupport (g : V → ℂ)} := by
  intro V _ _ _ f
  exact schwartz_dense_hasCompactSupport f

end GlobalTheory
end
