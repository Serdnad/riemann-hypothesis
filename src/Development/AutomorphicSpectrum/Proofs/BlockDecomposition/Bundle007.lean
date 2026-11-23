module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
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
public import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Linear
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

section

open MeasureTheory

namespace GlobalTheory.CompanionTheory.OneParamFourier

variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [MeasurableSpace A] [BorelSpace A]

theorem integral_translate_mul_char (lam : Measure A) [lam.IsAddHaarMeasure] (H : A → ℂ)
    (χ : AddChar A ℂ) (a : A) :
    ∫ b, H (b + a) * χ b ∂lam = χ (-a) * ∫ b, H b * χ b ∂lam := by
  have h := integral_add_right_eq_self (μ := lam) (fun b => H b * χ (b + -a)) a
  simp only [add_neg_cancel_right] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only [AddChar.map_add_eq_mul]
  ring

theorem integrable_mul_char {lam : Measure A} {H : A → ℂ} (hH : Integrable H lam)
    {χ : AddChar A ℂ} (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) :
    Integrable (fun b => H b * χ b) lam := by
  refine hH.mono (hH.aestronglyMeasurable.mul hχ.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun b => ?_)
  simp [hn]

theorem integrable_uncurry_translate (lam : Measure A) [lam.IsAddHaarMeasure] [SFinite lam]
    (c : ℝ →+ A) (hc : Continuous c) {G : A → ℂ} (hG : Continuous G) (hGi : Integrable G lam)
    {χ : AddChar A ℂ} (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) (K : ℂ) (s : ℝ) :
    Integrable (Function.uncurry fun (u : ℝ) (b : A) => K * G (b + c u) * χ b)
      ((volume.restrict (Set.uIoc 0 s)).prod lam) := by
  have hcont : Continuous (Function.uncurry fun (u : ℝ) (b : A) => K * G (b + c u) * χ b) := by
    unfold Function.uncurry
    fun_prop
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) s)) := by
    unfold Set.uIoc
    infer_instance
  refine (integrable_prod_iff hcont.aestronglyMeasurable).2 ⟨ae_of_all _ fun u => ?_, ?_⟩
  · have h1 : Integrable (fun b => G (b + c u)) lam := hGi.comp_add_right (c u)
    have h2 := integrable_mul_char (h1.const_mul K) hχ hn
    simpa [Function.uncurry, mul_assoc] using h2
  · have hconst : ∀ u : ℝ, ∫ b, ‖Function.uncurry (fun (u : ℝ) (b : A) => K * G (b + c u) * χ b) (u, b)‖ ∂lam
        = ‖K‖ * ∫ b, ‖G b‖ ∂lam := by
      intro u
      have h := integral_add_right_eq_self (μ := lam) (fun b => ‖G b‖) (c u)
      rw [← h, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp [Function.uncurry, hn]
    simp_rw [hconst]
    exact integrable_const _

theorem integral_mul_char_eq_of_hasDerivAt (A : Type) [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A] (lam : Measure A)
    [lam.IsAddHaarMeasure] [SFinite lam] (c : ℝ →+ A) (hc : Continuous c) (F G : A → ℂ)
    (hF : Continuous F) (hG : Continuous G) (hFi : Integrable F lam) (hGi : Integrable G lam)
    (χ : AddChar A ℂ) (hχ : Continuous χ) (hn : ∀ x, ‖χ x‖ = 1) (f : ℝ)
    (hf : ∀ s : ℝ, χ (c s) = Complex.exp (-(2 * Real.pi * Complex.I * ((s * f : ℝ) : ℂ))))
    (hd : ∀ (b : A) (s : ℝ),
      HasDerivAt (fun t : ℝ => F (b + c t)) (2 * Real.pi * Complex.I * G (b + c s)) s) :
    ∫ b, G b * χ b ∂lam = (f : ℂ) * ∫ b, F b * χ b ∂lam := by
  set K : ℂ := 2 * Real.pi * Complex.I with hK
  have hK0 : K ≠ 0 := by
    simp [hK, Real.pi_ne_zero, Complex.I_ne_zero]
  set e : ℝ → ℂ := fun u => Complex.exp (K * ((u * f : ℝ) : ℂ)) with he
  have hχe : ∀ s : ℝ, χ (-(c s)) = e s := by
    intro s
    rw [← map_neg, hf, he]
    simp only
    congr 1
    push_cast
    ring
  set Fh : ℂ := ∫ b, F b * χ b ∂lam with hFh
  set Gh : ℂ := ∫ b, G b * χ b ∂lam with hGh
  have hec : Continuous e := by
    rw [he]
    fun_prop
  have key : ∀ s : ℝ, (e s - 1) * Fh = K * Gh * ∫ u in (0 : ℝ)..s, e u := by
    intro s
    have hftc : ∀ b : A, F (b + c s) - F b = ∫ u in (0 : ℝ)..s, K * G (b + c u) := by
      intro b
      have hcu : Continuous fun u : ℝ => K * G (b + c u) := by fun_prop
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := s)
        (f := fun t : ℝ => F (b + c t)) (f' := fun u => K * G (b + c u))
        (fun x _ => hd b x) (hcu.intervalIntegrable _ _)
      simpa using this.symm
    have hswap := intervalIntegral_integral_swap
      (integrable_uncurry_translate lam c hc hG hGi hχ hn K s)
    have h1 : ∫ b, F (b + c s) * χ b ∂lam = e s * Fh := by
      rw [integral_translate_mul_char, hχe]
    have hi1 : Integrable (fun b => F (b + c s) * χ b) lam :=
      integrable_mul_char (hFi.comp_add_right (c s)) hχ hn
    have hi2 : Integrable (fun b => F b * χ b) lam := integrable_mul_char hFi hχ hn
    have h2 : (e s - 1) * Fh = ∫ b, (∫ u in (0 : ℝ)..s, K * G (b + c u) * χ b) ∂lam := by
      have : (e s - 1) * Fh = ∫ b, (F (b + c s) * χ b - F b * χ b) ∂lam := by
        rw [integral_sub hi1 hi2, h1]
        ring
      rw [this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      rw [intervalIntegral.integral_mul_const, ← hftc b]
      ring
    rw [h2, ← hswap, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    beta_reduce
    have h3 : ∫ b, K * G (b + c u) * χ b ∂lam = K * ∫ b, G (b + c u) * χ b ∂lam := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      ring
    rw [h3, integral_translate_mul_char, hχe]
    ring
  have hL : HasDerivAt (fun s : ℝ => (e s - 1) * Fh) (K * f * Fh) 0 := by
    have h0 : HasDerivAt (fun u : ℝ => K * ((u * f : ℝ) : ℂ)) (K * f) 0 := by
      have : HasDerivAt (fun u : ℝ => ((u : ℂ))) 1 0 := Complex.ofRealCLM.hasDerivAt
      simpa [mul_assoc] using (this.mul_const (f : ℂ)).const_mul K
    have := ((h0.cexp).sub_const 1).mul_const Fh
    simpa [he] using this
  have hR : HasDerivAt (fun s : ℝ => K * Gh * ∫ u in (0 : ℝ)..s, e u) (K * Gh) 0 := by
    have := (hec.integral_hasStrictDerivAt 0 0).hasDerivAt.const_mul (K * Gh)
    simpa [he] using this
  have hEq : (fun s : ℝ => (e s - 1) * Fh) = fun s : ℝ => K * Gh * ∫ u in (0 : ℝ)..s, e u :=
    funext key
  rw [hEq] at hL
  have := hL.unique hR
  have h4 : K * (f * Fh) = K * Gh := by
    rw [← mul_assoc]
    exact this
  exact (mul_left_cancel₀ hK0 h4).symm

end GlobalTheory.CompanionTheory.OneParamFourier
end

section

open Filter Topology

namespace GlobalTheory.CompanionTheory.ComplexAnalysis

theorem iteratedDeriv_zero_eq_of_eq_on_real_points (f g : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 ρ)) (hg : DifferentiableOn ℂ g (Metric.ball 0 ρ))
    (h : ∀ s : ℝ, |s| < ρ → f s = g s) (r : ℕ) :
    iteratedDeriv r f 0 = iteratedDeriv r g 0 := by

  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  have hreal : ∀ᶠ s : ℝ in 𝓝[≠] 0, f s = g s := by
    have hs : {s : ℝ | |s| < ρ} ∈ 𝓝 (0 : ℝ) :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hρ)
    exact Filter.mem_of_superset (nhdsWithin_le_nhds hs) fun s hs' => h s hs'
  have htend : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc := Complex.continuous_ofReal.tendsto (0 : ℝ)
      simpa using hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z := htend.frequently hreal.frequently
  have heq : Set.EqOn f g (Metric.ball 0 ρ) :=
    (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU)
      (convex_ball (0 : ℂ) ρ).isPreconnected h0 hfreq
  have hev : f =ᶠ[𝓝 0] g := Filter.mem_of_superset (hU.mem_nhds h0) heq
  exact hev.iteratedDeriv_eq r

end GlobalTheory.CompanionTheory.ComplexAnalysis
end

section

open scoped Matrix SchwartzMap

namespace GlobalTheory.CompanionTheory.KlocopSw

noncomputable def rightMulEquiv (m n : ℕ) (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) :
    (Fin m → Fin n → ℂ) ≃L[ℂ] (Fin m → Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => (Matrix.of u * a : Matrix (Fin m) (Fin n) ℂ)
      map_add' := fun u v => by
        show ((Matrix.of u + Matrix.of v) * a : Matrix (Fin m) (Fin n) ℂ) =
          Matrix.of u * a + Matrix.of v * a
        rw [Matrix.add_mul]
      map_smul' := fun r u => by
        show ((r • Matrix.of u) * a : Matrix (Fin m) (Fin n) ℂ) = r • (Matrix.of u * a)
        rw [Matrix.smul_mul]
      invFun := fun u => (Matrix.of u * a⁻¹ : Matrix (Fin m) (Fin n) ℂ)
      left_inv := fun u => by
        show (Matrix.of u * a * a⁻¹ : Matrix (Fin m) (Fin n) ℂ) = u
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv a ha, Matrix.mul_one]
        rfl
      right_inv := fun u => by
        show (Matrix.of u * a⁻¹ * a : Matrix (Fin m) (Fin n) ℂ) = u
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul a ha, Matrix.mul_one]
        rfl }

theorem exists_schwartz_rightMul : ∀ (m n : ℕ) (c : ℂ) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det →
    ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
      ⇑ψ = fun u => c * φ (Matrix.of u * a) := by
  intro m n c a ha φ
  refine ⟨c • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((rightMulEquiv m n a ha).restrictScalars ℝ) φ, ?_⟩
  funext u
  rfl

end GlobalTheory.CompanionTheory.KlocopSw
end

section

open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.HermitianCommuting

theorem exists_maximal_commuting_hermitian_subspace {n : ℕ}
    (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ 𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), 𝔞 ≤ 𝔤 ∧ (∀ A ∈ 𝔞, Aᴴ = A) ∧
      (∀ A ∈ 𝔞, ∀ B ∈ 𝔞, A * B = B * A) ∧
      ∀ Y ∈ 𝔤, Yᴴ = Y → (∀ A ∈ 𝔞, Y * A = A * Y) → Y ∈ 𝔞 := by
  let S : Set (Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :=
    {a | a ≤ 𝔤 ∧ (∀ A ∈ a, Aᴴ = A) ∧ ∀ A ∈ a, ∀ B ∈ a, A * B = B * A}
  have hS : S.Nonempty := by
    refine ⟨⊥, bot_le, ?_, ?_⟩
    · intro A hA
      rw [Submodule.mem_bot] at hA
      simp [hA]
    · intro A hA B hB
      rw [Submodule.mem_bot] at hA hB
      simp [hA, hB]
  obtain ⟨a, ha, hmax⟩ :=
    (wellFounded_gt (α := Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))).has_min S hS
  refine ⟨a, ha.1, ha.2.1, ha.2.2, ?_⟩
  intro Y hY hYh hYc
  have hmem : a ⊔ Submodule.span ℝ {Y} ∈ S := by
    refine ⟨sup_le ha.1 ((Submodule.span_singleton_le_iff_mem _ _).2 hY), ?_, ?_⟩
    · intro A hA
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hA
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [conjTranspose_add, ha.2.1 x hx, conjTranspose_smul, hYh]
      simp
    · intro A hA B hB
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hA
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      obtain ⟨x', hx', y', hy', rfl⟩ := Submodule.mem_sup.1 hB
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.1 hy'
      have h1 := ha.2.2 x hx x' hx'
      have h2 := hYc x hx
      have h3 := hYc x' hx'
      simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul, h1, h2, h3]
      rw [mul_comm d c]
      abel
  have hne : a ⊔ Submodule.span ℝ {Y} = a := by
    by_contra h
    exact hmax _ hmem (lt_of_le_of_ne le_sup_left (Ne.symm h))
  have hYmem : Y ∈ a ⊔ Submodule.span ℝ {Y} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self Y)
  rwa [hne] at hYmem

end GlobalTheory.CompanionTheory.HermitianCommuting
end

section

open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.IwaGen

theorem exists_regular_point : ∀ {n : ℕ} (𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ))
    (U : Matrix (Fin n) (Fin n) ℂ), ∃ H ∈ 𝔞, ∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j →
      ∀ A ∈ 𝔞, (Uᴴ * A * U) i i = (Uᴴ * A * U) j j := by
  classical
  intro n 𝔞 U
  let L : Fin n × Fin n → (↥𝔞 →ₗ[ℝ] ℂ) := fun p =>
    { toFun := fun A => (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.1 p.1
        - (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.2 p.2
      map_add' := by
        intro A B
        simp only [Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
        ring
      map_smul' := by
        intro c A
        simp only [Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
          RingHom.id_apply, smul_sub] }
  have hL : ∀ (p : Fin n × Fin n) (A : ↥𝔞), L p A =
      (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.1 p.1
        - (Uᴴ * (A : Matrix (Fin n) (Fin n) ℂ) * U) p.2 p.2 := fun _ _ => rfl
  let s : Finset (Submodule ℝ ↥𝔞) :=
    (Finset.univ.image fun p => LinearMap.ker (L p)).erase ⊤
  have hs : (⊤ : Submodule ℝ ↥𝔞) ∉ s := Finset.notMem_erase _ _
  obtain ⟨H, hH⟩ := (Set.ne_univ_iff_exists_notMem _).1
    (Subspace.biUnion_ne_univ_of_top_notMem hs)
  refine ⟨H, H.2, fun i j hij A hA => ?_⟩
  have hker : H ∈ LinearMap.ker (L (i, j)) := by
    rw [LinearMap.mem_ker, hL]
    exact sub_eq_zero.2 hij
  have htop : LinearMap.ker (L (i, j)) = ⊤ := by
    by_contra hne
    apply hH
    refine Set.mem_biUnion (x := LinearMap.ker (L (i, j))) ?_ hker
    exact Finset.mem_coe.2 (Finset.mem_erase.2
      ⟨hne, Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩⟩)
  have hA' : (⟨A, hA⟩ : ↥𝔞) ∈ LinearMap.ker (L (i, j)) := by
    rw [htop]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker, hL] at hA'
  exact sub_eq_zero.1 hA'

end GlobalTheory.CompanionTheory.IwaGen
end

section

open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.IwasawaGen

theorem skew_add_upper {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ)
    (hanti : Antitone h)
    (hf : ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤)
    (hstar : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤)
    (hreg : ∀ Y ∈ 𝔤, Yᴴ = Y → Matrix.diagonal (fun i => (h i : ℂ)) * Y =
      Y * Matrix.diagonal (fun i => (h i : ℂ)) → Y.IsDiag) :
    ∀ X ∈ 𝔤, ∃ A ∈ 𝔤, ∃ B ∈ 𝔤, X = A + B ∧ Aᴴ = -A ∧ B.BlockTriangular id := by
  intro X hX
  obtain ⟨P, hP, P_ent⟩ : ∃ P ∈ 𝔤, ∀ i j, P i j = if h j < h i then X i j else 0 := by
    refine ⟨_, hf (fun t => if 0 < t then 1 else 0) X hX, fun i j => ?_⟩
    by_cases hij : h j < h i
    · simp [hij]
    · simp [hij]
  obtain ⟨Z, hZ, Z_ent⟩ : ∃ Z ∈ 𝔤, ∀ i j, Z i j = if h i = h j then X i j else 0 := by
    refine ⟨_, hf (fun t => if t = 0 then 1 else 0) X hX, fun i j => ?_⟩
    by_cases hij : h i = h j
    · simp [hij]
    · simp [hij, sub_eq_zero]
  obtain ⟨M, hM, M_ent⟩ : ∃ M ∈ 𝔤, ∀ i j, M i j = if h i < h j then X i j else 0 := by
    refine ⟨_, hf (fun t => if t < 0 then 1 else 0) X hX, fun i j => ?_⟩
    by_cases hij : h i < h j
    · simp [hij]
    · simp [hij]
  have hsum : X = P + Z + M := by
    ext i j
    simp only [Matrix.add_apply, P_ent, Z_ent, M_ent]
    rcases lt_trichotomy (h i) (h j) with hij | hij | hij
    · simp [hij, hij.ne, not_lt.2 hij.le]
    · simp [hij]
    · simp [hij, hij.ne', not_lt.2 hij.le]
  set Y : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℝ) • (Z + Zᴴ) with hYdef
  have hY : Y ∈ 𝔤 := 𝔤.smul_mem _ (𝔤.add_mem hZ (hstar Z hZ))
  have Y_herm : Yᴴ = Y := by
    ext i j
    simp [hYdef, Matrix.conjTranspose_apply, add_comm]
  have Y_ent : ∀ i j, h i ≠ h j → Y i j = 0 := by
    intro i j hij
    simp [hYdef, Matrix.conjTranspose_apply, Z_ent, hij, hij.symm]
  have Y_comm : Matrix.diagonal (fun i => (h i : ℂ)) * Y =
      Y * Matrix.diagonal (fun i => (h i : ℂ)) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : h i = h j
    · rw [hij, mul_comm]
    · rw [Y_ent i j hij]; simp
  have Y_diag : Y.IsDiag := hreg Y hY Y_herm Y_comm
  refine ⟨(1 / 2 : ℝ) • (Z - Zᴴ) + M - Mᴴ, ?_, P + Y + Mᴴ, ?_, ?_, ?_, ?_⟩
  · exact 𝔤.sub_mem (𝔤.add_mem (𝔤.smul_mem _ (𝔤.sub_mem hZ (hstar Z hZ))) hM) (hstar M hM)
  · exact 𝔤.add_mem (𝔤.add_mem hP hY) (hstar M hM)
  · have hZsplit : Z = (1 / 2 : ℝ) • (Z - Zᴴ) + Y := by
      rw [hYdef, ← smul_add]
      have : Z - Zᴴ + (Z + Zᴴ) = (2 : ℝ) • Z := by
        rw [two_smul]; abel
      rw [this, smul_smul]; norm_num
    calc X = P + Z + M := hsum
      _ = P + ((1 / 2 : ℝ) • (Z - Zᴴ) + Y) + M := by rw [← hZsplit]
      _ = (1 / 2 : ℝ) • (Z - Zᴴ) + M - Mᴴ + (P + Y + Mᴴ) := by abel
  · simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_conjTranspose, star_trivial]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply]
    simp only [smul_eq_mul, Complex.real_smul, smul_sub]
    ring
  · intro i j hji
    have hji' : j < i := hji
    have hle : h i ≤ h j := hanti hji'.le
    have h1 : P i j = 0 := by
      rw [P_ent, if_neg (not_lt.2 hle)]
    have h2 : Y i j = 0 := Y_diag hji'.ne'
    have h3 : Mᴴ i j = 0 := by
      rw [Matrix.conjTranspose_apply, M_ent, if_neg (not_lt.2 hle)]; simp
    simp only [Matrix.add_apply, h1, h2, h3, add_zero]

end GlobalTheory.CompanionTheory.IwasawaGen
end

section

open Topology

namespace GlobalTheory.CompanionTheory.CompactOperators

theorem isCompactOperator_of_scaled_isometric_intertwiner
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (B : K →L[ℂ] K) (Φ : H →L[ℂ] K) (c : ℝ) (hc : 0 < c)
    (hΦ : ∀ x, ‖Φ x‖ = c * ‖x‖) (hAB : Φ ∘L A = B ∘L Φ) (hB : IsCompactOperator B) :
    IsCompactOperator A := by
  have hcn : (0 : ℝ) ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) Φ := by
    refine Φ.antilipschitz_of_bound fun x => ?_
    rw [Real.coe_toNNReal _ hcn, hΦ, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  have hemb : IsClosedEmbedding Φ := hanti.isClosedEmbedding Φ.uniformContinuous
  obtain ⟨S, hS, hSn⟩ := hB
  refine ⟨Φ ⁻¹' S, hemb.isCompact_preimage hS, ?_⟩
  have hpre : A ⁻¹' (Φ ⁻¹' S) = Φ ⁻¹' (B ⁻¹' S) := by
    ext x
    show Φ (A x) ∈ S ↔ B (Φ x) ∈ S
    rw [show Φ (A x) = B (Φ x) from ContinuousLinearMap.ext_iff.mp hAB x]
  rw [hpre]
  exact Φ.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hSn)

end GlobalTheory.CompanionTheory.CompactOperators
end
