module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormSqEqAdaptedFrameSum
public import GroundTheory.AutomorphicForms.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle004
public import GroundTheory.AutomorphicForms.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle002
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle003
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XSqDens
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XThmaAlg
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle049
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.HermTrace

section Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem quadConj_eq_complexConj (x : E) :
    conj (maximalRealSubfield E) E x = IsCMField.complexConj E x := by
  apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.AdaptedLen.conj_eq_complexConj <;> assumption

theorem complexConj_rt (H : Host E) : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h2 : (IsCMField.complexConj E (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
    rw [← map_pow, hsq, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
  · exfalso
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hc : starRingEnd ℂ (φ (H.rt : E)) = φ (H.rt : E) := by
      rw [← IsCMField.complexEmbedding_complexConj E φ, h]
    obtain ⟨s, hs⟩ := Complex.conj_eq_iff_real.1 hc
    have h3 := congrArg φ hsq
    rw [map_pow, map_neg, map_natCast, hs] at h3
    have h4 : (s ^ 2 : ℝ) = -(H.d : ℝ) := by exact_mod_cast h3
    nlinarith [sq_nonneg s]
  · exact h

theorem sesq_skew {V : Type} [AddCommGroup V] [Module E V] [Module ℚ V]
    (B : LinearMap.BilinForm ℚ V)
    (hadj : ∀ (a : E) x y, B (a • x) y = B x (IsCMField.complexConj E a • y))
    (hskew : ∀ u v, B u v = - B v u) (h₁ : V → V → E)
    (htr : ∀ x y (a : E), Algebra.trace ℚ E (a * h₁ x y) = B (a • x) y) (u v : V) :
    h₁ v u = - IsCMField.complexConj E (h₁ u v) := by
  have nd := traceForm_nondegenerate ℚ E
  have htc : ∀ z : E, Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z := fun z =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z
  have : h₁ v u - (- IsCMField.complexConj E (h₁ u v)) = 0 := by
    apply nd.1
    intro a
    have e1 : Algebra.trace ℚ E (a * IsCMField.complexConj E (h₁ u v)) =
        Algebra.trace ℚ E (IsCMField.complexConj E a * h₁ u v) := by
      rw [← htc, map_mul, IsCMField.complexConj_apply_apply]
    have e2 : B u (a • v) = B (IsCMField.complexConj E a • u) v := by
      rw [hadj, IsCMField.complexConj_apply_apply]
    rw [Algebra.traceForm_apply, mul_comm, mul_sub, map_sub, mul_neg, map_neg, e1, htr, htr,
      hskew (a • v) u, e2]
    ring
  linear_combination this


omit [IsCMField E] in
theorem exists_nat_integral {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ] (F : Λ → Λ → E)
    (h1 : ∀ x x' y, F (x + x') y = F x y + F x' y) (h2 : ∀ x y y', F x (y + y') = F x y + F x y') :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ x y, (m : E) * F x y ∈ integralClosure ℤ E := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Λ)
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (Finset.univ.image fun p : Fin n × Fin n => F (s p.1) (s p.2))
  have step : ∀ g : Λ →+ E, (∀ i, g (s i) ∈ integralClosure ℤ E) →
      ∀ x, g x ∈ integralClosure ℤ E := by
    intro g hg x
    have hx : x ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨i, rfl⟩ := h
      exact hg i
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | smul a x _ hx =>
      rw [map_zsmul]
      exact zsmul_mem hx a
  have core : ∀ m : ℕ, (∀ i k, (m : E) * F (s i) (s k) ∈ integralClosure ℤ E) →
      ∀ x y, (m : E) * F x y ∈ integralClosure ℤ E := by
    intro m hm x y
    let gy : Λ → Λ →+ E := fun x => AddMonoidHom.mk' (fun y => (m : E) * F x y)
      (fun a b => by rw [h2, mul_add])
    let gx : Λ → Λ →+ E := fun y => AddMonoidHom.mk' (fun x => (m : E) * F x y)
      (fun a b => by rw [h1, mul_add])
    exact step (gy x) (fun k => step (gx (s k)) (fun i => hm i k) x) y
  have hint : ∀ i k, IsIntegral ℤ (y • F (s i) (s k)) := fun i k =>
    hy _ (Finset.mem_image_of_mem _ (Finset.mem_univ (i, k)))
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨m, by simpa using hy0, core m fun i k => ?_⟩
    have := hint i k
    rwa [zsmul_eq_mul, Int.cast_natCast] at this
  · refine ⟨m, by simpa using hy0, core m fun i k => ?_⟩
    have := (hint i k).neg
    rwa [zsmul_eq_mul, Int.cast_neg, Int.cast_natCast, neg_mul, neg_neg] at this

end Field

theorem exists_hermitian_of_trace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)) (B : LinearMap.BilinForm ℚ (Fin N → E)), (∀ (a : E) u v, B (a • u) v = B u (IsCMField.complexConj E a • v)) → (∀ u v, B u v = - B v u) → (∀ u, (∀ v, B v u = 0) → u = 0) → ∃ (h : HermitianForm (maximalRealSubfield E) E (Fin N → E)) (m : ℕ), m ≠ 0 ∧ (∀ (a : E) u v, Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * h.toSesq v u)) = B (a • u) v) ∧ ∀ x y, h.toSesq (e x) (e y) ∈ integralClosure ℤ E := by
  intro E _ _ _ H Λ _ _ N e B hadj hskew hnd
  obtain ⟨h₁, ⟨htr, hadd1, hadd2, hsm1, hsm2⟩, -⟩ :=
    GlobalTheory.CompanionTheory.Ar.Flat.existsUnique_sesq_of_trace E (Fin N → E) B hadj
  have hsk := sesq_skew B hadj hskew h₁ htr
  obtain ⟨m, hm0, hint⟩ := exists_nat_integral (fun x y : Λ => h₁ (e y) (e x))
    (fun x x' y => by rw [map_add (f := _), hadd2]) (fun x y y' => by rw [map_add (f := _), hadd1])
  have hrt0 : (H.rt : E) ≠ 0 := by
    intro h0
    have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [h0] at hsq
    have hd : (H.d : E) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
    apply hd
    linear_combination hsq
  set c : E := (m : E) * (H.rt : E) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 hm0) hrt0
  have htc : IsCMField.complexConj E c = -c := by
    rw [hc, map_mul, map_natCast, complexConj_rt]
    ring
  let S : (Fin N → E) →ₛₗ[conjHom (maximalRealSubfield E) E] (Fin N → E) →ₗ[E] E :=
    LinearMap.mk₂'ₛₗ (conjHom (maximalRealSubfield E) E) (RingHom.id E) (fun v u => c * h₁ u v)
      (fun v v' u => by rw [hadd2, mul_add])
      (fun a v u => by
        rw [hsm2, smul_eq_mul]
        have : conjHom (maximalRealSubfield E) E a = IsCMField.complexConj E a :=
          quadConj_eq_complexConj a
        rw [this]
        ring)
      (fun v u u' => by rw [hadd1, mul_add])
      (fun a v u => by
        rw [hsm1, RingHom.id_apply, smul_eq_mul]
        ring)
  have Sapp : ∀ v u, S v u = c * h₁ u v := fun _ _ => rfl
  have hinj : Function.Injective S := by
    intro v v' hvv
    have hz : ∀ w, h₁ w (v - v') = 0 := by
      intro w
      have h3 : c * h₁ w v = c * h₁ w v' := by
        rw [← Sapp, ← Sapp, hvv]
      have h4 := mul_left_cancel₀ hc0 h3
      have h5 := hadd2 w (v - v') v'
      rw [sub_add_cancel, h4] at h5
      linear_combination -h5
    have : v - v' = 0 := hnd _ fun w => by
      have h6 := htr w (v - v') 1
      rw [one_smul, hz, mul_zero, map_zero] at h6
      exact h6.symm
    exact sub_eq_zero.1 this
  have hsurj : Function.Surjective S := by
    let g0 : (Fin N → E) →+ (Fin N → E) := AddMonoidHom.mk' (fun u i => S u (Pi.single i 1))
      (fun a b => by
        funext i
        show S (a + b) (Pi.single i 1) = S a (Pi.single i 1) + S b (Pi.single i 1)
        rw [Sapp, Sapp, Sapp, hadd2, mul_add])
    let g : (Fin N → E) →ₗ[ℚ] (Fin N → E) := g0.toRatLinearMap
    have gapp : ∀ u i, g u i = S u (Pi.single i 1) := fun _ _ => rfl
    have ginj : Function.Injective g := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro u hu
      have : S u = S 0 := by
        apply (Pi.basisFun E (Fin N)).ext
        intro i
        rw [Pi.basisFun_apply, map_zero, ← gapp, hu]
        rfl
      exact hinj (this.trans (by rw [map_zero]) |>.trans (map_zero S).symm)
    have gsurj : Function.Surjective g := LinearMap.injective_iff_surjective.1 ginj
    intro f
    obtain ⟨u, hu⟩ := gsurj fun i => f (Pi.single i 1)
    refine ⟨u, (Pi.basisFun E (Fin N)).ext fun i => ?_⟩
    rw [Pi.basisFun_apply, ← gapp, hu]
  refine ⟨⟨S, ⟨fun x y => ?_⟩, hinj, hsurj⟩, m, hm0, ?_, ?_⟩
  · have h7 : conjHom (maximalRealSubfield E) E (S x y) = IsCMField.complexConj E (S x y) :=
      quadConj_eq_complexConj _
    rw [h7, Sapp, Sapp, map_mul, htc, hsk y x]
    ring
  · intro a u v
    have h8 : ((m : E) * (H.rt : E))⁻¹ * S v u = h₁ u v := by
      rw [Sapp, ← hc, inv_mul_cancel_left₀ hc0]
    show Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * S v u)) = _
    rw [h8, htr]
  · intro x y
    show S (e x) (e y) ∈ integralClosure ℤ E
    rw [Sapp, hc]
    have h9 : (H.rt : E) ∈ integralClosure ℤ E := (H.rt).isIntegral_coe
    have h10 := mul_mem h9 (hint x y)
    convert h10 using 1
    ring

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.HermTrace
end
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund.Orbit

theorem log_h_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (ℓ : HermLine ι) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (ℓ.h (fun p => c p.1 * z p)) = Real.log (ℓ.h z) + ∑ k, (ℓ.a k : ℝ) * Real.log ‖c k‖ := by
  have hn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
  rw [ℓ.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hn k)) (ℓ.pos z hz).ne',
    Real.log_prod (fun k _ => zpow_ne_zero _ (hn k)), add_comm]
  simp only [Real.log_zpow]

theorem coef_add_smul {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (lam nu : Wt Ψ N) (s : ℝ)
    (j : Option (Ψ × Fin N)) : R.coef (lam - s • nu) s j + s * R.coef nu (-1) j = R.coef lam 0 j := by
  cases j with
  | none => simp only [RootModel.coef]; ring
  | some r => simp only [RootModel.coef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem line_a {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) :
    (R.line t j).a = (R.line 1 j).a := by
  cases j with
  | none => rfl
  | some r => simp only [RootModel.line, R.x_deg]

theorem torus_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (lam nu : Wt (CMType H) (D.p + D.q)) (n' n₀ : Option (RootIx D) → ℤ) (q₀ : ℕ) (s t : ℝ) (cc : RM.K → ℂ) (z : (Σ k, RM.ι k) → ℂ) (v : ℂ), 0 < q₀ → (∀ j, (n' j : ℝ) = RM.coef lam 0 j) → (∀ j, (n₀ j : ℝ) = q₀ * RM.coef nu (-1) j) → (∀ k, cc k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → v ≠ 0 → s / q₀ * Real.log ‖v * ∏ k, cc k ^ (combLine (RM.line 1) n₀).a k‖ + RM.weight t (lam - s • nu) s (fun p => cc p.1 * z p) - Real.log (∏ r, (Or.sing r).h (fun p => cc p.1 * z p) ^ n' (some r)) = s / q₀ * Real.log ‖v‖ + RM.weight t (lam - s • nu) s z - Real.log (∏ r, (Or.sing r).h z ^ n' (some r)) := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or lam nu n' n₀ q₀ s t cc z v hq hn' hn₀ hc hz hv
  have hq0 : (q₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have hn : ∀ k, ‖cc k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
  have hzc : ∀ k, ∃ i, (fun p : (Σ k, RM.ι k) => cc p.1 * z p) ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact ⟨i, mul_ne_zero (hc k) hi⟩

  have ha : ∀ k, (((combLine (RM.line 1) n₀).a k : ℤ) : ℝ) = ∑ j, (n₀ j : ℝ) * ((RM.line 1 j).a k : ℝ) := by
    intro k
    simp only [GlobalTheory.CompanionTheory.Ar.Top.combLine, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rfl

  have h1 : Real.log ‖v * ∏ k, cc k ^ (combLine (RM.line 1) n₀).a k‖ =
      Real.log ‖v‖ + ∑ k, ((combLine (RM.line 1) n₀).a k : ℝ) * Real.log ‖cc k‖ := by
    rw [norm_mul, norm_prod, Real.log_mul (norm_ne_zero_iff.mpr hv)
      (Finset.prod_ne_zero_iff.mpr fun k _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hc k))),
      Real.log_prod (fun k _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hc k)))]
    simp only [norm_zpow, Real.log_zpow]

  have h2 : RM.weight t (lam - s • nu) s (fun p => cc p.1 * z p) =
      RM.weight t (lam - s • nu) s z +
        ∑ k, (∑ j, RM.coef (lam - s • nu) s j * ((RM.line 1 j).a k : ℝ)) * Real.log ‖cc k‖ := by
    simp only [RootModel.weight, log_h_scale _ cc z hc hz, line_a RM t, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

  have hlog : ∀ w : (Σ k, RM.ι k) → ℂ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) →
      Real.log (∏ r, (Or.sing r).h w ^ n' (some r)) = ∑ r, (n' (some r) : ℝ) * Real.log ((Or.sing r).h w) := by
    intro w hw
    rw [Real.log_prod (fun r _ => (zpow_pos ((Or.sing r).pos w hw) _).ne')]
    simp only [Real.log_zpow]
  have h3 : Real.log (∏ r, (Or.sing r).h (fun p => cc p.1 * z p) ^ n' (some r)) =
      Real.log (∏ r, (Or.sing r).h z ^ n' (some r)) +
        ∑ k, (∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ)) * Real.log ‖cc k‖ := by
    rw [hlog _ hzc, hlog z hz]
    simp only [log_h_scale _ cc z hc hz, Or.sing_deg, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

  have hn'none : (n' none : ℝ) = 0 := by
    rw [hn' none]
    simp [RootModel.coef]
  have h4 : ∀ k, s / q₀ * ((combLine (RM.line 1) n₀).a k : ℝ) +
      ∑ j, RM.coef (lam - s • nu) s j * ((RM.line 1 j).a k : ℝ) =
      ∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ) := by
    intro k
    have e1 : ∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ) = ∑ j, (n' j : ℝ) * ((RM.line 1 j).a k : ℝ) := by
      rw [Fintype.sum_option, hn'none, zero_mul, zero_add]
      exact Finset.sum_congr rfl fun r _ => by simp only [RootModel.line, RM.x_deg]
    rw [e1, ha, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hn₀ j, hn' j, ← coef_add_smul RM lam nu s j]
    field_simp
    ring
  rw [h1, h2, h3]
  have h5 : s / q₀ * ∑ k, ((combLine (RM.line 1) n₀).a k : ℝ) * Real.log ‖cc k‖ +
      ∑ k, (∑ j, RM.coef (lam - s • nu) s j * ((RM.line 1 j).a k : ℝ)) * Real.log ‖cc k‖ =
      ∑ k, (∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ)) * Real.log ‖cc k‖ := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← h4 k]
    ring
  linear_combination h5

end GlobalTheory.CompanionTheory.Ar.Small.Fund.Orbit
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.ball_automorphism_inverse_exists : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Z (ballDom q) → Set.BijOn Z (ballDom q) (ballDom q) → DifferentiableOn ℂ G (ballDom q) → (∀ t ∈ ballDom q, ballPot q (Z t) = ballPot q t + (G t).re) → ∃ Y : (Fin n → ℂ) → Fin n → ℂ, DifferentiableOn ℂ Y (ballDom q) ∧ ∀ t ∈ ballDom q, Y t ∈ ballDom q ∧ Z (Y t) = t ∧ Y (Z t) = t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse.exists_inverse | exact GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse.exists_inverse | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BallInverse.exists_inverse <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex

theorem re_star_dotProduct_self {κ : Type} [Fintype κ] (w : κ → ℂ) :
    (star w ⬝ᵥ w).re = ‖WithLp.toLp 2 w‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [dotProduct, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (star (w i) * w i).re = Complex.normSq (w i) := by
    simp [Complex.normSq_apply]
  rw [this, Complex.normSq_eq_norm_sq]

theorem re_form_eq {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ']
    (Z : Matrix κ κ' ℂ) (v : κ' → ℂ) :
    (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)).re = ‖WithLp.toLp 2 v‖ ^ 2 - ‖WithLp.toLp 2 (Z *ᵥ v)‖ ^ 2 := by
  have h : star v ⬝ᵥ ((Zᴴ * Z) *ᵥ v) = star (Z *ᵥ v) ⬝ᵥ (Z *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, h, Complex.sub_re,
    re_star_dotProduct_self, re_star_dotProduct_self]

theorem posDef_iff {κ κ' : Type} [Fintype κ] [Fintype κ'] [DecidableEq κ']
    (Z : Matrix κ κ' ℂ) :
    (1 - Zᴴ * Z).PosDef ↔ ∀ v : κ' → ℂ, v ≠ 0 → ‖WithLp.toLp 2 (Z *ᵥ v)‖ < ‖WithLp.toLp 2 v‖ := by
  have hH : (1 - Zᴴ * Z).IsHermitian :=
    (Matrix.isHermitian_one).sub (Matrix.isHermitian_conjTranspose_mul_self _)
  constructor
  · intro h v hv
    have hpos := (Complex.lt_def.mp ((Matrix.posDef_iff_dotProduct_mulVec.mp h).2 hv)).1
    have h0 : (0 : ℝ) < ‖WithLp.toLp 2 v‖ ^ 2 - ‖WithLp.toLp 2 (Z *ᵥ v)‖ ^ 2 := by
      rw [← re_form_eq]
      simpa using hpos
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (sub_pos.mp h0)
  · intro h
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hH, fun v hv => ?_⟩
    have hre : 0 < (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)).re := by
      rw [re_form_eq, sub_pos]
      exact pow_lt_pow_left₀ (h v hv) (norm_nonneg _) two_ne_zero
    have hstar : star (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)) = star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v) := by
      conv_lhs => rw [star_dotProduct, star_star, Matrix.star_mulVec, hH.eq, ← Matrix.dotProduct_mulVec]
    have him : (star v ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v)).im = 0 := Complex.conj_eq_iff_im.mp hstar
    exact Complex.lt_def.mpr ⟨by simpa using hre, by simpa using him.symm⟩

theorem ballMat_combo {Ψ : Type} {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)
    (s t : Fin n → ℂ) (a b : ℝ) (τ : Ψ) :
    ballMat q (a • s + b • t) τ = a • ballMat q s τ + b • ballMat q t τ := by
  ext x y
  simp [ballMat]

theorem convex_ballDom {Ψ : Type} {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) [Fintype Ψ] :
    Convex ℝ (ballDom q) := by
  intro s hs t ht a b ha hb hab τ
  refine (posDef_iff _).mpr fun v hv => ?_
  have h1 := (posDef_iff _).mp (hs τ) v hv
  have h2 := (posDef_iff _).mp (ht τ) v hv
  have hc := convex_ball (0 : EuclideanSpace ℂ (Fin j)) ‖WithLp.toLp 2 v‖
    (x := WithLp.toLp 2 (ballMat q s τ *ᵥ v)) (y := WithLp.toLp 2 (ballMat q t τ *ᵥ v))
    (by simpa using h1) (by simpa using h2) ha hb hab
  have he : WithLp.toLp 2 (ballMat q (a • s + b • t) τ *ᵥ v) =
      a • WithLp.toLp 2 (ballMat q s τ *ᵥ v) + b • WithLp.toLp 2 (ballMat q t τ *ᵥ v) := by
    rw [ballMat_combo, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
    rfl
  rw [he]
  simpa using hc

theorem zero_mem_ballDom {Ψ : Type} {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have h : ballMat q (0 : Fin n → ℂ) τ = 0 := by
    ext x y
    simp [ballMat]
  rw [h]
  simpa using (Matrix.PosDef.one : (1 : Matrix (Fin j') (Fin j') ℂ).PosDef)

theorem ballDom_open_convex_zero : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n),
    IsOpen (ballDom q) ∧ Convex ℝ (ballDom q) ∧ (0 : Fin n → ℂ) ∈ ballDom q :=
  fun _ _ _ _ _ q => ⟨BallInverse.isOpen_ballDom q, convex_ballDom q, zero_mem_ballDom q⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex
end
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula : ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ (n k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Q.U n → paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z = maDens (fun (r : Fin (d + 1)) (z' : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (Q.G n (Fin.tail z')) (z' 0) else ∑ a, c a * Q.α n a (Fin.tail z')) z) ∧ ∀ i < k, ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Q.U n → paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z = maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; fun (r : Fin (d + 2)) (z' : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 0) + u r 1 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1) else ∑ a, c a * Q.α n a (Fin.tail (Fin.tail z'))) z := by
  intro d σ _ SY a₀ ε Q c hc n k hk _
  exact ⟨fun z hz => PositivityTheory.Xgp.sq_dens.part1 Q c hc n k z hz, fun i hi z hz => PositivityTheory.Xgp.sq_dens.part2 Q c hc n k hk i hi z hz⟩
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem coefficient_identities_give_operator_identity : ∀ (σ : Type) [Fintype σ] (D : ℕ) (a : (Fin (D + 1) → σ) → ℝ) (b : (Fin D → σ) → ℝ) (κ : ℕ → ℝ) (ε : σ → ℤ) (a₀ : σ), (∀ (π : Equiv.Perm (Fin (D + 1))) w, a (w ∘ π) = a w) → (∀ (π : Equiv.Perm (Fin D)) w, b (w ∘ π) = b w) → (∀ n : σ → ℤ, n a₀ = 0 → polar (D + 1) a (fun _ x => (n x : ℝ)) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 → polar (D + 1) a (mix (2 * k) (fun x => (ε x : ℝ)) fun x => (n x : ℝ)) = -(2 * κ k) * polar D b (mix (2 * k - 1) (fun x => (ε x : ℝ)) fun x => (n x : ℝ))) → ∀ (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (formPoly (D + 1) a) + eval (fun x => c x + u / 2 * ε x) (formPoly (D + 1) a) = (tsgPoly D κ (linePoly c ε (formPoly D b))).eval u :=
  @PositivityTheory.Xgp.t_thma_alg

end GlobalTheory.CompanionTheory.Ar.PB
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.holomorphic_span_coefficients : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (n m : ℕ) (W : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (b c : Fin m → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ), IsOpen W → t₀ ∈ W → (∀ i, DifferentiableOn ℂ (b i) W) → (∀ i, DifferentiableOn ℂ (c i) W) → (∀ t ∈ W, LinearIndependent ℂ fun i => b i t) → (∀ t ∈ W, ∀ i, c i t ∈ Submodule.span ℂ (Set.range fun j => b j t)) → LinearIndependent ℂ (fun i => c i t₀) → ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ W ∧ ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G V ∧ ∀ t ∈ V, LinearIndependent ℂ (fun i => c i t) ∧ Real.log ((R t).gram fun i => c i t).det.re = Real.log ((R t).gram fun i => b i t).det.re + (G t).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange.log_gram_frame_change | exact GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange.log_gram_frame_change | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange.log_gram_frame_change <;> assumption)
end
