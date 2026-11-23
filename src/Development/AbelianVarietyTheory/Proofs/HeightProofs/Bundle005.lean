module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle003
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Encodable
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.UniformSpace.Uniformizable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA

@[expose] public section

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms.DerLinear

variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}

theorem anti_exp (H : IsLieData σ j s) (a : 𝔸) : σ (NormedSpace.exp a) = NormedSpace.exp (σ a) := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  let f : 𝔸 →+* 𝔸ᵐᵒᵖ :=
    { toFun := fun b => MulOpposite.op (σ b)
      map_one' := by simp [H.one]
      map_mul' := fun b c => by simp [H.anti]
      map_zero' := by simp
      map_add' := fun b c => by simp }
  have hf : Continuous f := MulOpposite.continuous_op.comp (LinearMap.continuous_of_finiteDimensional σ)
  have h := NormedSpace.map_exp f hf a
  apply MulOpposite.op_injective
  rw [← NormedSpace.exp_op]
  exact h

theorem exp_unitary (H : IsLieData σ j s) (X : L) :
    σ (NormedSpace.exp (j X)) * NormedSpace.exp (j X) = 1 := by
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hs : σ (j X) = -j X := (H.skew (j X)).2 ⟨X, rfl⟩
  rw [anti_exp H, hs, ← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl _)), neg_add_cancel,
    NormedSpace.exp_zero]

theorem contDiff_exp (H : IsLieData σ j s) : ContDiff ℝ ∞ fun X : L => NormedSpace.exp (j X) := by
  have : FiniteDimensional ℝ L := Module.Finite.of_injective j H.inj
  have : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hexp : ContDiff ℝ ∞ (NormedSpace.exp : 𝔸 → 𝔸) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact hexp.comp (LinearMap.toContinuousLinearMap j).contDiff

omit [FiniteDimensional ℝ 𝔸] in
theorem der_eq_fderiv {e : L → G} {φ : G → ℂ} (hφ : Sm e φ) (X : L) (g : G) :
    Der e X φ g = fderiv ℝ (fun Z : L => φ (g * e Z)) 0 X := by
  have hF : DifferentiableAt ℝ (fun Z : L => φ (g * e Z)) 0 :=
    ((contDiff_infty_iff_fderiv.1 (hφ g)).1) 0
  have hd : HasDerivAt (fun t : ℝ => t • X) X 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const X
  have hF' : HasFDerivAt (fun Z : L => φ (g * e Z)) (fderiv ℝ (fun Z : L => φ (g * e Z)) 0) ((0 : ℝ) • X) := by
    rw [zero_smul]
    exact hF.hasFDerivAt
  exact (hF'.comp_hasDerivAt (0 : ℝ) hd).deriv

theorem sm_der (H : IsLieData σ j s) (hl : HasLog σ j) {φ : G → ℂ} (hφ : Sm (expMap j s) φ) (X : L) :
    Sm (expMap j s) (Der (expMap j s) X φ) := by
  intro g
  have hu1 : ∀ Z : L, σ (NormedSpace.exp (j Z)) * NormedSpace.exp (j Z) = 1 := exp_unitary H
  let c : L × ℝ → 𝔸 := fun p => NormedSpace.exp (j p.1) * NormedSpace.exp (j (p.2 • X))
  have hcd : ContDiff ℝ ∞ c :=
    ((contDiff_exp H).comp contDiff_fst).mul ((contDiff_exp H).comp (contDiff_snd.smul contDiff_const))
  have hcu : ∀ p, σ (c p) * c p = 1 := by
    intro p
    simp only [c]
    rw [H.anti, mul_assoc, ← mul_assoc (σ (NormedSpace.exp (j p.1))), hu1, one_mul, hu1]
  have hφ0 : ∀ g, ContDiffAt ℝ ∞ (fun X : L => φ (g * expMap j s X)) 0 := fun g => (hφ g).contDiffAt
  have hF := contDiff_family H hl hφ0 hcd hcu g
  have key : ∀ Y : L, Der (expMap j s) X φ (g * expMap j s Y) =
      fderiv ℝ (fun p : L × ℝ => φ (g * s (c p))) (Y, 0) ((0 : L), (1 : ℝ)) := by
    intro Y
    have h1 : (fun t : ℝ => φ (g * expMap j s Y * expMap j s (t • X))) = fun t => φ (g * s (c (Y, t))) := by
      funext t
      simp only [c, expMap, mul_assoc, H.mul _ _ (hu1 Y) (hu1 (t • X))]
    have hd : HasDerivAt (fun t : ℝ => ((Y, t) : L × ℝ)) ((0 : L), (1 : ℝ)) 0 :=
      (hasDerivAt_const (0 : ℝ) Y).prodMk (hasDerivAt_id 0)
    have hFd : HasFDerivAt (fun p : L × ℝ => φ (g * s (c p)))
        (fderiv ℝ (fun p : L × ℝ => φ (g * s (c p))) (Y, 0)) (Y, 0) :=
      ((contDiff_infty_iff_fderiv.1 hF).1 _).hasFDerivAt
    show deriv (fun t : ℝ => φ (g * expMap j s Y * expMap j s (t • X))) 0 = _
    rw [h1]
    exact (hFd.comp_hasDerivAt (0 : ℝ) hd).deriv
  simp_rw [key]
  exact (((contDiff_infty_iff_fderiv.1 hF).2).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const

end GlobalTheory.SmoothForms.DerLinear

namespace GlobalTheory.SmoothForms

theorem der_smooth_and_linear : ∀ (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G), IsLieData σ j s → HasLog σ j → ∀ φ : G → ℂ, Sm (expMap j s) φ → (∀ X, Sm (expMap j s) (Der (expMap j s) X φ)) ∧ (∀ X Y, Der (expMap j s) (X + Y) φ = Der (expMap j s) X φ + Der (expMap j s) Y φ) ∧ ∀ (c : ℝ) X, Der (expMap j s) (c • X) φ = (c : ℂ) • Der (expMap j s) X φ := by
  intro 𝔸 L G _ _ _ _ _ _ σ j s H hl φ hφ
  refine ⟨fun X => DerLinear.sm_der H hl hφ X, fun X Y => ?_, fun c X => ?_⟩
  · funext g
    rw [Pi.add_apply, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, map_add (f := _)]
  · funext g
    rw [Pi.smul_apply, DerLinear.der_eq_fderiv hφ, DerLinear.der_eq_fderiv hφ, map_smul, Complex.real_smul,
      smul_eq_mul]

end GlobalTheory.SmoothForms
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

theorem anti_map_exp {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] (σ : 𝔸 →ₗ[ℝ] 𝔸)
    (anti : ∀ a b, σ (a * b) = σ b * σ a) (one : σ 1 = 1) (X : 𝔸) :
    σ (NormedSpace.exp X) = NormedSpace.exp (σ X) := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hp : ∀ n : ℕ, σ (X ^ n) = σ X ^ n := fun n => by
    induction n with
    | zero => simpa using one
    | succ n ih => rw [pow_succ, anti, ih, pow_succ']
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X).map σ.toAddMonoidHom
    σ.continuous_of_finiteDimensional
  refine h1.unique ?_
  convert NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (σ X) using 1
  funext n
  simp [hp]

theorem exists_local_log (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] :
    ∃ l : 𝔸 → 𝔸, ContDiffAt ℝ ∞ l 1 ∧ (∀ᶠ h in 𝓝 (1 : 𝔸), NormedSpace.exp (l h) = h) ∧
      ∀ᶠ X in 𝓝 (0 : 𝔸), l (NormedSpace.exp X) = X := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  have hc : ContDiffAt ℝ ∞ (NormedSpace.exp : 𝔸 → 𝔸) 0 := (NormedSpace.exp_analytic (𝕂 := ℝ) 0).contDiffAt
  have hd : HasFDerivAt (NormedSpace.exp : 𝔸 → 𝔸)
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := hasFDerivAt_exp_zero
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hc.localInverse hd hn, ?_, ?_, (hc.hasStrictFDerivAt' hd hn).eventually_left_inverse⟩
  · have := hc.to_localInverse hd hn
    rwa [NormedSpace.exp_zero] at this
  · have := (hc.hasStrictFDerivAt' hd hn).eventually_right_inverse
    rw [NormedSpace.exp_zero] at this
    exact this

theorem hasLog_of_isLieData (𝔸 L G : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸]
    [NormedAddCommGroup L] [NormedSpace ℝ L] [Group G] (σ : 𝔸 →ₗ[ℝ] 𝔸) (j : L →ₗ[ℝ] 𝔸) (s : 𝔸 → G)
    (H : IsLieData σ j s) : HasLog σ j := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ 𝔸
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  haveI : FiniteDimensional ℝ L := FiniteDimensional.of_injective j H.inj
  obtain ⟨l, h1, h2, h3⟩ := exists_local_log 𝔸
  obtain ⟨p, hp⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 H.inj)
  have hp' : ∀ Y, p (j Y) = Y := fun Y => LinearMap.congr_fun hp Y
  have hl : l 1 = 0 := by simpa using h3.self_of_nhds
  refine ⟨fun h => p (l h), (LinearMap.toContinuousLinearMap p).contDiff.contDiffAt.comp 1 h1, ?_, ?_⟩
  · have ht : Filter.Tendsto (fun h => -σ (l h)) (𝓝 1) (𝓝 0) := by
      have := (σ.continuous_of_finiteDimensional.continuousAt.comp h1.continuousAt).neg.tendsto
      have e : (-(⇑σ ∘ l)) 1 = 0 := by simp [hl]
      rw [e] at this
      exact this
    filter_upwards [h2, ht.eventually h3] with h ha hb hu
    have e1 : NormedSpace.exp (σ (l h)) * h = 1 := by
      rw [← anti_map_exp σ H.anti H.one, ha, hu]
    have e2 : NormedSpace.exp (-σ (l h)) * NormedSpace.exp (σ (l h)) = 1 := by
      rw [← NormedSpace.exp_add_of_commute (Commute.refl _).neg_left, neg_add_cancel, NormedSpace.exp_zero]
    have e3 : NormedSpace.exp (-σ (l h)) = h := by
      rw [← mul_one (NormedSpace.exp (-σ (l h))), ← e1, ← mul_assoc, e2, one_mul]
    rw [e3] at hb
    obtain ⟨Y, hY⟩ := (H.skew (l h)).1 (neg_eq_iff_eq_neg.1 hb.symm)
    rw [← hY, hp', hY, ha]
  · have ht : Filter.Tendsto j (𝓝 0) (𝓝 0) := by
      simpa using j.continuous_of_finiteDimensional.tendsto 0
    filter_upwards [ht.eventually h3] with X hX
    rw [hX, hp']

end GlobalTheory.SmoothForms
end

section

open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology

namespace GlobalTheory.SmoothForms

theorem commutator_prod_ofFn {A : Type} [Ring A] (x : A) :
    ∀ (d : ℕ) (f : Fin d → A), x * (List.ofFn f).prod - (List.ofFn f).prod * x =
      ∑ p, (List.ofFn (Function.update f p (x * f p - f p * x))).prod
  | 0, f => by simp
  | d + 1, f => by
    have ih := commutator_prod_ofFn x d (fun i => f i.succ)
    have h : ∀ (p : Fin d) (y : A), (fun i : Fin d => Function.update f p.succ y i.succ) =
        Function.update (fun i => f i.succ) p y := fun p y => by
      funext i
      by_cases h : i = p
      · subst h; simp
      · simp [Function.update_of_ne h, Function.update_of_ne (fun h' => h (Fin.succ_injective _ h'))]
    rw [Fin.sum_univ_succ]
    simp only [List.ofFn_succ, List.prod_cons, Function.update_self, h,
      Function.update_of_ne (Fin.succ_ne_zero _), Function.update_of_ne (Fin.succ_ne_zero _).symm]
    rw [← Finset.mul_sum, ← ih]
    noncomm_ring

theorem sum_polar_left {A : Type} [AddCommGroup A] [Module ℂ A] {n d : ℕ} (a b : Fin n) (I : Fin d → Fin n)
    (g : (Fin d → Fin n) → A) :
    ∑ J, polar n d a b J I • g J = ∑ p, if b = I p then g (Function.update I p a) else 0 := by
  simp only [polar, Matrix.of_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : ∀ J : Fin d → Fin n, (J p = a ∧ I p = b ∧ ∀ q, q ≠ p → J q = I q) ↔
      (b = I p ∧ J = Function.update I p a) := fun J => by
    rw [Function.eq_update_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2.symm, h1, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1.symm, h3⟩
  simp only [h]
  by_cases hb : b = I p <;> simp [hb]

theorem sum_polar_right {A : Type} [AddCommGroup A] [Module ℂ A] {n d : ℕ} (a b : Fin n) (K : Fin d → Fin n)
    (g : (Fin d → Fin n) → A) :
    ∑ J, polar n d a b K J • g J = ∑ p, if K p = a then g (Function.update K p b) else 0 := by
  simp only [polar, Matrix.of_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : ∀ J : Fin d → Fin n, (K p = a ∧ J p = b ∧ ∀ q, q ≠ p → K q = J q) ↔
      (K p = a ∧ J = Function.update K p b) := fun J => by
    rw [Function.eq_update_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun q hq => (h3 q hq).symm⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun q hq => (h3 q hq).symm⟩
  simp only [h]
  by_cases hb : K p = a <;> simp [hb]

theorem commutator_word {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E)
    {d : ℕ} (a b : Fin n) (I K : Fin d → Fin n) :
    E a b * (List.ofFn fun q => E (I q) (K q)).prod - (List.ofFn fun q => E (I q) (K q)).prod * E a b =
      ∑ J, polar n d a b J I • (List.ofFn fun q => E (J q) (K q)).prod -
        ∑ J, polar n d a b K J • (List.ofFn fun q => E (I q) (J q)).prod := by
  rw [commutator_prod_ofFn, sum_polar_left, sum_polar_right, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h1 : (fun q => E (Function.update I p a q) (K q)) =
      Function.update (fun q => E (I q) (K q)) p (E a (K p)) := by
    funext q
    by_cases h : q = p
    · subst h; simp
    · simp [Function.update_of_ne h]
  have h2 : (fun q => E (I q) (Function.update K p b q)) =
      Function.update (fun q => E (I q) (K q)) p (E (I p) b) := by
    funext q
    by_cases h : q = p
    · subst h; simp
    · simp [Function.update_of_ne h]
  rw [h1, h2, hE a b (I p) (K p)]
  simp only [← MultilinearMap.mkPiAlgebraFin_apply (R := ℂ), MultilinearMap.map_update_sub]
  congr 1 <;> split_ifs <;> simp only [MultilinearMap.map_update_zero]

theorem commutator_wordMap : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A),
    Formalism.REAL.GlRel E → ∀ (d : ℕ) (a b : Fin n) (M : Matrix (Fin d → Fin n) (Fin d → Fin n) ℂ),
    E a b * wordMap E d M - wordMap E d M * E a b =
      wordMap E d (polar n d a b * M - M * polar n d a b) := by
  intro A _ _ n E hE d a b M
  have hw : ∀ N, wordMap E d N = ∑ I, ∑ K, N I K • (List.ofFn fun q : Fin d => E (I q) (K q)).prod := fun _ => rfl
  have hl : wordMap E d (polar n d a b * M) =
      ∑ I, ∑ K, M I K • ∑ J, polar n d a b J I • (List.ofFn fun q => E (J q) (K q)).prod := by
    simp only [hw, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun K _ => ?_
    rw [Finset.sum_comm]
    simp only [mul_comm]
  have hr : wordMap E d (M * polar n d a b) =
      ∑ I, ∑ K, M I K • ∑ J, polar n d a b K J • (List.ofFn fun q => E (I q) (J q)).prod := by
    simp only [hw, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_comm]
  rw [map_sub, hl, hr, hw, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun K _ => ?_
  rw [← smul_sub, ← commutator_word hE, smul_sub, mul_smul_comm, smul_mul_assoc]

end GlobalTheory.SmoothForms
end

section

namespace GlobalTheory.PowEntryCommutator

open Matrix

theorem pow_entry_commutator {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) (a b : Fin n) (m : ℕ) (c e : Fin n) :
    E a b * ((Matrix.of E) ^ m) c e - ((Matrix.of E) ^ m) c e * E a b =
      (if b = c then ((Matrix.of E) ^ m) a e else 0) -
        (if e = a then ((Matrix.of E) ^ m) c b else 0) := by
  induction m generalizing c e with
  | zero =>
    clear hE
    simp only [pow_zero, Matrix.one_apply]
    by_cases h1 : c = e <;> by_cases h2 : b = c <;> by_cases h3 : e = a <;>
      simp only [h1, h2, h3, if_true, if_false, mul_one, one_mul, mul_zero, zero_mul, sub_self] <;>
      subst_vars <;> simp_all <;> intro h <;> subst h <;> simp_all
  | succ m ih =>
    have hs : ∀ x y : Fin n, ((Matrix.of E) ^ (m + 1)) x y
        = ∑ k, ((Matrix.of E) ^ m) x k * E k y := by
      intro x y; rw [pow_succ, Matrix.mul_apply]; rfl
    have key : ∀ k, E a b * (((Matrix.of E) ^ m) c k * E k e)
          - ((Matrix.of E) ^ m) c k * E k e * E a b
        = (E a b * ((Matrix.of E) ^ m) c k - ((Matrix.of E) ^ m) c k * E a b) * E k e
          + ((Matrix.of E) ^ m) c k * (E a b * E k e - E k e * E a b) := by
      intro k; noncomm_ring
    rw [hs, hs, hs, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp_rw [key, ih, hE a b]
    simp only [sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, mul_ite,
      zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const_zero]
    split_ifs <;> simp [Finset.sum_sub_distrib] <;> abel

theorem target : ∀ {A : Type} [inst : Ring A] {n : ℕ} (E : Fin n → Fin n → A), Formalism.REAL.GlRel E →
    ∀ (a b : Fin n) (m : ℕ) (c e : Fin n),
    E a b * ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) c e -
      ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) c e * E a b =
    (if b = c then ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) a e
      else (0 : A)) -
    if e = a then ((Matrix.of : (Fin n → Fin n → A) → Matrix (Fin n) (Fin n) A) E ^ m) c b
      else (0 : A) :=
  fun E hE a b m c e => pow_entry_commutator E hE a b m c e

end GlobalTheory.PowEntryCommutator
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

theorem dense_mvPolynomial_eval_ne_zero {D : ℕ} (q : MvPolynomial (Fin D) ℂ) (hq : q ≠ 0) :
    Dense {z : Fin D → ℂ | MvPolynomial.eval z q ≠ 0} := by
  rw [Metric.dense_iff]
  intro z₀ r hr
  by_contra hne
  apply hq
  refine MvPolynomial.funext_set (fun i => Metric.ball (z₀ i) r)
    (fun i => infinite_of_mem_nhds (z₀ i) (Metric.ball_mem_nhds _ hr)) (fun x hx => ?_)
  rw [map_zero]
  by_contra hx0
  apply hne
  refine ⟨x, ?_, hx0⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  exact fun i => hx i (Set.mem_univ i)

theorem exists_algIndep_tuple_near :
    ∀ (K : Type) [Field K] [Countable K] (sg : K →+* ℂ) (D : ℕ) (z₀ : Fin D → ℂ) (ε : ℝ), 0 < ε → ∃ z : Fin D → ℂ, (∀ i, ‖z i - z₀ i‖ < ε) ∧ ∀ p : MvPolynomial (Fin D) K, p ≠ 0 → MvPolynomial.eval₂ sg z p ≠ 0 := by
  intro K _ _ sg D z₀ ε hε
  let S : {p : MvPolynomial (Fin D) K // p ≠ 0} → Set (Fin D → ℂ) :=
    fun p => {z | MvPolynomial.eval z (MvPolynomial.map sg p.1) ≠ 0}
  have : Countable (MvPolynomial (Fin D) K) := by
    refine Function.Surjective.countable (f := fun l : List ((Fin D →₀ ℕ) × K) =>
      (l.map fun mc => MvPolynomial.monomial mc.1 mc.2).sum) fun p => ?_
    refine ⟨p.support.toList.map fun m => (m, AddMonoidAlgebra.coeff p m), ?_⟩
    simp only [List.map_map]
    rw [Finset.sum_map_toList]
    exact p.as_sum.symm
  have hS : Dense (⋂ p, S p) := by
    apply dense_iInter_of_isOpen
    · intro p
      exact isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const
    · intro p
      refine dense_mvPolynomial_eval_ne_zero _ fun h0 => p.2 ?_
      exact MvPolynomial.map_injective sg sg.injective (h0.trans (map_zero _).symm)
  obtain ⟨z, hzS, hz⟩ := hS.exists_mem_open (Metric.isOpen_ball (x := z₀)) (Metric.nonempty_ball.mpr hε)
  refine ⟨z, ?_, fun p hp => ?_⟩
  · rw [Metric.mem_ball, dist_pi_lt_iff hε] at hz
    intro i
    rw [← dist_eq_norm]
    exact hz i
  · rw [← MvPolynomial.eval_map]
    exact Set.mem_iInter.mp hzS ⟨p, hp⟩

end GlobalTheory
end
