module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
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
public import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Nonarchimedean.Completion
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Data.Int.WithZero
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.Units

@[expose] public section

section

namespace GlobalTheory

theorem exists_unit_dirichletCharacter_ne_one_ne_one {N : ℕ} (θ₁ θ₂ : DirichletCharacter ℂ N)
    (h₁ : θ₁ ≠ 1) (h₂ : θ₂ ≠ 1) :
    ∃ u : (ZMod N)ˣ, θ₁ (u : ZMod N) ≠ 1 ∧ θ₂ (u : ZMod N) ≠ 1 := by
  obtain ⟨u₁, hu₁⟩ := MulChar.ne_one_iff.1 h₁
  obtain ⟨u₂, hu₂⟩ := MulChar.ne_one_iff.1 h₂
  by_cases a : θ₂ (u₁ : ZMod N) = 1
  · by_cases b : θ₁ (u₂ : ZMod N) = 1
    · refine ⟨u₁ * u₂, ?_, ?_⟩
      · rw [Units.val_mul, map_mul, b, mul_one]; exact hu₁
      · rw [Units.val_mul, map_mul, a, one_mul]; exact hu₂
    · exact ⟨u₂, b, hu₂⟩
  · exact ⟨u₁, hu₁, a⟩

theorem sq_ne_pow_succ_mul_zpow {p e : ℕ} (hp : 1 < p) (he : 1 ≤ e) {x : ℂ} (hx : ‖x‖ = 1)
    (hx1 : x ≠ 1) {n : ℤ} (hn : n = 1 ∨ n = -1) :
    (p : ℂ) ^ 2 ≠ (p : ℂ) ^ (e + 1) * x ^ n := by
  have hy1 : x ^ n ≠ 1 := by
    rcases hn with rfl | rfl
    · simpa using hx1
    · rw [zpow_neg_one]; exact fun h => hx1 (inv_eq_one.1 h)
  have hyn : ‖x ^ n‖ = 1 := by rw [norm_zpow, hx, one_zpow]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  intro h
  rcases Nat.lt_or_ge e 2 with he2 | he2
  · have : e = 1 := by omega
    subst this
    have h' : (p : ℂ) ^ 2 * x ^ n = (p : ℂ) ^ 2 := h.symm
    exact hy1 ((mul_eq_left₀ (pow_ne_zero 2 hp0)).1 h')
  · have h2 := congrArg norm h
    rw [norm_mul, hyn, mul_one, norm_pow, norm_pow, Complex.norm_natCast] at h2
    have hp' : (1 : ℝ) < p := by exact_mod_cast hp
    have := pow_lt_pow_right₀ hp' (show 2 < e + 1 by omega)
    linarith

theorem smoothing_integers_two_characters : ∀ (N l e : ℕ) (θ₁ θ₂ : DirichletCharacter ℂ N)
    (ψ : DirichletCharacter ℂ l), 0 < N → l.Prime → ¬ l ∣ N → 1 ≤ e → θ₁ ≠ 1 → θ₂ ≠ 1 →
    ∃ c d : ℕ, 1 < c ∧ 1 < d ∧ c.Coprime (6 * N * l) ∧ d.Coprime (6 * N * l) ∧
      (∀ z : ℂ, ‖z‖ = 1 → (c : ℂ) ^ e ≠ z) ∧
      ∀ n₁ n₂ : ℤ, (n₁ = 1 ∨ n₁ = -1) →
        (d : ℂ) ^ 2 ≠ (d : ℂ) ^ (e + 1) * (θ₁ d ^ n₁ * ψ d ^ n₂) ∧
        (d : ℂ) ^ 2 ≠ (d : ℂ) ^ (e + 1) * (θ₂ d ^ n₁ * ψ d ^ n₂) := by
  intro N l e θ₁ θ₂ ψ hN hl hlN he h₁ h₂
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI : NeZero (N * l) := ⟨Nat.mul_ne_zero hN.ne' hl.ne_zero⟩
  have hcop : N.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hlN).symm
  have hM : 0 < 6 * N * l := Nat.mul_pos (Nat.mul_pos (by norm_num) hN) hl.pos
  obtain ⟨u, hu₁, hu₂⟩ := exists_unit_dirichletCharacter_ne_one_ne_one θ₁ θ₂ h₁ h₂
  obtain ⟨k, hkN, hkl⟩ := Nat.chineseRemainder hcop (u : ZMod N).val 1
  have hkN' : (k : ZMod N) = u := by
    rw [(ZMod.natCast_eq_natCast_iff k _ N).2 hkN, ZMod.natCast_zmod_val]
  have hkl' : (k : ZMod l) = 1 := by
    rw [(ZMod.natCast_eq_natCast_iff k 1 l).2 hkl, Nat.cast_one]
  have hk1 : k.Coprime N := (ZMod.isUnit_iff_coprime k N).1 (hkN' ▸ u.isUnit)
  have hk2 : k.Coprime l := (ZMod.isUnit_iff_coprime k l).1 (hkl' ▸ isUnit_one)
  have hunit : IsUnit (k : ZMod (N * l)) :=
    (ZMod.isUnit_iff_coprime k (N * l)).2 (Nat.Coprime.mul_right hk1 hk2)
  obtain ⟨p, hpgt, hp, hpk⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (6 * N * l)
  have hpN : (p : ZMod N) = u := by
    have := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) hpk
    rw [map_natCast, map_natCast] at this
    rw [this, hkN']
  have hpl : (p : ZMod l) = 1 := by
    have := congrArg (ZMod.castHom (dvd_mul_left l N) (ZMod l)) hpk
    rw [map_natCast, map_natCast] at this
    rw [this, hkl']
  have hpcop : p.Coprime (6 * N * l) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt hM hpgt)
  refine ⟨6 * N * l + 1, p, by omega, hp.one_lt, ?_, hpcop, ?_, ?_⟩
  · rw [add_comm, Nat.coprime_add_self_left]; exact Nat.coprime_one_left _
  · intro z hz h
    have h2 := congrArg norm h
    rw [norm_pow, Complex.norm_natCast, hz] at h2
    have hc' : (1 : ℝ) < ((6 * N * l + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < 6 * N * l + 1 by omega)
    have := one_lt_pow₀ hc' (show e ≠ 0 by omega)
    linarith
  · intro n₁ n₂ hn
    rw [hpl, map_one, one_zpow, mul_one, mul_one, hpN]
    exact ⟨sq_ne_pow_succ_mul_zpow hp.one_lt he (DirichletCharacter.unit_norm_eq_one _ _) hu₁ hn,
      sq_ne_pow_succ_mul_zpow hp.one_lt he (DirichletCharacter.unit_norm_eq_one _ _) hu₂ hn⟩

end GlobalTheory
end

section

open Filter Topology

namespace GlobalTheory

theorem exists_baseChange_extension_of_flat {A K E M : Type*} [CommRing A] [Field K] [Algebra A K]
    [Module.Flat A K] [AddCommGroup E] [Module K E] [AddCommGroup M] [Module A M]
    (B : Submodule A M) (Θ : B → E)
    (h : ∀ (a a' : A) (b b' : B),
      Θ (a • b + a' • b') = algebraMap A K a • Θ b + algebraMap A K a' • Θ b') :
    ∃ L : TensorProduct A K M →ₗ[K] E, ∀ b : B, L (1 ⊗ₜ[A] (b : M)) = Θ b := by
  letI : Module A E := Module.compHom E (algebraMap A K)
  have hs : ∀ (a : A) (e : E), a • e = algebraMap A K a • e := fun _ _ => rfl
  haveI : IsScalarTower A K E := ⟨fun a k e => by rw [hs, Algebra.smul_def, mul_smul]⟩
  let Θ' : B →ₗ[A] E :=
    { toFun := Θ
      map_add' := fun b b' => by simpa using h 1 1 b b'
      map_smul' := fun a b => by
        have := h a 0 b b
        rwa [zero_smul, add_zero, map_zero, zero_smul, add_zero] at this }
  have hinj : Function.Injective (B.subtype.baseChange K) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ B.injective_subtype
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (B.subtype.baseChange K)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(Θ'.liftBaseChange K).comp r, fun b => ?_⟩
  have h1 : r (1 ⊗ₜ[A] (b : M)) = 1 ⊗ₜ[A] b := by
    simpa using LinearMap.congr_fun hr (1 ⊗ₜ[A] b)
  rw [LinearMap.comp_apply, h1, LinearMap.liftBaseChange_tmul, one_smul]
  rfl

theorem tendsto_appr_padicComplex (l : ℕ) [Fact l.Prime] (a : ℤ_[l]) :
    Tendsto (fun n => (((a.appr n : ℕ) : PadicAlgCl l) : ℂ_[l])) atTop
      (𝓝 ((algebraMap ℤ_[l] (PadicAlgCl l) a : PadicAlgCl l) : ℂ_[l])) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hq : ‖(l : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hq)
  have hn : ∀ z : ℤ_[l], ‖algebraMap ℤ_[l] (PadicAlgCl l) z‖ = ‖z‖ := fun z =>
    PadicAlgCl.norm_extends l (z : ℚ_[l])
  rw [← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends,
    ← map_natCast (algebraMap ℤ_[l] (PadicAlgCl l)), ← map_sub, hn, norm_sub_rev]
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n a)
  rw [← ht, norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) t.norm_le_one

theorem exists_linear_limit_of_compatible_family :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M)
      (R : ℕ → M → PadicAlgCl l → Prop) (C : ℝ),
    (∀ n, ∀ b ∈ B, ∃ x, R n b x) →
    (∀ n, ∀ b ∈ B, ∀ x y, R (n + 1) b x → R n b y →
      ‖x - y‖ ≤ C * ‖((l : ℕ) : PadicAlgCl l) ^ n‖) →
    (∀ n, ∀ b ∈ B, ∀ b' ∈ B, ∀ (a a' : ℤ_[l]) (x x' : PadicAlgCl l), R n b x → R n b' x' →
      R n (a • b + a' • b')
        (((a.appr n : ℕ) : PadicAlgCl l) * x + ((a'.appr n : ℕ) : PadicAlgCl l) * x')) →
    ∃ L : TensorProduct ℤ_[l] (PadicAlgCl l) M →ₗ[PadicAlgCl l] ℂ_[l], ∀ n, ∀ b ∈ B, ∀ x,
      R n b x → ‖(x : ℂ_[l]) - L (1 ⊗ₜ[ℤ_[l]] b)‖ ≤ C * ‖((l : ℕ) : PadicAlgCl l) ^ n‖ := by
  intro l _ M _ _ B R C h1 h2 h3
  simp only [norm_pow] at h2 ⊢
  set q : ℝ := ‖((l : ℕ) : PadicAlgCl l)‖ with hqdef
  have hq0 : 0 ≤ q := norm_nonneg _
  have hq1 : q < 1 := by
    rw [hqdef, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  choose! x hx using h1
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans
      (h2 0 0 B.zero_mem _ _ (hx 1 0 B.zero_mem) (hx 0 0 B.zero_mem))
    simpa using this
  have hmono : ∀ {n m : ℕ}, n ≤ m → C * q ^ m ≤ C * q ^ n := fun h =>
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1.le h) hC
  have htail : ∀ n, ∀ b ∈ B, ∀ y, R n b y → ∀ m, n + 1 ≤ m → ‖x m b - y‖ ≤ C * q ^ n := by
    intro n b hb y hy m hm
    induction m, hm using Nat.le_induction with
    | base => exact h2 n b hb _ _ (hx _ b hb) hy
    | succ m hm ih =>
      have e : x (m + 1) b - y = (x (m + 1) b - x m b) + (x m b - y) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      exact (h2 m b hb _ _ (hx _ b hb) (hx _ b hb)).trans (hmono (by omega))
  have hlim : ∀ b : B, ∃ z : ℂ_[l], Tendsto (fun n => ((x n b : PadicAlgCl l) : ℂ_[l])) atTop (𝓝 z) := by
    intro b
    refine cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric q C hq1 fun n => ?_)
    rw [dist_eq_norm, ← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends, norm_sub_rev]
    exact h2 n b b.2 _ _ (hx _ _ b.2) (hx _ _ b.2)
  choose Θ hΘ using hlim
  have hbound : ∀ n (b : B) (y : PadicAlgCl l), R n b y → ‖(y : ℂ_[l]) - Θ b‖ ≤ C * q ^ n := by
    intro n b y hy
    refine le_of_tendsto ((tendsto_const_nhds (x := (y : ℂ_[l]))).sub (hΘ b)).norm
      (eventually_atTop.2 ⟨n + 1, fun m hm => ?_⟩)
    rw [← UniformSpace.Completion.coe_sub, PadicComplex.norm_extends, norm_sub_rev]
    exact htail n b b.2 y hy m hm
  haveI : Module.Flat ℤ_[l] ℚ_[l] := IsLocalization.flat ℚ_[l] (nonZeroDivisors ℤ_[l])
  haveI : Module.Flat ℤ_[l] (PadicAlgCl l) := Module.Flat.trans ℤ_[l] ℚ_[l] (PadicAlgCl l)
  obtain ⟨L, hL⟩ := exists_baseChange_extension_of_flat (K := PadicAlgCl l) B Θ (by
    intro a a' b b'
    have hA := ((tendsto_appr_padicComplex l a).mul (hΘ b)).add
      ((tendsto_appr_padicComplex l a').mul (hΘ b'))
    rw [Algebra.smul_def, Algebra.smul_def]
    refine tendsto_nhds_unique ?_ hA
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun n : ℕ => C * q ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul C
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have := hbound n (a • b + a' • b') _
      (h3 n b b.2 b' b'.2 a a' _ _ (hx n _ b.2) (hx n _ b'.2))
    rwa [UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_mul,
      UniformSpace.Completion.coe_mul] at this)
  refine ⟨L, fun n b hb y hy => ?_⟩
  rw [show L (1 ⊗ₜ[ℤ_[l]] b) = Θ ⟨b, hb⟩ from hL ⟨b, hb⟩]
  exact hbound n ⟨b, hb⟩ y hy

end GlobalTheory
end

section

open scoped NNReal TensorProduct

namespace GlobalTheory.KLC

open IsDedekindDomain

theorem completeSpace_withAbs_of_unitBall (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K]
    [Algebra R K] [IsFractionRing R K] (f : AbsoluteValue K ℝ)
    (h : ∀ x : K, f x ≤ 1 ↔ x ∈ Set.range (algebraMap R K)) :
    CompleteSpace (WithAbs f) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let em : R →+* WithAbs f := (WithAbs.equiv f).symm.toRingHom.comp (algebraMap R K)
  have hnorm : ∀ x : R, ‖em x‖ = f (algebraMap R K x) := fun x => rfl
  have hinj : Function.Injective em := (WithAbs.equiv f).symm.injective.comp hinjK
  have hem0 : em π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  have hpos : 0 < ‖em π‖ := norm_pos_iff.2 hem0
  have hle : ∀ x, ‖em x‖ ≤ 1 := fun x => (h _).2 ⟨x, rfl⟩
  have key : ∀ (n : ℕ) (x : R), x ∈ IsLocalRing.maximalIdeal R ^ n ↔ ‖em x‖ ≤ ‖em π‖ ^ n := by
    intro n x
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩
      rw [map_mul, map_pow, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hle y)
    · intro hx
      rw [hnorm, hnorm] at hx
      have hπK : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ hinjK).2 hπ.ne_zero
      obtain ⟨y, hy⟩ := (h (algebraMap R K x / algebraMap R K π ^ n)).1 (by
        rw [map_div₀, map_pow]
        exact div_le_one_of_le₀ hx (by positivity))
      refine ⟨y, hinjK ?_⟩
      rw [map_mul, map_pow, hy, mul_div_cancel₀ _ (pow_ne_zero _ hπK)]
  have hlt : ‖em π‖ < 1 := by
    by_contra hge
    have : (1 : R) ∈ IsLocalRing.maximalIdeal R ^ 1 := (key 1 1).2 (by simpa using hge)
    rw [pow_one] at this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine Metric.complete_of_convergent_controlled_sequences (fun n => ‖em π‖ ^ n)
    (fun n => by positivity) ?_
  intro u hu
  have hv : ∀ n, ∃ v : R, em v = u n - u 0 := by
    intro n
    obtain ⟨v, hv⟩ := (h ((u n - u 0).ofAbs)).1 (by
      have := hu 0 n 0 (Nat.zero_le _) le_rfl
      rw [dist_eq_norm, pow_zero, WithAbs.norm_eq_apply_ofAbs] at this
      exact this.le)
    refine ⟨v, ?_⟩
    show WithAbs.toAbs f (algebraMap R K v) = _
    rw [hv, WithAbs.toAbs_ofAbs]
  choose v hv using hv
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal R) (M := R) inferInstance
    (f := v) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, key, map_sub, hv, hv,
        sub_sub_sub_cancel_right]
      have := hu m m n le_rfl hmn
      rw [dist_eq_norm] at this
      exact this.le)
  refine ⟨em L + u 0, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt)
  have := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, key, map_sub, hv] at this
  rw [dist_eq_norm]
  have e : u n - (em L + u 0) = u n - u 0 - em L := by abel
  rw [e]
  exact this

theorem exists_absoluteValue_completeSpace_of_isDiscreteValuationRing :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K] [Algebra R K]
      [IsFractionRing R K], ∃ f : AbsoluteValue K ℝ, IsNonarchimedean f ∧ f.IsNontrivial ∧
      (∀ x : K, f x ≤ 1 ↔ x ∈ Set.range (algebraMap R K)) ∧ CompleteSpace (WithAbs f) := by
  intro R K _ _ _ _ _ _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let v := IsDiscreteValuationRing.maximalIdeal R
  have hb : (1 : ℝ≥0) < 2 := one_lt_two
  have hball : ∀ x : K, v.adicAbv hb x ≤ 1 ↔ x ∈ Set.range (algebraMap R K) := by
    intro x
    have : v.adicAbv hb x ≤ 1 ↔ v.valuation K x ≤ 1 := by
      rw [← WithZeroMulInt.toNNReal_le_one_iff hb, ← NNReal.coe_le_coe]
      rfl
    rw [this]
    exact ⟨IsDiscreteValuationRing.exists_lift_of_le_one,
      fun ⟨y, hy⟩ => hy ▸ v.valuation_le_one y⟩
  refine ⟨v.adicAbv hb, v.isNonarchimedean_adicAbv hb, ?_, hball,
    completeSpace_withAbs_of_unitBall R K _ hball⟩
  have hπK : algebraMap R K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
  have h1 : v.valuation K (algebraMap R K π) < 1 :=
    (v.valuation_lt_one_iff_mem π).2
      (show π ∈ IsLocalRing.maximalIdeal R from (IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)
  have h2 : WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (v.valuation K (algebraMap R K π)) < 1 := by
    have := WithZeroMulInt.toNNReal_strictMono hb h1
    rwa [map_one] at this
  refine ⟨algebraMap R K π, hπK, ?_⟩
  intro heq
  have : ((WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (v.valuation K (algebraMap R K π)) : ℝ≥0) : ℝ)
      = 1 := heq
  exact absurd (NNReal.coe_lt_coe.2 h2) (by rw [this]; simp)

end GlobalTheory.KLC
end

section

open scoped NNReal TensorProduct

namespace GlobalTheory

open Polynomial

theorem exists_spectralValuation (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (f : AbsoluteValue K ℝ) (hna : IsNonarchimedean f) (hnt : f.IsNontrivial)
    (hc : CompleteSpace (WithAbs f)) :
    ∃ v : Valuation Ω ℝ≥0, (∀ x : K, (v (algebraMap K Ω x) : ℝ) = f x) ∧
      ∀ x : Ω, v x ≤ 1 ↔ ∀ i, f ((minpoly K x).coeff i) ≤ 1 := by
  obtain ⟨a, ha⟩ := hnt.exists_abv_gt_one
  letI : NontriviallyNormedField (WithAbs f) :=
    NontriviallyNormedField.ofNormNeOne ⟨WithAbs.toAbs f a, by
      intro h; rw [WithAbs.toAbs_eq_zero] at h; rw [h, map_zero] at ha; linarith, by
      rw [WithAbs.norm_toAbs_eq]; exact ha.ne'⟩
  haveI : IsUltrametricDist (WithAbs f) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y => hna x.ofAbs y.ofAbs
  haveI : IsScalarTower K (WithAbs f) Ω := inferInstance
  haveI : Algebra.IsAlgebraic (WithAbs f) Ω := Algebra.IsAlgebraic.tower_top (K := K) (WithAbs f)
  have hmin : ∀ x : Ω, minpoly (WithAbs f) x = (minpoly K x).map (algebraMap K (WithAbs f)) := by
    intro x
    have hx : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    have hmap : (minpoly K x).map (algebraMap K (WithAbs f)) =
        Polynomial.mapEquiv (WithAbs.equiv f).symm (minpoly K x) := by
      rw [Polynomial.mapEquiv_apply]; rfl
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · rw [hmap]; exact (MulEquiv.irreducible_iff _).mpr (minpoly.irreducible hx)
    · rw [Polynomial.aeval_map_algebraMap]; exact minpoly.aeval K x
    · exact (minpoly.monic hx).map _
  let v : Valuation Ω ℝ≥0 :=
    { toFun := fun x => ⟨spectralNorm (WithAbs f) Ω x, spectralNorm_nonneg x⟩
      map_zero' := by ext; exact spectralNorm_zero
      map_one' := by ext; exact spectralNorm_one
      map_mul' := fun x y => by
        ext; exact spectralAlgNorm_mul (K := WithAbs f) (L := Ω) x y
      map_add_le_max' := fun x y => by
        show spectralNorm (WithAbs f) Ω (x + y) ≤ max (spectralNorm (WithAbs f) Ω x) (spectralNorm (WithAbs f) Ω y)
        exact isNonarchimedean_spectralNorm x y }
  have hv : ∀ x : Ω, (v x : ℝ) = spectralNorm (WithAbs f) Ω x := fun _ => rfl
  refine ⟨v, fun x => ?_, fun x => ?_⟩
  · rw [hv]
    have : algebraMap K Ω x = algebraMap (WithAbs f) Ω (WithAbs.toAbs f x) := rfl
    rw [this, spectralNorm_extends, WithAbs.norm_toAbs_eq]
  · have hx : IsIntegral (WithAbs f) x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    rw [← NNReal.coe_le_coe, NNReal.coe_one, hv]
    show spectralValue (minpoly (WithAbs f) x) ≤ 1 ↔ _
    rw [spectralValue_le_one_iff (minpoly.monic hx), hmin x]
    refine forall_congr' fun i => ?_
    rw [Polynomial.coeff_map, WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq]
    rfl

end GlobalTheory
end

section

open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem matrix_inv_entries_bounded (R : Type) [NormedCommRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R] (n : ℕ) (G : Matrix (Fin n) (Fin n) R → ℝ) (hG : Continuous G) (hU : ∀ c, G c ≠ 0 → IsUnit c) (B ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, (∀ c : Matrix (Fin n) (Fin n) R, (∀ i j, ‖c i j‖ ≤ B) → G c ≤ C) ∧ ∀ c : GL (Fin n) R, (∀ i j, ‖c.1 i j‖ ≤ B) → ε ≤ G c.1 → ∀ i j, ‖c⁻¹.1 i j‖ ≤ C := by
  haveI : ProperSpace R := FiniteDimensional.proper_real R
  haveI : CompleteSpace R := FiniteDimensional.complete ℝ R
  set K : Set (Matrix (Fin n) (Fin n) R) := Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Metric.closedBall (0 : R) B)) with hK
  have hKc : IsCompact K := isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  have hmemK : ∀ c : Matrix (Fin n) (Fin n) R, (∀ i j, ‖c i j‖ ≤ B) → c ∈ K := by
    intro c h i _ j _
    simpa [Metric.mem_closedBall, dist_zero_right] using h i j
  obtain ⟨C1, hC1⟩ := hKc.exists_bound_of_continuousOn hG.continuousOn
  set K' := K ∩ {c | ε ≤ G c} with hK'
  have hK'c : IsCompact K' := hKc.inter_right (isClosed_le continuous_const hG)
  let f : Matrix (Fin n) (Fin n) R → (Fin n → Fin n → R) := fun c => fun i j => (c⁻¹) i j
  have hf : ContinuousOn f K' := by
    intro c hc
    have hu : IsUnit c := hU c (ne_of_gt (lt_of_lt_of_le hε hc.2))
    have hdet : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hu
    obtain ⟨u, hu'⟩ := hdet
    have h1 : ContinuousAt Ring.inverse c.det := by
      rw [← hu']; exact NormedRing.inverse_continuousAt u
    exact (continuousAt_matrix_inv c h1).continuousWithinAt
  obtain ⟨C2, hC2⟩ := hK'c.exists_bound_of_continuousOn hf
  refine ⟨max C1 C2, ?_, ?_⟩
  · intro c hc
    exact le_trans (le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC1 c (hmemK c hc))) (le_max_left _ _)
  · intro c hc hGc i j
    have hm : c.1 ∈ K' := ⟨hmemK _ hc, hGc⟩
    have h2 := hC2 _ hm
    have h3 : ‖f c.1 i j‖ ≤ ‖f c.1‖ := le_trans (norm_le_pi_norm (f c.1 i) j) (norm_le_pi_norm (f c.1) i)
    rw [Matrix.coe_units_inv]
    exact le_trans (le_trans h3 h2) (le_max_right _ _)

end GlobalTheory
end
