module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

section

open Filter Topology

namespace GlobalTheory.CompanionTheory.SimpleRoot

theorem exists_analytic_simple_root
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (n : ℕ)
    (c : ℕ → E → ℂ) (w₀ : E) (τ₀ : ℂ) (hc : ∀ j, AnalyticAt ℂ (c j) w₀)
    (h0 : ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j = 0)
    (h1 : ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) ≠ 0) :
    ∃ (V : Set E) (W : Set ℂ) (g : E → ℂ), IsOpen V ∧ w₀ ∈ V ∧ IsOpen W ∧ τ₀ ∈ W ∧
      AnalyticOnNhd ℂ g V ∧ ∀ w ∈ V, ∀ τ ∈ W,
        ∑ j ∈ Finset.range (n + 1), c j w * τ ^ j = 0 → τ = g w := by
  set F : E × ℂ → ℂ := fun p => ∑ j ∈ Finset.range (n + 1), c j p.1 * p.2 ^ j with hFdef
  have hFa : AnalyticAt ℂ F (w₀, τ₀) := by
    refine Finset.analyticAt_fun_sum _ fun j _ => ?_
    exact ((hc j).comp analyticAt_fst).mul (analyticAt_snd.pow j)
  have cdf : ContDiffAt ℂ (⊤ : WithTop ℕ∞) F (w₀, τ₀) := hFa.contDiffAt
  have pn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  set d : ℂ := ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) with hd_def
  have hd : HasDerivAt (fun τ => F (w₀, τ)) d τ₀ :=
    HasDerivAt.fun_sum (u := Finset.range (n + 1)) (A := fun j τ => c j w₀ * τ ^ j)
      (A' := fun j => (j : ℂ) * c j w₀ * τ₀ ^ (j - 1)) fun j _ => by
        rw [show (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) = c j w₀ * ((j : ℂ) * τ₀ ^ (j - 1)) by ring]
        exact (hasDerivAt_pow j τ₀).const_mul (c j w₀)
  have hfd : HasFDerivAt (fun τ => F (w₀, τ))
      ((fderiv ℂ F (w₀, τ₀)).comp (ContinuousLinearMap.inr ℂ E ℂ)) τ₀ :=
    hFa.differentiableAt.hasFDerivAt.comp τ₀ (hasFDerivAt_prodMk_right w₀ τ₀)
  have heq : (fderiv ℂ F (w₀, τ₀)).comp (ContinuousLinearMap.inr ℂ E ℂ) =
      ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d :=
    hfd.unique hd.hasFDerivAt
  have if₂ : ((fderiv ℂ F (w₀, τ₀)).comp (ContinuousLinearMap.inr ℂ E ℂ)).IsInvertible := by
    rw [heq]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 d h1), ?_⟩
    ext
    simp
  set g := cdf.implicitFunction pn if₂ with hg_def
  have hg : AnalyticAt ℂ g w₀ := (cdf.contDiffAt_implicitFunction pn if₂).analyticAt
  obtain ⟨V₂, W, hV₂o, hw₀V₂, hWo, hτ₀W, hsub⟩ :=
    mem_nhds_prod_iff'.1 (cdf.eventually_apply_eq_iff_implicitFunction pn if₂)
  refine ⟨{w | AnalyticAt ℂ g w} ∩ V₂, W, g, (isOpen_analyticAt ℂ g).inter hV₂o, ⟨hg, hw₀V₂⟩, hWo, hτ₀W,
    fun w hw => hw.1, ?_⟩
  intro w hw τ hτ hroot
  have hmem := hsub (Set.mk_mem_prod hw.2 hτ)
  simp only [Set.mem_ofPred_eq] at hmem
  have h' : F (w, τ) = F (w₀, τ₀) := by
    change (∑ j ∈ Finset.range (n + 1), c j w * τ ^ j) = ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j
    rw [hroot, h0]
  exact (hmem.1 h').symm

end GlobalTheory.CompanionTheory.SimpleRoot
end

section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Kaehler

theorem derivation_mem_span {S B M : Type} [CommRing S] [Algebra ℚ S] [CommRing B]
    [AddCommGroup M] [Module B M] (ψ : S →+* B) (D₀ : S →+ M)
    (leib : ∀ a b, D₀ (a * b) = ψ a • D₀ b + ψ b • D₀ a)
    {n : ℕ} (z : Fin n → S)
    (hz : Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤) (s : S) :
    D₀ s ∈ Submodule.span B (Set.range fun i => D₀ (z i)) := by
  let _ : Module S M := Module.compHom M ψ
  let _ : Module ℚ M := Module.compHom M (algebraMap ℚ S)
  have : IsScalarTower ℚ S M := ⟨fun q a x => by
    change ψ (q • a) • x = ψ (algebraMap ℚ S q) • (ψ a • x)
    rw [Algebra.smul_def, map_mul, mul_smul]⟩
  have hsm : ∀ (a : S) (x : M), a • x = ψ a • x := fun _ _ => rfl
  let D : Derivation ℚ S M := Derivation.mk' D₀.toRatLinearMap (fun a b => by
    simpa [hsm] using leib a b)
  have hD : ∀ a, D a = D₀ a := fun _ => rfl
  let L := D.liftKaehlerDifferential
  have hL : ∀ a, L (KaehlerDifferential.D ℚ S a) = D₀ a := fun a => by
    simp [L, hD]
  have key : ∀ x : Ω[S⁄ℚ], L x ∈ Submodule.span B (Set.range fun i => D₀ (z i)) := by
    intro x
    have hx : x ∈ Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) := by
      rw [hz]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [hL]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add y w _ _ hy hw => rw [map_add]; exact add_mem hy hw
    | smul a y _ hy =>
      rw [map_smul, hsm]
      exact Submodule.smul_mem _ _ hy
  simpa [hL] using key (KaehlerDifferential.D ℚ S s)

theorem maximalIdeal_eq_span_of_span_D :
    ∀ (S B : Type) [CommRing S] [Algebra ℚ S] [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [Algebra ℂ B] (ψ : S →+* B) (φ : S →+* ℂ),
    (∀ s, ψ s - algebraMap ℂ B (φ s) ∈ IsLocalRing.maximalIdeal B) →
    ∀ (T : Set S), IsLocalRing.maximalIdeal B = Ideal.span ((fun s => ψ s - algebraMap ℂ B (φ s)) '' T) →
    ∀ (n : ℕ) (z : Fin n → S),
    Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ →
    IsLocalRing.maximalIdeal B = Ideal.span (Set.range fun i => ψ (z i) - algebraMap ℂ B (φ (z i))) := by
  intro S B _ _ _ _ _ _ ψ φ hmem T hT n z hz
  set m := IsLocalRing.maximalIdeal B with hm
  set f : S → B := fun s => ψ s - algebraMap ℂ B (φ s) with hf
  set J : Ideal B := Ideal.span (Set.range fun i => f (z i)) with hJ
  have hJm : J ≤ m := by
    rw [hJ, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem (z i)
  let D₀ : S →+ m.Cotangent :=
    { toFun := fun s => m.toCotangent ⟨f s, hmem s⟩
      map_zero' := by
        have : (⟨f 0, hmem 0⟩ : m) = 0 := by ext; simp [hf]
        rw [this, map_zero]
      map_add' := fun a b => by
        rw [← map_add (f := _)]
        congr 1
        ext
        simp [hf]
        ring }
  have hD₀ : ∀ s, D₀ s = m.toCotangent ⟨f s, hmem s⟩ := fun _ => rfl
  have leib : ∀ a b, D₀ (a * b) = ψ a • D₀ b + ψ b • D₀ a := by
    intro a b
    rw [hD₀, hD₀, hD₀, ← map_smul, ← map_smul, ← map_add (f := _), Ideal.toCotangent_eq]
    have h2 : f a * f b ∈ m ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul (hmem a) (hmem b)
    have : ((⟨f (a * b), hmem (a * b)⟩ : m) : B)
        - ((ψ a • (⟨f b, hmem b⟩ : m) + ψ b • (⟨f a, hmem a⟩ : m) : m) : B) = -(f a * f b) := by
      simp [hf]
      ring
    rw [this]
    exact (m ^ 2).neg_mem h2
  have hspan : ∀ s, D₀ s ∈ Submodule.span B (Set.range fun i => D₀ (z i)) :=
    derivation_mem_span ψ D₀ leib z hz
  let Q : Submodule B m.Cotangent := Submodule.map m.toCotangent (Submodule.comap m.subtype J)
  have hPQ : Submodule.span B (Set.range fun i => D₀ (z i)) ≤ Q := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨f (z i), hmem (z i)⟩, Ideal.subset_span ⟨i, rfl⟩, rfl⟩
  have hfs : ∀ s, f s ∈ J ⊔ m • m := by
    intro s
    obtain ⟨y, hyJ, hy⟩ := hPQ (hspan s)
    have hy' := (Ideal.toCotangent_eq (I := m)).1 (hy.trans (hD₀ s))
    have hsub : f s = (y : B) - ((y : B) - f s) := by ring
    rw [hsub]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left hyJ) (Submodule.mem_sup_right ?_)
    simpa [pow_two] using hy'
  have hle : m ≤ J ⊔ m • m := by
    conv_lhs => rw [hT]
    rw [Ideal.span_le]
    rintro _ ⟨s, _, rfl⟩
    exact hfs s
  apply le_antisymm _ hJm
  exact Submodule.le_of_le_smul_of_le_jacobson (IsNoetherian.noetherian m)
    (by simpa only [Ideal.jacobson_bot] using
      (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal B))) hle

end GlobalTheory.CompanionTheory.Kaehler
end

section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.CompanionTheory.Ggeo

def ltOneIdeal {R : Type} [CommRing R] [IsDomain R] (μ : R →*₀ ℝ)
    (h0 : ∀ x, 0 ≤ μ x) (h1 : ∀ x, μ x ≤ 1)
    (hadd : ∀ x y, μ (x + y) ≤ max (μ x) (μ y)) : Ideal R where
  carrier := {x | μ x < 1}
  add_mem' := by
    intro x y hx hy
    exact lt_of_le_of_lt (hadd x y) (max_lt hx hy)
  zero_mem' := by
    show μ 0 < 1
    simp
  smul_mem' := by
    intro c x hx
    show μ (c * x) < 1
    rw [map_mul]
    have hx' : μ x < 1 := hx
    nlinarith [h0 c, h0 x, h1 c]

private theorem eq_pow_count_normalizedFactors_of_uniformizer {R : Type} [CommRing R] [IsDedekindDomain R]
    (μ : R →*₀ ℝ) (P : Ideal R) [P.IsPrime] (hone : ∀ x, x ∉ P → μ x = 1)
    (π : R) (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2) (x : R) (hx : x ≠ 0) :
    μ x = μ π ^ (normalizedFactors (Ideal.span {x})).count P := by
  have hspan : ∀ y : R, y ≠ 0 → Ideal.span {y} ≠ 0 := fun y hy => by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hy
  have hadd : ∀ y z : R, y ≠ 0 → z ≠ 0 → (normalizedFactors (Ideal.span {y * z})).count P =
      (normalizedFactors (Ideal.span {y})).count P + (normalizedFactors (Ideal.span {z})).count P := by
    intro y z hy hz
    rw [← Ideal.span_singleton_mul_span_singleton, normalizedFactors_mul (hspan y hy) (hspan z hz),
      Multiset.count_add]
  have hzero : ∀ y : R, y ∉ P → (normalizedFactors (Ideal.span {y})).count P = 0 := by
    intro y hy
    apply Ideal.count_normalizedFactors_eq
    · rw [pow_zero, Ideal.one_eq_top]
      exact le_top
    · rw [zero_add, pow_one, Ideal.span_singleton_le_iff_mem]
      exact hy
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hπ2 (zero_mem _)
  have hπ1 : (normalizedFactors (Ideal.span {π})).count P = 1 := by
    apply Ideal.count_normalizedFactors_eq
    · rw [pow_one, Ideal.span_singleton_le_iff_mem]
      exact hπ
    · rw [Ideal.span_singleton_le_iff_mem]
      exact hπ2
  obtain ⟨A, hA⟩ : P ∣ Ideal.span {π} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem P).2 hπ)
  have hAP : ¬A ≤ P := by
    intro hle
    apply hπ2
    rw [← Ideal.span_singleton_le_iff_mem, hA, pow_two]
    exact Ideal.mul_mono_right hle
  obtain ⟨s, hsA, hsP⟩ := SetLike.not_le_iff_exists.1 hAP
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hsP (zero_mem _)
  have hstep : ∀ y : R, y ∈ P → ∃ z, s * y = π * z := by
    intro y hy
    have : s * y ∈ Ideal.span {π} := by
      rw [hA, mul_comm s y]
      exact Ideal.mul_mem_mul hy hsA
    exact Ideal.mem_span_singleton.1 this
  have hdiv : ∀ y : R, y ≠ 0 → y ∈ P → ∃ z, z ≠ 0 ∧
      (normalizedFactors (Ideal.span {y})).count P =
        (normalizedFactors (Ideal.span {z})).count P + 1 ∧ μ y = μ π * μ z := by
    intro y hy hyP
    obtain ⟨z, hz⟩ := hstep y hyP
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hz
      exact mul_ne_zero hs0 hy hz
    have hc := hadd s y hs0 hy
    rw [hz, hadd π z hπ0 hz0, hπ1, hzero s hsP] at hc
    refine ⟨z, hz0, by omega, ?_⟩
    have hμ : μ s * μ y = μ π * μ z := by rw [← map_mul, ← map_mul, hz]
    rwa [hone s hsP, one_mul] at hμ
  suffices H : ∀ n : ℕ, ∀ y : R, y ≠ 0 → (normalizedFactors (Ideal.span {y})).count P = n →
      μ y = μ π ^ n from H _ x hx rfl
  intro n
  induction n with
  | zero =>
    intro y hy hn
    by_cases hyP : y ∈ P
    · obtain ⟨z, _, hc, _⟩ := hdiv y hy hyP
      omega
    · rw [hone y hyP, pow_zero]
  | succ n ih =>
    intro y hy hn
    by_cases hyP : y ∈ P
    · obtain ⟨z, hz0, hc, hμ⟩ := hdiv y hy hyP
      rw [hμ, ih z hz0 (by omega), pow_succ, mul_comm]
    · rw [hzero y hyP] at hn
      omega

theorem map_eq_pow_count_of_ultrametric :
    ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (μ : R →*₀ ℝ) (a : R), a ≠ 0 →
      (∀ x, 0 ≤ μ x) → (∀ x, μ x ≤ 1) → (∀ x y, μ (x + y) ≤ max (μ x) (μ y)) →
      μ a < 1 → μ a ≠ 0 →
      ∃ (P : Ideal R) (c : ℝ), P.IsPrime ∧ P ≠ ⊥ ∧ a ∈ P ∧ 0 < c ∧
        ∀ x : R, x ≠ 0 → μ x = c ^ (normalizedFactors (Ideal.span {x})).count P := by
  intro R _ _ μ a ha h0 h1 hadd hlt hne
  set P := GlobalTheory.CompanionTheory.Ggeo.ltOneIdeal μ h0 h1 hadd with hPdef
  have hmem : ∀ x, x ∈ P ↔ μ x < 1 := fun x => Iff.rfl
  have hPtop : P ≠ ⊤ := by
    intro htop
    have h1P := (Ideal.eq_top_iff_one P).1 htop
    rw [hmem, map_one] at h1P
    exact lt_irrefl _ h1P
  have hPprime : P.IsPrime := by
    refine ⟨hPtop, ?_⟩
    intro x y hxy
    have hxy' : μ x * μ y < 1 := by
      rw [← map_mul]
      exact (hmem _).1 hxy
    by_contra hc
    rw [not_or] at hc
    have hx1 : ¬μ x < 1 := fun h => hc.1 ((hmem x).2 h)
    have hy1 : ¬μ y < 1 := fun h => hc.2 ((hmem y).2 h)
    rw [not_lt] at hx1 hy1
    nlinarith [h0 x, h0 y]
  haveI := hPprime
  have haP : a ∈ P := (hmem a).2 hlt
  have hbot : P ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at haP
    exact ha haP
  obtain ⟨π, hπ, hπ2⟩ : ∃ π ∈ P ^ 1, π ∉ P ^ 2 := SetLike.exists_of_lt
    (Ideal.pow_right_strictAnti P hbot hPtop (by norm_num : 1 < 2))
  rw [pow_one] at hπ
  have hone : ∀ x, x ∉ P → μ x = 1 := fun x hx =>
    le_antisymm (h1 x) (not_lt.1 fun h => hx ((hmem x).2 h))
  have hkey := eq_pow_count_normalizedFactors_of_uniformizer μ P hone π hπ hπ2
  have hπne : μ π ≠ 0 := by
    intro h
    have ha' := hkey a ha
    rw [h] at ha'
    rcases Nat.eq_zero_or_pos ((normalizedFactors (Ideal.span {a})).count P) with hk | hk
    · rw [hk, pow_zero] at ha'
      rw [ha'] at hlt
      exact lt_irrefl _ hlt
    · rw [zero_pow hk.ne'] at ha'
      exact hne ha'
  exact ⟨P, μ π, hPprime, hbot, haP, lt_of_le_of_ne (h0 π) (Ne.symm hπne), hkey⟩

end GlobalTheory.CompanionTheory.Ggeo
end

section

namespace GlobalTheory.CompanionTheory.FieldGen

theorem isAlgebraic_adjoin_range_self {k E σ : Type} [Field k] [Field E] [Algebra k E] (y : σ → E) :
    Algebra.IsAlgebraic
      (Algebra.adjoin k (Set.range fun j =>
        (⟨y j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩ :
          IntermediateField.adjoin k (Set.range y))))
      (IntermediateField.adjoin k (Set.range y)) := by
  set E' := IntermediateField.adjoin k (Set.range y) with hE'
  set y' : σ → E' := fun j => ⟨y j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩ with hy'
  set A := Algebra.adjoin k (Set.range y') with hA
  have hmap : ∀ p ∈ Algebra.adjoin k (Set.range y), ∃ p' ∈ A, (p' : E) = p := by
    intro p hp
    have h1 : Algebra.adjoin k (Set.range y) = A.map (IntermediateField.val E') := by
      rw [hA, AlgHom.map_adjoin, ← Set.range_comp]
      rfl
    rw [h1] at hp
    obtain ⟨p', hp', rfl⟩ := Subalgebra.mem_map.1 hp
    exact ⟨p', hp', rfl⟩
  constructor
  intro z
  obtain ⟨v, hv⟩ := z
  obtain ⟨p, hp, q, hq, hpq⟩ := IntermediateField.mem_adjoin_iff_div.1 hv
  by_cases hq0 : q = 0
  · have hz : (⟨v, hv⟩ : E') = 0 := by
      apply Subtype.ext
      simp [hpq, hq0]
    rw [hz]
    exact isAlgebraic_zero
  obtain ⟨p', hp', hpp⟩ := hmap p hp
  obtain ⟨q', hq', hqq⟩ := hmap q hq
  have hq'0 : q' ≠ 0 := by
    rintro rfl
    exact hq0 (by rw [← hqq]; rfl)
  refine ⟨Polynomial.C (⟨q', hq'⟩ : A) * Polynomial.X - Polynomial.C ⟨p', hp'⟩, ?_, ?_⟩
  · intro h
    have h2 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 1) h
    simp at h2
    exact hq'0 (congrArg Subtype.val h2 :)
  · rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X, sub_eq_zero]
    change q' * (⟨v, hv⟩ : E') = p'
    apply Subtype.ext
    show (q' : E) * v = p'
    rw [hpp, hqq, hpq]
    field_simp

theorem algebraicIndependent_of_adjoin_eq :
    ∀ (K L J : Type) [Field K] [Field L] [Algebra K L] [Finite J] (x y : J → L),
      AlgebraicIndependent K x →
      IntermediateField.adjoin K (Set.range x) = IntermediateField.adjoin K (Set.range y) →
      AlgebraicIndependent K y := by
  intro K L J _ _ _ _ x y hx hxy
  set E := IntermediateField.adjoin K (Set.range y) with hE
  have hal := isAlgebraic_adjoin_range_self (k := K) y
  set y' : J → E := fun j => ⟨y j, IntermediateField.subset_adjoin K _ ⟨j, rfl⟩⟩ with hy'
  have hxmem : ∀ j, x j ∈ E := fun j => by
    rw [← hxy]
    exact IntermediateField.subset_adjoin K _ ⟨j, rfl⟩
  set x' : J → E := fun j => ⟨x j, hxmem j⟩ with hxd
  have hx' : AlgebraicIndependent K x' := AlgebraicIndependent.of_comp E.val hx
  have hle : Cardinal.mk J ≤ Algebra.trdeg K E := hx'.cardinalMk_le_trdeg
  have htb := Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite K y' hle
  exact htb.1.map' (f := E.val) E.val.injective

end GlobalTheory.CompanionTheory.FieldGen
end

section

namespace GlobalTheory.CompanionTheory.Exterior

theorem ιMulti_ne_zero_of_linearIndependent :
    ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (e : Fin n → V),
      LinearIndependent Ω e → exteriorPower.ιMulti Ω n e ≠ 0 := by
  intro Ω V _ _ _ n e he h
  let f : (Fin n → Ω) →ₗ[Ω] V := Fintype.linearCombination Ω e
  have hf : LinearMap.ker f = ⊥ :=
    LinearMap.ker_eq_bot.2 he.fintypeLinearCombination_injective
  obtain ⟨π, hπ⟩ := f.exists_leftInverse_of_injective hf
  have hπe : ∀ j, π (e j) = Pi.single j 1 := by
    intro j
    have h2 := LinearMap.congr_fun hπ (Pi.single j 1)
    simpa [f, Fintype.linearCombination_apply_single] using h2
  let D : V [⋀^Fin n]→ₗ[Ω] Ω :=
    (Matrix.detRowAlternating (n := Fin n) (R := Ω)).compLinearMap π
  have h1 := exteriorPower.alternatingMapLinearEquiv_apply_ιMulti D e
  rw [h, map_zero] at h1
  have h3 : D e = 1 := by
    have h4 : (fun i => π (e i)) = (1 : Matrix (Fin n) (Fin n) Ω) := by
      ext i j
      simp [hπe, Matrix.one_apply, Pi.single_apply, eq_comm]
    change Matrix.det (fun i => π (e i)) = 1
    rw [h4, Matrix.det_one]
  rw [h3] at h1
  exact zero_ne_one h1

end GlobalTheory.CompanionTheory.Exterior
end
