module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Filtration
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dual.Basis

@[expose] public section

section

namespace GlobalTheory.EqZeroOfMemMaximalPow

theorem eq_zero_of_mem_pow_maximal {R : Type} [CommRing R] [IsNoetherianRing R] (y : R)
    (h : ∀ i : MaximalSpectrum R × ℕ, y ∈ i.1.asIdeal ^ (i.2 + 1)) : y = 0 := by
  by_contra hy
  have hJ : LinearMap.ker (LinearMap.toSpanSingleton R R y) ≠ ⊤ := by
    intro htop
    have h1 : (1 : R) ∈ LinearMap.ker (LinearMap.toSpanSingleton R R y) := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, one_smul] at h1
    exact hy h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hJ
  have hmem : y ∈ (⨅ i : ℕ, m ^ i • ⊤ : Submodule R R) := by
    rw [Submodule.mem_iInf]
    intro i
    rcases i with _ | i
    · simp
    · have hi := h (⟨m, hm⟩, i)
      simpa [smul_eq_mul, Ideal.mul_top] using hi
  obtain ⟨⟨r, hr⟩, hry⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff m y).mp hmem
  have hJr : (1 - r) ∈ LinearMap.ker (LinearMap.toSpanSingleton R R y) := by
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, sub_smul, one_smul]
    exact sub_eq_zero.mpr hry.symm
  have h1 : (1 : R) ∈ m := by simpa using m.add_mem (hle hJr) hr
  exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end GlobalTheory.EqZeroOfMemMaximalPow
end

section

namespace GlobalTheory.IntegerShiftSingle

universe u_1 u_2 u_3

theorem shift_single_int {ι : Type u_1} {R : Type u_2} {E : Type u_3} [DecidableEq ι] [Ring R]
    {F : (ι → R) → E} (h : ∀ (i : ι) (x : ι → R), F (x + Pi.single i (1 : R)) = F x)
    (i : ι) (k : ℤ) : ∀ x : ι → R, F (x + Pi.single i ((k : ℤ) : R)) = F x := by
  induction k using Int.induction_on with
  | zero => intro x; simp
  | succ m ih =>
    intro x
    have : x + Pi.single i (((m : ℤ) + 1 : ℤ) : R) = (x + Pi.single i ((m : ℤ) : R)) + Pi.single i (1 : R) := by
      rw [Int.cast_add, Int.cast_one, Pi.single_add, add_assoc]
    rw [this, h, ih]
  | pred m ih =>
    intro x
    have : x + Pi.single i ((-(m : ℤ) : ℤ) : R) = (x + Pi.single i ((-(m : ℤ) - 1 : ℤ) : R)) + Pi.single i (1 : R) := by
      rw [add_assoc, ← Pi.single_add]
      congr 2
      push_cast
      first | rfl | ring | abel | simp
    rw [← ih x, this, h]

theorem main {ι : Type u_1} {R : Type u_2} {E : Type u_3} [Fintype ι] [inst : DecidableEq ι] [inst_1 : Ring R]
    {F : (ι → R) → E} : (∀ (i : ι) (x : ι → R), F (x + Pi.single i (1 : R)) = F x) →
    ∀ (n : ι → ℤ) (x : ι → R), F (x + fun (i : ι) ↦ (↑(n i) : R)) = F x := by
  intro h n x
  have key : ∀ s : Finset ι, ∀ y : ι → R, F (y + ∑ i ∈ s, Pi.single i ((n i : ℤ) : R)) = F y := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      intro y
      rw [Finset.sum_insert ha, ← add_assoc, ih, shift_single_int h]
  have hsum : (fun i : ι => ((n i : ℤ) : R)) = ∑ i ∈ Finset.univ, Pi.single i ((n i : ℤ) : R) := by
    rw [Finset.univ_sum_single]
  rw [hsum]
  exact key Finset.univ x

end GlobalTheory.IntegerShiftSingle
end

section

universe u_1 u_2

namespace GlobalTheory.CommonDenominatorForFinset

theorem exists_common_denominator {R : Type u_1} {A : Type u_2} [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Module.Finite R A] (a : A)
    (h : ∀ b : A, ∃ s : R, s ≠ 0 ∧ ∃ r : Polynomial R,
      algebraMap R A s * b = Polynomial.aeval a r) :
    ∃ s : R, s ≠ 0 ∧ ∀ b : A, ∃ r : Polynomial R,
      algebraMap R A s * b = Polynomial.aeval a r := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := A)
  choose f hf0 r hr using h
  refine ⟨∏ b ∈ S, f b, Finset.prod_ne_zero_iff.mpr fun b _ => hf0 b, ?_⟩

  let N : Submodule R A :=
    { carrier := {b | ∃ p : Polynomial R, algebraMap R A (∏ b ∈ S, f b) * b = Polynomial.aeval a p}
      add_mem' := by
        rintro x y ⟨p, hp⟩ ⟨q, hq⟩
        exact ⟨p + q, by rw [mul_add, hp, hq, map_add (f := _)]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨p, hp⟩
        refine ⟨Polynomial.C c * p, ?_⟩
        rw [map_mul, Polynomial.aeval_C, ← hp, Algebra.smul_def]
        ring }

  have hgen : (S : Set A) ⊆ N := by
    intro b hb
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem f hb
    refine ⟨Polynomial.C t * r b, ?_⟩
    rw [map_mul, Polynomial.aeval_C, ← hr b, ht, map_mul]
    ring
  have htop : (⊤ : Submodule R A) ≤ N := by
    rw [← hS, Submodule.span_le]
    exact hgen
  intro b
  exact htop Submodule.mem_top

end GlobalTheory.CommonDenominatorForFinset
end

section

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

private lemma eq_zero_of_cube_bound_of_doubling {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (F : E → ℂ) (ε C : ℝ)
    (hP : ∀ w : E, ‖w‖ < ε → ‖F w‖ ≤ C * ‖w‖ ^ 3 ∧ F ((2 : ℂ) • w) = 3 * F w + F (-w))
    (z : E) (hz : ‖z‖ < ε) : F z = 0 := by

  set M : E → ℝ := fun w => ‖F w‖ + ‖F (-w)‖ with hM
  have step : ∀ w : E, ‖w‖ < ε → M ((2 : ℂ) • w) ≤ 4 * M w := by
    intro w hw
    have h1 := (hP w hw).2
    have h2 := (hP (-w) (by rwa [norm_neg])).2
    rw [neg_neg] at h2
    simp only [hM]
    rw [← smul_neg, h1, h2]
    have e1 : ‖3 * F w + F (-w)‖ ≤ 3 * ‖F w‖ + ‖F (-w)‖ :=
      (norm_add_le _ _).trans (by simp)
    have e2 : ‖3 * F (-w) + F w‖ ≤ 3 * ‖F (-w)‖ + ‖F w‖ :=
      (norm_add_le _ _).trans (by simp)
    linarith
  set w : ℕ → E := fun n => ((2 : ℂ)⁻¹) ^ n • z with hw
  have hnorm : ∀ n, ‖w n‖ = ((2 : ℝ) ^ n)⁻¹ * ‖z‖ := by
    intro n
    simp [hw, norm_smul]
  have hsmall : ∀ n, ‖w n‖ < ε := by
    intro n
    rw [hnorm]
    have h1 : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    calc ((2 : ℝ) ^ n)⁻¹ * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < ε := by simpa using hz
  have hsucc : ∀ n, w n = (2 : ℂ) • w (n + 1) := by
    intro n
    simp only [hw, smul_smul]
    congr 1
    rw [pow_succ]
    field_simp
  have hiter : ∀ n : ℕ, M z ≤ 4 ^ n * M (w n) := by
    intro n
    induction n with
    | zero => simp [hw]
    | succ n ih =>
      calc M z ≤ 4 ^ n * M (w n) := ih
        _ = 4 ^ n * M ((2 : ℂ) • w (n + 1)) := by rw [← hsucc]
        _ ≤ 4 ^ n * (4 * M (w (n + 1))) := by
          gcongr
          exact step _ (hsmall _)
        _ = 4 ^ (n + 1) * M (w (n + 1)) := by ring
  have hbound : ∀ n : ℕ, M z ≤ (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n := by
    intro n
    have hb : M (w n) ≤ 2 * C * ‖w n‖ ^ 3 := by
      have a1 := (hP (w n) (hsmall n)).1
      have a2 := (hP (-w n) (by rw [norm_neg]; exact hsmall n)).1
      rw [norm_neg] at a2
      simp only [hM]
      linarith
    have h4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    calc M z ≤ 4 ^ n * M (w n) := hiter n
      _ ≤ 4 ^ n * (2 * C * ‖w n‖ ^ 3) := by gcongr
      _ = (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n := by
        have h2 : ((1 : ℝ) / 2) ^ n * 2 ^ n = 1 := by
          rw [← mul_pow]
          norm_num
        rw [hnorm, h4]
        field_simp
        linear_combination (-(C * ‖z‖ ^ 3)) * h2
  have hlim : Filter.Tendsto (fun n : ℕ => (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n)
      Filter.atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (2 * C * ‖z‖ ^ 3)
    simpa using this
  have hM0 : M z ≤ 0 := ge_of_tendsto' hlim hbound
  have : ‖F z‖ ≤ 0 := by
    have := norm_nonneg (F (-z))
    simp only [hM] at hM0
    linarith
  exact norm_le_zero_iff.1 this

theorem eventually_eq_zero_of_isBigO_cube_of_doubling :
    (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : E → ℂ),
      F =O[𝓝 0] (fun z => ‖z‖ ^ 3) →
      (∀ᶠ z in 𝓝 0, F ((2 : ℂ) • z) = 3 * F z + F (-z)) → ∀ᶠ z in 𝓝 0, F z = 0) := by
  intro E _ _ F hO hrel
  obtain ⟨C, hC⟩ := hO.bound
  have hev : ∀ᶠ z in 𝓝 (0 : E), ‖F z‖ ≤ C * ‖z‖ ^ 3 ∧ F ((2 : ℂ) • z) = 3 * F z + F (-z) := by
    filter_upwards [hC, hrel] with z h1 h2
    exact ⟨by simpa using h1, h2⟩
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 hev
  filter_upwards [Metric.ball_mem_nhds (0 : E) hε] with z hz
  exact eq_zero_of_cube_bound_of_doubling F ε C (fun w hw => hP (by simpa using hw)) z
    (by simpa using hz)

end GlobalTheory
end

section

open Matrix Polynomial
open scoped BigOperators

namespace GlobalTheory

theorem neg_one_zpow_form_apply_semicharacter :
    (∀ (X : Type) [AddCommGroup X] (E : LinearMap.BilinForm ℤ X) (w w' : X →ₗ[ℤ] X), (∀ x, E x x = 0) → w + w' = LinearMap.id → (∀ x y, E (w x) y = E x (w' y)) → ∀ x y, (-1 : ℂ) ^ E (x + y) (w (x + y)) = (-1) ^ E x (w x) * (-1) ^ E y (w y) * (-1) ^ E x y) := by
  intro X _ E w w' halt hsum hadj x y
  have hskew : ∀ a b, E a b = - E b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add (f := _), LinearMap.add_apply, halt] at h
    linarith
  have hy : w y + w' y = y := by
    have := LinearMap.congr_fun hsum y
    simpa using this
  have h1 : E x (w y) + E x (w' y) = E x y := by rw [← map_add (f := _), hy]
  have h2 : E y (w x) = - E x (w' y) := by rw [hskew, hadj]
  have h3 : E (x + y) (w (x + y))
      = E x (w x) + E y (w y) + E x y + 2 * (E x (w y) - E x y) := by
    simp only [map_add (f := _), LinearMap.add_apply]
    linarith
  have hne : (-1 : ℂ) ≠ 0 := by norm_num
  rw [h3, zpow_add₀ hne, zpow_add₀ hne, zpow_add₀ hne, _root_.zpow_mul]
  have h4 : (-1 : ℂ) ^ (2 : ℤ) = 1 := by norm_num
  rw [h4, _root_.one_zpow, mul_one]

end GlobalTheory
end

section

namespace GlobalTheory.EvaluationSpanTopToricGeometry

theorem span_eval_eq_top {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V] :
    Submodule.span ℂ (Set.range fun x : X => ((LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype))
      = ⊤ := by

  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set v : V := (Module.evalEquiv ℂ V).symm f with hv
  have hfv : Module.evalEquiv ℂ V v = f := by rw [hv, LinearEquiv.apply_symm_apply]
  have hv0 : v = 0 := by
    apply Subtype.ext
    funext x
    have hx : (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype ∈ LinearMap.ker f :=
      hle (Submodule.subset_span ⟨x, rfl⟩)
    rw [LinearMap.mem_ker, ← hfv] at hx
    exact hx
  apply hf0
  rw [← hfv, hv0, map_zero]

theorem exists_sum_mul {X Y : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V]
    (L : Submodule ℂ (Y → ℂ)) (F : X → Y → ℂ) (hV : ∀ y : Y, (fun x : X => F x y) ∈ V)
    (hL : ∀ x : X, F x ∈ L) :
    ∃ (n : ℕ) (h : Fin n → X → ℂ) (k : Fin n → Y → ℂ),
      (∀ i : Fin n, h i ∈ V ∧ k i ∈ L) ∧
        ∀ (x : X) (y : Y), F x y = ∑ i : Fin n, h i x * k i y := by

  let Φ : Module.Dual ℂ V →ₗ[ℂ] (Y → ℂ) :=
    { toFun := fun φ y => φ ⟨fun x => F x y, hV y⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

  have hΦ : ∀ φ, Φ φ ∈ L := by
    have hle : Submodule.span ℂ (Set.range fun x : X => ((LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ V.subtype))
        ≤ L.comap Φ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hL x
    intro φ
    exact hle (by rw [span_eval_eq_top V]; trivial)
  let b := Module.finBasis ℂ V
  refine ⟨Module.finrank ℂ V, fun i => (b i : X → ℂ), fun i => Φ (b.coord i), fun i => ⟨(b i).2, hΦ _⟩, ?_⟩
  intro x y
  have hs := congrArg (fun w : V => (w : X → ℂ) x) (b.sum_repr ⟨fun x' => F x' y, hV y⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
  rw [← hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  rfl

end GlobalTheory.EvaluationSpanTopToricGeometry
end

section

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

theorem bilinForm_bijective_of_nondegenerate_mod (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (E : LinearMap.BilinForm ℤ X)
    (h : ∀ (k : ℕ) (a : X), 0 < k → (∀ b, (k : ℤ) ∣ E a b) → ∃ a', a = (k : ℤ) • a') :
    Function.Bijective E := by
  classical
  set b := Module.Free.chooseBasis ℤ X
  have hinj : Function.Injective E := by
    refine (injective_iff_map_eq_zero E).2 fun a ha => ?_
    refine b.ext_elem fun i => ?_
    obtain ⟨n, hn⟩ : ∃ n, (b.repr a i).natAbs = n := ⟨_, rfl⟩
    obtain ⟨a', ha'⟩ := h (n + 1) a (Nat.succ_pos n) (fun y => by rw [ha]; simp)
    have hdvd : ((n + 1 : ℕ) : ℤ) ∣ b.repr a i := ⟨b.repr a' i, by rw [ha']; simp⟩
    rw [map_zero, Finsupp.zero_apply]
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd ?_
    rw [Int.natAbs_natCast, hn]
    exact Nat.lt_succ_self n
  have hrank : Module.rank ℤ (Module.Dual ℤ X ⧸ LinearMap.range E) = 0 := by
    have h1 := rank_quotient_add_rank_of_isDomain (LinearMap.range E)
    rw [← (LinearEquiv.ofInjective E hinj).rank_eq, ← b.toDualEquiv.rank_eq] at h1
    obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 (Module.rank_lt_aleph0 ℤ X)
    have hq : Module.rank ℤ (Module.Dual ℤ X ⧸ LinearMap.range E) < Cardinal.aleph0 :=
      lt_of_le_of_lt (le_self_add) (h1 ▸ Module.rank_lt_aleph0 ℤ X)
    obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 hq
    rw [hm, hn] at h1
    rw [hm]
    have : m + n = n := by exact_mod_cast h1
    exact_mod_cast (by omega : m = 0)
  refine ⟨hinj, fun f => ?_⟩
  obtain ⟨c, hc0, hcf⟩ := rank_eq_zero_iff.1 hrank (Submodule.Quotient.mk f)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hcf
  obtain ⟨x, hx⟩ := hcf
  have hk : 0 < c.natAbs * c.natAbs := Nat.mul_pos (Int.natAbs_pos.2 hc0) (Int.natAbs_pos.2 hc0)
  obtain ⟨a', ha'⟩ := h (c.natAbs * c.natAbs) (c • x) hk (fun y => by
    rw [Int.natAbs_mul_self, map_smul, hx, smul_smul]
    simp)
  refine ⟨a', ?_⟩
  have hEq : E (c • x) = ((c.natAbs * c.natAbs : ℕ) : ℤ) • f := by
    rw [Int.natAbs_mul_self, map_smul, hx, smul_smul]
  rw [ha', map_smul] at hEq
  ext y
  have hy := LinearMap.congr_fun hEq y
  simp only [LinearMap.smul_apply, smul_eq_mul] at hy
  exact mul_left_cancel₀ (by exact_mod_cast hk.ne') hy

end GlobalTheory
end
