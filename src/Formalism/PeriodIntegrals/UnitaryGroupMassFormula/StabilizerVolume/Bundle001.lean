module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Measure
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

section

noncomputable section

namespace PI.VolStabS

def ffH {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (x y : Fin M → K) : K :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

def ffGram {K : Type} [CommRing K] (σ : K →+* K) {M a : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (X : Fin a → Fin M → K) : Matrix (Fin a) (Fin a) K :=
  fun i j => ffH σ J (X i) (X j)

def IsQuadInv (k K : Type) [Field k] [CommRing K] [Algebra k K] (σ : K ≃ₐ[k] K) : Prop :=
  (∀ x, σ (σ x) = x) ∧
    ((IsField K ∧ Module.finrank k K = 2 ∧ σ ≠ AlgEquiv.refl) ∨
      ∃ e : K ≃ₐ[k] k × k, ∀ x, e (σ x) = (e x).swap)

def FFCount : Prop :=
  ∀ M : ℕ, ∃ C : ℝ, ∀ (k K : Type) [Field k] [Finite k] [CommRing K] [Algebra k K]
    (σ : K ≃ₐ[k] K), IsQuadInv k K σ → (2 : k) ≠ 0 →
    ∀ J : Matrix (Fin M) (Fin M) K, (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∀ a : ℕ, a + 2 ≤ M → ∀ T : Matrix (Fin a) (Fin a) K, (∀ i j, σ (T j i) = T i j) →
    IsUnit T.det →
    |(Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} : ℝ) /
        (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) - 1| ≤ C * ((Nat.card k : ℝ)⁻¹) ^ 2

def FFSplit : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) (k × k), (∀ i j, (J j i).swap = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) (k × k), (∀ i j, (T j i).swap = T i j) → IsUnit T.det →
    (Nat.card {X : Fin a → Fin M → k × k //
        ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J X = T} : ℝ) =
      (∏ i : Fin a, ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) *
        (Nat.card k : ℝ) ^ (a * (M - a))

def FFInert : Prop :=
  ∀ (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K),
    (∀ x, σ (σ x) = x) → Module.finrank k K = 2 → σ ≠ AlgEquiv.refl → (2 : k) ≠ 0 →
    ∀ (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) K, (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) K, (∀ i j, σ (T j i) = T i j) → IsUnit T.det →
    (Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} : ℝ) =
      ∏ j : Fin a, ((Nat.card k : ℝ) ^ (2 * (M - j) - 1) -
        (-1) ^ (M - j) * (Nat.card k : ℝ) ^ (M - j - 1))

end PI.VolStabS
end
end

section

noncomputable section

open NumberField

namespace PI.VolStabS

def ChInf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ χ : AddChar (InfiniteAdeleRing F) ℂ, Continuous χ →
    (∀ a ∈ Λ, χ (algebraMap F (InfiniteAdeleRing F) a) = 1) → ∀ x, χ x = 1

def ChLift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : AddChar (InfiniteAdeleRing F) ℂ), Continuous χ →
    ∃ ℓ : InfiniteAdeleRing F →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = Complex.exp (ℓ x)

def AddIntF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ g : F →+ ℂ, (∀ a ∈ Λ, ∃ n : ℤ, g a = n) → ∀ a, g a = 0

theorem chInf_of (hL : ChLift) (hA : AddIntF) : ChInf := by
  intro F _ _ Λ hne hnot χ hχ hΛ x
  obtain ⟨ℓ, hℓc, hℓ⟩ := hL F χ hχ
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]

  let g : F →+ ℂ := (AddMonoidHom.mulLeft (2 * (Real.pi : ℂ) * Complex.I)⁻¹).comp
    (ℓ.comp (algebraMap F (InfiniteAdeleRing F)).toAddMonoidHom)
  have hgv : ∀ a, g a = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ℓ (algebraMap F _ a) := fun a => rfl
  have hgint : ∀ a ∈ Λ, ∃ n : ℤ, g a = n := by
    intro a ha
    have h1 := hΛ a ha
    rw [hℓ, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    rw [hgv, hn, inv_mul_eq_iff_eq_mul₀ h2, mul_comm]
  have hg0 := hA F Λ hne hnot g hgint
  have hℓ0 : ∀ a : F, ℓ (algebraMap F (InfiniteAdeleRing F) a) = 0 := by
    intro a
    have h3 := hg0 a
    rw [hgv] at h3
    exact (mul_eq_zero.mp h3).resolve_left (inv_ne_zero h2)

  have hfun : (ℓ : InfiniteAdeleRing F → ℂ) = fun _ => 0 :=
    (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hℓc continuous_const
      (funext fun a => hℓ0 a)
  rw [hℓ, congrFun hfun x, Complex.exp_zero]

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS.FFHS

open Module

variable {K : Type} [Field K] {σ : K →+* K}

structure IsSq {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) :
    Prop where
  add_right : ∀ x y z, h x (y + z) = h x y + h x z
  smul_right : ∀ (c : K) x y, h x (c • y) = c * h x y
  herm : ∀ x y, h y x = σ (h x y)

structure IsHS {V : Type} [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V → V → K) : Prop
    extends IsSq σ h where
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0

section basic

variable {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}

def IsSq.lin (hs : IsSq σ h) (x : V) : V →ₗ[K] K where
  toFun := h x
  map_add' := hs.add_right x
  map_smul' c y := by simp [hs.smul_right]

theorem IsSq.lin_apply (hs : IsSq σ h) (x y : V) : hs.lin x y = h x y := rfl

theorem IsSq.add_left (hs : IsSq σ h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hs.herm z (x + y), hs.add_right, map_add (f := _), ← hs.herm z x, ← hs.herm z y]

theorem IsSq.smul_left (hs : IsSq σ h) (c : K) (x y : V) : h (c • x) y = σ c * h x y := by
  rw [hs.herm y (c • x), hs.smul_right, map_mul, ← hs.herm y x]

theorem IsSq.zero_right (hs : IsSq σ h) (x : V) : h x 0 = 0 := by
  simpa using hs.add_right x 0 0

theorem IsSq.zero_left (hs : IsSq σ h) (y : V) : h 0 y = 0 := by
  rw [hs.herm y 0, hs.zero_right, map_zero]

theorem IsSq.sub_right (hs : IsSq σ h) (x y z : V) : h x (y - z) = h x y - h x z :=
  (hs.lin x).map_sub y z

theorem IsSq.self_fixed (hs : IsSq σ h) (x : V) : σ (h x x) = h x x := (hs.herm x x).symm

theorem IsSq.ext_basis {h' : V → V → K} (hs : IsSq σ h) (hs' : IsSq σ h') {ι : Type}
    (b : Basis ι K V) (hb : ∀ i j, h (b i) (b j) = h' (b i) (b j)) (x y : V) : h x y = h' x y := by
  have step1 : ∀ i y, h (b i) y = h' (b i) y := fun i y => by
    have : hs.lin (b i) = hs'.lin (b i) := b.ext (fun j => hb i j)
    exact LinearMap.congr_fun this y
  have step2 : ∀ x, hs.lin x = hs'.lin x := fun x => b.ext (fun i => by
    simp only [IsSq.lin_apply]
    rw [hs.herm (b i) x, hs'.herm (b i) x, step1])
  exact LinearMap.congr_fun (step2 x) y

theorem exists_aniso (h2 : (2 : K) ≠ 0) (hs : IsHS σ h) (x : V) (hx : x ≠ 0) :
    ∃ e, h e e ≠ 0 := by
  have hq := hs.toIsSq
  by_contra H
  push_neg at H
  obtain ⟨y, hy⟩ : ∃ y, h x y ≠ 0 := by
    by_contra H'
    push_neg at H'
    exact hx (hs.nondeg x H')
  have key := H (x + (h x y)⁻¹ • y)
  simp only [hq.add_right, hq.add_left, hq.smul_right, hq.smul_left, H x, H y,
    hq.herm x y] at key
  have e1 : σ (h x y)⁻¹ * σ (h x y) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hy, map_one]
  have e2 : (h x y)⁻¹ * h x y = 1 := inv_mul_cancel₀ hy
  exact h2 (by linear_combination key - e1 - e2)

def perp (hs : IsSq σ h) (e : V) : Submodule K V := LinearMap.ker (hs.lin e)

theorem mem_perp (hs : IsSq σ h) (e w : V) : w ∈ perp hs e ↔ h e w = 0 := LinearMap.mem_ker

theorem perp_isHS (hs : IsHS σ h) (e : V) (he : h e e ≠ 0) :
    IsHS σ (fun w w' : perp hs.toIsSq e => h w w') where
  add_right x y z := hs.add_right x y z
  smul_right c x y := hs.smul_right c x y
  herm x y := hs.herm x y
  nondeg w hw := by
    have hq := hs.toIsSq
    apply Subtype.ext
    apply hs.nondeg
    intro y
    have hm : y - ((h e e)⁻¹ * h e y) • e ∈ perp hq e := by
      have : (h e e)⁻¹ * h e y * h e e = h e y := by
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ he, one_mul]
      rw [mem_perp, hq.sub_right, hq.smul_right, this, sub_self]
    have h1 := hw ⟨_, hm⟩
    have hwe : h w e = 0 := by rw [hq.herm e w, (mem_perp hq e w).1 w.2, map_zero]
    calc h w y = h w (((h e e)⁻¹ * h e y) • e + (y - ((h e e)⁻¹ * h e y) • e)) := by
          rw [add_sub_cancel]
      _ = ((h e e)⁻¹ * h e y) * h w e + h w (y - ((h e e)⁻¹ * h e y) • e) := by
          rw [hq.add_right, hq.smul_right]
      _ = 0 := by rw [hwe, h1]; ring

theorem finrank_perp [FiniteDimensional K V] (hs : IsSq σ h) (e : V) (he : h e e ≠ 0) :
    finrank K (perp hs e) + 1 = finrank K V := by
  have hsurj : Function.Surjective (hs.lin e) := fun c =>
    ⟨(c * (h e e)⁻¹) • e, by rw [IsSq.lin_apply, hs.smul_right, mul_assoc, inv_mul_cancel₀ he,
      mul_one]⟩
  have := LinearMap.finrank_range_add_finrank_ker (hs.lin e)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, finrank_self] at this
  unfold perp
  omega

theorem linIndep_orth (hs : IsSq σ h) {n : ℕ} (f : Fin n → V)
    (h1 : ∀ i j, i ≠ j → h (f i) (f j) = 0) (h2 : ∀ i, h (f i) (f i) ≠ 0) :
    LinearIndependent K f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have := congrArg (hs.lin (f i)) hg

  rw [map_sum, map_zero, Finset.sum_eq_single i] at this
  · rw [map_smul, IsSq.lin_apply, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_right (h2 i)
  · intro j _ hji
    rw [map_smul, IsSq.lin_apply, h1 i j (Ne.symm hji), smul_zero]
  · simp

theorem decomp_val (hs : IsSq σ h) (e w : V) (hw : h e w = 0) (s : K) :
    h (s • e + w) (s • e + w) = σ s * s * h e e + h w w := by
  simp only [hs.add_right, hs.add_left, hs.smul_right, hs.smul_left, hw, hs.herm e w, map_zero]
  ring

end basic

theorem exists_orth (h2 : (2 : K) ≠ 0) : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V → V → K), IsHS σ h → finrank K V = m →
    ∃ f : Fin m → V, (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, h (f i) (f i) ≠ 0 := by
  intro m
  induction m with
  | zero => intro V _ _ _ h _ _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    intro V _ _ _ h hs hm
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hm
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨e, he⟩ := exists_aniso h2 hs x hx
    have hq := hs.toIsSq
    have hfr : finrank K (perp hq e) = m := by have := finrank_perp hq e he; omega
    obtain ⟨g, hg1, hg2⟩ := ih (perp hq e) (fun w w' => h w w') (perp_isHS hs e he) hfr
    refine ⟨Fin.cons e (fun i => (g i : V)), ?_, ?_⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using (mem_perp hq e (g j)).1 (g j).2
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [hq.herm e, (mem_perp hq e (g i)).1 (g i).2, map_zero]
        | succ j =>
          simp only [Fin.cons_succ]
          exact hg1 i j (fun hh => hij (by rw [hh]))
    · intro i
      induction i using Fin.cases with
      | zero => simpa using he
      | succ i => simpa using hg2 i

end PI.VolStabS.FFHS
end
end

section

noncomputable section

namespace PI.VolStabS

open MeasureTheory Set
open scoped ENNReal Pointwise

section Abs

variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]

instance subMeasurableMul (H : Subgroup G) : MeasurableMul H where
  measurable_const_mul c := by
    exact (((measurable_const_mul (c : G)).comp measurable_subtype_coe).subtype_mk :
      Measurable fun x : H => (⟨(c : G) * x, H.mul_mem c.2 x.2⟩ : H))
  measurable_mul_const c := by
    exact (((measurable_mul_const (c : G)).comp measurable_subtype_coe).subtype_mk :
      Measurable fun x : H => (⟨(x : G) * c, H.mul_mem x.2 c.2⟩ : H))

instance subMeasurableInv (H : Subgroup G) : MeasurableInv H where
  measurable_inv := by
    exact ((measurable_inv.comp measurable_subtype_coe).subtype_mk :
      Measurable fun x : H => (⟨(x : G)⁻¹, H.inv_mem x.2⟩ : H))

theorem countable_subgroupOf {Γ H : Subgroup G} [Countable Γ] :
    Countable ((Γ ⊓ H).subgroupOf H) := by
  refine Function.Injective.countable
    (f := fun x : (Γ ⊓ H).subgroupOf H =>
      (⟨((x : H) : G), (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 x.2)).1⟩ : Γ)) ?_
  intro a b hab
  have e : ((a : H) : G) = ((b : H) : G) := congrArg (fun z : Γ => (z : G)) hab
  exact Subtype.ext (Subtype.ext e)

variable [MulAction G Y]

def orbS (Γ : Subgroup G) (y0 : Y) : Set Y := {x | ∃ γ ∈ Γ, γ • y0 = x}

def repO (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : G :=
  Classical.choose (x.2 : ∃ γ ∈ Γ, γ • y0 = (x : Y))

theorem repO_mem (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : repO Γ y0 x ∈ Γ := by
  exact (Classical.choose_spec x.2).1

theorem repO_smul (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : repO Γ y0 x • y0 = x := by
  exact (Classical.choose_spec x.2).2

def cntN (Γ : Subgroup G) (A : Set G) (g : G) : ℝ≥0∞ :=
  ∑' γ : Γ, A.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * g)

def cfun (Γ : Subgroup G) (A : Set G) (y0 : Y) (g : G) : ℝ≥0∞ :=
  ∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹)

theorem meas_cfun (Γ : Subgroup G) (y0 : Y) [Countable (orbS Γ y0)] {A : Set G}
    (hA : MeasurableSet A) : Measurable (cfun Γ A y0) := by
  unfold cfun
  exact Measurable.tsum fun x =>
    (measurable_const.indicator hA).comp ((measurable_const_mul (repO Γ y0 x)).comp measurable_inv)

theorem sum_rep_eq {Γ H : Subgroup G} (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0)
    (u : G → ℝ≥0∞) :
    ∑' x : orbS Γ y0, ∑' δ : (Γ ⊓ H).subgroupOf H, u (repO Γ y0 x * ((δ : H) : G)) =
      ∑' γ : Γ, u γ := by
  classical
  let F : orbS Γ y0 × (Γ ⊓ H).subgroupOf H → Γ := fun p =>
    ⟨repO Γ y0 p.1 * ((p.2 : H) : G), Γ.mul_mem (repO_mem Γ y0 p.1)
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 p.2.2)).1⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨x, δ⟩ ⟨x', δ'⟩ he
      have he' : repO Γ y0 x * ((δ : H) : G) = repO Γ y0 x' * ((δ' : H) : G) := congrArg Subtype.val he
      have hδ : ((δ : H) : G) • y0 = y0 := (hH _).1 (δ : H).2
      have hδ' : ((δ' : H) : G) • y0 = y0 := (hH _).1 (δ' : H).2
      have hx : (x : Y) = x' := by
        calc (x : Y) = repO Γ y0 x • y0 := (repO_smul Γ y0 x).symm
          _ = repO Γ y0 x • (((δ : H) : G) • y0) := by rw [hδ]
          _ = (repO Γ y0 x * ((δ : H) : G)) • y0 := (mul_smul _ _ _).symm
          _ = (repO Γ y0 x' * ((δ' : H) : G)) • y0 := by rw [he']
          _ = repO Γ y0 x' • (((δ' : H) : G) • y0) := mul_smul _ _ _
          _ = repO Γ y0 x' • y0 := by rw [hδ']
          _ = x' := repO_smul Γ y0 x'
      have hxx : x = x' := Subtype.ext hx
      subst hxx
      have e : ((δ : H) : G) = ((δ' : H) : G) := mul_left_cancel he'
      exact Prod.ext rfl (Subtype.ext (Subtype.ext e))
    · intro γ
      have hd : (repO Γ y0 ⟨(γ : G) • y0, γ, γ.2, rfl⟩)⁻¹ * γ ∈ H := by
        rw [hH, mul_smul, inv_smul_eq_iff, repO_smul]
      refine ⟨(⟨(γ : G) • y0, γ, γ.2, rfl⟩, ⟨⟨_, hd⟩, Subgroup.mem_subgroupOf.2
        (Subgroup.mem_inf.2 ⟨Γ.mul_mem (Γ.inv_mem (repO_mem Γ y0 _)) γ.2, hd⟩)⟩), ?_⟩
      apply Subtype.ext
      exact mul_inv_cancel_left _ _
  calc _ = ∑' p : orbS Γ y0 × (Γ ⊓ H).subgroupOf H, u (repO Γ y0 p.1 * ((p.2 : H) : G)) :=
        (ENNReal.tsum_prod (f := fun x (δ : (Γ ⊓ H).subgroupOf H) => u (repO Γ y0 x * ((δ : H) : G)))).symm
    _ = ∑' γ : Γ, u γ := (Equiv.ofBijective F hF).tsum_eq (fun γ : Γ => u γ)

end Abs

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology

def CosDens : Prop :=
  ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (ν m : Measure X) [IsFiniteMeasure m],
    IsFiniteMeasureOnCompacts ν →
    ∀ (H : ℕ → AddSubgroup X), (∀ n, IsOpen (H n : Set X)) → (∀ n, IsCompact (H n : Set X)) →
      Antitone H → (∀ N ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N) →
      ∀ (c0 : X) (κ : ENNReal), m {z | z - c0 ∈ H 0}ᶜ = 0 →
        (∀ n h, h - c0 ∈ H 0 → m {z | z - h ∈ H n} = κ * ν {z | z - h ∈ H n}) →
        ∀ S : Set X, IsCompact S → m S = κ * ν (S ∩ {z | z - c0 ∈ H 0})

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology

def HenselCount : Prop :=
  ∀ (V X : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
    ∀ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X), (∀ n, IsOpen (Λ n : Set V)) →
      (∀ n, IsCompact (Λ n : Set V)) → Antitone Λ → (∀ n, IsOpen (H n : Set X)) →
      (∀ n, IsCompact (H n : Set X)) →
      ∀ D : V →+ X, (∀ n, (Λ n).map D = H n) →
      ∀ (G : V → X) (y : V),
        (∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) →
        ∀ n h, h - G y ∈ H 0 →
          μ {Z | Z ∈ Λ 0 ∧ G (y + Z) - h ∈ H n} * ν (H 0) = μ (Λ 0) * ν (H n)

end PI.VolStabS
end
end
