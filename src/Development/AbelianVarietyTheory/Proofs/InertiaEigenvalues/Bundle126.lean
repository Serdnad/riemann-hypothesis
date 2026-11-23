module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle105
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NabBijectiveWindow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle104
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion

@[expose] public section

section

noncomputable section
namespace GlobalTheory.PhiGam.TwistShift
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

variable {k : Type} [Field k]

theorem zpow_one_add (c : k⟦X⟧) (s : ℤ) :
    ∃ d : k⟦X⟧, (1 + (c : k⸨X⸩) * vv k ^ 2) ^ s = 1 + (d : k⸨X⸩) * vv k ^ 2 := by
  have hw : (1 + c * PowerSeries.X ^ 2) * PowerSeries.invOfUnit (1 + c * PowerSeries.X ^ 2) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp)
  set w := PowerSeries.invOfUnit (1 + c * PowerSeries.X ^ 2) 1
  have hw' := congrArg (fun a : k⟦X⟧ => (a : k⸨X⸩)) hw
  simp only [map_mul, map_add (f := _), map_one, map_pow, ← vv_eq_coe_X] at hw'
  have hne : 1 + (c : k⸨X⸩) * vv k ^ 2 ≠ 0 := left_ne_zero_of_mul_eq_one hw'
  induction s using Int.induction_on with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨d + c + d * c * PowerSeries.X ^ 2, ?_⟩
    rw [zpow_add_one₀ hne, hd]
    simp only [map_mul, map_add (f := _), map_pow, ← vv_eq_coe_X]
    ring
  | pred n ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨(d - c) * w, ?_⟩
    rw [zpow_sub_one₀ hne, hd, ← eq_inv_of_mul_eq_one_right hw']
    simp only [map_mul, map_sub]
    linear_combination hw'

theorem one_add_pow (j : ℕ) :
    ∃ e : k⟦X⟧, (1 + vv k) ^ j = 1 + j * vv k + (e : k⸨X⸩) * vv k ^ 2 := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e + (n : k⟦X⟧) + e * PowerSeries.X, ?_⟩
    rw [pow_succ, he]
    simp only [map_mul, map_add (f := _), map_natCast, ← vv_eq_coe_X]
    push_cast
    ring

variable {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V]

theorem coe_smul_mem {N : Submodule k⟦X⟧ V} (a : k⟦X⟧) {x : V} (hx : x ∈ N) : (a : k⸨X⸩) • x ∈ N := by
  have := N.smul_mem a hx
  rwa [← algebraMap_smul k⸨X⸩ a x] at this

theorem zpow_smul_mem {N : Submodule k⟦X⟧ V} (a : ℤ) {s t : ℤ} (h : a + s = t) {x : V} (hx : x ∈ sh s N) :
    vv k ^ a • x ∈ sh t N := by
  rw [← h, ← sh_sh_eq]
  exact mem_sh_iff_exists.2 ⟨x, hx, rfl⟩

variable [Module k V]

theorem sub_mem_sh {σ : k⸨X⸩ →ₐ[k] k⸨X⸩} {g : V →ₗ[k] V} (hg : Semi σ g)
    (hv : ∃ c : k⟦X⟧, σ (vv k) = vv k * (1 + (c : k⸨X⸩) * vv k ^ 2)) {N : Submodule k⟦X⟧ V}
    (hN : ∀ x ∈ N, g x - x ∈ sh 2 N) {s : ℤ} {y : V} (hy : y ∈ sh s N) : g y - y ∈ sh (s + 2) N := by
  obtain ⟨c, hc⟩ := hv
  obtain ⟨d, hd⟩ := zpow_one_add c s
  obtain ⟨x, hx, rfl⟩ := mem_sh_iff_exists.1 hy
  have h1 : g (vv k ^ s • x) - vv k ^ s • x =
      ((1 + d * PowerSeries.X ^ 2 : k⟦X⟧) : k⸨X⸩) • vv k ^ s • (g x - x) +
        (d : k⸨X⸩) • vv k ^ (2 : ℤ) • vv k ^ s • x := by
    rw [hg, map_zpow₀, hc, mul_zpow, hd, zpow_ofNat]
    simp only [map_mul, map_add (f := _), map_one, map_pow, ← vv_eq_coe_X, smul_sub, smul_smul]
    rw [sub_eq_iff_eq_add, mul_comm (vv k ^ s), add_assoc, ← add_smul,
      add_mul _ _ (vv k ^ s), one_mul, mul_assoc, add_comm (_ * _) (vv k ^ s), sub_add_cancel]
  rw [h1]
  exact Submodule.add_mem _ (coe_smul_mem _ (zpow_smul_mem s rfl (hN x hx)))
    (coe_smul_mem _ (zpow_smul_mem 2 (add_comm _ _) hy))

theorem bijOn_twist : ∀ {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (σ : k⸨X⸩ →ₐ[k] k⸨X⸩) (g : V →ₗ[k] V), Semi σ g → (∀ a : k⟦X⟧, ∃ b : k⟦X⟧, σ (a : k⸨X⸩) = b) → (∃ c : k⟦X⟧, σ (vv k) = vv k * (1 + (c : k⸨X⸩) * vv k ^ 2)) → ∀ N : Submodule k⟦X⟧ V, IsLat N → (∀ x ∈ N, g x - x ∈ sh 2 N) → ∀ j : ℕ, (j : k) ≠ 0 → ∀ s : ℤ, Set.BijOn (fun y => (1 + vv k) ^ j • g y - y) (sh s N) (sh (s + 1) N) := by
  intro k _ V _ _ _ _ _ _ _ _ σ g hg _ hv N hL hN j hj s
  have hv0 := vv_ne_zero k
  obtain ⟨e, he⟩ := one_add_pow (k := k) j
  obtain ⟨r, hr⟩ : ∃ r : k⟦X⟧, (r : k⸨X⸩) * j = 1 :=
    ⟨PowerSeries.C (j : k)⁻¹, by
      rw [← map_natCast (HahnSeries.ofPowerSeries ℤ k), ← map_mul, ← map_natCast (PowerSeries.C (R := k)),
        ← map_mul, inv_mul_cancel₀ hj, map_one, map_one]⟩
  have hvv : vv k ^ (-1 : ℤ) * vv k = 1 := by rw [zpow_neg_one, inv_mul_cancel₀ hv0]
  let θ : V →+ V :=
    { toFun := fun y => (1 + vv k) ^ j • g y - y
      map_zero' := by simp
      map_add' := fun a b => by simp only [map_add (f := _), smul_add]; abel }
  have hθ : ∀ y, θ y = (1 + vv k) ^ j • g y - y := fun _ => rfl
  let E : V →+ V :=
    { toFun := fun y => y - (r : k⸨X⸩) • vv k ^ (-1 : ℤ) • θ y
      map_zero' := by simp
      map_add' := fun a b => by simp only [map_add (f := _), smul_add]; abel }
  have hE : ∀ y, E y = y - (r : k⸨X⸩) • vv k ^ (-1 : ℤ) • θ y := fun _ => rfl
  have hθE : ∀ y, θ y = ((j : k⟦X⟧) : k⸨X⸩) • vv k ^ (1 : ℤ) • (y - E y) := by
    intro y
    rw [hE, sub_sub_cancel, smul_smul, smul_smul, smul_smul, map_natCast, zpow_one]
    rw [show (j : k⸨X⸩) * vv k * r * vv k ^ (-1 : ℤ) = 1 by linear_combination (r * j) * hvv + hr, one_smul]
  have hEm : ∀ (t : ℤ), ∀ y ∈ sh t N, E y ∈ sh (t + 1) N := by
    intro t y hy
    have h1 : θ y = (((1 + PowerSeries.X) ^ j : k⟦X⟧) : k⸨X⸩) • (g y - y) + (e : k⸨X⸩) • vv k ^ (2 : ℤ) • y
        + (j * vv k) • y := by
      rw [hθ, map_pow, map_add (f := _), map_one, ← vv_eq_coe_X, smul_sub, zpow_ofNat]
      generalize (1 + vv k) ^ j • g y = z
      rw [he, add_smul, add_smul, one_smul, mul_smul (e : k⸨X⸩)]
      abel
    have h2 : E y = -((r : k⸨X⸩) • vv k ^ (-1 : ℤ) • ((((1 + PowerSeries.X) ^ j : k⟦X⟧) : k⸨X⸩) • (g y - y) +
        (e : k⸨X⸩) • vv k ^ (2 : ℤ) • y)) := by
      rw [hE, h1, smul_add _ _ ((j * vv k) • y), smul_add _ _ (_ • (j * vv k) • y),
        smul_smul _ (j * vv k), smul_smul _ (_ * (j * vv k)),
        show (r : k⸨X⸩) * (vv k ^ (-1 : ℤ) * (j * vv k)) = 1 by linear_combination (r * j) * hvv + hr, one_smul]
      abel
    rw [h2]
    refine Submodule.neg_mem _ (coe_smul_mem _ (zpow_smul_mem (s := t + 2) _ (by ring) ?_))
    exact Submodule.add_mem _ (coe_smul_mem _ (sub_mem_sh hg hv hN hy))
      (coe_smul_mem _ (zpow_smul_mem 2 (add_comm _ _) hy))
  have hEs : ∀ y ∈ sh s N, E y ∈ sh s N := fun y hy => sh_le_sh_of_le (by omega) N (hEm s y hy)
  let T : sh s N →+ sh s N :=
    { toFun := fun m => ⟨E m, hEs _ m.2⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  have hT : ∀ m, ((T m : sh s N) : V) = E m := fun _ => rfl
  haveI : Module.Finite k⟦X⟧ (sh s N) := Module.Finite.iff_fg.2 (hL.shift s).1
  haveI : IsPrecomplete (Ideal.span {(PowerSeries.X : k⟦X⟧)}) (sh s N) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module _ _
  haveI : IsHausdorff (Ideal.span {(PowerSeries.X : k⟦X⟧)}) (sh s N) := by
    rw [← PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  have hXs : ∀ (i : ℕ) (x : V), (PowerSeries.X ^ i : k⟦X⟧) • x = vv k ^ (i : ℤ) • x := by
    intro i x
    rw [← algebraMap_smul k⸨X⸩ (PowerSeries.X ^ i : k⟦X⟧) x, zpow_natCast, map_pow, vv_eq_coe_X]
    rfl
  have hfil : ∀ (i : ℕ) (m : sh s N),
      m ∈ (Ideal.span {(PowerSeries.X : k⟦X⟧)} ^ i • ⊤ : Submodule k⟦X⟧ (sh s N)) ↔ (m : V) ∈ sh (i + s) N := by
    intro i m
    rw [mem_span_pow_smul_top, ← sh_sh_eq, mem_sh_iff_exists]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, (hXs i y).symm⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext ((hXs i y).trans h)⟩
  have key := sub_id_bij_of_contracting (Ideal.span {(PowerSeries.X : k⟦X⟧)}) T (by
    intro i m hm
    rw [hfil] at hm ⊢
    have := hEm _ _ hm
    rw [hT]
    convert this using 2
    push_cast
    ring)
  change Set.BijOn θ _ _
  refine ⟨fun y hy => ?_, fun a ha b hb hab => ?_, fun z hz => ?_⟩
  · rw [hθE]
    exact coe_smul_mem _ (zpow_smul_mem 1 (add_comm _ _) (Submodule.sub_mem _ hy (hEs y hy)))
  · have := key.2 ⟨a - b, Submodule.sub_mem _ ha hb⟩ (Subtype.ext (by
      rw [hT, hE, map_sub θ, hab]; simp))
    exact sub_eq_zero.1 (congrArg Subtype.val this)
  · obtain ⟨m, hm⟩ := key.1 ⟨-((r : k⸨X⸩) • vv k ^ (-1 : ℤ) • z),
      Submodule.neg_mem _ (coe_smul_mem _ (zpow_smul_mem _ (by ring) hz))⟩
    refine ⟨m, m.2, ?_⟩
    have h1 : E m - m = -((r : k⸨X⸩) • vv k ^ (-1 : ℤ) • z) := congrArg Subtype.val hm
    rw [hθE, ← neg_sub, h1, neg_neg, smul_smul, smul_smul, smul_smul, map_natCast, zpow_one,
      show (j : k⸨X⸩) * vv k * r * vv k ^ (-1 : ℤ) = 1 by linear_combination (r * j) * hvv + hr, one_smul]

end GlobalTheory.PhiGam.TwistShift
end
end

section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.phiGammaModule_saturation_theorem :
    ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l)
      {n : ℕ} [NeZero n]
      {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
      [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
      [FiniteDimensional k⸨X⸩ V]
      {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W]
      [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W]
      [FiniteDimensional k⸨X⸩ W]
      (D : ModPG R n V) (D' : ModPG R n W) (f : ZMod n → W →ₗ[k⸨X⸩] V),
      (∀ i, Function.Injective (f i)) →
      (∀ i x, f i (D'.φ i x) = D.φ i (f (i - 1) x)) →
      (∀ i x, f i (D'.γ i x) = D.γ i (f i x)) →
      ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V),
        (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) →
        let N' := fun i => (N i).comap ((f i).restrictScalars k⟦X⟧);
        (∀ i, IsLat (N' i)) ∧ CondAB D'.φ w w' N' ∧ ∀ i, CondC (D'.γ i) (N' i) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC
  refine ⟨fun i => Sat.isLat_comap _ (hf i) (hN i), fun i => ?_, fun i x hx => ?_⟩
  · have h := Sat.comap_pull D D' i (f (i - 1)) (f i) (hf _) (hf _) (hφ i) (hN (i - 1)).1
    rw [← h, ← Sat.comap_sh, ← Sat.comap_sh]
    exact ⟨Submodule.comap_mono (hAB i).1, Submodule.comap_mono (hAB i).2⟩
  · rw [← Sat.comap_sh]
    change f i _ ∈ sh 1 (N i)
    rw [map_sub, hγ]
    exact hC i _ hx
end

section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.senMultiplicity_shift_lattice_variablePow : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N : Submodule k⟦X⟧ V, IsLat N → CondC g N → ∀ (a : ℤ) (x : k), sen g (sh a N) x = sen g N (x + a) := by
  first | exact @GlobalTheory.PhiGam.SenShift.sen_sh | exact GlobalTheory.PhiGam.SenShift.sen_sh | (intros; apply GlobalTheory.PhiGam.SenShift.sen_sh <;> assumption)
end

section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.quotientMultiplicity_shift_lattice_quotient : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ P Q : Submodule k⟦X⟧ V, IsLat P → IsLat Q → Q ≤ P → CondC g P → CondC g Q → ∀ x : k, qmult g (sh 1 P) (sh 1 Q) x = qmult g P Q (x + 1) := by
  first | exact @GlobalTheory.PhiGam.QuotShift.main | exact GlobalTheory.PhiGam.QuotShift.main | (intros; apply GlobalTheory.PhiGam.QuotShift.main <;> assumption)
end

section

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Gauge
section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
theorem _root_.GlobalTheory.PhiGam.Gauge.phi_sh {l : ℕ} (R : _root_.GlobalTheory.PhiGam.RingPG k l)
    (f : V →ₗ[k] V) (hf : _root_.GlobalTheory.PhiGam.Semi R.φ f)
    (N N' : Submodule k⟦X⟧ V) (w : ℤ)
    (h : _root_.GlobalTheory.PhiGam.pull f N' ≤ _root_.GlobalTheory.PhiGam.sh (-w) N) (m : ℕ) {x : V}
    (hx : x ∈ _root_.GlobalTheory.PhiGam.sh m N') :
    f x ∈ _root_.GlobalTheory.PhiGam.sh (l * m - w) N := by
  obtain ⟨y, hy, rfl⟩ := _root_.GlobalTheory.PhiGam.mem_sh_iff_exists.1 hx
  obtain ⟨u, hu⟩ := R.φ_v
  have hfy : f y ∈ _root_.GlobalTheory.PhiGam.sh (-w) N := h (Submodule.subset_span ⟨y, hy, rfl⟩)
  obtain ⟨z, hz, hz'⟩ := _root_.GlobalTheory.PhiGam.mem_sh_iff_exists.1 hfy
  rw [_root_.GlobalTheory.PhiGam.mem_sh_iff_exists]
  refine ⟨((u : k⟦X⟧) ^ m) • z, N.smul_mem _ hz, ?_⟩
  have hX := _root_.GlobalTheory.PhiGam.vv_ne_zero k
  rw [zpow_natCast, hf, map_pow, hu, ← hz', ← algebraMap_smul k⸨X⸩ ((u : k⟦X⟧) ^ m) z, smul_smul,
    smul_smul, LaurentSeries.coe_algebraMap, map_pow, sub_eq_add_neg, zpow_add₀ hX, mul_pow, ← pow_mul]
  congr 1
  rw [show ((l : ℤ) * (m : ℤ)) = ((l * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  ring

end

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
private theorem vv_smul_mem_sh_succ_iff (a : ℤ) (N : Submodule k⟦X⟧ V) (y : V) :
    _root_.GlobalTheory.PhiGam.vv k • y ∈ _root_.GlobalTheory.PhiGam.sh (a + 1) N ↔
      y ∈ _root_.GlobalTheory.PhiGam.sh a N := by
  have hX := _root_.GlobalTheory.PhiGam.vv_ne_zero k
  rw [_root_.GlobalTheory.PhiGam.mem_sh_iff_smul_mem, _root_.GlobalTheory.PhiGam.mem_sh_iff_smul_mem, smul_smul, ← zpow_add_one₀ hX]
  rw [show -(a + 1) + 1 = -a by ring]

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
private theorem apply_sub_self_eq_vv_smul_nab (f : V →ₗ[k] V) (x : V) :
    f x - x = _root_.GlobalTheory.PhiGam.vv k • _root_.GlobalTheory.PhiGam.nab f x := by
  rw [_root_.GlobalTheory.PhiGam.nab_apply_eq, smul_smul, mul_inv_cancel₀ (_root_.GlobalTheory.PhiGam.vv_ne_zero k),
    one_smul]


open scoped LaurentSeries PowerSeries in
theorem _root_.GlobalTheory.PhiGam.Gauge.main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l]
    (R : _root_.GlobalTheory.PhiGam.RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
    [FiniteDimensional k⸨X⸩ V] (D : _root_.GlobalTheory.PhiGam.ModPG R n V), ∀ (w w' : ZMod n → ℤ) (s : ZMod n → ℕ)
    (N : ZMod n → Submodule k⟦X⟧ V), (∀ i, _root_.GlobalTheory.PhiGam.IsLat (N i)) →
    _root_.GlobalTheory.PhiGam.CondAB D.φ w w' N →
    (∀ i, _root_.GlobalTheory.PhiGam.CondC (D.γ i) (N i)) →
    (∀ i, (s i : ℤ) + 1 ≤ l * (s (i - 1) + 1) - w i) →
    (∀ i (a : ℕ), a ≤ s i + 1 → _root_.GlobalTheory.PhiGam.sen (D.γ i) (N i) (a : k) = 0) →
    ∀ b g : ZMod n → V, (∀ i, D.γ i (b i) - b i =
      D.φ i (g (i - 1)) - g i) →
    (∀ i, g i ∈ _root_.GlobalTheory.PhiGam.sh 1 (N i)) →
    (∃ m : ZMod n → V, (∀ i, m i ∈ N i) ∧
      ∀ i, g i - (D.γ i (m i) - m i) ∈ _root_.GlobalTheory.PhiGam.sh (s i + 3) (N i)) ∧
    ((∀ i, g i ∈ _root_.GlobalTheory.PhiGam.sh (s i + 3) (N i)) → (∀ i, b i ∈ N i) →
      ∃ m : ZMod n → V, (∀ i, m i ∈ N i) ∧ ∀ i, b i = D.φ i (m (i - 1)) - m i ∧
        g i = D.γ i (m i) - m i) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ D w w' s N hN hAB hC hs hsen b g hcoc hg
  have hX := _root_.GlobalTheory.PhiGam.vv_ne_zero k
  have hl : (2 : ℤ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hW : ∀ i, _ := fun i => _root_.GlobalTheory.PhiGam.Window.nab_bijective_window R (D.γ i)
    (D.γ_semi i) (N i) (hN i) (hC i) 0 (s i + 2) (fun j hj => by
      simpa using hsen i j (by omega))
  refine ⟨?_, fun hg3 hb => ?_⟩
  · have key : ∀ i, ∃ x ∈ N i, g i - (D.γ i x - x) ∈
        _root_.GlobalTheory.PhiGam.sh (s i + 3) (N i) := by
      intro i
      have hy : (_root_.GlobalTheory.PhiGam.vv k)⁻¹ • g i ∈ _root_.GlobalTheory.PhiGam.sh 0 (N i) := by
        rw [← vv_smul_mem_sh_succ_iff, smul_inv_smul₀ hX]
        simpa using hg i
      obtain ⟨x, hx, hxy⟩ := (hW i).2 _ hy
      refine ⟨x, by rwa [_root_.GlobalTheory.PhiGam.sh_zero_eq] at hx, ?_⟩
      have h3 := (vv_smul_mem_sh_succ_iff _ _ _).2 hxy
      rw [smul_sub, smul_inv_smul₀ hX, ← apply_sub_self_eq_vv_smul_nab] at h3
      convert h3 using 2
      push_cast
      ring
    choose m hm1 hm2 using key
    exact ⟨m, hm1, hm2⟩
  · set φ := D.φ
    set γ := D.γ
    have hφ : ∀ i (a : ℕ) {x : V}, x ∈ _root_.GlobalTheory.PhiGam.sh a (N (i - 1)) →
        φ i x ∈ _root_.GlobalTheory.PhiGam.sh (l * a - w i) (N i) := fun i a x hx =>
      _root_.GlobalTheory.PhiGam.Gauge.phi_sh R (φ i) (D.φ_semi i) (N i)
        (N (i - 1)) (w i) (hAB i).1 a hx
    have hγ : ∀ i (a : ℤ) {x : V}, x ∈ _root_.GlobalTheory.PhiGam.sh a (N i) →
        γ i x - x ∈ _root_.GlobalTheory.PhiGam.sh (a + 1) (N i) := fun i a x hx => by
      rw [apply_sub_self_eq_vv_smul_nab, vv_smul_mem_sh_succ_iff]
      exact _root_.GlobalTheory.PhiGam.Window.nab_mem_sh R (D.γ_semi i) (hC i) a hx
    have hb' : ∀ i, b i ∈ _root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2) (N i) := by
      intro i
      have h1 : γ i (b i) - b i ∈ _root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2 + 1) (N i) := by
        rw [hcoc i]
        refine sub_mem ?_ (by convert hg3 i using 2; ring)
        have h2 := hφ i (s (i - 1) + 3) (by push_cast; exact hg3 (i - 1))
        refine _root_.GlobalTheory.PhiGam.sh_le_sh_of_le ?_ _ h2
        have := hs i
        push_cast
        nlinarith
      rw [apply_sub_self_eq_vv_smul_nab, vv_smul_mem_sh_succ_iff] at h1
      have := (hW i).1 (b i) (by rw [_root_.GlobalTheory.PhiGam.sh_zero_eq]; exact hb i) (by convert h1 using 2; push_cast; ring)
      convert this using 2
      push_cast
      ring
    have hP : ∀ i, ∀ x ∈ _root_.GlobalTheory.PhiGam.sh ((s (i - 1) : ℤ) + 2) (N (i - 1)),
        φ i x ∈ _root_.GlobalTheory.PhiGam.sh 1
          (_root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2) (N i)) := by
      intro i x hx
      rw [_root_.GlobalTheory.PhiGam.sh_sh_eq]
      refine _root_.GlobalTheory.PhiGam.sh_le_sh_of_le ?_ _ (hφ i (s (i - 1) + 2) (by push_cast; exact hx))
      have := hs i
      push_cast
      nlinarith
    have hF := _root_.GlobalTheory.PhiGam.one_sub_frob_bij R D
      (fun i => _root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2) (N i)) (fun i => (hN i).shift _) hP
    obtain ⟨m, hmP, hmb⟩ := hF.1 b hb'
    change ∀ i, φ i (m (i - 1)) - m i = b i at hmb
    have hg0 := hF.2 (fun i => g i - (γ i (m i) - m i))
      (fun i => sub_mem (_root_.GlobalTheory.PhiGam.sh_le_sh_of_le (by linarith) _ (hg3 i))
        (_root_.GlobalTheory.PhiGam.sh_le_sh_of_le (by linarith) _ (hγ i _ (hmP i))))
      (fun i => by
        show φ i (g (i - 1) - (γ (i - 1) (m (i - 1)) - m (i - 1))) = g i - (γ i (m i) - m i)
        have e := hcoc i
        rw [← hmb i, map_sub] at e
        have e2 := sub_eq_iff_eq_add.1 e.symm
        have hcomm : ∀ x, φ i (γ (i - 1) x) = γ i (φ i x) := D.comm i
        simp only [map_sub, hcomm]
        rw [e2]
        abel)
    refine ⟨m, fun i => ?_, fun i => ⟨(hmb i).symm, ?_⟩⟩
    · have := _root_.GlobalTheory.PhiGam.sh_le_sh_of_le (show (0 : ℤ) ≤ (s i : ℤ) + 2 by positivity) _ (hmP i)
      rwa [_root_.GlobalTheory.PhiGam.sh_zero_eq] at this
    · exact sub_eq_zero.1 (congrFun hg0 i)

end GlobalTheory.PhiGam.Gauge
end

section

noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem PhiMod.exists_X_pow_smul_eq_l_pow_smul (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι)
    (n : ℕ) : ∀ w ∈ P.MM, ∃ w' ∈ P.MM,
      (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w = (l : K) ^ (l ^ n) • w' := by
  intro w hw
  have hl0 := l_ne_zero (K := K) l
  have hlp := (Fact.out : l.Prime).pos
  have hm : monomial (e * l ^ (n + 1)) (((l : K) ^ (l ^ n))⁻¹) ∈ S O K e := by
    refine monomial_mem_S ?_
    rw [norm_inv, norm_pow, inv_mul_le_one₀ (pow_pos (norm_pos_iff.2 hl0) _), wS,
      Nat.mul_div_cancel_left _ (NeZero.pos e)]
    refine (norm_factorial_le l _).trans (le_of_eq ?_)
    rw [pow_succ, Nat.mul_div_cancel _ hlp]
  refine ⟨_, P.MM.smul_mem ⟨_, hm⟩ hw, ?_⟩
  change _ = (l : K) ^ (l ^ n) • ((monomial (e * l ^ (n + 1)) (((l : K) ^ (l ^ n))⁻¹)) • w)
  rw [← smul_assoc, monomial_eq_C_mul_X_pow, smul_eq_C_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (pow_ne_zero _ hl0), map_one, one_mul]
end BK
end GlobalTheory
end
end

section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CokerL

open Matrix

theorem inv_mul_coeff_eq_of_X_pow_mul {K : Type} [Field K] {N : ℕ} {c : K} (hc : c ≠ 0)
    {f g : K⟦X⟧} (h : X ^ N * f = c • g) (k : ℕ) : c⁻¹ * coeff k f = coeff (k + N) g := by
  have := congrArg (coeff (k + N)) h
  rw [coeff_X_pow_mul, coeff_smul, smul_eq_mul] at this
  rw [this, inv_mul_cancel_left₀ hc]

theorem mem_lpow_L_of_vpow_smul (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] (P : PhiMod O K l e a ι) (n b : ℕ) (w z : Vec K a ι) (hw : w ∈ P.L)
    (hz : z ∈ P.L) (h : ((X : K⟦X⟧) ^ e) ^ n • w = (l : K) ^ b • z) :
    ∃ z' ∈ P.L, w = (l : K) ^ b • z' := by
  have hc : (l : K) ^ b ≠ 0 := pow_ne_zero _ (l_ne_zero l)
  refine ⟨((l : K) ^ b)⁻¹ • w, mem_tot.2 fun τ => P.mem_extc_iff.2 fun i => ?_,
    (smul_inv_smul₀ hc w).symm⟩
  have hm := P.mem_extc_iff.1 (mem_tot.1 hw τ)
  have hm' := P.mem_extc_iff.1 (mem_tot.1 hz τ)
  have hi : X ^ (e * n) * (P.mxInv τ *ᵥ w τ) i = (l : K) ^ b • (P.mxInv τ *ᵥ z τ) i := by
    have hτ := congrArg (fun v : Vec K a ι => (P.mxInv τ *ᵥ v τ) i) h
    simp only [Pi.smul_apply, Matrix.mulVec_smul, smul_eq_mul] at hτ
    rw [pow_mul]
    exact hτ
  rw [mem_A]
  intro k
  rw [Pi.smul_apply, Matrix.mulVec_smul, Pi.smul_apply, coeff_smul, smul_eq_mul,
    inv_mul_coeff_eq_of_X_pow_mul hc hi]
  exact mem_A.1 (hm' i) _

end GlobalTheory.CokerL
end
