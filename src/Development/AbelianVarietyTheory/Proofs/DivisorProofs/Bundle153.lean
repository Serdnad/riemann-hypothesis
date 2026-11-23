module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle022
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam.QAllSubring

variable {R : Subring ℂ} {N : ℕ}

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.const {c : ℂ} (hc : c ∈ R) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun _ => c := by
  refine ⟨fun n => if n = 0 then c else 0, ?_, fun n => ?_⟩
  · rw [_root_.GlobalTheory.QFam.hasQ_iff]
    intro τ
    have h := hasSum_single (f := fun n : ℕ =>
      (if n = 0 then c else 0) * Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N) ^ n) 0
      (fun m hm => by simp [hm])
    simpa using h
  · show (if n = 0 then c else 0) ∈ R
    split_ifs
    · exact hc
    · exact R.zero_mem

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.add {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ + g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => a n + b n, ?_, fun n => R.add_mem (haR n) (hbR n)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  simpa [add_mul] using (ha τ).add (hb τ)

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.sub {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ - g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => a n - b n, ?_, fun n => R.sub_mem (haR n) (hbR n)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  simpa [sub_mul] using (ha τ).sub (hb τ)

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.mul {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ * g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2, ?_,
    fun n => R.sum_mem fun kl _ => R.mul_mem (haR kl.1) (hbR kl.2)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  set q := Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N)
  have hsa : Summable fun n => ‖a n * q ^ n‖ := summable_norm_iff.mpr (ha τ).summable
  have hsb : Summable fun n => ‖b n * q ^ n‖ := summable_norm_iff.mpr (hb τ).summable
  have hterm : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      a kl.1 * q ^ kl.1 * (b kl.2 * q ^ kl.2) =
      (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2) * q ^ n := by
    intro n
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hkl, pow_add]
    ring
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hsa hsb
  have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsa hsb
  rw [(ha τ).tsum_eq, (hb τ).tsum_eq] at heq
  rw [heq]
  simp only [hterm] at hs ⊢
  exact (summable_norm_iff.mp hs).hasSum

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.pow {f : ℍ → ℂ} (k : ℕ)
    (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ ^ k := by
  induction k with
  | zero => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.one_mem
  | succ k ih => simpa [pow_succ] using _root_.GlobalTheory.QFam.QAllSubring.mul ih hf

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.sum {κ : Type} (s : Finset κ) {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.zero_mem
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact _root_.GlobalTheory.QFam.QAllSubring.add (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.prod {κ : Type} (s : Finset κ) {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.one_mem
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact _root_.GlobalTheory.QFam.QAllSubring.mul (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.ring_closed : ∀ (R : Subring ℂ) (N : ℕ), 0 < N →
    (∀ c ∈ R, _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun _ => c) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ + g τ) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ - g τ) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ * g τ) ∧
    (∀ f (k : ℕ), _root_.GlobalTheory.QFam.QAll (· ∈ R) N f →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ ^ k) ∧
    (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ),
      (∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) →
      (_root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ) ∧
        _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ) := by
  intro R N _
  exact ⟨fun c hc => _root_.GlobalTheory.QFam.QAllSubring.const hc,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.add hf hg,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.sub hf hg,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.mul hf hg,
    fun f k hf => _root_.GlobalTheory.QFam.QAllSubring.pow k hf,
    fun κ s f hf => ⟨_root_.GlobalTheory.QFam.QAllSubring.sum s hf,
      _root_.GlobalTheory.QFam.QAllSubring.prod s hf⟩⟩

end GlobalTheory.QFam.QAllSubring
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

variable {ι : Type} {act : ι → SL(2, ℤ) → ι}

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
private lemma isFam_apply_smul_mul_denom_zpow {w : ℤ} {f : ι → ℍ → ℂ}
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) (i : ι) (γ : SL(2, ℤ)) (τ : ℍ) :
    f i (γ • τ) * UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) ↑τ ^ (-w) = f (act i γ) τ := by
  rw [← SL_slash_apply, hf i γ]


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
theorem _root_.GlobalTheory.QFam.IsFam.const_mul_fun {w : ℤ} {f : ι → ℍ → ℂ} (c : ℂ)
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) :
    _root_.GlobalTheory.QFam.IsFam act w fun i τ => c * f i τ := by
  intro i γ
  funext τ
  simp only [SL_slash_apply]
  rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ]
  ring


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
theorem _root_.GlobalTheory.QFam.IsFam.mul_fun {w w' : ℤ} {f g : ι → ℍ → ℂ}
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) (hg : _root_.GlobalTheory.QFam.IsFam act w' g) :
    _root_.GlobalTheory.QFam.IsFam act (w + w') fun i τ => f i τ * g i τ := by
  intro i γ
  funext τ
  simp only [SL_slash_apply]
  rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ, ← isFam_apply_smul_mul_denom_zpow hg i γ τ, neg_add,
    zpow_add₀ (UpperHalfPlane.denom_ne_zero _ _)]
  ring


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
theorem _root_.GlobalTheory.QFam.IsFam.pow_fun {w : ℤ} {f : ι → ℍ → ℂ} (k : ℕ)
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) :
    _root_.GlobalTheory.QFam.IsFam act (k * w) fun i τ => f i τ ^ k := by
  intro i γ
  funext τ
  simp only [SL_slash_apply]
  rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
    show -((k : ℤ) * w) = -w * k by ring]


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
theorem _root_.GlobalTheory.QFam.IsFam.sum_fun {κ : Type} (t : Finset κ) {w : ℤ}
    {f : κ → ι → ℍ → ℂ} (hf : ∀ k ∈ t, _root_.GlobalTheory.QFam.IsFam act w (f k)) :
    _root_.GlobalTheory.QFam.IsFam act w fun i τ => ∑ k ∈ t, f k i τ := by
  intro i γ
  funext τ
  simp only [SL_slash_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k hk => isFam_apply_smul_mul_denom_zpow (hf k hk) i γ τ


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
theorem _root_.GlobalTheory.QFam.isFam_algebra : ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι),
    (∀ c : ℂ, _root_.GlobalTheory.QFam.IsFam act 0 fun _ _ => c) ∧
    (∀ w f g, _root_.GlobalTheory.QFam.IsFam act w f → _root_.GlobalTheory.QFam.IsFam act w g →
      (_root_.GlobalTheory.QFam.IsFam act w fun i τ => f i τ + g i τ) ∧
        _root_.GlobalTheory.QFam.IsFam act w fun i τ => f i τ - g i τ) ∧
    (∀ w (c : ℂ) f, _root_.GlobalTheory.QFam.IsFam act w f →
      _root_.GlobalTheory.QFam.IsFam act w fun i τ => c * f i τ) ∧
    (∀ w w' f g, _root_.GlobalTheory.QFam.IsFam act w f → _root_.GlobalTheory.QFam.IsFam act w' g →
      _root_.GlobalTheory.QFam.IsFam act (w + w') fun i τ => f i τ * g i τ) ∧
    (∀ w f (k : ℕ), _root_.GlobalTheory.QFam.IsFam act w f →
      _root_.GlobalTheory.QFam.IsFam act (k * w) fun i τ => f i τ ^ k) ∧
    (∀ (κ : Type) (t : Finset κ) w (f : κ → ι → ℍ → ℂ),
      (∀ k ∈ t, _root_.GlobalTheory.QFam.IsFam act w (f k)) →
        _root_.GlobalTheory.QFam.IsFam act w fun i τ => ∑ k ∈ t, f k i τ) ∧
    (∀ (κ : Type) (t : Finset κ) (w : κ → ℤ) (f : κ → ι → ℍ → ℂ),
      (∀ k ∈ t, _root_.GlobalTheory.QFam.IsFam act (w k) (f k)) →
        _root_.GlobalTheory.QFam.IsFam act (∑ k ∈ t, w k) fun i τ => ∏ k ∈ t, f k i τ) ∧
    (∀ (κ : Type) (act' : κ → SL(2, ℤ) → κ) (φ : κ → ι) w f,
      (∀ k γ, φ (act' k γ) = act (φ k) γ) → _root_.GlobalTheory.QFam.IsFam act w f →
        _root_.GlobalTheory.QFam.IsFam act' w fun k => f (φ k)) := by
  intro ι act
  have hconst : ∀ c : ℂ, _root_.GlobalTheory.QFam.IsFam act 0 fun _ _ => c := by
    intro c i γ
    funext τ
    simp [SL_slash_apply]
  refine ⟨hconst, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w f g hf hg
    constructor
    · intro i γ
      funext τ
      simp only [SL_slash_apply]
      rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ, ← isFam_apply_smul_mul_denom_zpow hg i γ τ]
      ring
    · intro i γ
      funext τ
      simp only [SL_slash_apply]
      rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ, ← isFam_apply_smul_mul_denom_zpow hg i γ τ]
      ring
  · intro w c f hf
    exact hf.const_mul_fun c
  · intro w w' f g hf hg
    exact hf.mul_fun hg
  · intro w f k hf
    exact hf.pow_fun k
  · intro κ t w f hf
    exact _root_.GlobalTheory.QFam.IsFam.sum_fun t hf
  · intro κ t w f hf
    classical
    induction t using Finset.induction_on with
    | empty => simpa using hconst 1
    | insert a s ha ih =>
      have hmul := (hf a (Finset.mem_insert_self a s)).mul_fun
        (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
      simpa [Finset.sum_insert ha, Finset.prod_insert ha] using hmul
  · intro κ act' φ w f hφ hf k γ
    show f (φ k) ∣[w] γ = f (φ (act' k γ))
    rw [hf (φ k) γ, hφ k γ]

end GlobalTheory.QFam
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.IsFam.value_mul_denom {ι : Type} {act : ι → SL(2, ℤ) → ι}
    {w : ℤ} {f : ι → ℍ → ℂ}
    (h : _root_.GlobalTheory.QFam.IsFam act w f) (i : ι) (γ : SL(2, ℤ)) (τ : ℍ) :
    f i (γ • τ) * UpperHalfPlane.denom γ τ ^ (-w) = f (act i γ) τ := by
  have hi := congrFun (h i γ) τ
  rw [ModularForm.SL_slash_apply] at hi
  exact hi


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.IsFam.esymm_slash {ι : Type} [Fintype ι]
    {act : ι → SL(2, ℤ) → ι} {w : ℤ} {f : ι → ℍ → ℂ}
    (hb : _root_.GlobalTheory.QFam.ActBij act) (h : _root_.GlobalTheory.QFam.IsFam act w f)
    (γ : SL(2, ℤ)) (k : ℕ) :
    (fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) ∣[(k * w : ℤ)] γ =
      fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ := by
  let e : ι ≃ ι := Equiv.ofBijective _ (hb γ)
  ext τ
  rw [ModularForm.SL_slash_apply, Finset.sum_mul]
  have key : ∀ t ∈ Finset.powersetCard k (Finset.univ : Finset ι),
      (∏ i ∈ t, f i (γ • τ)) * UpperHalfPlane.denom γ τ ^ (-(k * w : ℤ)) =
        ∏ i ∈ t, f (e i) τ := by
    intro t ht
    rw [Finset.mem_powersetCard] at ht
    calc (∏ i ∈ t, f i (γ • τ)) * UpperHalfPlane.denom γ τ ^ (-(k * w : ℤ))
        = ∏ i ∈ t, (f i (γ • τ) * UpperHalfPlane.denom γ τ ^ (-w)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, ht.2, ← zpow_natCast, ← zpow_mul]
          congr 2
          ring
      _ = ∏ i ∈ t, f (e i) τ := Finset.prod_congr rfl fun i _ => h.value_mul_denom i γ τ
  rw [Finset.sum_congr rfl key]
  refine Finset.sum_nbij' (fun t => t.map e.toEmbedding) (fun t => t.map e.symm.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.card_map] at ht ⊢
    exact ht
  · intro t ht
    simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.card_map] at ht ⊢
    exact ht
  · intro t _
    simp [Finset.map_map]
  · intro t _
    simp [Finset.map_map]
  · intro t _
    rw [Finset.prod_map]
    rfl


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.sum_esymm_slash : ∀ (ι : Type) [Fintype ι]
    (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ),
    _root_.GlobalTheory.QFam.ActBij act → _root_.GlobalTheory.QFam.IsFam act w f → ∀ γ : SL(2, ℤ),
      ((fun τ => ∑ i, f i τ) ∣[w] γ = fun τ => ∑ i, f i τ) ∧
      ∀ k : ℕ, ((fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) ∣[(k * w : ℤ)] γ =
        fun τ => ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ) := by
  intro ι _ act w f hb h γ
  refine ⟨?_, fun k => h.esymm_slash hb γ k⟩
  let e : ι ≃ ι := Equiv.ofBijective _ (hb γ)
  ext τ
  rw [ModularForm.SL_slash_apply, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ => h.value_mul_denom i γ τ]
  exact e.sum_comp (fun i => f i τ)

end GlobalTheory.QFam
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

private lemma hasSum_conv_mul_of_multiplicative {a b : ℕ → ℂ} {e : ℕ → ℂ} {x y : ℂ}
    (he : ∀ m n, e (m + n) = e m * e n)
    (ha : HasSum (fun n => a n * e n) x) (hb : HasSum (fun n => b n * e n) y) :
    HasSum (fun n => conv a b n * e n) (x * y) := by
  have hna : Summable fun n => ‖a n * e n‖ := summable_norm_iff.mpr ha.summable
  have hnb : Summable fun n => ‖b n * e n‖ := summable_norm_iff.mpr hb.summable
  have hS : HasSum (fun n => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (a p.1 * e p.1) * (b p.2 * e p.2)) (x * y) := by
    rw [← ha.tsum_eq, ← hb.tsum_eq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hna hnb]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hna hnb).of_norm.hasSum
  convert hS using 1
  funext n
  rw [conv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, he]
  ring

private lemma mvExp_add_character_germs (N : ℕ) (τ : ℍ) (m n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((m + n : ℕ) : ℂ) * τ / N) =
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * τ / N) *
        Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / N) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem HasQ.mul_conv {N : ℕ} {f g : ℍ → ℂ} {a b : ℕ → ℂ} (hf : HasQ N f a) (hg : HasQ N g b) :
    HasQ N (fun τ => f τ * g τ) (conv a b) :=
  fun τ => hasSum_conv_mul_of_multiplicative (mvExp_add_character_germs N τ) (hf τ) (hg τ)

theorem hasQ_mul_conv : ∀ (N : ℕ) (f g : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N g b →
    HasQ N (fun τ => f τ * g τ) (conv a b) := by
  intro N f g a b _ hf hg τ
  exact hasSum_conv_mul_of_multiplicative (mvExp_add_character_germs N τ) (hf τ) (hg τ)

end GlobalTheory.QFam
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

theorem hasQ_vadd : ∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) (b : ℝ), HasQ N f a →
    HasQ N (fun τ => f (b +ᵥ τ))
      (fun n => a n * Complex.exp (2 * Real.pi * Complex.I * n * b / N)) := by
  intro N f a b h τ
  have h1 := h (b +ᵥ τ)
  have he : (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * b / N) *
      Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) =
      fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * ((b +ᵥ τ : ℍ) : ℂ) / N) := by
    funext n
    rw [UpperHalfPlane.coe_vadd, mul_assoc (a n), ← Complex.exp_add]
    congr 2
    ring
  show HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * b / N) *
      Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) (f (b +ᵥ τ))
  rw [he]
  exact h1

end GlobalTheory.QFam
end

section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory

theorem coefM_pencil : GlobalTheory.PsCo.Cw2a.T_coefM_pencil := by
  intro n L I _ _ A0 B0
  have h := pencil_det_adjugate_coeff (τ := Fin L ⊕ EntIdx n) A0 B0
  simpa only [coefM, muM, inM, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Polynomial.lcoeff_apply, AlgEquiv.toLinearMap_apply, AlgHom.coe_coe] using h

end GlobalTheory
end
