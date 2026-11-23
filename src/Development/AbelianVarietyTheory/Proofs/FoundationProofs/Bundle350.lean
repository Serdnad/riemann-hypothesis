module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle016
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Finite.Lattice
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory

theorem coboundary_closed_of_uniform_approx {𝕜 : Type} [NormedField 𝕜] {Γ : Type} (H : Set Γ)
    (k f : Γ → 𝕜) (hne : ∃ s ∈ H, k s ≠ 1)
    (happ : ∀ ε : ℝ, 0 < ε → ∃ X : 𝕜, ∀ s ∈ H, ‖f s - (k s * X - X)‖ ≤ ε) :
    ∃ X : 𝕜, ∀ s ∈ H, f s = k s * X - X := by
  obtain ⟨s₀, hs₀, hk⟩ := hne
  have hd : k s₀ - 1 ≠ 0 := sub_ne_zero.mpr hk
  have hdpos : 0 < ‖k s₀ - 1‖ := norm_pos_iff.mpr hd
  refine ⟨f s₀ / (k s₀ - 1), fun s hs => ?_⟩
  have hCpos : 0 < 1 + ‖k s - 1‖ / ‖k s₀ - 1‖ := by positivity
  have key : ∀ ε : ℝ, 0 < ε → ‖f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))‖
      ≤ ε * (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) := by
    intro ε hε
    obtain ⟨X, hX⟩ := happ ε hε
    have h0 := hX s₀ hs₀
    have e0 : f s₀ - (k s₀ * X - X) = (k s₀ - 1) * (f s₀ / (k s₀ - 1) - X) := by
      field_simp
    rw [e0, norm_mul] at h0
    have hXX : ‖X - f s₀ / (k s₀ - 1)‖ ≤ ε / ‖k s₀ - 1‖ := by
      rw [norm_sub_rev, le_div_iff₀ hdpos, mul_comm]; exact h0
    have e1 : f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))
        = (f s - (k s * X - X)) + (k s - 1) * (X - f s₀ / (k s₀ - 1)) := by ring
    calc ‖f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))‖
        = ‖(f s - (k s * X - X)) + (k s - 1) * (X - f s₀ / (k s₀ - 1))‖ := by rw [e1]
      _ ≤ ‖f s - (k s * X - X)‖ + ‖k s - 1‖ * ‖X - f s₀ / (k s₀ - 1)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ ε + ‖k s - 1‖ * (ε / ‖k s₀ - 1‖) := by
          gcongr
          exact hX s hs
      _ = ε * (1 + ‖k s - 1‖ / ‖k s₀ - 1‖) := by ring
  have hz : ‖f s - (k s * (f s₀ / (k s₀ - 1)) - f s₀ / (k s₀ - 1))‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h := key (ε / (1 + ‖k s - 1‖ / ‖k s₀ - 1‖)) (div_pos hε hCpos)
    rw [div_mul_cancel₀ _ hCpos.ne'] at h
    linarith
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hz)

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.DivChain

section
variable {X : Type} [AddCommGroup X]

def DivAll (l : ℕ) (y : X) : Prop := ∀ m : ℕ, ∃ w : X, l ^ m • w = y

lemma divBy_mono {l M m : ℕ} {z : X} (h : m ≤ M) (hz : ∃ w : X, l ^ M • w = z) :
    ∃ w : X, l ^ m • w = z := by
  obtain ⟨w, rfl⟩ := hz
  refine ⟨l ^ (M - m) • w, ?_⟩
  rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' h]

lemma finite_fiber {l : ℕ} (hfin : Finite {x : X // l • x = 0}) (y z0 : X) (hz0 : l • z0 = y) :
    Finite {z : X // l • z = y} := by
  refine Finite.of_injective (fun z : {z : X // l • z = y} =>
    (⟨z.1 - z0, by rw [smul_sub, z.2, hz0, sub_self]⟩ : {x : X // l • x = 0})) ?_
  intro a b hab
  apply Subtype.ext
  have := congrArg Subtype.val hab
  simpa using this

lemma exists_preimage {l : ℕ} (hfin : Finite {x : X // l • x = 0}) {y : X} (hy : DivAll l y) :
    ∃ z : X, l • z = y ∧ DivAll l z := by
  obtain ⟨z0, hz0⟩ := hy 1
  rw [pow_one] at hz0
  haveI := finite_fiber hfin y z0 hz0
  by_contra hcon
  push_neg at hcon
  have hm : ∀ z : {z : X // l • z = y}, ∃ m : ℕ, ∀ w : X, l ^ m • w ≠ z.1 := by
    intro z
    have := hcon z.1 z.2
    simp only [DivAll, not_forall, not_exists] at this
    exact this
  choose f hf using hm
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  obtain ⟨w, hw⟩ := hy (M + 1)
  have hz : l • (l ^ M • w) = y := by rw [← mul_smul, ← pow_succ']; exact hw
  have hle : f ⟨l ^ M • w, hz⟩ ≤ M := hM ⟨⟨l ^ M • w, hz⟩, rfl⟩
  obtain ⟨w', hw'⟩ := divBy_mono (z := l ^ M • w) hle ⟨w, rfl⟩
  exact hf ⟨l ^ M • w, hz⟩ w' hw'

lemma exists_last {l : ℕ} {z : X} (hz : z ≠ 0) :
    ∀ n : ℕ, l ^ n • z = 0 → ∃ k, l ^ k • z ≠ 0 ∧ l ^ (k + 1) • z = 0
  | 0, h => by simp at h; exact absurd h hz
  | n + 1, h => by
    by_cases hk : l ^ n • z = 0
    · exact exists_last hz n hk
    · exact ⟨n, hk, h⟩

lemma exists_start {l : ℕ} (htors : ∀ x : X, ∃ n : ℕ, l ^ n • x = 0)
    (hfin : Finite {x : X // l • x = 0}) (hunb : ∀ m : ℕ, ∃ x : X, l ^ m • x ≠ 0) :
    ∃ y : X, y ≠ 0 ∧ l • y = 0 ∧ DivAll l y := by
  by_contra hcon
  push_neg at hcon
  have hm : ∀ y : {x : X // l • x = 0}, ∃ m : ℕ, y.1 ≠ 0 → ∀ w : X, l ^ m • w ≠ y.1 := by
    intro y
    by_cases hy0 : y.1 = 0
    · exact ⟨0, fun h => absurd hy0 h⟩
    · have := hcon y.1 hy0 y.2
      simp only [DivAll, not_forall, not_exists] at this
      obtain ⟨m, hm⟩ := this
      exact ⟨m, fun _ => hm⟩
  choose f hf using hm
  obtain ⟨M, hM⟩ := (Set.finite_range f).bddAbove
  obtain ⟨x, hx⟩ := hunb M
  obtain ⟨n, hn⟩ := htors (l ^ M • x)
  obtain ⟨k, hk1, hk2⟩ := exists_last hx n hn
  have hy : l • (l ^ k • (l ^ M • x)) = 0 := by rw [← mul_smul, ← pow_succ']; exact hk2
  have hle : f ⟨_, hy⟩ ≤ M := hM ⟨⟨_, hy⟩, rfl⟩
  apply hf ⟨_, hy⟩ hk1 (l ^ (M - f ⟨_, hy⟩) • (l ^ k • x))
  show l ^ f ⟨_, hy⟩ • l ^ (M - f ⟨_, hy⟩) • l ^ k • x = l ^ k • l ^ M • x
  rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' hle, ← mul_smul, ← mul_smul, mul_comm]

end

theorem exists_divisible_chain : ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X],
    (∀ x : X, ∃ n : ℕ, l ^ n • x = 0) → Finite {x : X // l • x = 0} →
    (∀ m : ℕ, ∃ x : X, l ^ m • x ≠ 0) → ∃ x : ℕ → X, x 0 ≠ 0 ∧ ∀ n, l • x (n + 1) = x n := by
  intro l _ X _ htors hfin hunb
  obtain ⟨y0, hy0, -, hdiv⟩ := exists_start htors hfin hunb
  have H : ∀ y : {y : X // DivAll l y}, ∃ z : X, l • z = y.1 ∧ DivAll l z :=
    fun y => exists_preimage hfin y.2
  choose g hg hgd using H
  let s : ℕ → {y : X // DivAll l y} := fun n => Nat.rec ⟨y0, hdiv⟩ (fun _ y => ⟨g y, hgd y⟩) n
  exact ⟨fun n => (s n).1, hy0, fun n => hg (s n)⟩

end GlobalTheory.Ord2.DivChain
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.lipschitz_of_contraction_per_level : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (P : ℕ → Γ → Prop) (lam : Γ →* Multiplicative ℤ_[l]), (∀ m g, P (m + 1) g → P m g) → (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g, P N g → ‖(lam g).toAdd‖ ≤ ε) → (∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ g, P (m + 1) g → ∃ h g' : Γ, P m h ∧ P (m + 2) g' ∧ g = h ^ l * g') → ∃ C : ℝ, ∀ (m : ℕ) (g : Γ), P m g → ‖(lam g).toAdd‖ ≤ C * ((l : ℝ)⁻¹) ^ m := by
  intro l hl Γ _ P lam hmono hsmall hdec
  obtain ⟨m₀, hdec⟩ := hdec
  have hmono' : ∀ a b g, P (a + b) g → P a g := by
    intro a b g h
    induction b with
    | zero => simpa using h
    | succ b ih => exact ih (hmono _ _ h)
  have hlpos : (0:ℝ) < l := by exact_mod_cast hl.out.pos
  have key : ∀ x y : Γ, ‖(lam (x ^ l * y)).toAdd‖ ≤
      max ((l:ℝ)⁻¹ * ‖(lam x).toAdd‖) ‖(lam y).toAdd‖ := by
    intro x y
    rw [map_mul, map_pow, toAdd_mul, toAdd_pow]
    refine (PadicInt.nonarchimedean _ _).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, norm_mul, PadicInt.norm_p]
  have step : ∀ m, m₀ ≤ m → ∀ t : ℝ, 0 ≤ t → (∀ g, P m g → ‖(lam g).toAdd‖ ≤ t) →
      ∀ g, P (m + 1) g → ‖(lam g).toAdd‖ ≤ (l:ℝ)⁻¹ * t := by
    intro m hm t ht hyp g hg
    have chain : ∀ k : ℕ, ∃ g', P (m + 1 + k) g' ∧
        ‖(lam g).toAdd‖ ≤ max ((l:ℝ)⁻¹ * t) ‖(lam g').toAdd‖ := by
      intro k
      induction k with
      | zero => exact ⟨g, by simpa using hg, le_max_right _ _⟩
      | succ k ih =>
        obtain ⟨g', hg', hle⟩ := ih
        have hg'2 : P (m + k + 1) g' := by
          rw [show m + k + 1 = m + 1 + k by omega]; exact hg'
        obtain ⟨h, g'', hh, hg'', rfl⟩ := hdec (m + k) (by omega) g' hg'2
        refine ⟨g'', ?_, hle.trans (max_le (le_max_left _ _) ((key h g'').trans
          (max_le_max ?_ le_rfl)))⟩
        · rw [show m + 1 + (k + 1) = m + k + 2 by omega]; exact hg''
        · exact mul_le_mul_of_nonneg_left (hyp h (hmono' m k h hh)) (inv_nonneg.2 hlpos.le)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := hsmall ε hε
    obtain ⟨g', hg', hle⟩ := chain N
    have hsm := hN g' (hmono' N (m + 1) g' (by rw [show N + (m + 1) = m + 1 + N by omega]; exact hg'))
    exact hle.trans (max_le (le_add_of_nonneg_right hε.le)
      (hsm.trans (le_add_of_nonneg_left (mul_nonneg (inv_nonneg.2 hlpos.le) ht))))
  have levels : ∀ j : ℕ, ∀ g, P (m₀ + j) g → ‖(lam g).toAdd‖ ≤ ((l:ℝ)⁻¹) ^ j := by
    intro j
    induction j with
    | zero => intro g _; rw [pow_zero]; exact PadicInt.norm_le_one _
    | succ j ih =>
      intro g hg
      rw [pow_succ']
      exact step (m₀ + j) (by omega) _ (pow_nonneg (inv_nonneg.2 hlpos.le) _) ih g hg
  refine ⟨(l:ℝ) ^ m₀, fun m g hg => ?_⟩
  rcases le_or_gt m₀ m with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    calc ‖(lam g).toAdd‖ ≤ ((l:ℝ)⁻¹) ^ j := levels j g hg
      _ = (l:ℝ) ^ m₀ * ((l:ℝ)⁻¹) ^ (m₀ + j) := by
        rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hlpos.ne', one_pow, one_mul]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
    have e : (l:ℝ) ^ (m + j + 1) * ((l:ℝ)⁻¹) ^ m = (l:ℝ) ^ (j + 1) := by
      rw [show m + j + 1 = m + (j + 1) by omega, pow_add, mul_comm ((l:ℝ) ^ m), mul_assoc,
        ← mul_pow, mul_inv_cancel₀ hlpos.ne', one_pow, mul_one]
    rw [e]
    exact (PadicInt.norm_le_one _).trans (one_le_pow₀ (by exact_mod_cast hl.out.one_lt.le))
end
