module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle002
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.CfBasic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle003
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll

@[expose] public section

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem cf_sum_smul {n : ℕ} (s : Finset (Wt n)) (c : Wt n → ℂ) (g : Wt n → FR n) (y : Wt n) :
    cf (∑ x ∈ s, c x • g x) y = ∑ x ∈ s, c x * cf (g x) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [_root_.UpperTheory.RealTr.cf]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ((cfBasic n).2.2.2.1 _ _ (c a) y).1,
      ((cfBasic n).2.2.2.1 (g a) 0 (c a) y).2, ih]

private theorem asym_eq_of_strictAnti {n : ℕ} {f g : FR n} (hf : ASym f) (hg : ASym g)
    (h : ∀ y : Wt n, StrictAnti y → cf f y = cf g y) (y : Wt n) : cf f y = cf g y := by
  by_cases hy : Function.Injective y
  · obtain ⟨w, hw⟩ := ((rearr n).2.1 y).2.1
    have ha : Antitone (y ∘ ⇑w) := hw ▸ ((rearr n).2.1 y).1
    have hs : StrictAnti (y ∘ ⇑w) := ha.strictAnti_of_injective (hy.comp w.injective)
    have e := h _ hs
    rw [hf w y, hg w y] at e
    have hne : sg w ≠ 0 := by
      unfold sg
      rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h1 | h1 <;> simp [h1]
    exact mul_left_cancel₀ hne e
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hy
    have hfix : y ∘ ⇑(Equiv.swap a b) = y := by
      funext i
      simp only [Function.comp_apply, Equiv.swap_apply_def]
      split_ifs with h1 h2
      · subst h1; exact hab.symm
      · subst h2; exact hab
      · rfl
    have hsg : sg (Equiv.swap a b) = -1 := by
      simp [sg, Equiv.Perm.sign_swap hne]
    have e1 := hf (Equiv.swap a b) y
    have e2 := hg (Equiv.swap a b) y
    rw [hfix, hsg] at e1 e2
    have z1 : cf f y = 0 := by linear_combination e1 / 2
    have z2 : cf g y = 0 := by linear_combination e2 / 2
    rw [z1, z2]

theorem UpperTheory.RealTr.asymExp :
    ∀ (n : ℕ) (f : FR n), ASym f → ∃ s : Finset (Wt n), (∀ x ∈ s, StrictAnti x ∧ cf f x ≠ 0) ∧ f = ∑ x ∈ s, cf f x • alt x := by
  intro n f hf
  classical
  set s := f.coeff.support.filter (fun x => StrictAnti x) with hs
  have hmem : ∀ x, x ∈ s ↔ cf f x ≠ 0 ∧ StrictAnti x := by
    intro x
    simp [hs, _root_.UpperTheory.RealTr.cf, Finsupp.mem_support_iff]
  refine ⟨s, fun x hx => ⟨((hmem x).1 hx).2, ((hmem x).1 hx).1⟩, ?_⟩
  have hR : ASym (∑ x ∈ s, cf f x • alt x) := by
    intro w z
    rw [cf_sum_smul, cf_sum_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [(cfBasic n).2.2.2.2.2.2.2.2.1 x w z]
    ring
  apply (cfBasic n).2.2.1
  intro y
  apply asym_eq_of_strictAnti hf hR
  intro y hy
  rw [cf_sum_smul, Finset.sum_eq_single y, ((cfBasic n).2.2.2.2.2.2.2.2.2.2.2.1 y hy).1, mul_one]
  · intro x hx hxy
    rw [((cfBasic n).2.2.2.2.2.2.2.2.2.2.2.1 x ((hmem x).1 hx).2).2 y hy (Ne.symm hxy), mul_zero]
  · intro hy'
    have : cf f y = 0 := by
      by_contra hc
      exact hy' ((hmem y).2 ⟨hc, hy⟩)
    rw [this, zero_mul]
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem character_support_pairing_le_of_strict_anti {n : ℕ} (κ : Wt n) (χ : FR n) (hκ : Antitone κ)
    (h : alt (rhoV n) * χ = alt (κ + rhoV n)) (x : Wt n) (hx : StrictAnti x) (ξ : Wt n)
    (hξ : cf χ ξ ≠ 0) : ∑ a, x a * ξ a ≤ ∑ a, x a * κ a := by
  classical
  have hρ : StrictAnti (rhoV n) := (rearr n).2.2.1
  have hsupp : ∀ v, cf χ v ≠ 0 ↔ v ∈ χ.coeff.support := by
    intro v
    simp [_root_.UpperTheory.RealTr.cf, Finsupp.mem_support_iff]
  obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image χ.coeff.support
    (fun v => ∑ a, x a * v a) ⟨ξ, (hsupp ξ).1 hξ⟩
  have hμ' : cf χ μ ≠ 0 := (hsupp μ).2 hμ
  have hcoef : cf (alt (rhoV n) * χ) (rhoV n + μ) = cf χ μ := by
    rw [(cfBasic n).2.2.2.2.2.2.1, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · have e : rhoV n + μ - rhoV n ∘ ⇑(1 : Equiv.Perm (Fin n)) = μ := by
        funext a
        simp
      rw [e]
      simp [sg]
    · intro w _ hw
      have hz : cf χ (rhoV n + μ - rhoV n ∘ ⇑w) = 0 := by
        by_contra hc
        have h1 := hmax _ ((hsupp _).1 hc)
        have h2 := (rearr n).1 x (rhoV n) hx.antitone hρ.antitone w
        simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, mul_sub, mul_add,
          Finset.sum_add_distrib, Finset.sum_sub_distrib] at h1
        exact hw (h2.2 hx hρ (by linarith [h2.1]))
      rw [hz, mul_zero]
    · intro h1
      exact absurd (Finset.mem_univ _) h1
  rw [h] at hcoef
  obtain ⟨w, hw⟩ := (cfBasic n).2.2.2.2.2.2.2.2.2.2.1 (κ + rhoV n) (rhoV n + μ)
    (by rw [hcoef]; exact hμ')
  have hanti : Antitone (κ + rhoV n) := hκ.add hρ.antitone
  have h2 := ((rearr n).1 x (κ + rhoV n) hx.antitone hanti w).1
  have e : ∑ a, x a * (rhoV n + μ) a = ∑ a, x a * (κ + rhoV n) (w a) := by
    rw [hw]
    rfl
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] at e h2
  have h4 : ∑ a, x a * ξ a ≤ ∑ a, x a * μ a := hmax ξ ((hsupp ξ).1 hξ)
  linarith

private theorem character_support_pairing_le_of_antitone {n : ℕ} (κ : Wt n) (χ : FR n) (hκ : Antitone κ)
    (h : alt (rhoV n) * χ = alt (κ + rhoV n)) (x : Wt n) (hx : Antitone x) (ξ : Wt n)
    (hξ : cf χ ξ ≠ 0) : ∑ a, x a * ξ a ≤ ∑ a, x a * κ a := by
  have hρ : StrictAnti (rhoV n) := (rearr n).2.2.1
  have key : ∀ ε : ℝ, 0 < ε →
      ∑ a, x a * ξ a - ∑ a, x a * κ a ≤ ε * (∑ a, rhoV n a * κ a - ∑ a, rhoV n a * ξ a) := by
    intro ε hε
    have hs : StrictAnti (fun a => x a + ε * rhoV n a) := by
      intro a b hab
      have h1 := hρ hab
      have h2 := hx hab.le
      nlinarith
    have := character_support_pairing_le_of_strict_anti κ χ hκ h _ hs ξ hξ
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at this
    linarith
  by_contra hc
  push_neg at hc
  set A := ∑ a, x a * ξ a - ∑ a, x a * κ a with hA
  set B := ∑ a, rhoV n a * κ a - ∑ a, rhoV n a * ξ a with hB
  have hA0 : 0 < A := by rw [hA]; linarith
  have ht : 0 < |B| + 1 := by positivity
  have hε : 0 < A / (2 * (|B| + 1)) := by positivity
  have k := key _ hε
  have hle : A / (2 * (|B| + 1)) * B ≤ A / (2 * (|B| + 1)) * (|B| + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [le_abs_self B]) hε.le
  have heq : A / (2 * (|B| + 1)) * (|B| + 1) = A / 2 := by
    field_simp
  linarith

theorem UpperTheory.RealTr.divSupp :
    ∀ (n : ℕ) (κ : Wt n) (χ : FR n), Antitone κ → alt (rhoV n) * χ = alt (κ + rhoV n) → cf χ κ = 1 ∧ (∀ ξ, cf χ ξ ≠ 0 → Maj ξ κ) ∧
      (Sym χ → ∀ ξ, cf χ ξ ≠ 0 → nsq ξ ≤ nsq κ) := by
  intro n κ χ hκ h
  have hρ : StrictAnti (rhoV n) := (rearr n).2.2.1
  refine ⟨?_, fun ξ hξ x hx => character_support_pairing_le_of_antitone κ χ hκ h x hx ξ hξ, ?_⟩
  · have hs : StrictAnti (κ + rhoV n) := by
      intro a b hab
      have h1 := hρ hab
      have h2 := hκ hab.le
      simp only [Pi.add_apply]
      linarith
    have hcoef : cf (alt (rhoV n) * χ) (κ + rhoV n) = cf χ κ := by
      rw [(cfBasic n).2.2.2.2.2.2.1, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · have e : κ + rhoV n - rhoV n ∘ ⇑(1 : Equiv.Perm (Fin n)) = κ := by
          funext a
          simp
        rw [e]
        simp [sg]
      · intro w _ hw
        have hz : cf χ (κ + rhoV n - rhoV n ∘ ⇑w) = 0 := by
          by_contra hc
          have h1 := character_support_pairing_le_of_strict_anti κ χ hκ h (rhoV n) hρ _ hc
          have h2 := (rearr n).1 (rhoV n) (rhoV n) hρ.antitone hρ.antitone w
          simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, mul_sub, mul_add,
            Finset.sum_add_distrib, Finset.sum_sub_distrib] at h1
          exact hw (h2.2 hρ hρ (by linarith [h2.1]))
        rw [hz, mul_zero]
      · intro h1
        exact absurd (Finset.mem_univ _) h1
    rw [← hcoef, h]
    exact ((cfBasic n).2.2.2.2.2.2.2.2.2.2.2.1 _ hs).1
  · intro hS ξ hξ
    obtain ⟨w, hw⟩ := ((rearr n).2.1 ξ).2.1
    have hanti : Antitone (domC ξ) := ((rearr n).2.1 ξ).1
    have hc : cf χ (domC ξ) ≠ 0 := by
      rw [hw, hS w ξ]
      exact hξ
    have h1 := character_support_pairing_le_of_antitone κ χ hκ h (domC ξ) hanti (domC ξ) hc
    have h2 := ((rearr n).2.2.2.2.2 (domC ξ) κ (by
      simp only [nsq, sq]
      exact h1)).1
    rw [((rearr n).2.1 ξ).2.2.2.2] at h2
    exact h2
end
end

section

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem mem_lo {n : ℕ} (S : Finset (Fin n)) (hS : ∀ b ∈ S, ∀ c, c ≤ b → c ∈ S) (c : Fin n) :
    c ∈ S ↔ (c : ℕ) < S.card := by
  constructor
  · intro hc
    have hsub : Finset.Iic c ⊆ S := fun b hb => hS c hc b (Finset.mem_Iic.1 hb)
    have h := Finset.card_le_card hsub
    rw [Fin.card_Iic] at h
    omega
  · intro hlt
    by_contra hc
    have hsub : S ⊆ Finset.Iio c := fun b hb => Finset.mem_Iio.2 (by
      by_contra h
      exact hc (hS b hb c (not_lt.1 h)))
    have h := Finset.card_le_card hsub
    rw [Fin.card_Iio] at h
    omega

private theorem mem_hi {n : ℕ} (S : Finset (Fin n)) (hS : ∀ b ∈ S, ∀ c, b ≤ c → c ∈ S) (c : Fin n) :
    c ∈ S ↔ n ≤ (c : ℕ) + S.card := by
  constructor
  · intro hc
    have hsub : Finset.Ici c ⊆ S := fun b hb => hS c hc b (Finset.mem_Ici.mp hb)
    have := Finset.card_le_card hsub
    rw [Fin.card_Ici] at this
    omega
  · intro hle
    by_contra hc
    have hsub : S ⊆ Finset.Ioi c := by
      intro b hb
      rw [Finset.mem_Ioi]
      by_contra hbc
      exact hc (hS b hb c (not_lt.mp hbc))
    have := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at this
    have := c.isLt
    omega

private theorem harmonic_dominant_weight {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (L : Fin n → ℕ) (hL : IsLev lam L) :
    Dom (muQ lam L) ∧ domC (muQ lam L - rhoV n) + rhoV n = twoL lam := by
  obtain ⟨hmono, hlev⟩ := hL
  obtain ⟨D, hD⟩ : ∃ D : Fin n → ℕ, ∀ a, D a = #{b | L b < L a} := ⟨_, fun _ => rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Fin n → ℕ, ∀ a, U a = #{b | L a < L b} := ⟨_, fun _ => rfl⟩
  have hDlo : ∀ a c, L c < L a ↔ (c : ℕ) < D a := by
    intro a c
    have h := mem_lo (Finset.filter (fun b => L b < L a) Finset.univ)
      (fun b hb c hcb => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact lt_of_le_of_lt (hmono hcb) hb) c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    rw [hD]
    exact h
  have hUhi : ∀ a c, L a < L c ↔ n ≤ (c : ℕ) + U a := by
    intro a c
    have h := mem_hi (Finset.filter (fun b => L a < L b) Finset.univ)
      (fun b hb c hcb => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact lt_of_lt_of_le hb (hmono hcb)) c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    rw [hU]
    exact h
  have hDa : ∀ a : Fin n, D a ≤ a := fun a => not_lt.mp (fun h => lt_irrefl _ ((hDlo a a).mpr h))
  have hUa : ∀ a : Fin n, (a : ℕ) + U a < n := fun a => not_le.mp (fun h => lt_irrefl _ ((hUhi a a).mpr h))
  let f : Fin n → Fin n := fun a => ⟨D a + (n - 1 - U a) - a, by
    have := hDa a
    have := hUa a
    omega⟩
  have hfv : ∀ a, ((f a : Fin n) : ℕ) = D a + (n - 1 - U a) - a := fun a => rfl
  have hLf : ∀ a, L (f a) = L a := by
    intro a
    rcases lt_trichotomy (L (f a)) (L a) with h | h | h
    · have h1 := (hDlo a (f a)).mp h
      rw [hfv] at h1
      have := hDa a
      have := hUa a
      omega
    · exact h
    · have h1 := (hUhi a (f a)).mp h
      rw [hfv] at h1
      have := hDa a
      have := hUa a
      omega
  have hDf : ∀ a, D (f a) = D a := by
    intro a
    rw [hD, hD, hLf]
  have hUf : ∀ a, U (f a) = U a := by
    intro a
    rw [hU, hU, hLf]
  have hinv : Function.Involutive f := by
    intro a
    apply Fin.ext
    rw [hfv (f a), hDf, hUf, hfv]
    have := hDa a
    have := hUa a
    omega
  refine ⟨fun a b hab => ?_, ?_⟩
  · have hLab := hmono hab.le
    have hlab := hl hab.le
    have hUab : U b ≤ U a := by
      rw [hU, hU]
      refine Finset.card_le_card (fun c hc => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact lt_of_le_of_lt hLab hc
    have hDab : D a ≤ D b := by
      rw [hD, hD]
      refine Finset.card_le_card (fun c hc => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact lt_of_lt_of_le hc hLab
    have e1 : ((lam a - lam b).toNat : ℤ) = lam a - lam b := Int.toNat_of_nonneg (by omega)
    have e2 : (((lam a - lam b).toNat : ℕ) : ℝ) = (lam a : ℝ) - lam b := by
      have h := congrArg (Int.cast : ℤ → ℝ) e1
      push_cast at h
      exact h
    refine ⟨2 * (lam a - lam b).toNat + (U a - U b) + (D b - D a), ?_⟩
    simp only [muQ, rhoU]
    rw [← hU a, ← hU b, ← hD a, ← hD b]
    push_cast [Nat.cast_sub hUab, Nat.cast_sub hDab, e2]
    ring
  · obtain ⟨y, hy⟩ : ∃ y : Wt n, ∀ a, y a = 2 * (lam a : ℝ) + rhoV n a := ⟨_, fun _ => rfl⟩
    have hyA : Antitone y := by
      intro a b hab
      rw [hy, hy]
      have h1 : (lam b : ℝ) ≤ lam a := by exact_mod_cast hl hab
      have h2 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
      simp only [rhoV]
      linarith
    have hx : ∀ a, (muQ lam L - rhoV n) (f a) = y a := by
      intro a
      have hnat : ((f a : ℕ)) + a + 1 + U a = D a + n := by
        rw [hfv]
        have := hDa a
        have := hUa a
        omega
      have hreal : (((f a : ℕ)) : ℝ) + ((a : ℕ) : ℝ) + 1 + (U a : ℝ) = (D a : ℝ) + n := by
        exact_mod_cast hnat
      simp only [Pi.sub_apply, muQ, rhoU, rhoV]
      rw [← hU (f a), ← hD (f a), hUf, hDf, hlev _ _ (hLf a), hy]
      simp only [rhoV]
      linarith
    let w : Equiv.Perm (Fin n) := Function.Involutive.toPerm f hinv
    have hxy : muQ lam L - rhoV n = y ∘ w := by
      funext a
      have h := hx (f a)
      rw [hinv a] at h
      exact h
    have R := (rearr n).2.1 y
    rw [hxy, R.2.2.2.1 w, R.2.2.1 hyA]
    funext a
    simp only [Pi.add_apply, twoL, hy]
    ring

theorem UpperTheory.RealTr.harmDom :
    ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ μ ∈ harmSet lam, Dom μ ∧ domC (μ - rhoV n) + rhoV n = twoL lam := by
  intro n lam hl μ hμ
  simp only [harmSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hμ
  obtain ⟨lev, hlev, rfl⟩ := hμ
  exact harmonic_dominant_weight lam hl _ hlev
end
end
