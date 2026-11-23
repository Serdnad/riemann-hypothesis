module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle455
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

theorem _root_.GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_second_third_eq_zero : ∀ {R : Type} [CommRing R] {d : ℕ} (c : MvPowerSeries (Fin d ⊕ Fin d) R) (a b e : Fin d →₀ ℕ), a ≠ 0 → coeff (Finsupp.sumElim a (Finsupp.sumElim b e)) (at2 c x2 x3) = 0 := by
  first | exact @GlobalTheory.Katz.coeff_at2_x2_x3_eq_zero_of_first_ne_zero | exact GlobalTheory.Katz.coeff_at2_x2_x3_eq_zero_of_first_ne_zero | (intros; apply GlobalTheory.Katz.coeff_at2_x2_x3_eq_zero_of_first_ne_zero <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.coeff_powerSeriesEvalTwoGroups_single_pair : ∀ (R : Type) [CommRing R] (d : ℕ) (c : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d) (γ : Fin d ⊕ Fin d →₀ ℕ), coeff γ (at2 c (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R)) (Pi.single m (X (Sum.inr m)))) = if γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) + Finsupp.single (Sum.inr m) (γ (Sum.inr m)) then coeff γ c else 0 := by
  first | exact @GlobalTheory.coeff_at2_single_X_inl_inr | exact GlobalTheory.coeff_at2_single_X_inl_inr | (intros; apply GlobalTheory.coeff_at2_single_X_inl_inr <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.isCommFormalGroupLaw_map : ∀ (R S : Type) [CommRing R] [CommRing S] (σ : R →+* S) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → IsLaw (fun i => MvPowerSeries.map σ (μ i)) := by
  first | exact @GlobalTheory.Katz.isLaw_map | exact GlobalTheory.Katz.isLaw_map | (intros; apply GlobalTheory.Katz.isLaw_map <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (u' : σ → MvPowerSeries τ k), (∀ i, constantCoeff (u i) = 0) → (∀ i, Red p (u i) (u' i)) → (∀ (f : MvPowerSeries (σ) (Fr p k)) f', Red p f f' → Red p (subst u f) (subst u' f')) ∧ ∀ (c : WittVector p k) (f : MvPowerSeries (σ) (Fr p k)), f ∈ intBy p k σ c → subst u f ∈ intBy p k τ c := by
  first | exact @GlobalTheory.Katz.red_subst | exact GlobalTheory.Katz.red_subst | (intros; apply GlobalTheory.Katz.red_subst <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], ∀ (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (i : σ), evA k x hx (X i) = x i := by
  first | exact @GlobalTheory.Katz.evA_X | exact GlobalTheory.Katz.evA_X | (intros; apply GlobalTheory.Katz.evA_X <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

namespace GlobalTheory.Katz.RedCob

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ τ : Type} {d : ℕ}

variable [PerfectRing k p]

end GlobalTheory.Katz.RedCob

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
private theorem red_lift_self [CharP k p] {σ : Type} (f : MvPowerSeries σ k) :
    _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.lift p f) f := by
  unfold _root_.GlobalTheory.Katz.Red
  intro α
  exact ⟨WittVector.teichmuller p (coeff α f), _root_.GlobalTheory.Katz.coeff_lift p f α,
    by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
variable [CharP k p] [PerfectRing k p] in
omit [CharP k p] [PerfectRing k p] in
private theorem constantCoeff_at2_eq_zero {R : Type} [CommRing R] {d : ℕ} {τ : Type}
    {f : MvPowerSeries (Fin d ⊕ Fin d) R} {a b : Fin d → MvPowerSeries τ R}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (hf : constantCoeff f = 0) : constantCoeff (_root_.GlobalTheory.Katz.at2 f a b) = 0 := by
  have h : ∀ s, constantCoeff (Sum.elim a b s) = 0 := by
    rintro (i | i)
    · exact ha₀ i
    · exact hb₀ i
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h hf

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
variable [CharP k p] [PerfectRing k p] in
private theorem red_at2_of_red {d : ℕ} {τ : Type}
    {f : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)}
    {f' : MvPowerSeries (Fin d ⊕ Fin d) k}
    {a b : Fin d → MvPowerSeries τ (_root_.GlobalTheory.Katz.Fr p k)} {a' b' : Fin d → MvPowerSeries τ k}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (ha : ∀ i, _root_.GlobalTheory.Katz.Red p (a i) (a' i))
    (hb : ∀ i, _root_.GlobalTheory.Katz.Red p (b i) (b' i))
    (hf : _root_.GlobalTheory.Katz.Red p f f') :
    _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.at2 f a b)
      (_root_.GlobalTheory.Katz.at2 f' a' b') := by
  unfold _root_.GlobalTheory.Katz.at2
  refine (_root_.GlobalTheory.Katz.red_subst p k (Fin d ⊕ Fin d) τ (Sum.elim a b)
    (Sum.elim a' b') ?_ ?_).1 f f' hf
  · rintro (i | i)
    · exact ha₀ i
    · exact hb₀ i
  · rintro (i | i)
    · exact ha i
    · exact hb i

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
private theorem red_X' {σ : Type} (s : σ) :
    _root_.GlobalTheory.Katz.Red p (X s : MvPowerSeries σ (_root_.GlobalTheory.Katz.Fr p k))
      (X s) := by
  classical
  unfold _root_.GlobalTheory.Katz.Red
  intro α
  refine ⟨if α = Finsupp.single s 1 then 1 else 0, ?_, ?_⟩
  · rw [coeff_X]; split_ifs <;> simp
  · rw [coeff_X]; split_ifs <;> simp

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
private theorem red_sub_divisor {σ : Type} {f g : MvPowerSeries σ (_root_.GlobalTheory.Katz.Fr p k)}
    {f' g' : MvPowerSeries σ k} (hf : _root_.GlobalTheory.Katz.Red p f f')
    (hg : _root_.GlobalTheory.Katz.Red p g g') :
    _root_.GlobalTheory.Katz.Red p (f - g) (f' - g') := by
  unfold _root_.GlobalTheory.Katz.Red at *
  intro α
  obtain ⟨v, hv, hv'⟩ := hf α
  obtain ⟨w, hw, hw'⟩ := hg α
  exact ⟨v - w, by rw [map_sub, map_sub, hv, hw], by rw [map_sub, map_sub, hv', hw']⟩

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
private theorem red_add_divisor {σ : Type} {f g : MvPowerSeries σ (_root_.GlobalTheory.Katz.Fr p k)}
    {f' g' : MvPowerSeries σ k} (hf : _root_.GlobalTheory.Katz.Red p f f')
    (hg : _root_.GlobalTheory.Katz.Red p g g') :
    _root_.GlobalTheory.Katz.Red p (f + g) (f' + g') := by
  unfold _root_.GlobalTheory.Katz.Red at *
  intro α
  obtain ⟨v, hv, hv'⟩ := hf α
  obtain ⟨w, hw, hw'⟩ := hg α
  exact ⟨v + w, by rw [map_add (f := _), map_add (f := _), hv, hw], by rw [map_add (f := _), map_add (f := _), hv', hw']⟩

open MvPowerSeries in
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] in
variable [CharP k p] [PerfectRing k p] in
private theorem at2_mem_intBy_of_red {d : ℕ} {τ : Type}
    {f : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)}
    {a b : Fin d → MvPowerSeries τ (_root_.GlobalTheory.Katz.Fr p k)} {a' b' : Fin d → MvPowerSeries τ k}
    (ha₀ : ∀ i, constantCoeff (a i) = 0) (hb₀ : ∀ i, constantCoeff (b i) = 0)
    (ha : ∀ i, _root_.GlobalTheory.Katz.Red p (a i) (a' i))
    (hb : ∀ i, _root_.GlobalTheory.Katz.Red p (b i) (b' i)) (c : WittVector p k)
    (hf : f ∈ _root_.GlobalTheory.Katz.intBy p k (Fin d ⊕ Fin d) c) :
    _root_.GlobalTheory.Katz.at2 f a b ∈ _root_.GlobalTheory.Katz.intBy p k τ c := by
  unfold _root_.GlobalTheory.Katz.at2
  refine (_root_.GlobalTheory.Katz.red_subst p k (Fin d ⊕ Fin d) τ (Sum.elim a b)
    (Sum.elim a' b') ?_ ?_).2 c f hf
  · rintro (i | i)
    · exact ha₀ i
    · exact hb₀ i
  · rintro (i | i)
    · exact ha i
    · exact hb i


open CategoryTheory TensorProduct MvPowerSeries in
set_option autoImplicit false in
theorem _root_.GlobalTheory.Katz.red_coboundaries : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), (∀ i, constantCoeff (μ i) = 0) → (∀ g c, _root_.GlobalTheory.Katz.Red p g c → _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob2 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) g) (_root_.GlobalTheory.Katz.cob2 μ c) ∧ _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.swap g) (_root_.GlobalTheory.Katz.swap c)) ∧ (∀ b b', _root_.GlobalTheory.Katz.Red p b b' → _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.cob1 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) b) (_root_.GlobalTheory.Katz.cob1 μ b') ∧ _root_.GlobalTheory.Katz.RedV p (_root_.GlobalTheory.Katz.lin b) (_root_.GlobalTheory.Katz.lin b')) ∧ (∀ i, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) _root_.GlobalTheory.Katz.x1 (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3) i) (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x2 _root_.GlobalTheory.Katz.x3) i) ∧ _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2) _root_.GlobalTheory.Katz.x3 i) (_root_.GlobalTheory.Katz.op μ (_root_.GlobalTheory.Katz.op μ _root_.GlobalTheory.Katz.x1 _root_.GlobalTheory.Katz.x2) _root_.GlobalTheory.Katz.x3 i)) ∧ ∀ (c : WittVector p k) g, g ∈ _root_.GlobalTheory.Katz.intBy p k (Fin d ⊕ Fin d) c → _root_.GlobalTheory.Katz.cob2 (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) g ∈ _root_.GlobalTheory.Katz.intBy p k _ c ∧ _root_.GlobalTheory.Katz.swap g ∈ _root_.GlobalTheory.Katz.intBy p k _ c := by
  intro p _ k _ _ _ d μ hμ
  have hL₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.lift p (μ i)) = 0 := fun i =>
    _root_.GlobalTheory.Katz.constantCoeff_lift p (hμ i)
  have hL : ∀ i, _root_.GlobalTheory.Katz.Red p (_root_.GlobalTheory.Katz.lift p (μ i)) (μ i) :=
    fun i => red_lift_self (μ i)
  have hop : ∀ {τ : Type} (a b : Fin d → MvPowerSeries τ (_root_.GlobalTheory.Katz.Fr p k))
      (a' b' : Fin d → MvPowerSeries τ k),
      (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
      (∀ i, _root_.GlobalTheory.Katz.Red p (a i) (a' i)) →
      (∀ i, _root_.GlobalTheory.Katz.Red p (b i) (b' i)) →
      (∀ i, constantCoeff (_root_.GlobalTheory.Katz.op
        (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) a b i) = 0) ∧
      ∀ i, _root_.GlobalTheory.Katz.Red p
        (_root_.GlobalTheory.Katz.op (fun i => _root_.GlobalTheory.Katz.lift p (μ i)) a b i)
        (_root_.GlobalTheory.Katz.op μ a' b' i) := by
    intro τ a b a' b' ha₀ hb₀ ha hb
    exact ⟨fun i => constantCoeff_at2_eq_zero ha₀ hb₀ (hL₀ i),
      fun i => red_at2_of_red ha₀ hb₀ ha hb (hL i)⟩
  have hx₁₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.x1 i :
      MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i =>
    constantCoeff_X _
  have hx₂₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.x2 i :
      MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i =>
    constantCoeff_X _
  have hx₃₀ : ∀ i, constantCoeff (_root_.GlobalTheory.Katz.x3 i :
      MvPowerSeries (Fin d ⊕ Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i =>
    constantCoeff_X _
  have hx₁ : ∀ i, _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.x1 (R := _root_.GlobalTheory.Katz.Fr p k) (d := d) i)
      (_root_.GlobalTheory.Katz.x1 (R := k) i) := fun i => red_X' _
  have hx₂ : ∀ i, _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.x2 (R := _root_.GlobalTheory.Katz.Fr p k) (d := d) i)
      (_root_.GlobalTheory.Katz.x2 (R := k) i) := fun i => red_X' _
  have hx₃ : ∀ i, _root_.GlobalTheory.Katz.Red p
      (_root_.GlobalTheory.Katz.x3 (R := _root_.GlobalTheory.Katz.Fr p k) (d := d) i)
      (_root_.GlobalTheory.Katz.x3 (R := k) i) := fun i => red_X' _
  obtain ⟨h₁₂₀, h₁₂⟩ := hop _ _ _ _ hx₁₀ hx₂₀ hx₁ hx₂
  obtain ⟨h₂₃₀, h₂₃⟩ := hop _ _ _ _ hx₂₀ hx₃₀ hx₂ hx₃
  have hl₀ : ∀ i, constantCoeff (X (Sum.inl i) :
      MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i => constantCoeff_X _
  have hr₀ : ∀ i, constantCoeff (X (Sum.inr i) :
      MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k)) = 0 := fun i => constantCoeff_X _
  have hl : ∀ i, _root_.GlobalTheory.Katz.Red p
      (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k))
      (X (Sum.inl i)) := fun i => red_X' _
  have hr : ∀ i, _root_.GlobalTheory.Katz.Red p
      (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) (_root_.GlobalTheory.Katz.Fr p k))
      (X (Sum.inr i)) := fun i => red_X' _
  refine ⟨fun g c hg => ⟨?_, ?_⟩, fun b b' hb => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩,
    fun c g hg => ⟨?_, ?_⟩⟩
  · unfold _root_.GlobalTheory.Katz.cob2
    exact red_sub_divisor (red_add_divisor (red_sub_divisor
      (red_at2_of_red hx₂₀ hx₃₀ hx₂ hx₃ hg)
      (red_at2_of_red h₁₂₀ hx₃₀ h₁₂ hx₃ hg))
      (red_at2_of_red hx₁₀ h₂₃₀ hx₁ h₂₃ hg))
      (red_at2_of_red hx₁₀ hx₂₀ hx₁ hx₂ hg)
  · unfold _root_.GlobalTheory.Katz.swap
    exact red_at2_of_red hr₀ hl₀ hr hl hg
  · unfold _root_.GlobalTheory.Katz.cob1 _root_.GlobalTheory.Katz.inL _root_.GlobalTheory.Katz.inR
    exact red_sub_divisor (red_sub_divisor
      ((_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ μ hL₀ hL).1 b b' hb)
      ((_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ _ hl₀ hl).1 b b' hb))
      ((_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d ⊕ Fin d) _ _ hr₀ hr).1 b b' hb)
  · unfold _root_.GlobalTheory.Katz.lin _root_.GlobalTheory.Katz.RedV
    unfold _root_.GlobalTheory.Katz.Red at hb
    intro i
    exact hb _
  · exact (hop _ _ _ _ hx₁₀ h₂₃₀ hx₁ h₂₃).2 i
  · exact (hop _ _ _ _ h₁₂₀ hx₃₀ h₁₂ hx₃).2 i
  · unfold _root_.GlobalTheory.Katz.cob2
    exact sub_mem (add_mem (sub_mem
      (at2_mem_intBy_of_red hx₂₀ hx₃₀ hx₂ hx₃ c hg)
      (at2_mem_intBy_of_red h₁₂₀ hx₃₀ h₁₂ hx₃ c hg))
      (at2_mem_intBy_of_red hx₁₀ h₂₃₀ hx₁ h₂₃ c hg))
      (at2_mem_intBy_of_red hx₁₀ hx₂₀ hx₁ hx₂ c hg)
  · unfold _root_.GlobalTheory.Katz.swap
    exact at2_mem_intBy_of_red hr₀ hl₀ hr hl c hg
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.subst_sub_subst_integral_of_integral_differential : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u v : σ → MvPowerSeries (τ) (Fr p k)) (w : σ → MvPowerSeries τ k) (f : MvPowerSeries (σ) (Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, Red p (u i) (w i)) → (∀ i, Red p (v i) (w i)) → f ∈ quasiInt p k σ → subst u f - subst v f ∈ intBy p k τ p := by
  first | exact @GlobalTheory.Katz.subst_sub_subst_mem_intBy | exact GlobalTheory.Katz.subst_sub_subst_mem_intBy | (intros; apply GlobalTheory.Katz.subst_sub_subst_mem_intBy <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.Katz.LawMonoid

variable {R : Type} [CommRing R] {d : ℕ}

theorem constantCoeff_bivariateSeriesSubstPair {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : constantCoeff (at2 c u v) = constantCoeff c :=
  (GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d τ τ u v hu hv).2.2.2.1 c

theorem powerSeriesEvalTwoGroups_swapVariableGroups {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : at2 (swap c) u v = at2 c v u :=
  (GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d τ τ u v hu hv).2.2.2.2.1 c

theorem cc_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 := by
  show constantCoeff (at2 (μ i) u v) = 0
  rw [constantCoeff_bivariateSeriesSubstPair hu hv, hμ]

theorem subst_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    {τ τ' : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (a : τ → MvPowerSeries τ' R) (ha : ∀ t, constantCoeff (a t) = 0) (i : Fin d) :
    subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i :=
  GlobalTheory.Katz.SubstCalc.subst_powerSeriesEvalTwoGroups hu hv ha (μ i)

theorem constantCoeff_mvPowerSeries_X_eq_zero {τ : Type} (s : τ) : constantCoeff (X s : MvPowerSeries τ R) = 0 := constantCoeff_X s

theorem mon : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (τ : Type) [Finite τ] (u v w : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, constantCoeff (w i) = 0) → (∀ i, constantCoeff (op μ u v i) = 0) ∧ op μ (op μ u v) w = op μ u (op μ v w) ∧ op μ u v = op μ v u ∧ op μ u (fun _ => 0) = u ∧ ∀ (τ' : Type) (a : τ → MvPowerSeries τ' R), (∀ t, constantCoeff (a t) = 0) → ∀ i, subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i := by
  intro R _ d μ hμ τ _ u v w hu hv hw
  refine ⟨cc_op hμ.const hu hv, ?_, ?_, ?_, fun τ' a ha i => subst_op hu hv a ha i⟩
  ·
    let a : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim v w)
    have ha : ∀ t, constantCoeff (a t) = 0 := by
      intro t; rcases t with t | t | t
      · exact hu t
      · exact hv t
      · exact hw t
    have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
    have h1 : (fun j => subst a ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = u := by
      funext j; simp only [x1]; rw [subst_X hs]; rfl
    have h2 : (fun j => subst a ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = v := by
      funext j; simp only [x2]; rw [subst_X hs]; rfl
    have h3 : (fun j => subst a ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = w := by
      funext j; simp only [x3]; rw [subst_X hs]; rfl
    have hx1 : ∀ j, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    have hx2 : ∀ j, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    have hx3 : ∀ j, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    funext i
    have e := congrArg (fun F => subst a (F i)) hμ.assoc
    try simp only at e
    rw [subst_op (cc_op hμ.const hx1 hx2) hx3 a ha, subst_op hx1 (cc_op hμ.const hx2 hx3) a ha] at e
    have e1 : (fun j => subst a (op μ x1 x2 j)) = op μ u v := by
      funext j; rw [subst_op hx1 hx2 a ha, h1, h2]
    have e2 : (fun j => subst a (op μ x2 x3 j)) = op μ v w := by
      funext j; rw [subst_op hx2 hx3 a ha, h2, h3]
    rw [e1, e2, h1, h3] at e
    exact e
  · funext i
    show at2 (μ i) u v = at2 (μ i) v u
    rw [← powerSeriesEvalTwoGroups_swapVariableGroups hu hv, hμ.comm i]
  ·
    have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
    have hX : ∀ j, constantCoeff ((X j : MvPowerSeries (Fin d) R)) = 0 := fun j => constantCoeff_X j
    have h0 : ∀ j : Fin d, constantCoeff ((fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) j) = 0 := fun _ => map_zero _
    funext i
    have e := congrArg (fun F => subst u (F i)) hμ.unit
    try simp only at e
    rw [subst_op hX h0 u hu, subst_X hs] at e
    have e1 : (fun j => subst u ((X j : MvPowerSeries (Fin d) R))) = u := by
      funext j; rw [subst_X hs]
    have e0 : (fun j : Fin d => subst u ((fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) j)) = fun _ => 0 := by
      funext j; show subst u (0 : MvPowerSeries (Fin d) R) = 0
      rw [← coe_substAlgHom hs]; exact map_zero _
    rw [e1, e0] at e
    exact e

end GlobalTheory.Katz.LawMonoid
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.coboundary_eq_additive_leading_terms : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (N : ℕ), (∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 → coeff α (μ i) = coeff α (addLaw R d i)) → (∀ f : MvPowerSeries (Fin d) R, (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) → ∀ γ : Fin d ⊕ Fin d →₀ ℕ, (γ.degree < N → coeff γ (cob1 μ f) = 0) ∧ (γ.degree ≤ N → coeff γ (cob1 μ f) = coeff γ (cob1 (addLaw R d) f))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → coeff α c = 0) → ∀ γ : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ, γ.degree ≤ N → coeff γ (cob2 μ c) = coeff γ (cob2 (addLaw R d) c) := by
  first | exact @GlobalTheory.CobLead.cob_eq_additive_lead | exact GlobalTheory.CobLead.cob_eq_additive_lead | (intros; apply GlobalTheory.CobLead.cob_eq_additive_lead <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.powerSeriesEvalTwoGroups_rules : ∀ (R : Type) [CommRing R] (d : ℕ) (τ τ' : Type) [Finite τ] (u v : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ f, at2 (inL f) u v = subst u f) ∧ (∀ f, at2 (inR f) u v = subst v f) ∧ (∀ c c', at2 (c + c') u v = at2 c u v + at2 c' u v ∧ at2 (c - c') u v = at2 c u v - at2 c' u v) ∧ (∀ c, constantCoeff (at2 c u v) = constantCoeff c) ∧ (∀ c, at2 (swap c) u v = at2 c v u) ∧ (∀ (e : ℕ) (μ : Fin e → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ f : MvPowerSeries (Fin e) R, at2 (subst μ f) u v = subst (fun i => at2 (μ i) u v) f) ∧ (∀ a : τ → MvPowerSeries τ' R, (∀ t, constantCoeff (a t) = 0) → ∀ c, subst a (at2 c u v) = at2 c (fun i => subst a (u i)) (fun i => subst a (v i))) ∧ ∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, cob2 (addLaw R d) c = 0 → at2 c u v - at2 c (u + u) v + at2 c u (u + v) - at2 c u u = 0 := by
  first | exact @GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt | exact GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt | (intros; apply GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt <;> assumption)
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.CobPull

theorem cob1_subst_eq_pull2_of_isHom_formal : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), ∀ (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (φ : Fin d → MvPowerSeries (Fin d) R), (∀ i, constantCoeff (μ i) = 0) → (∀ i, constantCoeff (ν i) = 0) → IsHom μ ν φ → ∀ f : MvPowerSeries (Fin d) R, cob1 μ (subst φ f) = pull2 φ (cob1 ν f) := by
  intro R _ d μ ν φ hμ hν hφ f
  have hp : HasSubst φ := hasSubst_of_constantCoeff_zero hφ.const
  have hX : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hu : ∀ j, constantCoeff (inL (φ j)) = 0 := fun j => by
    unfold inL
    rw [SubstCalc.constantCoeff_subst_of_zero (fun _ => constantCoeff_X _), hφ.const j]
  have hv : ∀ j, constantCoeff (inR (φ j)) = 0 := fun j => by
    unfold inR
    rw [SubstCalc.constantCoeff_subst_of_zero (fun _ => constantCoeff_X _), hφ.const j]
  obtain ⟨hL, hR, hAS, -, -, hsub, -, -⟩ :=
    SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (fun j => inL (φ j))
      (fun j => inR (φ j)) hu hv
  unfold pull2 cob1
  rw [(hAS _ _).2, (hAS _ _).2, hL, hR, hsub d ν hν f]
  have e1 : subst μ (subst φ f) = subst (fun j => at2 (ν j) (fun j => inL (φ j)) (fun j => inR (φ j))) f := by
    rw [subst_comp_subst_apply hp (hasSubst_of_constantCoeff_zero hμ)]
    congr 1
    funext j
    exact hφ.hom j
  have e2 : inL (subst φ f) = subst (fun j => inL (φ j)) f := by
    unfold inL
    rw [subst_comp_subst_apply hp hX]
  have e3 : inR (subst φ f) = subst (fun j => inR (φ j)) f := by
    unfold inR
    rw [subst_comp_subst_apply hp hY]
  rw [e1, e2, e3]

end GlobalTheory.Katz.CobPull
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.subst_mem_integralDifferentialSubmodule : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (σ τ : Type) [Finite σ] (u : σ → MvPowerSeries (τ) (Fr p k)) (f : MvPowerSeries (σ) (Fr p k)), (∀ i, constantCoeff (u i) = 0) → (∀ i, u i ∈ intBy p k τ 1) → f ∈ quasiInt p k σ → subst u f ∈ quasiInt p k τ := by
  first | exact @GlobalTheory.Katz.subst_mem_quasiInt | exact GlobalTheory.Katz.subst_mem_quasiInt | (intros; apply GlobalTheory.Katz.subst_mem_quasiInt <;> assumption)
end
