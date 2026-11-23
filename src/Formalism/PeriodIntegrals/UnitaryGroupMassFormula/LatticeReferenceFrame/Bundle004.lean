module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct

namespace PI.ScRefExists.Sk

def Ap (I : Formalism.MainNotions.S.AutInst) (p : ℕ) : Subalgebra (𝓞 I.E) I.E where
  carrier := {x | ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E)}
  mul_mem' := by
    rintro x y ⟨s, hs, a, ha⟩ ⟨t, ht, b, hb⟩
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, a * b, ?_⟩
    push_cast at ha hb ⊢
    linear_combination (↑t * y) * ha + (a : I.E) * hb
  add_mem' := by
    rintro x y ⟨s, hs, a, ha⟩ ⟨t, ht, b, hb⟩
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, (t : 𝓞 I.E) * a + (s : 𝓞 I.E) * b, ?_⟩
    push_cast at ha hb ⊢
    linear_combination (↑t : I.E) * ha + (↑s : I.E) * hb
  algebraMap_mem' := by
    intro a
    exact ⟨1, Nat.coprime_one_left p, a, by simp⟩

def LA (I : Formalism.MainNotions.S.AutInst) (p : ℕ) : Submodule (Ap I p) (Fin I.n → I.E) :=
  Submodule.span (Ap I p) (I.L : Set (Fin I.n → I.E))

def ApPID : Prop := ∀ (I : Formalism.MainNotions.S.AutInst) (p : ℕ), p.Prime → IsPrincipalIdealRing (Ap I p)

def WFrame : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (p r k : ℕ) (e f : Fin r → Fin I.n → I.E) (M : ℕ),
    p.Prime → I.n = 2 * r + k + 1 →
    (∀ a b, hG I (e a) (e b) = 0) → (∀ a b, hG I (f a) (f b) = 0) →
    (∀ a b, hG I (e a) (f b) = if a = b then 1 else 0) →
    Nat.Coprime M p → (∀ a, M • e a ∈ I.L ∧ M • f a ∈ I.L) →
    ∃ w wd : Fin (k + 1) → Fin I.n → I.E,
      (∀ i, w i ∈ LA I p ∧ wd i ∈ LA I p) ∧
      (∀ a i, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0 ∧
        hG I (e a) (wd i) = 0 ∧ hG I (f a) (wd i) = 0) ∧
      (∀ i j, hG I (wd i) (w j) = if i = j then 1 else 0) ∧
      ∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) ∧
        y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd)

def PPAssemble : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (p m r k : ℕ) (θ : 𝓞 I.E) (e f : Fin r → Fin I.n → I.E) (M : ℕ)
    (w wd : Fin (k + 1) → Fin I.n → I.E),
    p.Prime → 1 ≤ m → Hyp I (p ^ m) r k θ e f M →
    (∀ i, w i ∈ LA I p ∧ wd i ∈ LA I p) →
    (∀ a i, hG I (e a) (w i) = 0 ∧ hG I (f a) (w i) = 0 ∧
        hG I (e a) (wd i) = 0 ∧ hG I (f a) (wd i) = 0) →
    (∀ i j, hG I (wd i) (w j) = if i = j then 1 else 0) →
    (∀ y ∈ I.L, y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range w) ∧
        y ∈ Submodule.span (Ap I p) (Set.range e ∪ Set.range f ∪ Set.range wd)) →
    Concl I (p ^ m) r k θ e f M

theorem gwpp_of (h1 : WFrame) (h2 : PPAssemble) : GWpp := by
  intro I p m r k θ e f M hp hm hH
  obtain ⟨_, _, _, hn, hee, hff, hef, hM, hL⟩ := id hH
  have hMp : Nat.Coprime M p :=
    Nat.Coprime.coprime_dvd_right (dvd_pow_self p (by omega)) hM
  obtain ⟨w, wd, hw, horth, hdual, hspan⟩ := h1 I p r k e f M hp hn hee hff hef hMp hL
  exact h2 I p m r k θ e f M w wd hp hm hH hw horth hdual hspan

end PI.ScRefExists.Sk
end
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace PI.ScRefExists.Id

theorem locIdem : LocIdem := by
  intro F _ _ v g α β hg hgv hα hβ
  classical
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have memO : ∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 := fun x => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  let ϖ : v.adicCompletionIntegers F := ⟨((g : ℕ) : v.adicCompletion F), (memO _).2 hgv.le⟩
  let aO : v.adicCompletionIntegers F := ⟨α, (memO _).2 hα⟩
  let bO : v.adicCompletionIntegers F := ⟨β, (memO _).2 hβ⟩
  have hϖ : ϖ ≠ 0 := by
    intro h
    have h' : ((g : ℕ) : v.adicCompletion F) = 0 := congrArg Subtype.val h
    exact (Nat.cast_ne_zero.mpr (by omega : g ≠ 0)) h'
  have h1 : ‖(ϖ : v.adicCompletion F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr hgv
  haveI := PI.LocalEndW.isAdicComplete v ϖ hϖ h1
  let f : Polynomial (v.adicCompletionIntegers F) := X ^ 2 - C (1 + ϖ * aO) * X + C (ϖ * bO)
  have hf : f.Monic := by simp only [f]; monicity!
  have h0 : f.eval 0 ∈ Ideal.span {ϖ} := by
    have e : f.eval 0 = bO * ϖ := by
      simp only [f, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C]; ring
    rw [e, Ideal.mem_span_singleton']
    exact ⟨bO, rfl⟩
  have hd : f.derivative.eval 0 = -(1 + ϖ * aO) := by simp [f]
  have hm : Ideal.Quotient.mk (Ideal.span {ϖ}) (-(1 + ϖ * aO)) = -1 := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {ϖ})), ← map_neg, Ideal.Quotient.eq,
      Ideal.mem_span_singleton']
    exact ⟨-aO, by ring⟩
  obtain ⟨ρ, hρ, hρI⟩ := HenselianRing.is_henselian (I := Ideal.span {ϖ}) f hf 0 h0
    (by rw [hd, hm]; exact isUnit_one.neg)
  rw [sub_zero, Ideal.mem_span_singleton'] at hρI
  obtain ⟨r0, rfl⟩ := hρI
  have hroot : (r0 * ϖ) ^ 2 - (1 + ϖ * aO) * (r0 * ϖ) + ϖ * bO = 0 := by
    have h : f.eval (r0 * ϖ) = 0 := hρ
    simpa only [f, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C] using h
  have hu : IsUnit (1 + ϖ * (aO - 2 * r0)) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have hy : Valued.v ((aO - 2 * r0 : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 :=
      (memO _).1 (aO - 2 * r0).2
    have hlt : Valued.v ((ϖ : v.adicCompletion F) *
        ((aO - 2 * r0 : v.adicCompletionIntegers F) : v.adicCompletion F)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hy) hgv
    exact (Valued.v).map_one_add_of_lt hlt
  obtain ⟨U, hU⟩ := hu
  obtain ⟨wO, hwO⟩ : ∃ w : v.adicCompletionIntegers F, w = ((U⁻¹ : (v.adicCompletionIntegers F)ˣ) :
      v.adicCompletionIntegers F) := ⟨_, rfl⟩
  have huw : (1 + ϖ * (aO - 2 * r0)) * wO = 1 := by rw [← hU, hwO]; exact U.mul_inv
  obtain ⟨c1, hc1⟩ : ∃ c : v.adicCompletionIntegers F, c = -(aO - 2 * r0) * wO := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c : v.adicCompletionIntegers F, c = r0 * wO := ⟨_, rfl⟩
  have hA : (1 + ϖ * aO) * (1 + ϖ * c1) ^ 2 - 2 * (1 + ϖ * c1) * (ϖ * c2) = 1 + ϖ * c1 := by
    rw [hc1, hc2]
    linear_combination ((1 + ϖ * (-(aO - 2 * r0) * wO)) * (1 - (1 + ϖ * aO))) * huw
  have hB : (ϖ * c2) ^ 2 - ϖ * bO * (1 + ϖ * c1) ^ 2 = -(ϖ * c2) := by
    rw [hc1, hc2]
    linear_combination (-(r0 * ϖ) * wO + ϖ * bO * (2 * wO - ((1 + ϖ * (aO - 2 * r0)) * wO - 1))) * huw
      + (-wO ^ 2) * hroot
  have hC : (ϖ * c2) ^ 2 - (1 + ϖ * aO) * (ϖ * c2) * (1 + ϖ * c1) + ϖ * bO * (1 + ϖ * c1) ^ 2 = 0 := by
    rw [hc1, hc2]
    linear_combination ((1 + ϖ * aO) * (r0 * ϖ) * wO - 2 * (ϖ * bO) * wO
      + ϖ * bO * ((1 + ϖ * (aO - 2 * r0)) * wO - 1)) * huw + wO ^ 2 * hroot
  refine ⟨(c1 : v.adicCompletion F), (c2 : v.adicCompletion F), (memO _).1 c1.2, (memO _).1 c2.2,
    ?_, ?_, ?_⟩
  · have e := congrArg (v.adicCompletionIntegers F).subtype hA
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_one, map_ofNat] at e
    exact e
  · have e := congrArg (v.adicCompletionIntegers F).subtype hB
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_one, map_ofNat, map_neg] at e
    exact e
  · have e := congrArg (v.adicCompletionIntegers F).subtype hC
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_one, map_ofNat, map_zero] at e
    exact e

end PI.ScRefExists.Id
end
end
