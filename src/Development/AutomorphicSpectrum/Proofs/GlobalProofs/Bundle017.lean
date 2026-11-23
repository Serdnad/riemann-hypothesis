module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle016
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CohomologicalDimensionTopologicalIso
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.Chebotarev.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet

@[expose] public section

section

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem classWeight_relation (F : Type) [Field F] [NumberField F] (𝔣 𝔠 A B : Ideal (𝓞 F)) (hc : (Ideal.absNorm 𝔠).Prime)
    (e : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} ≃
      {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠}) (he : ∀ J, (e J).1 = 𝔠 * J.1)
    (s : ℂ) (t : ℂ) (_hs : 1 < s.re)
    (hA : Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)))
    (hB : Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)))
    (ht : HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} =>
      (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) t) :
    ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (1 - s) *
        (∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) -
      (∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) = t := by
  classical
  have hp0 : ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne_zero
  have hf1 : (fun J : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} =>
      ((Ideal.absNorm (e J).1 : ℕ) : ℂ) ^ (-s)) = fun J =>
      ((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s) := by
    funext J
    rw [he J, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  have h1 : HasSum (fun J : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A} =>
      ((Ideal.absNorm (e J).1 : ℕ) : ℂ) ^ (-s))
      (((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) *
        ∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
    rw [hf1]
    exact hA.hasSum.mul_left _
  have h2 := (e.hasSum_iff (f := fun I : {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠} =>
      ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s))).mp h1
  have hι : Function.Injective (fun I : {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠} =>
      (⟨I.1, I.2.1⟩ : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B})) := by
    intro a b hab
    apply Subtype.ext
    have h := congrArg Subtype.val hab
    exact h
  have hf3 : ((fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} =>
      if I.1 ≤ 𝔠 then ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) else 0) ∘
      (fun I : {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠} =>
      (⟨I.1, I.2.1⟩ : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B}))) =
      fun I : {I : Ideal (𝓞 F) // (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B) ∧ I ≤ 𝔠} =>
      ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
    funext I
    simp only [Function.comp_apply, if_pos I.2.2]
  have h3 : HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} =>
      if I.1 ≤ 𝔠 then ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) else 0)
      (((Ideal.absNorm 𝔠 : ℕ) : ℂ) ^ (-s) *
        ∑' I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I A}, ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
    refine (hι.hasSum_iff ?_).mp ?_
    · intro x hx
      rw [if_neg]
      intro hle
      exact hx ⟨⟨x.1, x.2, hle⟩, rfl⟩
    · rw [hf3]
      exact h2
  have h4 := (h3.mul_left ((Ideal.absNorm 𝔠 : ℕ) : ℂ)).sub hB.hasSum
  have hf5 : (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I B} =>
      (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) =
      fun I => ((Ideal.absNorm 𝔠 : ℕ) : ℂ) * (if I.1 ≤ 𝔠 then ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) else 0) -
        ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s) := by
    funext I
    unfold classWeight
    split_ifs <;> push_cast <;> ring
  rw [hf5] at ht
  rw [ht.unique h4, sub_eq_add_neg (1 : ℂ) s, Complex.cpow_add _ _ hp0, Complex.cpow_one, mul_assoc]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end

section

set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

variable {V : Type} [AddCommGroup V] [Module ℚ V]

def coneOn (s : Finset V) : Set V :=
  {x | ∃ t : V → ℚ, (∀ i ∈ s, 0 < t i) ∧ x = ∑ i ∈ s, t i • i}

def SignConst (l : V →ₗ[ℚ] ℚ) (C : Set V) : Prop :=
  (∀ x ∈ C, l x = 0) ∨ (∀ x ∈ C, 0 < l x) ∨ (∀ x ∈ C, l x < 0)

inductive Tile (P : Set V) (Q : Set V → Prop) : Set V → Prop
  | empty : Tile P Q ∅
  | cone (s : Finset V) (hli : LinearIndepOn ℚ id (s : Set V)) (hP : (s : Set V) ⊆ P) (hQ : Q (coneOn s)) :
      Tile P Q (coneOn s)
  | union {A B : Set V} (hA : Tile P Q A) (hB : Tile P Q B) (hAB : Disjoint A B) : Tile P Q (A ∪ B)

def posCone (F : Type) [Field F] [NumberField F] : ConvexCone ℚ F where
  carrier := {x | TotPos F x}
  smul_mem' := by
    intro c hc x hx σ
    have h : σ (c • x) = (c : ℝ) * σ x := by
      rw [Rat.smul_def, map_mul, map_ratCast]
    rw [h]
    exact mul_pos (by exact_mod_cast hc) (hx σ)
  add_mem' := by
    intro x hx y hy σ
    rw [map_add (f := _)]
    exact add_pos (hx σ) (hy σ)

def congSubgroup {F : Type} [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)) : Subgroup (𝓞 F)ˣ where
  carrier := congUnits 𝔣
  mul_mem' := by
    intro a b ha hb
    refine ⟨?_, fun σ => ?_⟩
    · have h : ((a * b : (𝓞 F)ˣ) : 𝓞 F) - 1 = (a : 𝓞 F) * ((b : 𝓞 F) - 1) + ((a : 𝓞 F) - 1) := by
        rw [Units.val_mul]; ring
      rw [h]
      exact 𝔣.add_mem (𝔣.mul_mem_left _ hb.1) ha.1
    · have h : (((a * b : (𝓞 F)ˣ) : 𝓞 F) : F) = ((a : 𝓞 F) : F) * ((b : 𝓞 F) : F) := by
        rw [Units.val_mul]; simp
      rw [h, map_mul]
      exact mul_pos (ha.2 σ) (hb.2 σ)
  one_mem' := by
    refine ⟨by simp, fun σ => ?_⟩
    simp
  inv_mem' := by
    intro a ha
    refine ⟨?_, fun σ => ?_⟩
    · have h : ((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) - 1 = -(((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((a : 𝓞 F) - 1)) := by
        have : ((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (a : 𝓞 F) = 1 := by simp
        linear_combination this
      rw [h]
      exact 𝔣.neg_mem (𝔣.mul_mem_left _ ha.1)
    · have h1 : (((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((a : 𝓞 F) : F) = 1 := by
        have : ((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (a : 𝓞 F) = 1 := by simp
        exact_mod_cast congrArg (fun z : 𝓞 F => (z : F)) this
      have h2 := congrArg σ h1
      rw [map_mul, map_one] at h2
      have h3 := ha.2 σ
      by_contra hn
      have : σ (((a⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * σ ((a : 𝓞 F) : F) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hn) h3.le
      linarith

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
end
end

section

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem norm_natCast_cpow_neg (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : -s ≠ 0 := fun h => by
      have : s = 0 := neg_eq_zero.mp h
      simp [this] at hs
      linarith
    have h1 : -s.re ≠ 0 := by linarith
    simp [Complex.zero_cpow h0, Real.zero_rpow h1]
  · simpa using Complex.norm_natCast_cpow_of_pos hn (-s)

theorem classSummable : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 : Ideal (𝓞 F)) (J : Type) [Fintype J]
    (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → ∀ s : ℂ, 1 < s.re →
      Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
  intro F _ _ _ 𝔣 𝔞 𝔟 J _ r y v _ s hs
  have h := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).subtype
    (fun I : Ideal (𝓞 F) => CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞)
  refine Summable.of_norm (h.congr fun I => ?_)
  exact (norm_natCast_cpow_neg _ hs).symm

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end

section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global FiniteSubfield ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.CompanionTheory.GSCd GroundTheory.Global.IdeleGroup GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped DirectSum

theorem _root_.GlobalTheory.T.galois_unramified_outside_descends_finite : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → ∃ (K : FiniteSubfield) (S' : Finset (HeightOneSpectrum (𝓞 K.1))), ContainsAbove S' l ∧ Nonempty (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ* Gs K S') := by
  first | exact @GlobalTheory.CompanionTheory.GSCd.Transport.exists_gs_transport | exact GlobalTheory.CompanionTheory.GSCd.Transport.exists_gs_transport | (intros; apply GlobalTheory.CompanionTheory.GSCd.Transport.exists_gs_transport <;> assumption)
end
