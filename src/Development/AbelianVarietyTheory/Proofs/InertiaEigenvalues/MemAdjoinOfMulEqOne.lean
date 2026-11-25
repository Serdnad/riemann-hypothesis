module

import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitBasePointAdjoinTwistedSigma
import Mathlib.Tactic.Linter.Style

@[expose] public section

namespace GlobalTheory.UnitLemma.TwistUnit

open GlobalTheory.UnitLemma Polynomial

theorem adjoin_stab {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {s : A} (L : Submodule O A)
    (hL : ∀ y ∈ L, s * y ∈ L) {a : A} (ha : a ∈ Algebra.adjoin O {s}) : ∀ y ∈ L, a * y ∈ L := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx; exact hL
  | algebraMap r =>
    intro y hy
    rw [← Algebra.smul_def]; exact L.smul_mem r hy
  | add x z _ _ hx hz =>
    intro y hy
    rw [add_mul]; exact L.add_mem (hx y hy) (hz y hy)
  | mul x z _ _ hx hz =>
    intro y hy
    rw [mul_assoc]; exact hx _ (hz y hy)

variable {K : UQ}

theorem trace_σ (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  first | exact _root_.GlobalTheory.UnitLemma.Basic.trace_sigma | exact @_root_.GlobalTheory.UnitLemma.Basic.trace_sigma | apply _root_.GlobalTheory.UnitLemma.Basic.trace_sigma <;> assumption

theorem mem_range_c (e : K.E) : K.c e ∈ (algebraMap K.O K.E).range ↔ e ∈ (algebraMap K.O K.E).range := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := K.c_int a
    refine ⟨b, ?_⟩
    rw [← hb, ha, K.c_c]
  · rintro ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := K.c_int a
    exact ⟨b, hb.symm⟩

theorem trace_σ_mem (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) ∈ (algebraMap K.O K.E).range ↔
      Algebra.trace K.E B.A a ∈ (algebraMap K.O K.E).range := by
  rw [trace_σ, mem_range_c]

theorem twisted_unit_eq_unit : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g →
    ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧
      ∀ x : B.Aˣ, B.σ (x : B.A) = x →
        {L : Submodule K.O B.A | IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L,
          B.herm (β₀ * x) y z ∈ (algebraMap K.O K.E).range} = B.X x := by
  intro K B hg hs hi ε hε
  obtain ⟨β₀, hβ, hb1, hb2⟩ := _root_.GlobalTheory.UnitLemma.UnitBase.exists_unit_base K B hg hs hi ε hε
  refine ⟨β₀, hβ, fun x hx => ?_⟩
  set R := (algebraMap K.O K.E).range with hR
  set T := Algebra.trace K.E B.A with hT
  have hεT : ∀ a, T (ε * a) ∈ R ↔ T a ∈ R := by
    intro a
    rcases hε with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, map_neg, neg_mem_iff]
  have hstab : ∀ L : Submodule K.O B.A, (∀ y ∈ L, B.g * y ∈ L) → ∀ w : B.A,
      ((∀ y ∈ L, T ((β₀ : B.A) * x * y * B.σ w) ∈ R) ↔ ∀ y ∈ L, T ((x : B.A) * y * B.σ w) ∈ R) := by
    intro L hL w
    have s1 := adjoin_stab L hL hb1
    have s2 := adjoin_stab L hL hb2
    constructor
    · intro h y hy
      have := h _ (s2 y hy)
      have e : (β₀ : B.A) * x * (((β₀⁻¹ : B.Aˣ) : B.A) * y) * B.σ w = x * y * B.σ w := by
        have := β₀.mul_inv
        linear_combination (↑x * y * B.σ w) * this
      rwa [e] at this
    · intro h y hy
      have := h _ (s1 y hy)
      rwa [show (x : B.A) * ((β₀ : B.A) * y) * B.σ w = β₀ * x * y * B.σ w by ring] at this
  have hX' : ∀ (L : Submodule K.O B.A) (w : B.A),
      ((∀ y ∈ L, T ((x : B.A) * w * B.σ y) ∈ R) ↔ ∀ y ∈ L, T ((x : B.A) * y * B.σ w) ∈ R) := by
    intro L w
    refine forall₂_congr fun y _ => ?_
    rw [← trace_σ_mem B]
    rw [show B.σ ((x : B.A) * w * B.σ y) = x * y * B.σ w by
      rw [map_mul, map_mul, hx, B.σ_σ]; ring]
  have hsym : ∀ a b : B.A, T ((β₀ : B.A) * x * a * B.σ b) ∈ R ↔
      T ((β₀ : B.A) * x * (B.g * b) * B.σ a) ∈ R := by
    intro a b
    rw [← trace_σ_mem B ((β₀ : B.A) * x * a * B.σ b),
      show B.σ ((β₀ : B.A) * x * a * B.σ b) = ε * ((β₀ : B.A) * x * (B.g * b) * B.σ a) by
        rw [map_mul, map_mul, map_mul, hβ, hx, B.σ_σ]; ring, hεT]
  have hgg : B.σ B.g * B.g = 1 := by rw [mul_comm]; exact hg
  have hgad : B.g ∈ Algebra.adjoin K.O {B.σ B.g} := _root_.GlobalTheory.UnitLemma.UnitBase.mem_adjoin_of_mul_eq_one' hgg hi
  ext L
  simp only [Set.mem_setOf_eq, InvAlg.X, InvAlg.herm, ← hT, ← hR]
  constructor
  · rintro ⟨hLat, hU⟩
    have h1 : ∀ y ∈ L, B.σ B.g * y ∈ L := by
      intro y hy
      rw [hU]
      intro y' hy'
      rw [hsym, show (β₀ : B.A) * x * (B.g * (B.σ B.g * y)) * B.σ y' = β₀ * x * y * B.σ y' by
        linear_combination ((β₀ : B.A) * x * y * B.σ y') * hg]
      exact (hU y').1 hy' y hy
    have h2 : ∀ y ∈ L, B.g * y ∈ L := adjoin_stab L h1 hgad
    refine ⟨hLat, h2, fun y => ?_⟩
    rw [hX' L y, ← hstab L h2, ← hU]
  · rintro ⟨hLat, h2, hXc⟩
    refine ⟨hLat, fun z => ?_⟩
    rw [hstab L h2, ← hX', ← hXc]

end GlobalTheory.UnitLemma.TwistUnit
