module

public import ReciprocityTheory.DualLattices.Bundle002
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Lemmata.MiscLemmasL.Imports
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

def tot (B : BX R₀) {R : LAlg R₀} {x y : B.G R} (u : B.P R x y) : Σ x y : B.G R, B.P R x y :=
  ⟨x, y, u⟩

def tmap (B : BX R₀) {R S : LAlg R₀} (f : LHom R S) (t : Σ x y : B.G R, B.P R x y) :
    Σ x y : B.G S, B.P S x y :=
  ⟨B.map f t.1, B.map f t.2.1, B.pmap f t.2.2⟩

variable {B : BX R₀} {R S T : LAlg R₀}

end BX

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up.U3

open ReciprocityTheory.PGsh.L2

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]

structure IsTeich (v : Valuation C NNReal) (ω : ZMod p → C) : Prop where
  pow : ∀ a, ω a ^ p = ω a
  cong : ∀ a, v (ω a - (a.val : C)) < 1
  zero : ω 0 = 0
  one : ω 1 = 1
  mul : ∀ a b, ω (a * b) = ω a * ω b
  sep : ∀ a b, a ≠ b → v (ω a - ω b) = 1

namespace IsTeich

variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

theorem int (a : ZMod p) : v (ω a) ≤ 1 := by
  by_cases ha : a = 0
  · rw [ha, hω.zero, map_zero]
    exact zero_le
  · have h := hω.sep a 0 ha
    rw [hω.zero, sub_zero] at h
    exact h.le

theorem v_eq_one {a : ZMod p} (ha : a ≠ 0) : v (ω a) = 1 := by
  have h := hω.sep a 0 ha
  rwa [hω.zero, sub_zero] at h

theorem ne_zero {a : ZMod p} (ha : a ≠ 0) : ω a ≠ 0 := by
  intro h
  have h1 := hω.v_eq_one ha
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem pow_pred {a : ZMod p} (ha : a ≠ 0) : ω a ^ (p - 1) = 1 := by
  have hne := hω.ne_zero ha
  have h1 : ω a ^ (p - 1) * ω a = 1 * ω a := by
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, one_mul]
    exact hω.pow a
  exact mul_right_cancel₀ hne h1

end IsTeich

def wt (ω : ZMod p → C) (a : ZMod p) : C := ω a ^ (2 * p - 3)

def sS (ω : ZMod p → C) : C := ∑ b, wt ω b

def u0 (ω : ZMod p → C) (a : ZMod p) : C := wt ω a - if a = 0 then sS ω else 0

def lam (ω : ZMod p → C) (f : ZMod p → C) : C := ∑ a, u0 ω a * f a

section wt

namespace IsTeich

variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

theorem wt_zero : wt ω 0 = 0 := by
  unfold wt
  rw [hω.zero]
  exact zero_pow (by have := hp.out.two_le; omega)

theorem wt_mul_self {a : ZMod p} (ha : a ≠ 0) : wt ω a * ω a = 1 := by
  unfold wt
  rw [← pow_succ]
  have e : 2 * p - 3 + 1 = (p - 1) * 2 := by
    have := hp.out.two_le
    omega
  rw [e, pow_mul, hω.pow_pred ha, one_pow]

theorem wt_int (a : ZMod p) : v (wt ω a) ≤ 1 := by
  unfold wt
  rw [map_pow]
  exact pow_le_one₀ (zero_le) (hω.int a)

private theorem lam_eq_sum_wt_mul_sub (f : ZMod p → C) : lam ω f = ∑ a, wt ω a * (f a - f 0) := by
  simp [lam, u0, sS, sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

theorem lam_eq (f : ZMod p → C) : lam ω f = ∑ a, wt ω a * (f a - f 0) := by
  exact lam_eq_sum_wt_mul_sub hω f

theorem lam_omega : lam ω ω = (p : C) - 1 := by
  rw [lam_eq_sum_wt_mul_sub hω, hω.zero]
  simp only [sub_zero]
  have h1 : ∀ a, wt ω a * ω a = 1 - if a = 0 then 1 else 0 := fun a => by
    split_ifs with ha
    · rw [ha, hω.wt_zero, zero_mul, sub_self]
    · rw [hω.wt_mul_self ha, sub_zero]
  simp only [h1, Finset.sum_sub_distrib]
  simp

end IsTeich

end wt

section hopf

variable (hv : v.Integers R)
include hv

omit hv in
theorem pow_mem' (AA : HopfOrder (C := C) R (ZMod p)) {f : ZMod p → C} (hf : f ∈ AA.carrier)
    (n : ℕ) : f ^ n ∈ AA.carrier := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact AA.one_mem
  | succ n ih =>
    rw [pow_succ]
    exact AA.mul_mem _ _ ih hf


variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

end hopf

end ReciprocityTheory.PGsh.Up.U3
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable (p : ℕ) [Fact p.Prime] (g : ℕ)

abbrev Ix (g : ℕ) := Fin g ⊕ Fin g

abbrev TT := Ix g → ℤ_[p]

abbrev Nb := Ix g → ZMod p

def red (t : TT p g) : Nb p g := fun i => PadicInt.toZMod (t i)

def pair (E : Matrix (Ix g) (Ix g) ℤ_[p]) (s t : TT p g) : ℤ_[p] := s ⬝ᵥ (E *ᵥ t)

def sqIdeal {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {X : Type}
    (I : Submodule R (X → C)) : Submodule R (X → C) :=
  Submodule.span R {h | ∃ f ∈ I, ∃ f' ∈ I, h = f * f'}

abbrev LieDualModP (q : ℕ) (R : Type) [CommRing R] (n : ℕ) :=
  (Fin n → R) ⧸ (Ideal.span {(q : R)} • (⊤ : Submodule R (Fin n → R)))

def HasLen {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (M : Type) [AddCommGroup M] [Module R M] (x : NNReal) : Prop :=
  ∃ (m : ℕ) (c : Fin m → R), Nonempty (M ≃ₗ[R] ((i : Fin m) → R ⧸ Ideal.span {c i})) ∧
    ∏ i, v (algebraMap R C (c i)) = x

abbrev OmAA {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {X : Type}
    [AddCommGroup X] (M : Submodule R (X → C)) :=
  augIdeal M ⧸ (sqIdeal (augIdeal M)).comap (augIdeal M).subtype

structure HodgeTateDatum {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] [Algebra ℤ_[p] R] (O : Type) [CommRing O] [Algebra ℤ_[p] O]
    (σ : O ≃ₐ[ℤ_[p]] O) (cp : R) where

  ρ : O →ₐ[ℤ_[p]] Matrix (Ix g) (Ix g) ℤ_[p]

  ρL : O →+* Matrix (Fin g) (Fin g) R

  P : Matrix (Ix g) (Ix g) ℤ_[p]
  PL : Matrix (Fin g) (Fin g) R

  E : Matrix (Ix g) (Ix g) ℤ_[p]
  E_alternating : Eᵀ = -E ∧ ∀ i, E i i = 0
  isUnit_det_E : IsUnit E.det
  E_equivariant : ∀ a, (ρ a)ᵀ * E = E * ρ (σ a)
  projectors : P * P = P ∧ PL * PL = PL ∧ Pᵀ * E = E * P ∧
    (∀ a, P * ρ a = ρ a * P) ∧ ∀ a, PL * ρL a = ρL a * PL

  Ht : Matrix (Fin g) (Ix g) R

  Bt : Matrix (Fin g) (Ix g) R
  Ht_equivariant : (∀ a, Ht * (ρ a).map (algebraMap ℤ_[p] R) = (ρL (σ a))ᵀ * Ht) ∧
    Ht * P.map (algebraMap ℤ_[p] R) = PLᵀ * Ht
  form_eq_alt : Btᵀ * Ht - Htᵀ * Bt = cp • E.map (algebraMap ℤ_[p] R)

  AA : HopfOrder (C := C) R (Nb p g)
  h3 : ∀ a, ∀ f ∈ AA.carrier, ∃ f' ∈ AA.carrier, ∀ t, f' (red p g t) = f (red p g (ρ a *ᵥ t))

  h4 : ∀ k : Fin g,
    (∃ f ∈ AA.carrier, ∀ t : TT p g, ∃ r : R, algebraMap R C
      ((Ht *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) - f (red p g t) = algebraMap R C (p * r)) ∧
    (∃ f ∈ AA.carrier, ∀ t : TT p g, ∃ r : R, algebraMap R C
      ((Bt *ᵥ (algebraMap ℤ_[p] R ∘ t)) k) - f (red p g t) = algebraMap R C (p * r))

  h5 : p = 2 → ∀ s : TT p g, ∃ f ∈ AA.carrier, ∀ t : TT p g,
    f (red p g t) = (-1 : C) ^ (PadicInt.toZMod (pair p g E s t)).val

  φ : augIdeal AA.carrier →ₗ[R] LieDualModP p R g
  cotangent_surjective : Function.Surjective φ
  cotangent_ker_eq : LinearMap.ker φ = (sqIdeal (augIdeal AA.carrier)).comap (augIdeal AA.carrier).subtype
  cotangent_linear : ∀ (a : O) (f f' : augIdeal AA.carrier) (l : Fin g → R),
    (∀ t, (f' : Nb p g → C) (red p g t) = (f : Nb p g → C) (red p g (ρ a *ᵥ t))) →
    φ f = Submodule.Quotient.mk l → φ f' = Submodule.Quotient.mk ((ρL a)ᵀ *ᵥ l)

structure HodgeTateSetting {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] [Algebra ℤ_[p] R] (O : Type) [CommRing O] [Algebra ℤ_[p] O]
    (σ : O ≃ₐ[ℤ_[p]] O) (cp : R) : Prop where
  integers : v.Integers R
  p_lt : v (algebraMap R C (p : R)) < 1
  p_ne : v (algebraMap R C (p : R)) ≠ 0
  cp_val : v (algebraMap R C cp) ^ (p - 1) = v (algebraMap R C (p : R))
  invol : ∀ a, σ (σ a) = a

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

open Module

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem exists_smul_mem_of_mem_span [IsDomain R] [IsFractionRing R C]
    {V : Type} [AddCommGroup V] [Module C V] [Module R V] [IsScalarTower R C V]
    (S : Submodule R V) {x : V} (hx : x ∈ Submodule.span C (S : Set V)) :
    ∃ r : R, r ≠ 0 ∧ r • x ∈ S := by
  exact Bl.SecondBlockLemmaM.goal1 (C := C) S hx

theorem free_of_finite_torsionFree [IsDomain R] [ValuationRing R] (P : Type) [AddCommGroup P]
    [Module R P] [Module.Finite R P] (h : ∀ (r : R) (x : P), r ≠ 0 → r • x = 0 → x = 0) :
    Module.Free R P := by
  have : Module.Flat R P := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
    exact h a x (nonZeroDivisors.ne_zero a.2) ha
  exact Module.free_of_flat_of_isLocalRing

theorem algebraMap_ne_zero [IsFractionRing R C] {r : R} (hr : r ≠ 0) : algebraMap R C r ≠ 0 := by
  intro h0
  exact hr ((IsFractionRing.injective R C) (by simpa using h0))

theorem isLat_of_fg [IsDomain R] [ValuationRing R] [IsFractionRing R C]
    {X : Type} [Fintype X] [DecidableEq X] (M : Submodule R (X → C)) (hfg : M.FG)
    (hsp : Submodule.span C (M : Set (X → C)) = ⊤) : IsLat R M := by
  have : Module.Finite R M := Module.Finite.iff_fg.2 hfg
  have : Module.Free R M := free_of_finite_torsionFree M (by
    rintro r ⟨x, hx⟩ hr h
    have h' : (r • x : X → C) = 0 := by simpa using congrArg Subtype.val h
    rw [← algebraMap_smul C r x] at h'
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left (algebraMap_ne_zero hr)))
  let b := Module.Free.chooseBasis R M
  let v : Module.Free.ChooseBasisIndex R M → X → C := fun i => (b i : X → C)
  have hR : LinearIndependent R v := b.linearIndependent.map' M.subtype (Submodule.ker_subtype _)
  have hC : LinearIndependent C v := (LinearIndependent.iff_fractionRing R C).1 hR
  have hspR : Submodule.span R (Set.range v) = M := by
    have : Set.range v = M.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspC : Submodule.span C (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower R, hspR, hsp]
  let bC := Basis.mk hC (by rw [hspC])
  have hcard : Fintype.card X = Fintype.card (Module.Free.ChooseBasisIndex R M) := by
    rw [← Module.finrank_fintype_fun_eq_card (R := C), Module.finrank_eq_card_basis bC]
  let e : X ≃ Module.Free.ChooseBasisIndex R M := Fintype.equivOfCardEq hcard
  refine ⟨fun x j => v (e j) x, ?_, ?_⟩
  · have hli : LinearIndependent C (fun j x => v (e j) x) := hC.comp e e.injective
    have hu := (Matrix.linearIndependent_cols_iff_isUnit (A := (fun x j => v (e j) x : Matrix X X C))).1
      (by convert hli using 1; rfl)
    exact (Matrix.isUnit_iff_isUnit_det _).1 hu
  · have : Set.range (fun j x => v (e j) x) = Set.range v := by
      ext f; constructor
      · rintro ⟨j, rfl⟩; exact ⟨e j, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨e.symm i, by simp⟩
    rw [this, hspR]

theorem fg_of_isLat {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)}
    (h : IsLat R M) : M.FG := by
  obtain ⟨B, -, rfl⟩ := h
  exact Submodule.fg_span (Set.finite_range _)

theorem span_top_of_isLat {X : Type} [Fintype X] [DecidableEq X] {M : Submodule R (X → C)}
    (h : IsLat R M) : Submodule.span C (M : Set (X → C)) = ⊤ := by
  obtain ⟨B, hB, rfl⟩ := h
  rw [Submodule.span_span_of_tower]
  have hli : LinearIndependent C (fun j x => B x j) := by
    have := (Matrix.linearIndependent_cols_iff_isUnit (A := B)).2 ((Matrix.isUnit_iff_isUnit_det B).2 hB)
    convert this using 1; rfl
  exact hli.span_eq_top_of_card_eq_finrank' (by simp)

end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
end
end
