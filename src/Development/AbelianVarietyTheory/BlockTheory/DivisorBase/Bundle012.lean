module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LogFactorialIndices.Bundle001
public import Formalism.LocalToGlobal.ProjectiveLattices.VAddIntNonneg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

def ph (y : ℝ) : ℝ := y * Real.log y - y

def size {a : ℕ} (nu : DomWeight a) : ℕ := ∑ i, (nu.w i).toNat

def lastEntry {a : ℕ} (nu : DomWeight a) : ℕ := nu.detShift.toNat

def padZero {a : ℕ} (b : ℕ) (nu : DomWeight a) (j : Fin b) : ℤ :=
  if h : j.1 < a then nu.w ⟨j.1, h⟩ else 0

def StepWeights {a b : ℕ} (lam nu : DomWeight a) (lam' : DomWeight b) : Prop :=
  (∀ i, 0 ≤ nu.w i) ∧ (∃ s' : ℤ, ∀ i, nu.w i = lam.w i + s') ∧
    ∃ s : ℤ, ∀ j, lam'.w j + s = padZero b nu j

def invNormSq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (P : VV ℂ lam) : ℝ :=
  (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) P P).re

def OpNormSqLe {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (t : ℝ) : Prop :=
  ∀ P : VV ℂ lam, invNormSq lam' (T P) ≤ t * invNormSq lam P

def unitSq {ι : Type} [Fintype ι] {a b : ℕ} (r : ι → ℝ) (z : VCx ι a b) : ℝ :=
  ∑ τ, ∑ β, ∑ α, ‖(r τ : ℂ) * z τ β α‖ ^ 2

def tmax {ι : Type} [Fintype ι] {a : ℕ} (b : ℕ) (nu : ι → DomWeight a) (S : ℝ) (Om : ι → ℝ) : ℝ :=
  S ^ 2 * ∏ τ, ((Om τ)⁻¹ ^ size (nu τ) * Real.exp 1 * (2 * (size (nu τ) : ℝ) + 2) ^ (2 * (a * b)) *
    Real.exp (∑ i, ph ((nu τ).w i : ℝ)))

def BlockBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b →
  ∀ (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b),
    (∀ τ, StepWeights (lam τ) (nu τ) (lam' τ)) →
    (a = b → ∀ τ, lastEntry (nu τ) = 0) →
  ∀ (r Om : ι → ℝ) (cD : ι → ℂ),
    (∀ τ, 0 < r τ) → (∀ τ, 0 < Om τ) → (∀ τ, ‖cD τ * (r τ : ℂ)‖ ^ 2 = 1 / Om τ) →
  ∀ (G : VCx ι a b → ℂ) (S : ℝ), Differentiable ℂ G →
    (∀ z, ‖G z‖ ≤ S * Real.exp (unitSq r z / 2)) →
    OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => lastEntry (nu τ)) (tmax b nu S Om)

end GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PaddedWittNormSquare

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

def padZero {a : ℕ} (b : ℕ) (ν : DomWeight a) : Fin b → ℤ :=
  fun i => if h : i.1 < a then ν.w ⟨i.1, h⟩ else 0

def IsStepWeight {a b : ℕ} (lam ν : DomWeight a) (lam' : DomWeight b) (s' s : ℤ) : Prop :=
  (∀ i, ν.w i = lam.w i + s') ∧ (∀ i, 0 ≤ ν.w i) ∧ (∀ i, lam'.w i + s = padZero b ν i)

def wtSize {a : ℕ} (ν : DomWeight a) : ℕ := ∑ i, (ν.w i).toNat

def lastEntry {a : ℕ} (ν : DomWeight a) : ℕ := ν.detShift.toNat

def normSq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (v : VV ℂ lam) : ℝ :=
  (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v v).re

def OpNormSqLe {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (t : ℝ) : Prop :=
  ∀ v : VV ℂ lam, normSq lam' (T v) ≤ t * normSq lam v

def unitNormSq {ι : Type} [Fintype ι] {a b : ℕ} (r : ι → ℝ) (z : VCx ι a b) : ℝ :=
  ∑ τ, ∑ β, ∑ α, ‖(r τ : ℂ) * z τ β α‖ ^ 2

def tmax {ι : Type} [Fintype ι] {a : ℕ} (b : ℕ) (ν : ι → DomWeight a) (Om : ι → ℝ) (S : ℝ) : ℝ :=
  S ^ 2 * ∏ τ, ((Om τ)⁻¹ ^ wtSize (ν τ) * Real.exp 1 * (2 * (wtSize (ν τ) : ℝ) + 2) ^ (2 * (a * b)) *
    Real.exp (∑ i, Formalism.LatticeIndexTer.ph ((ν τ).w i : ℝ)))

def BlockBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b →
  ∀ (lam ν : ι → DomWeight a) (lam' : ι → DomWeight b) (s' s : ι → ℤ),
    (∀ τ, IsStepWeight (lam τ) (ν τ) (lam' τ) (s' τ) (s τ)) →
    (∀ τ, a < b ∨ lastEntry (ν τ) = 0) →
  ∀ (G : VCx ι a b → ℂ) (S : ℝ) (r Om : ι → ℝ) (cD : ι → ℂ),
    Differentiable ℂ G →
    (∀ τ, 0 < r τ) →
    (∀ z, ‖G z‖ ≤ S * Real.exp (unitNormSq r z / 2)) →
    (∀ τ, 0 < Om τ) →
    (∀ τ, ‖cD τ * (r τ : ℂ)‖ ^ 2 = 1 / Om τ) →
    OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => lastEntry (ν τ)) (tmax b ν Om S)

theorem natW_eq_padZero {a b : ℕ} (hab : a ≤ b) {lam ν : DomWeight a} {lam' : DomWeight b} {s' s : ℤ}
    (h : IsStepWeight lam ν lam' s' s) (hg : a < b ∨ lastEntry ν = 0) (i : Fin b) :
    ((lam'.natW i : ℕ) : ℤ) = padZero b ν i := by
  obtain ⟨h1, h2, h3⟩ := h
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) i.2
  have hpad : ∀ j, 0 ≤ padZero b ν j := by
    intro j
    unfold padZero
    split_ifs
    · exact h2 _
    · exact le_rfl
  let j0 : Fin b := ⟨b - 1, by omega⟩
  have hlast : padZero b ν j0 = 0 := by
    unfold padZero
    split_ifs with hlt
    · have hlt' : b - 1 < a := hlt
      rcases hg with hg | hg
      · omega
      · have ha : 0 < a := by omega
        have hz : ν.w ⟨a - 1, by omega⟩ ≤ 0 := by
          unfold lastEntry DomWeight.detShift at hg
          rw [dite_eq_left ha] at hg
          exact Int.toNat_eq_zero.mp hg
        have hidx : (⟨j0.1, hlt⟩ : Fin a) = ⟨a - 1, by omega⟩ := Fin.ext (by simp [j0]; omega)
        rw [hidx]
        exact le_antisymm hz (h2 _)
    · rfl
  have hshift : lam'.detShift = -s := by
    unfold DomWeight.detShift
    rw [dite_eq_left hb]
    show lam'.w j0 = -s
    have h30 := h3 j0
    rw [hlast] at h30
    linarith
  unfold DomWeight.natW
  rw [hshift]
  have hw : lam'.w i - -s = padZero b ν i := by linarith [h3 i]
  rw [hw, Int.toNat_of_nonneg (hpad i)]

end GlobalTheory.IndefiniteRowSideFullHecke.PaddedWittNormSquare
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SupremumLattice

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

section Ambient

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
  [IsScalarTower (𝓞 K) K R] (C : Submodule K R) (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal))
  (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)

def supIn : Submodule (𝓞 K) R := (latOf C Vs hV).map (C.subtype.restrictScalars (𝓞 K))

theorem supIn_full_iff :
    ((supIn C Vs hV).FG ∧ Submodule.span K (supIn C Vs hV : Set R) = C) ↔
      Submodule.IsFullLattice K (latOf C Vs hV) := by
  have h1 : (supIn C Vs hV).FG ↔ (latOf C Vs hV).FG :=
    ⟨Submodule.fg_of_fg_map_injective (C.subtype.restrictScalars (𝓞 K)) C.injective_subtype, fun h => h.map _⟩
  have h2 : Submodule.span K (supIn C Vs hV : Set R) =
      (Submodule.span K (latOf C Vs hV : Set C)).map C.subtype := by
    rw [← Submodule.span_image]; rfl
  rw [h1, h2]
  constructor
  · rintro ⟨a, b⟩
    exact { toIsLattice := Submodule.IsLattice.of_fg K a
            span_eq_top := Submodule.map_injective_of_injective C.injective_subtype (by
              rw [b, Submodule.map_subtype_top]) }
  · intro h
    exact ⟨h.fg, by rw [Submodule.IsFullLattice.span_eq_top (self := h), Submodule.map_subtype_top]⟩

end Ambient

variable {D : D7}

end GlobalTheory.IndefiniteRowSideFullHecke.SupremumLattice
end
end
