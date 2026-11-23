module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupExOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail
open scoped Classical TensorProduct


attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Choice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure Shuf (n : ℕ) where
  a : ℕ
  b : ℕ
  e : Fin a ⊕ Fin b ≃ Fin n
  monoL : StrictMono fun i : Fin a => e (Sum.inl i)
  monoR : StrictMono fun j : Fin b => e (Sum.inr j)
  eps : Fin n → ℂˣ

def resL (s : Shuf n) (x : Fin n → ℤ) : Fin s.a → ℤ := fun i => x (s.e (Sum.inl i))
def resR (s : Shuf n) (x : Fin n → ℤ) : Fin s.b → ℤ := fun j => x (s.e (Sum.inr j))

def qU (w : Pl E) (k : ℤ) : ℂˣ := if h : (qh w : ℂ) ≠ 0 then Units.mk0 _ h ^ k else 1

def chiOf (w : Pl E) (s : Shuf n) (ξa : Fin s.a → ℂˣ) (ξb : Fin s.b → ℂˣ) : Fin n → ℂˣ :=
  fun k => s.eps k * Sum.elim (fun i => ξa i * qU w ((s.a : ℤ) - 1 - 2 * (i : ℕ)))
    (fun j => ξb j * qU w ((s.b : ℤ) - 1 - 2 * (j : ℕ))) (s.e.symm k)

def ChiEval : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (s : Shuf n)
  (ξa : Fin s.a → ℂˣ) (ξb : Fin s.b → ℂˣ) (x : Fin n → ℤ),
  ((∏ k, s.eps k ^ x k : ℂˣ) : ℂ) * ev2 w ξa ξb (resL s x) (resR s x) = ((∏ k, chiOf w s ξa ξb k ^ x k : ℂˣ) : ℂ)

def GapRes : Prop := ∀ (n : ℕ) (s : Shuf n) (x : Fin n → ℤ), x ∈ coneGL n 2 → Gap (resL s x) ∧ Gap (resR s x)

def ChoiceT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (ι : Type) [Fintype ι]
  (s : ι → Shuf n) (Z : ∀ i, Set ((Fin (s i).a → ℂˣ) × (Fin (s i).b → ℂˣ))) (α : Fin n → ℂˣ), (∀ i, (Z i).Finite) →
  ∃ c : (Fin n → ℤ) →₀ ℂ, (↑c.support ⊆ coneGL n 2) ∧ evalGL c α = 1 ∧
    ∀ i, ∀ p ∈ Z i, (c.sum fun x a => a * ((∏ k, (s i).eps k ^ x k : ℂˣ) : ℂ) *
        ev2 w p.1 p.2 (resL (s i) x) (resR (s i) x)) ≠ 0 → chiOf w (s i) p.1 p.2 = α

def ChoiceS : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (GLw n w)),
  IsOpen (K' : Set (GLw n w)) → IsCompact (K' : Set (GLw n w)) → ∀ P : SmIrr (GLw n w), (∃ v ∈ fixed P.ρ K', v ≠ 0) →
  ∀ (k : ℕ) (D : Fin k → Pre E n),
  ∃ e : GLw n w → ℂ, IsHk K' e ∧ (∃ v₀ ∈ fixed P.ρ K', ∃ l : _ →ₗ[ℂ] ℂ, l v₀ = 1 ∧ ∀ v ∈ fixed P.ρ K', hk P.ρ K' e v = l v • v₀) ∧
    ∀ j, ∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt (D j) w) → IsEmpty (τ.ρ.Equiv P.ρ) →
      ∀ v ∈ fixed τ.ρ K', hk τ.ρ K' e v = 0

def ChoiceTOf : Prop := PeakCone → ChiEval → GapRes → ChoiceT

end PositivityTheory.Rg.BcB.F.Choice

end
end

section

noncomputable section

open Filter

namespace PositivityTheory.Rg.BcB.F.SG

open PositivityTheory.Rg.BcB.F

variable {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)]
  [∀ s, InnerProductSpace ℂ (H s)] [∀ s, CompleteSpace (H s)] {d : ℕ}

local notation "Vd" => EuclideanSpace ℂ (Fin d)

def trU (u : Vd →L[ℂ] Vd) (a : Prod' H d) (k : ℕ) : ℂ :=
  LinearMap.trace ℂ Vd (((u * a.2) ^ k : Vd →L[ℂ] Vd) : Vd →ₗ[ℂ] Vd)

def BoundAt (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (u : Vd →L[ℂ] Vd) (a : Prod' H d) : Prop :=
  ∃ (C : ℝ) (N j : ℕ), ∀ᶠ k : ℕ in atTop,
    ‖trU u a k‖ ≤ C * (1 + k) ^ N * Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * a.1 s) ^ (k - j)‖)

def TraceSplit (u : Vd →L[ℂ] Vd) (a : Prod' H d) (t : ι → ℕ → ℂ) : Prop :=
  ∀ᶠ k : ℕ in atTop, trU u a k = ∑ s, t s k

def BlockBound (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (a : Prod' H d) (t : ι → ℕ → ℂ) (j : ℕ) : Prop :=
  ∀ s, ∃ (C : ℝ) (N : ℕ), ∀ᶠ k : ℕ in atTop, ‖t s k‖ ≤ C * (1 + k) ^ N * ‖(β s ^ m * a.1 s) ^ (k - j)‖

theorem boundAt_of (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (u : Vd →L[ℂ] Vd) (a : Prod' H d) (t : ι → ℕ → ℂ) (j : ℕ)
    (h1 : TraceSplit u a t) (h2 : BlockBound β m a t j) : BoundAt β m u a := by
  choose C N hC using h2
  have hall := Filter.eventually_all.2 hC
  refine ⟨∑ s, |C s|, Finset.univ.sup N, j, ?_⟩
  filter_upwards [h1, hall] with k hk hks
  rw [hk]
  have hk1 : (1 : ℝ) ≤ 1 + (k : ℝ) := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  calc ‖∑ s, t s k‖ ≤ ∑ s, ‖t s k‖ := norm_sum_le _ _
    _ ≤ ∑ s, |C s| * (1 + (k : ℝ)) ^ (Finset.univ.sup N) *
          Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * a.1 s) ^ (k - j)‖) := by
        apply Finset.sum_le_sum
        intro s _
        have hP : (1 + (k : ℝ)) ^ (N s) ≤ (1 + (k : ℝ)) ^ (Finset.univ.sup N) :=
          pow_le_pow_right₀ hk1 (Finset.le_sup (Finset.mem_univ s))
        have hX : ‖(β s ^ m * a.1 s) ^ (k - j)‖ ≤
            Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * a.1 s) ^ (k - j)‖) :=
          Finset.le_sup' (fun s => ‖(β s ^ m * a.1 s) ^ (k - j)‖) (Finset.mem_univ s)
        calc ‖t s k‖ ≤ C s * (1 + (k : ℝ)) ^ (N s) * ‖(β s ^ m * a.1 s) ^ (k - j)‖ := hks s
          _ ≤ |C s| * (1 + (k : ℝ)) ^ (N s) * ‖(β s ^ m * a.1 s) ^ (k - j)‖ := by
            gcongr
            exact le_abs_self _
          _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hP (abs_nonneg _)) hX (norm_nonneg _)
              (by positivity)
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

end PositivityTheory.Rg.BcB.F.SG

end
end
