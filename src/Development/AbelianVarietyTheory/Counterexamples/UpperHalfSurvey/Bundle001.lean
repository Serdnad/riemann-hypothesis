module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import ReciprocityTheory.DualLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle004
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.DualLattices.DvdOfCoeffZero
import ReciprocityTheory.DualLattices.Bundle003
public import ReciprocityTheory.DualLattices.Bundle006
public import ReciprocityTheory.DualLattices.ValUntiltESubOne
public import ReciprocityTheory.DualLattices.Bundle011

@[expose] public section

section

noncomputable section
open scoped BigOperators
open Classical

namespace GlobalTheory.RowValueCheck

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

def Agree {σ : Type} (S : Set σ) (F F' : MvPowerSeries σ C) : Prop :=
  ∀ μ : σ →₀ ℕ, (∀ x, μ x ≠ 0 → x ∈ S) → MvPowerSeries.coeff μ F = MvPowerSeries.coeff μ F'

theorem Agree.mul {σ : Type} {S : Set σ} {F F' K K' : MvPowerSeries σ C} (h : Agree S F F')
    (h' : Agree S K K') : Agree S (F * K) (F' * K') := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have e : p.1 + p.2 = μ := by simpa using hp
  rw [h p.1 fun x hx => hμ x (by rw [← e]; simp; omega),
    h' p.2 fun x hx => hμ x (by rw [← e]; simp; omega)]

theorem Agree.pow {σ : Type} {S : Set σ} {F F' : MvPowerSeries σ C} (h : Agree S F F') (k : ℕ) :
    Agree S (F ^ k) (F' ^ k) := by
  induction k with
  | zero => intro μ _; simp
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem Agree.exp {σ : Type} {S : Set σ} {F F' : MvPowerSeries σ C} (h : Agree S F F') :
    Agree S (mvExp F) (mvExp F') := by
  intro μ hμ
  show (∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (F ^ k) / (k.factorial : C)) =
    ∑ k ∈ Finset.range (μ.degree + 1), MvPowerSeries.coeff μ (F' ^ k) / (k.factorial : C)
  exact Finset.sum_congr rfl fun k _ => by rw [h.pow k μ hμ]

theorem Agree.prod {σ α : Type} {S : Set σ} (s : Finset α) {F F' : α → MvPowerSeries σ C}
    (h : ∀ i, Agree S (F i) (F' i)) : Agree S (∏ i ∈ s, F i) (∏ i ∈ s, F' i) := by
  induction s using Finset.induction_on with
  | empty => intro μ _; simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha]; exact (h a).mul ih

theorem agree_rowCopy {N : ℕ} (S : Set (Fin N × WV I)) (ρ : Fin N) (F F' : MvPowerSeries (WV I) C)
    (h : Agree {w | (ρ, w) ∈ S} F F') : Agree S (rowCopy ρ F) (rowCopy ρ F') := by
  intro μ hμ
  have hs : MvPowerSeries.HasSubst
      (fun w : WV I => (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by simp)
  unfold rowCopy
  rw [MvPowerSeries.coeff_subst hs, MvPowerSeries.coeff_subst hs]
  refine finsum_congr fun e => ?_
  by_cases he : ∀ x, e x ≠ 0 → (ρ, x) ∈ S
  · rw [h e he]
  · push Not at he
    obtain ⟨x, hx, hxS⟩ := he
    have h0 : μ (ρ, x) = 0 := by
      by_contra h1
      exact hxS (hμ _ h1)
    have hd : (MvPowerSeries.X (ρ, x) : MvPowerSeries (Fin N × WV I) C) ∣
        e.prod fun s k => (MvPowerSeries.X (ρ, s) : MvPowerSeries (Fin N × WV I) C) ^ k :=
      (dvd_pow_self _ hx).trans (Finset.dvd_prod_of_mem
        (fun s => (MvPowerSeries.X (ρ, s) : MvPowerSeries (Fin N × WV I) C) ^ e s)
        (Finsupp.mem_support_iff.2 hx))
    rw [MvPowerSeries.X_dvd_iff.1 hd μ h0]
    simp

def hOf (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) :
    Option (Fin 2 × ZMod d × ZMod d) → MvPowerSeries (WV I) C
  | some (g, a, a') => hL g a a'
  | none => 0

theorem valOf_eq (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) {N : ℕ}
    (P : MvPolynomial (Fin N × WV I) C) (kind : Fin N → Option (Fin 2 × ZMod d × ZMod d))
    (gr : Fin N → MvPowerSeries (WV I) C) :
    ValOf hL P kind gr =
      jetAt0 P (∏ ρ, (rowCopy ρ (gr ρ) * mvExp (rowCopy ρ (hOf hL (kind ρ))))) := by
  unfold ValOf
  congr 1

end GlobalTheory.RowValueCheck
end
end

section

open WittVector Ideal ReciprocityTheory.PGsh

namespace GlobalTheory.AinfChecks


open WittVector Ideal in
theorem _root_.GlobalTheory.AinfChecks.padicComplex (p : ℕ) [Fact p.Prime] :
    ∃ (_ : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p])) (_ : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]),
      (∃ pflat : PreTilt 𝓞_ℂ_[p] p, pflat.untilt = ((p : ℕ) : 𝓞_ℂ_[p])) ∧
      (∃ ε : PreTilt 𝓞_ℂ_[p] p,
        IsPrimitiveRoot (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε).untilt) p) ∧
      _root_.ReciprocityTheory.PGsh.KerThetaStatement p 𝓞_ℂ_[p] ∧ _root_.ReciprocityTheory.PGsh.XiNuStatement p ℂ_[p] Valued.v 𝓞_ℂ_[p] ∧
      _root_.ReciprocityTheory.PGsh.RegularStatement p 𝓞_ℂ_[p] ∧ _root_.ReciprocityTheory.PGsh.FlatW'Statement p 𝓞_ℂ_[p] := by
  obtain ⟨hunit, hcomp, ε, hv, hε⟩ := _root_.GlobalTheory.PadicComplexHost.main p
  have hker : _root_.ReciprocityTheory.PGsh.KerThetaStatement p 𝓞_ℂ_[p] := _root_.ReciprocityTheory.PGsh.kerTheta ℂ_[p] Valued.v hv
  refine ⟨hunit, hcomp, _root_.ReciprocityTheory.PGsh.exists_pflat ℂ_[p] Valued.v 𝓞_ℂ_[p] hv, ⟨ε, hε⟩, hker,
    _root_.ReciprocityTheory.PGsh.xiNu p ℂ_[p] Valued.v 𝓞_ℂ_[p] hker, ?_, _root_.ReciprocityTheory.PGsh.flatW' p 𝓞_ℂ_[p]⟩
  refine _root_.ReciprocityTheory.PGsh.regular p 𝓞_ℂ_[p] fun x hx => ?_
  have h : ((p : ℂ_[p]) * (x : ℂ_[p])) = 0 := by
    simpa using congrArg (fun y : 𝓞_ℂ_[p] => (y : ℂ_[p])) hx
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  · exact Subtype.ext h

section
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]


end

end GlobalTheory.AinfChecks
end
