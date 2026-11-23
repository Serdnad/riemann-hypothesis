module

import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.Bundle002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.CuspEmbP
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle349
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle350
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc GlobalTheory.CompanionTheory.ExhGood

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isL_add_segment_of_injective_of_not_precedes [CharZero k] (HS : GlobalTheory.Published.StandardCosocleGL) (HL : LSocleGL k) (x : IrrGL (k := k))
    (y : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (y a).1 = x.1) (s : Segment k) (𝔫 : Multiset (Segment k))
    (hs : IsLSeg s (y 0).rep) (hn : IsL 𝔫 (y 1).rep)
    (hf : ∃ f : x.rep.IntertwiningMap (prodIrr y hd), Function.Injective f)
    (hp : ∀ Δ ∈ 𝔫, ¬ Δ.Precedes s) :
    IsL (𝔫 + {s}) x.rep := by
  apply CompanionTheory.Exh.isL_add_segment_of_injective_of_not_precedes <;> assumption

theorem peelGoodP (h1 : GlobalTheory.Published.StandardCosocleGL) (h2 : Zc.LSocleGL k) (_h3 : RefineP k) [CharZero k] :
    Zc.PeelGoodP k := by
  intro x y hd Δ 𝔫 hs hn hf hp
  exact isL_add_segment_of_injective_of_not_precedes h1 h2 x y hd Δ 𝔫 hs hn hf hp

end PositivityTheory.Exh

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem decW_up (Δ : Segment k) : decW (up Δ) = nxt Δ :: decW Δ := by
  apply CompanionTheory.Exh.decW_up <;> assumption

theorem nxt_not_mem (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) : nxt Δ ∉ decW Δ := by
  intro h
  rw [decW, List.mem_ofFn] at h
  obtain ⟨i, hi⟩ := h
  have h2 := GlobalTheory.T.cuspidal_twist_injective hA Δ.first Δ.isCusp_first _ _ hi
  have h3 := (Fin.rev i).isLt
  omega

theorem eq_decW_of_append (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (u P Q : List (IrrGL (k := k)))
    (h1 : decW Δ = P ++ Q) (h2 : u ++ [nxt Δ] = P ++ nxt Δ :: Q) : u = decW Δ := by
  apply CompanionTheory.Exh.eq_decW_of_append <;> assumption

end PositivityTheory.Exh

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nu_nu_nat (x : IrrGL (k := k)) (a b : ℕ) : (x.nu (a : ℂ)).nu (b : ℂ) = x.nu ((a + b : ℕ) : ℂ) := by
  rw [IrrGL.nu_nu, Nat.cast_add]

theorem not_linked_single (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) (n j : ℕ)
    (hj : j + 2 ≤ n) :
    ¬ (Segment.single (ρ.nu (n : ℂ)) (hρ.nu _)).Linked (Segment.single (ρ.nu (j : ℂ)) (hρ.nu _)) := by
  apply CompanionTheory.Exh.not_linked_single <;> assumption

theorem mem_tail_decW (Δ : Segment k) (x : IrrGL (k := k)) (hx : x ∈ (decW Δ).tail) :
    ∃ j : ℕ, j + 2 ≤ Δ.len ∧ x = Δ.first.nu (j : ℂ) := by
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hx
  have hm' : m + 1 < Δ.len := by
    have := hm
    simp [decW] at this
    omega
  refine ⟨Δ.len - (m + 2), by omega, ?_⟩
  simp only [List.getElem_tail, decW, List.getElem_ofFn, Segment.term, Fin.val_rev]

theorem move_past (hS : SwapP k) (σ ρ : IrrGL (k := k)) (hρ : ρ.IsCusp) :
    ∀ (Q P : List (IrrGL (k := k))), (∀ q ∈ Q, ∃ hq : q.IsCusp, ¬ (Segment.single ρ hρ).Linked (Segment.single q hq)) →
      EmbL σ (P ++ ρ :: Q) → EmbL σ (P ++ Q ++ [ρ]) := by
  apply CompanionTheory.Exh.move_past <;> assumption

theorem emb_move_end (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hS : SwapP k) (σ : IrrGL (k := k)) (Δ : Segment k)
    (P Q : List (IrrGL (k := k))) (h1 : decW Δ = P ++ Q) (hP : P ≠ []) (he : EmbL σ (P ++ nxt Δ :: Q)) :
    EmbL σ (decW Δ ++ [nxt Δ]) := by
  obtain ⟨p, P', rfl⟩ := List.exists_cons_of_ne_nil hP
  rw [h1]
  refine move_past hS σ (nxt Δ) (Δ.isCusp_first.nu _) Q (p :: P') ?_ he
  intro q hq
  have hq' : q ∈ (decW Δ).tail := by rw [h1]; simp [hq]
  obtain ⟨j, hj, rfl⟩ := mem_tail_decW Δ q hq'
  exact ⟨Δ.isCusp_first.nu _, not_linked_single hA Δ.first Δ.isCusp_first Δ.len j (by omega)⟩

end PositivityTheory.Exh

end
end
