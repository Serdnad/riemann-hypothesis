module

import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.ExhaustionOfSteps
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.CuspEmbP
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle463
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem move_left (hM : MidP k) (hR : RefineP k) (hS : SwapP k) (hJ : JuxtP k) (hL : LinkP k) (x ρ : IrrGL (k := k)) :
    ∀ (A : List (IrrGL (k := k))), (∀ a ∈ A, a.IsCusp ∧ ρ ≠ a.nu 1) → ∀ (Δ : Segment k) (b : IrrGL (k := k)) (B : List (IrrGL (k := k))), Δ.first = ρ →
      IsLSeg Δ b.rep → EmbL x (A ++ [b] ++ B) → ∃ (Γ : Segment k) (c y : IrrGL (k := k)), Γ.first = ρ ∧ IsLSeg Γ c.rep ∧ EmbL x [c, y] := by
  intro A
  induction A using List.reverseRecOn with
  | nil =>
    intro _ Δ b B hΔ hb hx
    obtain ⟨σ, -, hσ⟩ := hM x [b] B [] (by simpa using hx)
    exact ⟨Δ, b, σ, hΔ, hb, by simpa using hσ⟩
  | append_singleton A' a ih =>
    intro hA Δ b B hΔ hb hx
    have hA' : ∀ a ∈ A', a.IsCusp ∧ ρ ≠ a.nu 1 := fun a' ha' => hA a' (List.mem_append_left _ ha')
    have ha := hA a (by simp)
    have hx' : EmbL x (A' ++ [a, b] ++ B) := by simpa using hx
    by_cases hlk : (Segment.single a ha.1).Linked Δ
    · rcases hL a ha.1 Δ hlk with h | h
      · exact (ha.2 (hΔ.symm.trans h)).elim
      · obtain ⟨σ, hσ, hxσ⟩ := hM x A' [a, b] B hx'
        rw [h] at hσ
        rcases hJ σ b Δ hb hσ with h2 | h2
        · have hup : (up Δ).first = ρ := by
            unfold up
            rw [Segment.first_ofFirst]
            exact hΔ
          exact ih hA' (up Δ) σ B hup h2 hxσ
        · have h3 := hR x σ A' [b, Δ.first.nu Δ.len] B h2 hxσ
          rw [← h] at h3
          exact ih hA' Δ b ([a] ++ B) hΔ hb (by simpa using h3)
    · have h3 := hS x a b A' B _ Δ (single_spec ha.1).2.1 hb hlk hx'
      exact ih hA' Δ b ([a] ++ B) hΔ hb (by simpa using h3)

theorem exhaustion_of_steps
    (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      MidP k ∧ RefineP k ∧ SwapP k ∧ CuspEmbP k ∧ SuppP k ∧ JuxtP k ∧ LinkP k ∧ MinP k ∧ PeelGoodP k) :
    GlobalTheory.Published.LanglandsExhaustionGL := by
  apply CompanionTheory.Exh.exhaustion_of_steps <;> assumption

end PositivityTheory.Exh

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_isLSeg (Δ : Segment k) (x y : IrrGL (k := k)) (hx : IsLSeg Δ x.rep) (hy : IsLSeg Δ y.rep) : x = y := by
  obtain ⟨n, cx⟩ := x
  obtain ⟨m, cy⟩ := y
  obtain ⟨hx1, hxc⟩ := hx
  obtain ⟨hy1, hyc⟩ := hy
  have hnm : n = m := hx1.symm.trans hy1
  subst hnm
  obtain ⟨e⟩ := IsCosocle.unique hxc hyc
  have hc : cx = cy := by
    rw [← Quotient.out_eq cx, ← Quotient.out_eq cy]
    exact Quotient.sound ⟨e.symm⟩
  rw [hc]

end PositivityTheory.Exh

end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem linkP : LinkP k := by
  intro ρ hρ Δ hl
  obtain ⟨σ, hσ, c, d, c', d', h1, h2, e1, e2⟩ := hl.exists_eq_icc
  have hlen : (Segment.single ρ hρ).len = 1 := rfl
  have hfst : (Segment.single ρ hρ).first = ρ := Segment.first_ofFirst _ _ _ _
  rw [e1, e2, Segment.linked_icc] at hl
  rw [e1] at hlen hfst
  simp only [Segment.icc, Segment.len_ofFirst, Segment.first_ofFirst] at hlen hfst
  have hdc : d = c := by omega
  subst hdc e2 hfst
  simp only [Segment.icc, Segment.len_ofFirst, Segment.first_ofFirst, IrrGL.nu_nu]
  rcases hl with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
  · left
    obtain rfl : c' = d + 1 := by omega
    congr 1
    push_cast
    ring
  · right
    obtain rfl : d = d' + 1 := by omega
    rw [show (((d' - c' + 1).toNat : ℕ) : ℂ) = ((d' - c' + 1 : ℤ) : ℂ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]]
    congr 1
    push_cast
    ring

private theorem eq_zero_of_nu_eq_of_isCusp {ρ : IrrGL (k := k)} (hρ : ρ.IsCusp) (n : ℤ) (h : ρ.nu (n : ℂ) = ρ) : n = 0 := by
  have hsub : (Segment.icc ρ hρ n n le_rfl).carrier ⊆ (Segment.icc ρ hρ 0 0 le_rfl).carrier := by
    intro x hx
    rw [Segment.mem_icc] at hx ⊢
    obtain ⟨a, ha1, ha2, rfl⟩ := hx
    obtain rfl : a = n := le_antisymm ha2 ha1
    refine ⟨0, le_rfl, le_rfl, ?_⟩
    rw [h]
    simp [IrrGL.nu_zero]
  have := Segment.icc_subset_icc.mp hsub
  omega

theorem minP : MinP k := by
  classical
  intro l hl hc
  obtain ⟨ρ₀, h₀⟩ := List.exists_mem_of_ne_nil l hl
  set f : ℕ → IrrGL (k := k) := fun m => ρ₀.nu (-(m : ℂ)) with hf
  have hinj : Function.Injective f := by
    intro m m' hmm
    have h1 : (f m).nu (m : ℂ) = (f m').nu (m : ℂ) := by rw [hmm]
    simp only [hf, IrrGL.nu_nu, neg_add_cancel, IrrGL.nu_zero] at h1
    have h2 : ρ₀.nu (((m : ℤ) - m' : ℤ) : ℂ) = ρ₀ := by
      conv_rhs => rw [h1]
      congr 1
      push_cast
      ring
    have := eq_zero_of_nu_eq_of_isCusp (hc ρ₀ h₀) _ h2
    omega
  have hfin : {m : ℕ | f m ∈ l}.Finite := by
    refine ((l.toFinset.finite_toSet).preimage hinj.injOn).subset ?_
    intro m hm
    simpa using hm
  have h0 : (0 : ℕ) ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    show f 0 ∈ l
    simpa [hf, IrrGL.nu_zero] using h₀
  set M := hfin.toFinset.max' ⟨0, h0⟩ with hMdef
  have hM : f M ∈ l := by
    have hm := hfin.toFinset.max'_mem ⟨0, h0⟩
    rw [Set.Finite.mem_toFinset] at hm
    exact hm
  refine ⟨f M, hM, fun ρ' hρ' j hj heq => ?_⟩
  have hρ'eq : ρ' = f (M + j) := by
    have h3 : (f M).nu (-(j : ℂ)) = ρ' := by
      rw [heq, IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero]
    rw [← h3]
    simp only [hf, IrrGL.nu_nu]
    congr 1
    push_cast
    ring
  have hmem : M + j ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]
    show f (M + j) ∈ l
    rw [← hρ'eq]
    exact hρ'
  have := hfin.toFinset.le_max' _ hmem
  omega

end PositivityTheory.Exh

end
end
