module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle473
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Formalism.DoubleCosetMeasures.Statement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle480
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
import Mathlib.RingTheory.Henselian
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

@[expose] public section

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

open scoped Pointwise in
theorem nhds_one_slice_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB (k := k) a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice (k := k) a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1) →
    ∃ U ∈ nhds (1 : GL (Fin a) k), ∀ x ∈ U, ∀ (g : GL (Fin a) k), ∀ Z ∈ slice (k := k) a d,
      Φ (g.val * x.val * Z) = Φ (g.val * Z) := by
  intro k _ _ _ _ a d Φ hΦ s hs hsl huniq
  obtain ⟨⟨hlc, hcpt⟩, hrk⟩ := hΦ

  have hcl : IsClosed (Function.support Φ) := by
    have : Function.support Φ = (Φ ⁻¹' {0})ᶜ := by ext; simp
    rw [this, isClosed_compl_iff]; exact hlc.isOpen_fiber 0
  have hS : tsupport Φ ⊆ {Y | Y.rank = a} := by
    intro Y hY
    rw [tsupport, hcl.closure_eq] at hY
    by_contra h; exact hY (hrk Y h)
  set f : Matrix (Fin a) (Fin d) k → GL (Fin a) k × Matrix (Fin a) (Fin d) k :=
    fun Y => (s Y, ((s Y)⁻¹).val * Y) with hf
  have hfc : ContinuousOn f (tsupport Φ) := by
    have hs' := hs.mono hS
    refine ContinuousOn.prodMk hs' ?_
    exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_continuousOn
      ((Units.continuous_val.comp_continuousOn hs'.inv).prodMk continuousOn_id)
  have hA : IsCompact (f '' tsupport Φ) := hcpt.image_of_continuousOn hfc
  set n : Set ((GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k) :=
    {p | Φ (p.1.1.val * p.2.val * p.1.2) = Φ (p.1.1.val * p.1.2)} with hn
  have hno : IsOpen n := by
    have h1 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k =>
        Φ (p.1.1.val * p.2.val * p.1.2)) :=
      hlc.comp_continuous (by fun_prop)
    have h2 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k =>
        Φ (p.1.1.val * p.1.2)) :=
      hlc.comp_continuous (by fun_prop)
    exact (h1.prodMk h2) {q | q.1 = q.2}
  have hsub : (f '' tsupport Φ) ×ˢ ({1} : Set (GL (Fin a) k)) ⊆ n := by
    rintro ⟨⟨g, Z⟩, x⟩ ⟨_, hx⟩
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp [hn]
  obtain ⟨u, v, -, hv, hAu, h1v, huv⟩ := generalized_tube_lemma hA isCompact_singleton hno hsub

  have key : ∀ (h : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice (k := k) a d → Φ (h.val * Z) ≠ 0 →
      (h, Z) ∈ f '' tsupport Φ := by
    intro h Z hZ hne
    have hY : h.val * Z ∈ tsupport Φ := subset_tsupport _ hne
    have hr := hS hY
    have e : (s (h.val * Z))⁻¹ * h = 1 := by
      apply huniq Z _ hZ
      have := hsl _ hr
      simpa [Units.val_mul, Matrix.mul_assoc] using this
    have e' : s (h.val * Z) = h := by
      have := congrArg (fun t => s (h.val * Z) * t) e
      simpa [mul_assoc] using this.symm
    refine ⟨h.val * Z, hY, ?_⟩
    simp only [hf, e', Prod.mk.injEq, true_and]
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  refine ⟨v ∩ v⁻¹, Filter.inter_mem (hv.mem_nhds (h1v rfl)) ?_, ?_⟩
  · exact (hv.inv).mem_nhds (by simpa using h1v rfl)
  rintro x ⟨hxv, hxv'⟩ g Z hZ
  by_cases h0 : Φ (g.val * Z) ≠ 0
  · exact huv (Set.mk_mem_prod (hAu (key g Z hZ h0)) hxv)
  by_cases h0' : Φ (g.val * x.val * Z) ≠ 0
  · have hm : (g * x, Z) ∈ f '' tsupport Φ := key (g * x) Z hZ (by simpa [Units.val_mul] using h0')
    have := huv (Set.mk_mem_prod (hAu hm) (show x⁻¹ ∈ v from hxv'))
    simp only [hn, Set.mem_ofPred_eq] at this
    rw [Units.val_mul, Matrix.mul_assoc g.val x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one] at this
    rw [this]
  push Not at h0 h0'
  rw [h0, h0']

end GlobalTheory.RankFibreKer
end

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

open scoped Pointwise in

theorem _root_.GlobalTheory.T.continuous_slice_section_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB (k := k) a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice (k := k) a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1) →
    ∃ U ∈ nhds (1 : GL (Fin a) k), ∀ x ∈ U, ∀ (g : GL (Fin a) k), ∀ Z ∈ slice (k := k) a d,
      Φ (g.val * x.val * Z) = Φ (g.val * Z) := by
  intro k _ _ _ _ a d Φ hΦ s hs hsl huniq
  have hInvariant : ∃ U ∈ nhds (1 : GL (Fin a) k), ∀ x ∈ U, ∀ (g : GL (Fin a) k), ∀ Z ∈ slice (k := k) a d,
        Φ (g.val * x.val * Z) = Φ (g.val * Z) := by
    obtain ⟨⟨hlc, hcpt⟩, hrk⟩ := hΦ

    have hcl : IsClosed (Function.support Φ) := by
      have : Function.support Φ = (Φ ⁻¹' {0})ᶜ := by ext; simp
      rw [this, isClosed_compl_iff]; exact hlc.isOpen_fiber 0
    have hS : tsupport Φ ⊆ {Y | Y.rank = a} := by
      intro Y hY
      rw [tsupport, hcl.closure_eq] at hY
      by_contra h; exact hY (hrk Y h)
    set f : Matrix (Fin a) (Fin d) k → GL (Fin a) k × Matrix (Fin a) (Fin d) k :=
      fun Y => (s Y, ((s Y)⁻¹).val * Y) with hf
    have hfc : ContinuousOn f (tsupport Φ) := by
      have hs' := hs.mono hS
      refine ContinuousOn.prodMk hs' ?_
      exact (Continuous.matrix_mul continuous_fst continuous_snd).comp_continuousOn
        ((Units.continuous_val.comp_continuousOn hs'.inv).prodMk continuousOn_id)
    have hA : IsCompact (f '' tsupport Φ) := hcpt.image_of_continuousOn hfc
    set n : Set ((GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k) :=
      {p | Φ (p.1.1.val * p.2.val * p.1.2) = Φ (p.1.1.val * p.1.2)} with hn
    have hno : IsOpen n := by
      have h1 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k =>
          Φ (p.1.1.val * p.2.val * p.1.2)) :=
        hlc.comp_continuous (by fun_prop)
      have h2 : IsLocallyConstant (fun p : (GL (Fin a) k × Matrix (Fin a) (Fin d) k) × GL (Fin a) k =>
          Φ (p.1.1.val * p.1.2)) :=
        hlc.comp_continuous (by fun_prop)
      exact (h1.prodMk h2) {q | q.1 = q.2}
    have hsub : (f '' tsupport Φ) ×ˢ ({1} : Set (GL (Fin a) k)) ⊆ n := by
      rintro ⟨⟨g, Z⟩, x⟩ ⟨_, hx⟩
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      simp [hn]
    obtain ⟨u, v, -, hv, hAu, h1v, huv⟩ := generalized_tube_lemma hA isCompact_singleton hno hsub

    have key : ∀ (h : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice (k := k) a d → Φ (h.val * Z) ≠ 0 →
        (h, Z) ∈ f '' tsupport Φ := by
      intro h Z hZ hne
      have hY : h.val * Z ∈ tsupport Φ := subset_tsupport _ hne
      have hr := hS hY
      have e : (s (h.val * Z))⁻¹ * h = 1 := by
        apply huniq Z _ hZ
        have := hsl _ hr
        simpa [Units.val_mul, Matrix.mul_assoc] using this
      have e' : s (h.val * Z) = h := by
        have := congrArg (fun t => s (h.val * Z) * t) e
        simpa [mul_assoc] using this.symm
      refine ⟨h.val * Z, hY, ?_⟩
      simp only [hf, e', Prod.mk.injEq, true_and]
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    refine ⟨v ∩ v⁻¹, Filter.inter_mem (hv.mem_nhds (h1v rfl)) ?_, ?_⟩
    · exact (hv.inv).mem_nhds (by simpa using h1v rfl)
    rintro x ⟨hxv, hxv'⟩ g Z hZ
    by_cases h0 : Φ (g.val * Z) ≠ 0
    · exact huv (Set.mk_mem_prod (hAu (key g Z hZ h0)) hxv)
    by_cases h0' : Φ (g.val * x.val * Z) ≠ 0
    · have hm : (g * x, Z) ∈ f '' tsupport Φ := key (g * x) Z hZ (by simpa [Units.val_mul] using h0')
      have := huv (Set.mk_mem_prod (hAu hm) (show x⁻¹ ∈ v from hxv'))
      simp only [hn, Set.mem_ofPred_eq] at this
      rw [Units.val_mul, Matrix.mul_assoc g.val x.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.mul_one] at this
      rw [this]
    push Not at h0 h0'
    rw [h0, h0']
  exact hInvariant
end

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem mem_coinv_of_finset_sum (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ χ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (R : Finset (GL (Fin a) k)) (hΦ : Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)) (hχ : IsLocallyConstant χ)
    (h1 : ∀ Y, Φ Y = ∑ r ∈ R, χ ((r⁻¹).val * Y) * Φ Y)
    (h2 : ∀ Y, χ Y * ∑ r ∈ R, tw ν (a + b) r * Φ (r.val * Y) = 0) : Φ ∈ coinv ν β a (a + b) := by
  set H : GL (Fin a) k → Matrix (Fin a) (Fin (a + b)) k → ℂ :=
    fun r Y => χ Y * (tw ν (a + b) r * Φ (r.val * Y)) with hH
  have hHSB : ∀ r, H r ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) := by
    intro r
    have hs : (fun Y => Φ (r.val * Y)) ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) := by
      have := comp_mul_mem_SB r 1 hΦ
      simp only [Units.val_one, Matrix.mul_one] at this
      exact this
    obtain ⟨hs1, hs2⟩ := hs
    have e : H r = χ * ((fun _ => tw ν (a + b) r) * fun Y => Φ (r.val * Y)) := rfl
    rw [e]
    refine ⟨?_, ?_⟩
    · exact hχ.mul ((IsLocallyConstant.const _).mul hs1)
    · exact HasCompactSupport.mul_left (HasCompactSupport.mul_left hs2)
  have hom : ∀ r, omA ν β r 1 (H r) = fun Y => χ ((r⁻¹).val * Y) * Φ Y := by
    intro r
    funext Y
    rw [omA_one_apply]
    simp only [hH, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    field_simp [tw_ne_zero ν (a + b) r]
  have hsumH : ∑ r ∈ R, H r = 0 := by
    funext Y
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [hH, ← Finset.mul_sum]
    exact h2 Y
  have hΦeq : Φ = ∑ r ∈ R, (omA ν β r 1 (H r) - H r) := by
    rw [Finset.sum_sub_distrib, hsumH, sub_zero]
    funext Y
    rw [Finset.sum_apply]
    simp only [hom]
    exact h1 Y
  rw [hΦeq]
  refine Submodule.sum_mem _ fun r _ => Submodule.subset_span ⟨r, H r, hHSB r, rfl⟩

end GlobalTheory.RankFibreKer
end

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem exists_isCompact_of_slice : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB (k := k) a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice (k := k) a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1) →
    ∃ C : Set (GL (Fin a) k), IsCompact C ∧ ∀ (g : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice (k := k) a d →
      Φ (g.val * Z) ≠ 0 → g ∈ C := by
  intro k _ _ _ _ a d Φ hΦ s hs hsl huniq
  obtain ⟨⟨hlc, hcs⟩, hrank⟩ := hΦ
  have hclosed : IsClosed (Function.support Φ) := by
    exact (hlc.isClopen_fiber (0 : ℂ)).compl.isClosed
  have hts : tsupport Φ = Function.support Φ := hclosed.closure_eq
  have hsub : tsupport Φ ⊆ {Y | Y.rank = a} := by
    intro Y hY
    rw [hts] at hY
    by_contra h
    exact hY (hrank Y h)
  refine ⟨s '' tsupport Φ, hcs.isCompact.image_of_continuousOn (hs.mono hsub), ?_⟩
  intro g Z hZ hne
  have hY : g.val * Z ∈ tsupport Φ := subset_tsupport _ hne
  have hr : (g.val * Z).rank = a := hsub hY
  have h1 : ((s (g.val * Z))⁻¹ * g).val * Z ∈ slice (k := k) a d := by
    rw [Units.val_mul, Matrix.mul_assoc]
    exact hsl _ hr
  have h2 := huniq Z _ hZ h1
  have : g = s (g.val * Z) := by
    rw [inv_mul_eq_one] at h2
    exact h2.symm
  exact ⟨g.val * Z, hY, this.symm⟩

end GlobalTheory.RankFibreKer
end

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer


theorem _root_.GlobalTheory.T.continuous_slice_section_measure : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Φ : Matrix (Fin a) (Fin d) k → ℂ), Φ ∈ fullRankSB (k := k) a d →
    ∀ (s : Matrix (Fin a) (Fin d) k → GL (Fin a) k), ContinuousOn s {Y | Y.rank = a} →
    (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank = a → ((s Y)⁻¹).val * Y ∈ slice (k := k) a d) →
    (∀ (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice (k := k) a d → g.val * Z ∈ slice (k := k) a d → g = 1) →
    ∃ C : Set (GL (Fin a) k), IsCompact C ∧ ∀ (g : GL (Fin a) k) (Z : Matrix (Fin a) (Fin d) k), Z ∈ slice (k := k) a d →
      Φ (g.val * Z) ≠ 0 → g ∈ C := by
  intro k _ _ _ _ a d Φ hΦ s hs hsl huniq
  obtain ⟨⟨hlc, hcs⟩, hrank⟩ := hΦ
  have hclosed : IsClosed (Function.support Φ) :=
    (hlc.isClopen_fiber (0 : ℂ)).compl.isClosed
  have hsub : tsupport Φ ⊆ {Y | Y.rank = a} := by
    change closure (Function.support Φ) ⊆ _
    rw [hclosed.closure_eq]
    intro Y hY
    by_contra h
    exact hY (hrank Y h)
  refine ⟨s '' tsupport Φ, hcs.isCompact.image_of_continuousOn (hs.mono hsub), ?_⟩
  intro g Z hZ hne
  have hY : g.val * Z ∈ tsupport Φ := subset_tsupport _ hne
  have hslice : ((s (g.val * Z))⁻¹ * g).val * Z ∈ slice (k := k) a d := by
    rw [Units.val_mul, Matrix.mul_assoc]
    exact hsl _ (hsub hY)
  have heq := huniq Z _ hZ hslice
  rw [inv_mul_eq_one] at heq
  exact ⟨g.val * Z, hY, heq⟩
end

section

open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

namespace GlobalTheory.RankFibreKer

theorem integral_tw_eq_zero_of_fibre_eq_zero :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
    fibre ν β a b Φ = 0 → ∀ Y : Matrix (Fin a) (Fin (a + b)) k, Y.rank = a →
    ∫ g : GL (Fin a) k, Φ (g.val * Y) * tw ν (a + b) g ∂(haarVol (KO k (Fin a))) = 0 := by
  intro k _ _ _ _ _ _ ν β a b Φ hF Y hY
  obtain ⟨h, hYh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock (k := k) finSumFinEquiv Y).1 (by rw [hY, Fintype.card_fin])
  have e := congrFun hF h
  have hC : (β (gdet h) : ℂ) * apow (gdet h) (-(a : ℂ) / 2) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
  have key : ∀ g : GL (Fin a) k, omA ν β 1 h Φ (g.val * X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) *
      apow (gdet g) (((a + b : ℕ) : ℂ) / 2) = ((β (gdet h) : ℂ) * apow (gdet h) (-(a : ℂ) / 2)) *
      (Φ (g.val * Y) * tw ν (a + b) g) := by
    intro g
    have hm : g.val * Y = (((((1 : GL (Fin a) k)⁻¹).val * ((g.val * X0 k finSumFinEquiv : Matrix (Fin a) (Fin (a + b)) k))
        : Matrix (Fin a) (Fin (a + b)) k)) * (invT h).val : Matrix (Fin a) (Fin (a + b)) k) := by
      rw [inv_one, Units.val_one, Matrix.one_mul, hYh]
      exact (Matrix.mul_assoc _ _ _).symm
    rw [hm]
    simp only [omA, tw, Fintype.card_fin, map_one, inv_one, Units.val_one, apow_one]
    ring
  simp only [fibre, Pi.zero_apply, key, integral_const_mul] at e
  exact (mul_eq_zero.1 e).resolve_left hC

end GlobalTheory.RankFibreKer
end

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.UnitMinor

theorem isClopen_setOf_valuation_eq_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : IsClopen {x : k | valuation k x = 1} := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hy
    rw [IsValuativeTopology.mem_nhds_iff']
    by_cases h0 : y = 0
    · subst h0
      refine ⟨1, fun z hz ↦ ?_⟩
      simp only [Set.mem_ofPred_eq, Units.val_one, sub_zero, Set.mem_compl_iff, Set.mem_setOf_eq] at hz ⊢
      exact hz.ne
    · have hv : valuation k y ≠ 0 := by simpa using h0
      refine ⟨Units.mk0 _ hv, fun z hz ↦ ?_⟩
      simp only [Set.mem_ofPred_eq, Units.val_mk0, Set.mem_compl_iff, Set.mem_setOf_eq] at hz ⊢
      have : z = y + (z - y) := by ring
      rw [this, (valuation k).map_add_eq_of_lt_left hz]
      exact hy
  · rw [isOpen_iff_mem_nhds]
    intro y hy
    rw [IsValuativeTopology.mem_nhds_iff']
    refine ⟨1, fun z hz ↦ ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_one, Set.mem_setOf_eq] at hz hy ⊢
    have : z = y + (z - y) := by ring
    rw [this, (valuation k).map_add_eq_of_lt_left (by rw [hy]; exact hz), hy]

theorem isClopen_unitMinorSet (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n d : ℕ) : IsClopen (unitMinorSet k n d) := by
  have hI : IsClopen {A : Matrix (Fin n) (Fin d) k | ∀ i j, A i j ∈ 𝒪[k]} := by
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
    exact ⟨isCompact_intMatrix.isClosed, isOpen_intMatrix⟩
  have hU : IsClopen (⋃ f : Fin n ↪ Fin d,
      (fun Y : Matrix (Fin n) (Fin d) k ↦ (Y.submatrix id f).det) ⁻¹' {x : k | valuation k x = 1}) := by
    refine isClopen_iUnion_of_finite fun f ↦ (isClopen_setOf_valuation_eq_one k).preimage ?_
    exact Continuous.matrix_det (Continuous.matrix_submatrix continuous_id _ _)
  have e : unitMinorSet k n d = {A : Matrix (Fin n) (Fin d) k | ∀ i j, A i j ∈ 𝒪[k]} ∩ ⋃ f : Fin n ↪ Fin d,
      (fun Y : Matrix (Fin n) (Fin d) k ↦ (Y.submatrix id f).det) ⁻¹' {x : k | valuation k x = 1} := by
    ext Y; simp [unitMinorSet]
  rw [e]; exact hI.inter hU

end GlobalTheory.FullRankCoinv.UnitMinor
end

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory

theorem unitMinorSet_rank_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (Y : Matrix (Fin n) (Fin d) k), Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → Y.rank = n := by
  intro k _ _ _ _ n d Y hY
  obtain ⟨-, f, hf⟩ := hY
  have hdet : (Y.submatrix id f).det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hf
    exact zero_ne_one hf
  have hunit : IsUnit (Y.submatrix id f) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hsub : (Y.submatrix id f).rank = n := by
    rw [Matrix.rank_of_isUnit _ hunit, Fintype.card_fin]
  have hmul : Y * (1 : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl (Fin d)) f = Y.submatrix id f := by
    rw [Matrix.mul_submatrix_one]; rfl
  apply le_antisymm (Matrix.rank_le_height Y)
  calc n = (Y.submatrix id f).rank := hsub.symm
    _ = (Y * (1 : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl (Fin d)) f).rank := by rw [hmul]
    _ ≤ Y.rank := Matrix.rank_mul_le_left _ _

end GlobalTheory
end

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.UnitMinorStable

theorem mul_mem_unitMinorSet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k), E ∈ GlobalTheory.SplitWeil.KO k (Fin n) →
    Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d := by
  intro k _ _ _ _ n d E Y hE hY
  obtain ⟨hYi, f, hf⟩ := hY
  have hEi := ((GlobalTheory.SplitFlip.mem_KO_iff E).1 hE).1
  refine ⟨fun i j => ?_, f, ?_⟩
  · rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hEi i l) (hYi l j)
  · have hsub : (E.val * Y).submatrix id f = E.val * Y.submatrix id f := by
      ext i j; rfl
    have hdet := GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO hE
    have hg : ((GlobalTheory.SplitFlip.gdet E : kˣ) : k) = E.val.det := rfl
    rw [hsub, Matrix.det_mul, map_mul, hf, mul_one, ← hg, hdet]

end GlobalTheory.UnitMinorStable
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_local_holomorphic_extension_near_zeros : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ hS : (A.zeroSet s).Finite, (∀ P ∈ A.zeroSet s, jacAt A s P ≠ 0) → ∀ (f : Y → ℂ) (δ : ℝ), 0 < δ → ∃ (Ω : Set Y) (h : ι → Y → ℂ) (m : ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) ∧ 0 < m ∧ (∀ y, A.sqn L s y < m → y ∈ Ω) ∧ (∀ P ∈ A.zeroSet s, h (A.pick P) P = f P) ∧ (∀ T : ℝ, 2 ≤ T → ∫⁻ y in {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu ≤ ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ * ∑ P ∈ hS.toFinset, resSq A E L s P (f P))) ∧ ∫⁻ y, ENNReal.ofReal (1 / (1 + (δ * psi A L s y) ^ 2) * A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu < ⊤ := by
  first | exact @GlobalTheory.OTY.exists_local_extension | exact GlobalTheory.OTY.exists_local_extension | (intros; apply GlobalTheory.OTY.exists_local_extension <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.grpHom_algebraisation_of_reductions : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (A B : Over (Spec (CommRingCat.of R))) [GrpObj A] [GrpObj B], IsProper A.hom → IsProper B.hom → ∀ (Y Z : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] [∀ e, GrpObj (Z e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (δ : ∀ e, (Z e).left ⟶ (Z (e + 1)).left) (a : ∀ e, (Y e).left ⟶ A.left) (b : ∀ e, (Z e).left ⟶ B.left), (∀ e, IsGrpPullback (Y e) A (thick R I e) (a e)) → (∀ e, β e ≫ a (e + 1) = a e) → (∀ e, IsGrpPullback (Z e) B (thick R I e) (b e)) → (∀ e, δ e ≫ b (e + 1) = b e) → ∀ f : ∀ e, Y e ⟶ Z e, (∀ e, IsMonHom (f e)) → (∀ e, β e ≫ (f (e + 1)).left = (f e).left ≫ δ e) → ∃ g : A ⟶ B, IsMonHom g ∧ (∀ e, a e ≫ g.left = (f e).left ≫ b e) ∧ ∀ g' : A ⟶ B, (∀ e, a e ≫ g'.left = (f e).left ≫ b e) → g' = g := by
  first | exact @GlobalTheory.grpHom_algebraise | exact GlobalTheory.grpHom_algebraise | (intros; apply GlobalTheory.grpHom_algebraise <;> assumption)
end
