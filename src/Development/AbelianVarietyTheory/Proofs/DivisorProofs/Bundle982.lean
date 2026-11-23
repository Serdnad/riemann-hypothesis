module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle975
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle963
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle977
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle012
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle965
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle492
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals
open scoped nonZeroDivisors

namespace GlobalTheory.ZetaDenom

theorem eulerStep {F : Type} [Field F] [NumberField F] (𝔪 𝔭 : Ideal (𝓞 F)) (hmax : 𝔭.IsMaximal) (hp : 𝔭 ≠ ⊥) (hcop : 𝔭 ⊔ 𝔪 = ⊤)
    (C : ClassGroup (𝓞 F)) (Z Z' : ℂ → ℂ) (hZ : IsRayL 𝔪 (wideInd C) Z) (hZ' : IsRayL 𝔪 (wideInd (C * (cls 𝔭)⁻¹)) Z') :
    IsRayL (𝔪 * 𝔭) (wideInd C) (fun s => Z s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Z' s) :=
  GlobalTheory.T.isNarrowRayClassLFunction_mul_prime_wideIndicator 𝔪 𝔭 hmax hp hcop C Z Z' hZ hZ'

theorem isRayL_top_iff {F : Type} [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ) :
    IsRayL (⊤ : Ideal (𝓞 F)) (wideInd C) Z ↔ IsClassZeta C Z :=
  GlobalTheory.T.isNarrowRayClassLFunction_top_wideIndicator_iff C Z

theorem primesOver_exists {F : Type} [Field F] [NumberField F] (l : ℕ) (hl : l.Prime) :
    ∃ P : Finset (Ideal (𝓞 F)), (∀ 𝔭 ∈ P, 𝔭.IsMaximal ∧ 𝔭 ≠ ⊥ ∧ l ∣ Ideal.absNorm 𝔭) ∧
      ∀ I : Ideal (𝓞 F), CoprimeTo F (∏ 𝔭 ∈ P, 𝔭) I ↔ CoprimeTo F (Ideal.span {(l : 𝓞 F)}) I :=
  GlobalTheory.T.exists_finite_primes_over_prime_coprimality_equiv l hl

theorem inZl_of_shift {G : Type} [CommGroup G] [Finite G] (l : ℕ) [Fact l.Prime] (g : G) (q : ℕ) (hq : l ∣ q)
    (x : G → ℚ) (h : ∀ C, InZl l (x C - (q : ℚ) * x (C * g))) (C : G) : InZl l (x C) :=
  GlobalTheory.T.isRatInPadicIntegers_of_twisted_difference l g q hq x h C

theorem cE_le_of_inZl {F : Type} [Field F] [NumberField F] (z : ClassGroup (𝓞 F) → ℚ) (l a n : ℕ) [Fact l.Prime]
    (ha : 2 ≤ a) (hn : 1 ≤ n) (h : ∀ C, InZl l (((a ^ n - 1 : ℕ) : ℚ) * z C)) :
    cE z l ≤ finrank ℚ F * padicValNat l 2 + padicValNat l (a ^ n - 1) :=
  GlobalTheory.T.partialZetaDenominatorExponent_le_of_integral z l a n ha hn h

theorem mMin_eq_mE (hmin : Formalism.PairingDivisionLocalBalance.MinVal) (l n : ℕ) (hl : l.Prime) (hn : 2 ≤ n) (he : Even n) :
    mMin l n = Formalism.PairingDivisionLocalBalance.mE l n :=
  GlobalTheory.T.minPadicValPowSubOneCoprime_eq_closedFormula hmin l n hl hn he

theorem sumBound_of_local {F : Type} [Field F] [NumberField F] (hsum : Formalism.PairingDivisionLocalBalance.CESum) (k : ℕ)
    (z : ClassGroup (𝓞 F) → ℚ) (hk : 2 ≤ k) (h16 : 16 ≤ finrank ℚ F * k)
    (h : ∀ l : ℕ, l.Prime → cE z l ≤ finrank ℚ F * padicValNat l 2 + Formalism.PairingDivisionLocalBalance.mE l (finrank ℚ F * k)) : SumBound k z :=
  GlobalTheory.T.partialZetaDenomSumBound_of_local_bounds hsum k z hk h16 h

theorem isRayL_of_coprime_iff {F : Type} [Field F] [NumberField F] {𝔣 𝔤 : Ideal (𝓞 F)}
    (h : ∀ I, CoprimeTo F 𝔣 I ↔ CoprimeTo F 𝔤 I) {ε : Ideal (𝓞 F) → ℚ} {L : ℂ → ℂ} (hL : IsRayL 𝔣 ε L) : IsRayL 𝔤 ε L :=
  ⟨hL.1, fun s hs => (Equiv.subtypeEquivRight fun I => (h I).symm).hasSum_iff
    (f := fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I} => (ε I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) |>.2 (hL.2 s hs)⟩

theorem exists_isZetaValues (h : GlobalTheory.Published.SiegelKlingen) (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ)
    (hk : 1 ≤ k) : ∃ z : ClassGroup (𝓞 F) → ℚ, IsZetaValues k z := by
  have : ∀ C : ClassGroup (𝓞 F), ∃ r : ℚ, ∃ Z : ℂ → ℂ, IsClassZeta C Z ∧ Z (1 - (k : ℂ)) = (r : ℂ) := by
    intro C
    obtain ⟨L, hL, hv⟩ := h F ⊤ top_ne_bot (wideInd C) (isRayFun_wideInd _ C)
    obtain ⟨r, hr⟩ := hv k hk
    exact ⟨r, L, (isRayL_top_iff C L).1 hL, hr⟩
  choose z hz using this
  exact ⟨z, hz⟩

theorem inZl_mul_zeta (h : GlobalTheory.Published.DeligneRibet) (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (l : ℕ) [hl : Fact l.Prime] (a k : ℕ) (ha : 2 ≤ a) (hac : a.Coprime l) (hk : 2 ≤ k)
    (z : ClassGroup (𝓞 F) → ℚ) (hz : IsZetaValues k z) (C : ClassGroup (𝓞 F)) :
    InZl l (((a ^ (finrank ℚ F * k) - 1 : ℕ) : ℚ) * z C) := by
  classical
  obtain ⟨P, hP, hPc⟩ := primesOver_exists (F := F) l hl.out
  set c : ℚ := ((a ^ (finrank ℚ F * k) - 1 : ℕ) : ℚ) with hcdef
  let St : Finset (Ideal (𝓞 F)) → Prop := fun T => ∀ x : ClassGroup (𝓞 F) → ℚ,
    (∀ C, ∃ Z : ℂ → ℂ, IsRayL (∏ 𝔭 ∈ T, 𝔭) (wideInd C) Z ∧ Z (1 - (k : ℂ)) = (x C : ℂ)) → ∀ C, InZl l (c * x C)

  have hfull : St P := by
    intro x hx C
    obtain ⟨Z, hZ, e⟩ := hx C
    have hZ1 : IsRayL (powMod F l 1) (wideInd C) Z :=
      isRayL_of_coprime_iff (fun I => by rw [hPc, coprimeTo_powMod_iff le_rfl]) hZ
    have ha0 : (a : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hcop : CoprimeTo F (powMod F l 1) (Ideal.span {(a : 𝓞 F)}) := by
      rw [coprimeTo_powMod_iff le_rfl]
      refine ⟨by simpa using ha0, ?_⟩
      rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
      simpa using (Nat.isCoprime_iff_coprime.2 hac).map (Int.castRingHom (𝓞 F))
    have hv : IsRayValue (powMod F l 1) (wideInd C) k (x C) := ⟨Z, hZ1, e⟩
    have hv' : IsRayValue (powMod F l 1) (translate (Ideal.span {(a : 𝓞 F)}) (wideInd C)) k (x C) := by
      rw [translate_wideInd ha0]; exact hv
    have hint : ∀ I, CoprimeTo F (powMod F l 1) I → InZl l (wideInd C I) := fun I _ => by
      unfold wideInd; split_ifs <;> simp [InZl]
    have := h F l 1 le_rfl (wideInd C) (isRayFun_wideInd _ C) hint _ hcop k (by omega) (x C) (x C) hv hv'
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank] at this
    have e2 : c * x C = -(x C - (((a ^ finrank ℚ F : ℕ) : ℚ)) ^ k * x C) := by
      rw [hcdef, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]; push_cast; ring
    rw [e2, inZl_iff, padicValRat.neg, ← inZl_iff]; exact this

  have step : ∀ (T : Finset (Ideal (𝓞 F))) (𝔭 : Ideal (𝓞 F)), 𝔭 ∉ T → 𝔭 ∈ P → T ⊆ P → St (insert 𝔭 T) → St T := by
    intro T 𝔭 h𝔭T h𝔭P hTP hSt x hx
    choose Zf hZf eZ using hx
    obtain ⟨hmax, hne, hdvd⟩ := hP 𝔭 h𝔭P
    have hcopT : 𝔭 ⊔ ∏ 𝔮 ∈ T, 𝔮 = ⊤ := by
      rw [← Ideal.isCoprime_iff_sup_eq]
      refine IsCoprime.prod_right fun 𝔮 h𝔮 => Ideal.isCoprime_iff_sup_eq.2 ?_
      exact Ideal.IsMaximal.coprime_of_ne hmax (hP 𝔮 (hTP h𝔮)).1 (fun e => h𝔭T (e ▸ h𝔮))
    set q : ℕ := Ideal.absNorm 𝔭 ^ (k - 1) with hqdef
    have hy : ∀ C, ∃ Z : ℂ → ℂ, IsRayL (∏ 𝔮 ∈ insert 𝔭 T, 𝔮) (wideInd C) Z ∧
        Z (1 - (k : ℂ)) = ((x C - (q : ℚ) * x (C * (cls 𝔭)⁻¹) : ℚ) : ℂ) := by
      intro C
      refine ⟨fun s => Zf C s - ((Ideal.absNorm 𝔭 : ℕ) : ℂ) ^ (-s) * Zf (C * (cls 𝔭)⁻¹) s, ?_, ?_⟩
      · rw [Finset.prod_insert h𝔭T, mul_comm]
        exact eulerStep _ 𝔭 hmax hne hcopT C _ _ (hZf C) (hZf _)
      · have e1 : -(1 - (k : ℂ)) = ((k - 1 : ℕ) : ℂ) := by rw [Nat.cast_sub (by omega)]; push_cast; ring
        simp only [e1, Complex.cpow_natCast, eZ, hqdef]
        push_cast; ring
    have := hSt _ hy
    intro C
    have hmul := inZl_of_shift l ((cls 𝔭)⁻¹) q (dvd_pow hdvd (by omega)) (fun C => c * x C)
      (fun C => by have := this C; rwa [mul_sub, mul_left_comm] at this) C
    exact hmul
  have key : ∀ U : Finset (Ideal (𝓞 F)), U ⊆ P → St (P \ U) := by
    intro U
    induction U using Finset.induction_on with
    | empty => intro _; simpa using hfull
    | insert 𝔭 U h𝔭U ih =>
      intro hU
      have h𝔭P : 𝔭 ∈ P := hU (Finset.mem_insert_self _ _)
      have ih := ih ((Finset.subset_insert _ _).trans hU)
      have e : P \ U = insert 𝔭 (P \ insert 𝔭 U) := by
        ext 𝔮; simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩; by_cases h : 𝔮 = 𝔭 <;> simp_all
        · rintro (h | ⟨h1, h2⟩)
          · subst h; exact ⟨h𝔭P, h𝔭U⟩
          · exact ⟨h1, fun h => h2 (Or.inr h)⟩
      rw [e] at ih
      exact step _ 𝔭 (by simp) h𝔭P Finset.sdiff_subset ih
  have h0 := key P subset_rfl
  rw [Finset.sdiff_self] at h0
  refine h0 z (fun C => ?_) C
  obtain ⟨Z, hZ, e⟩ := hz C
  exact ⟨Z, by rw [Finset.prod_empty, Ideal.one_eq_top]; exact (isRayL_top_iff C Z).2 hZ, e⟩

theorem zetaDenominators (h : GlobalTheory.Published.SiegelKlingenDeligneRibet) : ZetaDenominators := by
  apply ZetaDenominatorsReal.cm
  intro F _ _ _ s hs
  have hf : 1 ≤ finrank ℚ F := (Module.finrank_pos : 0 < finrank ℚ F)
  have hn2 : 2 ≤ finrank ℚ F * (2 * s) := by nlinarith
  have hev : Even (finrank ℚ F * (2 * s)) := ⟨finrank ℚ F * s, by ring⟩
  have hloc : ∀ z : ClassGroup (𝓞 F) → ℚ, IsZetaValues (2 * s) z → ∀ l : ℕ, l.Prime → LocalBound (2 * s) z l := by
    intro z hz l hl
    haveI := Fact.mk hl
    have hm := mMin_eq_mE GlobalTheory.T.dividedPowerValuations_minVal l _ hl hn2 hev
    obtain ⟨a, ha2, hac, hv⟩ := GlobalTheory.T.dividedPowerValuations_minVal l _ hl hn2 hev
    have hc := cE_le_of_inZl (F := F) z l a _ ha2 (by omega) (inZl_mul_zeta h.2 F l a (2 * s) ha2 hac (by omega) z hz)
    rw [hv] at hc
    refine ⟨by rw [hm]; exact hc, fun h2 hd => ?_, fun h2 hd => ?_, fun h2 => ?_⟩ <;> rw [hm] <;> simp [Formalism.PairingDivisionLocalBalance.mE, *]
  refine ⟨exists_isZetaValues h.1 F (2 * s) (by omega), fun z hz => ⟨hloc z hz, fun h16 =>
    sumBound_of_local GlobalTheory.T.cmValues_exponent_log_sum_le (2 * s) z (by omega) h16 fun l hl => ?_⟩⟩
  have h1 := hloc z hz l hl
  have h2 := h1.1
  rwa [h1.mMin_eq] at h2

end GlobalTheory.ZetaDenom
end
end

section

noncomputable section

namespace GlobalTheory.Proof.WeightSequenceEntries

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

theorem padZero_eq {a : ℕ} (b : ℕ) (ν : DomWeight a) (j : Fin b) :
    PaddedWittNormSquare.padZero b ν j = PaddedLastEntry.padZero b ν j := rfl

theorem lastEntry_eq {a : ℕ} (ν : DomWeight a) : PaddedWittNormSquare.lastEntry ν = PaddedLastEntry.lastEntry ν := rfl

theorem normSq_eq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (v : VV ℂ lam) :
    PaddedWittNormSquare.normSq lam v = PaddedLastEntry.invNormSq lam v := rfl

theorem unitSq_eq {ι : Type} [Fintype ι] {a b : ℕ} (r : ι → ℝ) (z : VCx ι a b) :
    PaddedWittNormSquare.unitNormSq r z = PaddedLastEntry.unitSq r z := rfl

theorem tmax_eq {ι : Type} [Fintype ι] {a : ℕ} (b : ℕ) (ν : ι → DomWeight a) (Om : ι → ℝ) (S : ℝ) :
    PaddedWittNormSquare.tmax b ν Om S = PaddedLastEntry.tmax b ν S Om := rfl

theorem opNormSqLe_iff {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (t : ℝ) :
    PaddedWittNormSquare.OpNormSqLe lam lam' T t ↔ PaddedLastEntry.OpNormSqLe lam lam' T t := by
  unfold PaddedWittNormSquare.OpNormSqLe PaddedLastEntry.OpNormSqLe
  simp only [normSq_eq]

theorem stepWeights_iff {a b : ℕ} (lam ν : DomWeight a) (lam' : DomWeight b) :
    (∃ s' s : ℤ, PaddedWittNormSquare.IsStepWeight lam ν lam' s' s) ↔ PaddedLastEntry.StepWeights lam ν lam' := by
  unfold PaddedWittNormSquare.IsStepWeight PaddedLastEntry.StepWeights
  constructor
  · rintro ⟨s', s, hν, hpos, hpad⟩
    exact ⟨hpos, ⟨s', hν⟩, ⟨s, fun j => (hpad j).trans (padZero_eq b ν j)⟩⟩
  · rintro ⟨hpos, ⟨s', hν⟩, ⟨s, hpad⟩⟩
    exact ⟨s', s, hν, hpos, fun j => (hpad j).trans (padZero_eq b ν j).symm⟩

theorem stepWeights_family_iff {ι : Type} {a b : ℕ} (lam ν : ι → DomWeight a) (lam' : ι → DomWeight b) :
    (∃ s' s : ι → ℤ, ∀ τ, PaddedWittNormSquare.IsStepWeight (lam τ) (ν τ) (lam' τ) (s' τ) (s τ)) ↔
      ∀ τ, PaddedLastEntry.StepWeights (lam τ) (ν τ) (lam' τ) := by
  constructor
  · rintro ⟨s', s, h⟩ τ
    exact (stepWeights_iff (lam τ) (ν τ) (lam' τ)).1 ⟨s' τ, s τ, h τ⟩
  · intro h
    choose s' s hs using fun τ => (stepWeights_iff (lam τ) (ν τ) (lam' τ)).2 (h τ)
    exact ⟨s', s, hs⟩

theorem guard_iff {ι : Type} {a b : ℕ} (hab : a ≤ b) (ν : ι → DomWeight a) :
    (∀ τ, a < b ∨ PaddedWittNormSquare.lastEntry (ν τ) = 0) ↔ (a = b → ∀ τ, PaddedLastEntry.lastEntry (ν τ) = 0) := by
  constructor
  · intro h heq τ
    rcases h τ with hlt | h0
    · exact absurd heq (ne_of_lt hlt)
    · exact (lastEntry_eq (ν τ)).symm.trans h0
  · intro h τ
    rcases lt_or_eq_of_le hab with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ((lastEntry_eq (ν τ)).trans (h heq τ))

theorem growth_iff {ι : Type} [Fintype ι] {a b : ℕ} (G : VCx ι a b → ℂ) (S : ℝ) (r : ι → ℝ) :
    (∀ z, ‖G z‖ ≤ S * Real.exp (PaddedWittNormSquare.unitNormSq r z / 2)) ↔
      ∀ z, ‖G z‖ ≤ S * Real.exp (PaddedLastEntry.unitSq r z / 2) := by
  simp only [unitSq_eq]

theorem conclusion_iff {ι : Type} [Fintype ι] {a b : ℕ} (lam ν : ι → DomWeight a) (lam' : ι → DomWeight b)
    (G : VCx ι a b → ℂ) (S : ℝ) (Om : ι → ℝ) (cD : ι → ℂ) :
    PaddedWittNormSquare.OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => PaddedWittNormSquare.lastEntry (ν τ)) (PaddedWittNormSquare.tmax b ν Om S) ↔
      PaddedLastEntry.OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => PaddedLastEntry.lastEntry (ν τ)) (PaddedLastEntry.tmax b ν S Om) := by
  simp only [opNormSqLe_iff, tmax_eq, lastEntry_eq]

theorem blockBound_iff : PaddedWittNormSquare.BlockBound ↔ PaddedLastEntry.BlockBound := by
  unfold PaddedWittNormSquare.BlockBound PaddedLastEntry.BlockBound
  constructor
  · intro h ι _ a b hab lam ν lam' hstep hguard r Om cD hr hOm hc G S hG hgrowth
    obtain ⟨s', s, hs⟩ := (stepWeights_family_iff lam ν lam').2 hstep
    exact (conclusion_iff lam ν lam' G S Om cD).1
      (h ι a b hab lam ν lam' s' s hs ((guard_iff hab ν).2 hguard) G S r Om cD hG hr
        ((growth_iff G S r).2 hgrowth) hOm hc)
  · intro h ι _ a b hab lam ν lam' s' s hs hguard G S r Om cD hG hr hgrowth hOm hc
    exact (conclusion_iff lam ν lam' G S Om cD).2
      (h ι a b hab lam ν lam' ((stepWeights_family_iff lam ν lam').1 ⟨s', s, hs⟩)
        ((guard_iff hab ν).1 hguard) r Om cD hr hOm hc G S hG ((growth_iff G S r).1 hgrowth))

end GlobalTheory.Proof.WeightSequenceEntries
end
end

section

open CategoryTheory AlgebraicGeometry GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.SecPowLoc

theorem fnOf_map {X : Scheme.{0}} [IsIntegral X] {U V : X.Opens} (i : V ⟶ U)
    (h : genericPoint X ∈ V) (a : Γ(X, U)) :
    fnOf V h (X.presheaf.map i.op a) = fnOf U (i.le h) a :=
  X.presheaf.germ_res_apply i _ h a

end GlobalTheory.Cartier.SecPowLoc

namespace GlobalTheory.Cartier


end GlobalTheory.Cartier
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem smul_comm_of_finrank_one (D : Datum H) (h : Module.finrank (𝓞 E) D.La = 1)
    (l : D.La →ₗ[𝓞 E] 𝓞 E) (x y : D.La) : l x • y = l y • x := by
  have := D.fin
  have := D.proj
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨r, s, hr, e⟩ := CMLat.exists_smul_eq_smul h hx y
  have hl : r * l y = s * l x := by rw [← smul_eq_mul, ← map_smul, e, map_smul, smul_eq_mul]
  have h0 : r • (l x • y - l y • x) = 0 := by
    rw [smul_sub, smul_comm r (l x) y, e, smul_smul, smul_smul, hl, mul_comm, sub_self]
  rw [smul_eq_zero] at h0
  exact sub_eq_zero.1 (h0.resolve_left hr)

theorem exists_dualBasis (D : Datum H) :
    ∃ (n : ℕ) (a : Fin n → D.La) (l : Fin n → (D.La →ₗ[𝓞 E] 𝓞 E)), ∀ x, ∑ k, l k x • a k = x := by
  have := D.fin
  have := D.proj
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) D.La
  refine ⟨n, fun k => f (fun j => if k = j then 1 else 0), fun k => LinearMap.proj k ∘ₗ g, fun x => ?_⟩
  have hx : f (g x) = x := LinearMap.congr_fun hfg x
  conv_rhs => rw [← hx, LinearMap.pi_apply_eq_sum_univ f (g x)]
  rfl

theorem exists_sum_comp_eq_id (DA DB : Datum H) (hA : DA.p + DA.q = 1) :
    ∃ (n : ℕ) (α : Fin n → (DA.La →ₗ[𝓞 E] DB.La)) (β : Fin n → (DB.La →ₗ[𝓞 E] DA.La)),
      ∑ i, α i ∘ₗ β i = LinearMap.id := by
  have := DA.fin
  have := DA.proj
  have hr : Module.finrank (𝓞 E) DA.La = 1 := by rw [DA.rank, hA]
  obtain ⟨n, a, l, decA⟩ := exists_dualBasis DA
  obtain ⟨m, b, mu, decB⟩ := exists_dualBasis DB
  have tr : ∑ k, l k (a k) = 1 := by
    have : Nontrivial DA.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [hr]; exact one_pos)
    obtain ⟨x, hx⟩ := exists_ne (0 : DA.La)
    have e : (∑ k, l k (a k)) • x = (1 : 𝓞 E) • x := by
      rw [Finset.sum_smul, one_smul]
      conv_rhs => rw [← decA x]
      exact Finset.sum_congr rfl fun k _ => smul_comm_of_finrank_one DA hr (l k) (a k) x
    have h0 : ((∑ k, l k (a k)) - 1) • x = 0 := by rw [sub_smul, e, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_right hx)
  refine ⟨n * m, fun i => (l (finProdFinEquiv.symm i).1).smulRight (b (finProdFinEquiv.symm i).2),
    fun i => (mu (finProdFinEquiv.symm i).2).smulRight (a (finProdFinEquiv.symm i).1), ?_⟩
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.sum_apply, LinearMap.id_apply]
  rw [finProdFinEquiv.symm.sum_comp (fun p : Fin n × Fin m =>
    ((l p.1).smulRight (b p.2) ∘ₗ (mu p.2).smulRight (a p.1)) y), Fintype.sum_prod_type, Finset.sum_comm]
  conv_rhs => rw [← decB y]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [LinearMap.comp_apply, LinearMap.smulRight_apply, map_smul, smul_eq_mul, smul_smul]
  rw [← Finset.sum_smul, ← Finset.mul_sum, tr, _root_.mul_one]

end GlobalTheory.CM
end

noncomputable section
namespace GlobalTheory.CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] {ω : R}
  {C : Ell H R ω}

theorem IsTen.isLinearHom_mapLeft {A B : PAT H (Sp R)} {DA DB : Datum H} {hA : DA.La → DA.La → OK H}
    {hB : DB.La → DB.La → OK H} (tA : IsTen C DA hA A) (tB : IsTen C DB hB B) (φ : DA.La →ₗ[𝓞 E] DB.La) :
    Serre.IsLinearHom A.t.act B.t.act (tA.ten.mapLeft tB.ten (φ.restrictScalars (OK H))) := by
  refine ⟨inferInstance, fun s => ?_⟩
  have := A.t.act.hom s
  have := B.t.act.hom s
  refine tA.ten.hom_ext fun m => ?_
  rw [← Category.assoc, ← tA.lin, Serre.IsTensor.tmul_mapLeft, ← Category.assoc, Serre.IsTensor.tmul_mapLeft,
    LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, map_smul, tB.lin]

theorem IsTen.prod_mapLeft {B : PAT H (Sp R)} {DB : Datum H} {hB : DB.La → DB.La → OK H}
    (tB : IsTen C DB hB B) {I : Type} (s : Finset I) (φ : I → (DB.La →ₗ[𝓞 E] DB.La)) :
    ∏ i ∈ s, tB.ten.mapLeft tB.ten ((φ i).restrictScalars (OK H)) =
      tB.ten.mapLeft tB.ten ((∑ i ∈ s, φ i).restrictScalars (OK H)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, LinearMap.restrictScalars_zero, Serre.IsTensor.mapLeft_zero]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, LinearMap.restrictScalars_add, Serre.IsTensor.mapLeft_add]

theorem isTen_retract_of_rank_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (A B : PAT H (Sp R)) (DA DB : Datum H)
    (hA : DA.La → DA.La → OK H) (hB : DB.La → DB.La → OK H), DA.p + DA.q = 1 → IsTen C DA hA A → IsTen C DB hB B →
    ∃ (n : ℕ) (f : Fin n → (A.t.G ⟶ B.t.G)) (g : Fin n → (B.t.G ⟶ A.t.G)),
      (∀ i, Serre.IsLinearHom A.t.act B.t.act (f i)) ∧ (∀ i, Serre.IsLinearHom B.t.act A.t.act (g i)) ∧
      ∏ i, (g i ≫ f i) = 𝟙 B.t.G := by
  intro E _ _ _ H R _ ω C A B DA DB hA hB h tA tB
  obtain ⟨n, α, β, hαβ⟩ := exists_sum_comp_eq_id DA DB h
  refine ⟨n, fun i => tA.ten.mapLeft tB.ten ((α i).restrictScalars (OK H)),
    fun i => tB.ten.mapLeft tA.ten ((β i).restrictScalars (OK H)),
    fun i => tA.isLinearHom_mapLeft tB (α i), fun i => tB.isLinearHom_mapLeft tA (β i), ?_⟩
  have e : ∀ i, tB.ten.mapLeft tA.ten ((β i).restrictScalars (OK H)) ≫ tA.ten.mapLeft tB.ten ((α i).restrictScalars (OK H))
      = tB.ten.mapLeft tB.ten ((α i ∘ₗ β i).restrictScalars (OK H)) := fun i =>
    (Serre.IsTensor.mapLeft_comp _ _ _ _ _).symm
  simp only [e]
  rw [tB.prod_mapLeft, hαβ]
  exact Serre.IsTensor.mapLeft_id _

end GlobalTheory.CM
end
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k : ℕ, 0 < m → Reg (Nat.card F) m k → IsChar ℂ ℂ (cusp θ m k) ∧ ∑ᶠ x, cusp θ m k x * star (cusp θ m k x) = (Nat.card (GL (Fin m) F) : ℂ) := by
  first | (exact @GlobalTheory.Shin.isChar_cusp_and_norm_of_reg) | (exact GlobalTheory.Shin.isChar_cusp_and_norm_of_reg) | (intros; apply GlobalTheory.Shin.isChar_cusp_and_norm_of_reg  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.twisted_virtualCharacter_norm_one_support : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) → ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) → ∀ z : ℤ, ∑ᶠ g, X (inl g) * star (Y g) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) → Kills (fun δ => X (inl δ * inr s)) Y := by
  first | (exact @GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime) | (exact GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime) | (intros; apply GlobalTheory.Shin.kills_of_norm_one_of_pairing_prime  <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin


open Polynomial SemidirectProduct in
open scoped Classical in
theorem _root_.GlobalTheory.Shin.isChar_J_of_reg : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ _root_.GlobalTheory.Shin.Reg (Nat.card F) p.1 p.2) → ∀ n, n = _root_.GlobalTheory.Shin.deg L → _root_.GlobalTheory.BI.IsChar ℂ ℂ (_root_.GlobalTheory.Shin.J θ L n) := by
  intro F _ _ θ hθ L
  induction L with
  | nil =>
    intro _ n _
    rw [_root_.GlobalTheory.Shin.J_nil]
    exact _root_.GlobalTheory.BI.isChar_one ℂ ℂ _
  | cons p L ih =>
    intro hL n hn
    rw [_root_.GlobalTheory.Shin.J_cons]
    have hp := hL p List.mem_cons_self
    refine _root_.GlobalTheory.Shin.HCChar.hc_isChar F _ _ n ?_ _ _
      (_root_.GlobalTheory.Shin.isChar_cusp_and_norm_of_reg F θ hθ p.1 p.2 hp.1 hp.2).1
      (ih (fun q hq => hL q (List.mem_cons_of_mem p hq)) _ rfl)
    rw [hn]
    simp [_root_.GlobalTheory.Shin.deg]

end GlobalTheory.Shin
end
