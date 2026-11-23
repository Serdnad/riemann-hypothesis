module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle049
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableSetPreSingleton
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
public import Formalism.DoubleCosetMeasures.StatementZ
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle120
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel

namespace GlobalTheory.SmGL

theorem exists_expMult_ne_zero_of_fixed_iwahori (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hπ : IsAdmissible π)
    (h : fixed π (iwahori k (Fin n)) ≠ ⊥) : ∃ χ : (Fin n → kˣ) →* ℂˣ, expMult π χ ≠ 0 := by
  haveI := hπ.2 _ (IwahoriOnto.isOpen_iwahori k (Fin n)) (IwahoriOnto.isCompact_iwahori k (Fin n))
  have hb := GlobalTheory.Published.BorelCasselman_holds k (Fin n) V π hπ
  haveI : FiniteDimensional ℂ (fixed (jacBU π) (torusO k (Fin n))) :=
    Module.Finite.of_surjective _ hb.2
  haveI : Nontrivial (fixed π (iwahori k (Fin n))) := Submodule.nontrivial_iff_ne_bot.2 h
  haveI : Nontrivial (fixed (jacBU π) (torusO k (Fin n))) := hb.1.nontrivial
  obtain ⟨ψ, v, hv, hψ⟩ := GlobalTheory.exists_character_eigenvector_of_commute ℂ (Fin n → kˣ) _
    (jacBUFixed π) fun a b => by rw [← map_mul, mul_comm, map_mul]
  let ι : (ofChar ψ).IntertwiningMap (jacBUFixed π) :=
    ⟨LinearMap.toSpanSingleton ℂ _ v, fun g => by
      refine LinearMap.ext_ring ?_
      simp [hψ]⟩
  exact ⟨ψ, JHMult.jhMult_ne_zero_iff.2 (IsSubquotient.of_injective ι (smul_left_injective ℂ hv))⟩

end GlobalTheory.SmGL
end

section

open Formalism.L2.Theta

namespace GlobalTheory.SignedHC.GridData

def mergedDecreasingWordPiZeroDZero (G : GridData) (p : ℕ) : ℚ :=
  if p ≤ G.m then G.a p
  else if p ≤ G.m + 2 * (G.k - 1) then
    (if (p - G.m) % 2 = 1 then (G.v ((p - G.m + 3) / 2) : ℚ) else G.vHalf ((p - G.m + 2) / 2))
  else -(G.b (p - G.m - 2 * (G.k - 1)) : ℚ)

def mergedDecreasingWordParity (G : GridData) (p : ℕ) : Bool := decide ((G.m + p) % 2 = 1)

theorem merged_word_succ_lt (G : GridData) (hga : 0 < G.ga) (hvb : 1 ≤ G.v G.k + G.b 1) {p : ℕ}
    (hp : p < 2 * G.m + 2 * (G.k - 1)) : G.mergedDecreasingWordPiZeroDZero (p + 1) < G.mergedDecreasingWordPiZeroDZero p := by
  have k2 := G.two_le_k
  have hg : (0 : ℚ) < G.ga := by exact_mod_cast hga
  unfold mergedDecreasingWordPiZeroDZero
  rcases lt_trichotomy p G.m with h | rfl | h
  · rw [if_pos (by omega : p + 1 ≤ G.m), if_pos h.le, G.a_eq_succ_add p]; linarith
  · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos le_rfl,
      show (G.m + 1 - G.m + 3) / 2 = 2 by omega, G.a_m]
    linarith
  · rw [if_neg (show ¬ p + 1 ≤ G.m by omega), if_neg (show ¬ p ≤ G.m by omega)]
    rcases lt_trichotomy p (G.m + 2 * (G.k - 1)) with h' | h' | h'
    · rw [if_pos (show p + 1 ≤ G.m + 2 * (G.k - 1) by omega), if_pos h'.le]
      by_cases hj : (p - G.m) % 2 = 1
      · rw [if_neg (show ¬ (p + 1 - G.m) % 2 = 1 by omega), if_pos hj, show (p + 1 - G.m + 2) / 2 = (p - G.m + 3) / 2 by omega, vHalf]
        linarith
      · rw [if_pos (show (p + 1 - G.m) % 2 = 1 by omega), if_neg hj, show (p + 1 - G.m + 3) / 2 = (p - G.m + 2) / 2 + 1 by omega, vHalf]
        have := G.v_anti ((p - G.m + 2) / 2) ((p - G.m + 2) / 2 + 1) (by omega) (by omega) (by omega)
        have : ((G.v ((p - G.m + 2) / 2 + 1) : ℤ) : ℚ) + 1 ≤ (G.v ((p - G.m + 2) / 2) : ℚ) := by
          exact_mod_cast this
        linarith
    · subst h'
      rw [if_neg (show ¬ G.m + 2 * (G.k - 1) + 1 ≤ G.m + 2 * (G.k - 1) by omega), if_pos le_rfl,
        if_neg (show ¬ (G.m + 2 * (G.k - 1) - G.m) % 2 = 1 by omega),
        show G.m + 2 * (G.k - 1) + 1 - G.m - 2 * (G.k - 1) = 1 by omega,
        show (G.m + 2 * (G.k - 1) - G.m + 2) / 2 = G.k by omega, vHalf]
      have : (1 : ℚ) ≤ (G.v G.k : ℚ) + (G.b 1 : ℚ) := by exact_mod_cast hvb
      linarith
    · rw [if_neg (show ¬ p + 1 ≤ G.m + 2 * (G.k - 1) by omega), if_neg (show ¬ p ≤ G.m + 2 * (G.k - 1) by omega),
        show p + 1 - G.m - 2 * (G.k - 1) = (p - G.m - 2 * (G.k - 1)) + 1 by omega]
      have := G.b_mono (p - G.m - 2 * (G.k - 1)) (p - G.m - 2 * (G.k - 1) + 1) (by omega) (by omega) (by omega)
      have : ((G.b (p - G.m - 2 * (G.k - 1)) : ℤ) : ℚ) < (G.b (p - G.m - 2 * (G.k - 1) + 1) : ℚ) := by
        exact_mod_cast this
      linarith

theorem merged_word_strict_anti (G : GridData) (hga : 0 < G.ga) (hvb : 1 ≤ G.v G.k + G.b 1) {p p' : ℕ} (h : p < p')
    (hp' : p' ≤ 2 * G.m + 2 * (G.k - 1)) : G.mergedDecreasingWordPiZeroDZero p' < G.mergedDecreasingWordPiZeroDZero p := by
  induction p' with
  | zero => omega
  | succ p' ih =>
    have h1 := G.merged_word_succ_lt hga hvb (p := p') (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact h1.trans (ih h (by omega))
    · exact h1

end GlobalTheory.SignedHC.GridData

namespace GlobalTheory.SignedHC.GridData

theorem exists_pos_of_mem_lam (G : GridData) {x : ℚ × Bool} (hx : x ∈ G.lam) :
    ∃ p ≤ 2 * G.m + 2 * (G.k - 1), x.1 = G.mergedDecreasingWordPiZeroDZero p ∧ (!x.2) = G.mergedDecreasingWordParity p := by
  have k2 := G.two_le_k
  rcases mem_lam.1 hx with ⟨i, hi, rfl⟩ | ⟨hc, hs⟩
  · refine ⟨i, by omega, by simp [mergedDecreasingWordPiZeroDZero, hi], ?_⟩
    simp only [mergedDecreasingWordParity, Nat.even_iff]
    by_cases h : (G.m - i) % 2 = 0
    · simp [h]; omega
    · simp [h]; omega
  · obtain ⟨i, hi2, hik, hv⟩ := mem_cloudHalf.1 hc
    refine ⟨G.m + 2 * i - 2, by omega, ?_, ?_⟩
    · rw [hv, mergedDecreasingWordPiZeroDZero, if_neg (show ¬ G.m + 2 * i - 2 ≤ G.m by omega),
        if_pos (show G.m + 2 * i - 2 ≤ G.m + 2 * (G.k - 1) by omega),
        if_neg (show ¬ (G.m + 2 * i - 2 - G.m) % 2 = 1 by omega),
        show (G.m + 2 * i - 2 - G.m + 2) / 2 = i by omega]
    · rw [hs, mergedDecreasingWordParity]; simp; omega

theorem exists_position_of_mem_D0 (G : GridData) {x : ℚ × Bool} (hx : x ∈ G.parD0) :
    ∃ p ≤ 2 * G.m + 2 * (G.k - 1), x.1 = G.mergedDecreasingWordPiZeroDZero p ∧ x.2 = G.mergedDecreasingWordParity p := by
  have k2 := G.two_le_k
  rcases mem_discrete_parameter_iff.1 hx with ⟨hc, hs⟩ | ⟨l, hl1, hlm, rfl⟩
  · obtain ⟨i, hi2, hik, hv⟩ := mem_cloud.1 hc
    refine ⟨G.m + 2 * i - 3, by omega, ?_, ?_⟩
    · rw [hv, mergedDecreasingWordPiZeroDZero, if_neg (show ¬ G.m + 2 * i - 3 ≤ G.m by omega),
        if_pos (show G.m + 2 * i - 3 ≤ G.m + 2 * (G.k - 1) by omega),
        if_pos (show (G.m + 2 * i - 3 - G.m) % 2 = 1 by omega),
        show (G.m + 2 * i - 3 - G.m + 3) / 2 = i by omega]
    · rw [hs, mergedDecreasingWordParity]; simp; omega
  · refine ⟨G.m + 2 * (G.k - 1) + l, by omega, ?_, ?_⟩
    · rw [mergedDecreasingWordPiZeroDZero, if_neg (show ¬ G.m + 2 * (G.k - 1) + l ≤ G.m by omega),
        if_neg (show ¬ G.m + 2 * (G.k - 1) + l ≤ G.m + 2 * (G.k - 1) by omega),
        show G.m + 2 * (G.k - 1) + l - G.m - 2 * (G.k - 1) = l by omega]
    · simp only [mergedDecreasingWordParity, Nat.even_iff]
      by_cases h : (l - 1) % 2 = 0
      · simp [h]; omega
      · simp [h]; omega

theorem mem_of_pos (G : GridData) {p : ℕ} (hp : p ≤ 2 * G.m + 2 * (G.k - 1)) :
    (∃ x ∈ G.lam, x.1 = G.mergedDecreasingWordPiZeroDZero p) ∨ ∃ x ∈ G.parD0, x.1 = G.mergedDecreasingWordPiZeroDZero p := by
  have k2 := G.two_le_k
  by_cases h1 : p ≤ G.m
  · exact Or.inl ⟨(G.a p, decide (Even (G.m - p))), mem_lam.2 (Or.inl ⟨p, h1, rfl⟩), by simp [mergedDecreasingWordPiZeroDZero, h1]⟩
  by_cases h2 : p ≤ G.m + 2 * (G.k - 1)
  · by_cases h3 : (p - G.m) % 2 = 1
    · refine Or.inr ⟨((G.v ((p - G.m + 3) / 2) : ℚ), true), mem_discrete_parameter_iff.2 (Or.inl ⟨mem_cloud.2 ⟨_, by omega, by omega, rfl⟩, rfl⟩), ?_⟩
      simp [mergedDecreasingWordPiZeroDZero, h1, h2, h3]
    · refine Or.inl ⟨(G.vHalf ((p - G.m + 2) / 2), true), mem_lam.2 (Or.inr ⟨mem_cloudHalf.2 ⟨_, by omega, by omega, rfl⟩, rfl⟩), ?_⟩
      simp [mergedDecreasingWordPiZeroDZero, h1, h2, h3]
  · refine Or.inr ⟨(-(G.b (p - G.m - 2 * (G.k - 1)) : ℚ), decide (Even (p - G.m - 2 * (G.k - 1) - 1))),
      mem_discrete_parameter_iff.2 (Or.inr ⟨_, by omega, by omega, rfl⟩), ?_⟩
    simp [mergedDecreasingWordPiZeroDZero, h1, h2]

theorem interlaced_pi_zero_and_D0 : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool}
    {mu : Fin n → ℝ} {ε' : Fin n → Bool}, 0 < G.ga → 1 ≤ G.v G.k + G.b 1 → IsEnum (G.parPi 0) lam ε →
    IsEnum G.parD0 mu ε' → GlobalTheory.SepReal.Interlaced ε lam ε' mu := by
  intro G n lam ε mu ε' hga hvb ⟨hA, q, hq, hS⟩ ⟨hB, q', hq', hD⟩ x y hlt hbtw
  rw [parPi_zero] at hS
  set N := 2 * G.m + 2 * (G.k - 1) with hN
  have hV : ∀ z : Fin (n + 1) ⊕ Fin n, Sum.elim lam mu z = ((Sum.elim q q' z : ℚ) : ℝ) := by
    rintro (a | b)
    · exact hq a
    · exact hq' b
  have key : ∀ z : Fin (n + 1) ⊕ Fin n, ∃ p ≤ N, Sum.elim q q' z = G.mergedDecreasingWordPiZeroDZero p ∧
      xor (Sum.elim ε ε' z) z.isLeft = G.mergedDecreasingWordParity p := by
    rintro (a | b)
    · have hm : (q a, ε a) ∈ G.lam := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
      obtain ⟨p, hp, h1, h2⟩ := G.exists_pos_of_mem_lam hm
      refine ⟨p, hp, h1, ?_⟩
      simpa using h2
    · have hm : (q' b, ε' b) ∈ G.parD0 := by rw [hD]; exact Finset.mem_image_of_mem _ (Finset.mem_univ b)
      obtain ⟨p, hp, h1, h2⟩ := G.exists_position_of_mem_D0 hm
      refine ⟨p, hp, h1, ?_⟩
      simpa using h2
  have surj : ∀ p ≤ N, ∃ z : Fin (n + 1) ⊕ Fin n, Sum.elim q q' z = G.mergedDecreasingWordPiZeroDZero p := by
    intro p hp
    rcases G.mem_of_pos hp with ⟨x, hx, hx1⟩ | ⟨x, hx, hx1⟩
    · rw [hS] at hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨Sum.inl a, hx1⟩
    · rw [hD] at hx
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨Sum.inr b, hx1⟩
  obtain ⟨px, hpx, hx1, hx2⟩ := key x
  obtain ⟨py, hpy, hy1, hy2⟩ := key y
  rw [hV, hV, hx1, hy1, Rat.cast_lt] at hlt
  have hlt' : px < py := by
    by_contra h
    rcases (not_lt.1 h).eq_or_lt with h | h
    · subst h; exact lt_irrefl _ hlt
    · exact lt_asymm hlt (G.merged_word_strict_anti hga hvb h hpx)
  have hsucc : py = px + 1 := by
    by_contra h
    obtain ⟨z, hz⟩ := surj (px + 1) (by omega)
    refine hbtw z ⟨?_, ?_⟩
    · rw [hV, hV, hy1, hz, Rat.cast_lt]; exact G.merged_word_strict_anti hga hvb (by omega) hpy
    · rw [hV, hV, hx1, hz, Rat.cast_lt]; exact G.merged_word_strict_anti hga hvb (Nat.lt_succ_self px) (by omega)
  have hpar : G.mergedDecreasingWordParity py = !G.mergedDecreasingWordParity px := by
    subst hsucc; simp only [mergedDecreasingWordParity]
    by_cases h : (G.m + px) % 2 = 1
    · simp [h]; omega
    · simp [h]; omega
  rw [← hx2, ← hy2] at hpar
  revert hpar
  cases Sum.elim ε ε' x <;> cases Sum.elim ε ε' y <;> cases x.isLeft <;> cases y.isLeft <;> decide

end GlobalTheory.SignedHC.GridData
end

section

noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.SupportVolume

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem residue_eq_zero_iff_lt (x : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (x : k) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

theorem isUnit_iff_val (x : 𝒪[k]) : IsUnit x ↔ valuation k (x : k) = 1 :=
  (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one

theorem isUnit_red_iff {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n 𝒪[k]) :
    IsUnit (GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.red A) ↔ valuation k ((A.det : 𝒪[k]) : k) = 1 := by
  rw [← isUnit_iff_val, ← Matrix.isUnit_iff_isUnit_det]
  exact ⟨GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.isUnit_of_red A, fun h => h.map (IsLocalRing.residue 𝒪[k]).mapMatrix⟩

theorem det_coe {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n 𝒪[k]) :
    ((A.det : 𝒪[k]) : k) = (A.map (algebraMap 𝒪[k] k)).det :=
  by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl

def suppBar (A D E : Type) [Fintype A] [DecidableEq A] :
    Set (Matrix (A ⊕ E) (A ⊕ D) 𝓀[k]) :=
  {B | IsUnit B.toBlocks₁₁ ∧ B.toBlocks₂₁ = 0}

theorem inSupp_eq_pre {A D E : Type} [Fintype A] [DecidableEq A] :
    {x : Matrix (A ⊕ E) (A ⊕ D) k | InSupp x} = GlobalTheory.IndexVolume.pre (suppBar (k := k) A D E) := by
  ext x
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨Matrix.of fun i j => ⟨x i j, h1 i j⟩, rfl, ?_, ?_⟩
    · change IsUnit (GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.red (Matrix.of fun i j => (⟨x i j, h1 i j⟩ : 𝒪[k])).toBlocks₁₁)
      rw [isUnit_red_iff, det_coe]
      exact h2
    · ext i j
      exact (residue_eq_zero_iff_lt _).2 (h3 i j)
  · rintro ⟨A, rfl, hu, hz⟩
    refine ⟨fun i j => (A i j).2, ?_, fun i j => ?_⟩
    · have := (isUnit_red_iff A.toBlocks₁₁).1 hu
      rw [det_coe] at this
      exact this
    · exact (residue_eq_zero_iff_lt (A (.inr i) (.inl j))).1 (congrFun (congrFun hz i) j)

def unitBar (A : Type) [Fintype A] [DecidableEq A] : Set (Matrix A A 𝓀[k]) := {U | IsUnit U}

theorem KO_eq_pre (A : Type) [Fintype A] [DecidableEq A] :
    Units.val '' (KO k A : Set (GL A k)) = GlobalTheory.IndexVolume.pre (unitBar (k := k) A) := by
  ext x
  constructor
  · rintro ⟨g, ⟨h, rfl⟩, rfl⟩
    exact ⟨h.val, rfl, h.isUnit.map (IsLocalRing.residue 𝒪[k]).mapMatrix⟩
  · rintro ⟨M, rfl, hM⟩
    obtain ⟨u, hu⟩ := GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.isUnit_of_red M hM
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u, ⟨u, rfl⟩, ?_⟩
    rw [← hu]
    rfl

theorem card_matrix (m n : Type) [Fintype m] [Fintype n] :
    Nat.card (Matrix m n 𝓀[k]) = Nat.card 𝓀[k] ^ (Fintype.card m * Fintype.card n) := by
  change Nat.card (m → n → 𝓀[k]) = _
  rw [Nat.card_fun, Nat.card_fun, ← pow_mul, Nat.card_eq_fintype_card (α := m), Nat.card_eq_fintype_card (α := n), mul_comm]

def suppEquiv (A D E : Type) [Fintype A] [DecidableEq A] :
    suppBar (k := k) A D E ≃ unitBar (k := k) A × Matrix A D 𝓀[k] × Matrix E D 𝓀[k] where
  toFun B := (⟨B.1.toBlocks₁₁, B.2.1⟩, B.1.toBlocks₁₂, B.1.toBlocks₂₂)
  invFun U := ⟨fromBlocks U.1.1 U.2.1 0 U.2.2, ⟨by rw [toBlocks_fromBlocks₁₁]; exact U.1.2, toBlocks_fromBlocks₂₁ _ _ _ _⟩⟩
  left_inv B := by
    obtain ⟨B, h1, h2⟩ := B
    apply Subtype.ext
    simp only
    rw [← h2, fromBlocks_toBlocks]
  right_inv U := by
    obtain ⟨⟨U, hU⟩, X, Y⟩ := U
    simp

theorem card_suppBar (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [Fintype E] :
    Nat.card (suppBar (k := k) A D E) = Nat.card (unitBar (k := k) A) *
      (Nat.card 𝓀[k] ^ (Fintype.card A * Fintype.card D) * Nat.card 𝓀[k] ^ (Fintype.card E * Fintype.card D)) := by
  rw [Nat.card_congr (suppEquiv A D E), Nat.card_prod, Nat.card_prod, card_matrix, card_matrix]

theorem measure_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ (r : ℕ) (D E : Type) [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E],
    MeasurableSet {x : Matrix (Fin r ⊕ E) (Fin r ⊕ D) k | InSupp x} ∧
    (volM ν (Fin r ⊕ E) (Fin r ⊕ D)).real {x | InSupp x} = volAdd ν r * ((resCard k : ℝ) ^ (r * Fintype.card E))⁻¹ := by
  intro k _ _ _ _ _ _ ν hν r D E _ _ _ _
  haveI := hν.1
  rw [inSupp_eq_pre]
  refine ⟨GlobalTheory.IndexVolume.measurableSet_pre _, ?_⟩
  have h1 : (volM ν (Fin r ⊕ E) (Fin r ⊕ D)).real (GlobalTheory.IndexVolume.pre (suppBar (k := k) (Fin r) D E)) =
      _ := GlobalTheory.IndexVolume.measureReal_pre ν hν.2 _
  have h2 : (volM ν (Fin r) (Fin r)).real (GlobalTheory.IndexVolume.pre (unitBar (k := k) (Fin r))) =
      _ := GlobalTheory.IndexVolume.measureReal_pre ν hν.2 _
  unfold volAdd
  rw [KO_eq_pre, h1, h2, card_suppBar]
  have hq : (0 : ℝ) < Nat.card 𝓀[k] := by exact_mod_cast Nat.card_pos
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.resCard, resCard, Fintype.card_sum, Fintype.card_fin]
  push_cast
  set q : ℝ := (Nat.card 𝓀[k] : ℝ)
  set d := Fintype.card D
  set e := Fintype.card E
  have hexp : q ^ ((r + e) * (r + d)) = q ^ (r * r) * q ^ (r * e) * (q ^ (r * d) * q ^ (e * d)) := by
    rw [← pow_add, ← pow_add, ← pow_add]; ring_nf
  rw [hexp]
  have : q ≠ 0 := hq.ne'
  field_simp

end GlobalTheory.SupportVolume
end
end

section

open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.JetScale

section General

variable {σ : Type} [Fintype σ]

def scaleVar (w : σ → ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun v => C (w v) * X v

lemma monomial_eq_prod (s : σ →₀ ℕ) (r : ℂ) :
    (monomial s r : MvPolynomial σ ℂ) = C r * ∏ v, X v ^ s v := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

lemma scaleVar_monomial (w : σ → ℂ) (s : σ →₀ ℕ) (r : ℂ) :
    scaleVar w (monomial s r) = monomial s (r * ∏ v, w v ^ s v) := by
  rw [monomial_eq_prod, monomial_eq_prod, scaleVar, map_mul, aeval_C, map_prod, map_mul C, map_prod C]
  simp only [map_pow, aeval_X, mul_pow, Finset.prod_mul_distrib, algebraMap_eq]
  ring

end General

section Jet

variable {ι : Type} [Fintype ι] {a b : ℕ}

lemma jetLin_monomial (J : (DVar ι a b →₀ ℕ) → ℂ) (m : ((ι × Fin b × Fin b) ⊕ DVar ι a b) →₀ ℕ) (r : ℂ) :
    jetLin J (monomial m r) =
      monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (r * J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have h : (monomial m r : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) =
      r • basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, jetLin, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

def wDer (c : ι → ℂ) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℂ := Sum.elim (fun _ => 1) (fun k => c k.1)

def wCoord (c : ι → ℂ) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℂ := Sum.elim (fun k => c k.1) (fun _ => 1)

lemma jetLin_scaleDer (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    jetLin J (scaleVar (wDer c) Q) = jetLin (fun m => (∏ k, c k.1 ^ m k) * J m) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [scaleVar_monomial, jetLin_monomial, jetLin_monomial, Fintype.prod_sum_type]
    simp [wDer, Finsupp.comapDomain_apply]
    congr 1
    ring
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]

lemma blockAct_diag (c : ι → ℂ) :
    Formalism.GradedWeylDivisibility.blockAct ℂ (n := b) (fun τ => Matrix.diagonal fun _ : Fin b => c τ) = scaleVar (fun v : ι × Fin b × Fin b => c v.1) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [Formalism.GradedWeylDivisibility.blockAct, scaleVar, Matrix.diagonal_apply, apply_ite C, ite_mul, Finset.sum_ite_eq]

lemma jetLin_scaleCoord (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    jetLin J (scaleVar (wCoord c) Q) = scaleVar (fun v : ι × Fin b × Fin b => c v.1) (jetLin J Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [scaleVar_monomial, jetLin_monomial, jetLin_monomial, scaleVar_monomial, Fintype.prod_sum_type]
    simp [wCoord, Finsupp.comapDomain_apply]
    congr 1
    ring
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

lemma scale_subD (c : ι → ℂ) :
    (scaleVar (wDer (a := a) (b := b) c)).comp (subD ℂ ι a b) = (scaleVar (wCoord c)).comp (subD ℂ ι a b) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, subD, aeval_X]
  split_ifs

  · simp only [map_sum, map_mul, scaleVar, aeval_X, wDer, wCoord, Sum.elim_inl, Sum.elim_inr, map_one, one_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  · simp

lemma jetLin_smul_table (u : ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    jetLin (fun m => u * J m) Q = u • jetLin J Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [jetLin_monomial, jetLin_monomial, smul_monomial, smul_eq_mul]
    congr 1
    ring
  | add p q hp hq => simp only [map_add (f := _), hp, hq, smul_add]

end Jet

theorem jetMap_weight_scale {ι : Type} [Fintype ι] {a b : ℕ} (u : ℂ) (c : ι → ℂ) (J : (DVar ι a b →₀ ℕ) → ℂ) (nn : ι → ℕ)
    (P : Formalism.L2.DIV.Pol ℂ ι a) :
    jetMap (fun m => u * ((m.prod fun k e => c k.1 ^ e) * J m)) nn P =
      u • Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => Matrix.diagonal fun _ : Fin b => c τ) (jetMap J nn P) := by
  have hJ : (fun m : DVar ι a b →₀ ℕ => u * ((m.prod fun k e => c k.1 ^ e) * J m)) =
      fun m => u * ((∏ k, c k.1 ^ m k) * J m) := by
    funext m
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [hJ, blockAct_diag]
  rw [jetMap, jetMap, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply]
  have key := DFunLike.congr_fun (scale_subD (a := a) (b := b) c) (LinearMap.mulRight ℂ (∏ τ, frDet ℂ a τ ^ nn τ) P)
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at key
  rw [jetLin_smul_table, ← jetLin_scaleDer, key, jetLin_scaleCoord]

end GlobalTheory.JetScale
end
end
