module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle167
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle208
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle270
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle232
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle170
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFieldCmCurvesUnitDiscriminant
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle227
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNumeratorOfInvolution
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle234
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
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
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open GlobalTheory.NeedB Polynomial

theorem _root_.GlobalTheory.T.kummer_divisor_descends_functionField : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ : Ω, θ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} →
      (∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N) →
      ∃ f : K, f ≠ 0 ∧ ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
        ∃ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 ∧ B.valuation (θ ^ N / (algebraMap K Ω f * c ^ N)) = 1 := by
  first | exact @GlobalTheory.KummerCob.divisor_descends | exact GlobalTheory.KummerCob.divisor_descends | (intros; apply GlobalTheory.KummerCob.divisor_descends <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

theorem _root_.GlobalTheory.T.galois_action_siegelUnitInTower : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b d : ℕ) (s : Ω ≃ₐ[ℚ] Ω), 0 < M → a < M → s (eOm ε (1 / M)) = eOm ε (d / M) → admitted c ![(a : ℚ) / M, (b : ℚ) / M] → admitted c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] → T.gal s (siegel T c ![(a : ℚ) / M, (b : ℚ) / M]) = siegel T c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] := by
  first | exact @GlobalTheory.KZ.gal_siegel | exact GlobalTheory.KZ.gal_siegel | (intros; apply GlobalTheory.KZ.gal_siegel <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.galois_slTwo_action_modularFunctionRing_of_congr : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : GlobalTheory.FN.ring ε.range) (N w : ℕ), 0 < N → Lv ε.range N w a → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.gal s (T.io a)) := by
  first | exact @GlobalTheory.FN.gal_sl_io_of_cong | exact GlobalTheory.FN.gal_sl_io_of_cong | (intros; apply GlobalTheory.FN.gal_sl_io_of_cong <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem eigF_of_prim : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (ρ : ℍ → ℝ) (α β : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → Prim k N χ g → Wt (N * l) ρ → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (k - 1) → ∃ (B : ℕ) (c : ℕ → ℂ), EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧ ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = pet k ρ (qs (Vo l fun n => conj (g n))) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs fun n => conj (g n)) (qs a) := by
  intro k N l χ g ρ α β hk hN hl hlN hg hρ hab hαβ
  haveI : NeZero N := ⟨by omega⟩
  set h : ℕ → ℂ := fun n => conj (g n) with hh_def
  have hNl : 0 < N * l := Nat.mul_pos hN hl.pos
  have hdvd : N ∣ N * l := dvd_mul_right N l
  have hP : Prim k N χ⁻¹ h := (GlobalTheory.T.cuspForm_conjugate_coefficients_inv_char k N χ g).2 hg
  have hMFh : MF k N (ch χ⁻¹) h := hP.cf.1
  have lin := GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) (ch χ⁻¹)
  have hCFh : CF k (N * l) (ch χ⁻¹) h := (GlobalTheory.T.modularFormCoeffSeq_linear_structure k N (ch χ⁻¹)).2.2.2.2.2 (N * l) h hdvd hP.cf
  have hCFV : CF k (N * l) (ch χ⁻¹) (Vo l h) := (GlobalTheory.T.coeffHeckeVOperator_raises_level k N l (ch χ⁻¹) h hl.pos).2 hP.cf
  have petlin := GlobalTheory.T.halfPeterssonIntegralWeighted_linear_forms k (N * l) (N * l) N χ⁻¹ ρ hk hNl hdvd hρ

  have hsc : ∀ (h' a : ℕ → ℂ) (x : ℂ), CF k (N * l) (ch χ⁻¹) h' → MF k (N * l) (ch χ⁻¹) a →
      pet k ρ (qs (x • h')) (qs a) = conj x * pet k ρ (qs h') (qs a) := by
    intro h' a x hh' ha
    have e : qs (x • h') = fun τ => x * qs h' τ + 0 * qs h' τ := by
      rw [(lin.2.2.1 x h' hh'.1).2]; funext τ; simp
    rw [e, petlin.2 h' h' a x 0 hh' hh' ha.1]; simp
  have hconj : ∀ x : ZMod N, conj (χ x) = χ⁻¹ x := fun x => MulChar.star_apply' χ x
  have hch : ∀ n : ℕ, ch χ⁻¹ (n : ℤ) = χ⁻¹ (n : ZMod N) := by intro n; simp [ch]
  set φ : (ℕ → ℂ) → ℂ := fun a => pet k ρ (qs (Vo l h)) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs h) (qs a) with hφ_def
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_sturmBound_isModularFormCoeffSeq k (N * l) N χ⁻¹ hNl hdvd
  obtain ⟨c, hc⟩ := GlobalTheory.T.linearFunctional_eq_coeffLinearCombinationFinite {a | MF k (N * l) (ch χ⁻¹) a} B φ lin.1
    (by
      intro a ha b hb
      refine ⟨(lin.2.1 a b ha hb).1, ?_⟩
      have e1 := petlin.1 (Vo l h) a b 1 1 hCFV ha.1 hb.1
      have e2 := petlin.1 h a b 1 1 hCFh ha.1 hb.1
      simp only [one_smul, one_mul] at e1 e2
      simp only [hφ_def, e1, e2]; ring)
    (by
      intro x a ha
      refine ⟨(lin.2.2.1 x a ha).1, ?_⟩
      have e1 := petlin.1 (Vo l h) a a x 0 hCFV ha.1 ha.1
      have e2 := petlin.1 h a a x 0 hCFh ha.1 ha.1
      simp only [zero_smul, add_zero, zero_mul] at e1 e2
      simp only [hφ_def, e1, e2]; ring)
    hB
  have hφ : ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = φ a := fun a ha => (hc a ha).symm
  refine ⟨B, c, ⟨?_, ?_⟩, hφ⟩
  ·
    intro a ha q hq hqNl
    have hqN : ¬ q ∣ N := fun d => hqNl (dvd_mul_of_dvd_left d l)
    have hql : q ≠ l := fun e => hqNl (e ▸ dvd_mul_left q N)
    have hcop : q.Coprime l := (Nat.coprime_primes hq hl).2 hql
    have hTa := GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ⁻¹ a hk hdvd hq hqNl ha
    rw [hφ _ hTa, hφ _ ha]
    have eigh : To k (ch χ⁻¹ q) q h = h q • h := by
      rw [hP.eig q hq hqN]; funext n; simp
    have eigV : To k (ch χ⁻¹ q) q (Vo l h) = h q • Vo l h := by
      rw [(GlobalTheory.T.coeffHecke_UV_cauchyProduct_identities ℂ l hl.pos).2.2.2.2.1 k q _ h hcop hq.pos, eigh]
      funext n; simp only [Vo, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp
    have adj0 := GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k (N * l) N q χ⁻¹ ρ h a hk hNl hdvd hq hqNl hρ hCFh ha
    have adj1 := GlobalTheory.T.halfPeterssonIntegral_heckeT_adjoint k (N * l) N q χ⁻¹ ρ (Vo l h) a hk hNl hdvd hq hqNl hρ hCFV ha
    rw [eigh, hsc h a _ hCFh ha] at adj0
    rw [eigV, hsc (Vo l h) a _ hCFV ha] at adj1
    have hgq : conj (h q) = g q := by simp [hh_def]
    simp only [hφ_def]
    rw [adj0, adj1]
    simp only [hgq, hch]
    ring
  ·
    intro a ha
    have hper : ∀ d : ℤ, ch χ⁻¹ (d + ((N * l : ℕ) : ℤ)) = ch χ⁻¹ d := by
      intro d; simp only [ch]; congr 1; push_cast; simp
    have hUa := (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch χ⁻¹) a hk hl (dvd_mul_left l N) hper ha).1
    rw [hφ _ hUa, hφ _ ha]
    have adjU0 := GlobalTheory.T.halfPeterssonIntegral_heckeU_adjoint k (N * l) N l χ⁻¹ ρ h a hk hNl hdvd hl (dvd_mul_left l N) hlN hρ hCFh ha
    have adjU1 := GlobalTheory.T.halfPeterssonIntegral_heckeU_adjoint k (N * l) N l χ⁻¹ ρ (Vo l h) a hk hNl hdvd hl (dvd_mul_left l N) hlN hρ hCFV ha
    have tr0 := GlobalTheory.T.sum_slash_heckeRepLowerLevel_eq_pow_mul_heckeV k N l χ⁻¹ h hk hl.pos hMFh
    have eigl : To k (ch χ⁻¹ l) l h = h l • h := by
      rw [hP.eig l hl hlN]; funext n; simp
    have tr1 := GlobalTheory.T.sum_slash_heckeRepLower_heckeV_eigenform k N l χ⁻¹ h (h l) hk hN hl hlN hMFh eigl
    have f0 : (fun τ => ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ)
        = fun τ => ((l : ℂ) ^ k) * qs (Vo l h) τ + 0 * qs (Vo l h) τ := by
      funext τ; rw [tr0]; ring
    have f1 : (fun τ => ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ)
        = fun τ => (ch χ⁻¹⁻¹ l * h l) * qs (Vo l h) τ + (-(ch χ⁻¹⁻¹ l * (l : ℂ)⁻¹)) * qs h τ := by
      funext τ; rw [tr1]; ring
    rw [f0, petlin.2 (Vo l h) (Vo l h) a _ 0 hCFV hCFV ha.1] at adjU0
    rw [f1, petlin.2 (Vo l h) h a _ _ hCFV hCFh ha.1] at adjU1
    have e1 : conj (ch χ⁻¹⁻¹ (l : ℤ)) = χ⁻¹ (l : ZMod N) := by
      rw [inv_inv]; simp only [ch, Int.cast_natCast]; exact hconj _
    have hgl : conj (h l) = g l := by simp [hh_def]
    have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
    have key : (l : ℂ) ^ (k - 1) / (l : ℂ) ^ k = (l : ℂ)⁻¹ := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]; field_simp
    simp only [map_mul, map_neg, map_inv₀, map_pow, Complex.conj_natCast, map_zero, e1, hgl, zero_mul, add_zero] at adjU0 adjU1
    simp only [hφ_def, adjU0, adjU1]
    set P0 := pet k ρ (qs h) (qs a)
    set P1 := pet k ρ (qs (Vo l h)) (qs a)
    have hcan : (l : ℂ) ^ k / (l : ℂ) ^ k = 1 := div_self (pow_ne_zero _ hl0)
    linear_combination (-P1) * hab + (P0 / (l : ℂ) ^ k) * hαβ + (χ⁻¹ (l : ZMod N) * P0) * key + (-β * P1) * hcan

end GlobalTheory.EisM
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators IntermediateField

noncomputable section

namespace GlobalTheory.CurveAlgebraic

theorem exists_algHom_apply_eq {k : Type} [Field k] [Algebra k ℂ] {x x' : ℂ}
    (hx : Transcendental k x) (hx' : Transcendental k x')
    (hm : x ∈ (algebraicClosure k⟮x⟯ ℂ)) :
    ∃ σ : (algebraicClosure k⟮x⟯ ℂ) →ₐ[k] ℂ, σ ⟨x, hm⟩ = x' := by
  let τ : k⟮x⟯ →ₐ[k] ℂ := (k⟮x'⟯.val).comp
    ((RatFunc.algEquivOfTranscendental x' hx').toAlgHom.comp
      (RatFunc.algEquivOfTranscendental x hx).symm.toAlgHom)
  have hτ : τ (IntermediateField.AdjoinSimple.gen k x) = x' := by
    change ((RatFunc.algEquivOfTranscendental x' hx')
      ((RatFunc.algEquivOfTranscendental x hx).symm
        (IntermediateField.AdjoinSimple.gen k x)) : ℂ) = x'
    rw [RatFunc.algEquivOfTranscendental_symm_gen, RatFunc.algEquivOfTranscendental_X]
  obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := k) (L := k⟮x⟯)
    (M := ℂ) (E := algebraicClosure k⟮x⟯ ℂ) τ
  refine ⟨σ, ?_⟩
  rw [← hτ, ← hσ]
  rfl

theorem isAlgebraic_of_torsion {k : Type} [Field k] [CharZero k] [Algebra k ℂ]
    (W : WeierstrassCurve.Affine k) (V : WeierstrassCurve.Affine ℂ) (hV : W.baseChange ℂ = V)
    (m : ℕ) (S : Set ℂ) (hS : S.Finite)
    (hmem : ∀ x y (h : V.Nonsingular x y),
      m • (WeierstrassCurve.Affine.Point.some x y h) = 0 → x ∈ S)
    {x y : ℂ} (h : V.Nonsingular x y) (h0 : m • (WeierstrassCurve.Affine.Point.some x y h) = 0)
    (hy : IsAlgebraic k⟮x⟯ y) : IsAlgebraic k x := by
  subst hV
  by_contra hx
  let F := algebraicClosure k⟮x⟯ ℂ
  have hxF : x ∈ F := F.algebraMap_mem (IntermediateField.AdjoinSimple.gen k x)
  have hyF : y ∈ F := mem_algebraicClosure_iff.mpr hy
  let ι : F →ₐ[k] ℂ := F.val.restrictScalars k
  have hι : Function.Injective ι := ι.toRingHom.injective
  have hF : (W.baseChange F).Nonsingular ⟨x, hxF⟩ ⟨y, hyF⟩ :=
    (W.baseChange_nonsingular hι _ _).mp h
  have h1 : m • (WeierstrassCurve.Affine.Point.some _ _ hF) = 0 := by
    apply WeierstrassCurve.Affine.Point.map_injective (W' := W) ι
    rw [map_nsmul, map_zero, WeierstrassCurve.Affine.Point.map_some]
    exact h0
  have h2 : ∀ n : ℕ, x + n ∈ S := fun n => by
    have hn : Transcendental k (x + n) := fun ha => hx (by
      have := ha.sub (isAlgebraic_natCast (R := k) (A := ℂ) n)
      simpa using this)
    obtain ⟨σ, hσ⟩ := exists_algHom_apply_eq hx hn hxF
    have h3 := congrArg (WeierstrassCurve.Affine.Point.map (W' := W) σ) h1
    rw [map_nsmul, map_zero, WeierstrassCurve.Affine.Point.map_some] at h3
    exact hσ ▸ hmem _ _ _ h3
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => x + n) ?_ h2 hS
  intro a b hab
  simpa using hab

theorem weierstrassP_mem (L : PeriodPair) (h2 : L.g₂ ∈ Qbar) (h3 : L.g₃ ∈ Qbar) {m : ℕ}
    (hm : 0 < m) {t : ℂ} (ht : t ∉ L.lattice) (hmt : (m : ℂ) * t ∈ L.lattice) :
    L.weierstrassP t ∈ Qbar ∧ L.derivWeierstrassP t ∈ Qbar := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmul : ∀ z : ℂ, m • latticePoint L z = latticePoint L ((m : ℂ) * z) := fun z => by
    rw [← latticePointHom_apply, ← latticePointHom_apply, ← map_nsmul, nsmul_eq_mul]
  obtain ⟨A, D, -, -, hD, -, -, -, -, hroot, -⟩ := exists_weierstrassP_mul_eq_div (L := L) (L' := L)
    hm0 (fun l hl => by rw [← nsmul_eq_mul]; exact nsmul_mem hl m) ⊤ trivial trivial trivial
    (fun _ _ _ => trivial)
  have hsq := L.derivWeierstrassP_sq t ht
  have hx : IsAlgebraic Qbar (L.weierstrassP t) := by
    refine isAlgebraic_of_torsion
      (⟨0, 0, 0, -⟨L.g₂, h2⟩ / 4, -⟨L.g₃, h3⟩ / 4⟩ : WeierstrassCurve Qbar) (latticeCurve L).toAffine ?_ m
      (D.rootSet ℂ) (D.rootSet_finite ℂ) ?_ (latticeCurve_nonsingular L ht) ?_ ?_
    · ext <;> simp [latticeCurve, WeierstrassCurve.Affine.baseChange, WeierstrassCurve.baseChange] <;> rfl
    · intro x y h h0
      obtain ⟨z, hz⟩ := latticePoint_surjective L (.some x y h)
      have hz' : z ∉ L.lattice := fun hc => by
        rw [latticePoint_of_mem L hc] at hz
        exact WeierstrassCurve.Affine.Point.some_ne_zero _ hz.symm
      rw [← hz, hmul, latticePoint_eq_zero_iff] at h0
      rw [latticePoint_of_notMem L hz'] at hz
      obtain ⟨rfl, -⟩ := WeierstrassCurve.Affine.Point.some.inj hz
      rw [Polynomial.mem_rootSet]
      exact ⟨hD.ne_zero, (hroot z hz').mpr h0⟩
    · rw [← latticePoint_of_notMem L ht, hmul, latticePoint_eq_zero_iff]
      exact hmt
    · set F := (↥Qbar)⟮L.weierstrassP t⟯
      have e1 : L.weierstrassP t ∈ F := IntermediateField.mem_adjoin_simple_self _ _
      have e2 : L.g₂ ∈ F := F.algebraMap_mem ⟨L.g₂, h2⟩
      have e3 : L.g₃ ∈ F := F.algebraMap_mem ⟨L.g₃, h3⟩
      have e4 : (L.derivWeierstrassP t / 2) ^ 2 ∈ F := by
        rw [div_pow, hsq]
        refine div_mem (sub_mem (sub_mem (mul_mem (ofNat_mem F 4) (pow_mem e1 3)) (mul_mem e2 e1)) e3)
          (pow_mem (ofNat_mem F 2) 2)
      exact IsAlgebraic.of_pow two_pos (isAlgebraic_algebraMap (⟨_, e4⟩ : F))
  have hx' : L.weierstrassP t ∈ Qbar :=
    haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
    mem_algebraicClosure_iff.mpr (hx.restrictScalars ℚ)
  refine ⟨hx', mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow two_pos ?_)⟩
  rw [hsq, ← mem_algebraicClosure_iff]
  exact sub_mem (sub_mem (mul_mem (ofNat_mem _ 4) (pow_mem hx' 3)) (mul_mem h2 hx')) h3

theorem exists_periodPair (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (h : Crv D cc δ) : ∃ L : PeriodPair, (∀ z, z ∈ lamOf D cc δ ↔ z ∈ L.lattice) ∧
      L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 ∧ IsIntegral ℤ (1728 * L.g₂ ^ 3) := by
  obtain ⟨⟨w₁, w₂, hw, he⟩, -, hΔ, -, hcm⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hD cc δ h
  let L : PeriodPair := ⟨w₁, w₂, hw⟩
  have hL : ∀ z, z ∈ lamOf D cc δ ↔ z ∈ L.lattice := fun z => by
    rw [he, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
    simp [L]
  obtain ⟨e2, e3, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL
  have hΔ' : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by rw [← e2, ← e3]; exact hΔ
  refine ⟨L, hL, hΔ', ?_⟩
  have := CMCurves.isIntegral_latticeJ (Formalism.L2.Pj.LPb.finrank_K D)
    (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) L
    (fun a z hz => (hL _).mp (hcm a z ((hL _).mpr hz)))
  rwa [CMCurves.latticeJ, hΔ', div_one] at this

theorem integral_j_and_algebraic_data : ∀ (D : D7), admG1 D → GL3Theta.admJ D ∧ ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → DataIn D (tor0 D cc δ) Qbar ∧ ∀ t, InRationalLattice (lamOf D cc δ) t → t ∉ (lamOf D cc δ) → wpF (lamOf D cc δ) t ∈ Qbar ∧ wpD (lamOf D cc δ) t ∈ Qbar := by
  intro D hD
  refine ⟨fun cc δ h1 h2 => ?_, fun cc δ h => ?_⟩
  · obtain ⟨L, hL, -, hj⟩ := exists_periodPair D hD cc δ ⟨h1, h2⟩
    rwa [(GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL).1]
  obtain ⟨L, hL, hΔ, hj⟩ := exists_periodPair D hD cc δ h
  obtain ⟨e2, e3, -, -, hp, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL
  have hj' : 1728 * L.g₂ ^ 3 ∈ Qbar :=
    mem_algebraicClosure_iff.mpr (hj.tower_top (A := ℚ)).isAlgebraic
  have hc : L.g₂ ^ 3 ∈ Qbar := by
    have := div_mem hj' (ofNat_mem Qbar 1728)
    rwa [mul_div_cancel_left₀ _ (by norm_num)] at this
  have h2 : L.g₂ ∈ Qbar :=
    mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow three_pos (mem_algebraicClosure_iff.mp hc))
  have h3 : L.g₃ ∈ Qbar := by
    refine mem_algebraicClosure_iff.mpr (IsAlgebraic.of_pow two_pos ?_)
    rw [← mem_algebraicClosure_iff,
      show L.g₃ ^ 2 = (L.g₂ ^ 3 - 1) / 27 by linear_combination (-1 / 27 : ℂ) * hΔ]
    exact div_mem (sub_mem hc (one_mem _)) (ofNat_mem _ 27)
  refine ⟨⟨fun τ x => ?_, e2 ▸ h2, e3 ▸ h3⟩, ?_⟩
  · exact mem_algebraicClosure_iff.mpr
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom)
  · rintro t ⟨m, hm, hmt⟩ ht
    rw [(hp t ht).1, (hp t ht).2]
    exact weierstrassP_mem L h2 h3 hm (fun hc => ht ((hL _).mpr hc)) ((hL _).mp hmt)

end GlobalTheory.CurveAlgebraic
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.MovedIdx

theorem common_denom {A ι : Type} [CommRing A] [Fintype ι] (S : Subring A) (f : ι → A) (P : ℕ → Prop) (h1 : P 1)
    (hm : ∀ a b, P a → P b → P (a * b)) (h : ∀ i, ∃ n : ℕ, P n ∧ (n : A) * f i ∈ S) :
    ∃ n : ℕ, P n ∧ ∀ i, (n : A) * f i ∈ S := by
  choose n hn hf using h
  refine ⟨∏ i, n i, Finset.prod_induction _ P hm h1 fun i _ => hn i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  rw [hc, mul_comm (n i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem S c) (hf i)

theorem dvd_of_dvd_idx {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (A B : Submodule R X) (n q : ℕ)
    (hq : q.Prime) (h0 : idx A B ≠ 0) (hn : ∀ x ∈ B, n • x ∈ A) (hd : q ∣ idx A B) : q ∣ n := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) := Nat.finite_of_card_ne_zero h0
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) q hd
  rw [← hx, addOrderOf_dvd_iff_nsmul_eq_zero]
  induction x using QuotientAddGroup.induction_on with
  | H y =>
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact hn y.1 y.2

theorem denom_mul (D : D7) {q : ℕ} (hq : q.Prime) {x : AE D} (hx : ZeroAt D q x) (y : AE D) :
    ∃ n : ℕ, n.Coprime q ∧ (n : AE D) * (y * x) ∈ OhE D := by
  obtain ⟨n, hn, hy⟩ := GlobalTheory.HeckeVal.exists_denom D y
  obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
  obtain ⟨m, -, hmq, s, hs, h⟩ := hx a
  refine ⟨m * n', Nat.Coprime.mul_left hmq ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, ?_⟩
  convert mul_mem hs hy using 1
  push_cast
  linear_combination (n' : AE D) * y * h

theorem one_entry_mem (D : D7) {N : ℕ} (i j : Fin N) : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem denom_triv (D : D7) {q N : ℕ} {g : GL (Fin N) (AE D)} (hg : TrivAt D q g) :
    ∃ n : ℕ, n.Coprime q ∧ ∀ i j, (n : AE D) * (g : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  obtain ⟨n, hn, h⟩ := common_denom (OhE D) (fun p : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) (AE D)) p.1 p.2)
    (fun n => n.Coprime q) (by simp) (fun a b => Nat.Coprime.mul_left) (by
      rintro ⟨i, j⟩
      obtain ⟨m, -, hm, s, hs, e⟩ := hg i j 0
      refine ⟨m, hm, ?_⟩
      convert add_mem hs (mul_mem (natCast_mem _ m) (one_entry_mem D i j)) using 1
      linear_combination e)
  exact ⟨n, hn, fun i j => h (i, j)⟩

theorem denom_triv_inv (D : D7) {q N : ℕ} (hq : q.Prime) {g : GL (Fin N) (AE D)} (hg : TrivAt D q g) :
    ∃ n : ℕ, n.Coprime q ∧ ∀ i j, (n : AE D) * ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  obtain ⟨n, hn, h⟩ := common_denom (OhE D) (fun p : Fin N × Fin N × Fin N =>
      ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) p.1 p.2.1 *
      ((g : Matrix (Fin N) (Fin N) (AE D)) p.2.1 p.2.2 - (1 : Matrix (Fin N) (Fin N) (AE D)) p.2.1 p.2.2))
    (fun n => n.Coprime q) (by simp) (fun a b => Nat.Coprime.mul_left) (fun p => denom_mul D hq (hg _ _) _)
  refine ⟨n, hn, fun i j => ?_⟩
  have e : ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      1 - ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) * ((g : Matrix (Fin N) (Fin N) (AE D)) - 1) := by
    rw [Matrix.mul_sub, Units.inv_mul, Matrix.mul_one, sub_sub_cancel]
  rw [e, Matrix.sub_apply, Matrix.mul_apply, mul_sub, Finset.mul_sum]
  exact sub_mem (mul_mem (natCast_mem _ n) (one_entry_mem D i j)) (sum_mem fun l _ => h (i, l, j))

theorem denom_mat (D : D7) {N : ℕ} (M : Matrix (Fin N) (Fin N) (AE D)) :
    ∃ n : ℕ, 0 < n ∧ ∀ i j, (n : AE D) * M i j ∈ OhE D := by
  obtain ⟨n, hn, h⟩ := common_denom (OhE D) (fun p : Fin N × Fin N => M p.1 p.2)
    (fun n => 0 < n) one_pos (fun a b => Nat.mul_pos) (fun p => GlobalTheory.HeckeVal.exists_denom D _)
  exact ⟨n, hn, fun i j => h (i, j)⟩

theorem nsmul_mem_latA (D : D7) (cc : Ideal (𝓞 D.host.K)) {N N' : ℕ} (g : GA D N) (g' : GA D N') {n n' : ℕ}
    (h : ∀ i j, (n : AE D) * (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D)
    (h' : ∀ i j, (n' : AE D) * ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) i j ∈ OhE D) :
    ∀ ζ ∈ (latA D cc N N').map (actA D N N' (g, g')), (n * n') • ζ ∈ latA D cc N N' := by
  rintro _ ⟨ζ, hζ, rfl⟩ i j
  rw [actA_apply, Matrix.smul_apply, Matrix.mul_apply, Finset.smul_sum]
  refine sum_mem fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  convert ihE_mul D cc (mul_mem (h l j) (h' i k)) (hζ k l) using 1
  rw [nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.FinWeil.MovedIdx


open GlobalTheory.FinWeil.MovedIdx in
theorem GlobalTheory.FinWeil.idx_map_actA : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N'), idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) ≠ 0 ∧ (∀ q : ℕ, q.Prime → TrivAt D q (g : GL (Fin N) (AE D)) → TrivAt D q (g' : GL (Fin N') (AE D)) → ¬ q ∣ idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g')))) ∧ (IntG D (g : GL (Fin N) (AE D)) → IntG D (g' : GL (Fin N') (AE D)) → (latA D cc N N').map (actA D N N' (g, g')) ≤ latA D cc N N') := by
  intro D hD cc δ hC N N' g g'
  have h0 : idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) ≠ 0 := by
    obtain ⟨n, hn, h⟩ := denom_mat D (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
    obtain ⟨n', hn', h'⟩ := denom_mat D ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D))
    exact GlobalTheory.T.heisenbergRelativeIndex_completedStandard_ne_zero D hD cc δ hC N N' _ (Nat.mul_pos hn hn') _ (nsmul_mem_latA D cc g g' h h')
  refine ⟨h0, fun q hq hg hg' hd => ?_, fun hg hg' ζ hζ => ?_⟩
  · obtain ⟨n, hn, h⟩ := denom_triv_inv D hq hg
    obtain ⟨n', hn', h'⟩ := denom_triv D hg'
    exact (Nat.Prime.coprime_iff_not_dvd hq).1 (Nat.Coprime.mul_left hn hn').symm
      (dvd_of_dvd_idx _ _ _ q hq h0 (nsmul_mem_latA D cc g g' h h') hd)
  · have := nsmul_mem_latA D cc g g' (n := 1) (n' := 1) (fun i j => by simpa using (hg i j).2)
      (fun i j => by simpa using (hg' i j).1) ζ hζ
    simpa using this
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

theorem _root_.GlobalTheory.T.model_parameter_series_deriv_transport : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative (R := ℂ_[p]) (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F) := by
  first | exact @GlobalTheory.DerivTransport.atU_deriv | exact GlobalTheory.DerivTransport.atU_deriv | (intros; apply GlobalTheory.DerivTransport.atU_deriv <;> assumption)
end
