module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle077
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle018
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.BalancedPairs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.WeightAlgebra

@[expose] public section

section

noncomputable section
open NumberField Formalism.MainNotions.ModuliIntegralCharts
open GlobalTheory.LeastExponentCompare
open scoped Pointwise

namespace GlobalTheory.LeastExponentProbe

variable {E : Type} [Field E] [NumberField E] {cj : E → E}
variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

def vals (b : SymB cj Y) : Set ℝ := {x | ∃ l : SymB cj Y →ₗ[ℝ] ℝ,
    (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) ∧
    (∀ β : SymB cj Y, (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → β ≠ 0 → 0 < l β) ∧ x = l b}

theorem phiC_def (b : SymB cj Y) : phiC cj b = sInf (vals b) := rfl

private lemma vals_eq_functionalValues [IsCMField E] (b : SymB cj Y) : vals b = functionalValues b := by
  ext x
  constructor
  · rintro ⟨l, h1, h2, hx⟩
    exact ⟨l, ⟨h1, h2⟩, hx⟩
  · rintro ⟨l, ⟨h1, h2⟩, hx⟩
    exact ⟨l, h1, h2, hx⟩

section CM

variable [IsCMField E] [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y]

theorem one_le_phiC (h : IsConj cj) (b : SymB cj Y)
    (hint : ∀ a c, ∃ z : ℤ, (b : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z)
    (hpos : ∀ a, 0 ≤ (b : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) (h0 : b ≠ 0) : 1 ≤ phiC cj b := by
  rw [phiC_def]
  refine le_csInf (by rw [vals_eq_functionalValues]; exact functionalValues_nonempty h b) ?_
  rintro x ⟨l, h1, h2, rfl⟩
  obtain ⟨z, hz⟩ := h1 b hint
  have hp := h2 b hpos h0
  rw [hz] at hp ⊢
  have hz0 : (0 : ℤ) < z := by exact_mod_cast hp
  exact_mod_cast (show (1 : ℤ) ≤ z by omega)

end CM

end GlobalTheory.LeastExponentProbe

end
end

section

noncomputable section

namespace GlobalTheory.RamValCheck

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

theorem g_coprime (D : Formalism.BasicNotions.D7) (k : Fin 2) (p : ℕ)
    (hp : p ∈ D.host.condN.primeFactors) :
    Nat.Coprime (D.host.g k) p := by
  have hc := D.ntypes.g_cond k
  have hdvd : p ∣ D.host.QS * D.host.q * D.host.d := Nat.dvd_of_mem_primeFactors hp
  refine Nat.Coprime.coprime_dvd_right hdvd ?_
  rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc]
  simp

end GlobalTheory.RamValCheck
end
end

section

set_option autoImplicit false

namespace GlobalTheory.BalancedTwist

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem pairing_eq {S : Type} [CommRing S] {d : ℕ} (M : Fin d → Fin d → S) (v w : Fin d → S) :
    ∑ i, ∑ j, M i j * v i * w j = v ⬝ᵥ (Matrix.of M *ᵥ w) := by
  simp only [dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem balanced_iff (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] {d : ℕ}
    (A : 𝓞 E → Matrix (Fin d) (Fin d) S) (u : Lt1 Dw → Fin d → S)
    (heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), A a *ᵥ u ℓ = algebraMap c.F S (embK c ℓ.1 a) • u ℓ)
    (hsp : ∀ v : Fin d → S, ∃ a : Lt1 Dw → S, ∀ j, ∑ ℓ, a ℓ * u ℓ j = v j)
    (M : Fin d → Fin d → S) :
    (∀ a, (A a)ᵀ * Matrix.of M = Matrix.of M * A (H.bar a)) ↔
      ∀ ℓ ℓ' : Lt1 Dw, ∑ i, ∑ j, M i j * u ℓ i * u ℓ' j ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 := by
  have eL : ∀ a ℓ ℓ', u ℓ ⬝ᵥ (((A a)ᵀ * Matrix.of M) *ᵥ u ℓ') =
      algebraMap c.F S (embK c ℓ.1 a) * (u ℓ ⬝ᵥ (Matrix.of M *ᵥ u ℓ')) := by
    intro a ℓ ℓ'
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose, heig, smul_dotProduct, smul_eq_mul]
  have eR : ∀ a ℓ ℓ', u ℓ ⬝ᵥ ((Matrix.of M * A a) *ᵥ u ℓ') =
      algebraMap c.F S (embK c ℓ'.1 a) * (u ℓ ⬝ᵥ (Matrix.of M *ᵥ u ℓ')) := by
    intro a ℓ ℓ'
    rw [← mulVec_mulVec, heig, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have cc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ => by
    ext x; simp [ComplexEmbedding.conjugate]
  constructor
  · intro h ℓ ℓ' hne
    by_contra hc
    apply hne
    rw [pairing_eq]
    refine GlobalTheory.ChartJoints.balanced_pairs H c ℓ.1 ℓ'.1 _ (fun a => ?_) (fun h' => hc ?_)
    · rw [← eL, ← eR, h]
    · rw [h', cc]
  · intro h a
    set N := (A a)ᵀ * Matrix.of M - Matrix.of M * A (H.bar a) with hN
    have h0 : ∀ ℓ ℓ', u ℓ ⬝ᵥ (N *ᵥ u ℓ') = 0 := by
      intro ℓ ℓ'
      rw [hN, sub_mulVec, dotProduct_sub, eL, eR]
      by_cases hz : ∑ i, ∑ j, M i j * u ℓ i * u ℓ' j = 0
      · rw [← pairing_eq, hz]; simp
      · have hb : embK c ℓ'.1 (H.bar a) = embK c ℓ.1 a := by
          apply Subtype.ext
          rw [embK_coe, embK_coe, GlobalTheory.ChartJoints.emb_bar, h ℓ ℓ' hz, cc]
        rw [hb, sub_self]
    have hv : ∀ v : Fin d → S, ∃ a : Lt1 Dw → S, v = ∑ ℓ, a ℓ • u ℓ := by
      intro v
      obtain ⟨a, ha⟩ := hsp v
      exact ⟨a, funext fun j => by simp [← ha j, Finset.sum_apply]⟩
    have h1 : ∀ v w : Fin d → S, v ⬝ᵥ (N *ᵥ w) = 0 := by
      intro v w
      obtain ⟨a, rfl⟩ := hv v
      obtain ⟨b, rfl⟩ := hv w
      simp [sum_dotProduct, mulVec_sum, dotProduct_sum, mulVec_smul, h0]
    rw [← sub_eq_zero]
    ext i j
    have := h1 (Pi.single i 1) (Pi.single j 1)
    have h2 : N i j = 0 := by simpa using this
    exact h2

theorem frTruncFix_iff : FrTruncFixSt ↔ FrTruncFixBSt := by
  have key : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
      (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
      (M : Fin C.d → Fin C.d → S),
      (∀ a, (TB.dLin (C.B.A.act a))ᵀ * Matrix.of M = Matrix.of M * TB.dLin (C.B.A.act (H.bar a))) ↔
      ∀ ℓ ℓ' : Lt1 Dw, ∑ i, ∑ j, M i j * C.uvec ℓ i * C.uvec ℓ' j ≠ 0 →
        ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 := by
    intro E _ _ _ H Dw l Xo c _ S _ _ _ y C M
    refine balanced_iff c (fun a => TB.dLin (C.B.A.act a)) C.uvec (fun a ℓ => ?_)
      (fun v => (C.chart.basis v).exists) M
    funext i
    exact GlobalTheory.EigDir.linEig_holds E H Dw l Xo c S y C a ℓ i
  constructor
  · intro h E _ _ _ H Dw l Xo c _ hs S _ _ _ y C
    obtain ⟨e', hfr, hrig, cc, h1, h2, h3, h4, h5⟩ := h E H Dw l Xo c hs S y C
    exact ⟨e', hfr, hrig, cc, h1, h2, h3, fun m => (key E H Dw l Xo c S y C (cc m)).1 (h4 m), h5⟩
  · intro h E _ _ _ H Dw l Xo c _ hs S _ _ _ y C
    obtain ⟨e', hfr, hrig, cc, h1, h2, h3, h4, h5⟩ := h E H Dw l Xo c hs S y C
    exact ⟨e', hfr, hrig, cc, h1, h2, h3, fun m => (key E H Dw l Xo c S y C (cc m)).2 (h4 m), h5⟩

end GlobalTheory.BalancedTwist
end
