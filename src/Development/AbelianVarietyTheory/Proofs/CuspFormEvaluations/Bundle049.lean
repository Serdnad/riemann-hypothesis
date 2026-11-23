module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle044
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle042
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle043
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.unitaryDatumNumbers_for_supBounds : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), fdeg D.host.E = D.R.f ∧ Real.log (rdE D.host.E) = lrd D ∧ 1 ≤ rdE D.host.E ∧ 1 ≤ D.R.f ∧ 1 ≤ D.R.r ∧ 0 < xiR D ∧ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) ≤ WeightAlgebra.DF w ∧ absA w = (WeightAlgebra.DF w : ℝ) ∧ (∀ σ, GoodEmb T.Q.c σ → ∀ k τ, ((T.U j σ).X k).c τ = 2 * xiR D) ∧ lieFac (T.Q.Dw j) (xiR D) (wtA w) = Real.exp (-(((Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℕ) : ℝ) / 2) * Real.log (Real.pi * (2 * xiR D))) ∧ T.Q.l.A = 1 ∧ 0 < D.host.pde ∧ 0 < D.host.pde' ∧ ∀ (ι : Type) (σ : T.Q.c.F →+* ℂ) (P : MvPolynomial ι T.Q.c.F), l1At (goodOf T.Q.c σ) P = l1At σ P := by
  first | exact @GlobalTheory.SupDict.record_dictionary | exact GlobalTheory.SupDict.record_dictionary | (intros; apply GlobalTheory.SupDict.record_dictionary <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

theorem _root_.GlobalTheory.T.exists_reduced_integral_basis_harmonicPolynomials : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (n : ℕ), Dw.p + Dw.q ≤ n → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (L : ℝ), 2 ≤ L → Real.log (FD.rdE E) ≤ 2 * L → Real.log (FD.fdeg E) ≤ 2 * L → Real.log (1 + DF Dw a) ≤ 2 * L → Real.log n ≤ L → ∃ (R : ℕ) (b : Fin R → MvPolynomial (LtN Dw n) c.F), (∀ i, b i ∈ harmA (Dw := Dw) c a n) ∧ (∀ P ∈ harmA (Dw := Dw) c a n, ∃ z : Fin R → ℤ, P = ∑ i, (z i : c.F) • b i) ∧ R ≤ Module.finrank ℚ c.F * (1 + DF Dw a) ^ (FD.fdeg E * (Dw.p + Dw.q) * n) ∧ ∀ i (σ : c.F →+* ℂ), l1At σ (b i) ≤ Real.exp (140 * (Dw.p + Dw.q : ℕ) * L * DF Dw a + 2 * FD.fdeg E * (Dw.p + Dw.q : ℕ) * n * L + 4 * Real.log (Module.finrank ℚ c.F) + Real.log |((NumberField.discr c.F : ℤ) : ℝ)| / Module.finrank ℚ c.F) := by
  first | exact @GlobalTheory.HarmBasis.exists_reduced_basis_harmA | exact GlobalTheory.HarmBasis.exists_reduced_basis_harmA | (intros; apply GlobalTheory.HarmBasis.exists_reduced_basis_harmA <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

private theorem AnFr.exp_nsmul_eq_pow_vt {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) (z : Fin g → ℂ) (n : ℕ) : Φ.e (n • z) = Φ.e z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact (Φ.e_ker 0).2 Φ.lat.zero_mem
  | succ n ih => rw [succ_nsmul, Φ.e_add, ih, pow_succ]

theorem rd_vt_and_uu : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ (N : ℕ), Odd N → ∀ (s : LB.Sec (LPow A L.L 1 (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Φ.Rd 1 s θ → (∀ (ok : (Over.mk x0 ⟶ A) → Prop) (t : Over.mk x0 ⟶ A) (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) (Over.mk x0))), IsVtOver A L N ok s t F → (∀ t', ok t' → t' ^ N = t → t' ^ (N ^ 2) = 1) → ∃ x δ : Fin g → ℂ, δ ∈ Φ.lat ∧ ((N : ℂ) ^ 2) • x = (2 : ℂ) • δ ∧ ok (Φ.e x) ∧ Φ.e x ^ N = t ∧ Φ.Rd ((N : ℤ) ^ 2) F (fock Φ.Hm ((N : ℤ) ^ 2) x fun z => θ ((N : ℂ) • z))) ∧ ∀ (x₁ δ₁ x₂ δ₂ : Fin g → ℂ) (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) (Over.mk x0))), δ₁ ∈ Φ.lat → ((N : ℂ) ^ 2) • x₁ = (2 : ℂ) • δ₁ → δ₂ ∈ Φ.lat → ((N : ℂ) ^ 2) • x₂ = (2 : ℂ) • δ₂ → IsUUOver A L N s (Φ.e x₁) (Φ.e x₂) F → Φ.Rd ((N : ℤ) ^ 2) F (fock Φ.Hm ((N : ℤ) ^ 2) x₂ (fock Φ.Hm ((N : ℤ) ^ 2) x₁ fun z => θ ((N : ℂ) • z))) := by
  intro S A _ _ L x0 g Φ hχ N hN s θ hs
  have hN2 : Odd (N ^ 2) := hN.pow
  refine ⟨?_, ?_⟩
  · rintro ok t F ⟨t', α₀, α, s₁, U, ht, hok, h1, h2, h3, h4, h5, h6⟩ hkill
    obtain ⟨x', rfl⟩ := Φ.e_onto t'
    have hl : (N ^ 2) • x' ∈ Φ.lat := by
      rw [← Φ.e_ker, Φ.exp_nsmul_eq_pow_vt]; exact hkill _ hok ht
    obtain ⟨m, hm⟩ := hN2
    have he : Φ.e (x' + (N ^ 2) • x') = Φ.e x' := by
      rw [Φ.e_add, (Φ.e_ker _).2 hl, _root_.mul_one]
    have hx : ((N ^ 2 : ℕ) : ℂ) • (x' + (N ^ 2) • x') = (2 : ℂ) • ((m + 1) • (N ^ 2) • x') := by
      rw [hm]
      ext i
      simp only [Pi.smul_apply, Pi.add_apply]
      simp only [smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    refine ⟨x' + (N ^ 2) • x', (m + 1) • (N ^ 2) • x', Φ.lat.nsmul_mem hl _, ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hx
    · rw [he]; exact hok
    · rw [he]; exact ht
    · refine GlobalTheory.T.symmetric_lift_odd_order_acts_as_translation S A L x0 g Φ hχ _ (N ^ 2) U _ _ s₁ F _ ⟨m, hm⟩ (Φ.lat.nsmul_mem hl _) hx ?_ h6
        (GlobalTheory.T.normalisedPullbackMulN_reads_theta S A L x0 g Φ N α₀ α s s₁ θ h1 h2 h3 h4 hs)
      rw [he]; exact h5
  · rintro x₁ δ₁ x₂ δ₂ F hδ₁ hx₁ hδ₂ hx₂ ⟨α₀, α, s₁, s₂, U₁, U₂, h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine GlobalTheory.T.symmetric_lift_odd_order_acts_as_translation S A L x0 g Φ hχ _ (N ^ 2) U₂ x₂ δ₂ s₂ F _ hN2 hδ₂ (by simpa only [Nat.cast_pow] using hx₂) h7 h8 ?_
    exact GlobalTheory.T.symmetric_lift_odd_order_acts_as_translation S A L x0 g Φ hχ _ (N ^ 2) U₁ x₁ δ₁ s₁ s₂ _ hN2 hδ₁ (by simpa only [Nat.cast_pow] using hx₁) h5 h6
      (GlobalTheory.T.normalisedPullbackMulN_reads_theta S A L x0 g Φ N α₀ α s s₁ θ h1 h2 h3 h4 hs)

end GlobalTheory.AnVal
end
