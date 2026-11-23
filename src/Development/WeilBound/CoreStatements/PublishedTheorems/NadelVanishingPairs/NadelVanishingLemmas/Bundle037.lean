module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle036
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsEmbeddedResolution
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle030
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsMultiplierIdeal
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle034
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
namespace GlobalTheory.LogResBig

theorem supp_nsmul_le {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) : ∀ c : ℕ, (c • D).supp ≤ D.supp
  | 0 => by
    rw [zero_smul, CartierDiv.supp_eq_bot_iff.2 rfl]
    exact bot_le
  | c + 1 => by
    rw [succ_nsmul]
    exact (CartierDiv.supp_add_le _ _).trans (sup_le (supp_nsmul_le D c) le_rfl)

theorem eff_nsmul {Y : Scheme.{0}} [IsIntegral Y] {D : CartierDiv Y} (hD : D.Eff) : ∀ c : ℕ, (c • D).Eff
  | 0 => by
    rw [zero_smul]
    exact CartierDiv.eff_zero
  | c + 1 => by
    rw [succ_nsmul]
    exact (eff_nsmul hD c).add hD

theorem exists_logRes_smul_eq_ample_add_eff :
    GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X), η ≠ 0 → ∀ Z : Closeds X, Z ≠ ⊤ → ∀ (M : LB X) (hM : M.IsLB), (letI := algebraΓOfHom p; IsBig k M) → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y), IsLogRes p n η m G s K B ∧ (∀ y, s y ∈ Z → y ∈ B) ∧ ∃ (a : ℕ) (Fd : CartierDiv Y) (A : LB Y) (hA : IsAmpleLB A), 0 < a ∧ Fd.Eff ∧ Fd.supp ≤ B ∧ a • CechPic.pull s (cls M hM) = cls A hA.isLB + toPic Fd := by
  intro hP k _ _ X _ p n hp hdim η m G hη Z hZ M hM hbig
  obtain ⟨Y₀, _, s₀, _, hsm, hpr, hbir⟩ := GlobalTheory.T.exists_smooth_projective_birational_model hP k X p n hp hdim
  have hdim₀ : topologicalKrullDim Y₀ = topologicalKrullDim X := by
    rw [hdim]
    exact GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (s₀ ≫ p) n hsm
  have hbig₀ := GlobalTheory.PullBig.isBig_pull k Y₀ X p s₀ hp hpr hdim₀ s₀.denseRange M hbig
  obtain ⟨A, hA⟩ := GlobalTheory.exists_isAmpleLB_of_isProjOver hpr
  obtain ⟨a₀, D₀, ha₀, hD₀, e₀⟩ := GlobalTheory.T.big_line_bundle_kodaira_of_isProjOver k Y₀ (s₀ ≫ p) hpr (M.pull s₀) A hbig₀ hA
  let Zp : Closeds Y₀ := ⟨s₀ ⁻¹' (Z : Set X), Z.isClosed.preimage s₀.continuous⟩
  have hZ' : Zp ⊔ D₀.supp ≠ ⊤ := by
    intro htop
    have hg : genericPoint Y₀ ∈ ((Zp ⊔ D₀.supp : Closeds Y₀) : Set Y₀) := by
      rw [htop]; trivial
    rw [Closeds.coe_sup] at hg
    rcases hg with hg | hg
    · apply hZ
      have hall : Set.univ ⊆ (Zp : Set Y₀) :=
        ((genericPoint_spec Y₀).mem_closed_set_iff Zp.isClosed).1 hg
      have hrange : Set.range s₀ ⊆ (Z : Set X) := by
        rintro _ ⟨y, rfl⟩
        exact hall (Set.mem_univ y)
      have hcl : closure (Set.range s₀) ⊆ (Z : Set X) := closure_minimal hrange Z.isClosed
      rw [s₀.denseRange.closure_range] at hcl
      exact Closeds.ext (Set.eq_univ_of_univ_subset hcl)
    · exact CartierDiv.genericPoint_notMem_supp D₀ hg
  obtain ⟨Y, _, t, _, K, B, hres, hB, c, E, A₁, hA₁, hc, hE, hEB, e₁⟩ :=
    GlobalTheory.T.exists_embedded_resolution hP k X p n η m G hη Y₀ s₀ hsm hpr hbir (Zp ⊔ D₀.supp) hZ' A hA
  have hmem : ∀ y : Y, t y ∈ Zp ∨ t y ∈ D₀.supp → y ∈ B := fun y h => by
    apply hB y
    show t y ∈ ((Zp ⊔ D₀.supp : Closeds Y₀) : Set Y₀)
    rw [Closeds.coe_sup]
    exact h
  refine ⟨Y, inferInstance, t ≫ s₀, inferInstance, K, B, hres, ?_, c * a₀, E + c • pullCart t D₀, A₁, hA₁,
    Nat.mul_pos hc ha₀, hE.add (eff_nsmul ((GlobalTheory.T.cartierDivisorPullback_support_and_effective Y₀ Y t D₀).2 hD₀) c), ?_, ?_⟩
  · intro y hy
    refine hmem y (Or.inl ?_)
    show s₀ (t y) ∈ (Z : Set X)
    simpa using hy
  · refine (CartierDiv.supp_add_le _ _).trans (sup_le hEB ((supp_nsmul_le _ c).trans ?_))
    intro y hy
    exact hmem y (Or.inr ((GlobalTheory.T.cartierDivisorPullback_support_and_effective Y₀ Y t D₀).1 y hy))
  · have e₀' : a₀ • CechPic.pull s₀ (cls M hM) = cls A hA.isLB + toPic D₀ := e₀
    rw [map_add (f := _), map_nsmul, toPic_pullCart, GlobalTheory.CechPic.pull_comp, mul_smul,
      ← map_nsmul (CechPic.pull t) a₀, e₀', map_add, smul_add, e₁, add_assoc]

end GlobalTheory.LogResBig
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem exists_isMultIdeal_support_iff_not_kltAt : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ : X → ℚ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X), IsLogMult p n Δ η m G → ∃ J : X.IdealSheafData, IsMultIdeal p n η m G J ∧ ∀ x : X, x ∈ J.support ↔ ¬ KltAt p n Δ x := by
  intro hP k _ _ X _ _ _ p n hp hdim Δ η m G hL
  have hne : (⊥ : Closeds X) ≠ ⊤ := by
    intro h
    have hx : genericPoint X ∈ ((⊤ : Closeds X) : Set X) := trivial
    rw [← h] at hx
    exact hx
  obtain ⟨Y, hYi, s, hsd, K, B, hR, -⟩ :=
    LogResExist.exists_logRes hP k X p n hp hdim η m G hL.ne_zero ⊥ hne
  haveI := hYi
  haveI := hsd
  haveI := hR.smooth
  have hsm : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth (n := n) (f := s ≫ p)
  obtain ⟨-, -, hYn⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k Y (s ≫ p) hsm
  haveI := hYn
  obtain ⟨J, hJ⟩ := MultIdealExists.exists_isMultIdeal k X p n hp η m G Y s K B hL.ne_zero hL.pos hR
  exact ⟨J, hJ, mem_support_multIdeal_iff k X p n hp hdim Δ η m G Y s K B hL hR J hJ⟩

end GlobalTheory.Discrepancy
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.exists_log_resolution : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X), η ≠ 0 → ∀ Z : Closeds X, Z ≠ ⊤ → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y), IsLogRes p n η m G s K B ∧ ∀ y, s y ∈ Z → y ∈ B := by
  first | exact @_root_.GlobalTheory.LogResExist.exists_logRes | exact _root_.GlobalTheory.LogResExist.exists_logRes | (intros; apply _root_.GlobalTheory.LogResExist.exists_logRes <;> assumption)
end
