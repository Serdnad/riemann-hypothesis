module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMeanContinuity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TubeFourierExpansion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle016
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem isotropic_outside_line_of_covering (hD3 : IntegerApproximationCount (E := E)) : IsotropicOutsideLine (E := E) := by
  intro r X ξ hξ z0 hz0 x hxL hxξ _hxne hsmall
  obtain ⟨hξΛ, hξξ, -⟩ := hξ
  obtain ⟨hzdom, hzD⟩ := hz0
  have hmaj_ne : ∀ τ : X.Ψ, X.maj z0 τ (Data.emb τ.1 ξ) ≠ 0 := fun τ h => by
    have h1 := hzD τ
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  have hHne : ∀ τ : X.Ψ, X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) ≠ 0 := fun τ => by
    rw [X.Hf_self hzdom τ]
    exact_mod_cast hmaj_ne τ
  have hu : ∀ (v : Fin r → E) (τ : X.Ψ), X.ucomp z0 ξ (X.embV v) τ = Data.emb τ.1 v -
      (X.Hf z0 τ (Data.emb τ.1 v) (Data.emb τ.1 ξ) / X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
        Data.emb τ.1 ξ := fun v τ => rfl
  have hxx : herm X.Gm x x = 0 := by
    apply UnipotentCoefficientShift.eq_zero_of_conj_lt_one (X.L'_int x hxL x hxL)
    have hΨ : ∀ τ : X.Ψ, ‖τ.1 (herm X.Gm x x)‖ < 1 := by
      intro τ
      have h1 : hermC τ.1 X.Gm (Data.emb τ.1 x) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hxξ, map_zero]
      have h2 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 x) = 0 := by
        rw [← hermC_conj τ.1 X.Gm_herm, h1, map_zero]
      have h3 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hξξ, map_zero]
      have hww : hermC τ.1 X.Gm (X.ucomp z0 ξ (X.embV x) τ) (X.ucomp z0 ξ (X.embV x) τ) =
          τ.1 (herm X.Gm x x) := by
        rw [hu x τ]
        simp only [hermC_sub_left, hermC_sub_right, hermC_smul_left, hermC_smul_right]
        rw [h1, h2, h3, hermC_emb]
        ring
      rw [← hww]
      exact lt_of_le_of_lt (UnipotentCoefficientShift.norm_hermC_le_maj hzdom τ _) (hsmall τ)
    intro σ
    by_cases hσ : σ ∈ X.Ψ
    · exact hΨ ⟨σ, hσ⟩
    · have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
        have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
          RingHom.ext fun a => by simp
        rw [X.cmType, hcc]
        exact hσ
      have h := hΨ ⟨_, hc⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using h
  refine ⟨hxx, ?_⟩
  obtain ⟨α, hα⟩ := (hD3 r X.toData).1 (fun τ => -(X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
    X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) / (X.NA : ℂ))
  refine ⟨α, ?_⟩
  intro x'
  have hemb : ∀ τ : X.Ψ, Data.emb τ.1 x' =
      Data.emb τ.1 x + τ.1 ((X.NA : E) * α) • Data.emb τ.1 ξ := by
    intro τ
    funext a
    simp [x', Data.emb]
  have hx'L : x' ∈ X.L' := by
    apply X.L'.add_mem hxL
    have h1 : (X.NA : E) • ξ ∈ X.L' := X.NA_sub ξ hξΛ
    have h2 := X.L'.smul_mem α h1
    have h3 : α • ((X.NA : E) • ξ) = ((X.NA : E) * (α : E)) • ξ := by
      rw [← algebraMap_smul E α ((X.NA : E) • ξ), smul_smul]
      congr 1
      exact mul_comm _ _
    rwa [h3] at h2
  have hx'ξ : herm X.Gm x' ξ = 0 := by
    simp only [x']
    rw [HermitianTraceFormVanishing.herm_add_left, HermitianTraceFormVanishing.herm_smul_left, hxξ, hξξ, mul_zero, add_zero]
  have hucomp : X.ucomp z0 ξ (X.embV x') = X.ucomp z0 ξ (X.embV x) := by
    funext τ
    rw [hu x' τ, hu x τ, hemb τ, UnipotentCoefficientShift.ucomp_shift _ _ _ _ _ (hHne τ)]
  have hcoef : ∀ τ : X.Ψ, ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA := by
    intro τ
    rw [hemb τ, UnipotentCoefficientShift.coef_shift _ _ _ _ _ (hHne τ)]
    have hNA : (X.NA : ℂ) ≠ 0 := by exact_mod_cast X.NA_pos.ne'
    set k := X.Hf z0 τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with hkdef
    have hk : (X.NA : ℂ) * (k / X.NA) = k := by field_simp
    have e : k + τ.1 ((X.NA : E) * α) = (X.NA : ℂ) * (τ.1 (α : E) - -k / X.NA) := by
      rw [map_mul, map_natCast]
      linear_combination (-1 : ℂ) * hk
    rw [e, norm_mul, Complex.norm_natCast]
    have hb : ‖τ.1 (α : E) - -k / X.NA‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := hα τ
    calc (X.NA : ℝ) * ‖τ.1 (α : E) - -k / X.NA‖ ≤ X.NA * (2 * (fdeg E : ℝ) ^ 2 * rdE E) :=
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = 2 * (fdeg E : ℝ) ^ 2 * rdE E * X.NA := by ring
  refine ⟨hx'L, hx'ξ, hucomp, hcoef, ?_⟩
  intro τ
  have hembNC : Data.emb τ.1 ((X.NC : E) • x') = ((X.NC : ℝ) : ℂ) • Data.emb τ.1 x' := by
    funext a
    simp [Data.emb]
  rw [hembNC, UnipotentCoefficientShift.maj_smul hzdom, UnipotentCoefficientShift.maj_decomp hzdom τ _ _ (hHne τ)]
  have hw : Data.emb τ.1 x' - (X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
      X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ =
        X.ucomp z0 ξ (X.embV x) τ := by
    rw [← hucomp, hu x' τ]
  rw [hw]
  have hK := hcoef τ
  set K := ‖X.Hf z0 τ (Data.emb τ.1 x') (Data.emb τ.1 ξ) /
    X.Hf z0 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ with hKdef
  set m := X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ) with hmdef
  have hc2 : X.c τ ≤ 2 := by
    unfold Data.c
    rw [X.ξ0_abs τ]
    linarith [X.k0_le]
  have hc0 : 0 ≤ X.c τ := by
    unfold Data.c
    positivity
  have hD := hzD τ
  have hm : m < 1 := hsmall τ
  have hK0 : 0 ≤ K := norm_nonneg _
  have h1 : X.c τ * m ≤ 2 := by nlinarith
  have h2 : K ^ 2 ≤ 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2 := by
    nlinarith [mul_le_mul hK hK hK0 (le_trans hK0 hK)]
  have h3 : X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)) = X.c τ * m + K ^ 2 := by
    linear_combination K ^ 2 * hD
  have h4 : X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)) ≤
      2 + 4 * (fdeg E : ℝ) ^ 4 * rdE E ^ 2 * (X.NA : ℝ) ^ 2 := by
    rw [h3]
    linarith
  calc X.c τ * ((X.NC : ℝ) ^ 2 * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ)))
      = (X.NC : ℝ) ^ 2 * (X.c τ * (m + K ^ 2 * X.maj z0 τ (Data.emb τ.1 ξ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)

theorem isotropic_outside_line : IsotropicOutsideLine (E := E) := isotropic_outside_line_of_covering integerApproximationCount_holds

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem cusp_coefficient_quantitative_holds : CuspCoefficientBound (E := E) := CuspCoefficientQuantitative.cusp_coefficient_bound_of_unipotent_lattice_lift unipotent_lattice_lift

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.ChartRestriction.G.FD.TubeSummability ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
  ReciprocityTheory.ChartRestriction.G.FD.FrequencyIndexing

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem m3bExp_holds : FourierJacobiExpansion (E := E) := by
  classical
  intro r X la P hP ξ hξ x hx s hs
  obtain ⟨hξΛ, hξ0, -⟩ := id hξ

  obtain ⟨n, ω, hω⟩ : ∃ (n : ℕ) (ω : Module.Basis (Fin n) ℝ (X.Ψ → ℝ)),
      Submodule.span ℤ (Set.range ω) = perL X la := by
    let b := (Module.Free.chooseBasis ℤ (perL X la)).reindex (Fintype.equivFin _)
    exact ⟨_, b.ofZLatticeBasis ℝ (perL X la), b.ofZLatticeBasis_span ℝ (perL X la)⟩
  have hωp : ∀ j, ω j ∈ X.periods la := by
    intro j
    have h1 : ω j ∈ perL X la := by
      rw [← hω]
      exact Submodule.subset_span ⟨j, rfl⟩
    exact h1

  have hsurj : ∀ u : X.Ψ → ℂ, ∃ t : Fin n → ℂ, TubeSummability.Lc X ω t = u := by
    intro u
    refine ⟨fun j => (ω.repr (fun τ => (u τ).re) j : ℂ) +
      (ω.repr (fun τ => (u τ).im) j : ℂ) * I, ?_⟩
    funext τ
    have hre : ∑ j, ω.repr (fun τ => (u τ).re) j * ω j τ = (u τ).re := by
      have := congrFun (ω.sum_repr (fun τ => (u τ).re)) τ
      simpa [Finset.sum_apply, smul_eq_mul] using this
    have him : ∑ j, ω.repr (fun τ => (u τ).im) j * ω j τ = (u τ).im := by
      have := congrFun (ω.sum_repr (fun τ => (u τ).im)) τ
      simpa [Finset.sum_apply, smul_eq_mul] using this
    simp only [TubeSummability.Lc]
    calc _ = ((∑ j, ω.repr (fun τ => (u τ).re) j * ω j τ : ℝ) : ℂ) +
          ((∑ j, ω.repr (fun τ => (u τ).im) j * ω j τ : ℝ) : ℂ) * I := by
          push_cast
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = u τ := by
          rw [hre, him]
          exact Complex.re_add_im (u τ)
  obtain ⟨t, rfl⟩ := hsurj s
  have ht : t ∈ tube n (TubeSummability.Om X ξ x ω) :=
    (TubeSummability.flow_Lc_mem_dom (ω := ω) hξ0 hx t).mp hs
  have hΩ := TubeSummability.Om_open_convex (ξ := ξ) (ω := ω) hx
  have hexp : HasSum (fun k : Fin n → ℤ =>
      fourCoeff (TubeSummability.hline X P ξ x ω) 0 k * cexp (2 * Real.pi * I * ∑ j, (k j : ℂ) * t j))
      (P (X.flow ξ (TubeSummability.Lc X ω t) x)) :=
    (TubeFourierExpansion.tube_expansion (TubeSummability.Om X ξ x ω) (TubeSummability.hline X P ξ x ω) hΩ.1 hΩ.2
      (TubeSummability.zero_mem_Om (ω := ω) hξ0 hx) (TubeSummability.hline_diff (X := X) (la := la) (P := P) (ξ := ξ) (x := x) (ω := ω) hP hξ0 hx)
      (TubeSummability.hline_periodic (X := X) (la := la) (P := P) (ξ := ξ) (x := x) (ω := ω)
        hP hξΛ hξ0 hx hωp) t ht).2
  refine ((FrequencyIndexing.νk_injective (ω := ω)).hasSum_iff ?_).mp ?_
  · intro ν hν
    have hfj : X.fj la ξ ν P x = 0 := by
      rw [Data.fj]
      refine if_neg ?_
      intro hall
      apply hν
      choose k hk using fun j => hall (ω j) (hωp j)
      exact ⟨k, (FrequencyIndexing.eq_νk (ω := ω) ν k hk).symm⟩
    simp only [hfj, zero_mul]
  · convert hexp using 1
    funext k
    simp only [Function.comp_apply]
    congr 1
    · exact FlowMeanContinuity.fj_eq_fourCoeff (X := X) (la := la) P hP hξ hx ω hω
        (FrequencyIndexing.νk ω k) k (FrequencyIndexing.νk_spec (ω := ω) k)
    · congr 1
      have key : ∀ j, ∑ τ, (FrequencyIndexing.νk ω k τ : ℂ) * (ω j τ : ℂ) = (k j : ℂ) / 2 := by
        intro j
        have h2 := FrequencyIndexing.νk_spec (ω := ω) k j
        have h3 : ∑ τ, FrequencyIndexing.νk ω k τ * ω j τ = (k j : ℝ) / 2 := by linarith
        exact_mod_cast h3
      have hsw : ∑ τ, (FrequencyIndexing.νk ω k τ : ℂ) * TubeSummability.Lc X ω t τ =
          ∑ j, t j * ((k j : ℂ) / 2) := by
        simp only [TubeSummability.Lc, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← key j, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun τ _ => by ring)
      rw [hsw, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)

end ReciprocityTheory.ChartRestriction.G.FD
end
