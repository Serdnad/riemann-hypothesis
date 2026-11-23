module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle043
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Group.Tannery
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle411
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.TraceSimilitude

theorem trace_natSq_mul {E : Type} [Field E] [NumberField E] (N : ℕ) (x : E) :
    Algebra.trace ℚ E ((N : E) ^ 2 * x) = (N : ℚ) ^ 2 * Algebra.trace ℚ E x := by
  have h : ((N : E) ^ 2) = algebraMap ℚ E ((N : ℚ) ^ 2) := by simp
  rw [h, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem exists_gl_of_trace_similitude : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ), 0 < N → (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) → ∀ (gam : X.Λ →ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (gam u : Fin r → E) (gam v : Fin r → E)) = (N : ℚ) ^ 2 * Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (u : Fin r → E) (v : Fin r → E))) → (∀ w : X'.Λ, ∃ v, gam v = (N ^ 2) • w) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (N : E) • ((a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E)) = (gam v : Fin r → E)) ∧ (∀ w ∈ X'.Λ, (N : E) • (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) ∈ X.Λ) ∧ ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * herm X.Gm u v := by
  classical
  intro E _ _ _ r X X' N hN hn gam htr hsurj
  have hs : Submodule.span E (Set.range X.Λ.subtype) = ⊤ := by
    rw [← X.Λ_span]; congr 1; exact Subtype.range_coe
  have hs' : Submodule.span E (Set.range X'.Λ.subtype) = ⊤ := by
    rw [← X'.Λ_span]; congr 1; exact Subtype.range_coe
  obtain ⟨A, hA⟩ := FrameFibre.exists_matrix X.Λ.subtype X.Λ.injective_subtype hs
    (X'.Λ.subtype ∘ₗ gam)
  have hA' : ∀ v : X.Λ, A *ᵥ (v : Fin r → E) = (gam v : Fin r → E) := hA
  have hN0 : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hcoe : ∀ w : X'.Λ, (((N ^ 2) • w : X'.Λ) : Fin r → E) = ((N : E) ^ 2) • (w : Fin r → E) := by
    intro w
    rw [Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul E]
    push_cast; rfl
  have hsurjA : Function.Surjective (Matrix.toLin' A) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs', Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := hsurj w
    refine ⟨((N : E) ^ 2)⁻¹ • (v : Fin r → E), ?_⟩
    rw [map_smul, Matrix.toLin'_apply, hA', hv, hcoe, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero 2 hN0), one_smul]
    rfl
  have hU : IsUnit A := Matrix.mulVec_surjective_iff_isUnit.1 hsurjA
  set U := hU.unit with hUdef
  have hUA : (U : Matrix (Fin r) (Fin r) E) = A := hU.unit_spec
  let a : GL (Fin r) E :=
    ⟨(N : E)⁻¹ • A, (N : E) • ((U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E),
      by rw [smul_mul_smul_comm, inv_mul_cancel₀ hN0, one_smul, ← hUA, U.mul_inv],
      by rw [smul_mul_smul_comm, mul_inv_cancel₀ hN0, one_smul, ← hUA, U.inv_mul]⟩
  have ha : (a : Matrix (Fin r) (Fin r) E) = (N : E)⁻¹ • A := rfl
  have hai : ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) =
      (N : E) • ((U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) := rfl
  obtain ⟨ε, hε, hξ⟩ : ∃ ε : E, (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 := by
    rcases TraceIsometry.eq_or_eq_neg_of_norm_eq X.ξ0_im X'.ξ0_im hn with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, _root_.one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul]⟩
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
  have h1 : cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
  have key : ∀ u v : X.Λ, herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) =
      (N : E) ^ 2 * ε * herm X.Gm u v := by
    intro u v
    have h0 : -X'.ξ0 * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) -
        (N : E) ^ 2 * (-X.ξ0 * herm X.Gm u v) = 0 := by
      refine FrameFibre.eq_zero_of_trace _ fun b => ?_
      have h2 := htr (b • u) v
      have h3 : ((b • u : X.Λ) : Fin r → E) = (b : E) • (u : Fin r → E) := rfl
      have h4 := FrameFibre.herm_smul_smul X'.Gm (b : E) 1 (A *ᵥ (u : Fin r → E))
        (A *ᵥ (v : Fin r → E))
      have h5 := FrameFibre.herm_smul_smul X.Gm (b : E) 1 (u : Fin r → E) (v : Fin r → E)
      rw [one_smul, h1, _root_.mul_one] at h4 h5
      rw [← hA', ← hA', h3, Matrix.mulVec_smul, h4, h5] at h2
      have e1 : (b : E) * (-X'.ξ0 * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E))) =
          -X'.ξ0 * ((b : E) * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E))) := by ring
      have e2 : (b : E) * ((N : E) ^ 2 * (-X.ξ0 * herm X.Gm u v)) =
          (N : E) ^ 2 * (-X.ξ0 * ((b : E) * herm X.Gm u v)) := by ring
      rw [mul_sub, map_sub, e1, e2, trace_natSq_mul, h2, sub_self]
    rw [hξ] at h0
    apply mul_left_cancel₀ X.ξ0_ne
    linear_combination (-ε) * h0 -
      (X.ξ0 * herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E))) * hε2
  have keyA : ∀ x y : Fin r → E, herm X'.Gm (A *ᵥ x) (A *ᵥ y) = (N : E) ^ 2 * ε * herm X.Gm x y := by
    intro x y
    obtain ⟨c, v, hc, hv⟩ := FrameFibre.exists_smul_eq X.Λ.subtype hs x
    obtain ⟨d, w, hd, hw⟩ := FrameFibre.exists_smul_eq X.Λ.subtype hs y
    have h2 := key v w
    rw [Submodule.subtype_apply] at hv hw
    rw [← hv, ← hw, Matrix.mulVec_smul, Matrix.mulVec_smul, FrameFibre.herm_smul_smul,
      FrameFibre.herm_smul_smul] at h2
    have hc' : (c : E) ≠ 0 := by simpa using hc
    have hd' : cc (d : E) ≠ 0 := (map_ne_zero (IsCMField.complexConj E)).2 (by simpa using hd)
    apply mul_left_cancel₀ (mul_ne_zero hc' hd')
    linear_combination h2
  refine ⟨a, ε, hε, hξ, fun v => ?_, fun w hw => ?_, fun x y => ?_⟩
  · rw [ha, Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hN0, one_smul, hA']
  · obtain ⟨v, hv⟩ := hsurj ⟨w, hw⟩
    have h3 : (U : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) = (N : E) ^ 2 • w := by
      rw [hUA, hA', hv, hcoe]
    have h2 : ((U⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((N : E) ^ 2 • w) = v := by
      rw [← h3, Matrix.mulVec_mulVec, U.inv_mul, Matrix.one_mulVec]
    rw [hai, Matrix.smul_mulVec, smul_smul, ← pow_two, ← Matrix.mulVec_smul, h2]
    exact v.2
  · have hcc : cc ((N : E)⁻¹) = (N : E)⁻¹ :=
      (map_inv₀ (IsCMField.complexConj E) _).trans (by rw [map_natCast])
    rw [ha, Matrix.smul_mulVec, Matrix.smul_mulVec, FrameFibre.herm_smul_smul, hcc,
      keyA]
    field_simp

end GlobalTheory.TraceSimilitude
end

section

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix

namespace GlobalTheory.HeckeEx

theorem bddSec_tendsto_constTerm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsBddSec la P → ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, (∀ t : ℝ, 0 ≤ t → X.flow ξ (fun _ => Complex.I * t) x ∈ X.dom) ∧ Filter.Tendsto (fun t : ℝ => P (X.flow ξ (fun _ => Complex.I * t) x)) Filter.atTop (nhds (X.fj la ξ 0 P x)) := by
  intro E _ _ _ r X la P hP ξ hξ x hx
  have hdom : ∀ t : ℝ, 0 ≤ t → X.flow ξ (fun _ => Complex.I * t) x ∈ X.dom := fun t ht =>
    GlobalTheory.FjCauchy.flow_mem_dom X hξ hx _ fun τ => by
      have := GlobalTheory.FjCauchy.tt_pos X hξ hx τ
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, one_mul, zero_add]
      linarith
  refine ⟨hdom, ?_⟩
  have hexp := m3bExp_holds (E := E) r X la P hP.1 ξ hξ x hx

  have hfac : ∀ (ν : X.Ψ → ℝ) (t : ℝ),
      Complex.exp (4 * Real.pi * Complex.I * ∑ τ, (ν τ : ℂ) * (fun _ => Complex.I * (t : ℂ)) τ) =
        ((Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)) : ℝ) : ℂ) := by
    intro ν t
    rw [Complex.ofReal_exp]
    congr 1
    have hs : ∑ τ, (ν τ : ℂ) * (Complex.I * (t : ℂ)) = (∑ τ, (ν τ : ℂ)) * (Complex.I * t) := by
      rw [Finset.sum_mul]
    simp only [hs]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  set F : ℝ → (X.Ψ → ℝ) → ℂ := fun t ν =>
    X.fj la ξ ν P x * Complex.exp (4 * Real.pi * Complex.I * ∑ τ, (ν τ : ℂ) * (fun _ => Complex.I * (t : ℂ)) τ)
    with hF
  have hF' : ∀ t ν, F t ν = X.fj la ξ ν P x * ((Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)) : ℝ) : ℂ) := by
    intro t ν; rw [hF]; dsimp only; rw [hfac]

  have hsum0 : Summable fun ν : X.Ψ → ℝ => X.fj la ξ ν P x := by
    have h := (hexp _ (hdom 0 le_rfl)).summable
    refine h.congr fun ν => ?_
    have := hF' 0 ν
    rw [hF] at this
    simp only [mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, _root_.mul_one] at this
    exact this
  have hbound : Summable fun ν : X.Ψ → ℝ => ‖X.fj la ξ ν P x‖ := summable_norm_iff.mpr hsum0
  have hsign : ∀ ν : X.Ψ → ℝ, X.fj la ξ ν P x ≠ 0 → ∀ τ, 0 ≤ ν τ := fun ν h =>
    BoundedSectionAlgebra.sign_of_bdd X moderateCoefficientPositivity_holds hP hξ ν hx h
  have hlim : Filter.Tendsto (fun t => ∑' ν, F t ν) Filter.atTop
      (nhds (∑' ν : X.Ψ → ℝ, if ν = 0 then X.fj la ξ 0 P x else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hbound (fun ν => ?_) ?_
    · by_cases h0 : X.fj la ξ ν P x = 0
      · have : (if ν = 0 then X.fj la ξ 0 P x else 0) = 0 := by
          split_ifs with h; · subst h; exact h0
          · rfl
        rw [this]
        simp only [hF', h0, zero_mul]
        exact tendsto_const_nhds
      by_cases hν : ν = 0
      · subst hν
        simp only [hF', if_true, Finset.sum_const_zero, Pi.zero_apply, mul_zero, zero_mul, neg_zero,
          Real.exp_zero, Complex.ofReal_one, _root_.mul_one]
        exact tendsto_const_nhds
      · rw [if_neg hν]
        have hnn := hsign ν h0
        obtain ⟨τ0, hτ0⟩ : ∃ τ0, ν τ0 ≠ 0 := by
          by_contra hc; push_neg at hc; exact hν (funext hc)
        have hS : 0 < ∑ τ, ν τ :=
          Finset.sum_pos' (fun τ _ => hnn τ) ⟨τ0, Finset.mem_univ _, lt_of_le_of_ne (hnn τ0) (Ne.symm hτ0)⟩
        have hk : 0 < 4 * Real.pi * ∑ τ, ν τ := by positivity
        have he : Filter.Tendsto (fun t : ℝ => Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)))
            Filter.atTop (nhds 0) :=
          Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.tendsto_id.const_mul_atTop hk)
        have := ((Complex.continuous_ofReal.tendsto 0).comp he).const_mul (X.fj la ξ ν P x)
        simp only [Complex.ofReal_zero, mul_zero] at this
        simp only [hF']
        exact this
    · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht ν
      rw [hF', norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      by_cases h0 : X.fj la ξ ν P x = 0
      · simp [h0]
      have hS : 0 ≤ ∑ τ, ν τ := Finset.sum_nonneg fun τ _ => hsign ν h0 τ
      have : Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ 4 * Real.pi * (∑ τ, ν τ) * t := by positivity
        linarith
      calc ‖X.fj la ξ ν P x‖ * Real.exp (-(4 * Real.pi * (∑ τ, ν τ) * t))
          ≤ ‖X.fj la ξ ν P x‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = ‖X.fj la ξ ν P x‖ := _root_.mul_one _
  rw [tsum_ite_eq] at hlim
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  simp only [hF]
  exact (hexp _ (hdom t ht)).tsum_eq

end GlobalTheory.HeckeEx
end
