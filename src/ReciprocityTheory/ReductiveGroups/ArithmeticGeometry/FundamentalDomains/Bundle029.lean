module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Schwarz
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientPositivity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermitianPsiBounds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantNormalForms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LogDOfPosBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CoefficientConvolutionOfSubCoefficients
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SublatticeCoefficients

@[expose] public section

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open Matrix NumberField Complex Module

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem reductionTheory_holds : MahlerCompactnessCriterion (E := E) := by
  unfold MahlerCompactnessCriterion
  intro r X ε hε
  classical
  have hm : (0:ℝ) < ε ^ 2 := by positivity
  have hB0 : (0:ℝ) ≤ 2 ^ (finrank ℤ X.Λ * (finrank ℤ X.Λ - 1)) *
      |(QuadraticLatticeForms.Bm X (RealPlaceEmbeddings.zb X)).det| / (ε ^ 2) ^ (finrank ℤ X.Λ - 1) := by positivity
  set B : ℝ := 2 ^ (finrank ℤ X.Λ * (finrank ℤ X.Λ - 1)) *
      |(QuadraticLatticeForms.Bm X (RealPlaceEmbeddings.zb X)).det| / (ε ^ 2) ^ (finrank ℤ X.Λ - 1) with hB_def
  have hC : 0 ≤ HermitianPsiBounds.Cinv X := HermitianPsiBounds.Cinv_nonneg (X := X)
  have hD : (0:ℝ) ≤ ∑ σ : E →+* ℂ, ‖σ (X.den : E)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set D : ℝ := ∑ σ : E →+* ℂ, ‖σ (X.den : E)‖ with hD_def
  have hR : 0 ≤ D * ((B + B) * HermitianPsiBounds.Cinv X) := mul_nonneg hD (mul_nonneg (add_nonneg hB0 hB0) hC)
  set R : ℝ := D * ((B + B) * HermitianPsiBounds.Cinv X) with hR_def
  have hW : (0:ℝ) ≤ ∑ k : Free.ChooseBasisIndex ℤ (𝓞 E), ∑ τ : X.Ψ,
      ‖τ.1 ((RingOfIntegers.basis E k : 𝓞 E) : E)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  set W : ℝ := ∑ k : Free.ChooseBasisIndex ℤ (𝓞 E), ∑ τ : X.Ψ,
      ‖τ.1 ((RingOfIntegers.basis E k : 𝓞 E) : E)‖ ^ 2 with hW_def
  set T : ℝ := 9 ^ (finrank ℤ X.Λ) * (W * B) / ε ^ 2 with hT_def
  have hfin := FiniteTranslateSets.TS_finite (X := X) (ι := Fin (finrank ℤ X.Λ)) R T hR

  obtain ⟨rep, hrep⟩ : ∃ rep : _ → Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ,
      ∀ t ∈ FiniteTranslateSets.TS X (ι := Fin (finrank ℤ X.Λ)) R T, HermitianLatticeMaps.ty X (rep t) = t := by
    refine ⟨fun t => if h : ∃ f : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ, HermitianLatticeMaps.ty X f = t
      then h.choose else RealPlaceEmbeddings.zb X, fun t ht => ?_⟩
    have h : ∃ f : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ, HermitianLatticeMaps.ty X f = t := by
      simp only [FiniteTranslateSets.TS, Set.mem_setOf_eq] at ht
      obtain ⟨f, -, hf⟩ := ht
      exact ⟨f, hf⟩
    simp only [dif_pos h]
    exact h.choose_spec
  obtain ⟨S, hS⟩ := X.Γ_index
  let q := fun t (s : GL (Fin r) E) (k : Fin r) (i : Fin (finrank ℤ X.Λ)) =>
    (RealPlaceEmbeddings.qb X (rep t)).repr ((s : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single k 1) i
  set Q : ℝ := ∑ t ∈ hfin.toFinset, ∑ s ∈ S, ∑ k : Fin r, ∑ i : Fin (finrank ℤ X.Λ),
      ‖((q t s k i : ℚ) : ℂ)‖ with hQ_def
  have hG0 : (0:ℝ) ≤ ∑ τ : X.Ψ, ∑ k : Fin r, ∑ a : Fin r, ‖(X.Gm.map τ.1)⁻¹ k a‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      norm_nonneg _
  set G0 : ℝ := ∑ τ : X.Ψ, ∑ k : Fin r, ∑ a : Fin r, ‖(X.Gm.map τ.1)⁻¹ k a‖ with hG0_def
  refine ⟨CompactEntryBounds.Kset X (∑ _k : Fin r, G0 * (Q * (1 + B * HermitianPsiBounds.Cinv X))),
    CompactEntryBounds.Kset_compact (X := X) _, CompactEntryBounds.Kset_sub (X := X) _, ?_⟩
  intro x hx hl
  obtain ⟨b, hb, hnf⟩ := MajorantNormalForms.exists_normal_frame (X := X) hx
  have hy : IntegralBasisReduction.IsNormal X (mat (rmul x b)) := by
    unfold IntegralBasisReduction.IsNormal
    intro τ
    exact ⟨CompactEntryBounds.det_ne_of_gram (X := X) (hnf τ).1, (hnf τ).1⟩
  have hmin : ∀ v ∈ X.Λ, v ≠ 0 → ε ^ 2 ≤ QuadraticLatticeForms.Qy X (mat (rmul x b)) v := fun v hv hv0 =>
    HermitianPsiBounds.sq_le_Qy_of_le_firstMinimum (X := X) (x := x) (y := mat (rmul x b)) (fun τ u => (hnf τ).2 u) hε hl hv hv0
  obtain ⟨f, hfB, hfZ⟩ := IntegralBasisReduction.reduce (X := X) hy hm hmin

  have hmem : HermitianLatticeMaps.ty X f ∈ FiniteTranslateSets.TS X (ι := Fin (finrank ℤ X.Λ)) R T := by
    simp only [FiniteTranslateSets.TS, FiniteTranslateSets.Sh, FiniteTranslateSets.Sz, Set.mem_setOf_eq]
    refine ⟨f, ⟨fun i j => ?_, fun k i j => ?_⟩, rfl⟩
    · refine ⟨⟨(X.den : E) * herm X.Gm (f i : Fin r → E) (f j : Fin r → E),
        X.Λ_int _ (f i).2 _ (f j).2⟩, rfl, fun σ => ?_⟩
      show ‖σ ((X.den : E) * herm X.Gm (f i : Fin r → E) (f j : Fin r → E))‖ ≤ R
      rw [map_mul, norm_mul]
      have h1 : ‖σ (X.den : E)‖ ≤ D :=
        Finset.single_le_sum (f := fun σ : E →+* ℂ => ‖σ (X.den : E)‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)
      have h2 := HermitianPsiBounds.herm_bound (X := X) hy σ (f i : Fin r → E) (f j : Fin r → E)
      have h3 : (QuadraticLatticeForms.Qy X (mat (rmul x b)) (f i : Fin r → E) +
          QuadraticLatticeForms.Qy X (mat (rmul x b)) (f j : Fin r → E)) * HermitianPsiBounds.Cinv X ≤
          (B + B) * HermitianPsiBounds.Cinv X :=
        mul_le_mul_of_nonneg_right (add_le_add (hfB i) (hfB j)) hC
      exact mul_le_mul h1 (h2.trans h3) (norm_nonneg _) hD
    · show (((f.repr (RingOfIntegers.basis E k • f i) j : ℤ) : ℝ)) ^ 2 ≤ T
      have h2 : QuadraticLatticeForms.Qy X (mat (rmul x b))
          ((RingOfIntegers.basis E k • f i : X.Λ) : Fin r → E) ≤ W * B := by
        rw [HermitianLatticeMaps.smul_coe (X := X)]
        refine (HermitianPsiBounds.Qy_smul (X := X) _ _ _).trans
          (mul_le_mul ?_ (hfB i) (QuadraticLatticeForms.Qy_nonneg (X := X) _ _) hW)
        exact Finset.single_le_sum (f := fun k : Free.ChooseBasisIndex ℤ (𝓞 E) =>
            ∑ τ : X.Ψ, ‖τ.1 ((RingOfIntegers.basis E k : 𝓞 E) : E)‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ k)
      calc _ ≤ _ := hfZ _ j
        _ ≤ 9 ^ (finrank ℤ X.Λ) * (W * B) / ε ^ 2 := by gcongr
  have hts : HermitianLatticeMaps.ty X (rep (HermitianLatticeMaps.ty X f)) = HermitianLatticeMaps.ty X f := hrep _ hmem
  obtain ⟨γ, hγU, -, hγinv⟩ :=
    HermitianLatticeMaps.exists_gl (X := X) (f := f) (f' := rep (HermitianLatticeMaps.ty X f)) hts.symm
  obtain ⟨s, hsS, hsΓ⟩ := hS γ hγU
  refine ⟨s⁻¹ * γ, hsΓ, b, hb, ?_⟩
  have hgU := X.Γ_stab _ hsΓ
  simp only [CompactEntryBounds.Kset, Set.mem_setOf_eq]
  intro τ
  have hgram : gram τ.1 X.Gm (((s⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      mat (rmul x b) τ) = diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) := by
    rw [CompactEntryBounds.gram_stab (X := X) hgU.1]
    exact (hnf τ).1
  refine ⟨hgram, fun a c => ?_⟩
  show ‖(((s⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
    mat (rmul x b) τ) a c‖ ≤ _
  have hdet := CompactEntryBounds.det_ne_of_gram (X := X) hgram
  refine (CompactEntryBounds.entry_bound (X := X) hdet hgram a c).trans (Finset.sum_le_sum fun k _ => ?_)
  refine mul_le_mul ?_ ?_ (norm_nonneg _) hG0
  · have e1 := Finset.single_le_sum (f := fun a' : Fin r => ‖(X.Gm.map τ.1)⁻¹ k a'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
    have e2 := Finset.single_le_sum
      (f := fun k' : Fin r => ∑ a' : Fin r, ‖(X.Gm.map τ.1)⁻¹ k' a'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    have e3 := Finset.single_le_sum
      (f := fun τ' : X.Ψ => ∑ k' : Fin r, ∑ a' : Fin r, ‖(X.Gm.map τ'.1)⁻¹ k' a'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ τ)
    exact e1.trans (e2.trans e3)
  · have hemb : Data.emb τ.1 (Pi.single k (1:E)) = Pi.single k 1 := by
      funext a'
      by_cases h : a' = k
      · subst h; simp [Data.emb]
      · simp [Data.emb, h]
    have hcol : ((((s⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
        mat (rmul x b) τ)⁻¹) c k =
        ((((s⁻¹ * γ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
        mat (rmul x b) τ)⁻¹ *ᵥ Data.emb τ.1 (Pi.single k 1)) c := by
      rw [hemb]
      first
        | (simp; done)
        | (simp [Matrix.mulVec, dotProduct, Pi.single_apply]; done)
        | (simp [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply]; done)
    rw [hcol, CompactEntryBounds.inv_lact]
    have hginv : (((s⁻¹ * γ)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ Pi.single k 1 =
        ∑ i, q (HermitianLatticeMaps.ty X f) s k i • (f i : Fin r → E) := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hγinv _
    rw [hginv]
    refine (CompactEntryBounds.comb_bound (X := X) (mat (rmul x b)) τ (q (HermitianLatticeMaps.ty X f) s k)
      (fun i => (f i : Fin r → E)) c).trans ?_
    have hterm : ∀ i, ‖((q (HermitianLatticeMaps.ty X f) s k i : ℚ) : ℂ)‖ *
        (1 + QuadraticLatticeForms.Qy X (mat (rmul x b)) (f i : Fin r → E) / X.c τ) ≤
        ‖((q (HermitianLatticeMaps.ty X f) s k i : ℚ) : ℂ)‖ * (1 + B * HermitianPsiBounds.Cinv X) := by
      intro i
      refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (norm_nonneg _)
      rw [div_eq_mul_one_div]
      exact mul_le_mul (hfB i) (HermitianPsiBounds.inv_c_le (X := X) τ)
        (le_of_lt (one_div_pos.mpr (QuadraticLatticeForms.c_pos (X := X) τ))) hB0
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (add_nonneg zero_le_one (mul_nonneg hB0 hC))
    have i1 := Finset.single_le_sum
      (f := fun k' : Fin r => ∑ i : Fin (finrank ℤ X.Λ), ‖((q (HermitianLatticeMaps.ty X f) s k' i : ℚ) : ℂ)‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    have i2 := Finset.single_le_sum
      (f := fun s' : GL (Fin r) E => ∑ k' : Fin r, ∑ i : Fin (finrank ℤ X.Λ),
        ‖((q (HermitianLatticeMaps.ty X f) s' k' i : ℚ) : ℂ)‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) hsS
    have i3 := Finset.single_le_sum
      (f := fun t' => ∑ s' ∈ S, ∑ k' : Fin r, ∑ i : Fin (finrank ℤ X.Λ),
        ‖((q t' s' k' i : ℚ) : ℂ)‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (hfin.mem_toFinset.mpr hmem)
    exact i1.trans (i2.trans i3)

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Matrix

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem orthonormalChartNormControl_holds : OrthonormalChartNormControl (E := E) := by
  intro r X x hx ho ρ hρ0 hρ1
  refine ⟨fun Z hZ => ⟨OrthonormalChartBounds.xZ_mem_dom (X := X) hx ho (lt_of_le_of_lt hZ (by linarith)),
    fun la w hw => OrthonormalChartBounds.nfac_xZ (X := X) hx ho hρ0 hρ1 hZ la w hw,
    fun τ v => OrthonormalChartBounds.maj_xZ (X := X) hx ho hρ0 hρ1 hZ τ v⟩, ?_⟩
  intro G hG

  have hd : Differentiable ℂ (fun Z : X.Coord => X.xZ x Z) := by
    refine differentiable_pi.mpr fun τ => ?_
    refine differentiable_pi.mpr fun a => ?_
    refine differentiable_pi.mpr fun b => ?_
    simp only [Data.xZ, Matrix.mul_apply, Data.lowBlock, Matrix.of_apply]
    have hsum : ∀ {f : Fin r → X.Coord → ℂ}, (∀ j, Differentiable ℂ (f j)) →
        Differentiable ℂ (fun Z => ∑ j, f j Z) := by
      intro f hf
      first
        | exact Differentiable.fun_sum fun j _ => hf j
        | simpa [Finset.sum_fn] using Differentiable.sum (u := Finset.univ) (fun j _ => hf j)
        | fun_prop
    refine hsum fun k => ?_
    refine Differentiable.const_mul ?_ _
    refine (differentiable_const _).add ?_
    by_cases h : X.p0 ≤ (k : ℕ) ∧ (b : ℕ) < X.p0
    · simp only [dif_pos h]
      first
        | fun_prop
        | exact (differentiable_pi.mp ((differentiable_pi.mp
            ((differentiable_pi.mp differentiable_id) τ)) _)) _
    · simp only [dif_neg h]
      exact differentiable_const _
  refine hG.comp hd.differentiableOn ?_
  intro Z hZ
  exact OrthonormalChartBounds.xZ_mem_dom (X := X) hx ho (lt_of_lt_of_le hZ (by linarith))

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem nonvanishing_coefficient_positivity : NonvanishingCoefficientPositivity (E := E) := CoefficientPositivity.nonvanishing_coefficient_positivity_of unipotent_lattice_lift fourier_coefficients_holds

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex Metric

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem nonvanishingNearHalfMax_holds : NonvanishingNearHalfMax (E := E) := by
  unfold NonvanishingNearHalfMax
  intro r X la P z0 x0 w hSec hz0 hx0o ⟨b, hb, hx0⟩ hmax hpos hw hw1 hr Z hZ hPZ
  have hx0d : x0 ∈ X.dom := by rw [hx0]; exact OrthogonalFrameDomain.rmul_mem_dom (X := X) hz0 hb
  have hpx : X.pnorm la P x0 = X.pnorm la P z0 := by
    rw [hx0]; exact FrameDegreeData.pnorm_rmul (X := X) la P hSec.2.1 z0 hz0 b hb
  have hpn : ∀ y, X.pnorm la P y = ‖P y‖ * X.nfac la y := fun y => rfl
  have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.mpr hr
  have hw0 : w ≠ 0 := by positivity
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  have hwr : 0 < w * r := by nlinarith
  have hwr1 : 1 ≤ w * r := by nlinarith
  have hsq : Real.sqrt (w * r) ^ 2 = w * r := Real.sq_sqrt hwr.le
  have hs1 : 1 ≤ Real.sqrt (w * r) := by nlinarith [Real.sqrt_nonneg (w * r)]
  set ρ := frameRadius w r with hρdef
  have hρpos : 0 < ρ := by rw [hρdef, frameRadius]; positivity
  have hρle : ρ ≤ 1 / 10 := by
    rw [hρdef, frameRadius]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hρsq : 4 * w * r * ρ ^ 2 = 1 / 25 := by
    rw [hρdef, frameRadius, div_pow, mul_pow, hsq]
    field_simp
    ring
  have hM0 : 0 < ‖P x0‖ := by
    have h1 : 0 < X.pnorm la P x0 := hpx ▸ hpos
    rw [hpn] at h1
    rcases (norm_nonneg (P x0)).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at h1
      exact absurd h1 (lt_irrefl 0)
  have hzt : ∀ t : ℂ, ‖t‖ < 5 → X.zN (t • Z) ≤ ρ := fun t ht =>
    (OrthogonalFrameDomain.zN_smul_le (X := X) t Z).trans (by nlinarith [OrthogonalFrameDomain.zN_nonneg (X := X) Z, norm_nonneg t])
  have hdom : ∀ t : ℂ, ‖t‖ < 5 → X.xZ x0 (t • Z) ∈ X.dom := fun t ht =>
    OrthonormalChartBounds.xZ_mem_dom (X := X) hx0d hx0o (lt_of_le_of_lt (hzt t ht) (by linarith))
  have hbound : ∀ t : ℂ, ‖t‖ < 5 → ‖P (X.xZ x0 (t • Z))‖ < 3 * ‖P x0‖ := by
    intro t ht
    have hyd := hdom t ht
    have hny := BoundedSectionAlgebra.nfac_pos (X := X) hyd la
    have hnx := BoundedSectionAlgebra.nfac_pos (X := X) hx0d la
    have hlog := OrthonormalChartBounds.nfac_xZ (X := X) hx0d hx0o hρpos hρle (hzt t ht) la w hw
    have hz2 : 4 * w * r * X.zN (t • Z) ^ 2 ≤ 1 / 25 := by
      rw [← hρsq]
      have hwr4 : 0 ≤ 4 * w * r := by nlinarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (OrthogonalFrameDomain.zN_nonneg (X := X) _) (hzt t ht) 2) hwr4
    have hlow : Real.log (X.nfac la x0) - 1 / 25 ≤ Real.log (X.nfac la (X.xZ x0 (t • Z))) := by
      have := (abs_le.mp (hlog.trans hz2)).1
      linarith
    have hexp : X.nfac la x0 * Real.exp (-(1 / 25)) ≤ X.nfac la (X.xZ x0 (t • Z)) := by
      rw [← Real.exp_log hnx, ← Real.exp_log hny, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hpy : X.pnorm la P (X.xZ x0 (t • Z)) ≤ 2 * X.pnorm la P x0 := by
      rw [hpx]; exact hmax _ hyd
    rw [hpn, hpn] at hpy
    have h1 : ‖P (X.xZ x0 (t • Z))‖ * (X.nfac la x0 * Real.exp (-(1 / 25))) ≤
        2 * (‖P x0‖ * X.nfac la x0) :=
      (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)).trans hpy
    have h2 : ‖P (X.xZ x0 (t • Z))‖ * Real.exp (-(1 / 25)) ≤ 2 * ‖P x0‖ := by
      have h3 : (‖P (X.xZ x0 (t • Z))‖ * Real.exp (-(1 / 25))) * X.nfac la x0 ≤
          (2 * ‖P x0‖) * X.nfac la x0 := by nlinarith
      exact le_of_mul_le_mul_right h3 hnx
    have hE : Real.exp (-(1 / 25)) * Real.exp (1 / 25) = 1 := by
      rw [← Real.exp_add]; simp
    have h4 : ‖P (X.xZ x0 (t • Z))‖ ≤ 2 * ‖P x0‖ * Real.exp (1 / 25) := by
      calc ‖P (X.xZ x0 (t • Z))‖
          = ‖P (X.xZ x0 (t • Z))‖ * Real.exp (-(1 / 25)) * Real.exp (1 / 25) := by
            rw [mul_assoc, hE, mul_one]
        _ ≤ 2 * ‖P x0‖ * Real.exp (1 / 25) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    have he := OrthogonalFrameDomain.exp_small
    nlinarith [mul_lt_mul_of_pos_left he hM0]
  have h5 : ∀ s ∈ Metric.ball (1 : ℂ) 4, ‖s‖ < 5 := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm] at hs
    calc ‖s‖ = ‖(s - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ < 5 := by rw [norm_one]; linarith
  set g : ℂ → ℂ := fun t => P (X.xZ x0 (t • Z)) with hg
  have hg1 : g 1 = 0 := by simp only [hg, one_smul]; exact hPZ
  have hg0 : g 0 = P x0 := by simp only [hg, zero_smul, (OrthogonalFrameDomain.xZ_zero (X := X))]
  have hgd : DifferentiableOn ℂ g (Metric.ball 1 4) := by
    intro t ht
    have hin : DifferentiableAt ℂ (fun s : ℂ => X.xZ x0 (s • Z)) t :=
      (OrthogonalFrameDomain.xZ_diff (X := X) x0).differentiableAt.comp t (differentiableAt_id.smul_const Z)
    exact (hSec.1 _ (hdom t (h5 t ht))).comp t hin.differentiableWithinAt
      (fun s hs => hdom s (h5 s hs))
  have hmaps : Set.MapsTo g (Metric.ball 1 4) (Metric.closedBall (g 1) (3 * ‖P x0‖)) := by
    intro s hs
    rw [Metric.mem_closedBall, dist_eq_norm, hg1, sub_zero]
    exact (hbound s (h5 s hs)).le
  have hd : dist (0 : ℂ) 1 = 1 := by simp [dist_eq_norm]
  have h0 : (0 : ℂ) ∈ Metric.ball (1 : ℂ) 4 := by rw [Metric.mem_ball, hd]; norm_num
  have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hgd hmaps h0
  rw [hg0, hg1, dist_zero_right, hd, mul_one] at hS
  linarith

end ReciprocityTheory.ChartRestriction.G.FD
end

section

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem coefficientConvolution_holds : CoefficientConvolution (E := E) :=
  PeriodLatticeMembership.coefficientConvolution_of_subCoefficients (fun r X la P hP ξ hξ x hx ω hωp hωi k ν hk =>
    SublatticeCoefficients.subCoeff X la P hP ξ hξ x hx ω hωp hωi k ν hk)

end ReciprocityTheory.ChartRestriction.G.FD
end
