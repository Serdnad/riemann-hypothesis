module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle047
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle048
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle045
public import Formalism.LocalToGlobal.ProjectiveLattices.GenericSectionMinimumIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle034
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle014
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle049
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.LocalUnitReduction.IsUnitMkOfForallPrime
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle033
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle031
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
public import Formalism.LocalToGlobal.ProjectiveLattices.CurveLoc
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle040
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CurveRecord

theorem ev_ne_zero_of_nonZeroComp {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)
    {wF wL : WeightFamilies.Wt D j} (g0 : B.Cusp j wF) (hg : X.NonZeroComp wF g0) (Z : ι) (g : B.Cusp j wL)
    (h1 : gF Z (X.inc wL g) ≠ 0) (h2 : ∀ Z', Z' ≠ Z → gF Z' (X.inc wL g) = 0) : gF Z (X.inc wF g0) ≠ 0 := by
  intro h0
  obtain ⟨H, hH⟩ := X.inc_mul wF wL g0 g
  have hz : H = 0 := by
    refine hinj _ H fun Z' => ?_
    rw [← hH, map_mul]
    by_cases e : Z' = Z
    · subst e
      rw [h0, zero_mul]
    · rw [h2 Z' e, mul_zero]
  have hg0 : g = 0 := hg wL g (by rw [hH, hz, map_zero])
  exact h1 (by rw [hg0, map_zero, map_zero])

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)


include hT in


theorem evC_ne_zero (hV : GenValInjSt h j hG) (hC : CompSplitSt h j hG) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BigAt h j hj hG G) (g0 : (recB h.toLawsCore).Cusp j wF)
    (hg : (recPlus h j hj).NonZeroComp wF g0) (Z : Comp (T.Q.Xo j) T.Q.c) :
    evC hG Z ((g0 : (recB h.toLawsCore).Cusp j wF) : T.R j) ≠ 0 := by
  obtain ⟨k, hk, -⟩ := hB.2 Z
  obtain ⟨g, h1, h2⟩ := split_of h j hj hG hT hC G Z k
  have := ev_ne_zero_of_nonZeroComp (recPlus h j hj) (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG hT Z)
    (fun u F hF => hV u F fun Z => (formsEvR_inc h j hj hG hT Z u F).symm.trans (hF Z)) g0 hg Z g
    (fun h0 => hk ((formsEvR_inc h j hj hG hT Z wL (G.w k)).symm.trans (h1.symm.trans h0))) h2
  exact fun h0 => this ((formsEvR_inc h j hj hG hT Z wF g0).trans h0)

end Inst


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem curveInst : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG), GenValInjSt h j hG → CompSplitSt h j hG → (∀ (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF), BigAt h j hj hG G → BIRSt h j hj hG G) → CurveInstSt h j hj := by
  intro D T h j hj hG hT hV hC hB
  haveI : Finite (Comp (T.Q.Xo j) T.Q.c) := CompFin.finite_comp _ _
  letI : Fintype (Comp (T.Q.Xo j) T.Q.c) := Fintype.ofFinite _
  obtain ⟨hfg, htr⟩ := GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q h.pins.2.2.2 j hj
  have hQ := countQAtSt_holds h j hj hG hT
  have hinj : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ f : ↥(Frac0 (recPlus h j hj) la G.w), (∀ Z, phiI h j hj hG hT la G Z f = 0) → f = 0 :=
    fun ka wL wF G S g0 la _ f hf => curveInj h j hj hG hT hV G la f hf
  have hone := hone_of h j hj hG hT hC
  have hloc : ∀ ka wL wF G S g0 la, CurveHyp h j hj hG ka wL wF G S g0 →
      ∀ Z (r : RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w),
        ∃ a p : ↥(Frac0 (recPlus h j hj) la G.w),
          (∀ Q : Ideal ↥(Frac0 (recPlus h j hj) la G.w), Q.IsPrime → Jid (recPlus h j hj) la G.w ≤ Q →
            RingHom.ker (phiI h j hj hG hT la G Z) ≤ Q → p ∉ Q) ∧
          phiI h j hj hG hT la G Z p * r = phiI h j hj hG hT la G Z a := by
    intro ka wL wF G S g0 la hH Z r
    exact CurveLoc.loc_of_bir (recPlus h j hj) la G.N G.w (formsEvR j hG hT Z)
      (birAt_of h j hj hG hT G (hB ka wL wF G hH.2.1) Z) (hQ ka wL wF G S g0 la hH Z) r
  have hS1 := finite_reduced_section h j hj hG hT hfg htr
  refine curveInst_of h j hj hG hT hinj hone hloc hS1 ?_ ?_
  · intro ka wL wF G S g0 la hH e w' θ hw hθ
    have h1 := LocalUnitReduction.finRed (Kp (recPlus h j hj) la G.N) ↥(Frac0 (recPlus h j hj) la G.w)
      (Jid (recPlus h j hj) la G.w) (Comp (T.Q.Xo j) T.Q.c)
      (fun Z => RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
      (fun Z => phiI h j hj hG hT la G Z) (hinj _ _ _ G S g0 la hH) (hone _ _ _ G S g0 la hH)
      (hloc _ _ _ G S g0 la hH) (hS1 _ _ _ G S g0 la hH)
    exact unit_ideal_cusp_form_record h j hj hG hT G la g0 θ hw (hinj _ _ _ G S g0 la hH) (hone _ _ _ G S g0 la hH)
      (hloc _ _ _ G S g0 la hH) h1.1 (evC_ne_zero h j hj hG hT hV hC G hH.2.1 g0 hH.2.2.2) hθ
  · intro ka wL wF G S g0 la hH
    exact nonzero_divisor_cusp_form_record h j hj hG hT G la g0 (hinj _ _ _ G S g0 la hH)
      (evC_ne_zero h j hj hG hT hV hC G hH.2.1 g0 hH.2.2.2)

end GlobalTheory.CurveRecord
end

section




noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PrimeData

section General

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem ev_ne_zero_of_nonZeroComp (X : PJ D B P j) {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)]
    [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
    (hinj : ∀ (w : WeightFamilies.Wt D j) (g : B.Cusp j w), (∀ Z, gF Z (X.inc w g) = 0) → g = 0)
    {u : WeightFamilies.Wt D j} {F : B.Cusp j u} (hF : X.NonZeroComp u F) (Z : ι) {w : WeightFamilies.Wt D j} (g : B.Cusp j w)
    (hg : gF Z (X.inc w g) ≠ 0) (hg' : ∀ Z', Z' ≠ Z → gF Z' (X.inc w g) = 0) : gF Z (X.inc u F) ≠ 0 := by
  intro h0
  obtain ⟨H, hH⟩ := X.inc_mul u w F g
  have hH0 : H = 0 := by
    refine hinj _ H fun Z' => ?_
    rw [← hH, map_mul]
    by_cases hZ : Z' = Z
    · subst hZ
      rw [h0, zero_mul]
    · rw [hg' Z' hZ, mul_zero]
  rw [hH0, map_zero] at hH
  have := hF w g hH
  rw [this, map_zero, map_zero] at hg
  exact hg rfl

theorem ne_zero_of_nval_eq {T T' : CDVR} {e : ℕ} {x : T.Fr} {x' : T'.Fr} (hx : x ≠ 0)
    (h : nval T.V e x = nval T'.V e x') : x' ≠ 0 := by
  rintro rfl
  rw [nval_zero, nval_of_ne hx] at h
  exact EReal.coe_ne_top _ h

variable {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j}

theorem finiteDimensional_of_model {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
    {g0 : B.Cusp j wF} (C : CurveModel G la g0) :
    FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := by
  have : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥C.A' ⧸ C.JA) := C.fin
  exact LinearEquiv.finiteDimensional C.quotEquiv.toLinearEquiv

theorem isReduced_of_model {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}
    {g0 : B.Cusp j wF} (C : CurveModel G la g0) : IsReduced (OsK (xplus X E hM) la G.w) := by
  have : IsReduced (↥C.A' ⧸ C.JA) := C.red
  exact isReduced_of_injective C.quotEquiv.symm.toRingHom C.quotEquiv.symm.injective

end General

section Inst

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
  (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)


include hT in
theorem nzAt_of_nonZeroComp (hV : GenValInjSt h j hG) (hC : CompSplitSt h j hG) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (hB : BigAt h j hj hG G) {u : WeightFamilies.Wt D j}
    (F : (recB h.toLawsCore).Cusp j u) (hF : (recPlus h j hj).NonZeroComp u F) : NZAt hG (F : T.R j) := by
  intro Z
  obtain ⟨k, hk, -⟩ := hB.2 Z
  obtain ⟨g, e1, e2⟩ := hC Z wL (G.w k)
  have := ev_ne_zero_of_nonZeroComp (recPlus h j hj) (fun Z => Om Z) (fun Z => formsEvR j hG hT Z)
    (fun w g hg => hV w g fun Z => (formsEvR_inc h j hj hG hT Z w g).symm.trans (hg Z)) hF Z g
    (fun h0 => hk (e1.symm.trans ((formsEvR_inc h j hj hG hT Z wL g).symm.trans h0)))
    (fun Z' hZ' => (formsEvR_inc h j hj hG hT Z' wL g).trans (e2 Z' hZ'))
  exact fun h0 => this ((formsEvR_inc h j hj hG hT Z u F).trans h0)

theorem fromW_ne_zero {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO))
    (hU : IsUnif (OsK (recPlus h j hj) la G.w) (unifO (recPlus h j hj) la G.N)) [∀ ζ : PtsG G la, IsDVRAt ζ]
    (hR : RealPtNZSt h j hj hG G la hU) (ζ : PtsG G la) :
    ∃ (y : (extAll h j hj).Pt' la) (hw : FromW (E := extAll h j hj) (hM := intAtExt_extAll h j hj) ζ y),
      ∀ (w : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j w), NZAt hG (F : T.R j) →
        hw.ev (emb (recPlus h j hj) la G.N ((recPJ h j hj).inc w F)) ≠ 0 := by
  obtain ⟨y, Tc, ι, hl, hunr, ev, hu, hv, hdeg, hnz⟩ := hR ζ
  obtain ⟨hw⟩ := @fromW_of D (recB h.toLawsCore) T.G.P j (recPJ h j hj) (extAll h j hj) (intAtExt_extAll h j hj)
    ka wL wF G la ζ (‹∀ ζ : PtsG G la, IsDVRAt ζ› ζ) y hU Tc ι hl hunr ev hu hv hdeg
  exact ⟨y, hw, fun w F hF => ne_zero_of_nval_eq (hnz w F hF) ((hv w F).symm.trans (hw.hv w F))⟩

end Inst

end GlobalTheory.PrimeData
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Reg




theorem section_ratios_integral : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (S : Scal (recB h.toLawsCore)) (g0 : (recB h.toLawsCore).Cusp j wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)), CurveHyp h j hj hG ka wL wF G S g0 → GenValInjSt h j hG → CompSplitSt h j hG → BIRSt h j hj hG G → Nonempty (CurveModel (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la g0) → GenericSectionMinimumIntegral (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la := by
  intro D T h j hj hG _ ka wL wF G S g0 la _ _ _ _ _
  exact Formalism.L2.Pj.GenericSectionMinimum.generic_section_minimum_integral (E := extAll h j hj) (hM := intAtExt_extAll h j hj) G la

end GlobalTheory.Reg
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem _root_.GlobalTheory.T.exists_integral_smooth_chart_frame_moduli : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ p : Xo.XF c, ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra c.F A) (j : Sp A ⟶ Xo.XF c) (y : FrPt Xo c A), IsOpenImmersion j ∧ p ∈ Set.range j ∧ j ≫ pullback.snd _ _ = spMap (algebraMap c.F A) ∧ Algebra.Smooth c.F A ∧ y.x = j ≫ pullback.fst _ _ := by
  first | exact @GlobalTheory.LocalFrame.exists_integral_chart_frame | exact GlobalTheory.LocalFrame.exists_integral_chart_frame | (intros; apply GlobalTheory.LocalFrame.exists_integral_chart_frame <;> assumption)
end
