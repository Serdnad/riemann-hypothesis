import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsChowFormIntLineZero
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.WeightSectionsHeightEstimate
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.WeightSectionsCdvrEstimate
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace PositivityTheory.Xj7N.Inj

open GlobalTheory

section Generic

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem exists_rat_small (L : HermLB p) (s₀ : L.B.Sec) (hs₀ : genericPoint X ∈ nonzeroLocus s₀) (τ : ℕ) (t : ℝ) :
    ∃ R : (lbPow L.B τ).Sec → X.functionField, Function.Injective R ∧ ∀ h : X.functionField,
      (∀ (c : L.B.ι) (x : X) (hx : x ∈ L.B.U c), RegAt x (h * fnOf (L.B.U c) (gen_mem hx) (s₀.f c) ^ τ)) →
      (∀ (σ : k →+* ℂ) (y : CxPts p σ) (c : L.B.ι) (hy : y ∈ ptsIn p σ (L.B.U c)),
        RegAt (under y) (h * fnOf (L.B.U c) (gen_mem (mem_ptsIn.1 hy)) (s₀.f c) ^ τ) →
        ‖ratVal (h * fnOf (L.B.U c) (gen_mem (mem_ptsIn.1 hy)) (s₀.f c) ^ τ) y‖ ^ 2 *
          Real.exp (-((τ : ℝ) * (L.φ σ).φ c y)) ≤ Real.exp (2 * (τ : ℝ) * t)) →
      ∃ S ∈ ((L.shift (fun _ => t) (fun _ => rfl)).pow τ).smallSec, R S = h := by
  have hr := isRatSec_ratOfSec s₀ hs₀
  have hrτ := GlobalTheory.TrueGeo.SmallSec.isRatSec_pow hr τ
  have hPr := presents_divOfRatSec (L.pow τ).isLB hrτ
  refine ⟨hPr.rat, hPr.rat_injective, fun h hreg hb => ?_⟩
  have hsec : h ∈ (divOfRatSec (L.pow τ).isLB hrτ).sections := by
    refine CartierDiv.mem_sections.2 fun x => ?_
    obtain ⟨c, hc⟩ := exists_chart (L.pow τ).isLB x
    have hx : x ∈ L.B.U (c PUnit.unit) := Set.mem_iInter.1 hc PUnit.unit
    refine ⟨_, hPr.isEqn c x hc, ?_⟩
    rw [Units.val_pow_eq_pow_val, val_ratOfSec (gen_mem hx)]
    exact hreg _ x hx
  obtain ⟨S, hS⟩ := hPr.exists_rat_eq hsec
  refine ⟨S, fun σ y => ?_, hS⟩
  let Lτ := (L.shift (fun _ => t) (fun _ => rfl)).pow τ
  obtain ⟨c, hc⟩ := exists_chart Lτ.isLB (under y)
  have hy : y ∈ ptsIn p σ (Lτ.B.U c) := mem_ptsIn.2 hc
  have hy1 : y ∈ ptsIn p σ (L.B.U (c PUnit.unit)) := mem_ptsIn.2 (Set.mem_iInter.1 hc PUnit.unit)
  have hgen : genericPoint X ∈ Lτ.B.U c := gen_mem hc
  have e0 : fnOf (Lτ.B.U c) hgen ((S : Lτ.B.Sec).f c) =
      h * fnOf _ (gen_mem (mem_ptsIn.1 hy1)) (s₀.f (c PUnit.unit)) ^ τ := by
    have := hPr.rat_mul S c hgen
    rw [hS, Units.val_pow_eq_pow_val, val_ratOfSec (gen_mem (mem_ptsIn.1 hy1))] at this
    exact this.symm
  have e1 : ev p σ (Lτ.B.U c) ((S : Lτ.B.Sec).f c) y =
      ratVal (h * fnOf _ (gen_mem (mem_ptsIn.1 hy1)) (s₀.f (c PUnit.unit)) ^ τ) y := by
    rw [← e0]; exact (ratVal_fnOf hy hgen ((S : Lτ.B.Sec).f c)).symm
  have e2 : (Lτ.φ σ).φ c y = (τ : ℝ) * ((L.φ σ).φ (c PUnit.unit) y + 2 * t) := by
    have := Weight.zpow_φ ((L.φ σ).addFn fun _ => 2 * t) (τ : ℤ) c y
    exact this.trans (by push_cast; rfl)
  have hb' := hb σ y (c PUnit.unit) hy1 (hreg _ _ (mem_ptsIn.1 hy1))
  have hn := Weight.nsq_eq (Lτ.φ σ) (secVal_mem (p := p) (σ := σ) (S : Lτ.B.Sec)) hy
  show (Lτ.φ σ).nsq (secVal p σ (S : Lτ.B.Sec)) y ≤ 1
  refine hn.le.trans ?_
  have e4 : secVal p σ (S : Lτ.B.Sec) c y = ev p σ (Lτ.B.U c) ((S : Lτ.B.Sec).f c) y := by
    erw [secVal_apply]; rfl
  rw [e4, e1, e2]
  have e3 : Real.exp (-((τ : ℝ) * ((L.φ σ).φ (c PUnit.unit) y + 2 * t))) =
      Real.exp (-((τ : ℝ) * (L.φ σ).φ (c PUnit.unit) y)) * (Real.exp (2 * (τ : ℝ) * t))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_add]; ring_nf
  rw [e3, ← mul_assoc, mul_inv_le_iff₀ (Real.exp_pos _), one_mul]
  exact hb'

end Generic

theorem eq_zero_of_genVal' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
    {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) (h0 : genVal Z f = 0) : f = 0 := by
  refine secZ_eq_zero_of_genVal hf.1.1 fun Z' => ?_
  by_cases hZ : Z' = Z
  · rw [hZ, h0]
  · exact evC_eq_zero (GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ _ _).1 hZ hf.2

/-- A base-point-free model of a nonzero linear system has a section that is
nonzero both at the generic point of the model and under evaluation. -/
theorem exists_nonzero_section_at_generic_point
    {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω]
    {Nm : (K →+* ℂ) → V → ℝ} {W : Submodule (𝓞 K) V} {evaluation : V →ₗ[K] Ω}
    {d : ℕ} {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp (𝓞 K)} {L : HermLB p}
    {ψ : Ω →+* X.functionField} {s : W → L.B.Sec}
    (model : ImageModel.IsModelOf Nm W evaluation d p L ψ s)
    (spans : Submodule.span K (W : Set V) = ⊤) (nonzero : evaluation ≠ 0) :
    ∃ w : W, genericPoint X ∈ nonzeroLocus (s w) ∧ evaluation w ≠ 0 := by
  have nonzero_on_lattice : ∃ w : W, evaluation w ≠ 0 := by
    by_contra! zero_on_lattice
    apply nonzero
    apply LinearMap.ext
    intro v
    have hker : Submodule.span K (W : Set V) ≤ LinearMap.ker evaluation :=
      Submodule.span_le.2 fun w hw => zero_on_lattice ⟨w, hw⟩
    exact hker (spans.symm ▸ Submodule.mem_top)
  have point_mem : genericPoint X ∈ (⨆ w, nonzeroLocus (s w) : X.Opens) := by
    rw [model.bpf]
    trivial
  rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion] at point_mem
  obtain ⟨w, hw⟩ := point_mem
  refine ⟨w, hw, fun zero => ?_⟩
  obtain ⟨v, hv⟩ := nonzero_on_lattice
  obtain ⟨c, hc⟩ := exists_chart L.isLB (genericPoint X)
  apply mul_ne_zero ((map_ne_zero_iff ψ model.bij.1).2 hv) (fnOf_sec_ne_zero hw hc)
  simpa only [zero, map_zero, zero_mul] using model.ratio v w c hc

theorem genVal_injective_on_cusp {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {Z : Comp Xo c} {G : WTZ E} :
    Function.Injective (fun f : cuspOn U Z G => genVal Z (f : Rul Xo c)) := by
  intro f g h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_genVal' (Submodule.sub_mem _ f.2 g.2)
  rw [map_sub]
  exact sub_eq_zero.mpr h

/-- Injective evaluation bounds the cardinality of a family by that of any
other family attaining all of its evaluations. -/
theorem encard_le_of_evaluation_lifts {α β κ : Type*} {S : Set α} {T : Set β}
    {evalSource : α → κ} {evalTarget : β → κ} (source_inj : Set.InjOn evalSource S)
    (lifts : ∀ s ∈ S, ∃ t ∈ T, evalTarget t = evalSource s) : S.encard ≤ T.encard := by
  calc
    S.encard = (evalSource '' S).encard := source_inj.encard_image.symm
    _ ≤ (evalTarget '' T).encard := by
      refine Set.encard_le_encard ?_
      rintro _ ⟨s, hs, rfl⟩
      exact lifts s hs
    _ ≤ T.encard := Set.encard_image_le _ _

set_option maxHeartbeats 1000000 in

theorem injectivity_weight_sections_of (hK : Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → ∀ f ∈ smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t, ∀ w : latOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 → ∀ (σ : 𝓞 Y.d.c₂.F →+* ℂ) (y : GlobalTheory.CxPts p σ) (k : L.B.ι) (hy : y ∈ GlobalTheory.CxPts.ptsIn p σ (L.B.U k)), GlobalTheory.Cartier.RegAt (GlobalTheory.Cartier.under y) (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) → ‖GlobalTheory.Cartier.ratVal (ψ (genVal Z (f : Rul Y.d.Xo₂ Y.d.c₂)) * (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i) * fnOf (L.B.U k) (gen_mem (GlobalTheory.CxPts.mem_ptsIn.1 hy)) ((s w).f k) ^ (8 * i)) y‖ ^ 2 * Real.exp (-(((8 * i : ℕ) : ℝ) * (L.φ σ).φ k y)) ≤ Real.exp (2 * ((8 * i : ℕ) : ℝ) * t)) : Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t).encard ≤ ((L.shift (fun _ => t) (fun _ => rfl)).pow (8 * i)).smallSec.encard := by
  intro hP D T j Y e o hY hE Z u X _ p L ψ s t hGood hBir hNB hdg hM i hi
  obtain ⟨w, hw, hw0⟩ := exists_nonzero_section_at_generic_point hM hGood.2.2 hBir.1
  have hw0' : genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) : Rul Y.d.Xo₂ Y.d.c₂) ≠ 0 := hw0
  let denominator := (ψ (genVal Z ((w : cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) :
    Rul Y.d.Xo₂ Y.d.c₂)))⁻¹ ^ (8 * i)
  have denominator_ne_zero : denominator ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero ((map_ne_zero_iff ψ hM.bij.1).2 hw0'))
  obtain ⟨R, -, lift⟩ := exists_rat_small L (s w) hw (8 * i) t
  refine encard_le_of_evaluation_lifts (evalTarget := R)
    (((mul_left_injective₀ denominator_ne_zero).comp hM.bij.1).comp genVal_injective_on_cusp).injOn ?_
  intro f hf
  exact lift _ (ChowFormHeightComparison₂.weight_sections_cdvr_estimate hP D T j Y e o hY hE Z u X p L ψ s t hGood hBir hNB hdg hM i hi f hf w hw0'
      (ChowFormHeightComparison₂.weight_sections_height_estimate hP D T j Y e o hY hE Z u X p L ψ s t hGood hBir hNB hdg hM i hi f hf w hw0'))
      (hK hP D T j Y e o hY hE Z u X p L ψ s t hGood hBir hNB hdg hM i hi f hf w hw0')

end PositivityTheory.Xj7N.Inj

end
