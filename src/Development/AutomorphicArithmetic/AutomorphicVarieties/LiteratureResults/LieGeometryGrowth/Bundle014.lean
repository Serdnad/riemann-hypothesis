module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle133
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrBwd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrCochain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Pf.bddInt :
    UpperTheory.V.Lit.Geo.Pf.BddInt := by
  intro E _ _ _ a μ _ F hF ⟨C, hC⟩
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have h := GlobalTheory.CuspQuot.memL2_of_bound (μ := μ) hF.cont
    (GlobalTheory.CuspRep.CuspidalL2GL.leftInv_latticeGL hF.left hF.centre) hC
  exact ⟨h.2.integrable one_le_two, h⟩
end

section

open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem one_kills {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))
    (hm : m ∈ Submodule.span ℂ {x | ∃ φ v, IsLevelFn U Ξ φ ∧ x = φ ⊗ₜ[ℂ] v}) : smLie Ξ (oneL E a) m = 0 := by
  obtain ⟨r, hr⟩ := oneReal E a Ξ
  have hr' : Ξ.dmat (oneL E a) = (r : ℂ) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := hr
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, v, hφ, rfl⟩ := hx
    change (lie E a (oneL E a)).rTensor _ (φ ⊗ₜ[ℂ] v) + (Matrix.toLin' (Ξ.dmat (oneL E a))).lTensor _ (φ ⊗ₜ[ℂ] v) = 0
    rw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hφ.2.2 _ hr', hr', map_smul, Matrix.toLin'_one,
      LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.smul_tmul, ← TensorProduct.tmul_add, neg_smul, neg_add_cancel,
      TensorProduct.tmul_zero]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

private theorem d_basic {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ} (α : Co Ξ q) (hα : IsLev U Ξ α)
    (X : Fin (q + 1) → Herm E a) (i : Fin (q + 1)) (hX : (X i).1 = 1) : dCo (smLie Ξ) α X = 0 := by
  rw [dCo_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : i = j
  · subst hj
    have h := one_kills U Ξ _ (hα.val (i.removeNth X))
    have e : oneL E a = toL (X i).1 := by rw [hX]
    rw [e] at h
    rw [h, smul_zero]
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
    have hz : α (j.removeNth X) = 0 := hα.basic _ k (by rw [← hX, ← hk]; rfl)
    rw [hz, map_zero, smul_zero]

theorem UpperTheory.V.Lit.Geo.levGood :
    LevGood := by
  intro E _ _ _ a ho U Ξ q
  refine ⟨fun α hα => ?_, fun w hw => ?_⟩
  · have hv : ∀ X, LeftInv (α X) ∧ RightInv U (α X) := fun X => (levelVal E a U Ξ _).1 (hα.val X)
    obtain ⟨w, hw, h0⟩ := corrFwd E a U Ξ q α hα.equiv fun X => (hv X).2
    let w' : (geo ho U Ξ).Om q := ⟨w, fun s => ⟨corrSmooth E a U Ξ q _ w hw s, h0 s⟩⟩
    have hw' : Corr U Ξ α w'.1 := hw
    exact ⟨w', hw', (corrInv E a ho U Ξ q _ _ hw').1 fun X => (hv X).1, (corrBasic E a U Ξ q _ _ hw').1 hα.basic,
      (corrBasic E a U Ξ (q + 1) _ _ (corrD E a ho U Ξ q _ _ hw')).1 (d_basic U Ξ α hα)⟩
  · obtain ⟨α, hα⟩ := corrBwd E a ho U Ξ q w
    have b := (corrBasic E a U Ξ q _ _ hα).2 hw.basic
    have b' := (corrBasic E a U Ξ (q + 1) _ _ (corrD E a ho U Ξ q _ _ hα)).2 hw.dbasic
    obtain ⟨c1, c2⟩ := corrCochain E a U Ξ q _ _ hα
    exact ⟨α, hα, c1, b, fun X => (levelVal E a U Ξ _).2 ((corrInv E a ho U Ξ q _ _ hα).2 hw.inv X) (c2 X)
      (centralOf E a _ (smLie Ξ) q α b b' X)⟩
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.corrBd :
    CorrBd := by
  intro E _ _ _ a U Ξ C q
  obtain ⟨B, hB, hM⟩ := matBd E a Ξ C
  obtain ⟨r, hr⟩ := oneReal E a Ξ
  obtain ⟨T, hT⟩ := (retrFacts E a).2.2 C
  refine ⟨B * Real.exp (|r| * T) * B ^ q, by positivity, ?_⟩
  intro α w hα hw g y h x M hg h1 h2 hM0 hbd v
  obtain ⟨m1, -, m3⟩ := hM h h1 h2
  obtain ⟨t, ht, e⟩ := hT g h h1 h2
  have hcomm : infGL E a h * finGL E a x = finGL E a x * infGL E a h := by
    first | exact GlobalTheory.CuspRep.infGL_comm _ _ | exact TR.infGL_comm _ _
  rw [hg, mul_assoc, ← hcomm, ← mul_assoc, ← map_mul] at e
  set X : Fin q → Herm E a := fun i => hv.symm ((1 / 2 : ℝ) • sand h⁻¹ (v i)) with hX
  have hc := hw (y * h) x X
  have hv' : (fun i => (2 : ℝ) • sand (y * h) (hv (X i))) = fun i => sand y (v i) := by
    funext i
    simp only [hX, LinearEquiv.apply_symm_apply, map_smul, smul_smul]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel_right]
    norm_num
  have hcv := centreVal E a U Ξ r hr q α hα X 1 t
    (GroundTheory.Automorphic.CuspidalSpectrum.retractOne (g * infGL E a h) : KernelIndexFullLattice.G1 E a).1
  rw [map_one, one_mul] at hcv
  rw [hv', e, hcv] at hc
  rw [hc, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel_left]
  refine (m1 _).trans ?_
  rw [norm_smul]
  have hexp : ‖Complex.exp (-(r * t))‖ ≤ Real.exp (|r| * T) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.2 ?_
    have : (-((r : ℂ) * t)).re = -(r * t) := by simp
    rw [this]
    refine (neg_le_abs _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  have hp : ∏ i, ‖hv (X i)‖ ≤ B ^ q * ∏ i, ‖v i‖ := by
    have : B ^ q * ∏ i, ‖v i‖ = ∏ i, B * ‖v i‖ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [this]
    refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
    simp only [hX, LinearEquiv.apply_symm_apply]
    rw [norm_smul]
    have h3 := m3 (v i)
    have h4 := norm_nonneg (sand h⁻¹ (v i))
    have h5 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [h5]
    linarith
  have hb := (hbd X).trans (mul_le_mul_of_nonneg_left hp hM0)
  calc _ ≤ B * (Real.exp (|r| * T) * (M * (B ^ q * ∏ i, ‖v i‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hexp hb (norm_nonneg _) (Real.exp_pos _).le) hB
    _ = _ := by ring
end

section

open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr
open Set ContinuousAlternatingMap
open scoped ContDiff

private theorem extDeriv_smooth {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Y : Set V} (hY : IsOpen Y) {q : ℕ} {w : V → V [⋀^Fin q]→L[ℝ] F}
    (hw : ContDiffOn ℝ ∞ w Y) : ContDiffOn ℝ ∞ (extDeriv w) Y :=
  (alternatizeUncurryFinCLM ℝ V F).contDiff.comp_contDiffOn
    (hw.fderiv_of_isOpen hY (by simp))

private theorem pb_flow_zero {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (W : V → V) {q : ℕ} (w : V → V [⋀^Fin q]→L[ℝ] F) (p : V) :
    pb (flow W 0) w p = w p := by
  have h : flow W 0 = id := by
    funext x
    simp [flow]
  ext v
  simp [pb_apply, h]

private theorem homForm_of (hP : HomPt) (hS : HkSmooth) : HomForm := by
  intro V F _ _ _ _ _ _ Y hY W hW p hp
  have hWp : ContDiffAt ℝ ∞ W p := hW.1.contDiffAt (hY.mem_nhds hp)
  refine ⟨fun w hw => ?_, fun q w hw => ?_⟩
  · have hI := ((hS V F Y hY W hW 0 _ (extDeriv_smooth hY hw)).2.2.1 p hp).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) zero_le_one
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r => pb (flow W r) w p) (hk W t (extDeriv w) p) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      exact (hP V F W p t hWp).1 w (hw.contDiffAt (hY.mem_nhds (hW.2 p hp t ht)))
    have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hI
    rw [pb_flow_zero] at h3
    exact h3.symm
  · have hI := ((hS V F Y hY W hW (q + 1) _ (extDeriv_smooth hY hw)).2.2.1 p hp).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) zero_le_one
    obtain ⟨hU, hΦ, -, -⟩ := hS V F Y hY W hW q w hw
    obtain ⟨hc, hD⟩ := paramDeriv V _ p _ _ hU (fun t ht => ⟨hp, hW.2 p hp t ht⟩) hΦ
    dsimp only at hc hD
    have hJ := hc.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) zero_le_one
    have hJ' : IntervalIntegrable (fun t => alternatizeUncurryFinCLM ℝ V F (fderiv ℝ (fun x => hk W t w x) p))
        MeasureTheory.volume 0 1 :=
      ((alternatizeUncurryFinCLM ℝ V F).continuous.comp_continuousOn hc).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) zero_le_one
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r => pb (flow W r) w p)
        (alternatizeUncurryFinCLM ℝ V F (fderiv ℝ (fun x => hk W t w x) p) + hk W t (extDeriv w) p) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      exact (hP V F W p t hWp).2 q w (hw.contDiffAt (hY.mem_nhds (hW.2 p hp t ht)))
    have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hJ'.add hI)
    rw [pb_flow_zero, intervalIntegral.integral_add hJ' hI,
      (alternatizeUncurryFinCLM ℝ V F).intervalIntegral_comp_comm hJ, ← hD.fderiv] at h3
    exact h3.symm

theorem UpperTheory.V.Lit.Geo.homForm :
    HomForm :=
  homForm_of homPt hkSmooth
end

section

open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr

theorem UpperTheory.V.Lit.Geo.omEquiv :
    OmEquiv := by
  intro Γ V S _ _ _ _ d G W hW q γ
  have hρρ : ∀ x, G.ρ γ (G.ρ γ⁻¹ x) = x := fun x => by simpa using G.ρ_inv_apply γ⁻¹ x
  have hσ : ∀ s, G.σ γ (G.σ γ⁻¹ s) = s := fun s => by simp
  have hout : ∀ p, p ∉ G.Y → G.ρ γ⁻¹ p ∉ G.Y := fun p hp h => hp (by simpa [hρρ] using G.maps γ _ h)
  have heq : ∀ s, ∀ p ∈ G.Y, W s (G.ρ γ p) = G.ρ γ (W (G.σ γ⁻¹ s) p) := fun s p hp => by
    have := hW.equiv γ (G.σ γ⁻¹ s) p hp
    rwa [hσ] at this
  have hnat := fun s => pbNat V (Fin d → ℂ) G.Y G.isOpen (G.ρ γ) (mulVecL (G.ξ γ)) (W (G.σ γ⁻¹ s)) (W s)
    (hW.field _) (hW.field s) (G.maps γ) (heq s) q
  have hrel : ∀ (k : ℕ) (w : G.Om k) (s : S), ∀ p ∈ G.Y, ∀ v : Fin k → V,
      ((G.act k γ w).1 s (G.ρ γ p)) (fun i => G.ρ γ (v i)) = mulVecL (G.ξ γ) (w.1 (G.σ γ⁻¹ s) p v) := by
    intro k w s p hp v
    simp only [Geo.act_apply, mulVecL_apply, Geo.ρ_inv_apply]
  have hz : ∀ (k : ℕ) (w : G.Om k) (s : S) (p : V), p ∉ G.Y → w.1 s p = 0 :=
    fun k w s p hp => (w.2 s).2 p hp
  have hsm := fun (k : ℕ) (w : G.Om k) (s : S) => (w.2 s).1
  obtain ⟨hA, hB⟩ := omApply Γ V S d G W hW q
  refine ⟨fun w => ?_, fun w => ?_⟩
  · apply Subtype.ext
    funext s p
    ext v
    by_cases hp : p ∈ G.Y
    · have hp' := G.maps γ⁻¹ p hp
      rw [Geo.act_apply, hA w _ _ hp', hA (G.act q γ w) s p hp]
      have := (hnat s).1 (w.1 (G.σ γ⁻¹ s)) ((G.act q γ w).1 s) (hrel q w s) 1 ⟨zero_le_one, le_rfl⟩
        (G.ρ γ⁻¹ p) hp' (fun i => G.ρ γ⁻¹ (v i))
      simp only [hρρ] at this
      rw [← mulVecL_apply]
      exact congrFun this.symm _
    · rw [Geo.act_apply, hz q _ _ _ (hout p hp), hz q _ s p hp]
      simp
  · apply Subtype.ext
    funext s p
    ext v
    by_cases hp : p ∈ G.Y
    · have hp' := G.maps γ⁻¹ p hp
      rw [Geo.act_apply, hB w _ _ hp', hB (G.act (q + 1) γ w) s p hp]
      have := ((hnat s).2 (w.1 (G.σ γ⁻¹ s)) ((G.act (q + 1) γ w).1 s) (hrel (q + 1) w s)).2
        (hsm _ w _) (hsm _ _ s) (G.ρ γ⁻¹ p) hp' (fun i => G.ρ γ⁻¹ (v i))
      simp only [hρρ] at this
      rw [← mulVecL_apply]
      exact congrFun this.symm _
    · rw [Geo.act_apply, hz q _ _ _ (hout p hp), hz q _ s p hp]
      simp
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit UpperTheory.V.Lit.Dr
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo
open scoped TensorProduct

private theorem cont_ev {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) {Ξ : AlgRep E a}
    {m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)}
    (hm : m ∈ Submodule.span ℂ {x | ∃ φ v, IsLevelFn U Ξ φ ∧ x = φ ⊗ₜ[ℂ] v}) : Continuous (ev m) := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, v, hφ, rfl⟩ := hx
    let S : Subgroup (GL (Fin a) (Af E)) :=
      { carrier := {k | finRep E a k φ = φ}
        one_mem' := by simp
        mul_mem' := fun {x y} hx hy => by
          have hx' : finRep E a x φ = φ := hx
          have hy' : finRep E a y φ = φ := hy
          change finRep E a (x * y) φ = φ
          rw [map_mul, Module.End.mul_apply, hy', hx']
        inv_mem' := fun {x} hx => by
          have hx' : finRep E a x φ = φ := hx
          change finRep E a x⁻¹ φ = φ
          conv_lhs => rw [← hx']
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hS : IsOpen (S : Set (GL (Fin a) (Af E))) := Subgroup.isOpen_mono (H₁ := U) (fun u hu => hφ.2.1 u hu) hU
    exact (ContAut.continuous_of_isOpen_stab E a φ hS).smul continuous_const
  | zero => rw [map_zero]; exact continuous_const
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact hx.add hy
  | smul c x _ hx => rw [map_smul]; exact hx.const_smul c

theorem UpperTheory.V.Lit.Geo.bdCompact :
    BdCompact := by
  intro E _ _ _ a U hU Ξ q α hα R
  obtain ⟨T, B, hB, hT⟩ := bdBasis E a Ξ q
  obtain ⟨K, hK, hR⟩ := (qhtFacts E a).2.2.2 R
  have hb : ∀ X : Fin q → Herm E a, ∃ c : ℝ, ∀ g ∈ K, ‖ev (α X) (retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ c := fun X =>
    hK.exists_bound_of_continuousOn
      ((cont_ev hU (hα.val X)).comp (continuous_subtype_val.comp continuous_retractOne)).continuousOn
  choose c hc using hb
  refine ⟨B * ∑ X ∈ T, |c X|, by positivity, fun g hg => hT α g _ (by positivity) fun X hX => ?_⟩
  obtain ⟨γ, t, h⟩ := hR g hg
  have e := hc X _ h
  rw [(retrFacts E a).2.1, ((levelVal E a U Ξ _).1 (hα.val X)).1] at e
  exact (e.trans (le_abs_self _)).trans (Finset.single_le_sum (f := fun X => |c X|) (fun _ _ => abs_nonneg _) hX)
end

section

open UpperTheory.V.Lit.Geo NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

theorem UpperTheory.V.Lit.Geo.bdGrowth :
    BdGrowth := by
  intro E _ _ _ a Ξ q α
  obtain ⟨T, B, hB, hT⟩ := bdBasis E a Ξ q
  have hq := (qhtFacts E a).1
  have hr : ∀ g, qht (E := E) (a := a)
      (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1 = qht g := fun g => by
    obtain ⟨t, ht⟩ := (retrFacts E a).1 g
    have h := (qhtFacts E a).2.1 1 t g
    rw [map_one, one_mul] at h
    rw [ht, h]
  have hs : ∀ (C : _ → ℝ), ∀ X ∈ T, C X ≤ ∑ X ∈ T, |C X| := fun C X hX =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun X => |C X|) (fun _ _ => abs_nonneg _) hX)
  refine ⟨fun ⟨N, h⟩ => ?_, fun h N => ?_⟩
  · choose C hC using h
    have h0 : 0 ≤ ∑ X ∈ T, |C X| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨N, B * ∑ X ∈ T, |C X|, mul_nonneg hB h0, fun g => ?_⟩
    have q0 : 0 < qht g := one_pos.trans_le (hq g)
    rw [mul_assoc]
    refine hT α g _ (by positivity) fun X hX => (hC X _).trans ?_
    rw [hr]
    exact mul_le_mul_of_nonneg_right (hs C X hX) (by positivity)
  · choose C hC using fun X => h X N
    have h0 : 0 ≤ ∑ X ∈ T, |C X| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨B * ∑ X ∈ T, |C X|, mul_nonneg hB h0, fun g => ?_⟩
    have q0 : 0 < qht g := one_pos.trans_le (hq g)
    rw [mul_div_assoc]
    refine hT α g _ (by positivity) fun X hX => ?_
    rw [le_div_iff₀ (by positivity), ← hr g]
    exact (hC X _).trans (hs C X hX)
end

section

open UpperTheory.V.Lit.Geo Matrix

private theorem form_bd {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x y : Fin d → ℂ) :
    ‖star x ⬝ᵥ G *ᵥ y‖ ≤ (∑ i, ∑ j, ‖G i j‖) * ‖x‖ * ‖y‖ := by
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, Pi.star_apply, norm_star]
  calc ‖x i‖ * (‖G i j‖ * ‖y j‖) = ‖G i j‖ * ‖x i‖ * ‖y j‖ := by ring
    _ ≤ ‖G i j‖ * ‖x‖ * ‖y‖ := by
      gcongr
      · exact norm_le_pi_norm x i
      · exact norm_le_pi_norm y j

theorem UpperTheory.V.Lit.Geo.ptBd :
    PtBd := by
  intro E _ _ _ a ha U hU Ξ r χ G n e hD q
  refine ⟨∑ I : Fin q → Fin n, (∑ i, ∑ j, ‖G i j‖) * (∏ i, ‖UpperTheory.V.Lit.Dr.hv (e (I i))‖) ^ 2,
    by positivity, fun α β hα hβ g M M' hM hM' h1 h2 => ?_⟩
  rw [ptRetr E a ha U hU Ξ r χ G n e hD q α β hα hβ g, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  refine (form_bd _ _ _).trans ?_
  have b1 := h1 fun i => e (I i)
  have b2 := h2 fun i => e (I i)
  have hP : 0 ≤ ∏ i, ‖UpperTheory.V.Lit.Dr.hv (e (I i))‖ := by positivity
  have hS : 0 ≤ ∑ i, ∑ j, ‖G i j‖ := by positivity
  refine (mul_le_mul (mul_le_mul_of_nonneg_left b1 hS) b2 (norm_nonneg _)
    (mul_nonneg hS (mul_nonneg hM hP))).trans_eq ?_
  ring
end

section

open UpperTheory.V.Lit.Geo.Cs

private theorem le_div_one_add_pow_succ_of_mul_le {x K Q A C F : ℝ} {N : ℕ} (hQ : 1 ≤ Q) (hA : 0 ≤ A) (hN : A * C ≤ N)
    (hF : F ≤ C * (1 + Real.log Q)) (hx : 0 ≤ x) (h : x * Q ^ N ≤ K) :
    x ≤ K * Real.exp (A * C) * Real.exp (-(A * F)) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le one_pos hQ
  have hl : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hp : Q ^ N = Real.exp (N * Real.log Q) := by
    rw [Real.exp_nat_mul, Real.exp_log hQ0]
  have h1 : A * F - A * C ≤ N * Real.log Q := by
    have := mul_le_mul_of_nonneg_left hF hA
    have := mul_le_mul_of_nonneg_right hN hl
    nlinarith
  have h2 : x * Real.exp (A * F - A * C) ≤ K := by
    refine le_trans ?_ h
    rw [hp]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hx
  have h3 : x = x * Real.exp (A * F - A * C) * (Real.exp (A * C) * Real.exp (-(A * F))) := by
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add, show A * F - A * C + (A * C + -(A * F)) = 0 by ring,
      Real.exp_zero, mul_one]
  rw [h3, mul_assoc K]
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

open GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.CuspidalSpectrum in
theorem UpperTheory.V.Lit.Geo.Cs.rapidAll :
    RapidAll := by
  intro E _ _ _ a U Ξ f lam C hlam hf q α hα hR
  obtain ⟨r, hr⟩ := UpperTheory.V.Lit.Bor.oneReal E a Ξ
  obtain ⟨hq1, hq2, -⟩ := UpperTheory.V.Lit.Geo.qhtFacts E a
  refine ⟨|r|, abs_nonneg r, fun A hA X j l => ?_⟩
  obtain ⟨he, hv⟩ := UpperTheory.V.Lit.Geo.Cs.rapidEig E a U Ξ r hr q α hα X j l
  obtain ⟨K, hK⟩ := hR l X ⌈A * C⌉₊
  refine ⟨K * Real.exp (A * C), fun g => ?_⟩
  obtain ⟨g₁, hs⟩ : ∃ g₁ : KernelIndexFullLattice.G1 E a, splitCentre E a (lam g) * g₁.1 = g := ⟨_, hlam.split g⟩
  have hK' := hK g₁
  have hq : qht g = qht (E := E) (a := a) g₁.1 := by
    have := hq2 1 (lam g) g₁.1
    rw [map_one, one_mul, hs] at this
    exact this
  have ha := UpperTheory.V.Lit.Bor.aInv E a _ _ he (lam g) g₁.1
  rw [hs] at ha
  rw [← hq] at hK'
  have hb := le_div_one_add_pow_succ_of_mul_le (hq1 g) hA (Nat.le_ceil (A * C)) (hf g) (norm_nonneg _)
    (le_trans (mul_le_mul_of_nonneg_right (norm_le_pi_norm _ j) (pow_nonneg (zero_le_one.trans (hq1 g)) _)) hK')
  have hb' : ‖((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g₁.1‖ ≤
      K * Real.exp (A * C) * Real.exp (-(A * f g)) := by
    rw [← hv]
    exact hb
  have hc : ‖Complex.exp (-(r : ℂ) * (lam g : ℂ))‖ ≤ Real.exp (|r| * |lam g|) := by
    rw [Complex.norm_exp, Real.exp_le_exp, ← abs_mul]
    simpa using neg_le_abs (r * lam g)
  rw [ha, norm_mul, sub_eq_add_neg, Real.exp_add, mul_left_comm]
  exact mul_le_mul hc hb' (norm_nonneg _) (Real.exp_pos _).le
end
