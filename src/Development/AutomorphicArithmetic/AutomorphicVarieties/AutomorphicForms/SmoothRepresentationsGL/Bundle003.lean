module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem exists_one_add_norm_pow_mul_norm_schwartz_le {V M E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : 𝓢(V × M, E)) (k : ℕ) :
    ∃ C, ∀ ξ m, (1 + ‖ξ‖) ^ k * ‖H (ξ, m)‖ ≤ C := by
  refine ⟨2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) H, fun ξ m => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl H (ξ, m)
  rw [norm_iteratedFDeriv_zero] at h
  refine le_trans ?_ h
  gcongr
  exact norm_fst_le (ξ, m)

theorem UpperTheory.V.Af.Smo.pftDeriv :
    UpperTheory.V.Af.Smo.PftDeriv := by
  intro V M _ _ _ _ _ _ _ _ G
  obtain ⟨C0, hC0⟩ := exists_one_add_norm_pow_mul_norm_schwartz_le G (Module.finrank ℝ V + 2)
  obtain ⟨C1, hC1⟩ := exists_one_add_norm_pow_mul_norm_schwartz_le (SchwartzMap.fderivCLM ℝ (V × M) ℂ G) (Module.finrank ℝ V + 1)
  simp only [SchwartzMap.fderivCLM_apply] at hC1
  have hC0n : 0 ≤ C0 := le_trans (by positivity) (hC0 0 0)
  have hC1n : 0 ≤ C1 := le_trans (by positivity) (hC1 0 0)
  have hG0 : Continuous (⇑G) := G.continuous
  have hG1 : Continuous (fun p => fderiv ℝ (⇑G) p) :=
    (SchwartzMap.fderivCLM ℝ (V × M) ℂ G).continuous
  obtain ⟨B, hB⟩ : ∃ B : V → ℝ, ∀ ξ,
      B ξ = (C1 + 2 * Real.pi * C0) / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := ⟨_, fun _ => rfl⟩
  have hBint : Integrable B := by
    have h := (integrable_one_add_norm (E := V) (μ := volume)
      (r := ((Module.finrank ℝ V + 1 : ℕ) : ℝ)) (by push_cast; linarith)).const_mul (C1 + 2 * Real.pi * C0)
    refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [hB]
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, div_eq_mul_inv]
  have hGB : ∀ ξ m, ‖G (ξ, m)‖ ≤ B ξ := by
    intro ξ m
    rw [hB, le_div_iff₀ (by positivity)]
    calc ‖G (ξ, m)‖ * (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1)
        ≤ (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 2) * ‖G (ξ, m)‖ := by
          have : (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) ≤ (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 2) :=
            pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) (by omega)
          nlinarith [norm_nonneg (G (ξ, m))]
      _ ≤ C0 := hC0 ξ m
      _ ≤ C1 + 2 * Real.pi * C0 := by nlinarith [Real.pi_gt_three]
  obtain ⟨F', hF'⟩ : ∃ F' : V × M → V → (V × M →L[ℝ] ℂ), ∀ z ξ, F' z ξ =
      ((𝐞 (-⟪ξ, z.1⟫) : Circle) : ℂ) • ((fderiv ℝ G (ξ, z.2)).comp
        ((0 : V × M →L[ℝ] V).prod (ContinuousLinearMap.snd ℝ V M))) +
      G (ξ, z.2) • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (2 * (Real.pi : ℂ) * Complex.I * 𝐞 (-⟪ξ, z.1⟫))).comp
        (-((innerSL ℝ ξ).comp (ContinuousLinearMap.fst ℝ V M)))) := ⟨_, fun _ _ => rfl⟩
  have hF'v : ∀ z ξ v, F' z ξ v = (𝐞 (-⟪ξ, z.1⟫) : ℂ) * fderiv ℝ G (ξ, z.2) (0, v.2) +
      G (ξ, z.2) * (-((⟪ξ, v.1⟫ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * 𝐞 (-⟪ξ, z.1⟫))) := by
    intro z ξ v
    rw [hF']
    simp [Complex.real_smul]
  have hcont : ∀ z, Continuous (F' z) := by
    intro z
    have he : Continuous (fun ξ : V => ((𝐞 (-⟪ξ, z.1⟫) : Circle) : ℂ)) := by fun_prop
    have : F' z = fun ξ => _ := funext (hF' z)
    rw [this]
    fun_prop
  have hbound : ∀ z ξ, ‖F' z ξ‖ ≤ B ξ := by
    intro z ξ
    have ht : 0 < 1 + ‖ξ‖ := by positivity
    have ha : ‖fderiv ℝ G (ξ, z.2)‖ ≤ C1 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact hC1 ξ z.2
    have hb : ‖G (ξ, z.2)‖ * ‖ξ‖ ≤ C0 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := by
      rw [le_div_iff₀ (by positivity)]
      calc ‖G (ξ, z.2)‖ * ‖ξ‖ * (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1)
          ≤ ‖G (ξ, z.2)‖ * (1 + ‖ξ‖) * (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) := by
            gcongr
            linarith
        _ = (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 2) * ‖G (ξ, z.2)‖ := by ring
        _ ≤ C0 := hC0 ξ z.2
    rw [hB]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [hF'v]
    have h0v : ‖((0 : V), v.2)‖ ≤ ‖v‖ := by
      rw [Prod.norm_def, Prod.norm_def]
      simp
    have h1 : ‖fderiv ℝ G (ξ, z.2) (0, v.2)‖ ≤ ‖fderiv ℝ G (ξ, z.2)‖ * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
    have h2 : |⟪ξ, v.1⟫| ≤ ‖ξ‖ * ‖v‖ :=
      (abs_real_inner_le_norm _ _).trans (by gcongr; exact norm_fst_le v)
    have e1 : ‖(𝐞 (-⟪ξ, z.1⟫) : ℂ) * fderiv ℝ G (ξ, z.2) (0, v.2)‖
        = ‖fderiv ℝ G (ξ, z.2) (0, v.2)‖ := by
      rw [norm_mul, Circle.norm_coe, one_mul]
    have e2 : ‖G (ξ, z.2) * (-((⟪ξ, v.1⟫ : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * 𝐞 (-⟪ξ, z.1⟫)))‖
        = ‖G (ξ, z.2)‖ * (|⟪ξ, v.1⟫| * (2 * Real.pi)) := by
      simp [abs_of_pos Real.pi_pos, Circle.norm_coe]
    have h3 := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ ‖v‖ * (2 * Real.pi))
    have h4 := mul_le_mul_of_nonneg_right ha (norm_nonneg v)
    calc _ ≤ ‖fderiv ℝ G (ξ, z.2)‖ * ‖v‖ + ‖G (ξ, z.2)‖ * (‖ξ‖ * ‖v‖ * (2 * Real.pi)) := by
          refine (norm_add_le _ _).trans ?_
          rw [e1, e2]
          exact add_le_add h1 (by gcongr)
      _ ≤ (C1 + 2 * Real.pi * C0) / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * ‖v‖ := by
          have e3 : (C1 + 2 * Real.pi * C0) / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * ‖v‖
              = C1 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * ‖v‖
                + C0 / (1 + ‖ξ‖) ^ (Module.finrank ℝ V + 1) * (‖v‖ * (2 * Real.pi)) := by ring
          rw [e3]
          nlinarith [h3, h4]
  have hFint : ∀ z, Integrable (F' z) :=
    fun z => hBint.mono' (hcont z).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => hbound z ξ)
  have hder1 : ∀ ξ z, HasFDerivAt (fun z : V × M => (𝐞 (-⟪ξ, z.1⟫) : ℂ) * G (ξ, z.2)) (F' z ξ) z := by
    intro ξ z
    have h1 := (Real.hasDerivAt_fourierChar _).hasFDerivAt.comp z
      (((innerSL ℝ ξ).comp (ContinuousLinearMap.fst ℝ V M)).hasFDerivAt.neg)
    have h2 : HasFDerivAt (fun z : V × M => G (ξ, z.2))
        ((fderiv ℝ G (ξ, z.2)).comp ((0 : V × M →L[ℝ] V).prod (ContinuousLinearMap.snd ℝ V M))) z :=
      (G.hasFDerivAt (ξ, z.2)).comp z ((hasFDerivAt_const ξ z).prodMk hasFDerivAt_snd)
    rw [hF']
    refine ((h1.mul h2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)).congr_fderiv ?_
    · simp
    · refine ContinuousLinearMap.ext fun v => ?_
      simp
  have hpft : ∀ (H : V × M → ℂ) z, pft H z = ∫ ξ, (𝐞 (-⟪ξ, z.1⟫) : ℂ) * H (ξ, z.2) := by
    intro H z
    simp only [UpperTheory.V.Af.Smo.pft, Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  have hder : ∀ z, HasFDerivAt (pft ⇑G) (∫ ξ, F' z ξ) z := by
    intro z
    have hfun : pft ⇑G = fun z => ∫ ξ, (𝐞 (-⟪ξ, z.1⟫) : ℂ) * G (ξ, z.2) := funext (hpft G)
    rw [hfun]
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ) (bound := B)
      Filter.univ_mem ?_ ?_ ((hcont z).aestronglyMeasurable) ?_ hBint ?_
    · refine Filter.Eventually.of_forall fun z' => ?_
      have : Continuous fun ξ : V => (𝐞 (-⟪ξ, z'.1⟫) : ℂ) * G (ξ, z'.2) := by fun_prop
      exact this.aestronglyMeasurable
    · have : Continuous fun ξ : V => (𝐞 (-⟪ξ, z.1⟫) : ℂ) * G (ξ, z.2) := by fun_prop
      refine hBint.mono' this.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
      rw [norm_mul, Circle.norm_coe, one_mul]
      exact hGB ξ z.2
    · exact Filter.Eventually.of_forall fun ξ z' _ => hbound z' ξ
    · exact Filter.Eventually.of_forall fun ξ z' _ => hder1 ξ z'
  refine ⟨fun z => (hder z).differentiableAt, fun v => ?_⟩
  have hl := (Complex.ofRealCLM.comp ((innerSL ℝ v.1).comp
    (ContinuousLinearMap.fst ℝ V M))).hasTemperateGrowth
  obtain ⟨G', hG'⟩ : ∃ G' : 𝓢(V × M, ℂ), ∀ p : V × M,
      G' p = -(2 * (Real.pi : ℂ) * Complex.I) * ((⟪v.1, p.1⟫ : ℝ) : ℂ) * G p + fderiv ℝ G p (0, v.2) := by
    refine ⟨(-(2 * (Real.pi : ℂ) * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (⇑(Complex.ofRealCLM.comp ((innerSL ℝ v.1).comp (ContinuousLinearMap.fst ℝ V M)))) G
      + LineDeriv.lineDerivOp ((0 : V), v.2) G, fun p => ?_⟩
    simp [SchwartzMap.smulLeftCLM_apply_apply hl, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    ring
  refine ⟨G', ?_⟩
  funext z
  show fderiv ℝ (pft ⇑G) z v = pft (⇑G') z
  rw [(hder z).fderiv, ContinuousLinearMap.integral_apply (hFint z) v, hpft]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [hF'v, hG', real_inner_comm v.1 ξ]
  ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem wl_nice_zero : Nice (0 : GA E n → ℂ) := by
  exact ⟨continuous_zero, ⟨0, fun _ => by simp⟩, fun _ _ => rfl,
    fun _ _ _ g => constantTerm_zero g, ⟨⊤, fun _ _ _ => rfl⟩⟩

private theorem wl_nice_add {f f' : GA E n → ℂ} (h : Nice f) (h' : Nice f') : Nice (f + f') := by
  refine ⟨h.cont.add h'.cont, ?_, IsLeftInvariant.add h.left h'.left, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := h.bdd
    obtain ⟨C', hC'⟩ := h'.bdd
    exact ⟨C + C', fun g => (norm_add_le _ _).trans (add_le_add (hC g) (hC' g))⟩
  · intro r a b g
    have e := constantTerm_add (r := r) h.cont h'.cont g
    rw [h.cusp r a b g, h'.cusp r a b g, add_zero] at e
    exact e
  · obtain ⟨V, hV⟩ := h.level
    obtain ⟨V', hV'⟩ := h'.level
    refine ⟨V ⊓ V', fun g v hv => ?_⟩
    rw [OpenSubgroup.mem_inf] at hv
    rw [Pi.add_apply, Pi.add_apply, hV g v hv.1, hV' g v hv.2]

private theorem wl_nice_smul {f : GA E n → ℂ} (h : Nice f) (z : ℂ) : Nice (z • f) := by
  refine ⟨h.cont.const_smul z, ?_, IsLeftInvariant.smul z h.left, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := h.bdd
    refine ⟨‖z‖ * C, fun g => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg _)
  · intro r a b g
    have e := constantTerm_smul (r := r) z f g
    rw [h.cusp r a b g, smul_zero] at e
    exact e
  · obtain ⟨V, hV⟩ := h.level
    exact ⟨V, fun g v hv => by rw [Pi.smul_apply, Pi.smul_apply, hV g v hv]⟩

private theorem wl_nice_tr {f : GA E n → ℂ} (h : Nice f) (x : GL (Fin n) (Af E)) :
    Nice (fun g => f (g * finGL E n x)) := by
  refine ⟨h.cont.comp (continuous_id.mul continuous_const),
    h.bdd.imp (fun _ hC _ => hC _), ?_, ?_, ?_⟩
  · intro γ g
    have e := h.left γ (g * finGL E n x)
    rw [← mul_assoc] at e
    exact e
  · intro r a b g
    exact (constantTerm_rightTranslate (r := r) f (finGL E n x) g).trans (h.cusp r a b _)
  · obtain ⟨V, hV⟩ := h.level
    refine ⟨V.comap (MulAut.conj x⁻¹).toMonoidHom ?_, fun g v hv => ?_⟩
    · show Continuous fun v => x⁻¹ * v * x⁻¹⁻¹
      exact (continuous_const.mul continuous_id).mul continuous_const
    · have hv' : x⁻¹ * v * x⁻¹⁻¹ ∈ V := hv
      have e := hV (g * finGL E n x) _ hv'
      rw [inv_inv, mul_assoc g, ← map_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, map_mul,
        ← mul_assoc] at e
      exact e

private theorem wl_add {f f' : GA E n → ℂ} (h : Continuous f) (h' : Continuous f') :
    whittaker (f + f') = whittaker f + whittaker f' := by
  funext g
  obtain ⟨C, hC, hD⟩ := FourierWhittaker.exists_isCompact_superset_vecDomain (K := E)
    (ι := FourierWhittaker.Pos n)
  have i : ∀ {φ : GA E n → ℂ}, Continuous φ → IntegrableOn (FourierWhittaker.wInt 0 φ g)
      (FourierWhittaker.vecDomain E (FourierWhittaker.Pos n))
      (FourierWhittaker.vecMeasure E (FourierWhittaker.Pos n)) := fun hφ =>
    ((FourierWhittaker.continuous_wInt 0 hφ g).continuousOn.integrableOn_compact hC).mono_set hD
  have e := integral_add (i h) (i h')
  simp only [FourierWhittaker.wInt] at e
  simp only [whittaker, Pi.add_apply, add_mul]
  exact e

private theorem wl_smul (f : GA E n → ℂ) (z : ℂ) : whittaker (z • f) = z • whittaker f := by
  funext g
  simp only [whittaker, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

private theorem wl_tr (f : GA E n → ℂ) (y : GA E n) :
    whittaker (fun g => f (g * y)) = fun g => whittaker f (g * y) := by
  funext g
  simp only [whittaker, mul_assoc]

private theorem wl_sum {f : GA E n → ℂ} (h : Nice f) (c : GL (Fin n) (Af E) → ℂ) (s : Finset (GL (Fin n) (Af E))) :
    Nice (∑ x ∈ s, c x • fun g => f (g * finGL E n x)) ∧
      whittaker (∑ x ∈ s, c x • fun g => f (g * finGL E n x)) =
        ∑ x ∈ s, c x • fun g => whittaker f (g * finGL E n x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    refine ⟨wl_nice_zero, ?_⟩
    funext g
    simp [whittaker]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have k := wl_nice_smul (wl_nice_tr h a) (c a)
    exact ⟨wl_nice_add k ih.1, by rw [wl_add k.cont ih.1.cont, ih.2, wl_smul, wl_tr]⟩

private theorem wl_fop (c : GL (Fin n) (Af E) →₀ ℂ) (f : GA E n → ℂ) :
    fop c f = ∑ x ∈ c.support, c x • fun g => f (g * finGL E n x) := by
  funext g
  simp [fop, Finsupp.sum, Finset.sum_apply]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Af.Smo.whLin :
    UpperTheory.V.Af.Smo.WhLin := by
  intro E _ _ n f hf
  refine ⟨fun c => ?_, fun f' hf' => ?_⟩
  · rw [wl_fop, wl_fop]
    exact wl_sum hf c c.support
  · have e : f - f' = f + (-1 : ℂ) • f' := by rw [neg_one_smul, sub_eq_add_neg]
    have k := wl_nice_smul hf' (-1)
    rw [e]
    exact ⟨wl_nice_add hf k, by rw [wl_add hf.cont k.cont, wl_smul, neg_one_smul, sub_eq_add_neg]⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem slice_int {V M : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup M] [NormedSpace ℝ M] (G : 𝓢(V × M, ℂ)) (y : M) :
    Integrable (fun ξ : V => G (ξ, y)) := by
  have h1 : Function.HasTemperateGrowth (fun ξ : V => (ξ, y)) := by
    have := (ContinuousLinearMap.inl ℝ V M).hasTemperateGrowth.add
      (Function.HasTemperateGrowth.const ((0 : V), y))
    convert this using 1
    ext ξ <;> simp
  have h2 : AntilipschitzWith 1 (fun ξ : V => (ξ, y)) := (Isometry.antilipschitz (by
    refine Isometry.of_dist_eq fun a b => ?_
    simp [Prod.dist_eq]))
  exact (SchwartzMap.compCLMOfAntilipschitz ℝ h1 h2 G).integrable

private theorem shear_int {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    [MeasurableSpace M] [BorelSpace M] (μ : Measure M) [μ.IsAddHaarMeasure] (N : M →L[ℝ] M)
    (hN : ∀ x, N (N x) = 0) (f : M → ℂ) : ∫ x, f (x + N x) ∂μ = ∫ x, f x ∂μ := by
  let L : M →ₗ[ℝ] M := 1 + (N : M →ₗ[ℝ] M)
  have hnil : IsNilpotent (-(N : M →ₗ[ℝ] M) : Module.End ℝ M) := ⟨2, by
    ext x
    simp [pow_two, hN]⟩
  have hdet : LinearMap.det L = 1 := by
    have := LinearMap.eval_charpoly (-(N : M →ₗ[ℝ] M)) 1
    rw [(LinearMap.isNilpotent_iff_charpoly _).1 hnil] at this
    simpa [L] using this.symm
  have hmap : Measure.map L μ = μ := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  let e : M ≃ₜ M :=
    { toFun := fun x => x + N x
      invFun := fun x => x - N x
      left_inv := fun x => by simp [hN]
      right_inv := fun x => by simp [hN]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hp : MeasurePreserving e.toMeasurableEquiv μ μ := ⟨e.toMeasurableEquiv.measurable, hmap⟩
  exact hp.integral_comp' f

theorem UpperTheory.V.Af.Smo.betaInt :
    UpperTheory.V.Af.Smo.BetaInt := by
  intro V M _ _ _ _ _ _ _ _ _ _ μ _ B hB G K K' hK hK' w η hw ⟨C, hC⟩ hwB
  have hint : ∀ (F : 𝓢(V × M, ℂ)) (a : V × M → ℂ), Measurable a → (∀ z, ‖a z‖ ≤ C) →
      ∫ u, ∫ x, a (u, x) * F (u, x) ∂μ = ∫ x, (∫ u, a (u, x) * F (u, x)) ∂μ := by
    intro F a ha haC
    refine integral_integral_swap (f := fun u x => a (u, x) * F (u, x)) ?_
    have : Integrable F ((volume : Measure V).prod μ) := F.integrable
    exact this.bdd_mul ha.aestronglyMeasurable (Filter.Eventually.of_forall haC)
  have h1 := hint K' (fun z => w z.2) (hw.comp measurable_snd) (fun z => hC _)
  have h2 := hint K (fun z => (𝐞 ⟪η, z.1⟫ : ℂ) * w z.2)
    (Measurable.mul (Continuous.measurable (by fun_prop)) (hw.comp measurable_snd)) (fun z => by rw [norm_mul, Circle.norm_coe, one_mul]; exact hC _)
  simp only [integral_const_mul] at h1
  rw [← h1]
  have h3 : ∀ u, ∫ x, w x * K' (u, x) ∂μ = ∫ x, (𝐞 ⟪η, u⟫ : ℂ) * w x * K (u, x) ∂μ := by
    intro u
    rw [← shear_int μ (B u) (hB u)]
    congr 1
    ext x
    rw [hwB, hK']
    simp [hB]
  simp only [h3]
  rw [h2]
  congr 1
  ext x
  have hF : 𝓕 (fun ξ => G (ξ, x)) = fun u => K (u, x) := by
    ext u
    rw [hK]; rfl
  have h4 := Continuous.fourierInv_fourier_eq (f := fun ξ => G (ξ, x)) (by fun_prop) (slice_int G x)
    (by rw [hF]; exact slice_int K x)
  have h5 := congrFun h4 η
  rw [hF, Real.fourierInv_eq] at h5
  rw [← h5, ← integral_const_mul]
  congr 1
  ext u
  rw [Circle.smul_def, smul_eq_mul, real_inner_comm]
  ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem lmul_lmul {E : Type} [Field E] [NumberField E] {n : ℕ} (a b : Matrix (Fin n) (Fin n) (Rinf E))
    (x : Lie E n) : lmul (toL a) (lmul (toL b) x) = lmul (toL (a * b)) x := by
  change toL (a * (b * Matrix.of x)) = toL (a * b * Matrix.of x)
  rw [Matrix.mul_assoc]

private theorem rowM_one {R : Type} [CommRing R] {n : ℕ} (m : Fin n) :
    rowM m ((1 : Matrix (Fin n) (Fin n) R) m) = 1 := by
  ext i j
  simp only [rowM, Matrix.of_apply]
  split_ifs with h
  · rw [h.1]
  · rfl

theorem UpperTheory.V.Af.Smo.archKir :
    UpperTheory.V.Af.Smo.ColConj → UpperTheory.V.Af.Smo.RowStep → UpperTheory.V.Af.Smo.ArchStep → UpperTheory.V.Af.Smo.LinChange → UpperTheory.V.Af.Smo.ArchKir := by
  classical
  intro hC hR hA hL E _ _ n m
  induction m with
  | zero =>
    intro _
    refine ⟨fun p => psiR E (supN p.val), ?_, fun α => ⟨α, fun w _ _ hw p hp => ?_⟩⟩
    · have : supN (1 : GL (Fin n) (Rinf E)).val = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        split_ifs with h
        · exact Matrix.one_apply_ne (fun e => by subst e; omega)
        · rfl
      simp only [this]
      simp [psiR]
    · simp only [hw p hp, mul_assoc]
      exact integral_const_mul _ _
  | succ m ih =>
    intro hm
    obtain ⟨H, H1, hH⟩ := ih (by omega)
    let m' : Fin n := ⟨m, by omega⟩
    obtain ⟨h, h1, hu, hh⟩ := hA E n m' hm
    obtain ⟨c, c1, hc⟩ := hL E n
    refine ⟨fun p => if hs : IsUnit (rowM m' (p.val m')) then h (p.val m') * (c hs.unit * H (p * hs.unit⁻¹)) else 0, ?_,
      fun α => ?_⟩
    · have hs : IsUnit (rowM m' ((1 : GL (Fin n) (Rinf E)).val m')) := by
        rw [Units.val_one, rowM_one]; exact isUnit_one
      have e : hs.unit = 1 := Units.ext (by rw [hs.unit_spec, Units.val_one, rowM_one])
      simp only [dif_pos hs, e]
      simp [h1, c1, H1]
    · obtain ⟨β₀, hβ₀⟩ := hH α
      obtain ⟨β, hβ⟩ := hh β₀
      refine ⟨β, fun w wm wb hw p hp => ?_⟩
      obtain ⟨C, hCb⟩ := wb
      have key := hβ (fun x => w (lmul (toL p.val) x)) (p.val m')
        (wm.comp (lmul (toL p.val)).continuous.measurable) ⟨C, fun x => hCb _⟩ (fun u x => by
          obtain ⟨ν, hν, hs, e⟩ := hC (Rinf E) n m' hm p hp u
          simp only [lmul_lmul]
          rw [e, ← lmul_lmul, hw ν hν, hs])
      rw [key]
      by_cases h0 : h (p.val m') = 0
      · simp [h0]
      have hs := hu _ h0
      simp only [dif_pos hs]
      have hy := hR (Rinf E) n m' p hs.unit hp hs.unit_spec
      have e1 := hβ₀ w wm ⟨C, hCb⟩ hw _ hy
      have e2 := hc hs.unit (fun y => w (lmul (toL (p * hs.unit⁻¹).val) y) * β₀ y)
      have e3 : (p * hs.unit⁻¹).val * hs.unit.val = p.val := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      simp only [lmul_lmul, e3] at e2
      rw [hs.unit_spec] at e2
      rw [e2, e1]
      ring
end
