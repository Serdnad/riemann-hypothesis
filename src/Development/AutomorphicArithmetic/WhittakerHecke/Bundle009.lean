module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Bundle001
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle245
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle453
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Satake
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

@[expose] public section

section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

private theorem out_eq_cuspQuot {E : Type} [Field E] [NumberField E] {r : ℕ}
    (F : AdelicGLn.AdelicGL E r → ℂ) (h : AutomorphicForm.IsLeftInvariant F)
    (y : RightCosetSpace (rationalGLOne (K := E) (n := r))) :
    F ((Quotient.out y : normOneGL (K := E) (n := r)) : AdelicGLn.AdelicGL E r) = CuspidalSpectrum.cuspQuot h y := by
  have e : RightCosetSpace.mk (rationalGLOne (K := E) (n := r)) (Quotient.out y) = y := Quotient.out_eq y
  calc F ((Quotient.out y : normOneGL (K := E) (n := r)) : AdelicGLn.AdelicGL E r)
      = CuspidalSpectrum.cuspQuot h (RightCosetSpace.mk (rationalGLOne (K := E) (n := r)) (Quotient.out y)) := rfl
    _ = CuspidalSpectrum.cuspQuot h y := by rw [e]

theorem UpperTheory.integrable_translate_mul_conj_and_inner_self_ne_zero :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (S : Set (Pl E)) (r : ℕ) (b : Blo S r),
      (∀ g : GA E r, Integrable (fun y : RightCosetSpace (rationalGLOne (K := E) (n := r)) => b.f.1 (((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * g) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r))) (quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r))) ∧
      ∫ y : RightCosetSpace (rationalGLOne (K := E) (n := r)), b.f.1 ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r)) ∂(quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r)) ≠ 0 := by
  intro E _ _ _ S r b
  have : OpensMeasurableSpace (RightCosetSpace (rationalGLOne (K := E) (n := r))) := by
    set_option synthInstance.maxHeartbeats 200000 in
      infer_instance
  have hfin := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := r) (mu1 E r)
  have hcont : Continuous b.f.1 := b.cusp.1.continuous
  have hL : AutomorphicForm.IsLeftInvariant b.f.1 := b.cusp.1.isLeftInvariant
  obtain ⟨C, hC⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms b.cusp
  have hsec : ∀ s : {x : ℝ // 0 < x}, centralSection E r s = zt E r (Real.log s.1) := fun s => by
    unfold zt
    exact congrArg _ (Subtype.ext (Real.exp_log s.2).symm)
  have hb : ∀ g, ‖b.f.1 g‖ ≤ C := fun g => by
    obtain ⟨s, y, hy, rfl⟩ := CuspidalSpectrum.exists_centralSection_mul_mem_normOneGL g
    rw [hsec s, b.cen]
    exact hC y hy
  have hbq : ∀ (F : AdelicGLn.AdelicGL E r → ℂ) (h : AutomorphicForm.IsLeftInvariant F), (∀ g, ‖F g‖ ≤ C) →
      ∀ q, ‖CuspidalSpectrum.cuspQuot h q‖ ≤ C := fun F h hF q => by
    rw [← out_eq_cuspQuot F h q]
    exact hF _
  have hq := CuspidalSpectrum.continuous_cuspQuot hL hcont
  refine ⟨fun g => ?_, fun h0 => ?_⟩
  · have hLg : AutomorphicForm.IsLeftInvariant (fun x => b.f.1 (x * g)) := fun γ x => by
      show b.f.1 (_ * x * g) = b.f.1 (x * g)
      rw [mul_assoc]
      exact hL γ _
    have hcg : Continuous (fun x : AdelicGLn.AdelicGL E r => b.f.1 (x * g)) :=
      hcont.comp (continuous_id.mul continuous_const)
    have hqg := CuspidalSpectrum.continuous_cuspQuot hLg hcg
    have e : (fun y : RightCosetSpace (rationalGLOne (K := E) (n := r)) => b.f.1 (((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * g) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r))) =
        fun y => CuspidalSpectrum.cuspQuot hLg y * starRingEnd ℂ (CuspidalSpectrum.cuspQuot hL y) := by
      funext y
      rw [← out_eq_cuspQuot _ hLg y, ← out_eq_cuspQuot _ hL y]
    rw [e]
    refine Integrable.of_bound (hqg.mul (Complex.continuous_conj.comp hq)).aestronglyMeasurable (C * C)
      (Filter.Eventually.of_forall fun q => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hbq _ hLg (fun x => hb _) q) (hbq _ hL hb q) (norm_nonneg _)
      ((norm_nonneg _).trans (hbq _ hL hb q))
  · have e : ∀ y : RightCosetSpace (rationalGLOne (K := E) (n := r)),
        b.f.1 ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r) * starRingEnd ℂ (b.f.1 ((Quotient.out y : normOneGL (K := E) (n := r)) : GA E r)) =
        ((‖CuspidalSpectrum.cuspQuot hL y‖ ^ 2 : ℝ) : ℂ) := fun y => by
      rw [out_eq_cuspQuot _ hL y, Complex.mul_conj', Complex.ofReal_pow]
    have h1 : ∫ q, ‖CuspidalSpectrum.cuspQuot hL q‖ ^ 2 ∂(quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r)) = 0 := by
      rw [← Complex.ofReal_eq_zero, ← integral_complex_ofReal, ← h0]
      exact integral_congr_ae (Filter.Eventually.of_forall fun q => (e q).symm)
    have hi : Integrable (fun q => ‖CuspidalSpectrum.cuspQuot hL q‖ ^ 2) (quotientMeasure (rationalGLOne (K := E) (n := r)) (mu1 E r)) :=
      Integrable.of_bound (hq.norm.pow 2).aestronglyMeasurable (C ^ 2) (Filter.Eventually.of_forall fun q => by
        rw [norm_pow, norm_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbq _ hL hb q) 2)
    have h2 := (integral_eq_zero_iff_of_nonneg (fun q => sq_nonneg _) hi).1 h1
    have h3 := MeasureTheory.QuasiMeasurePreserving.ae_eq_comp
      (RightCosetSpace.quasiMeasurePreserving_mk (rationalGLOne (K := E) (n := r)) (mu1 E r)) h2
    have h4 := (Continuous.ae_eq_iff_eq (mu1 E r) (f := fun y : normOneGL (K := E) (n := r) => ‖b.f.1 (y : AdelicGLn.AdelicGL E r)‖ ^ 2)
      ((hcont.comp continuous_subtype_val).norm.pow 2) continuous_const).1 h3
    apply b.ne
    refine Subtype.ext (funext fun g => ?_)
    obtain ⟨s, y, hy, rfl⟩ := CuspidalSpectrum.exists_centralSection_mul_mem_normOneGL g
    rw [hsec s, b.cen]
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (congrFun h4 ⟨y, hy⟩))
end

section

open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

private theorem flow_abs {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    (ν : Measure Y) [SFinite ν] (T : ℝ → Y → Y) (hT : Continuous fun p : Y × ℝ => T p.2 p.1)
    (hm : ∀ u, MeasurePreserving (T u) ν ν) (he : ∀ u, MeasurableEmbedding (T u)) (H D : Y → ℂ) (hD : Continuous D)
    (iH : Integrable H ν) (iD : Integrable D ν) (hd : ∀ y u, HasDerivAt (fun s => H (T s y)) (D (T u y)) u) :
    ∫ y, D y ∂ν = 0 := by
  have hc : Continuous fun p : Y × ℝ => D (T p.2 p.1) := hD.comp hT
  have h1 : ∀ y, ∫ u in Set.Ioc (0 : ℝ) 1, D (T u y) = H (T 1 y) - H (T 0 y) := fun y => by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd y u)
      ((hc.comp (Continuous.prodMk_right y)).intervalIntegrable _ _)
  have hi : Integrable (Function.uncurry fun y u => D (T u y)) (ν.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    refine (integrable_prod_iff' hc.aestronglyMeasurable).2 ⟨.of_forall fun u => ((hm u).integrable_comp_emb (he u)).2 iD, ?_⟩
    have : (fun u => ∫ y, ‖D (T u y)‖ ∂ν) = fun _ => ∫ y, ‖D y‖ ∂ν := funext fun u => (hm u).integral_comp (he u) fun y => ‖D y‖
    exact this ▸ integrable_const _
  have h2 := integral_integral_swap hi
  simp only [h1, fun u => (hm u).integral_comp (he u) D] at h2
  have i : ∀ u, Integrable (fun x => H (T u x)) ν := fun u => ((hm u).integrable_comp_emb (he u)).2 iH
  rw [integral_sub (i 1) (i 0),
    (hm 1).integral_comp (he 1) H, (hm 0).integral_comp (he 0) H] at h2
  simpa using h2.symm

private theorem flow_cont {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ : Subgroup G) (c : ℝ → G)
    (hc : Continuous c) : Continuous fun p : RightCosetSpace Γ × ℝ => rightMul Γ (c p.2) p.1 :=
  (continuous_rightMul_prod Γ).comp (f := fun p : RightCosetSpace Γ × ℝ => (p.1, c p.2))
    (continuous_fst.prodMk (hc.comp continuous_snd))

theorem UpperTheory.integral_quotient_derivative_oneParameter_eq_zero :
    ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (h D : GA E r → ℂ) (c : ℝ → GA E r),
          AutomorphicForm.IsLeftInvariant h → AutomorphicForm.IsLeftInvariant D → Continuous D → Continuous c → c 0 = 1 →
          (∀ s t, c (s + t) = c s * c t) → (∀ s, c s ∈ normOneGL (K := E) (n := r)) → (∀ g, HasDerivAt (fun s => h (g * c s)) (D g) 0) →
          Integrable (onQ h) (muQ E r) → Integrable (onQ D) (muQ E r) → ∫ y, onQ D y ∂muQ E r = 0 := by
  intro E _ _ r h D c hh hD cD cc _ cadd c1 hd ih iD
  have e : ∀ {f : GA E r → ℂ} (hf : AutomorphicForm.IsLeftInvariant f), onQ f = CuspidalSpectrum.cuspQuot hf := fun hf => by
    funext y
    conv_rhs => rw [← Quotient.out_eq y]
    rfl
  rw [e hh] at ih
  rw [e hD] at iD ⊢
  haveI : IsFiniteMeasure (muQ E r) := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := r) (mu1 E r)
  haveI : SigmaFinite (muQ E r) := IsFiniteMeasure.toSigmaFinite _
  haveI : SFinite (muQ E r) := instSFiniteOfSigmaFinite
  set_option synthInstance.maxHeartbeats 200000 in
    refine flow_abs (muQ E r) (fun u => rightMul (rationalGLOne (K := E) (n := r)) ⟨c u, c1 u⟩) ?_
      (fun u => measurePreserving_rightMul (Γ := rationalGLOne (K := E) (n := r)) (mu1 E r) _)
      (fun u => (rightMulHomeomorph (rationalGLOne (K := E) (n := r)) _).measurableEmbedding) _ _ ?_ ih iD fun y u => ?_
    · exact flow_cont (rationalGLOne (K := E) (n := r)) (fun u => ⟨c u, c1 u⟩) (cc.subtype_mk c1)
    · exact (isOpenQuotientMap_mk (rationalGLOne (K := E) (n := r))).isQuotientMap.continuous_iff.2 (cD.comp continuous_subtype_val)
    · obtain ⟨g, rfl⟩ := mk_surjective (rationalGLOne (K := E) (n := r)) y
      have h1 := (hd (g * c u)).scomp_of_eq u ((hasDerivAt_id u).sub_const u) (by simp)
      rw [one_smul] at h1
      refine h1.congr_of_eventuallyEq (.of_forall fun s => ?_)
      change h (g * c s) = h (g * c u * c (s - u))
      rw [mul_assoc, ← cadd, add_sub_cancel]
end

section

open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

private theorem zt_eq (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r : ℕ) (t : ℝ) :
    zt E r t = GlobalTheory.UnitaryBC.splitCentre E r (t * ((r * Module.finrank ℚ E : ℝ))⁻¹) := by
  have h := GlobalTheory.CuspBoundSiegel.diagUnits_posIdele (E := E) r
    (Real.rpow_pos_of_pos (Real.exp_pos t) ((r * Module.finrank ℚ E : ℝ))⁻¹)
  rw [Real.log_rpow (Real.exp_pos t), Real.log_exp, mul_comm _ t] at h
  exact h

theorem UpperTheory.functional_vanishes_invariant :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r : ℕ) (f : Sm E r), (∀ t g, f.1 (zt E r t * g) = f.1 g) → j0 E r f = 0 := by
  intro E _ _ _ r f hf
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [j0]
  have hd : ((r * Module.finrank ℚ E : ℝ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hr.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  have h : ∀ t g, f.1 (GlobalTheory.UnitaryBC.splitCentre E r t * g) = f.1 g := fun t g => by
    have := hf (t * (r * Module.finrank ℚ E : ℝ)) g
    rwa [zt_eq, mul_inv_cancel_right₀ hd] at this
  have h0 : lie E r (oneL E r) f = 0 := by
    refine Subtype.ext (funext fun g => ?_)
    have h1 := GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre E r f g 0
    have h2 : (fun t : ℝ => f.1 (g * GlobalTheory.UnitaryBC.splitCentre E r t)) = fun _ => f.1 g := by
      funext t
      rw [← CuspidalL2GL.splitCentre_comm, h]
    rw [h2] at h1
    have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (f.1 g))
    rw [CuspidalL2GL.splitCentre_zero, mul_one] at h3
    exact h3
  have h4 : lie E r (oneL E r) = ∑ τ : E →+* ℂ, ∑ i : Fin r, Eop τ i i := by
    rw [UpperTheory.V.Cm.lie_eq_sum]
    have hc : ∀ (τ : E →+* ℂ) (i k : Fin r), coord τ (oneL E r i k) = if i = k then 1 else 0 := fun τ i k => by
      have : oneL E r i k = (1 : Matrix (Fin r) (Fin r) (Cinf E)) i k := rfl
      rw [this, Matrix.one_apply]
      split_ifs <;> simp
    simp only [hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [j0, LinearMap.smul_apply, ← h4, h0, smul_zero]
end

section

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin GlobalTheory.LFun Formalism.UG Formalism.UG.P
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem fst_finGL (k : GL (Fin a) (Af E)) :
    Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E a k) = 1 :=
  map_cornerGL_of_zero _ _ (fun _ => rfl) k

private theorem det_finGL_any (k : GL (Fin a) (Af E)) :
    Matrix.GeneralLinearGroup.det (finGL E a k) = finId E (Matrix.GeneralLinearGroup.det k) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · have h := GlobalTheory.CuspRep.det_map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E a k)
    rw [fst_finGL] at h
    refine h.symm.trans ?_
    change _ = RingHom.fst (InfiniteAdeleRing E) (Af E) ((1 : Ad E) - sFin E 1 + sFin E _)
    have hz : ∀ x, (sFin E x).1 = 0 := fun _ => rfl
    simp only [map_one, map_sub, map_add]
    change (1 : InfiniteAdeleRing E) = 1 - (sFin E 1).1 + (sFin E (Matrix.GeneralLinearGroup.det k : Af E)).1
    simp [hz]
  · have h := GlobalTheory.CuspRep.det_map (pFin E) (finGL E a k)
    rw [pFin_finGL] at h
    refine h.symm.trans ?_
    change _ = (1 : Af E) - 1 + (Matrix.GeneralLinearGroup.det k : (Af E)ˣ)
    simp

private theorem norm_of_val_one {w : Pl E} {y : w.adicCompletion E} (h : Valued.v y = 1) : ‖y‖ = 1 := by
  rw [FinitePlace.norm_def, h, map_one, NNReal.coe_one]

private theorem norm_unif {w : Pl E} {ϖ : w.adicCompletion E} (hu : IsUnifV E w ϖ) : ‖ϖ‖ = (qV E w : ℝ)⁻¹ := by
  have h0 : Valued.v ϖ ≠ 0 := by
    rw [show Valued.v ϖ = _ from hu]; exact WithZero.coe_ne_zero
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
  have e : Multiplicative.toAdd (WithZero.unzero h0) = -1 := by
    have : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = _ :=
      (WithZero.coe_unzero h0).trans hu
    exact congrArg Multiplicative.toAdd (WithZero.coe_injective this)
  rw [WithZero.toAdd_unzero_eq_log] at e
  rw [e, zpow_neg_one]
  simp [qV]

end

theorem UpperTheory.detModule_satakeTset_eq_inv_pow :
    ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r a : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → a ≤ r → ∀ x ∈ satakeTset (n := r) w ϖ a,
      (detModule E r (finGL E r (locGL E r w x)) : ℝ) = ((qV E w : ℝ) ^ a)⁻¹ := by
  intro E _ _ w r a ϖ hu ha x hx
  obtain ⟨k₁, h₁, k₂, h₂, e⟩ := hx
  have hm : (Matrix.GeneralLinearGroup.det x : (w.adicCompletion E)ˣ).val =
      (Matrix.GeneralLinearGroup.det k₁).val * ϖ ^ a * (Matrix.GeneralLinearGroup.det k₂).val := by
    change x.val.det = k₁.val.det * _ * k₂.val.det
    rw [e, Matrix.det_mul, Matrix.det_mul, GlobalTheory.SphGal.det_diagJ ϖ ha]
  have hid : Matrix.GeneralLinearGroup.det (finGL E r (locGL E r w x)) =
      GroundTheory.Global.IdeleGroup.finiteEmbedding w (Matrix.GeneralLinearGroup.det x) :=
    (det_finGL_any _).trans (finId_det_locGL w x)
  have hmod : (detModule E r (finGL E r (locGL E r w x)) : ℝ) =
      ‖((Matrix.GeneralLinearGroup.det x : (w.adicCompletion E)ˣ) : w.adicCompletion E)‖ := by
    change ((GroundTheory.Global.IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det (finGL E r (locGL E r w x))) : {r : ℝ // 0 < r}) : ℝ) = _
    rw [hid, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding]
  have n₁ : ‖(Matrix.GeneralLinearGroup.det k₁).val‖ = 1 :=
    norm_of_val_one (GlobalTheory.SphGal.isUnitAt_det_of_mem (k := k₁) h₁)
  have n₂ : ‖(Matrix.GeneralLinearGroup.det k₂).val‖ = 1 :=
    norm_of_val_one (GlobalTheory.SphGal.isUnitAt_det_of_mem (k := k₂) h₂)
  rw [hmod, hm, norm_mul, norm_mul, n₁, n₂, norm_pow, norm_unif hu, one_mul, mul_one, inv_pow]
end
