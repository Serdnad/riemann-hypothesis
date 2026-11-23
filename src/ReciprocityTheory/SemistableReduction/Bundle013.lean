module

public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import ReciprocityTheory.SemistableReduction.Bundle001
public import ReciprocityTheory.SemistableReduction.Bundle002
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.GeneralBFactAlt
public import Lemmata.GeneralBFactTail.Imports
public import ReciprocityTheory.SemistableReduction.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.UniformSpace.Uniformizable
public import ReciprocityTheory.SemistableReduction.Bundle005
public import ReciprocityTheory.SemistableReduction.RestBlockSubstIsMultiHomogeneous
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Lemmata.GeneralBFactLast.Imports
public import Mathlib.RingTheory.OrderOfVanishing.Basic

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix Filter Topology Set

theorem analyticOnNhd_V_of_differentiableOn {n : ℕ} {f : ReciprocityTheory.L2DbarEstimates.V n → ℂ}
    {B : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hB : IsOpen B) (hf : DifferentiableOn ℂ f B) :
    AnalyticOnNhd ℂ f B := by
  intro x hx
  let e : ReciprocityTheory.L2DbarEstimates.V n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  have hU : IsOpen (e.symm ⁻¹' B) := hB.preimage e.symm.continuous
  have hg : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' B) :=
    hf.comp e.symm.differentiable.differentiableOn (fun y hy => hy)
  have ha := ReciprocityTheory.AnForm.Osgood.osgood n _ _ hU hg (e x) (by simpa using hx)
  have hfe : f = (f ∘ e.symm) ∘ e := by ext y; simp
  rw [hfe]
  exact ha.comp ((e : ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] (Fin n → ℂ)).analyticAt x)

theorem differentiableOn_finset_prod' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [DecidableEq ι] {F : ι → E → ℂ} {B : Set E}
    (hF : ∀ i, DifferentiableOn ℂ (F i) B) (s : Finset ι) :
    DifferentiableOn ℂ (fun v => ∏ i ∈ s, F i v) B := by
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hF a).mul ih

theorem differentiableOn_det_of {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Type} [Fintype U] [DecidableEq U] {F : U → U → E → ℂ} {B : Set E}
    (hF : ∀ a b, DifferentiableOn ℂ (F a b) B) :
    DifferentiableOn ℂ (fun v => (Matrix.of fun a b => F a b v).det) B := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  exact (differentiableOn_const _).mul
    (differentiableOn_finset_prod' (F := fun i v => F (σ i) i v) (fun i => hF _ _) _)

end ReciprocityTheory.MultiplicativeHeights
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory MvPolynomial NumberField

theorem harmonic_pred_le_one_add_log {n : ℕ} (hn : 0 < n) : (harmonic (n - 1) : ℝ) ≤ 1 + Real.log n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := harmonic_le_one_add_log (m + 1)
  have h2 : harmonic (m + 1 - 1) ≤ harmonic (m + 1) := by
    have e : m + 1 - 1 = m := by omega
    rw [e, harmonic_succ]
    have : (0 : ℚ) ≤ (((m + 1 : ℕ) : ℚ))⁻¹ := by positivity
    linarith
  have h3 : (harmonic (m + 1 - 1) : ℝ) ≤ harmonic (m + 1) := by exact_mod_cast h2
  linarith

theorem log_norm_coeff_sub_le_blockSphereLogMean (hSJ : SJStatement) (hInt : SphereLogIntegrableStatement) {B n : ℕ}
    (hn : 0 < n) {a : Fin B → ℕ} {g : MvPolynomial (Fin B × Fin n) ℂ}
    (hg : IsMultiHomogeneous a g) (s : Fin B × Fin n →₀ ℕ) (hs : g.coeff s ≠ 0) :
    Real.log ‖g.coeff s‖ - ∑ b, (a b : ℝ) * (Real.log n + 1 / 2) ≤ blockSphereMean B n g := by
  obtain ⟨z, hz1, hzc⟩ := exists_torus_coeff_le g s
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set r : ℝ := Real.sqrt n with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr hnpos
  have hr2 : r ^ 2 = n := Real.sq_sqrt hnpos.le

  have hmem : ∀ b : Fin B, (WithLp.toLp 2 (fun j => z (b, j) / (r : ℂ)) : EuclideanSpace ℂ (Fin n)) ∈
      Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1 := by
    intro b
    have hj : ∀ j, ‖z (b, j) / (r : ℂ)‖ = 1 / r := by
      intro j
      rw [norm_div, hz1, Complex.norm_of_nonneg hr.le]
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    simp only [PiLp.toLp_apply, hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [div_pow, one_pow, hr2, mul_one_div_cancel hnpos.ne', Real.sqrt_one]
  let u : BlockSphere B n := fun b => ⟨WithLp.toLp 2 (fun j => z (b, j) / (r : ℂ)), hmem b⟩
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hz' : (fun p => (r : ℂ) * blockPoint u p) = z := by
    funext p
    simp only [blockPoint, spherePoint, u, PiLp.toLp_apply]
    field_simp
  have hev := eval_mul_of_isMultiHomogeneous hg (r : ℂ) (blockPoint u)
  rw [hz'] at hev
  have hcpos : 0 < ‖g.coeff s‖ := norm_pos_iff.mpr hs
  have hgz : 0 < ‖eval z g‖ := lt_of_lt_of_le hcpos hzc
  have hnorm : ‖eval z g‖ = r ^ (∑ b, a b) * ‖eval (blockPoint u) g‖ := by
    rw [hev, norm_mul, norm_pow, Complex.norm_of_nonneg hr.le]
  have hgu : eval (blockPoint u) g ≠ 0 := by
    intro h0
    rw [hnorm, h0, norm_zero, mul_zero] at hgz
    exact lt_irrefl _ hgz
  have hbb := blockSphere_logMean_bound hSJ hInt hn B a g u hg hgu
  have hH := harmonic_pred_le_one_add_log hn
  have hlogr : Real.log r = Real.log n / 2 := Real.log_sqrt hnpos.le
  have hlz : Real.log ‖eval z g‖ =
      ((∑ b, a b : ℕ) : ℝ) * Real.log r + Real.log ‖eval (blockPoint u) g‖ := by
    rw [hnorm, Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hgu), Real.log_pow]
  have hlc : Real.log ‖g.coeff s‖ ≤ Real.log ‖eval z g‖ := Real.log_le_log hcpos hzc
  set A : ℝ := ∑ b, (a b : ℝ) with hAdef
  have hsum : ((∑ b, a b : ℕ) : ℝ) = A := by rw [hAdef]; push_cast; rfl
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun b _ => Nat.cast_nonneg _)
  have hmul : A / 2 * (harmonic (n - 1) : ℝ) ≤ A / 2 * (1 + Real.log n) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  have hgoal : ∑ b, (a b : ℝ) * (Real.log n + 1 / 2) = A * (Real.log n + 1 / 2) := by
    rw [hAdef, Finset.sum_mul]
  rw [hgoal]
  rw [hsum, hlogr] at hlz
  nlinarith

theorem neg_log_norm_coeff_le_finitePlaces {K : Type*} [Field K] [NumberField K] {ι : Type*} (f : MvPolynomial ι K)
    (s : ι →₀ ℕ) (hs : s ∈ f.support) :
    -Real.log |((Algebra.norm ℚ (f.coeff s) : ℚ) : ℝ)| ≤
      ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w f) := by
  classical
  have hc : f.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  have hA : ∀ w : FinitePlace K, w (f.coeff s) ≤ gaussAbs w f := by
    intro w
    unfold gaussAbs
    have h1 := Finset.le_sup (f := fun t => (w (f.coeff t)).toNNReal) hs
    calc w (f.coeff s) ≤ ((w (f.coeff s)).toNNReal : ℝ) := Real.le_coe_toNNReal _
      _ ≤ _ := by exact_mod_cast h1
  have hpos : ∀ w : FinitePlace K, 0 < w (f.coeff s) := fun w => NumberField.FinitePlace.pos_iff.mpr hc
  have hU : (⋃ t ∈ f.support, Function.mulSupport (fun w : FinitePlace K => w (f.coeff t))).Finite :=
    Set.Finite.biUnion f.support.finite_toSet
      (fun t ht => NumberField.FinitePlace.hasFiniteMulSupport (MvPolynomial.mem_support_iff.mp ht))
  set T := hU.toFinset with hT
  have hsubG : Function.support (fun w : FinitePlace K => Real.log (gaussAbs w f)) ⊆ (T : Set _) := by
    intro w hw
    rw [hT, Set.Finite.coe_toFinset]
    by_contra hnot
    apply hw
    simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hnot
    have h1 : gaussAbs w f = 1 := by
      unfold gaussAbs
      have hne : f.support.Nonempty := ⟨s, hs⟩
      rw [Finset.sup_congr rfl (g := fun _ => (1 : NNReal)) (fun t ht => by simp [hnot t ht]),
        Finset.sup_const hne]
      simp
    simp [h1]
  have hsubW : Function.mulSupport (fun w : FinitePlace K => w (f.coeff s)) ⊆ (T : Set _) := by
    intro w hw
    rw [hT, Set.Finite.coe_toFinset]
    exact Set.mem_biUnion hs hw
  have hprod := NumberField.FinitePlace.prod_eq_inv_abs_norm hc
  rw [finprod_eq_prod_of_mulSupport_subset _ hsubW] at hprod
  rw [finsum_eq_sum_of_support_subset _ hsubG]
  have hlog : Real.log (∏ w ∈ T, w (f.coeff s)) = ∑ w ∈ T, Real.log (w (f.coeff s)) :=
    Real.log_prod (fun w _ => (hpos w).ne')
  rw [hprod] at hlog
  have hle : ∑ w ∈ T, Real.log (w (f.coeff s)) ≤ ∑ w ∈ T, Real.log (gaussAbs w f) :=
    Finset.sum_le_sum (fun w _ => Real.log_le_log (hpos w) (hA w))
  push_cast at hlog
  rw [Real.log_inv] at hlog
  linarith

theorem sum_log_norm_embedding_eq {K : Type*} [Field K] [NumberField K] (c : K) (hc : c ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ c‖ = Real.log |((Algebra.norm ℚ c : ℚ) : ℝ)| := by
  classical
  have hne : ∀ σ : K →+* ℂ, ‖σ c‖ ≠ 0 := fun σ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hc)
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ c
  have h2 : ∏ σ : K →+* ℂ, σ c = ∏ σ : K →ₐ[ℚ] ℂ, σ c :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)
  have hprod : ∏ σ : K →+* ℂ, ‖σ c‖ = |((Algebra.norm ℚ c : ℚ) : ℝ)| := by
    rw [← norm_prod, h2, ← h]
    simp [Complex.norm_ratCast]
  rw [← hprod, Real.log_prod (fun σ _ => hne σ)]

end ReciprocityTheory.MultiplicativeHeights
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric

def BlockPoly (k n : ℕ) (a : Fin k → ℕ) (F : (Fin k → Fin n → ℂ) → ℂ) : Prop :=
  Continuous F ∧ ∀ (b : Fin k) (p : Fin k → Fin n → ℂ), ∃ g : MvPolynomial (Fin n) ℂ,
    g.IsHomogeneous (a b) ∧ ∀ w, F (Function.update p b w) = MvPolynomial.eval w g

def onSpheres {k n : ℕ} (F : (Fin k → Fin n → ℂ) → ℂ) (z : Fin k → UnitSphereC n) : ℂ :=
  F fun b => spherePoint (z b)

theorem BlockPoly.restrict {k n : ℕ} {a : Fin (k + 1) → ℕ} {F : (Fin (k + 1) → Fin n → ℂ) → ℂ}
    (hF : BlockPoly (k + 1) n a F) (v : Fin n → ℂ) :
    BlockPoly k n (fun j => a j.succ) (fun p => F (Fin.cons v p)) := by
  refine ⟨hF.1.comp (continuous_const.finCons continuous_id), fun b p => ?_⟩
  obtain ⟨g, hg, hgF⟩ := hF.2 b.succ (Fin.cons v p)
  refine ⟨g, hg, fun w => ?_⟩
  simp only
  rw [Fin.cons_update]
  exact hgF w

theorem blockPoly_claim (hSJ : SJStatement) (n : ℕ) : ∀ (k : ℕ) (a : Fin k → ℕ)
    (F : (Fin k → Fin n → ℂ) → ℂ), BlockPoly k n a F → ∀ z0 : Fin k → UnitSphereC n,
    onSpheres F z0 ≠ 0 →
    Integrable (fun z => Real.log ‖onSpheres F z‖) (Measure.pi fun _ : Fin k => sphereProb n) ∧
      Measure.pi (fun _ : Fin k => sphereProb n) {z | onSpheres F z = 0} = 0 := by
  haveI : IsFiniteMeasure (sphereProb n) := by unfold sphereProb; infer_instance
  intro k
  induction k with
  | zero =>
    intro a F hF z0 hz0
    have hconst : ∀ z : Fin 0 → UnitSphereC n, onSpheres F z = onSpheres F z0 := by
      intro z
      unfold onSpheres
      congr 1
      funext b
      exact b.elim0
    refine ⟨?_, ?_⟩
    · simp_rw [hconst]
      exact integrable_const _
    · simp_rw [hconst]
      simp [hz0]
  | succ k ih =>
    intro a F hF z0 hz0
    set μ := sphereProb n with hμ
    set ν := Measure.pi fun _ : Fin k => sphereProb n with hν
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => UnitSphereC n) 0
    have mp : MeasurePreserving e (Measure.pi fun _ : Fin (k + 1) => sphereProb n) (μ.prod ν) :=
      measurePreserving_piFinSuccAbove (fun _ => sphereProb n) 0
    let e2 := e.trans MeasurableEquiv.prodComm
    have mp2 : MeasurePreserving e2 (Measure.pi fun _ : Fin (k + 1) => sphereProb n) (ν.prod μ) :=
      (Measure.measurePreserving_swap).comp mp
    have hcont : Continuous (onSpheres F : (Fin (k + 1) → UnitSphereC n) → ℂ) :=
      hF.1.comp (continuous_pi fun b => (continuous_spherePoint n).comp (continuous_apply b))
    let H : (Fin k → UnitSphereC n) × UnitSphereC n → ℂ := fun q => onSpheres F (e2.symm q)
    have hHm : Measurable H := hcont.measurable.comp e2.symm.measurable
    have hsymm : ∀ z' w, e2.symm (z', w) = Fin.cons w z' := by
      intro z' w
      simp [e2, e, MeasurableEquiv.prodComm, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNth_zero']
    have hH : ∀ z' w, H (z', w) = F (Fin.cons (spherePoint w) (fun b => spherePoint (z' b))) := by
      intro z' w
      simp only [H, onSpheres, hsymm]
      congr 1
      funext b
      refine Fin.cases ?_ (fun j => ?_) b <;> simp
    have hcomp : ∀ z, onSpheres F z = H (e2 z) := by
      intro z
      simp only [H, MeasurableEquiv.symm_apply_apply]
    set v0 := spherePoint (z0 0) with hv0
    have hR := hF.restrict v0
    have hG : ∀ z', onSpheres (fun p => F (Fin.cons v0 p)) z' = H (z', z0 0) := by
      intro z'
      rw [hH]
      rfl
    have hz0' : onSpheres (fun p => F (Fin.cons v0 p)) (fun j => z0 j.succ) ≠ 0 := by
      simp only [onSpheres] at hz0 ⊢
      convert hz0 using 2
      funext b
      refine Fin.cases ?_ (fun j => ?_) b <;> simp [v0]
    obtain ⟨ihInt, ihNull⟩ := ih _ _ hR _ hz0'
    simp_rw [hG] at ihInt ihNull
    have hgood : ∀ᵐ z' ∂ν, H (z', z0 0) ≠ 0 := by
      rw [ae_iff]
      simpa using ihNull
    have hslice : ∀ z', H (z', z0 0) ≠ 0 →
        Integrable (fun w => Real.log ‖H (z', w)‖) μ ∧
        Real.log ‖H (z', z0 0)‖ - (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ) ≤
          ∫ w, Real.log ‖H (z', w)‖ ∂μ ∧ μ {w | H (z', w) = 0} = 0 := by
      intro z' hz'
      obtain ⟨g, hg, hgF⟩ := hF.2 0 (Fin.cons 0 (fun b => spherePoint (z' b)))
      have hHw : ∀ w, H (z', w) = MvPolynomial.eval (spherePoint w) g := by
        intro w
        rw [hH, ← hgF, Fin.update_cons_zero]
      have hu : ‖(z0 0 : EuclideanSpace ℂ (Fin n))‖ = 1 := norm_eq_of_mem_sphere _
      have hgu : MvPolynomial.eval (WithLp.ofLp (z0 0 : EuclideanSpace ℂ (Fin n))) g ≠ 0 := by
        rw [hHw] at hz'
        exact hz'
      obtain ⟨hI, hL⟩ := hSJ n (a 0) g _ hg hu hgu
      have hN := sphere_zero_null hSJ g hg _ hu hgu
      simp_rw [hHw]
      exact ⟨hI, hL, hN⟩
    obtain ⟨C, hC⟩ : ∃ C, ∀ z, ‖onSpheres F z‖ ≤ C := by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
      exact ⟨C, fun z => hC z (Set.mem_univ _)⟩
    set M := Real.log (max C 1) with hMdef
    have hM0 : 0 ≤ M := Real.log_nonneg (le_max_right _ _)
    have hLM : ∀ q, Real.log ‖H q‖ ≤ M := by
      intro q
      rcases (norm_nonneg (H q)).eq_or_lt with h0 | hpos
      · rw [← h0, Real.log_zero]
        exact hM0
      · exact Real.log_le_log hpos ((hC _).trans (le_max_left _ _))
    have habs : ∀ q, ‖Real.log ‖H q‖‖ ≤ 2 * M - Real.log ‖H q‖ := by
      intro q
      rw [Real.norm_eq_abs]
      have := hLM q
      rcases le_total 0 (Real.log ‖H q‖) with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_nonpos h]; linarith
    have hfm : AEStronglyMeasurable (fun q => Real.log ‖H q‖) (ν.prod μ) :=
      (Real.measurable_log.comp hHm.norm).aestronglyMeasurable
    have hInt2 : Integrable (fun q => Real.log ‖H q‖) (ν.prod μ) := by
      rw [integrable_prod_iff hfm]
      refine ⟨hgood.mono fun z' hz' => (hslice z' hz').1, ?_⟩
      refine Integrable.mono'
        (g := fun z' => ∫ _w, (2 * M) ∂μ -
          (Real.log ‖H (z', z0 0)‖ - (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ)))
        ((integrable_const _).sub (ihInt.sub (integrable_const _)))
        hfm.norm.integral_prod_right' ?_
      filter_upwards [hgood] with z' hz'
      obtain ⟨hI, hL, -⟩ := hslice z' hz'
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc ∫ w, ‖Real.log ‖H (z', w)‖‖ ∂μ ≤ ∫ w, (2 * M - Real.log ‖H (z', w)‖) ∂μ :=
            integral_mono hI.norm ((integrable_const _).sub hI) (fun w => habs _)
        _ = ∫ _w, (2 * M) ∂μ - ∫ w, Real.log ‖H (z', w)‖ ∂μ :=
            integral_sub (integrable_const _) hI
        _ ≤ _ := by linarith
    have hNull2 : (ν.prod μ) {q | H q = 0} = 0 := by
      have hms : MeasurableSet {q | H q = 0} := hHm (measurableSet_singleton 0)
      rw [Measure.measure_prod_null hms]
      filter_upwards [hgood] with z' hz'
      simpa [Set.preimage] using (hslice z' hz').2.2
    refine ⟨?_, ?_⟩
    · have h1 : (fun z => Real.log ‖onSpheres F z‖) = (fun q => Real.log ‖H q‖) ∘ e2 := by
        funext z
        simp only [Function.comp_apply]
        rw [hcomp z]
      rw [h1, mp2.integrable_comp_emb e2.measurableEmbedding]
      exact hInt2
    · have h1 : {z | onSpheres F z = 0} = e2 ⁻¹' {q | H q = 0} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_preimage]
        rw [hcomp z]
      rw [h1, mp2.measure_preimage_emb e2.measurableEmbedding]
      exact hNull2

end ReciprocityTheory.MultiplicativeHeights
end
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open Module Submodule

theorem det_subtype_comp_associated_prod {R M : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι R M) (N : Submodule R M)
    (h : finrank R N = finrank R M) (e : M ≃ₗ[R] N) :
    Associated (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N)))
      (∏ i, smithNormalFormCoeffs b h i) := by
  first | exact Bl.general_b_fact_tail.goal1 .. | (apply Bl.general_b_fact_tail.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_tail.goal1 <;> assumption)

theorem addVal_prod {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ι : Type*} (s : Finset ι) (a : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal O (a i) := by
  first | exact Bl.general_b_fact'''''''.goal1 .. | (apply Bl.general_b_fact'''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact'''''''.goal1 <;> assumption)

theorem gaugeSplitting_holds : NormLengthStatement := by
  intro O B _ _ _ _ _ _ _ _ g hg
  classical
  have : Module.Free O B := Module.free_iff_isTorsionFree.mpr inferInstance
  set b := Module.Free.chooseBasis O B
  set I : Ideal B := Ideal.span ({g} : Set B)
  have hI : I ≠ ⊥ := by simpa [I] using hg
  have h := Ideal.finrank_eq_finrank b I hI
  have hlen : Module.length O (B ⧸ I) =
      ∑ i, IsDiscreteValuationRing.addVal O (smithNormalFormCoeffs b h i) := by
    rw [(Ideal.quotientEquivPiSpan I b hI).length_eq, Module.length_pi_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Ring.ord_eq_addVal]
    rfl
  have hdet : Associated (Algebra.norm O g) (∏ i, smithNormalFormCoeffs b h i) := by
    rw [Algebra.norm_apply]
    have key := det_subtype_comp_associated_prod b (I.restrictScalars O) h
      (b.equiv (Ideal.basisSpanSingleton b hg) (Equiv.refl _))
    convert key using 2
    refine b.ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
    have h1 := Basis.equiv_apply (b := b) (b' := Ideal.basisSpanSingleton b hg) (e := Equiv.refl _) i
    refine Eq.trans ?_ (congrArg Subtype.val h1).symm
    rw [Equiv.refl_apply, Ideal.basisSpanSingleton_apply]
    rfl
  rw [hlen, ← addVal_prod, ← Ring.ord_eq_addVal, ← Ring.ord_eq_addVal]
  exact Ring.ord_eq_of_associated hdet

end ReciprocityTheory.MultiplicativeHeights
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate Module
open scoped ComplexOrder

def ballRatio (r : ℕ) : ℝ := (1 + 1 / (7 * (r : ℝ))) / (1 - 1 / (7 * (r : ℝ)))

def signMat (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun k : Fin r => sgn p k

def BoundedBallStatement : Prop :=
  ∀ (r p : ℕ) (H : Matrix (Fin r) (Fin r) ℂ) (s : ℝ),
    H.PosDef → H * signMat p r * H = signMat p r → 0 ≤ s → s < 1 →
    (∀ u : Fin r → ℂ, signMat p r *ᵥ (H *ᵥ u) = u → negSq p u ≤ s ^ 2 * posSq p u) →
    ∀ u : Fin r → ℂ, hq H u ≤ (1 + s) / (1 - s) * normSq u ∧
      normSq u ≤ (1 + s) / (1 - s) * hq H u

def NoContraction {K : Type} [Field K] [NumberField K] {r : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  ∀ N : Matrix (Fin r) (Fin r) K, (∀ x ∈ L, N *ᵥ x ∈ L) →
    (∀ (σ : K →+* ℂ) (u : Fin r → ℂ), u ≠ 0 → hq (H σ) (N.map σ *ᵥ u) < hq (H σ) u) → N = 0

end ReciprocityTheory.MultiplicativeHeights
end
end
