module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem of_lmul (a : Matrix (Fin n) (Fin n) (Rinf E)) (x : Lie E n) :
    lmul (toL a) x = toL (a * Matrix.of x) := rfl

private theorem lmul_one_add (a : Matrix (Fin n) (Fin n) (Rinf E)) (x : Lie E n) :
    lmul (toL (1 + a)) x = x + lmul (toL a) x := by
  rw [of_lmul, of_lmul, add_mul, one_mul]; rfl

private theorem exists_bil {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : V →ₗ[ℝ] Matrix (Fin n) (Fin n) (Rinf E)) :
    ∃ B : V →L[ℝ] Lie E n →L[ℝ] Lie E n, ∀ u x, B u x = lmul (toL (L u)) x := by
  let B0 : V →ₗ[ℝ] Lie E n →L[ℝ] Lie E n :=
    { toFun := fun u => lmul (toL (L u))
      map_add' := fun u v => by
        ext1 x
        rw [ContinuousLinearMap.add_apply, of_lmul, of_lmul, of_lmul, map_add (f := _), add_mul]; rfl
      map_smul' := fun c u => by
        ext1 x
        rw [ContinuousLinearMap.smul_apply, of_lmul, of_lmul, map_smul, smul_mul_assoc]; rfl }
  exact ⟨LinearMap.toContinuousLinearMap B0, fun _ _ => rfl⟩

private theorem isUnit_of_inj (a : Matrix (Fin n) (Fin n) (Rinf E)) (h : ∀ y : Lie E n, lmul (toL a) y = 0 → y = 0) :
    IsUnit a := by
  have hi : Function.Injective (LinearMap.mulLeft ℝ a) :=
    (injective_iff_map_eq_zero _).2 fun y hy => h (toL y) hy
  obtain ⟨b, hb⟩ := LinearMap.injective_iff_surjective.1 hi 1
  exact IsUnit.of_mul_eq_one b hb

private noncomputable def colL (m : Fin n) : EuclideanSpace ℝ (Fin n × InfinitePlace E) →ₗ[ℝ] Matrix (Fin n) (Fin n) (Rinf E) where
  toFun u := Matrix.of fun i j => if i ≤ m ∧ j.val = m.val + 1 then (fun v => u (i, v)) else 0
  map_add' u v := by
    ext i j w
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c u := by
    ext i j w
    simp only [Matrix.of_apply, Matrix.smul_apply]
    split_ifs <;> simp

private noncomputable def rowL (m : Fin n) : EuclideanSpace ℝ (Fin n × InfinitePlace E) →ₗ[ℝ] Matrix (Fin n) (Fin n) (Rinf E) where
  toFun u := Matrix.of fun i j => if i = m ∧ j ≤ m then (fun v => -u (j, v)) else 0
  map_add' u v := by
    ext i j w
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp [add_comm]
  map_smul' c u := by
    ext i j w
    simp only [Matrix.of_apply, Matrix.smul_apply]
    split_ifs <;> simp

private noncomputable def eta (m : Fin n) (ξ : Fin n → Rinf E) : EuclideanSpace ℝ (Fin n × InfinitePlace E) :=
  WithLp.toLp 2 fun z => if z.1 ≤ m then -ξ z.1 z.2 else 0

private theorem colL_sq (m : Fin n) (u : EuclideanSpace ℝ (Fin n × InfinitePlace E)) : colL m u * colL m u = 0 := by
  ext1 i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [colL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
  by_cases h : k ≤ m
  · rw [if_neg, zero_mul]
    rintro ⟨-, h'⟩
    rw [Fin.le_def] at h
    omega
  · rw [if_neg (fun h' : k ≤ m ∧ _ => h h'.1), mul_zero]

private theorem rowM_eq (m : Fin n) (ξ : Fin n → Rinf E) :
    rowM m ξ = 1 + rowL m (eta m ξ - eta m ((1 : Matrix (Fin n) (Fin n) (Rinf E)) m)) := by
  ext i j w
  simp only [rowM, rowL, eta, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply, Matrix.add_apply]
  split_ifs with h
  · obtain ⟨rfl, h⟩ := h
    simp [h]
  · simp

private theorem inner_eta (m : Fin n) (ξ : Fin n → Rinf E) (u : EuclideanSpace ℝ (Fin n × InfinitePlace E)) :
    ⟪eta m ξ, u⟫ = -∑ v, dotLe m ξ (fun j v => u (j, v)) v := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type_right, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [dotLe, Finset.sum_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j ≤ m <;> simp [eta, h, mul_comm]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Af.Smo.archStep :
    UpperTheory.V.Af.Smo.SchTw → UpperTheory.V.Af.Smo.PftSch → UpperTheory.V.Af.Smo.BetaSch → UpperTheory.V.Af.Smo.BetaInt → UpperTheory.V.Af.Smo.ArchStep := by
  intro h1 h2 h3 h4 E _ _ n m _
  obtain ⟨B, hB⟩ := exists_bil (colL (E := E) m)
  obtain ⟨A, hA⟩ := exists_bil (rowL (E := E) m)
  have hBB : ∀ u x, B u (B u x) = 0 := fun u x => by
    rw [hB, hB, of_lmul, of_lmul]
    change toL (colL m u * (colL m u * Matrix.of x)) = 0
    rw [← mul_assoc, colL_sq, zero_mul]; rfl
  obtain ⟨h, he, hu, hG⟩ := h1 _ _ A (eta m ((1 : Matrix (Fin n) (Fin n) (Rinf E)) m))
  have hrow : ∀ ξ y, y + A (eta m ξ - eta m ((1 : Matrix (Fin n) (Fin n) (Rinf E)) m)) y = lmul (toL (rowM m ξ)) y :=
    fun ξ y => by rw [rowM_eq, lmul_one_add, hA]
  refine ⟨fun ξ => h (eta m ξ), he, fun ξ hξ => isUnit_of_inj _ fun y hy => hu _ hξ y (by rw [hrow, hy]), fun α => ?_⟩
  obtain ⟨G, hG⟩ := hG α
  obtain ⟨K, hK⟩ := h2 _ _ G
  obtain ⟨K', β, hK', hβ⟩ := h3 _ _ B hBB K
  refine ⟨β, fun w ξ hw hb hw' => ?_⟩
  haveI : (volume : Measure (Rinf E)).IsAddHaarMeasure := isAddHaarMeasure_volume_pi _
  haveI : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have := h4 _ _ (volume : Measure (Lie E n)) B hBB G K K' hK hK' w (eta m ξ) hw hb fun u x => by
    rw [hB, ← lmul_one_add, inner_eta]
    exact hw' (fun j v => u (j, v)) x
  simp only [hβ]
  rw [this, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hG, hrow]
  ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem conv_left {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (f : GA E n → ℂ)
    (α : Lie E n → ℂ) (z : GA E n) (h : ∀ g, f (z * g) = f g) (g : GA E n) : Af.Smo.conv f α (z * g) = Af.Smo.conv f α g := by
  have e : chart f (z * g) = chart f g := by
    funext x
    unfold chart
    split_ifs with hx
    · rw [mul_assoc, h]
    · rfl
  unfold Af.Smo.conv
  rw [e]

set_option synthInstance.maxHeartbeats 200000 in
private theorem zero_of_sq {E : Type} [Field E] [NumberField E] {n : ℕ} (μ : Measure (Reduction.normOneGL (K := E) (n := n)))
    [μ.IsHaarMeasure] (F : AdelicGLn.AdelicGL E n → ℂ) (hc : Continuous F) (C : ℝ) (hC : ∀ g, ‖F g‖ ≤ C)
    (h : IsLeftInvariant F)
    (h0 : ∫ q, starRingEnd ℂ (CuspidalSpectrum.cuspQuot h q) * CuspidalSpectrum.cuspQuot h q
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) = 0) :
    ∀ y ∈ Reduction.normOneGL (K := E) (n := n), F y = 0 := by
  have := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := n) μ
  have hq := CuspidalSpectrum.continuous_cuspQuot h hc
  have hb : ∀ q, ‖CuspidalSpectrum.cuspQuot h q‖ ≤ C := fun q => by
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    exact hC _
  have h1 : ∫ q, ‖CuspidalSpectrum.cuspQuot h q‖ ^ 2
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) = 0 := by
    rw [← Complex.ofReal_eq_zero, ← integral_complex_ofReal, ← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [Complex.conj_mul', Complex.ofReal_pow]
  have hi : Integrable (fun q => ‖CuspidalSpectrum.cuspQuot h q‖ ^ 2)
      (RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) :=
    Integrable.of_bound (hq.norm.pow 2).aestronglyMeasurable (C ^ 2) (Filter.Eventually.of_forall fun q => by
      rw [norm_pow, norm_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb q) 2)
  have h2 := (integral_eq_zero_iff_of_nonneg (fun q => sq_nonneg _) hi).1 h1
  have h3 := QuasiMeasurePreserving.ae_eq_comp (RightCosetSpace.quasiMeasurePreserving_mk (Reduction.rationalGLOne (K := E) (n := n)) μ) h2
  have h4 := (Continuous.ae_eq_iff_eq μ (f := fun y : Reduction.normOneGL (K := E) (n := n) => ‖F y‖ ^ 2)
    ((hc.comp continuous_subtype_val).norm.pow 2) continuous_const).1 h3
  intro y hy
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (congrFun h4 ⟨y, hy⟩))

theorem UpperTheory.V.Af.Smo.orthConv :
    UpperTheory.V.Af.Smo.OrthStep → UpperTheory.V.Af.Smo.ConvCont → UpperTheory.V.Af.Smo.OrthConv := by
  intro hS hC E _ _ _ n μ _ φ φ' hφ hφ' ho β β' e
  obtain ⟨C, hb⟩ := exists_norm_le_of_mem_centralCuspForms hφ
  obtain ⟨C', hb'⟩ := exists_norm_le_of_mem_centralCuspForms hφ'
  have l : IsLeftInvariant (Af.Smo.conv φ.1 β) := fun γ g => conv_left _ _ _ (φ.2.1.isLeftInvariant γ) g
  have l' : IsLeftInvariant (Af.Smo.conv φ'.1 β') := fun γ g => conv_left _ _ _ (φ'.2.1.isLeftInvariant γ) g
  obtain ⟨hc, D, hD⟩ := hC E n φ'.1 φ'.2.1.continuous ⟨C', hb'⟩ β'
  have s1 : ∀ g, ∫ q, starRingEnd ℂ (quotTr φ g q) * CuspidalSpectrum.cuspQuot l' q
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) = 0 := fun g =>
    hS E n μ φ'.1 φ'.2.1.continuous ⟨C', hb'⟩ φ'.2.1.isLeftInvariant (fun q => starRingEnd ℂ (quotTr φ g q))
      (Complex.continuous_conj.comp (continuous_quotTr φ g))
      ⟨C, fun q => by
        obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
        rw [Complex.norm_conj]
        exact hb _⟩
      (fun g' _ => ho g g') β' l'
  have s2 := hS E n μ φ.1 φ.2.1.continuous ⟨C, hb⟩ φ.2.1.isLeftInvariant
    (fun q => starRingEnd ℂ (CuspidalSpectrum.cuspQuot l' q))
    (Complex.continuous_conj.comp (CuspidalSpectrum.continuous_cuspQuot l' hc))
    ⟨D, fun q => by
      obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
      rw [Complex.norm_conj]
      exact hD _⟩
    (fun g _ => by
      have h := congrArg (starRingEnd ℂ) (s1 g)
      rw [← integral_conj, map_zero] at h
      refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)) h
      simp only [map_mul, Complex.conj_conj]
      exact mul_comm _ _) β l
  have e' : CuspidalSpectrum.cuspQuot l = CuspidalSpectrum.cuspQuot l' :=
    CuspidalSpectrum.cuspQuot_surj_eq l l' fun y => congrFun e _
  rw [e'] at s2
  have z := zero_of_sq μ _ hc D hD l' s2
  rw [e]
  funext x
  obtain ⟨s, y, hy, rfl⟩ := CuspidalSpectrum.exists_centralSection_mul_mem_normOneGL x
  exact (conv_left _ _ _ (hφ' s) y).trans (z y hy)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem exists_schwartz_integral_eq_one {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (F : X → ℂ) (U : Set X) (x₀ : X)
    (hU : U ∈ 𝓝 x₀) (hF : ContinuousOn F U) (h0 : F x₀ ≠ 0) : ∃ α : 𝓢(X, ℂ), ∫ x, F x * α x ∂μ = 1 := by
  have hc : ContinuousAt (fun x => (F x / F x₀).re) x₀ :=
    Complex.continuous_re.continuousAt.comp ((hF.continuousAt hU).div_const _)
  have hp : ∀ᶠ x in 𝓝 x₀, 0 < (F x / F x₀).re :=
    hc.eventually (lt_mem_nhds (by simp [div_self h0]))
  obtain ⟨r, hr, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (interior_mem_nhds.2 hU) hp)
  let b : ContDiffBump x₀ := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hs : tsupport b = Metric.closedBall x₀ r := b.tsupport_eq
  have hs' : Function.support b = Metric.ball x₀ r := b.support_eq
  have hG : Continuous fun x => b x • (F x / F x₀) := by
    refine continuous_of_tsupport fun x hx => ?_
    have hx' : x ∈ Metric.closedBall x₀ r := hs ▸ tsupport_smul_subset_left _ _ hx
    exact b.continuous.continuousAt.smul ((hF.continuousAt (mem_interior_iff_mem_nhds.1 (hb hx').1)).div_const _)
  have hK : HasCompactSupport fun x => b x • (F x / F x₀) := b.hasCompactSupport.smul_right
  have hI : Integrable (fun x => b x • (F x / F x₀)) μ := hG.integrable_of_hasCompactSupport hK
  have hpos : 0 < ∫ x, (b x • (F x / F x₀)).re ∂μ := by
    refine (Complex.continuous_re.comp hG).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x₀)
      (hK.comp_left (g := Complex.re) rfl) (fun x => ?_) ?_
    · by_cases hx : b x = 0
      · simp [hx]
      · have hx' : x ∈ Metric.closedBall x₀ r := Metric.ball_subset_closedBall (hs' ▸ hx)
        have h1 : 0 < (F x / F x₀).re := (hb hx').2
        simpa using mul_nonneg b.nonneg h1.le
    · have h1 : b x₀ = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
      simp [h1, div_self h0]
  have hne : ∫ x, b x • (F x / F x₀) ∂μ ≠ 0 := by
    intro h
    have h2 := integral_re hI
    rw [h] at h2
    simp only [RCLike.re_to_complex, Complex.zero_re] at h2
    exact hpos.ne' h2
  set c := ∫ x, b x • (F x / F x₀) ∂μ with hc'
  have hd : ContDiff ℝ ∞ fun x => b x • ((F x₀)⁻¹ * c⁻¹) := b.contDiff.smul contDiff_const
  have hk : HasCompactSupport fun x => b x • ((F x₀)⁻¹ * c⁻¹) := b.hasCompactSupport.smul_right
  refine ⟨hk.toSchwartzMap hd, ?_⟩
  have e : ∀ x, F x * (hk.toSchwartzMap hd) x = (b x • (F x / F x₀)) * c⁻¹ := fun x => by
    change F x * (b x • ((F x₀)⁻¹ * c⁻¹)) = _
    simp only [Complex.real_smul, div_eq_mul_inv]
    ring
  simp only [e]
  rw [integral_mul_const, ← hc', mul_inv_cancel₀ hne]

theorem UpperTheory.V.Af.Smo.seedConv :
    UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.SeedConv := by
  intro h E _ _ _ n W hW y hy
  haveI i1 : (volume : Measure (Rinf E)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  refine exists_schwartz_integral_eq_one volume (chart W 1) (invSet E n) (toL y.val) ?_ ?_ ?_
  · exact TR.isOpen_invSet.mem_nhds (TR.val_mem_invSet y)
  · exact (h E n W hW).1.comp (f := fun x => ((1 : GA E n), x)) (by fun_prop) fun x hx => ⟨trivial, hx⟩
  · rw [TR.chart_val, one_mul]
    exact hy
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.schTw :
    UpperTheory.V.Af.Smo.SchTensor → UpperTheory.V.Af.Smo.SchTw := by
  intro hT V M _ _ _ _ _ _ A e
  obtain ⟨δ, hδ, hAδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ‖A‖ * δ ≤ 1 / 2 := by
    refine ⟨1 / (2 * (‖A‖ + 1)), by positivity, ?_⟩
    have h0 : 0 ≤ ‖A‖ := norm_nonneg _
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hball : ∀ ξ ∈ Metric.ball e δ, ‖A (ξ - e)‖ ≤ 1 / 2 := by
    intro ξ hξ
    calc ‖A (ξ - e)‖ ≤ ‖A‖ * ‖ξ - e‖ := A.le_opNorm _
      _ ≤ ‖A‖ * δ := by
        gcongr
        rw [← dist_eq_norm]
        exact (Metric.mem_ball.mp hξ).le
      _ ≤ 1 / 2 := hAδ
  let φ : ContDiffBump e := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  let χ : ContDiffBump e := ⟨δ / 2, δ, by positivity, by linarith⟩
  let g : V → (M →L[ℝ] M) := fun ξ => χ ξ • A (ξ - e)
  have hsmall : ∀ ξ : V, ‖g ξ‖ ≤ 1 / 2 := by
    intro ξ
    by_cases hξ : χ ξ = 0
    · simp [g, hξ]
    · have hmem : ξ ∈ Metric.ball e δ := by
        have h1 : ξ ∈ Function.support χ := hξ
        rwa [χ.support_eq] at h1
      simp only [g]
      rw [norm_smul, Real.norm_of_nonneg χ.nonneg]
      calc χ ξ * ‖A (ξ - e)‖ ≤ 1 * (1 / 2) := by
            gcongr
            · exact χ.le_one
            · exact hball ξ hmem
        _ = 1 / 2 := by norm_num
  refine ⟨fun ξ => ((φ ξ : ℝ) : ℂ), ?_, ?_, ?_⟩
  · have h1 : φ e = 1 := φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)
    simp [h1]
  · intro ξ hξ y hy
    have hφ : φ ξ ≠ 0 := by
      intro h1
      apply hξ
      simp [h1]
    have hmem : ξ ∈ Metric.ball e δ := by
      have h1 : ξ ∈ Function.support φ := hφ
      rw [φ.support_eq] at h1
      exact Metric.ball_subset_ball (show δ / 2 ≤ δ by linarith) h1
    have h2 : y = -(A (ξ - e)) y := eq_neg_of_add_eq_zero_left hy
    have h3 : ‖y‖ ≤ 1 / 2 * ‖y‖ := by
      calc ‖y‖ = ‖(A (ξ - e)) y‖ := by
            conv_lhs => rw [h2]
            exact norm_neg _
        _ ≤ ‖A (ξ - e)‖ * ‖y‖ := (A (ξ - e)).le_opNorm y
        _ ≤ 1 / 2 * ‖y‖ := mul_le_mul_of_nonneg_right (hball ξ hmem) (norm_nonneg _)
    have h4 : ‖y‖ = 0 := le_antisymm (by linarith [norm_nonneg y]) (norm_nonneg y)
    exact norm_eq_zero.mp h4
  · intro α
    have hh : ContDiff ℝ ∞ (fun ξ => ((φ ξ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp φ.contDiff
    have hhc : HasCompactSupport (fun ξ => ((φ ξ : ℝ) : ℂ)) :=
      φ.hasCompactSupport.comp_left Complex.ofReal_zero
    obtain ⟨G0, hG0⟩ := hT V M (fun ξ => ((φ ξ : ℝ) : ℂ)) hh hhc α
    have hg : Function.HasTemperateGrowth g := by
      apply HasCompactSupport.hasTemperateGrowth
      · exact χ.hasCompactSupport.smul_right (f' := fun ξ => A (ξ - e))
      · exact χ.contDiff.smul (A.contDiff.comp (contDiff_id.sub contDiff_const))
    let Φ : V × M → V × M := fun p => p + ContinuousLinearMap.inr ℝ V M (g p.1 p.2)
    have hΦ : Function.HasTemperateGrowth Φ := by
      have h1 : Function.HasTemperateGrowth (fun p : V × M => g p.1) :=
        hg.comp (ContinuousLinearMap.fst ℝ V M).hasTemperateGrowth
      have h2 : Function.HasTemperateGrowth (fun p : V × M => g p.1 p.2) :=
        (ContinuousLinearMap.id ℝ (M →L[ℝ] M)).bilinear_hasTemperateGrowth h1
          (ContinuousLinearMap.snd ℝ V M).hasTemperateGrowth
      exact Function.HasTemperateGrowth.add Function.HasTemperateGrowth.id
        ((ContinuousLinearMap.inr ℝ V M).hasTemperateGrowth.comp h2)
    have hΦp : ∀ p : V × M, Φ p = (p.1, p.2 + g p.1 p.2) := by
      intro p
      ext <;> simp [Φ]
    have hup : ∃ (k : ℕ) (C : ℝ), ∀ p, ‖p‖ ≤ C * (1 + ‖Φ p‖) ^ k := by
      refine ⟨1, 2, fun p => ?_⟩
      have e1 : ‖p.2‖ ≤ ‖p.2 + g p.1 p.2‖ + ‖g p.1 p.2‖ := by
        simpa using norm_sub_le (p.2 + g p.1 p.2) (g p.1 p.2)
      have e2 : ‖g p.1 p.2‖ ≤ 1 / 2 * ‖p.2‖ :=
        ((g p.1).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hsmall _) (norm_nonneg _))
      have e3 : ‖p.2 + g p.1 p.2‖ ≤ ‖Φ p‖ := by
        rw [hΦp]
        exact norm_snd_le (p.1, p.2 + g p.1 p.2)
      have e4 : ‖p.1‖ ≤ ‖Φ p‖ := by
        rw [hΦp]
        exact norm_fst_le (p.1, p.2 + g p.1 p.2)
      rw [pow_one]
      refine norm_prod_le_iff.mpr ⟨?_, ?_⟩ <;> nlinarith [norm_nonneg (Φ p), norm_nonneg p.2]
    refine ⟨SchwartzMap.compCLM ℂ hΦ hup G0, fun ξ y => ?_⟩
    rw [SchwartzMap.compCLM_apply, Function.comp_apply, hΦp, hG0]
    by_cases hφ : φ ξ = 0
    · simp [hφ]
    · have hmem : ξ ∈ Metric.closedBall e χ.rIn := by
        have h1 : ξ ∈ Function.support φ := hφ
        rw [φ.support_eq] at h1
        exact Metric.ball_subset_closedBall h1
      simp [g, χ.one_of_mem_closedBall hmem]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.convNice :
    UpperTheory.V.Af.Smo.ConvCont → UpperTheory.V.Af.Smo.ConvFub → UpperTheory.V.Af.Smo.ConvNice := by
  intro hc hf E _ _ _ n f hN α
  obtain ⟨h1, h2⟩ := hc E n f hN.cont hN.bdd α
  refine ⟨⟨h1, h2, ?_, ?_, ?_⟩, ?_⟩
  · intro γ g
    have e : chart f (AdelicGLn.diagonal E n γ * g) = chart f g := by
      funext x
      simp only [chart, mul_assoc, hN.left γ]
    simp only [conv, e]
  · intro r hr hrn g
    haveI : IsFiniteMeasure ((unipMeasure E n r).restrict (unipFundamentalDomain E n r)) := by
      obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := n) (r := r)
      exact ⟨by
        rw [Measure.restrict_apply_univ]
        exact (measure_mono hDC).trans_lt hC.measure_lt_top⟩
    have h := hf E n f hN.cont hN.bdd α _ ((unipMeasure E n r).restrict (unipFundamentalDomain E n r))
      unipGL (fun _ => 1) continuous_unipGL continuous_const ⟨1, fun _ => by simp⟩ g
    simp only [mul_one] at h
    have e : (fun g' => ∫ x in unipFundamentalDomain E n r, f (unipGL x * g') ∂unipMeasure E n r) = fun _ => 0 :=
      funext fun g' => hN.cusp r hr hrn g'
    rw [constantTerm, h, e]
    simp [conv, chart]
  · obtain ⟨V, hV⟩ := hN.level
    refine ⟨V, fun g v hv => ?_⟩
    have e : (fun x => f (x * finGL E n v)) = f := funext fun x => hV x v hv
    rw [conv, ← TR.chart_rt_fin, e, conv]
  · funext g
    haveI : IsFiniteMeasure ((FourierWhittaker.vecMeasure E (FourierWhittaker.Pos n)).restrict
        (FourierWhittaker.vecDomain E (FourierWhittaker.Pos n))) :=
      ⟨by rw [Measure.restrict_apply_univ, FourierWhittaker.vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
    exact hf E n f hN.cont hN.bdd α _ ((FourierWhittaker.vecMeasure E (FourierWhittaker.Pos n)).restrict
        (FourierWhittaker.vecDomain E (FourierWhittaker.Pos n))) FourierWhittaker.uGL
      (fun X => (GroundTheory.Global.adelicChar E (-FourierWhittaker.supSum 0 X) : ℂ)) FourierWhittaker.continuous_uGL
      (continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp
        (FourierWhittaker.continuous_supSum 0).neg)) ⟨1, fun _ => (Circle.norm_coe _).le⟩ g
end
