module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle002
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle001
public import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.Analysis.Fourier.AddCircle
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice

@[expose] public section

section

open Complex Filter Topology

namespace GlobalTheory.ArtinKernel

theorem exists_glue {g : ℕ} {J : Type*} (D : J → Set (Fin g → ℂ))
    (G : J → (Fin g → ℂ) → ℂ) (hD : ∀ j, IsOpen (D j)) (hcov : ∀ z, ∃ j, z ∈ D j)
    (hG : ∀ j, DifferentiableOn ℂ (G j) (D j))
    (hc : ∀ j j' z, z ∈ D j → z ∈ D j' → G j z = G j' z) :
    ∃ F : (Fin g → ℂ) → ℂ, Differentiable ℂ F ∧ ∀ j z, z ∈ D j → F z = G j z := by
  choose k hk using hcov
  refine ⟨fun z => G (k z) z, fun z => ?_, fun j z hz => hc _ _ _ (hk z) hz⟩
  have hU : D (k z) ∈ 𝓝 z := (hD (k z)).mem_nhds (hk z)
  have hev : (fun w => G (k w) w) =ᶠ[𝓝 z] G (k z) := by
    filter_upwards [hU] with w hw
    exact hc _ _ _ (hk w) hw
  exact ((hG (k z)).differentiableAt hU).congr_of_eventuallyEq hev

theorem differentiable_fderiv {g : ℕ} {F : (Fin g → ℂ) → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (fderiv ℂ F) := differentiableOn_univ.mp (GlobalTheory.SCV.differentiableOn_fderiv isOpen_univ hF.differentiableOn)

theorem exists_linear_of_add_period {g : ℕ} {F : (Fin g → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {S : Set (Fin g → ℂ)} (hS : Submodule.span ℝ S = ⊤) (b : S → ℂ)
    (hb : ∀ (l : S) z, F (z + l) = F z + b l) :
    ∃ lam : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ l : S, b l = lam l := by
  have hD : Differentiable ℂ (fderiv ℂ F) := differentiable_fderiv hF
  have hper : ∀ z, ∀ l ∈ S, fderiv ℂ F (z + l) = fderiv ℂ F z := by
    intro z l hl
    have h1 : (fun w => F (w + l)) = fun w => F w + b ⟨l, hl⟩ := funext fun w => hb ⟨l, hl⟩ w
    rw [← fderiv_comp_add_right (f := F) l, h1, fderiv_add_const]
  have hconst : ∀ z, fderiv ℂ F z = fderiv ℂ F 0 := fun z =>
    GlobalTheory.entire_apply_eq_of_periodic_of_span_real hD hS hper z 0
  set L := fderiv ℂ F 0 with hL
  have hlin : ∀ z, F z = F 0 + L z := by
    intro z
    have hd : Differentiable ℂ (fun w => F w - L w) := hF.sub L.differentiable
    have h0 : ∀ w, fderiv ℂ (fun w => F w - L w) w = 0 := by
      intro w
      rw [fderiv_fun_sub (hF w) L.differentiableAt, L.fderiv, hconst w, sub_self]
    have := is_const_of_fderiv_eq_zero hd h0 z 0
    rw [map_zero, sub_zero] at this
    linear_combination this
  refine ⟨L.toLinearMap, fun l => ?_⟩
  have := hb l 0
  rw [zero_add, hlin l.1] at this
  simp only [ContinuousLinearMap.coe_coe]
  linear_combination -this

theorem exists_linear_of_mul_period {g : ℕ} {F : (Fin g → ℂ) → ℂ} (hF : Differentiable ℂ F)
    (h0 : ∀ z, F z ≠ 0) {S : Set (Fin g → ℂ)} (hS : Submodule.span ℝ S = ⊤) (b : S → ℂ)
    (hb : ∀ (l : S) z, F (z + l) = b l * F z) :
    ∃ lam : (Fin g → ℂ) →ₗ[ℂ] ℂ, ∀ l : S, b l = cexp (lam l) := by
  have hb0 : ∀ l : S, b l ≠ 0 := by
    intro l hl
    have := hb l 0
    rw [hl, zero_mul, zero_add] at this
    exact h0 _ this
  have hdF : ∀ (l : S) z, fderiv ℂ F (z + l) = b l • fderiv ℂ F z := by
    intro l z
    have h1 : (fun w => F (w + l)) = fun w => b l * F w := funext fun w => hb l w
    rw [← fderiv_comp_add_right (f := F) (l : Fin g → ℂ), h1, fderiv_const_mul (hF z)]
  set H : (Fin g → ℂ) → ((Fin g → ℂ) →L[ℂ] ℂ) := fun z => (F z)⁻¹ • fderiv ℂ F z with hH
  have hHd : Differentiable ℂ H := (hF.inv h0).smul (differentiable_fderiv hF)
  have hper : ∀ z, ∀ l ∈ S, H (z + l) = H z := by
    intro z l hl
    simp only [hH]
    rw [hb ⟨l, hl⟩ z, hdF ⟨l, hl⟩ z, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (hb0 _), mul_one]
  have hconst : ∀ z, H z = H 0 := fun z =>
    GlobalTheory.entire_apply_eq_of_periodic_of_span_real hHd hS hper z 0
  set L := H 0 with hL
  have hDF : ∀ w, fderiv ℂ F w = F w • L := by
    intro w
    rw [← hconst w, hH, smul_smul, mul_inv_cancel₀ (h0 w), one_smul]
  have hK : ∀ w, fderiv ℂ (fun z => F z * cexp (-L z)) w = 0 := by
    intro w
    have h2 : HasFDerivAt (fun z => F z * cexp (-L z))
        (F w • (cexp (-L w) • -L) + cexp (-L w) • fderiv ℂ F w) w :=
      (hF w).hasFDerivAt.mul L.hasFDerivAt.neg.cexp
    rw [h2.fderiv, hDF w]
    ext v
    simp only [add_apply, smul_apply, neg_apply, zero_apply, smul_eq_mul]
    ring
  have hKd : Differentiable ℂ (fun z => F z * cexp (-L z)) :=
    hF.mul (L.differentiable.neg.cexp)
  refine ⟨L.toLinearMap, fun l => ?_⟩
  have e1 := is_const_of_fderiv_eq_zero hKd hK (l : Fin g → ℂ) 0
  have e2 := hb l 0
  rw [zero_add] at e2
  rw [e2, map_zero, neg_zero, Complex.exp_zero, mul_one, mul_right_comm] at e1
  have e3 : b l * cexp (-L l) = 1 := by
    have := mul_right_cancel₀ (h0 0) (e1.trans (one_mul _).symm)
    exact this
  rw [Complex.exp_neg, mul_inv_eq_one₀ (Complex.exp_ne_zero _)] at e3
  simpa only [ContinuousLinearMap.coe_coe] using e3

section Artin

variable {R : Type} [CommRing R] [Algebra ℂ R] [IsLocalRing R] [Module.Finite ℂ R]

theorem exists_residue : ∃ ρ : R →ₐ[ℂ] ℂ, ∀ r, ρ r = 0 → r ∈ IsLocalRing.maximalIdeal R := by
  have hsurj := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := ℂ) (K := R ⧸ IsLocalRing.maximalIdeal R))
  let e : ℂ ≃ₐ[ℂ] R ⧸ IsLocalRing.maximalIdeal R := AlgEquiv.ofBijective (Algebra.ofId ℂ _) hsurj
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ _), fun r hr => ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h1 : e.symm (Ideal.Quotient.mk _ r) = 0 := hr
  have h2 := congrArg e h1
  rwa [AlgEquiv.apply_symm_apply, map_zero] at h2

theorem subsingleton_primeSpectrum : Subsingleton (PrimeSpectrum R) := by
  have : IsArtinianRing R := IsArtinianRing.of_finite ℂ R
  refine ⟨fun p q => PrimeSpectrum.ext ?_⟩
  rw [IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime p.asIdeal),
    IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime q.asIdeal)]

theorem exists_functional {ι : Type*} (δ : ι → R) (hδ : ∃ i, δ i ≠ 0) :
    ∃ lam : R →ₗ[ℂ] ℂ, (∃ i, lam (δ i) ≠ 0) ∧
      ∀ i, ∀ r ∈ IsLocalRing.maximalIdeal R, lam (r * δ i) = 0 := by
  classical
  set m := IsLocalRing.maximalIdeal R
  set N : Submodule ℂ R := Submodule.span ℂ {x | ∃ r ∈ m, ∃ i, x = r * δ i} with hN
  have hex : ∃ i, δ i ∉ N := by
    by_contra! hall
    set J : Ideal R := Ideal.span (Set.range δ) with hJ
    have hNJ : ∀ x ∈ N, x ∈ m • J := by
      intro x hx
      refine Submodule.span_induction (p := fun x _ => x ∈ m • J) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨r, hr, i, rfl⟩
        exact Submodule.smul_mem_smul hr (Ideal.subset_span ⟨i, rfl⟩)
      · exact zero_mem _
      · intro x y _ _ hx hy
        exact add_mem hx hy
      · intro c x _ hx
        exact Submodule.smul_of_tower_mem _ c hx
    have hle : J ≤ m • J := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hNJ _ (hall i)
    have : IsArtinianRing R := IsArtinianRing.of_finite ℂ R
    have hJ0 : J = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m J
      (IsNoetherian.noetherian J) hle
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)
    obtain ⟨i, hi⟩ := hδ
    apply hi
    have : δ i ∈ J := Ideal.subset_span ⟨i, rfl⟩
    rw [hJ0] at this
    exact (Submodule.mem_bot R).mp this
  obtain ⟨i, hi⟩ := hex
  obtain ⟨lam, hlam, hker⟩ := Submodule.exists_le_ker_of_notMem hi
  refine ⟨lam, ⟨i, hlam⟩, fun j r hr => ?_⟩
  exact hker (Submodule.subset_span ⟨r, hr, j, rfl⟩)


omit [IsLocalRing R] in
theorem differentiableOn_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E} {F G : E → R}
    (hF : ∀ lam : R →ₗ[ℂ] ℂ, DifferentiableOn ℂ (fun z => lam (F z)) S)
    (hG : ∀ lam : R →ₗ[ℂ] ℂ, DifferentiableOn ℂ (fun z => lam (G z)) S) (lam : R →ₗ[ℂ] ℂ) :
    DifferentiableOn ℂ (fun z => lam (F z * G z)) S := by
  classical
  set b := Module.Free.chooseBasis ℂ R
  have key : (fun z => lam (F z * G z)) = fun z =>
      ∑ j, ∑ i, b.coord i (F z) * b.coord j (G z) * lam (b i * b j) := by
    funext z
    conv_lhs => rw [← b.sum_repr (F z), ← b.sum_repr (G z)]

    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul,
    smul_eq_mul, Module.Basis.coord_apply]
  rw [key]
  refine DifferentiableOn.fun_sum fun j _ => DifferentiableOn.fun_sum fun i _ => ?_
  exact ((hF (b.coord i)).mul (hG (b.coord j))).mul_const _

end Artin

end GlobalTheory.ArtinKernel
end

section

open Complex Matrix Filter Topology MeasureTheory
open scoped BigOperators Real

namespace GlobalTheory

theorem apply_add_intCast_vec_of_unit_periods {ι R E : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] {F : (ι → R) → E} (hF : ∀ (i : ι) x, F (x + Pi.single i 1) = F x)
    (n : ι → ℤ) (x : ι → R) : F (x + fun i => (n i : R)) = F x := by
  first
  | exact @_root_.GlobalTheory.IntegerShiftSingle.main
  | exact _root_.GlobalTheory.IntegerShiftSingle.main
  | (apply _root_.GlobalTheory.IntegerShiftSingle.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerShiftSingle.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerShiftSingle.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerShiftSingle.main ..)

theorem setIntegral_unitCube_add_right_of_periodic {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : (ι → ℝ) → E}
    (hF : ∀ (i : ι) x, F (x + Pi.single i 1) = F x) (t : ι → ℝ) :
    ∫ x in Set.Icc (0 : ι → ℝ) 1, F (x + t) = ∫ x in Set.Icc (0 : ι → ℝ) 1, F x := by
  letI : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
  haveI : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
  haveI : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
  let G : UnitAddTorus ι → E := fun y => F fun i => (AddCircle.equivIoc 1 0 (y i) : ℝ)
  have hG : ∀ x : ι → ℝ, G (fun i => (x i : UnitAddCircle)) = F x := by
    intro x
    have h : ∀ i, ∃ n : ℤ, (AddCircle.equivIoc 1 0 (x i : UnitAddCircle) : ℝ) = x i + n := by
      intro i
      have h1 : ((AddCircle.equivIoc 1 0 (x i : UnitAddCircle) : ℝ) : UnitAddCircle) = x i :=
        (AddCircle.equivIoc 1 0).symm_apply_apply _
      rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff] at h1
      obtain ⟨k, hk⟩ := h1
      refine ⟨k, ?_⟩
      rw [zsmul_eq_mul, mul_one] at hk
      linarith
    choose n hn using h
    have := apply_add_intCast_vec_of_unit_periods hF n x
    rw [← this]
    simp only [G, hn]
    rfl
  have hae : Set.Icc (0 : ι → ℝ) 1 =ᵐ[volume]
      {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)} := by
    have h := Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : ι => (volume : Measure ℝ))
      (f := (0 : ι → ℝ)) (g := 1)
    have e : {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : ι → ℝ) i) ((0 : ι → ℝ) i + 1)}
        = Set.univ.pi fun i => Set.Ioc ((0 : ι → ℝ) i) ((1 : ι → ℝ) i) := by
      ext x
      simp [Set.mem_pi]
    rw [e]
    exact h.symm
  rw [setIntegral_congr_set hae, setIntegral_congr_set hae]
  have h1 := UnitAddTorus.integral_preimage G 0
  have h2 := UnitAddTorus.integral_preimage (fun y => G (y + fun i => (t i : UnitAddCircle))) 0
  have h3 : ∫ y : UnitAddTorus ι, G (y + fun i => (t i : UnitAddCircle)) = ∫ y, G y :=
    integral_add_right_eq_self G _
  have h4 : ∀ x : ι → ℝ, G ((fun i => (x i : UnitAddCircle)) + fun i => (t i : UnitAddCircle))
      = F (x + t) := fun x => hG (x + t)
  simp only [hG] at h1
  simp only [h4] at h2
  rw [← h1, ← h2]
  exact h3

theorem setIntegral_unitCube_add_of_entire_periodic {g : ℕ} {f : (Fin g → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (hper : ∀ (i : Fin g) z, f (z + Pi.single i 1) = f z)
    (w : Fin g → ℂ) :
    ∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w)
      = ∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) := by
  have hd : DifferentiableOn ℂ
      (fun w => ∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w)) Set.univ := by
    refine (differentiableOn_setIntegral_of_holomorphic_of_continuousOn
      (F := fun (x : Fin g → ℝ) w => f ((fun i => (x i : ℂ)) + w)) isOpen_univ
      isCompact_Icc subset_rfl measurableSet_Icc isCompact_Icc.measure_lt_top.ne ?_ ?_).1
    · have := hf.continuous
      refine Continuous.continuousOn ?_
      unfold Function.uncurry
      fun_prop
    · intro x _
      exact (hf.comp ((differentiable_const _).add differentiable_id)).differentiableOn
  have h := SCV.eq_of_invariant_real isOpen_univ isPreconnected_univ hd
    (fun z _ t _ => by
      have := setIntegral_unitCube_add_right_of_periodic
        (F := fun x : Fin g → ℝ => f ((fun i => (x i : ℂ)) + z)) (fun i x => by
          rw [← hper i ((fun i => (x i : ℂ)) + z)]
          congr 1
          funext j
          by_cases hij : j = i
          · subst hij; simp; ring
          · simp [hij]) t
      rw [← this]
      congr 1
      funext x
      congr 1
      funext i
      simp only [Pi.add_apply, Complex.ofReal_add]
      ac_rfl) (Set.mem_univ w) (Set.mem_univ 0)
  simpa using h

theorem fourierCoeff_unitCube_translate_of_entire_periodic (g : ℕ) (f : (Fin g → ℂ) → ℂ)
    (hf : Differentiable ℂ f) (hper : ∀ (i : Fin g) z, f (z + Pi.single i 1) = f z)
    (m : Fin g → ℤ) (w : Fin g → ℂ) :
    (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f ((fun i => (x i : ℂ)) + w) *
        cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) =
      cexp (2 * Real.pi * I * ∑ i, (m i : ℂ) * w i) *
        (∫ x in Set.Icc (0 : Fin g → ℝ) 1, f (fun i => (x i : ℂ)) *
          cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * (x i : ℂ))) := by
  have h := setIntegral_unitCube_add_of_entire_periodic
    (f := fun z => f z * cexp (-(2 * Real.pi * I) * ∑ i, (m i : ℂ) * z i))
    (by fun_prop) (fun i z => by
      rw [hper]
      congr 1
      have e : ∑ j, (m j : ℂ) * (z + (Pi.single i 1 : Fin g → ℂ)) j
          = ∑ j, (m j : ℂ) * z j + m i := by
        simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
      rw [e, mul_add, Complex.exp_add]
      have : cexp (-(2 * Real.pi * I) * (m i : ℂ)) = 1 := by
        have := Complex.exp_int_mul_two_pi_mul_I (-m i)
        rw [← this]
        congr 1
        push_cast
        ring
      rw [this, mul_one]) w
  rw [← h, ← integral_const_mul]
  congr 1
  funext x
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

end GlobalTheory
end

section

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

theorem isConnected_basicOpen_complexPoints_of_dense :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → ∃ h : A, h ≠ 0 ∧ IsConnected {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x (h * f) ≠ 0}) →
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x 1 ≠ 0} ⊆ closure {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x f ≠ 0}) →
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → IsConnected {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x f ≠ 0}) := by
  intro H1 H2 A _ _ _ _ f hf

  obtain ⟨h, hh, hconn⟩ := H1 A f hf
  have hhf : h * f ≠ 0 := mul_ne_zero hh hf

  apply hconn.subset_closure
  · rintro x ⟨φ, rfl, hx⟩
    refine ⟨φ, rfl, ?_⟩
    rw [map_mul] at hx
    exact right_ne_zero_of_mul hx
  · rintro x ⟨φ, rfl, -⟩
    exact H2 A (h * f) hhf ⟨φ, rfl, by simp⟩

end GlobalTheory
end
