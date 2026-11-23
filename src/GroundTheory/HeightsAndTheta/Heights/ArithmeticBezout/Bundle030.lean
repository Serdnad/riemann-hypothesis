module

import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle042
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle006
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsGraphAreaFibre
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

namespace VerticalPartMultiplicity

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)

theorem length_localizedModule_quotient {A : Type*} [CommRing A] (K W : Ideal A) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ K)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) := by
  apply _root_.GroundTheory.Heights₂.Heights.NumbersDVR.length_localizedModule_quotient_eq <;> assumption

theorem length_self_eq_of_ringEquiv {Q Q' : Type*} [CommRing Q] [CommRing Q'] (τ : Q ≃+* Q') :
    Module.length Q Q = Module.length Q' Q' := by
  letI := RingHomInvPair.of_ringEquiv τ
  letI := RingHomInvPair.symm (↑τ : Q →+* Q') (τ.symm : Q' →+* Q)
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap τ.toSemilinearEquiv)]

variable {n : ℕ}

end VerticalPartMultiplicity

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem not_dvd_pderiv_of_pderiv_ne_zero {F σ : Type*} [Field F] {g : MvPolynomial σ F}
    (hg : g ≠ 0) {i : σ} (hne : pderiv i g ≠ 0) : ¬ g ∣ pderiv i g := by
  classical
  rintro ⟨q, hq⟩
  have hi : 0 < degreeOf i g := by
    obtain ⟨m, hm⟩ := support_nonempty.2 hne
    rw [mem_support_iff, coeff_pderiv] at hm
    have h1 : m + Finsupp.single i 1 ∈ g.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
    have := monomial_le_degreeOf i h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  have hlt : degreeOf i (pderiv i g) < degreeOf i g := by
    rw [degreeOf_lt_iff hi]
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    have h1 : m + Finsupp.single i 1 ∈ g.support := mem_support_iff.2 (left_ne_zero_of_mul hm)
    have := monomial_le_degreeOf i h1
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  rw [hq, degreeOf_mul_eq hg (right_ne_zero_of_mul (hq ▸ hne))] at hlt
  omega

theorem IsChowForm.exists_pderiv_ne_zero {F : Type} [Field F] [IsAlgClosed F] {p : ℕ} [hp : Fact p.Prime]
    [CharP F p] {n k : ℕ} {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P)
    {g : MvPolynomial (Fin (k + 1) × Fin n) F} (hg : IsChowForm P (k + 1) g) :
    ∃ l, pderiv (0, l) g ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon

  have hall : ∀ v, pderiv v g = 0 := by
    rintro ⟨i, l⟩
    obtain ⟨c, hc2, hc⟩ := hg.rename_swap 0 i
    have hinj : Function.Injective (Prod.map (Equiv.swap (0 : Fin (k + 1)) i) (id : Fin n → Fin n)) :=
      (Equiv.swap 0 i).injective.prodMap Function.injective_id
    have h := pderiv_rename hinj (0, l) g
    rw [hc, pderiv_C_mul, hcon l, map_zero, Prod.map_apply, Equiv.swap_apply_left, id] at h
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc2
    exact (mul_eq_zero.1 h).resolve_left fun h0 => hc0 (C_eq_zero.1 h0)

  have hexp : ∀ s ∈ g.support, ∀ v, p ∣ s v := by
    intro s hs v
    by_cases h0 : s v = 0
    · simp [h0]
    have hle : Finsupp.single v 1 ≤ s := Finsupp.single_le_iff.2 (by omega)
    have h1 := congrArg (AddMonoidAlgebra.coeff · (s - Finsupp.single v 1)) (hall v)
    rw [coeff_pderiv, AddMonoidAlgebra.coeff_zero, tsub_add_cancel_of_le hle] at h1
    have h2 := (mul_eq_zero.1 h1).resolve_left (mem_support_iff.1 hs)
    rw [Finsupp.tsub_apply, Finsupp.single_eq_same] at h2
    have h3 : ((s v : ℕ) : F) = 0 := by
      rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 h0)]
      push_cast
      exact h2
    exact (CharP.cast_eq_zero_iff F p _).1 h3

  obtain ⟨h, hgh⟩ : ∃ h : MvPolynomial (Fin (k + 1) × Fin n) F, h ^ p = g := by
    have hroot : ∀ a : F, ∃ b : F, b ^ p = a := fun a => IsAlgClosed.exists_pow_nat_eq a hp.out.pos
    choose r hr using hroot
    refine ⟨∑ s ∈ g.support, monomial (Finsupp.mapRange (· / p) (Nat.zero_div p) s) (r (AddMonoidAlgebra.coeff g s)), ?_⟩
    rw [sum_pow_char]
    conv_rhs => rw [as_sum g]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' : p • Finsupp.mapRange (· / p) (Nat.zero_div p) s = s := by
      ext v
      simp [Nat.mul_div_cancel' (hexp s hs v)]
    rw [monomial_pow, hr, hs']

  have hmem : ∀ q, q ∈ incIdeal P (k + 1) ↔ g ∣ q := by
    intro q
    rw [← hg.2 q, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hprime : Prime g := by
    have hI := IncIdealPrime.full F n (k + 1) P hP.isPrime hP.isRelevant
    have hspan : incIdeal P (k + 1) = Ideal.span {g} := by
      ext q
      rw [Ideal.mem_span_singleton, hmem]
    rw [hspan] at hI
    exact (Ideal.span_singleton_prime hg.1).1 hI
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact hg.1 (by rw [← hgh, zero_pow hp.out.ne_zero])
  obtain ⟨q, hq⟩ := hprime.dvd_of_dvd_pow (show g ∣ h ^ p by rw [hgh])
  obtain ⟨m, hm⟩ : ∃ m, p = m + 2 := ⟨p - 2, by have := hp.out.two_le; omega⟩
  have h1 : h * (h ^ (m + 1) * q) = h * 1 := by
    rw [mul_one]
    conv_rhs => rw [hq, ← hgh, hm]
    ring
  have hu : IsUnit (h ^ (m + 1)) := IsUnit.of_mul_eq_one q (mul_left_cancel₀ hh0 h1)
  have hu' : IsUnit h := (isUnit_pow_iff (Nat.succ_ne_zero m)).1 hu
  exact hprime.not_isUnit (hgh ▸ hu'.pow p)

theorem ChowFormBirationalAlgClosed.proof : ChowFormBirationalAlgClosed.Statement := by
  intro F _ _ n k P g c hP hg hc
  obtain _ | ⟨p, hp, hch⟩ := CharP.exists' F
  · exact ChowFormBirational.full F n k P g c hP hg hc
  have := hP.isPrime
  classical

  have hmem : ∀ h, h ∈ incIdeal P (k + 1) ↔ g ∣ h := by
    intro h
    rw [← hg.2 h, incIdeal]
    simp only [Submodule.mem_iInf, RingHom.mem_ker]
  have hg0 : aeval (genSubst (genPt P) c) g = 0 :=
    (IncidenceGeneric.full F n (k + 1) P c hc g).1 ((hmem g).2 dvd_rfl)

  have hA : ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) =
      C (genPt P m) * ∑ l, aeval (genSubst (genPt P) c) (pderiv (0, l) g) * C (c l) := by
    intro m
    have h := pderiv_aeval_eq_sum (genSubst (genPt P) c) (0, m) g
    rw [hg0, map_zero] at h
    simp only [pderiv_genSubst, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Fin.succ_ne_zero, if_false, Finset.sum_const_zero, add_zero] at h
    rw [eq_comm, sub_eq_zero] at h
    rw [h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) = C (genPt P m) * ρ :=
    ⟨_, hA⟩

  obtain ⟨l, hl⟩ := IsChowForm.exists_pderiv_ne_zero (p := p) hP hg
  refine ⟨Pi.single l 1, ?_, fun m => ?_⟩
  · have hsum : (∑ l', C ((Pi.single l (1 : F) : Fin n → F) l') * pderiv (0, l') g) =
        pderiv (0, l) g := by
      rw [Finset.sum_eq_single l]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [hsum, hmem]
    exact not_dvd_pderiv_of_pderiv_ne_zero hg.1 hl
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_apply, hρ]
      simp only [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l' _ => ?_
      ring

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

theorem mem_coneTangent_self {n : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsProjPrime J) {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ coneSet h J) :
    y ∈ coneTangent h J y := by
  intro q hq
  have hd : ∀ d, eval (h.pointOf y) (∑ j, X j * pderiv j (homogeneousComponent d q)) = 0 := by
    intro d
    rw [(homogeneousComponent_isHomogeneous d q).sum_X_mul_pderiv, map_nsmul,
      hy _ (hJ.isHomog q hq d), smul_zero]
  calc ∑ j, eval (h.pointOf y) (pderiv j q) * h.pointOf y j
      = eval (h.pointOf y) (∑ j, X j * pderiv j q) := by simp [map_sum, mul_comm]
    _ = ∑ d ∈ Finset.range (q.totalDegree + 1),
          eval (h.pointOf y) (∑ j, X j * pderiv j (homogeneousComponent d q)) := by
        conv_lhs => rw [← sum_homogeneousComponent q]

        simp only [map_sum, Finset.mul_sum]
        exact Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun d _ => hd d

theorem isClosed_coneSet {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsClosed (coneSet h J) := by
  have : coneSet h J = ⋂ q ∈ J, {y | eval (h.pointOf y) q = 0} := by
    ext y
    simp [coneSet]
  rw [this]
  exact isClosed_biInter fun q _ =>
    isClosed_eq ((MvPolynomial.continuous_eval q).comp h.continuous_pointOf) continuous_const

theorem sFinite_restrict_of_ball {n : ℕ} (μ : Measure (EuclideanSpace ℂ (Fin n)))
    (C : Set (EuclideanSpace ℂ (Fin n))) (hC : ∀ R : ℝ, μ (C ∩ Metric.ball 0 R) < ⊤) :
    SFinite (μ.restrict C) := by
  have : IsLocallyFiniteMeasure (μ.restrict C) := ⟨fun x => ⟨Metric.ball 0 (‖x‖ + 1),
    Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (by linarith)), by
      rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet, Set.inter_comm]
      exact hC _⟩⟩
  infer_instance

theorem ConeTangentAverage.proof (hMass : ConeLocalMass.Statement)
    (hMeas : ConeJacMeasurable.Statement) (hDim : ConeTangentDim.Statement)
    (hInv : TangentGaussInvariant.Statement) : ConeTangentAverage.Statement := by
  intro n m h J hJ hm hmn hfib
  have : SFinite ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
      Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J)) :=
    sFinite_restrict_of_ball _ _ (hMass n m h J hJ hm hmn hfib)
  have hG : Measurable fun π : Fin m → Fin n → ℂ => matGauss π := by
    unfold matGauss
    exact (by fun_prop : Continuous fun π : Fin m → Fin n → ℂ =>
      Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2)).measurable.ennreal_ofReal
  have hP : Continuous fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => linProj p.1 p.2 := by
    unfold linProj
    fun_prop
  have hF : AEMeasurable (Function.uncurry fun (π : Fin m → Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) =>
      matGauss π * ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
        ENNReal.ofReal (coneJac h J π y)))
      ((volume : Measure (Fin m → Fin n → ℂ)).prod
        ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J))) :=
    (hG.comp measurable_fst).aemeasurable.mul
      (((measurable_one.indicator Metric.isOpen_ball.measurableSet).comp hP.measurable).aemeasurable.mul
        (hMeas n m h J hJ hm hmn hfib).ennreal_ofReal)
  rw [show (fun π : Fin m → Fin n → ℂ => matGauss π *
      ∫⁻ y in coneSet h J, (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
        ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))) =
      fun π => ∫⁻ y in coneSet h J, matGauss π *
        ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y)) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) from
    funext fun π => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm,
    lintegral_lintegral_swap hF]
  refine lintegral_congr_ae ?_
  filter_upwards [hDim n m h J hJ hm hmn hfib, ae_restrict_mem (isClosed_coneSet h J).measurableSet]
    with y hy hyC
  simp only [← mul_assoc]
  exact hInv n m hm hmn _ hy y (mem_coneTangent_self h hJ hyC)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

theorem GraphAreaIntegral.continuous_areaJacobian {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] :
    Continuous fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F) := by
  have h : (fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F)) =
      fun M => √((ContinuousLinearMap.adjoint M ∘L M).det) := by
    funext M
    rfl
  rw [h]
  exact (ContinuousLinearMap.continuous_det.comp
    ((ContinuousLinearMap.adjoint.continuous).clm_comp continuous_id)).sqrt

theorem GraphAreaIntegral.proof (h : GraphAreaHolomorphic.Statement) : GraphAreaIntegral.Statement := by
  intro d m n e Ω F hΩ hF A hAΩ hA g
  set G := graphPt e F with hGdef
  set μ : Measure (EuclideanSpace ℂ (Fin d)) := μH[((2 * d : ℕ) : ℝ)] with hμ
  set ν : Measure (EuclideanSpace ℂ (Fin n)) := μH[((2 * d : ℕ) : ℝ)] with hν
  set J : EuclideanSpace ℂ (Fin d) → ℝ≥0∞ := fun x => ENNReal.ofReal (areaJacobian
    (fderiv ℝ G x : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) with hJ
  have hJm : Measurable J := ENNReal.measurable_ofReal.comp
    (GraphAreaIntegral.continuous_areaJacobian.measurable.comp (measurable_fderiv ℝ G))
  have hGc : ContinuousOn G A := (continuousOn_graphPt e hF.continuousOn).mono hAΩ
  let f : A → EuclideanSpace ℂ (Fin n) := fun a => G a
  have hfc : Continuous f := hGc.domRestrict
  have hf : MeasurableEmbedding f :=
    { injective := fun a b hab => Subtype.ext (graphPt_injective_of_graphBase e F hab)
      measurable := hfc.measurable
      measurableSet_image' := fun s hs => by
        have hs' : MeasurableSet (((↑) : A → EuclideanSpace ℂ (Fin d)) '' s) :=
          MeasurableSet.subtype_image hA hs
        have : f '' s = G '' (((↑) : A → EuclideanSpace ℂ (Fin d)) '' s) := by
          rw [Set.image_image]
        rw [this]
        exact hs'.image_of_continuousOn_injOn (hGc.mono (by rintro _ ⟨a, -, rfl⟩; exact a.2))
          (graphPt_injective_of_graphBase e F).injOn }
  set M : Measure A := (μ.withDensity J).comap ((↑) : A → EuclideanSpace ℂ (Fin d)) with hM
  have hmeas : ν.restrict (G '' A) = M.map f := by
    ext1 S hS
    have hpre : ((↑) : A → EuclideanSpace ℂ (Fin d)) '' (f ⁻¹' S) = A ∩ G ⁻¹' S := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a.2, ha⟩
      · rintro ⟨hx, hxS⟩
        exact ⟨⟨x, hx⟩, hxS, rfl⟩
    have hmS : MeasurableSet (A ∩ G ⁻¹' S) := by
      rw [← hpre]
      exact MeasurableSet.subtype_image hA (hf.measurable hS)
    rw [Measure.restrict_apply hS, Measure.map_apply hf.measurable hS,
      (MeasurableEmbedding.subtype_coe hA).comap_apply, hpre, withDensity_apply _ hmS,
      Set.inter_comm S, ← Set.image_inter_preimage]
    exact h d m n e Ω F hΩ hF _ (Set.inter_subset_left.trans hAΩ) hmS
  calc ∫⁻ y in G '' A, g y ∂ν = ∫⁻ y, g y ∂(M.map f) := by rw [hmeas]
    _ = ∫⁻ a, g (f a) ∂M := hf.lintegral_map g
    _ = ∫⁻ x in A, g (G x) ∂(μ.withDensity J) := lintegral_subtype_comap hA (fun x => g (G x))
    _ = ∫⁻ x, g (G x) ∂((μ.restrict A).withDensity J) := by rw [restrict_withDensity hA]
    _ = ∫⁻ x in A, J x * g (G x) ∂μ :=
      lintegral_withDensity_eq_lintegral_mul_non_measurable _ hJm
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
    _ = ∫⁻ x in A, g (G x) * J x ∂μ := by simp_rw [mul_comm]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open Module

theorem det_linProj_comp_zeroExt {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ) :
    LinearMap.det ((linProjₗ π).comp (zeroExt m k)) = (coordPlaneBlock π).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin m) ℂ).toBasis]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp [linProjₗ, linProj_zeroExt, Matrix.mulVec, dotProduct]

theorem LeadPlaneJac.proof : LeadPlaneJac.Statement := by
  intro m k π
  have hmem : ∀ x, zeroExt m k x ∈ leadCoordPlane (m + k) m := fun x j hj => zeroExt_apply_of_le x j hj
  let e : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] leadCoordPlane (m + k) m := (zeroExt m k).codRestrict (leadCoordPlane (m + k) m) hmem
  let eᵢ : EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] leadCoordPlane (m + k) m :=
    { toLinearMap := e, norm_map' := fun x => norm_zeroExt m k x }
  have he_surj : Function.Surjective e := by
    rintro ⟨y, hy⟩
    exact ⟨_, Subtype.ext (eq_zeroExt_of hy).symm⟩
  have hrank : finrank ℂ (EuclideanSpace ℂ (Fin m)) = finrank ℂ (leadCoordPlane (m + k) m) :=
    (LinearEquiv.ofBijective e ⟨eᵢ.injective, he_surj⟩).finrank_eq
  have hcomp : ((linProjₗ π).comp (leadCoordPlane (m + k) m).subtype).comp e = (linProjₗ π).comp (zeroExt m k) := rfl
  have he1 : LinearMap.normDet (𝕜 := ℂ) (U := EuclideanSpace ℂ (Fin m)) (V := leadCoordPlane (m + k) m) e = 1 := by
    have h := LinearIsometry.normDet_eq_one (𝕜 := ℂ) (U := EuclideanSpace ℂ (Fin m)) (V := leadCoordPlane (m + k) m) eᵢ
    exact h
  have key := LinearMap.normDet_comp_of_finrank_eq (𝕜 := ℂ) (U := EuclideanSpace ℂ (Fin m)) (V := leadCoordPlane (m + k) m)
    (W := EuclideanSpace ℂ (Fin m)) e ((linProjₗ π).comp (leadCoordPlane (m + k) m).subtype) hrank
  rw [hcomp, he1, mul_one, LinearMap.normDet_eq_norm_det, det_linProj_comp_zeroExt] at key
  unfold tangentJac
  rw [← key]

end

end GroundTheory.Heights₂.Heights
end
