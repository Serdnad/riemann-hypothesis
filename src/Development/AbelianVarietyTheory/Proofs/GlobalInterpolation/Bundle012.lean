module

public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LiftInvariantsFinrankEq
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle007
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
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
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPowerSeries.Equiv
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
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Sheaves.Init
import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.Basic

@[expose] public section

section

open Matrix Formalism.UG

namespace GlobalTheory.DualFrames

variable {A : Type} [CommRing A] {k : ℕ}

theorem hform_eq_dot (τ : A →+* A) (J : Matrix (Fin k) (Fin k) A) (x y : Fin k → A) :
    hform τ J x y = (τ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  unfold hform
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_frames (τ : A →+* A) (J B C : Matrix (Fin k) (Fin k) A)
    (h : cT τ B * J * C = 1) (x y : Fin k → A) :
    hform τ J (B *ᵥ x) (C *ᵥ y) = ∑ i, τ (x i) * y i := by
  rw [hform_eq_dot]
  have hmap : (τ ∘ (B *ᵥ x)) = (B.map τ) *ᵥ (τ ∘ x) := by
    funext i

    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  have hct : (B.map τ)ᵀ = cT τ B := by
    unfold cT
    rfl
  rw [hmap, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hct, h, Matrix.one_mulVec]
  simp [dotProduct]

theorem hform_swap (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) (J : Matrix (Fin k) (Fin k) A)
    (hJ : IsHerm τ J) (x y : Fin k → A) : τ (hform τ J x y) = hform τ J y x := by
  unfold IsHerm cT at hJ
  have hJ' : ∀ i j, τ (J i j) = J j i := by
    intro i j
    simpa using congrFun (congrFun hJ j) i
  unfold hform

  simp only [map_sum, map_mul, hτ, hJ']
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_mulVec (B : GL (Fin k) A) (y : Fin k → A) :
    ∃ z, (B : Matrix (Fin k) (Fin k) A) *ᵥ z = y := by
  refine ⟨((B⁻¹ : GL (Fin k) A) : Matrix (Fin k) (Fin k) A) *ᵥ y, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem dual_of_dual_frames :
    ∀ (A : Type) [CommRing A] (S : Subring A) (τ : A →+* A), (∀ a, τ (τ a) = a) →
      (∀ a ∈ S, τ a ∈ S) → ∀ (k : ℕ) (J : Matrix (Fin k) (Fin k) A), IsHerm τ J →
      ∀ (B C : GL (Fin k) A) (L₁ L₂ : Submodule S (Fin k → A)),
      cT τ (B : Matrix (Fin k) (Fin k) A) * J * (C : Matrix (Fin k) (Fin k) A) = 1 →
      (∀ y : Fin k → A, (B : Matrix (Fin k) (Fin k) A) *ᵥ y ∈ L₁ ↔ ∀ i, y i ∈ S) →
      (∀ y : Fin k → A, (C : Matrix (Fin k) (Fin k) A) *ᵥ y ∈ L₂ ↔ ∀ i, y i ∈ S) →
      (∀ y, y ∈ L₂ ↔ ∀ x ∈ L₁, hform τ J x y ∈ S) ∧
      (∀ y, y ∈ L₁ ↔ ∀ x ∈ L₂, hform τ J x y ∈ S) ∧
      (∀ x, x ∈ L₁ ↔ ∀ y ∈ L₂, hform τ J x y ∈ S) := by
  intro A _ S τ hτ hS k J hJ B C L₁ L₂ h hL₁ hL₂

  have pair : ∀ u v : Fin k → A,
      hform τ J ((B : Matrix (Fin k) (Fin k) A) *ᵥ u) ((C : Matrix (Fin k) (Fin k) A) *ᵥ v) =
        ∑ i, τ (u i) * v i :=
    fun u v => hform_frames τ J B C h u v
  have flip : ∀ x y, hform τ J x y = τ (hform τ J y x) :=
    fun x y => (hform_swap τ hτ J hJ y x).symm
  have memS_iff : ∀ a, τ a ∈ S ↔ a ∈ S := fun a =>
    ⟨fun ha => hτ a ▸ hS _ ha, hS a⟩
  have single_mem : ∀ i j, (Pi.single i (1 : A) : Fin k → A) j ∈ S := by
    intro i j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj, S.zero_mem]
  have coord : ∀ u v : Fin k → A, (∀ i, u i ∈ S) → (∀ i, v i ∈ S) → ∑ i, τ (u i) * v i ∈ S :=
    fun u v hu hv => sum_mem fun i _ => mul_mem (hS _ (hu i)) (hv i)
  have part1 : ∀ y, y ∈ L₂ ↔ ∀ x ∈ L₁, hform τ J x y ∈ S := by
    intro y
    obtain ⟨v, rfl⟩ := exists_mulVec C y
    rw [hL₂]
    constructor
    · intro hv x hx
      obtain ⟨u, rfl⟩ := exists_mulVec B x
      rw [pair]
      exact coord u v ((hL₁ u).1 hx) hv
    · intro hall i
      have key := hall ((B : Matrix (Fin k) (Fin k) A) *ᵥ Pi.single i 1) ((hL₁ _).2 (single_mem i))
      have e : ∑ j, τ ((Pi.single i (1 : A) : Fin k → A) j) * v j = v i := by
        simp [Pi.single_apply]
      rwa [pair, e] at key
  have part2 : ∀ y, y ∈ L₁ ↔ ∀ x ∈ L₂, hform τ J x y ∈ S := by
    intro y
    obtain ⟨v, rfl⟩ := exists_mulVec B y
    rw [hL₁]
    constructor
    · intro hv x hx
      obtain ⟨u, rfl⟩ := exists_mulVec C x
      rw [flip, pair, memS_iff]
      exact coord v u hv ((hL₂ u).1 hx)
    · intro hall i
      have key := hall ((C : Matrix (Fin k) (Fin k) A) *ᵥ Pi.single i 1) ((hL₂ _).2 (single_mem i))
      have e : ∑ j, τ (v j) * (Pi.single i (1 : A) : Fin k → A) j = τ (v i) := by
        simp [Pi.single_apply]
      rwa [flip, pair, memS_iff, e, memS_iff] at key
  have part3 : ∀ x, x ∈ L₁ ↔ ∀ y ∈ L₂, hform τ J x y ∈ S := by
    intro x
    rw [part2]
    refine forall₂_congr fun y _ => ?_
    rw [flip x y, memS_iff]
  exact ⟨part1, part2, part3⟩

end GlobalTheory.DualFrames
end

section

noncomputable section

open MvPowerSeries IsLocalRing Formalism.BasicNotions.V1

namespace GlobalTheory.PsCNL

section Division

variable {σ : Type} {O : Type} [CommRing O]

end Division

section

variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}

theorem mem_max_iff (f : MvPowerSeries (Fin a) O) :
    f ∈ maximalIdeal (MvPowerSeries (Fin a) O) ↔ constantCoeff f ∈ maximalIdeal O :=
  _root_.GlobalTheory.MaximalIdealMembership.mem_maximalIdeal_iff f

theorem ps_isPrecomplete [IsPrecomplete (maximalIdeal O) O] (a : ℕ) :
    IsPrecomplete (maximalIdeal (MvPowerSeries (Fin a) O)) (MvPowerSeries (Fin a) O) :=
  _root_.GlobalTheory.PowerSeriesIdealPowers.main a

end

theorem haus_of_noeth (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] :
    IsHausdorff (maximalIdeal B) B :=
  _root_.GlobalTheory.NoetherianLocalHausdorff.noeth_local_hausdorff B

theorem psCNL : ∀ (O : Type) [CommRing O] [IsLocalRing O] (C : TR O) (n : ℕ),
    ∃ (_ : IsLocalRing (MvPowerSeries (Fin n) C.C)), IsCNL O (MvPowerSeries (Fin n) C.C) ∧
      ∀ x : MvPowerSeries (Fin n) C.C, x ∈ maximalIdeal (MvPowerSeries (Fin n) C.C) ↔
        MvPowerSeries.constantCoeff x ∈ maximalIdeal C.C := by
  intro O _ _ A n
  refine ⟨inferInstance, ?_, fun x => mem_max_iff x⟩
  exact
    { noeth := inferInstance
      complete :=
        { toIsHausdorff := haus_of_noeth _
          toIsPrecomplete := ps_isPrecomplete n }
      localHom := ⟨fun a ha => by
        rw [MvPowerSeries.algebraMap_apply, isUnit_iff_constantCoeff, constantCoeff_C] at ha
        exact isUnit_of_map_unit _ _ ha⟩
      resSurj := by
        intro y
        obtain ⟨f, rfl⟩ := residue_surjective y
        obtain ⟨a, ha⟩ := IsCNL.resSurj (O := O) (A := A.C) (residue A.C (constantCoeff f))
        have ha' : residue A.C (algebraMap O A.C a) = residue A.C (constantCoeff f) := ha
        refine ⟨a, ?_⟩
        show residue _ (algebraMap O (MvPowerSeries (Fin n) A.C) a) = residue _ f
        rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
          isUnit_iff_constantCoeff, map_sub, MvPowerSeries.algebraMap_apply, constantCoeff_C]
        show algebraMap O A.C a - constantCoeff f ∈ maximalIdeal A.C
        rw [← residue_eq_zero_iff, map_sub, ha', sub_self] }

end GlobalTheory.PsCNL
end
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory

theorem norm_sq_le_integral_square :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℂ → ℂ) (ρ : ℂ) (r : ℝ), Differentiable ℂ f → 0 < r →
      ‖f ρ‖ ^ 2 ≤ C / r ^ 2 * ∫ σ in (ρ.re - r)..(ρ.re + r), ∫ t in (ρ.im - r)..(ρ.im + r),
        ‖f (σ + t * I)‖ ^ 2 := by
  refine ⟨Real.pi⁻¹, inv_pos.mpr Real.pi_pos, fun f ρ r hf hr => ?_⟩
  set S : Set ℂ := Set.Ioc (ρ.re - r) (ρ.re + r) ×ℂ Set.Ioc (ρ.im - r) (ρ.im + r) with hS
  have hcont : Continuous fun z => ‖f z‖ ^ 2 := hf.continuous.norm.pow 2
  have hSsub : S ⊆ Metric.closedBall ρ (2 * r) := by
    intro z hz
    simp only [hS, Complex.mem_reProdIm, Set.mem_Ioc] at hz
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h := Complex.norm_le_abs_re_add_abs_im (z - ρ)
    simp only [Complex.sub_re, Complex.sub_im] at h
    have h1 : |z.re - ρ.re| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |z.im - ρ.im| ≤ r := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hint : IntegrableOn (fun z => ‖f z‖ ^ 2) S :=
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall ρ (2 * r))).mono_set hSsub
  have hball : Metric.ball ρ r ⊆ S := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - ρ)
    have h2 := Complex.abs_im_le_norm (z - ρ)
    simp only [Complex.sub_re, Complex.sub_im] at h1 h2
    have a1 := abs_lt.mp (lt_of_le_of_lt h1 hz)
    have a2 := abs_lt.mp (lt_of_le_of_lt h2 hz)
    simp only [hS, Complex.mem_reProdIm, Set.mem_Ioc]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hv := volume_ball_complex ρ hr
  simp only [Module.finrank_self, pow_one, mul_one, Nat.factorial_one, Nat.cast_one,
    div_one] at hv
  have hvr : volume.real (Metric.ball ρ r) = Real.pi * r ^ 2 := by
    rw [measureReal_def, hv, ENNReal.toReal_ofReal (by positivity)]
  have key := norm_pow_le_inv_measure_mul_integral_ball volume (a := ρ) hr hf.differentiableOn 2
    (integrableOn_norm_pow_ball volume (a := ρ) hf.continuous.continuousOn 2)
  rw [hvr] at key
  have hmono : ∫ z in Metric.ball ρ r, ‖f z‖ ^ 2 ≤ ∫ z in S, ‖f z‖ ^ 2 :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun z => by positivity)
      (Filter.Eventually.of_forall hball)
  have hp := Complex.volume_preserving_equiv_real_prod.symm
  have he := Complex.measurableEquivRealProd.symm.measurableEmbedding
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' S =
      Set.Ioc (ρ.re - r) (ρ.re + r) ×ˢ Set.Ioc (ρ.im - r) (ρ.im + r) := by
    ext p
    simp [hS, Complex.measurableEquivRealProd_symm_apply, Complex.mem_reProdIm]
  have hint' := (hp.integrableOn_comp_preimage he).mpr hint
  rw [hpre, Measure.volume_eq_prod] at hint'
  have hiter : ∫ z in S, ‖f z‖ ^ 2 = ∫ σ in (ρ.re - r)..(ρ.re + r),
      ∫ t in (ρ.im - r)..(ρ.im + r), ‖f (σ + t * I)‖ ^ 2 := by
    rw [← hp.setIntegral_preimage_emb he (fun z => ‖f z‖ ^ 2) S, hpre, Measure.volume_eq_prod,
      setIntegral_prod (fun x => ‖f (Complex.measurableEquivRealProd.symm x)‖ ^ 2) hint', intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_congr_fun measurableSet_Ioc fun σ _ => ?_
    rw [intervalIntegral.integral_of_le (by linarith)]
    simp [Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I]
  calc ‖f ρ‖ ^ 2 ≤ (Real.pi * r ^ 2)⁻¹ * ∫ z in Metric.ball ρ r, ‖f z‖ ^ 2 := key
    _ ≤ (Real.pi * r ^ 2)⁻¹ * ∫ z in S, ‖f z‖ ^ 2 := by gcongr
    _ = _ := by rw [hiter, mul_inv, div_eq_mul_inv]

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory.UnitaryBC

theorem exists_finset_detecting_of_finiteDimensional {X : Type} (W : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ W] :
    ∃ s : Finset X, ∀ v : W, (∀ x ∈ s, (v : X → ℂ) x = 0) → v = 0 := by
  apply _root_.GlobalTheory.FinitePointsDetect.finite_points_detect

theorem exists_interpolation_of_finiteDimensional {X : Type} (W : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ W] :
    ∃ (s : Finset X) (w : s → X → ℂ), ∀ v ∈ W, ∀ y, v y = ∑ x : s, v x * w x y := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_detecting_of_finiteDimensional W
  let r : W →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun x : s => (LinearMap.proj (x : X)) ∘ₗ W.subtype
  have hr : LinearMap.ker r = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hs v fun x hx => congrFun hv ⟨x, hx⟩
  obtain ⟨L, hL⟩ := r.exists_leftInverse_of_injective hr
  refine ⟨s, fun x => (L fun j => if x = j then 1 else 0 : W), fun v hv y => ?_⟩
  have h1 : L (r ⟨v, hv⟩) = ⟨v, hv⟩ := LinearMap.congr_fun hL ⟨v, hv⟩
  rw [LinearMap.pi_apply_eq_sum_univ] at h1
  have h2 := congrFun (congrArg Subtype.val h1) y
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul] at h2
  exact h2.symm

theorem eq_zero_of_integral_mul_eq_zero_of_separating {K : Type} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] (R : Subalgebra ℂ (K → ℂ))
    (hc : ∀ p ∈ R, Continuous p) (hs : ∀ p ∈ R, star p ∈ R)
    (hsep : ∀ x y : K, x ≠ y → ∃ p ∈ R, p x ≠ p y) (g : K → ℂ) (hg : Continuous g)
    (h0 : ∀ p ∈ R, ∫ k, g k * p k ∂μ = 0) : g = 0 := by
  let A : StarSubalgebra ℂ C(K, ℂ) :=
    { carrier := {φ | (φ : K → ℂ) ∈ R}
      mul_mem' := fun ha hb => R.mul_mem ha hb
      add_mem' := fun ha hb => R.add_mem ha hb
      algebraMap_mem' := fun c => R.algebraMap_mem c
      star_mem' := fun ha => hs _ ha }
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨p, hp, hne⟩ := hsep x y hxy
    exact ⟨p, ⟨⟨p, hc p hp⟩, hp, rfl⟩, hne⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  let G : C(K, ℂ) := ⟨g, hg⟩
  have hcont : Continuous fun φ : C(K, ℂ) => ∫ k, g k * φ k ∂μ := by
    have h1 : Continuous fun φ : C(K, ℂ) =>
        ∫ k, (ContinuousMap.toLp (E := ℂ) 1 μ ℂ (G * φ)) k ∂μ :=
      MeasureTheory.continuous_integral.comp
        ((ContinuousMap.toLp (E := ℂ) 1 μ ℂ).continuous.comp (continuous_const.mul continuous_id))
    convert h1 using 2 with φ
    exact (integral_congr_ae (ContinuousMap.coeFn_toLp (E := ℂ) (p := 1) (𝕜 := ℂ) μ (G * φ))).symm
  have hcl : IsClosed {φ : C(K, ℂ) | ∫ k, g k * φ k ∂μ = 0} := isClosed_eq hcont continuous_const
  have hmem : star G ∈ closure (A : Set C(K, ℂ)) := by
    have : star G ∈ A.topologicalClosure := htop ▸ StarSubalgebra.mem_top
    exact this
  have hsub : (A : Set C(K, ℂ)) ⊆ {φ : C(K, ℂ) | ∫ k, g k * φ k ∂μ = 0} :=
    fun φ hφ => h0 _ hφ
  have hz : ∫ k, g k * (starRingEnd ℂ) (g k) ∂μ = 0 := closure_minimal hsub hcl hmem
  simp only [Complex.mul_conj] at hz
  rw [integral_complex_ofReal] at hz
  have hz' : ∫ k, Complex.normSq (g k) ∂μ = 0 := by exact_mod_cast hz
  have hcn : Continuous fun k => Complex.normSq (g k) := Complex.continuous_normSq.comp hg
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg (g k))
    (hcn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 hz'
  have := (Continuous.ae_eq_iff_eq μ hcn continuous_zero).1 hae
  funext k
  exact Complex.normSq_eq_zero.1 (congrFun this k)

theorem mem_of_finiteDimensional_span_rightTranslates :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] (R : Subalgebra ℂ (K → ℂ)), (∀ p ∈ R, Continuous p) → (∀ p ∈ R, star p ∈ R) → (∀ x y : K, x ≠ y → ∃ p ∈ R, p x ≠ p y) → (∀ p ∈ R, ∃ (m : ℕ) (a b : Fin m → K → ℂ), (∀ i, a i ∈ R ∧ Continuous (b i)) ∧ ∀ x k, p (x⁻¹ * k) = ∑ i, a i x * b i k) → ∀ f : K → ℂ, Continuous f → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun x : K => f (x * k))) → f ∈ R := by
  intro K _ _ _ _ _ R hc hs hsep hsplit f hf hfd
  classical
  borelize K
  let μ : Measure K := Measure.haar
  have hint : ∀ u : K → ℂ, Continuous u → Integrable u μ := fun u hu =>
    hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfx : ∀ x : K, Continuous fun k => f (x * k) := fun x =>
    hf.comp (continuous_const.mul continuous_id)
  obtain ⟨s, w, hw⟩ := exists_interpolation_of_finiteDimensional
    (Submodule.span ℂ (Set.range fun k : K => fun x : K => f (x * k)))
  have hdec : ∀ y k, f (y * k) = ∑ x : s, f (x * k) * w x y := fun y k =>
    hw _ (Submodule.subset_span ⟨k, rfl⟩) y

  have hconv : ∀ p ∈ R, (fun y => ∫ k, f (y * k) * p k ∂μ) ∈ R := by
    intro p hp
    obtain ⟨m, a, b, hab, hp'⟩ := hsplit p hp
    have : (fun y => ∫ k, f (y * k) * p k ∂μ) = ∑ i, (∫ k, f k * b i k ∂μ) • a i := by
      funext y
      have h1 := integral_mul_left_eq_self (μ := μ) (fun k => f k * p (y⁻¹ * k)) y
      simp only [inv_mul_cancel_left] at h1
      rw [h1]
      simp only [hp', Finset.mul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← integral_mul_const]
        congr 1
        funext k
        ring
      · intro i _
        exact hint _ (hf.mul (continuous_const.mul (hab i).2))
    rw [this]
    exact R.sum_mem fun i _ => R.smul_mem (hab i).1 _
  let T : R →ₗ[ℂ] (s → ℂ) :=
    { toFun := fun p x => ∫ k, f (x * k) * (p : K → ℂ) k ∂μ
      map_add' := fun p q => by
        funext x
        simp only [Subalgebra.coe_add, Pi.add_apply, mul_add]
        exact integral_add (hint _ ((hfx x).mul (hc _ p.2))) (hint _ ((hfx x).mul (hc _ q.2)))
      map_smul' := fun c p => by
        funext x
        simp only [Subalgebra.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext k
        ring }
  have hmem : (fun x : s => f x) ∈ LinearMap.range T := by
    by_contra hne
    obtain ⟨l, hl1, hl0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hne inferInstance
    let c : s → ℂ := fun x => l fun j => if x = j then 1 else 0
    have hl : ∀ v : s → ℂ, l v = ∑ x, v x * c x := fun v => LinearMap.pi_apply_eq_sum_univ l v
    have hg : (fun k => ∑ x : s, f (x * k) * c x) = 0 := by
      refine eq_zero_of_integral_mul_eq_zero_of_separating μ R hc hs hsep _
        (continuous_finsetSum _ fun x _ => (hfx x).mul continuous_const) fun p hp => ?_
      have h1 : l (T ⟨p, hp⟩) = 0 := by
        have : l (T ⟨p, hp⟩) ∈ Submodule.map l (LinearMap.range T) :=
          Submodule.mem_map_of_mem ⟨_, rfl⟩
        rw [hl0] at this
        exact (Submodule.mem_bot ℂ).1 this
      rw [hl] at h1
      rw [← h1]
      simp only [Finset.sum_mul]
      rw [integral_finsetSum]
      · refine Finset.sum_congr rfl fun x _ => ?_
        change _ = (∫ k, f (x * k) * p k ∂μ) * c x
        rw [← integral_mul_const]
        congr 1
        funext k
        ring
      · intro x _
        exact hint _ (((hfx x).mul continuous_const).mul (hc p hp))
    apply hl1
    rw [hl]
    simpa using congrFun hg 1
  obtain ⟨p, hp⟩ := hmem
  have hfeq : f = fun y => ∫ k, f (y * k) * (p : K → ℂ) k ∂μ := by
    funext y
    have h1 := hdec y 1
    simp only [mul_one] at h1
    rw [h1]
    have h2 : ∀ k, f (y * k) * (p : K → ℂ) k = ∑ x : s, f (x * k) * (p : K → ℂ) k * w x y := by
      intro k
      rw [hdec y k, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    simp only [h2]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [integral_mul_const]
      congr 1
      exact (congrFun hp x).symm
    · intro x _
      exact hint _ (((hfx x).mul (hc _ p.2)).mul continuous_const)
  rw [hfeq]
  exact hconv _ p.2

end GlobalTheory.UnitaryBC
end

section

open MeasureTheory Topology

theorem _root_.GlobalTheory.T.map_smul_addHaar_of_norm_eq_one : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (c : K), ‖c‖ = 1 → Measure.map (fun x : V => c • x) μ = μ := by
  first | exact @GlobalTheory.addHaar_map_smul_of_norm_eq_one | exact GlobalTheory.addHaar_map_smul_of_norm_eq_one | (intros; apply GlobalTheory.addHaar_map_smul_of_norm_eq_one <;> assumption)
end
