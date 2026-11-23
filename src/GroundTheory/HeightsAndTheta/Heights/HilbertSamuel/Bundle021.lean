module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.CovolumeCount
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle014
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace HilbFnValueSpan

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def coneQ (y : (Σ k, ι k) → Ω) : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] MvPolynomial K Ω :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1


omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem map_mCoordIdeal (y : (Σ k, ι k) → Ω) :
    (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = RingHom.ker (coneQ y) := by
  have hring : ((coneQ y : MvPolynomial (Σ k, ι k) ℚ →+* MvPolynomial K Ω).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) = (mConeMap y : MRing ι →+* MvPolynomial K Ω) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coneQ, mConeMap]
    · intro i
      simp [coneQ, mConeMap]
  have hker : mCoordIdeal y =
      (RingHom.ker (coneQ y)).comap (MvPolynomial.map (Int.castRingHom ℚ)) := by
    ext f
    rw [Ideal.mem_comap]
    simp only [mCoordIdeal, RingHom.mem_ker]
    have h := RingHom.congr_fun hring f
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h
    rw [h]
  let _ := MvPolynomial.algebraMvPolynomial (σ := Σ k, ι k) (R := ℤ) (S := ℚ)
  have e : algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) =
      MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  have h := IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)))
    (MvPolynomial (Σ k, ι k) ℚ) (RingHom.ker (coneQ y))
  rw [e] at h
  rw [hker]
  exact h

theorem weight_blockWeight (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (NumbersDVR.blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]

theorem isWeightedHomogeneous_iff {R : Type} [CommRing R] (f : MvPolynomial (Σ k, ι k) R) (a : K → ℕ) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a ↔ ∀ m ∈ f.support, ∀ k, ∑ i, m ⟨k, i⟩ = a k := by
  constructor
  · intro h m hm k
    rw [← weight_blockWeight, h (mem_support_iff.mp hm)]
  · intro h m hm
    funext k
    rw [weight_blockWeight, h m (mem_support_iff.mpr hm) k]

theorem coneQ_eq (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    coneQ y f = MvPolynomial.C (aeval y f) * ∏ k, MvPolynomial.X k ^ a k := by
  have hf' := (isWeightedHomogeneous_iff f a).mp hf
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]

  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : (Σ k, ι k), (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p =
      ∏ k, MvPolynomial.X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf' m hm k]
  simp only [coneQ, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem mem_ker_iff (y : (Σ k, ι k) → Ω) {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) :
    f ∈ RingHom.ker (coneQ y) ↔ aeval y f = 0 := by
  rw [RingHom.mem_ker, coneQ_eq y hf]
  constructor
  · intro h
    have hne : (∏ k, MvPolynomial.X k ^ a k : MvPolynomial K Ω) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k)
    rcases mul_eq_zero.mp h with h | h
    · exact MvPolynomial.C_eq_zero.mp h
    · exact absurd h hne
  · intro h
    rw [h, map_zero, zero_mul]

def evalForms (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a →ₗ[ℚ] Ω :=
  (aeval y : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] Ω).toLinearMap.comp (Submodule.subtype _)

def quotForms (P : Ideal (MvPolynomial (Σ k, ι k) ℚ)) (a : K → ℕ) :
    weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a →ₗ[ℚ] MvPolynomial (Σ k, ι k) ℚ ⧸ P :=
  (Ideal.Quotient.mkₐ ℚ P).toLinearMap.comp (Submodule.subtype _)

theorem range_evalForms (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    LinearMap.range (evalForms y a) = valueSpan y a := by
  apply le_antisymm
  · rintro _ ⟨⟨f, hf⟩, rfl⟩
    have hf' := (isWeightedHomogeneous_iff f a).mp ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hf)
    show aeval y f ∈ valueSpan y a
    conv => arg 2; rw [f.as_sum]

    rw [map_sum]
    refine Submodule.sum_mem _ fun v hv => ?_
    have hmon : aeval y (monomial v (AddMonoidAlgebra.coeff f v)) =
        AddMonoidAlgebra.coeff f v • aeval y (monomial v (1 : ℤ) : MRing ι) := by
      simp only [aeval_monomial, Algebra.smul_def, map_one, one_mul]
    rw [hmon]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨monomial v 1, ?_, rfl⟩)
    intro m hm k
    rw [support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm
    rw [hm]
    exact hf' v hv k
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    have hmem : MvPolynomial.map (Int.castRingHom ℚ) g ∈
        weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι) a := by
      rw [mem_weightedHomogeneousSubmodule, isWeightedHomogeneous_iff]
      exact fun m hm k => hg m (support_map_subset _ _ hm) k
    refine ⟨⟨_, hmem⟩, ?_⟩
    show aeval y (MvPolynomial.map (Int.castRingHom ℚ) g) = aeval y g
    rw [← algebraMap_int_eq, aeval_map_algebraMap]

theorem finrank_gradedPiece (y : (Σ k, ι k) → Ω) (a : K → ℕ) :
    Module.finrank ℚ (NumbersDVR.gradedPiece
        ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))) a) =
      Module.finrank ℚ (valueSpan y a) := by
  set P := (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))
  have hrange : LinearMap.range (quotForms P a) = NumbersDVR.gradedPiece P a := by
    rw [quotForms, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have hker : LinearMap.ker (quotForms P a) = LinearMap.ker (evalForms y a) := by
    ext ⟨f, hf⟩
    rw [mem_weightedHomogeneousSubmodule] at hf
    simp only [LinearMap.mem_ker, quotForms, evalForms, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    rw [show P = RingHom.ker (coneQ y) from map_mCoordIdeal y, mem_ker_iff y hf]
  rw [← hrange, ← range_evalForms y a, ← (quotForms P a).quotKerEquivRange.finrank_eq,
    ← (evalForms y a).quotKerEquivRange.finrank_eq]
  exact (Submodule.quotEquivOfEq _ _ hker).finrank_eq

end HilbFnValueSpan

theorem HilbFnValueSpan.proof : HilbFnValueSpan.Statement := by
  intro K _ _ ι _ Ω _ _ y a
  unfold NumbersDVR.hilbFn
  rw [if_pos (fun k => Int.natCast_nonneg _)]
  have ha : (fun k => ((a k : ℤ)).toNat) = a := funext fun k => Int.toNat_natCast _
  rw [ha, HilbFnValueSpan.finrank_gradedPiece]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Metric Module ZSpan

noncomputable section

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  (La : Submodule ℤ V) {c : ℝ}

theorem LatticeCount.exists_near (B : ShortLatticeBasis La c) (x : V) :
    ∃ μ ∈ La, ‖x + μ‖ ≤ finrank ℝ V * c := by
  let e := basisOfLinearIndependentOfCardEqFinrank' B.vec B.linearIndependent (Fintype.card_fin _)
  have he : ∀ i, e i = B.vec i := fun i ↦ by simp [e]
  refine ⟨-((floor e x : Submodule.span ℤ (Set.range e)) : V), ?_, ?_⟩
  · refine La.neg_mem ?_
    have hle : Submodule.span ℤ (Set.range e) ≤ La := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [he]
      exact B.mem i
    exact hle (floor e x).2
  · rw [← sub_eq_add_neg, ← fract_apply]
    calc ‖fract e x‖ ≤ ∑ i, ‖e i‖ := norm_fract_le e x
      _ ≤ ∑ _i : Fin (finrank ℝ V), c :=
          Finset.sum_le_sum fun i _ ↦ by rw [he]; exact B.norm_le i
      _ = _ := by simp

theorem LatticeCount.encard_le (B : ShortLatticeBasis La c) (b : ℝ) (x : V) :
    {y : V | y ∈ La ∧ ‖y‖ ≤ b}.encard ≤
      {g : La | g +ᵥ x ∈ closedBall (0 : V) (b + finrank ℝ V * c)}.encard := by
  classical
  obtain ⟨μ, hμ, hxμ⟩ := LatticeCount.exists_near La B x
  refine Set.encard_le_encard_of_injOn
    (f := fun y : V ↦ if h : y ∈ La then (⟨y + μ, La.add_mem h hμ⟩ : La) else 0) ?_ ?_
  · rintro y ⟨hy, hyb⟩
    simp only [Set.mem_ofPred_eq, hy, dif_pos, mem_closedBall, dist_zero_right,
      Submodule.vadd_def, vadd_eq_add]
    calc ‖y + μ + x‖ = ‖y + (x + μ)‖ := by congr 1; abel
      _ ≤ ‖y‖ + ‖x + μ‖ := norm_add_le _ _
      _ ≤ b + finrank ℝ V * c := add_le_add hyb hxμ
  · rintro y ⟨hy, -⟩ y' ⟨hy', -⟩ h
    simp only [hy, hy', dif_pos, Subtype.mk.injEq, add_left_inj] at h
    exact h

end

theorem LatticeCount.proof : LatticeCount.Statement := by
  intro V _ _ _ _ _ La _ _ c b B hb
  set R := finrank ℝ V with hRdef
  set S := {x : V | x ∈ La ∧ ‖x‖ ≤ b}
  have hfin : S.Finite := finite_lattice_closedBall La b
  refine ⟨hfin, ?_⟩
  have hRc : 0 ≤ (R : ℝ) * c := by
    rcases Nat.eq_zero_or_pos R with h | h
    · simp [h]
    · exact mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (B.norm_le ⟨0, h⟩))
  set r := b + R * c with hrdef
  have hr : 0 ≤ r := add_nonneg hb hRc
  have : MeasurableVAdd La V := (inferInstance : MeasurableVAdd La.toAddSubgroup V)
  have : VAddInvariantMeasure La V volume :=
    (inferInstance : VAddInvariantMeasure La.toAddSubgroup V volume)
  set bz := Free.chooseBasis ℤ La
  have hF := ZLattice.isAddFundamentalDomain bz volume
  set F := fundamentalDomain (bz.ofZLatticeBasis ℝ La)
  set A := closedBall (0 : V) r
  have hA : MeasurableSet A := measurableSet_closedBall
  have hmeas : ∀ g : La, Measurable fun x : V ↦ A.indicator (1 : V → ENNReal) (g +ᵥ x) :=
    fun g ↦ (measurable_one.indicator hA).comp (measurable_const_vadd g)
  have key : ∀ x : V,
      (S.encard : ENNReal) ≤ ∑' g : La, A.indicator (1 : V → ENNReal) (g +ᵥ x) := by
    intro x
    have hind : (fun g : La ↦ A.indicator (1 : V → ENNReal) (g +ᵥ x)) =
        {g : La | g +ᵥ x ∈ A}.indicator 1 := by
      funext g
      by_cases hg : g +ᵥ x ∈ A <;> simp [hg]
    rw [hind, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    exact_mod_cast LatticeCount.encard_le La B b x
  have hFfin : volume F ≠ ⊤ := (fundamentalDomain_isBounded _).measure_lt_top.ne
  have hvol : (S.encard : ENNReal) * ENNReal.ofReal (ZLattice.covolume La) ≤ volume A := by
    calc (S.encard : ENNReal) * ENNReal.ofReal (ZLattice.covolume La)
        = (S.encard : ENNReal) * volume F := by
          rw [ZLattice.covolume_eq_measure_fundamentalDomain La volume hF,
            ofReal_measureReal hFfin]
      _ = ∫⁻ _ in F, (S.encard : ENNReal) := (setLIntegral_const F _).symm
      _ ≤ ∫⁻ x in F, ∑' g : La, A.indicator 1 (g +ᵥ x) := lintegral_mono key
      _ = ∑' g : La, ∫⁻ x in F, A.indicator 1 (g +ᵥ x) :=
          lintegral_tsum fun g ↦ (hmeas g).aemeasurable
      _ = ∫⁻ x, A.indicator 1 x := (hF.lintegral_eq_tsum'' _).symm
      _ = volume A := lintegral_indicator_one hA
  have hunit : volume (ball (0 : V) 1) =
      volume (ball (0 : EuclideanSpace ℝ (Fin R)) 1) := by
    let f := (stdOrthonormalBasis ℝ V).repr
    rw [← f.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet,
      f.preimage_ball, map_zero]
  have hunitfin : volume (ball (0 : EuclideanSpace ℝ (Fin R)) 1) ≠ ⊤ :=
    isBounded_ball.measure_lt_top.ne
  have hball : volume A = ENNReal.ofReal (unitBallVolume R * r ^ R) := by
    rw [Measure.addHaar_closedBall volume 0 hr, hunit, unitBallVolume,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hunitfin, mul_comm]
  have hS : (S.encard : ENNReal) * ENNReal.ofReal (ZLattice.covolume La) =
      ENNReal.ofReal (S.ncard * ZLattice.covolume La) := by
    rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hpos : 0 ≤ unitBallVolume R * r ^ R :=
    mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hr _)
  have := (hS ▸ hvol).trans_eq hball
  exact (ENNReal.ofReal_le_ofReal_iff hpos).1 this

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Matrix Equiv
open scoped ComplexOrder

noncomputable section

theorem LogDetDerivative.hasDerivAt_det {m : ℕ} {G : ℝ → Matrix (Fin m) (Fin m) ℂ}
    {G' : Matrix (Fin m) (Fin m) ℂ} {t : ℝ} (h : ∀ i j, HasDerivAt (fun s ↦ G s i j) (G' i j) t) :
    HasDerivAt (fun s ↦ (G s).det) (∑ i, (G t).cramer (fun k ↦ G' k i) i) t := by
  have key : ∀ σ : Perm (Fin m), HasDerivAt (fun s ↦ ((Perm.sign σ : ℤ) : ℂ) * ∏ i, G s (σ i) i)
      (((Perm.sign σ : ℤ) : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, G t (σ j) j) * G' (σ i) i) t := by
    intro σ
    have := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i s ↦ G s (σ i) i)
      (f' := fun i ↦ G' (σ i) i) (x := t) (fun i _ ↦ h (σ i) i)
    simpa [smul_eq_mul] using this.const_mul ((Perm.sign σ : ℤ) : ℂ)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ ↦ key σ)
  have hfun : (fun s ↦ (G s).det) =
      fun s ↦ ∑ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : ℂ) * ∏ i, G s (σ i) i := by
    ext s
    exact det_apply' _
  rw [hfun]
  refine hsum.congr_deriv ?_
  symm
  rw [Finset.sum_congr rfl fun i _ ↦ cramer_apply (G t) (fun k ↦ G' k i) i]
  simp only [det_apply', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hrest : ∏ j ∈ Finset.univ.erase i, (G t).updateCol i (fun k ↦ G' k i) (σ j) j =
      ∏ j ∈ Finset.univ.erase i, G t (σ j) j := by
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    rw [updateCol_ne (Finset.ne_of_mem_erase hj)]
  rw [hrest, updateCol_self]
  ring

theorem LogDetDerivative.sum_cramer_eq {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ)
    (hA : IsUnit A.det) :
    ∑ i, A.cramer (fun k ↦ B k i) i = A.det * (A⁻¹ * B).trace := by
  simp only [← det_smul_inv_mulVec_eq_cramer A _ hA, Pi.smul_apply, smul_eq_mul, trace,
    diag_apply, Matrix.mul_apply, mulVec, dotProduct, Finset.mul_sum]

theorem LogDetDerivative.intersectionNumber_baseChange : LogDetDerivative.Statement := by
  intro m G G' hpos hG t
  have hdet := LogDetDerivative.hasDerivAt_det (hG t)
  rw [LogDetDerivative.sum_cramer_eq _ _ (hpos t).det_pos.ne'.isUnit] at hdet
  have hre : HasDerivAt (fun s ↦ (G s).det.re)
      ((G t).det * ((G t)⁻¹ * G' t).trace).re t := by
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hdet
  have hp := (hpos t).det_pos
  rw [Complex.lt_def] at hp
  obtain ⟨hre0, him0⟩ := hp
  simp only [Complex.zero_re, Complex.zero_im] at hre0 him0
  have hlog := (hre.log hre0.ne').const_mul (-(1 / 2) : ℝ)
  refine hlog.congr_deriv ?_
  rw [Complex.mul_re, ← him0, zero_mul, sub_zero]
  field_simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

theorem Weight.lerp_self_zero {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    {L : HolLineBundle A} (W : Weight L) : W.lerp W 0 = W := by
  cases W
  simp only [Weight.lerp, zero_mul, add_zero]

theorem SupNormAgainstL2.proof (h : UniformBergmanBound.Statement) : SupNormAgainstL2.Statement := by
  intro D X _ _ _ _ _ A L W dV hW
  obtain ⟨C, hC⟩ := h A L W W dV hW hW
  refine ⟨⟨Real.sqrt C, fun n hn s hs x => ?_⟩, fun n s hs M hM => ?_⟩
  · set V : Submodule ℂ (Fin A.n → X → ℂ) := ℂ ∙ s
    have hV : V ≤ L.sections n := (Submodule.span_singleton_le_iff_mem _ _).2 hs
    have hB := hC n hn 0 ⟨le_rfl, zero_le_one⟩ V hV x
    rw [Weight.lerp_self_zero] at hB
    set r := ptNormSq W n s x / sectionL2NormSq W dV n s
    have hr0 : 0 ≤ r := div_nonneg (ptNormSq_nonneg W n s x) (sectionL2NormSq_nonneg W dV n s)
    have hbdd : BddAbove (range fun v : V => ptNormSq W n (v : Fin A.n → X → ℂ) x /
        sectionL2NormSq W dV n v) := by
      refine ⟨r, ?_⟩
      rintro _ ⟨⟨v, hv⟩, rfl⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      simp only [ptNormSq_smul, sectionL2NormSq_smul]
      rcases eq_or_ne c 0 with rfl | hc
      · simpa using hr0
      · rw [mul_div_mul_left _ _ (by positivity)]
    have hle : r ≤ bergman W dV V n x :=
      le_ciSup hbdd (⟨s, Submodule.mem_span_singleton_self s⟩ : V)
    have hrC : r ≤ C * (n : ℝ) ^ D := hle.trans hB
    rcases (sectionL2NormSq_nonneg W dV n s).eq_or_lt with h0 | hpos
    · rw [ptNormSq_eq_zero_of_l2NormSq_eq_zero W dV hs h0.symm x, Real.sqrt_zero]
      positivity
    · have hpt : ptNormSq W n s x ≤ C * ((n : ℝ) ^ D * sectionL2NormSq W dV n s) := by
        rw [← mul_assoc, ← div_le_iff₀ hpos]; exact hrC
      calc Real.sqrt (ptNormSq W n s x)
          ≤ Real.sqrt (C * ((n : ℝ) ^ D * sectionL2NormSq W dV n s)) := Real.sqrt_le_sqrt hpt
        _ = Real.sqrt C * Real.sqrt ((n : ℝ) ^ D) * Real.sqrt (sectionL2NormSq W dV n s) := by
          rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_mul (by positivity), mul_assoc]
  · have := dV.isProb
    obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure dV.μ
    have hM0 : 0 ≤ M := (Real.sqrt_nonneg _).trans (hM x₀)
    have hpt : ∀ y, ptNormSq W n s y ≤ M ^ 2 := fun y => by
      have h1 := Real.sq_sqrt (ptNormSq_nonneg W n s y)
      have h2 := hM y
      nlinarith [Real.sqrt_nonneg (ptNormSq W n s y)]
    have hl2 : sectionL2NormSq W dV n s ≤ M ^ 2 := by
      calc sectionL2NormSq W dV n s ≤ ∫ _ : X, M ^ 2 ∂dV.μ :=
            integral_mono_of_nonneg (Eventually.of_forall fun y => ptNormSq_nonneg W n s y)
              (integrable_const _) (Eventually.of_forall hpt)
        _ = M ^ 2 := by simp
    calc Real.sqrt (sectionL2NormSq W dV n s) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt hl2
      _ = M := Real.sqrt_sq hM0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
