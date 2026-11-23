module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle002
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Separation.CompletelyRegular
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntSphere
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

noncomputable section

def zeroExt (m k : ℕ) : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin (m + k)) where
  toFun x := WithLp.toLp 2 (Fin.append (fun i => x i) 0)
  map_add' x y := by
    ext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
  map_smul' c x := by
    ext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

theorem norm_zeroExt (m k : ℕ) (x : EuclideanSpace ℂ (Fin m)) : ‖zeroExt m k x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, zeroExt, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.sum_univ_add]
  simp

theorem isometry_zeroExt (m k : ℕ) : Isometry (zeroExt m k) :=
  AddMonoidHomClass.isometry_of_norm (zeroExt m k) (norm_zeroExt m k)

theorem coordBall_mass {n m : ℕ} (hmn : m ≤ n) :
    0 < Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0} ∧
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0} < ⊤ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hset : {y : EuclideanSpace ℂ (Fin (m + k)) | ‖y‖ < 1 ∧ ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0} =
      zeroExt m k '' Metric.ball 0 1 := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨hy, hz⟩
      refine ⟨WithLp.toLp 2 fun i => y (Fin.castAdd k i), ?_, ?_⟩
      · rw [← norm_zeroExt m k]
        convert hy using 2
        ext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [zeroExt]
        · simp [zeroExt, hz (Fin.natAdd m i) (by simp)]
      · ext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [zeroExt]
        · simp [zeroExt, hz (Fin.natAdd m i) (by simp)]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨by rwa [norm_zeroExt], fun j hj => ?_⟩
      revert hj
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · intro hi
        simp at hi
        omega
      · intro _
        simp [zeroExt]
  rw [hset, (isometry_zeroExt m k).hausdorffMeasure_image (Or.inl (by positivity))]
  have hd : ((2 * m : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  rw [hd]
  exact ⟨Metric.measure_ball_pos _ _ one_pos, measure_ball_lt_top⟩

def linProjₗ {m n : ℕ} (π : Fin m → Fin n → ℂ) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) where
  toFun := linProj π
  map_add' x y := by
    ext i
    simp [linProj, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    simp [linProj, Finset.mul_sum, mul_left_comm]

theorem ae_fibreCount_eq_zero {n m : ℕ} (hnm : n < m) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (π : Fin m → Fin n → ℂ) :
    ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w = 0 := by
  set R := (LinearMap.range (linProjₗ π)).restrictScalars ℝ
  have hR : R ≠ ⊤ := by
    intro hT
    rw [Submodule.restrictScalars_eq_top_iff] at hT
    have h1 := LinearMap.finrank_range_le (linProjₗ π)
    rw [hT, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at h1
    omega
  have h0 : volume (R : Set (EuclideanSpace ℂ (Fin m))) = 0 := Measure.addHaar_submodule _ R hR
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with w hw
  rw [fibreCount, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro y ⟨-, rfl⟩
  exact hw ⟨y, rfl⟩

theorem ConeIntegralMass.proof (hF : ConeFibreDegree.Statement) (hM : ConeMassOfFibre.Statement) :
    ConeIntegralMass.Statement := by
  intro n e δ h W f hW hf hδ
  have hfib := hF n e δ h W f hW hf hδ
  have hmass := hM n (e + 1) δ h W hW hfib
  unfold coneIntegral
  simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  rw [hmass]
  by_cases hn : e + 1 ≤ n
  · obtain ⟨hpos, hfin⟩ := coordBall_mass hn
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_div_assoc,
      div_self (ENNReal.toReal_pos hpos.ne' hfin.ne).ne', mul_one]
  · have hδ0 : δ = 0 := by
      have : (volume : Measure (Fin (e + 1) → Fin n → ℂ)).IsAddHaarMeasure :=
        Measure.pi.isAddHaarMeasure _
      have : (ae (volume : Measure (Fin (e + 1) → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
      have : (ae (volume : Measure (EuclideanSpace ℂ (Fin (e + 1))))).NeBot :=
        ae_neBot.2 (NeZero.ne _)
      obtain ⟨π, hπ⟩ := hfib.exists
      obtain ⟨w, hw1, hw2⟩ := (hπ.and (ae_fibreCount_eq_zero (by omega) h W π)).exists
      rw [hw1] at hw2
      exact_mod_cast hw2
    simp [hδ0]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre)

open scoped ENNReal ComplexOrder

theorem gramVol_nonneg {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) :
    0 ≤ gramVol v y := by
  unfold gramVol
  dsimp only
  set w : Fin (e + 1) → Fin n → ℂ := Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1)
  have hM : (Matrix.of fun a b => ∑ i, star (w a i) * w b i) =
      (Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i)ᴴ *
        Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have h := (Matrix.posSemidef_conjTranspose_mul_self
    (Matrix.of fun (i : Fin n) (a : Fin (e + 1)) => w a i)).det_nonneg
  rw [← hM] at h
  exact (Complex.nonneg_iff.1 h).1

section Abstract

variable {E X W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]

variable [MeasurableSpace X]

end Abstract

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem ConeMeetNull.null_of_mem_not_mem (hZ : ZeroLocusDimH.Statement) {n e : ℕ} (h : HermNorm n)
    (W W' : Ideal (MvPolynomial (Fin n) ℂ)) [W.IsPrime]
    (hW : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (g : MvPolynomial (Fin n) ℂ) (hgW' : g ∈ W') (hgW : g ∉ W) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W ∩ coneBall h W') = 0 := by
  set J : Ideal (MvPolynomial (Fin n) ℂ) := W ⊔ Ideal.span {g} with hJ

  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (e : ℕ) :=
    ZeroLocusDimH.le_of_add_one_le_succ
      ((ZeroLocusDimH.ringKrullDim_quot_sup_add_one_le W g hgW).trans hW)

  let φ : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ) :=
    (Matrix.transpose h.mat).mulVecLin.comp (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  have hφ : ∀ y, φ y = h.pointOf y := fun _ => rfl
  have hinj : Function.Injective φ := by
    have hu : IsUnit (Matrix.transpose h.mat) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact h.isUnit_det
    exact (Matrix.mulVec_injective_iff_isUnit.mpr hu).comp
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).injective
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz φ).mp hinj

  have hsub : coneBall h W ∩ coneBall h W' ⊆ φ ⁻¹' {x | ∀ q ∈ J, eval x q = 0} := by
    rintro y ⟨⟨-, hyW⟩, ⟨-, hyW'⟩⟩
    have hle : J ≤ RingHom.ker (eval (h.pointOf y)) := by
      refine sup_le (fun q hq => (RingHom.mem_ker).2 (hyW q hq)) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      exact hyW' g hgW'
    intro q hq
    rw [hφ]
    exact (RingHom.mem_ker).1 (hle hq)
  have hdimH : dimH (coneBall h W ∩ coneBall h W') ≤ 2 * (e : ENNReal) :=
    (dimH_mono hsub).trans ((hK.dimH_preimage_le _).trans (hZ n e J hdim))
  have hlt : dimH (coneBall h W ∩ coneBall h W') < (((2 * (e + 1) : ℕ) : NNReal) : ENNReal) := by
    refine hdimH.trans_lt ?_
    rw [ENNReal.coe_natCast]
    exact_mod_cast (by omega : 2 * e < 2 * (e + 1))
  rw [show ((2 * (e + 1) : ℕ) : ℝ) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) from
    (NNReal.coe_natCast _).symm]
  exact hausdorffMeasure_of_dimH_lt hlt

theorem ConeMeetNull.proof (hZ : ZeroLocusDimH.Statement) : ConeMeetNull.Statement := by
  intro n e h W W' hWp hW'p hne hW hW'
  by_cases hle : W' ≤ W
  ·
    have hnle : ¬ W ≤ W' := fun h' => hne (le_antisymm h' hle)
    obtain ⟨g, hgW, hgW'⟩ := Set.not_subset.mp hnle
    rw [Set.inter_comm]
    exact ConeMeetNull.null_of_mem_not_mem hZ h W' W hW' g hgW hgW'
  · obtain ⟨g, hgW', hgW⟩ := Set.not_subset.mp hle
    exact ConeMeetNull.null_of_mem_not_mem hZ h W W' hW g hgW' hgW

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealSeparate.proof (hZ : IncidenceZeroLocus.Statement) (hT : FormsThroughPoint.Statement)
    (hD : IncIdealNeBotDim.Statement) : IncIdealSeparate.Statement := by
  intro F _ n k P Q hP hQ hne hle q hqQ
  by_contra hqP
  have := hP.isPrime

  obtain ⟨φ, hφ⟩ : ∃ φ : (MvPolynomial (Fin n) F ⧸ P) →ₐ[F] AlgebraicClosure F,
      φ (Ideal.Quotient.mk P q) ≠ 0 := by
    by_contra h
    push Not at h
    exact hqP (Ideal.Quotient.eq_zero_iff_mem.mp
      (FGNullstellensatz.proof F (MvPolynomial (Fin n) F ⧸ P) (Ideal.Quotient.mk P q) h))
  let x : Fin n → AlgebraicClosure F := fun j => φ (Ideal.Quotient.mk P (X j))
  have hev : ∀ g, aeval x g = φ (Ideal.Quotient.mk P g) := by
    intro g
    have h : (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F) =
        φ.comp (Ideal.Quotient.mkₐ F P) := by
      ext j
      simp [x]
    rw [h]
    rfl
  have hxq : aeval x q ≠ 0 := by rw [hev]; exact hφ
  have hx0 : x ≠ 0 := by
    intro h0
    apply hxq
    have hc : constantCoeff q = 0 := by
      by_contra hc
      have hmem := hQ.isHomog q hqQ 0
      rw [homogeneousComponent_zero, ← constantCoeff_eq] at hmem
      exact hQ.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit hc).map C))
    rw [h0, aeval_zero, hc, map_zero]

  obtain ⟨u, hux, huQ⟩ := hT F n k Q hQ (hD F n k Q hQ hne) x hx0 ⟨q, hqQ, hxq⟩
  apply huQ
  refine hZ F n k Q hQ.isHomog (AlgebraicClosure F) u fun g hg => ?_
  have hgP := hle hg
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hgP
  refine hgP u ⟨x, hx0, fun g' hg' => ?_, hux⟩
  rw [hev, Ideal.Quotient.eq_zero_iff_mem.mpr hg', map_zero]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ThroughPointIncIdeal.eval_aeval {F K : Type*} [Field F] [Field K] [Algebra F K] {σ τ : Type*}
    (s : σ → MvPolynomial τ K) (a : τ → K) (g : MvPolynomial σ F) :
    eval a (aeval s g) = aeval (fun i => eval a (s i)) g := by
  induction g using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem ThroughPointIncIdeal.eval_genSubst_vanish {K : Type*} [Field K] {n k : ℕ} (x c : Fin n → K)
    (hc : ∑ j, c j * x j = 1) (a : Fin k × Fin n → K) (i : Fin k) :
    ∑ j, eval a (genSubst (k := k) x c (i, j)) * x j = 0 := by
  have h : ∀ j, eval a (genSubst (k := k) x c (i, j)) =
      a (i, j) - (∑ l, a (i, l) * x l) * c j := fun j => by simp [genSubst]
  simp_rw [h, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hc, mul_one, sub_self]

theorem ThroughPointIncIdeal.proof : ThroughPointIncIdeal.Statement := by
  intro F _ n k Q x c hc hinc g hg
  apply MvPolynomial.funext
  intro a
  rw [map_zero, ThroughPointIncIdeal.eval_aeval]
  have hu := hinc (fun ij => eval a (genSubst (k := k) x c ij))
    (ThroughPointIncIdeal.eval_genSubst_vanish x c hc a)
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hg
  exact hg _ hu

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ProjSecDomain.Statement : Prop :=
  ∀ (n e : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    W.IsPrime → ComplexSets.IsFiniteProjection W A →
      IsDomain (Vertical.SecAlg
          (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
          (projPar A)) ∧
        Module.Finite (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
          (Vertical.SecAlg
            (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
            (projPar A))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set MvPolynomial

noncomputable section

namespace LogInt

variable {n k : ℕ}

def ballSet (h : HermNorm n) (k : ℕ) : Set (Fin k × Fin n → ℂ) :=
  {u | ∀ i, h.norm (fun j => u (i, j)) < 1}

theorem measurableSet_ballSet (h : HermNorm n) : MeasurableSet (ballSet h k) := by
  have e : ballSet h k = ⋂ i, {u : Fin k × Fin n → ℂ | h.norm (fun j => u (i, j)) < 1} := by
    ext u; simp [ballSet]
  rw [e]
  exact MeasurableSet.iInter fun i => measurableSet_lt (measurable_groupNorm h i) measurable_const

theorem ballSet_subset_polydisc (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) :
    ballSet h k ⊆ polydisc _ C := by
  intro u hu
  simp only [polydisc, mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  intro ij
  exact (hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)

theorem normT_univ (h : HermNorm n) (u : Fin k × Fin n → ℂ) :
    normT h Finset.univ u = fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij := by
  funext ij
  simp [normT]

theorem integrableOn_log_mahler (h : HermNorm n) (f : MvPolynomial (Fin k × Fin n) ℂ) (hf : f ≠ 0) :
    IntegrableOn (fun u : Fin k × Fin n → ℂ =>
        Real.log ‖eval (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij) f‖)
        (ballSet h k) ∧
      ∀ᵐ u ∂(volume.restrict (ballSet h k)),
        eval (fun ij => ((h.norm fun j => u (ij.1, j) : ℝ) : ℂ)⁻¹ * u ij) f ≠ 0 := by
  obtain ⟨C, hC0, hC⟩ := h.li_exists_coord_le
  obtain ⟨h1, h2⟩ := logNormT h C hC0 hC Finset.univ f hf
  simp only [normT_univ] at h1 h2
  exact ⟨h1.mono_set (ballSet_subset_polydisc h C hC0 hC),
    ae_restrict_of_ae_restrict_of_subset (ballSet_subset_polydisc h C hC0 hC) h2⟩

end LogInt

theorem mahlerMul : MahlerMul.Statement := by
  intro n k h f g hf hg
  obtain ⟨i1, z1⟩ := LogInt.integrableOn_log_mahler h f hf
  obtain ⟨i2, z2⟩ := LogInt.integrableOn_log_mahler h g hg
  unfold mahler sphereMean
  change ⨍ u in LogInt.ballSet h k, _ = (⨍ u in LogInt.ballSet h k, _) + ⨍ u in LogInt.ballSet h k, _
  rw [setAverage_eq, setAverage_eq, setAverage_eq, ← smul_add, ← integral_add i1 i2]
  congr 1
  refine setIntegral_congr_ae (LogInt.measurableSet_ballSet h) ?_
  have := (ae_restrict_iff' (LogInt.measurableSet_ballSet h)).mp (z1.and z2)
  filter_upwards [this] with u hu hB
  obtain ⟨h1, h2⟩ := hu hB
  rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)]

end

end GroundTheory.Heights₂.Heights
end
