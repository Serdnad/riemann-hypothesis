module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import Mathlib.Algebra.MvPolynomial.Funext
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle007
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle001
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import Mathlib.Analysis.Calculus.ContDiff.Defs
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ComplexHessianIsHermitianOfContDiffAt

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology

noncomputable section

theorem exists_eval_ne_zero_of_isOpen {d : ℕ} {P : MvPolynomial (Fin d) ℂ} (hP : P ≠ 0)
    {S : Set (Fin d → ℂ)} (hS : IsOpen S) (hne : S.Nonempty) : ∃ y ∈ S, eval y P ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hS y₀ hy₀
  by_contra h
  push Not at h
  apply hP
  have hinf : ∀ i, (Metric.ball (y₀ i) r).Infinite := fun i =>
    infinite_of_mem_nhds (y₀ i) (Metric.ball_mem_nhds _ hr)
  refine (funext_set_iff (p := P) (q := 0) _ hinf).mpr fun y hy => ?_
  rw [map_zero]
  exact h y (hball (by rwa [ball_pi _ hr]))

theorem eval_linPoly {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (z : Fin n → ℂ) :
    (fun i => eval z (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i)) = A.mulVec z := by
  ext i
  simp [GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]

theorem finrank_real_fin_complex (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Complex.finrank_real_complex, smul_eq_mul, mul_comm]

theorem ZeroSetOpenMass.proof
    (hG : GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement)
    (hD : GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.Statement)
    (hF : FiniteMapOpen.Statement) : ZeroSetOpenMass.Statement := by
  intro n d W hW hdim x O hO hxO hxZ
  obtain ⟨A, hA⟩ := (hG n d W hW hdim).2.1
  obtain ⟨P, hP0, hPcov⟩ := hD n d W A hW hdim hA
  have hopen := hF n d W (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A) hW hA.injective hA.finite x hxZ O
    (hO.mem_nhds hxO)
  have hfun : (fun z : Fin n → ℂ => fun i => eval z (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i)) =
      fun z => A.mulVec z := funext (eval_linPoly A)
  rw [hfun, eval_linPoly A x] at hopen
  obtain ⟨y, hyS, hPy⟩ := exists_eval_ne_zero_of_isOpen hP0 isOpen_interior
    ⟨_, mem_interior_iff_mem_nhds.mpr hopen⟩
  obtain ⟨z, ⟨hzW, hzO⟩, hzy⟩ := interior_subset hyS
  subst hzy
  obtain ⟨-, -, hloc⟩ := hPcov _ hPy
  obtain ⟨U, V, g, hU, hzU, hV, hzV, hg, hgz, hAg, hZV⟩ := hloc z ⟨hzW, rfl⟩
  set U' := U ∩ g ⁻¹' (O ∩ V) with hU'def
  have hU' : IsOpen U' := hg.continuousOn.isOpen_inter_preimage hU (hO.inter hV)
  have hzU' : A.mulVec z ∈ U' := ⟨hzU, by simp only [Set.mem_preimage, hgz]; exact ⟨hzO, hzV⟩⟩
  have hsub : g '' U' ⊆ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ O := by
    rintro _ ⟨w, ⟨hwU, hwO, -⟩, rfl⟩
    have hw : g w ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ V := by
      rw [hZV]; exact Set.mem_image_of_mem g hwU
    exact ⟨hw.1, hwO⟩
  have himg : (fun z => A.mulVec z) '' (g '' U') = U' := by
    rw [Set.image_image]
    exact (Set.image_congr fun w (hw : w ∈ U') => hAg w hw.1).trans (Set.image_id' _)
  obtain ⟨K, hK⟩ : ∃ K, LipschitzWith K (fun z : Fin n → ℂ => A.mulVec z) :=
    ⟨_, (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).lipschitz⟩
  have hpos : 0 < μH[((2 * d : ℕ) : ℝ)] U' := by
    rw [← finrank_real_fin_complex d]
    exact hU'.measure_pos _ ⟨_, hzU'⟩
  have hle := hK.hausdorffMeasure_image_le (by positivity : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ)) (g '' U')
  rw [himg] at hle
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at hle
  exact hpos.ne' (nonpos_iff_eq_zero.mp hle)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

namespace PrimitiveElementFibres

variable {n d : ℕ}

theorem algebraMap_C_eq (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) (a : ℂ) :
    projHom J A (C a) = Ideal.Quotient.mk J (C a) := by
  simp [projHom, pullback]
  rfl

theorem adjoin_eq_top (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ) :
    (letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (projHom J A).toRingHom.toAlgebra
    Algebra.adjoin (MvPolynomial (Fin d) ℂ)
      (Set.range fun j : Fin n => Ideal.Quotient.mk J (X j)) = ⊤) := by
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  rw [eq_top_iff]
  rintro b -
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective b
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : Ideal.Quotient.mk J (C a) = algebraMap (MvPolynomial (Fin d) ℂ) _ (C a) :=
      (algebraMap_C_eq J A a).symm
    rw [h]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq =>
    rw [map_add]
    exact add_mem hp hq
  | mul_X p i hp => rw [map_mul]; exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

def evalAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) (hx : x ∈ zeroSet J) :
    MvPolynomial (Fin n) ℂ ⧸ J →+* ℂ :=
  Ideal.Quotient.lift J (eval x) (fun q hq => hx q hq)

theorem evalAt_projHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {y : Fin d → ℂ} {x : Fin n → ℂ} (hx : x ∈ fibre J A y) (P : MvPolynomial (Fin d) ℂ) :
    evalAt J x hx.1 (projHom J A P) = eval y P := by
  change eval x (pullback A P) = _
  rw [FibreBound.eval_pullback, hx.2]

theorem proof : PrimitiveElementFibres.Statement := by
  intro n d J A hJ _ hA
  have := hJ
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := (projHom J A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) := hA.injective
  obtain ⟨c, m, D, Q, hmon, hdeg, hdiv, hD, ⟨a, b, hab⟩, hQ⟩ :=
    PrimitiveLinearForm.exists_primitive_data hinj (MvPolynomial.C : ℂ →+* (MvPolynomial (Fin d) ℂ))
      (fun j : Fin n => Ideal.Quotient.mk J (X j)) (adjoin_eq_top J A)
  set ℓ : (MvPolynomial (Fin n) ℂ ⧸ J) := ∑ j, algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (C (c j)) * Ideal.Quotient.mk J (X j) with hℓ
  have hℓmk : ℓ = Ideal.Quotient.mk J (∑ j, C (c j) * X j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hℓ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    congr 1
    exact algebraMap_C_eq J A (c j)

  have hev : ∀ y (x : Fin n → ℂ) (hx : x ∈ fibre J A y) (p : Polynomial (MvPolynomial (Fin d) ℂ)),
      evalAt J x hx.1 (Polynomial.aeval ℓ p) = (p.map (eval y)).eval (∑ j, c j * x j) := by
    intro y x hx p
    have h1 : (evalAt J x hx.1).comp (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) = eval y :=
      RingHom.ext fun P => evalAt_projHom J A hx P
    have h2 : evalAt J x hx.1 ℓ = ∑ j, c j * x j := by
      rw [hℓmk]
      change eval x (∑ j, C (c j) * X j) = _
      simp
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, h1, h2, Polynomial.eval_map]
  refine ⟨c, m, D, Q, hmon, hdeg, hD, fun y hy => ⟨?_, ?_, ?_⟩⟩
  ·
    have h := congrArg (Polynomial.map (eval y)) hab
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C,
      ← Polynomial.derivative_map] at h
    have hu : Polynomial.C (eval y D)⁻¹ * Polynomial.C (eval y D) = (1 : Polynomial ℂ) := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hy, Polynomial.C_1]
    exact ⟨Polynomial.C (eval y D)⁻¹ * a.map (eval y), Polynomial.C (eval y D)⁻¹ * b.map (eval y),
      by linear_combination Polynomial.C (eval y D)⁻¹ * h + hu⟩
  · intro x hx
    refine ⟨?_, fun j => ?_⟩
    · have h := congrArg (evalAt J x hx.1) ((hdiv m).mpr dvd_rfl)
      rw [hev y x hx, map_zero] at h
      exact h
    · have h := congrArg (evalAt J x hx.1) (hQ j)
      have h3 : evalAt J x hx.1 (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) D) =
          eval y D := evalAt_projHom J A hx D
      have h4 : evalAt J x hx.1 (Ideal.Quotient.mk J (X j)) = x j := by simp [evalAt]
      rw [hev y x hx, map_mul, h3, h4] at h
      exact h
  ·
    intro τ hτ
    let _ : Algebra (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) := (Polynomial.aeval ℓ).toRingHom.toAlgebra
    set_option synthInstance.maxHeartbeats 100000 in
      have : IsScalarTower (MvPolynomial (Fin d) ℂ) (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) :=
        IsScalarTower.of_algebraMap_eq fun r => (Polynomial.aeval_C ℓ r).symm
    have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.IsIntegral.of_finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)
    have : Algebra.IsIntegral (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ⟨fun s => (Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) s).tower_top⟩
    let evτ : Polynomial (MvPolynomial (Fin d) ℂ) →+* ℂ := (Polynomial.evalRingHom τ).comp (Polynomial.mapRingHom (eval y))
    have hmax : (RingHom.ker evτ).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun z => ⟨Polynomial.C (C z), by simp [evτ]⟩)
    have hker : RingHom.ker (algebraMap (Polynomial (MvPolynomial (Fin d) ℂ)) (MvPolynomial (Fin n) ℂ ⧸ J)) ≤ RingHom.ker evτ := by
      intro p hp
      obtain ⟨q, rfl⟩ := (hdiv p).mp hp
      rw [RingHom.mem_ker, map_mul]
      have : evτ m = 0 := hτ
      rw [this, zero_mul]
    obtain ⟨P, hP, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := (MvPolynomial (Fin n) ℂ ⧸ J)) _ hker
    have hP' : (P.comap (Ideal.Quotient.mk J)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hP'
    have hmem : ∀ q, Ideal.Quotient.mk J q ∈ P → eval x q = 0 := by
      intro q hq
      have hq' : q ∈ P.comap (Ideal.Quotient.mk J) := hq
      rw [hx] at hq'
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x q).mp hq'
    have hover : ∀ p : Polynomial (MvPolynomial (Fin d) ℂ), evτ p = 0 → Polynomial.aeval ℓ p ∈ P := by
      intro p hp
      have : p ∈ (RingHom.ker evτ) := hp
      rw [← hPc] at this
      exact this
    have hxZ : x ∈ zeroSet J :=
      fun q hq => hmem q (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq]; exact P.zero_mem)
    refine ⟨x, ⟨hxZ, ?_⟩, ?_⟩
    · funext i
      have h1 := hover (Polynomial.C (X i - C (y i))) (by simp [evτ])
      rw [Polynomial.aeval_C] at h1
      have h2 := hmem (pullback A (X i - C (y i))) h1
      rw [FibreBound.eval_pullback] at h2
      simpa [sub_eq_zero] using h2
    · have h1 := hover (Polynomial.X - Polynomial.C (C τ)) (by simp [evτ])
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hℓmk] at h1
      have h3 : algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) (C τ) = Ideal.Quotient.mk J (C τ) := algebraMap_C_eq J A τ
      rw [h3, ← map_sub] at h1
      have h2 := hmem _ h1
      simpa [sub_eq_zero] using h2

end PrimitiveElementFibres

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff

noncomputable section

def cutStep (t : ℝ) : ℝ := Real.smoothTransition (2 - 2 * t)

def cutLevel (k : ℕ) : ℝ := Real.exp (-Real.exp ((k : ℝ) + 1))

def logAbsSq {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) : ℝ :=
  Real.log (‖eval y Q‖ ^ 2)

def logLogCut {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (k : ℕ) (y : Fin m → ℂ) : ℝ :=
  if ‖eval y Q‖ ^ 2 = 0 then 0
  else if 1 ≤ ‖eval y Q‖ ^ 2 then 1
  else cutStep (Real.log (-logAbsSq Q y) / ((k : ℝ) + 1))

def logLogCutAlong {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (Q : MvPolynomial (Fin m) ℂ) (k : ℕ)
    (x : Fin n → ℂ) : ℝ :=
  logLogCut Q k (A *ᵥ x)

def tubeWeight {m : ℕ} (Q : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) : ℝ :=
  if logAbsSq Q y ≤ -1 then (logAbsSq Q y ^ 2)⁻¹ else 0

def tubeDens {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ) (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) :
    (Fin (d + 1) → ℂ) → ℝ :=
  chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => tubeWeight P (A *ᵥ x))
    (vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) φ)

def CutOffShape.Statement : Prop :=
  ∀ (m : ℕ) (Q : MvPolynomial (Fin m) ℂ),
    (∀ k, ContDiff ℝ ∞ (logLogCut Q k) ∧ (∀ y, logLogCut Q k y ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ y, ‖eval y Q‖ ^ 2 < cutLevel k → logLogCut Q k y = 0) ∧
    ∀ y, eval y Q ≠ 0 → Tendsto (fun k => logLogCut Q k y) atTop (𝓝 1)

theorem cutLevel_mem (k : ℕ) : 0 < cutLevel k ∧ cutLevel k < 1 := by
  refine ⟨Real.exp_pos _, Real.exp_lt_one_iff.2 (neg_neg_of_pos (Real.exp_pos _))⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def ConeSliceSheetParam.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (A : Matrix (Fin e) (Fin n) ℂ),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J → IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A →
      ∃ (U D : ℕ → Set (Fin e → ℂ)) (N : ℕ → ℕ)
        (s : (k : ℕ) → Fin (N k) → (Fin e → ℂ) → Fin n → ℂ),
        (∀ k, IsOpen (U k) ∧ MeasurableSet (D k) ∧ D k ⊆ U k ∧
          ∀ j, DifferentiableOn ℂ (s k j) (U k)) ∧
        Pairwise (Function.onFun Disjoint D) ∧
        volume (⋃ k, D k)ᶜ = 0 ∧
        (∀ k, ∀ y ∈ U k,
          ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y = Set.range (fun j => s k j y) ∧
          Function.Injective (fun j => s k j y) ∧
          ∀ j, IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A (s k j y) (s k j)) ∧
        Set.InjOn (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
            q.2.2 • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s q.1.1 q.1.2 q.2.1))
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ∧
        (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
            q.2.2 • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s q.1.1 q.1.2 q.2.1)) ''
          {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ⊆
          {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0} ∧
        Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
          ({z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0} \
            (fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
              q.2.2 • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s q.1.1 q.1.2 q.2.1)) ''
              {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0}) = 0

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def ChartIntCountAdd.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (E : ℕ → Set (Fin n → ℂ)),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) → IsFiniteProjection W A →
    Continuous f → HasCompactSupport f → (∀ k, SmoothNear (zeroSet W) (φ k)) →
    (∀ i, MeasurableSet (E i)) → Pairwise (Function.onFun Disjoint E) →
      HasSum (fun i => chartInt W A ((E i).indicator f) φ) (chartInt W A ((⋃ i, E i).indicator f) φ)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def DiscriminantSheetCover.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
      ∃ (P : MvPolynomial (Fin d) ℂ) (U D : ℕ → Set (Fin d → ℂ)) (N : ℕ → ℕ)
        (s : (k : ℕ) → Fin (N k) → (Fin d → ℂ) → Fin n → ℂ),
        P ≠ 0 ∧
        (∀ k, IsOpen (U k) ∧ MeasurableSet (D k) ∧ D k ⊆ U k ∧
          ∀ j, DifferentiableOn ℂ (s k j) (U k)) ∧
        Pairwise (Function.onFun Disjoint D) ∧
        (⋃ k, D k)ᶜ ⊆ {y | eval y P = 0} ∧
        volume (⋃ k, D k)ᶜ = 0 ∧
        (∀ k, ∀ y ∈ U k,
          ComplexSets.fibre J A y = Set.range (fun j => s k j y) ∧
          Function.Injective (fun j => s k j y) ∧
          ∀ j, IsSheetAt J A (s k j y) (s k j))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff

noncomputable section

def PolydiscLelongLimit.Statement : Prop :=
  ∀ (d m : ℕ) (r ρ : ℝ) (F : (Fin (d + 1) → ℂ) → ℂ) (χ : (Fin (d + 1) → ℂ) → ℝ)
    (ψ : Fin d → (Fin (d + 1) → ℂ) → ℝ),
    ρ < r → VanishesToOrder F r m → ContDiffOn ℝ ∞ χ (Metric.ball 0 r) →
    (∀ τ ∈ Metric.ball (0 : Fin (d + 1) → ℂ) r, χ τ ≠ 0 → τ ∈ Metric.ball 0 ρ) →
    (∀ k, ContDiffOn ℝ ∞ (ψ k) (Metric.ball 0 r)) →
      Tendsto (fun ε : ℝ =>
          ReciprocityTheory.AnForm.maInt (vecCons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) χ (Metric.ball 0 r))
        (𝓝[>] 0)
        (𝓝 ((m : ℝ) * ∫ w in Metric.ball (0 : Fin d → ℂ) r,
          χ (ReciprocityTheory.AnForm.A.hypIncl w) * ReciprocityTheory.AnForm.A.densHyp ψ w))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

def HessCCompPluri.Statement : Prop :=
  ∀ (D : ℕ) (F : ℝ → ℝ) (L : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ),
    ContDiffAt ℝ 2 F (L z) → ContDiffAt ℝ 2 L z → hessC L z = 0 →
      hessC (fun w => F (L w)) z = ((deriv (deriv F) (L z) : ℝ) : ℂ) • hessC (fun w => L w ^ 2 / 2) z

end

end GroundTheory.Heights₂.Heights
end
