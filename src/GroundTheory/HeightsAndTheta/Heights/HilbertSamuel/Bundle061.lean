module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgePot
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle052
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle055
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle003
public import ReciprocityTheory.GeometryOfNumbers.AsymptoticSequences.ClosingHS

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartDenominator.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (b : K → ℤ) (τ : ℕ) (s : Ω),
    s ∈ chartLatQ y b τ → ∃ n : ℕ, 1 ≤ n ∧ (n : Ω) * s ∈ chartLat y b τ

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def BlockResolutionInterpIntegral.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), A'.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → IsSmoothHerm A' →
    ((D : ℝ) + 1) * blockMetricInt d A' =
      ∑ i ∈ Finset.range (D + 1),
        mInt d.R.A
          (fun j : Fin D => if j.val < i then AnResBridge.potOf d.R A' else AnResBridge.potOf d.R d.A)
          (fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

def BlockResolutionMetricPair.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0' : Ideal (MRing ι)),
    A'.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → P0' ≤ mCoordIdeal d.y → IsSemipositiveRel P0' (mCoordIdeal d.y) A' →
    ∃ (A : FinHolAtlas D d.R.X) (L : HolLineBundle A) (W₀ W₁ : Weight L) (dV : SmoothVolume A)
      (σ : ℕ → MvPolynomial (Σ k, ι k) ℚ → Fin A.n → d.R.X → ℂ),
      A.Compatible d.R.A ∧ W₀.IsSemipositive ∧ W₁.IsSemipositive ∧ dV.μ = d.dV ∧
      (∀ (n : ℕ) (b : MvPolynomial (Σ k, ι k) ℚ), IsMultiHomog b (blockDeg d.k₀ n) → σ n b ∈ L.sections n) ∧
      (∀ y : d.R.X, ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
        (∀ (n : ℕ) (b : MvPolynomial (Σ k, ι k) ℚ), IsMultiHomog b (blockDeg d.k₀ n) →
          σ n b (chartIdx A y) y = eval (fun p => c p.1 * blockPt d y p) (map (algebraMap ℚ ℂ) b)) ∧
        W₀.φ (chartIdx A y) y = 2 * Real.log (d.A.h (fun p => c p.1 * blockPt d y p)) ∧
        W₁.φ (chartIdx A y) y = 2 * Real.log (A'.h (fun p => c p.1 * blockPt d y p))) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ g : d.R.X → ℝ, Continuous g →
        ∫ y, g y * bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ =
          mInt d.R.A (fun _ => blockInterpPot d d.A A' t) g / (D.factorial : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

namespace FrameChange

section Matrices

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem matAct_matAct (A A' : Matrix J J ℚ) (x : J → Ω) : matAct A (matAct A' x) = matAct (A * A') x := by
  funext i
  simp only [matAct, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem isInvMat_mul {A A' : Matrix J J ℚ} (hA : IsInvMat A) (hA' : IsInvMat A') : IsInvMat (A * A') := by
  obtain ⟨C, hC⟩ := hA
  obtain ⟨C', hC'⟩ := hA'
  refine ⟨C' * C, fun v => ⟨?_, ?_⟩⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hC' (C.mulVec v)).1, (hC v).1]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hC (A'.mulVec v)).2, (hC' v).2]


open Classical in
def scaleMat {D : ℕ} (e : Fin (D + 1) → J) (m : ℕ) : Matrix J J ℚ :=
  Matrix.diagonal fun i => if i ∈ Set.range e then 1 else (m : ℚ)


open Classical in
theorem matAct_scaleMat {D : ℕ} (e : Fin (D + 1) → J) (m : ℕ) (y : J → Ω) :
    matAct (scaleMat e m) y = scaleOff e m y := by
  funext i
  simp only [matAct, scaleMat, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  rw [if_pos rfl]
  unfold scaleOff
  split_ifs <;> simp


open Classical in
theorem isInvMat_scaleMat {D : ℕ} (e : Fin (D + 1) → J) {m : ℕ} (hm : 0 < m) : IsInvMat (scaleMat e m) := by
  have hc : ∀ i, (if i ∈ Set.range e then 1 else (m : ℚ)) ≠ 0 := fun i => by
    split_ifs
    · exact one_ne_zero
    · exact_mod_cast hm.ne'
  refine ⟨Matrix.diagonal fun i => (if i ∈ Set.range e then 1 else (m : ℚ))⁻¹, fun v => ⟨?_, ?_⟩⟩
  · funext i
    simp only [scaleMat, Matrix.mulVec_diagonal]
    rw [← mul_assoc, mul_inv_cancel₀ (hc i), one_mul]
  · funext i
    simp only [scaleMat, Matrix.mulVec_diagonal]
    rw [← mul_assoc, inv_mul_cancel₀ (hc i), one_mul]

end Matrices

theorem proof (hN : RatNoetherFrame.Statement) (hT : HSMTransport.Statement) (hI : ResChiIndex.Statement) :
    FrameChange.Statement := by
  intro D Ω _ _ κ _ d
  obtain ⟨B₀, e, hB₀, hfr⟩ := hN D Ω κ d.x d.arith
  obtain ⟨m, hm, hfr'⟩ := exists_scaleOff_isProjFrame (matAct B₀ d.x) e hfr
  have hB : IsInvMat (scaleMat e m * B₀) := isInvMat_mul (isInvMat_scaleMat e hm) hB₀
  obtain ⟨d', hx', hm', hG⟩ := hT D Ω κ d _ hB
  have hx'' : d'.x = scaleOff e m (matAct B₀ d.x) := by
    rw [hx', ← matAct_matAct, matAct_scaleMat]
  refine ⟨_, d', e, hB, hx', hm', by rw [hx'']; exact hfr', ?_⟩
  have h0 := hI D Ω κ d d' _ hB hx' hG
  have hz : (fun n => resChi d' n - resChi d n - latLogIndex d.x d'.x n) = fun _ => (0 : ℝ) :=
    funext fun n => by rw [h0 n, sub_self]
  rw [hz]
  exact isLittleO_zero _ _

end FrameChange

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace GenDegAmple

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem hilbFn_nonneg {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (m : K → ℤ) : 0 ≤ NumbersDVR.hilbFn q m := by
  unfold NumbersDVR.hilbFn
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

theorem eventualValue_nonneg {K : Type} [Fintype K] (f : (K → ℤ) → ℤ) (hf : ∀ m, 0 ≤ f m) :
    0 ≤ eventualValue f := by
  unfold eventualValue
  split_ifs with h
  · obtain ⟨m, hm⟩ := h.choose_spec.exists
    rw [← hm]
    exact hf m
  · exact le_rfl

theorem unit_nonneg {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (e : ℕ) : ∀ q : Ideal (MRing ι F), NumbersDVR.IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ r : Fin e → K, 0 ≤ intNum F q (fun j => unitDeg (r j)) := by
  induction e with
  | zero =>
    intro q _ _ r
    unfold intNum mixedDiff
    rw [List.ofFn_zero, List.foldr_nil]
    exact eventualValue_nonneg _ (hilbFn_nonneg q)
  | succ e ih =>
    intro q hq hd r
    obtain ⟨i, hX⟩ := hq.relevant (r 0)
    have hd' : ringKrullDim (MRing ι F ⧸ q) = ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := hd
    have hsplit : (fun j : Fin (e + 1) => unitDeg (r j)) =
        Matrix.vecCons (unitDeg (r 0)) (fun j : Fin e => unitDeg (r j.succ)) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp
    rw [hsplit, IntersectionRecursion.proof F K ι q e hq hd' (r 0) i hX]
    refine finsum_nonneg fun W => ?_
    split_ifs with h
    · exact mul_nonneg (Int.natCast_nonneg _) (ih W h.1 h.2.2 _)
    · exact le_rfl

end GenDegAmple

theorem GenDegAmple.proof (hVar : GenericFibreVar.Statement) (hPos : MultiDegreePositive.Statement) :
    GenDegAmple.Statement := by
  intro K _ ι _ Ω _ y D d hV hd
  classical
  have hPV := hVar K ι Ω y D hV
  have hP := (Bridge.isMultiProjPrime_iff _).mpr hPV.1
  have hrel : FieldNumbers.relDim (KH.genIdeal y) = D := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hPV.2]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  set f := intNumMultilinear (KH.genIdeal y) D hP.multiHomog hP.relevant hrel with hf
  have hg : ∀ b, genDeg (mCoordIdeal y) D b = f (fun _ => b) := fun b => by
    rw [hf, intNumMultilinear_apply, genDeg]
    congr
  have hN : ∀ r : Fin D → K, 0 ≤ f (fun j => unitDeg (r j)) := fun r => by
    rw [hf, intNumMultilinear_apply]
    exact GenDegAmple.unit_nonneg D _ hP hPV.2 r
  have hH : 0 < f (fun _ => fun _ => (1 : ℤ)) := by
    rw [hf, intNumMultilinear_apply]
    exact hPos ℚ K ι _ D hP hPV.2
  have hsum : ∀ b : K → ℤ, (fun _ : Fin D => b) = fun _ => ∑ k, b k • unitDeg k := fun b => by
    funext _ k'
    simp [unitDeg, Finset.sum_apply, Pi.single_apply]
  have expand : ∀ b : K → ℤ,
      f (fun _ => b) = ∑ r : Fin D → K, (∏ j, b (r j)) * f (fun j => unitDeg (r j)) := fun b => by

    rw [hsum b, f.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [f.map_smul_univ (fun j => b (r j)) (fun j => unitDeg (r j)), smul_eq_mul]
    simp only [RingHom.id_apply]
  rw [hg, expand d]
  have hH' := hH
  rw [expand (fun _ => (1 : ℤ))] at hH'
  simp only [Finset.prod_const_one, one_mul] at hH'
  refine lt_of_lt_of_le hH' (Finset.sum_le_sum fun r _ => ?_)
  have hp : (1 : ℤ) ≤ ∏ j, d (r j) := by
    calc (1 : ℤ) = ∏ _j : Fin D, (1 : ℤ) := Finset.prod_const_one.symm
      _ ≤ ∏ j, d (r j) := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun j _ => hd (r j))
  exact le_mul_of_one_le_left (hN r) hp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem BlockMetricChange.proof (hMeas : BlockMeasureChange.Statement)
    (hMet : BlockDefectMetricChange.Statement) : BlockMetricChange.Statement := by
  intro D K _ _ ι _ Ω _ _ I d d' hI hy hk
  have hdeg : d'.A.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ := hk ▸ d'.deg
  have hle : d'.P0 ≤ mCoordIdeal d.y := hy ▸ d'.normalForm_baseLattice_le_dualSpan_sup_line
  have hp : IsSemipositiveRel d'.P0 (mCoordIdeal d.y) d'.A := hy ▸ d'.semipos

  have h1 := hMeas D K ι Ω (d.withMetric d'.A d'.P0 hdeg d'.conjInv hle hp) d' hy hk rfl
  have h2 := hMet D K ι Ω I d d'.A d'.P0 hdeg d'.conjInv hle hp hI
  refine (h1.add h2).congr_left fun n => ?_
  simp only [hsDefect, hy]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockComplexGramMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0' : Ideal (MRing ι))
    (hdeg : A'.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀) (hc : IsConjInvariantH A') (hle : P0' ≤ mCoordIdeal d.y)
    (hp : IsSemipositiveRel P0' (mCoordIdeal d.y) A'),
    (fun n => blockCChi (d.withMetric A' P0' hdeg hc hle hp) n - blockCChi d n -
        (n : ℝ) ^ (D + 1) / (D.factorial : ℝ) * blockMetricInt d A') =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

theorem GenDegGeomDeg.proof (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    GenDegGeomDeg.Statement := by
  intro K _ ι _ Ω _ y D A hV hA
  classical
  have h := hDG K ι (mCoordIdeal y) D (fun _ => A) hV (fun _ => hA)
  have hpot : pot (fun _ : Fin D => A) = fun (_ : Fin D) z => Real.log (A.h z) := rfl
  rw [hpot] at h
  unfold geomDeg genDeg
  rw [h]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem chiP_zero_dim (n : ℕ) : chiP 0 n = 0 := by
  simp [chiP, monoNormSq, Finset.Nat.antidiagonalTuple_one]

theorem HilbertSamuelProjective.proof (hR : ReductionToProjective.Statement) (hV : SecondVeronese.Statement)
    (h0 : PointHeightFS.Statement) : HilbertSamuelProjective.Statement := by
  intro D I hI
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · have hh := h0 I hI
    refine (isLittleO_zero (fun n : ℕ => (n : ℝ) ^ (0 + 1)) atTop).congr' ?_ EventuallyEq.rfl
    refine Eventually.of_forall fun n => ?_
    simp [hsDefect, hh, chiP_zero_dim]
  · obtain ⟨Ω, _, _, κ, _, d, hchi, htop, hdeg⟩ := hV D hD
    have h2 := (hR D Ω κ I d hI).2
    have hfun : resChi d = fun m => chiP D (2 * m) := funext hchi
    rw [hfun, htop I hI, hdeg] at h2
    push_cast at h2
    exact hilbertSamuelDefect_projectiveSpace_isLittleO D (hhOf I D) h2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem TheoremHSMBlock.proof (hR : ReductionToProjectiveBlock.Statement)
    (hP : HilbertSamuelProjective.Statement) (hS : SupBoundBlock.Statement) :
    TheoremHSMBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ I d hI
  refine ⟨?_, hS D K ι Ω d⟩
  have h1 := hR D K ι Ω I d hI
  have h2 := (hP D I hI).const_mul_left (genDeg (mCoordIdeal d.y) D d.A.a : ℝ)
  refine (h1.add h2).congr_left fun n => ?_
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def BlockImageGenDeg.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (κ : Type) [Fintype κ] (y : (Σ k, ι k) → Ω) (k₀ : K) (M : Matrix (Ix κ) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix κ) ℤ) (x : Ix κ → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsBlockImage y k₀ M N x →
    genDeg (ι := GlobalTheory κ) (coordIdeal ℤ x) D 1 = genDeg (mCoordIdeal y) D (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg k₀)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
