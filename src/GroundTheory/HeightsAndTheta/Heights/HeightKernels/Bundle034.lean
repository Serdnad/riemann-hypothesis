module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineSemipositive
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualGeomDegCharts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle026
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle028
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 MvPolynomial

namespace StandardDualBaseChange

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

theorem isMultiHomog_linForm (A : ∀ _ : Unit, Fin i → T → ℤ) (q : Σ _ : Unit, Fin i) :
    IsMultiHomog (linForm (ι := dualBlocks T) (ι₂ := PBlk i) A q) fun _ => 1 := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  cases k
  simp [Finsupp.single_apply]


omit [DecidableEq T] in
theorem exists_linForm_not_mem (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hP : IsArithVar (dualIdeal b) i)
    (hBP : IsBasePtFree (K₂ := Unit) (ι₂ := PBlk i) (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b))) :
    ∀ k₂ : Unit, ∃ j, linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨k₂, j⟩ ∉ dualIdeal b := by
  intro k₂
  by_contra hall
  simp only [not_exists, not_not] at hall
  obtain ⟨-, ⟨hprime, -, hrel⟩, -, -⟩ := hP
  obtain ⟨t, ht⟩ := hrel ()
  obtain ⟨N, hN⟩ := hBP k₂ fun _ => t
  have hle : Ideal.span (Set.range fun j : Fin i =>
      linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨k₂, j⟩) ≤ dualIdeal b :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hall)
  rw [sup_eq_left.mpr hle, Fintype.prod_unique] at hN
  exact ht (hprime.mem_of_pow_mem N hN)

end StandardDualBaseChange


open StandardDualBaseChange in
theorem DualStdBaseChange.proof (hCM : ChangeOfModelStatement) (hGr : GraphStatement)
    (hGF : GenFibreExistsStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hBP : DualStdBasePtFree.Statement) (hIm : DualStdImageBot.Statement)
    (hDeg : DualStdGenDeg.Statement) (hMet : DualStdMetricPull.Statement) :
    DualStdBaseChange.Statement := by
  intro K _ _ i T _ _ b hb II hi hII
  have hP : IsArithVar (dualIdeal b) i :=
    DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K i _ T b hi
  have hBPb := hBP K i T b
  have hGraph := (hGr Unit (dualBlocks T) Unit (PBlk i) (dualIdeal b) i
    (linForm (ι₂ := PBlk i) (dualStdCoordMat b)) (fun _ _ => 1) hP
    (isMultiHomog_linForm _) (exists_linForm_not_mem b hP hBPb)).1
  obtain ⟨G⟩ := hGF Unit (PBlk i) (Unit ⊕ Unit) (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr inrV _ i
    isBlockMap_inr hGraph
  obtain ⟨J, hJ, -⟩ := hEU G.Φ _ (fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) (Sum.inr : Unit → Unit ⊕ Unit))
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hbot : IsArithVar (imageZ (inrV (ι := dualBlocks T) (ι₂ := PBlk (n + 1)))
      (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk (n + 1)) (dualStdCoordMat b)))) (n + 1) := by
    rw [hIm K (n + 1) T b]
    exact IndefiniteRowSideFullHecke.Inter.isArithVar_bot n
  have key := hCM II hII Unit (dualBlocks T) (PBlk (n + 1)) (dualIdeal b) (n + 1) (dualStdCoordMat b) G J
    (fun _ => fsMulti (PBlk (n + 1))) (fun _ => dualLine (HermLattice.standard K (n + 1)) b hb)
    hP hBPb hbot hJ (fun _ => FsLineSmooth.proof Unit (PBlk (n + 1)))
    (fun _ => (DualLineSemipositive.proof K (n + 1) _ T b hb).1) (fun _ => rfl)
    (fun _ z hz => hMet K (n + 1) T b hb z hz)
  rw [key, hDeg K (n + 1) T b G J hi hJ, hIm K (n + 1) T b]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial Matrix NumberField
open scoped ComplexOrder

noncomputable section

namespace DualPointLineDegreeAlt

theorem sum_log_norm {L : Type*} [Field L] [NumberField L] {x : L} (hx : x ≠ 0) :
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |(Algebra.norm ℚ x : ℝ)| := by
  classical
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx))]
  congr 1
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ (fun φ => ‖φ x‖)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← norm_prod,
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real,
    Real.norm_eq_abs]

theorem isMultiHomog_X {T : Type} [Fintype T] (t : T) :
    IsMultiHomog (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) (fun _ => 1) := by
  classical
  intro m hm k
  obtain ⟨⟩ := k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  rw [Finset.sum_eq_single t]
  · simp
  · intro c _ hc
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hc (sigma_mk_injective h).symm
  · simp

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type} {K' : Type} [Field K'] [NumberField K'] [Algebra K K']

theorem dualNormSq_point (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (v : Fin i → K') (σ' : K' →+* ℂ) :
    dualNormSq b hb (fun t => σ' (dualPointCoord b v ⟨(), t⟩)) =
      (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re := by
  classical
  set σ := σ'.comp (algebraMap K K') with hσ
  let w : (K →+* ℂ) × Fin i → ℂ := fun q => if q.1 = σ then σ' (v q.2) else 0
  have hw : dualRecover b hb (fun t => σ' (dualPointCoord b v ⟨(), t⟩)) = w := by
    rw [dualRecover, LinearEquiv.symm_apply_eq]
    funext t

    simp only [LinearEquiv.ofBijective_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    dualEmbMatrix, w, Fintype.sum_prod_type, mul_ite, mul_zero, dualPointCoord, map_sum, map_mul]
    rw [Finset.sum_eq_single σ (fun τ _ hτ => by simp [hτ]) (by simp)]
    simp [hσ]
  rw [dualNormSq, hw, Finset.sum_eq_single σ, Matrix.det_unique]
  · simp only [w, if_true, gramAt]
    rfl
  · intro τ _ hτ
    have h0 : (fun j => w (τ, j)) = 0 := by
      funext j
      simp [w, hτ]
    rw [h0]
    simp
  · simp

end DualPointLineDegreeAlt


open DualPointLineDegreeAlt in
theorem DualPointLineDegree.proof (hPt : DualCurvePoint.Statement) (hPos : PointDegCPos.Statement)
    (hAr : PointArInt.Statement) (hVert : PointVertR.Statement) (hIdx : DualLineIndex.Statement)
    (hSemi : DualLineSemipositive.Statement) : DualPointLineDegree.Statement := by
  intro K _ _ i F T _ _ b hb II hII W hW hbW
  obtain ⟨K', _, _, _, v, hv, rfl⟩ := hPt K i F T b W hW hbW
  set y := dualPointCoord b v with hy
  set A := dualLine F b hb with hA
  refine ⟨hPos T K' y hW, K', inferInstance, inferInstance, inferInstance, v, hv, ?_⟩
  obtain ⟨t₀, ht₀⟩ := hW.2.1.2.2 ()
  set s : MRing (dualBlocks T) := X ⟨(), t₀⟩ with hs
  have hs1 : IsMultiHomog s (fun _ => 1) := isMultiHomog_X t₀
  have hsec : IsSectionOn (mCoordIdeal y) A s := ⟨fun _ => 1, fun _ => rfl, hs1, ht₀⟩
  have hsm : IsSmoothHerm A := (hSemi K i F T b hb).1
  have hy0 : y ⟨(), t₀⟩ ≠ 0 := by
    intro h
    apply ht₀
    change mConeMap y (X ⟨(), t₀⟩) = 0
    simp [mConeMap, h]

  have hR := (hII Unit (dualBlocks T)).2.2 (mCoordIdeal y) 0 Fin.elim0 A s (fun _ => 1) hW
    (fun j => j.elim0) hsm (fun _ => rfl) hs1 ht₀
  have hsnoc :
      (Fin.snoc (Fin.elim0 : Fin 0 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) A :
        Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)) =
      ![A] := by
    funext j
    fin_cases j
    rfl
  rw [hsnoc, Inter.SpecIntHeightFormula.proof Inter.arithVarZero Unit (dualBlocks T) _ _ A s hW hsm hsec] at hR

  have hV := hVert T K' y s hW hs1 ht₀
  have hI := hAr T K' y A s hW hsec
  have hL := hIdx K i F T b K' v hv
  have hys : aeval y s = y ⟨(), t₀⟩ := by simp [hs]
  have hlog : ∀ σ' : K' →+* ℂ, logNorm A s (fun p => σ' (y p)) =
      Real.log ‖σ' (y ⟨(), t₀⟩)‖ -
        1 / 2 * Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re := by
    intro σ'
    have hq : dualNormSq b hb (fun t => σ' (y ⟨(), t⟩)) =
        (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re :=
      dualNormSq_point b hb v σ'
    have hpos : 0 < dualNormSq b hb (fun t => σ' (y ⟨(), t⟩)) := by
      have := A.pos (fun p => σ' (y p)) (fun _ => ⟨t₀, (map_ne_zero σ').mpr hy0⟩)
      simpa [hA, dualLine] using this
    have hne : ‖σ' (y ⟨(), t₀⟩)‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero σ').mpr hy0)
    simp only [logNorm, hs, map_X, eval_X, hA, dualLine]
    rw [Real.log_div hne (Real.sqrt_pos.mpr hpos).ne', Real.log_sqrt hpos.le, ← hq]
    ring
  rw [Finset.sum_congr rfl fun σ' _ => hlog σ', Finset.sum_sub_distrib,
    sum_log_norm hy0, ← Finset.mul_sum] at hI
  rw [hys] at hV
  have hn : (0 : ℝ) < Module.finrank ℚ K' := by exact_mod_cast Module.finrank_pos
  have hd : (0 : ℝ) < degC (mCoordIdeal y) := by exact_mod_cast hPos T K' y hW
  rw [← hy] at hL
  have hdeg : F.lineDegree K' v = (-Real.log (genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
      (1 : Submodule (𝓞 K') K').toAddSubgroup) - 1 / 2 * ∑ σ' : K' →+* ℂ,
        Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re) /
      Module.finrank ℚ K' := by
    unfold HermLattice.lineDegree subDegree normalise
    rw [eq_inv_of_mul_eq_one_left hL, Real.log_inv]
  have hR' : II Unit (dualBlocks T) (mCoordIdeal y) 1 ![A] =
      vertR (mCoordIdeal y) Fin.elim0 s - arInt (mCoordIdeal y) s A Fin.elim0 := hR
  have key : (vertR (mCoordIdeal y) Fin.elim0 s - arInt (mCoordIdeal y) s A Fin.elim0) *
      Module.finrank ℚ K' = degC (mCoordIdeal y) * (Real.log (genIndex
        (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup) +
        1 / 2 * ∑ σ' : K' →+* ℂ,
          Real.log (gramAt (F.metric (σ'.comp (algebraMap K K'))) σ' (fun _ : Fin 1 => v)).det.re) := by
    linear_combination hV - hI
  rw [hdeg, hR', neg_div, ← neg_div, div_eq_div_iff hn.ne' hd.ne']
  linear_combination key

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter Topology Matrix NumberField
open scoped ComplexOrder

noncomputable section

namespace DualEnergyChartsAlt

open StandardDualMassAtPoint DualGeometricDegreeCharts

variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]
  {D : ℕ} {F : HermLattice K (D + 1)}

def chartMat (hOf : DualPtsOfPlane.Statement) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)} (hΨ : IsGoodProj (dualIdeal b) Ψ)
    (σ : K →+* ℂ) : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ :=
  LinearMap.toMatrix' (LinearEquiv.ofBijective _ (restr_bijective hOf b hb hΨ σ)).symm.toLinearMap

theorem atProj (hOn : DualPtsOnPlane.Statement) (hOf : DualPtsOfPlane.Statement)
    (hInt : ChartEnergyIntegrable.Statement) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)) (hΨ : IsGoodProj (dualIdeal b) Ψ) :
    (∀ σ, Function.Bijective (chartMat hOf b hb hΨ σ).mulVec) ∧ ∀ k : ℕ,
      ptsIntegralAt (e := D) (dualIdeal b) Ψ
          (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
          (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
        ∑ σ : K →+* ℂ, chartMixedEnergy ((chartMat hOf b hb hΨ σ)ᴴ * F.metric σ * chartMat hOf b hb hΨ σ)
          ((chartMat hOf b hb hΨ σ)ᴴ * chartMat hOf b hb hΨ σ) k := by
  set A := chartMat hOf b hb hΨ with hAdef
  let E : (K →+* ℂ) → (Fin (D + 1) → ℂ) ≃ₗ[ℂ] (Fin (D + 1) → ℂ) := fun σ =>
    LinearEquiv.ofBijective _ (restr_bijective hOf b hb hΨ σ)
  have hAv : ∀ σ v, A σ *ᵥ v = (E σ).symm v := fun σ v => LinearMap.toMatrix'_mulVec _ v
  have hAbij : ∀ σ, Function.Bijective (A σ).mulVec := fun σ => by
    have : (A σ).mulVec = (E σ).symm := funext (hAv σ)
    rw [this]
    exact (E σ).symm.bijective
  have hΨA : ∀ σ v, Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ v))) = v := fun σ v => by
    rw [hAv]
    exact (E σ).apply_symm_apply v
  have huniq : ∀ σ v c, Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ v)) = c → v = A σ *ᵥ c :=
    fun σ v c h => (E σ).injective (by
      show Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ v)) =
        Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ c)))
      rw [h, hΨA])
  have hne : ∀ σ (y : Fin D → ℂ), A σ *ᵥ Fin.cons 1 y ≠ 0 := fun σ y h0 => by
    have h1 : Fin.cons 1 y = (0 : Fin (D + 1) → ℂ) := (hAbij σ).1 (h0.trans (Matrix.mulVec_zero _).symm)
    simpa using congrFun h1 0
  have hfib : ∀ y : Fin D → ℂ, _root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre (dualIdeal b) Ψ y =
      Set.range fun σ : K →+* ℂ => segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) := by
    intro y
    ext w
    constructor
    · rintro ⟨z, hz, rfl, hΨz⟩
      obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
      have hz' := eq_planePt b hb hσ
      have hv : recLin b hb σ z = A σ *ᵥ Fin.cons 1 y := huniq σ _ _ (by rw [← hz']; exact hΨz)
      refine ⟨σ, ?_⟩
      show segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) = segre z
      rw [← hv, ← hz']
    · rintro ⟨σ, rfl⟩
      exact ⟨_, hOf K (D + 1) F T b hb σ _ (hne σ y), rfl, hΨA σ _⟩
  have hsheet : ∀ σ (y : Fin D → ℂ), IsSheet (dualIdeal b) Ψ y
      (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)))
      (fun y' => dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y')) := by
    intro σ y
    have hc : Differentiable ℂ (fun y' : Fin D → ℂ => (Fin.cons 1 y' : Fin (D + 1) → ℂ)) := by
      rw [differentiable_pi]
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · simpa using differentiable_apply (𝕜 := ℂ) k
    refine ⟨rfl, Filter.Eventually.of_forall fun y' => ⟨?_, hOf K (D + 1) F T b hb σ _ (hne σ y'), hΨA σ _⟩⟩
    refine (differentiable_pi.mpr fun p => ?_) y'
    simp only [dualPlanePt, Matrix.mulVec, dotProduct]
    exact Differentiable.fun_sum fun j _ =>
      (Differentiable.fun_sum fun k _ => (differentiable_pi.mp hc k).const_mul _).const_mul _

  have hnear : ∀ σ (y : Fin D → ℂ) γ, IsSheet (dualIdeal b) Ψ y
      (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) γ →
      ∀ᶠ y' in 𝓝 y, γ y' = dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y') := by
    intro σ y γ hγ
    have hγy : γ y = dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y) := by
      funext ⟨u, t⟩
      cases u
      have h1 := congrFun hγ.1 (fun _ => t)
      simpa only [segre_const] using h1
    have hcont : ContinuousAt γ y := (hγ.2.self_of_nhds).1.continuousAt
    have hR : ∀ᶠ y' in 𝓝 y, recLin b hb σ (γ y') ≠ 0 := by
      have hc : ContinuousAt (fun y' => recLin b hb σ (γ y')) y :=
        (LinearMap.continuous_of_finiteDimensional (recLin b hb σ)).continuousAt.comp hcont
      apply hc.eventually_ne
      rw [hγy, recLin_planePt]
      exact hne σ y
    filter_upwards [hγ.2, hR] with y' hy' hRy'
    obtain ⟨-, hmc, hΨy'⟩ := hy'
    obtain ⟨ρ, hρ⟩ := hOn K (D + 1) F T b hb _ hmc
    have hρσ : ρ = σ := by
      by_contra h
      apply hRy'
      funext k
      exact hρ σ (Ne.symm h) k
    subst hρσ
    have hz' := eq_planePt b hb hρ
    have hv : recLin b hb ρ (γ y') = A ρ *ᵥ Fin.cons 1 y' :=
      huniq ρ _ _ (by rw [← hz']; exact hΨy')
    rw [hz', hv]

  have hpotF : ∀ σ (y' : Fin D → ℂ), Real.log ((dualLine F b hb).h (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y'))) =
      hermChartPot ((A σ)ᴴ * F.metric σ * A σ) y' := fun σ y' => by
    rw [h_planePt, hermChartPot_eq]
  have hpotS : ∀ σ (y' : Fin D → ℂ),
      Real.log ((dualLine F.withStdMetric b hb).h (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y'))) =
      hermChartPot ((A σ)ᴴ * A σ) y' := fun σ y' => by
    have h1 := h_planePt (F := F.withStdMetric) b hb σ (A σ *ᵥ Fin.cons 1 y')
    have h2 := hermChartPot_eq (A σ) (1 : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) y'
    rw [Matrix.mul_one] at h2
    rw [h2]
    exact congrArg Real.log h1
  refine ⟨hAbij, fun k => ?_⟩
  have hdens : ∀ σ (y : Fin D → ℂ), sheetDensity (dualIdeal b) Ψ
      (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
      (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) y
      (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) =
      (hermChartPot ((A σ)ᴴ * F.metric σ * A σ) y - hermChartPot ((A σ)ᴴ * A σ) y) *
        maDensity (fun j : Fin D => if (j : ℕ) < k then hermChartPot ((A σ)ᴴ * F.metric σ * A σ)
          else hermChartPot ((A σ)ᴴ * A σ)) y := by
    intro σ y
    have hex : ∃ γ, IsSheet (dualIdeal b) Ψ y
        (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) γ := ⟨_, hsheet σ y⟩
    unfold sheetDensity
    rw [dite_eq_left hex]
    have hev := hnear σ y _ hex.choose_spec
    beta_reduce
    rw [hev.self_of_nhds, hpotF, hpotS]
    congr 1
    apply maDensity_congr_of_eventuallyEq
    intro j
    filter_upwards [hev] with y' hy'
    simp only [pot]
    rw [hy']
    split_ifs
    · exact hpotF σ y'
    · exact hpotS σ y'
  have hinj : ∀ y : Fin D → ℂ, Function.Injective fun σ : K →+* ℂ =>
      segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) :=
    fun y σ τ h => planePt_inj b hb (hne σ y) h
  have hsum : ∀ y : Fin D → ℂ, ∑ᶠ w ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre (dualIdeal b) Ψ y,
      sheetDensity (dualIdeal b) Ψ
        (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
        (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) y w =
      ∑ σ : K →+* ℂ, (hermChartPot ((A σ)ᴴ * F.metric σ * A σ) y - hermChartPot ((A σ)ᴴ * A σ) y) *
        maDensity (fun j : Fin D => if (j : ℕ) < k then hermChartPot ((A σ)ᴴ * F.metric σ * A σ)
          else hermChartPot ((A σ)ᴴ * A σ)) y := by
    intro y
    rw [hfib y, finsum_mem_range (hinj y), finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun σ _ => hdens σ y
  have hN : ∀ σ, ((A σ)ᴴ * A σ).PosDef := fun σ => by
    simpa using (Matrix.PosDef.one (n := Fin (D + 1)) (R := ℂ)).conjTranspose_mul_mul_same (hAbij σ).1
  unfold ptsIntegralAt
  simp only [hsum]
  rw [integral_finsetSum _ fun σ _ =>
    hInt D _ _ ((F.posDef σ).conjTranspose_mul_mul_same (hAbij σ).1) (hN σ) k]
  rfl

end DualEnergyChartsAlt


open DualEnergyChartsAlt DualGeometricDegreeCharts in
theorem DualEnergyCharts.proof (hInt : ChartEnergyIntegrable.Statement) : DualEnergyCharts.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨D, rfl⟩ : ∃ D, i = D + 1 := ⟨i - 1, by omega⟩
  have hex : ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (dualIdeal b) Ψ := ⟨_, dualProj_good DualPtsOnPlane.proof b hb⟩
  obtain ⟨hA, hE⟩ := atProj DualPtsOnPlane.proof DualPtsOfPlane.proof hInt b hb hex.choose hex.choose_spec
  refine ⟨chartMat DualPtsOfPlane.proof b hb hex.choose_spec, hA, fun k => ?_⟩
  show ptsIntegral (e := D) (dualIdeal b)
      (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
      (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) = _
  unfold ptsIntegral
  rw [dite_eq_left hex]
  exact hE k

end

end GroundTheory.Heights₂.Heights
end
