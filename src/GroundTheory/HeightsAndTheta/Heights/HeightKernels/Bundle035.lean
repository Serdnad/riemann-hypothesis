module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineSemipositive
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StandardModelDualRank
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle023
public import Mathlib.Algebra.Module.Lattice.Full
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle030
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 NumberField

noncomputable section

namespace TopDualMetricChange

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

theorem hermLine_ext {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)}
    (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A; cases B; cases ha; cases hh; rfl

theorem dualLine_h_zero (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ)
    (hz : ¬ ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0) : (dualLine F b hb).h z = 0 := by
  have h0 : (fun t => z ⟨(), t⟩) = 0 := by
    funext t; by_contra h; exact hz fun _ => ⟨t, h⟩
  show Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩) = 0
  rw [h0]
  simp [dualNormSq, ← Pi.zero_def]

def weight (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) : ((Σ _ : Unit, T) → ℂ) → ℝ :=
  fun z => Real.log ((dualLine F.withStdMetric b hb).h z) - Real.log ((dualLine F b hb).h z)

theorem weight_hom (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    ∀ (c : Unit → ℂ) z, (∀ k, c k ≠ 0) → weight F b hb (fun p => c p.1 * z p) = weight F b hb z := by
  intro c z hc
  by_cases hz : ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0
  · simp only [weight]
    rw [(dualLine F.withStdMetric b hb).smul c z hc, (dualLine F b hb).smul c z hc]
    have ha : (dualLine F.withStdMetric b hb).a = (dualLine F b hb).a := rfl
    have hs : 0 < ∏ k, ‖c k‖ ^ (dualLine F b hb).a k :=
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
    rw [ha, Real.log_mul hs.ne' ((dualLine F.withStdMetric b hb).pos z hz).ne',
      Real.log_mul hs.ne' ((dualLine F b hb).pos z hz).ne']
    ring
  · have hz0 : ∀ p, z p = 0 := by
      rintro ⟨k, t⟩; by_contra h; exact hz fun _ => ⟨t, h⟩
    congr 1; funext p; simp [hz0 p]

theorem weight_smooth (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) : SmoothFn (weight F b hb) :=
  ((DualLineSemipositive.proof K i F.withStdMetric T b hb).1.log fun z hz =>
      ((dualLine F.withStdMetric b hb).pos z hz).ne').sub
    ((DualLineSemipositive.proof K i F T b hb).1.log fun z hz => ((dualLine F b hb).pos z hz).ne')

theorem dualLine_eq_tensor (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    dualLine F b hb = (dualLine F.withStdMetric b hb).tensor
      (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight (weight F b hb) (weight_hom F b hb)) := by
  refine hermLine_ext (funext fun _ => by simp [ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight, dualLine]) ?_
  funext z
  show (dualLine F b hb).h z = (dualLine F.withStdMetric b hb).h z * Real.exp (-weight F b hb z)
  by_cases hz : ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0
  · have h1 := (dualLine F.withStdMetric b hb).pos z hz
    have h2 := (dualLine F b hb).pos z hz
    rw [weight, neg_sub, Real.exp_sub, Real.exp_log h1, Real.exp_log h2]
    field_simp
  · rw [dualLine_h_zero F b hb z hz, dualLine_h_zero F.withStdMetric b hb z hz, zero_mul]

theorem ptsIntegral_neg {κ : Type} [Fintype κ] {ι : κ → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ (fun z => -g z) = -ptsIntegral P φ g := by
  have hs : ∀ Ψ y w, sheetDensity P Ψ φ (fun z => -g z) y w = -sheetDensity P Ψ φ g y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> simp [neg_mul]
  unfold ptsIntegral ptsIntegralAt
  split_ifs
  · rw [← MeasureTheory.integral_neg]
    simp only [hs, finsum_neg_distrib]
  · simp

theorem degree_withStdMetric_sub (F : HermLattice K i) :
    F.withStdMetric.degree - F.degree = 1 / 2 * ∑ σ : K →+* ℂ, Real.log (F.metric σ).det.re := by
  simp only [HermLattice.degree, subDegree, HermLattice.withStdMetric, IndefiniteRowSideFullHecke.Kernels.gramAt_single,
    Matrix.det_one, Complex.one_re, Real.log_one, Finset.sum_const_zero, mul_zero, sub_zero]
  ring

end TopDualMetricChange


open TopDualMetricChange in
theorem DualTopMetricChange.proof (hTel : TelescopeStatement) (hEnergy : DualMetricEnergy.Statement) :
    DualTopMetricChange.Statement := by
  intro K _ _ i F T _ _ b hb II hi hII
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hP : IsArithVar (dualIdeal b) (n + 1) :=
    DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K (n + 1) F T b hi
  have hT := hTel Unit (dualBlocks T) (II Unit (dualBlocks T)) (hII Unit (dualBlocks T)) (dualIdeal b) n
    (dualLine F.withStdMetric b hb) (weight F b hb) (weight_hom F b hb) hP
    (DualLineSemipositive.proof K (n + 1) F.withStdMetric T b hb).1 (weight_smooth F b hb)
  rw [← dualLine_eq_tensor F b hb] at hT
  have hw : weight F b hb = fun z =>
      -(Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) := by
    funext z; simp only [weight]; ring
  rw [hw] at hT
  simp only [ptsIntegral_neg, Finset.sum_neg_distrib, neg_neg] at hT
  have hE : ∑ k ∈ Finset.range (n + 1),
      ptsIntegral (dualIdeal b)
        (pot fun j : Fin n => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
        (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
      1 / 2 * (∑ σ : K →+* ℂ, Real.log (F.metric σ).det.re) *
        geomDeg (grassIdeal 1 1 (n + 1 - 1)) (fsMulti (plBlocks 1 1 (n + 1 - 1))) (1 * 1 * (n + 1 - 1)) :=
    hEnergy K (n + 1) F T b hb hi
  rw [degree_withStdMetric_sub F]
  linarith

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section


open StandardModelDualRank in
theorem DualStdModelRank.proof : DualStdModelRank.Statement := by
  intro K _ _ i T _ _ b Φ₀ _ _ hΦ _ c
  have hrange : Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i)) = Set.range (u K i) := by
    ext x
    constructor
    · rintro ⟨⟨⟨⟩, j⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨(), j⟩, rfl⟩
  rw [hrange] at hΦ
  refine ⟨?_, ?_⟩
  · change dualStdModelEmb K i (dualLatticeCoord b ⟨(), c⟩) * dualStdModelS K i ≠ 0
    exact mul_ne_zero (coord_ne_zero b c) S_ne_zero
  have hr : (fun t : T => dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
      dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)) =
      fun t => w b t * (w b c)⁻¹ := by
    funext t
    change dualStdModelEmb K i (dualLatticeCoord b ⟨(), t⟩) * dualStdModelS K i /
      (dualStdModelEmb K i (dualLatticeCoord b ⟨(), c⟩) * dualStdModelS K i) = _
    rw [← div_eq_mul_inv, w, w, mul_div_mul_right (_ * dualStdModelS K i) _ (T_ne_zero (K := K) (i := i))]
  rw [hr]
  let B := Module.finBasis ℚ K
  let M' := Algebra.adjoin Φ₀ (Set.range (embK K i))
  have hM' : Subalgebra.toSubmodule M' = Submodule.span Φ₀ (Set.range fun k => embK K i (B k)) :=
    adjoin_embK_eq_span B Φ₀
  have hfg : (Subalgebra.toSubmodule M').FG := by
    rw [hM']
    exact Submodule.fg_span (Set.finite_range _)
  have hwM' : ∀ t, w b t ∈ M' := fun t => by
    rw [w_eq]
    refine Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨_, rfl⟩) ?_
    have hu : u K i j ∈ (algebraMap Φ₀ (dualStdModelField K i)).fieldRange := by
      rw [hΦ]
      exact Subfield.subset_closure ⟨j, rfl⟩
    obtain ⟨g, hg⟩ := RingHom.mem_fieldRange.mp hu
    rw [← hg]
    exact Subalgebra.algebraMap_mem _ g
  have hMM' : Algebra.adjoin Φ₀ (Set.range fun t => w b t * (w b c)⁻¹) ≤ M' := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨t, rfl⟩
    exact Subalgebra.mul_mem _ (hwM' t) (Subalgebra.inv_mem_of_algebraic M' (x := ⟨w b c, hwM' c⟩)
      (IsIntegral.of_mem_of_fg M' hfg _ (hwM' c)).isAlgebraic)
  have hβM : ∀ a, embK K i a ∈ Algebra.adjoin Φ₀ (Set.range fun t => w b t * (w b c)⁻¹) := fun a => by
    obtain ⟨N, hN, n, hn⟩ := _root_.GroundTheory.Heights₂.Heights.StandardModelDualRank.exists_int_comb b c a
    have hNΩ : (N : dualStdModelField K i) ≠ 0 := by
      rw [← map_intCast (embK K i)]
      exact (map_ne_zero_iff _ (embK K i).injective).mpr (Int.cast_ne_zero.mpr hN)
    have he : embK K i a =
        algebraMap Φ₀ _ ((N : Φ₀)⁻¹) * ∑ t, (n t : dualStdModelField K i) * (w b t * (w b c)⁻¹) := by
      rw [map_inv₀, map_intCast]
      simp only [← mul_assoc, ← Finset.sum_mul, hn]
      field_simp [w_ne_zero b c]
    rw [he]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.sum_mem _ fun t _ =>
      Subalgebra.mul_mem _ (intCast_mem _ _) (Algebra.subset_adjoin ⟨t, rfl⟩))
  have hMeq : Subalgebra.toSubmodule (Algebra.adjoin Φ₀ (Set.range fun t => w b t * (w b c)⁻¹)) =
      Submodule.span Φ₀ (Set.range fun k => embK K i (B k)) := by
    apply le_antisymm
    · rw [← hM']
      exact fun x hx => hMM' hx
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hβM (B k)
  rw [← Subalgebra.finrank_toSubmodule, hMeq, finrank_span_eq_card (linIndep B Φ₀ hΦ), Fintype.card_fin]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace DualStackedDegreeAlt

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

theorem isLattice (F : HermLattice K i) : Submodule.IsFullLattice ℚ (F.lattice.restrictScalars ℤ) :=
  LinesIsLattice.proof K (Fin i) F.lattice (F.fg.restrictScalars) F.span_eq

theorem degree_withStdMetric (F : HermLattice K i) :
    F.withStdMetric.degree = Real.log (genIndex F.lattice.toAddSubgroup
      (HermLattice.standard K i).lattice.toAddSubgroup) := by
  have hspan : Submodule.span K (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → K)) = ⊤ := by
    have h : (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → K)) =
        Set.range (Pi.basisFun K (Fin i)) := by
      congr 1; funext j; exact (Pi.basisFun_apply _ _ _).symm
    rw [h]; exact (Pi.basisFun K (Fin i)).span_eq
  have hlat : F.withStdMetric.lattice = F.lattice := rfl
  have hstd : F.withStdMetric.metric = fun _ => 1 := rfl
  simp only [HermLattice.degree, subDegree, hlat, hstd, hspan, Submodule.restrictScalars_top, inf_top_eq,
    TopDualLatticeChange.gramAt_one_single, Matrix.det_one, Complex.one_re, Real.log_one,
    Finset.sum_const_zero, mul_zero, sub_zero]
  rfl

theorem degree_sub (F F' : HermLattice K i) (h : F'.lattice ≤ F.lattice) :
    F.withStdMetric.degree - F'.withStdMetric.degree =
      Real.log (F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup) := by
  have hT := LinesGenIndexTrans.proof LinesLatticeBasis.proof
    (LinesGenIndexDet.proof LinesLatticeBasis.proof)
  obtain ⟨hpos1, hmul⟩ := hT (Fin i → K) (F.lattice.restrictScalars ℤ) (F'.lattice.restrictScalars ℤ)
    ((HermLattice.standard K i).lattice.restrictScalars ℤ) (isLattice F) (isLattice F') (isLattice _)
  obtain ⟨hpos2, -⟩ := hT (Fin i → K) (F'.lattice.restrictScalars ℤ)
    ((HermLattice.standard K i).lattice.restrictScalars ℤ)
    ((HermLattice.standard K i).lattice.restrictScalars ℤ) (isLattice F') (isLattice _) (isLattice _)
  have e : ∀ L : Submodule (𝓞 K) (Fin i → K), (L.restrictScalars ℤ).toAddSubgroup = L.toAddSubgroup :=
    fun _ => rfl
  simp only [e] at hpos1 hmul hpos2
  rw [degree_withStdMetric, degree_withStdMetric, ← hmul, Real.log_mul hpos1.ne' hpos2.ne',
    add_sub_cancel_right, genIndex, (AddSubgroup.relIndex_eq_one (H := F.lattice.toAddSubgroup)
      (K := F'.lattice.toAddSubgroup)).mpr (fun _ hx => h hx), Nat.cast_one, div_one]

theorem relIndex_stacked {T : Type} [Fintype T] [DecidableEq T] {F F' : HermLattice K i}
    (h : F'.lattice ≤ F.lattice) (b : Module.Basis T ℤ (dualLattice F))
    (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ)
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) :
    ((dualLattice F).toAddSubgroup.relIndex (dualLattice F').toAddSubgroup : ℝ) = ∏ t, |(a t : ℝ)| := by
  rw [AddSubgroup.relIndex_eq_natAbs_det _ _ (DualTopStackedExistence.dualLattice_mono h) b b']
  have hv : (fun t => (⟨(b t : Fin i → K), DualTopStackedExistence.dualLattice_mono h (b t).2⟩ :
      dualLattice F')) = fun t => a t • b' t := by
    funext t; exact Subtype.ext (hab t)
  have hdet : b'.det (fun t => a t • b' t) = ∏ t, a t := by
    rw [Module.Basis.det_apply]
    have hm : b'.toMatrix (fun t => a t • b' t) = Matrix.diagonal a := by
      ext s t
      by_cases hst : s = t
      · subst hst; simp [Module.Basis.toMatrix_apply]
      · simp [Module.Basis.toMatrix_apply, hst]
    rw [hm, Matrix.det_diagonal]
  erw [hv, hdet]
  push_cast [Nat.cast_natAbs, Int.cast_abs, Int.cast_prod, Finset.abs_prod]
  rfl

end DualStackedDegreeAlt


open DualStackedDegreeAlt in
theorem DualStackedDegree.proof (hIdx : DualLatticeIndex.Statement) : DualStackedDegree.Statement := by
  intro K _ _ i F F' T _ _ b b' a h hab
  have ha : ∀ t, a t ≠ 0 := fun t ht => b.ne_zero t (Subtype.ext (by rw [hab t, ht, zero_smul]; rfl))
  rw [degree_sub F F' h, ← hIdx K i F F' h, relIndex_stacked h b b' a hab,
    Real.log_prod (fun t _ => abs_ne_zero.mpr (Int.cast_ne_zero.mpr (ha t)))]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def linPointMap {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k) :
    MRing (stackedBlocks T) →+* MvPolynomial (Option (Fin n)) k :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl _, t⟩ => C (α t) * X none
    | ⟨.inr _, t⟩ => ∑ j, C (M t j) * X (some j)

def linPrime {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k) :
    Ideal (MRing (stackedBlocks T)) :=
  RingHom.ker (linPointMap α M)

def LinFormsIndep {T : Type} {k : Type} [Field k] {n : ℕ} (M : T → Fin n → k) : Prop :=
  ∀ w : Fin n → k, (∀ t, ∑ j, M t j * w j = 0) → w = 0

def DualStackedExcLinear.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E →
      ∃ (k : Type) (_ : Field k) (_ : Fintype k) (α : T → k) (M : T → Fin i → k),
        Submodule.span ℤ (Set.range α) = ⊤ ∧ LinFormsIndep M ∧ E = linPrime α M ∧
          Fintype.card k = F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup

def LinPrimeCut.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (k : Type) [Field k] (n : ℕ) (α : T → k) (M : T → Fin (n + 2) → k),
    Submodule.span ℤ (Set.range α) = ⊤ → LinFormsIndep M →
    ∀ c : T, graphSecond c ∉ linPrime α M →
      ∃ M' : T → Fin (n + 1) → k, LinFormsIndep M' ∧
        divSupp (linPrime α M) (graphSecond c) = {linPrime α M'} ∧
        multAt (linPrime α M ⊔ Ideal.span {graphSecond c}) (linPrime α M') = 1

def LinPrimeBase.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (k : Type) [Field k] (α : T → k) (M : T → Fin 1 → k),
    Submodule.span ℤ (Set.range α) = ⊤ → LinFormsIndep M →
    ∀ c : (κ : Unit ⊕ Unit) → stackedBlocks T κ,
      (∀ κ, (X ⟨κ, c κ⟩ : MRing (stackedBlocks T)) ∉ linPrime α M) →
      Nonempty ((MRing (stackedBlocks T) ⧸ (linPrime α M ⊔
        Ideal.span (Set.range fun κ => (X ⟨κ, c κ⟩ : MRing (stackedBlocks T)) - 1))) ≃+* k)

namespace LinPrimeExample

theorem linPointMap_first {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k)
    (t : T) : linPointMap α M (graphFirst t) = C (α t) * X none := by
  simp [linPointMap, graphFirst]

theorem linPointMap_second {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k)
    (t : T) : linPointMap α M (graphSecond t) = ∑ j, C (M t j) * X (some j) := by
  simp [linPointMap, graphSecond]

end LinPrimeExample

end

end GroundTheory.Heights₂.Heights
end
