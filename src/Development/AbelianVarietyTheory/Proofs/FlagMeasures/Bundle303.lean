module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle003
public import Formalism.PeriodIntegrals.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle295
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle021
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueHaarDensityAtIdentity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle026
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle039
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle047
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle257
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle237
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle159
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle299
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.HaarDensChart

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU

variable {k r : ℕ}

instance : LocallyCompactSpace (Gp k r) :=
  (amb_closed (k := k) (r := r)).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem isMatGroup_uwb : PI.IsMatGroup (UWb k r) :=
  ⟨amb_closed, uwb_one, fun _ ha _ hb => uwb_mul ha hb, fun a ha => ⟨uwb_inv ha, Matrix.mul_nonsing_inv _ (uwb_unit ha)⟩⟩

theorem exists_haarOn (k r : ℕ) : ∃ νh : Measure (Mt k r), IsHaarOn (UWb k r) νh := by
  let μ : Measure (Gp k r) := Measure.haar
  refine ⟨μ.map inc, inc_memb.sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩
  · intro h
    have := congrArg (fun m : Measure (Mt k r) => m Set.univ) h
    simp only [inc_memb.map_apply, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this
    exact (IsOpen.measure_pos μ isOpen_univ Set.univ_nonempty).ne' this
  · rw [inc_memb.map_apply]
    have : (inc : Gp k r → Mt k r) ⁻¹' {x | Matrix.of x ∉ UWb k r} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact inc_mem x
    rw [this, measure_empty]
  · let a : Gp k r := ⟨s, hs⟩
    rw [Measure.map_map (lmulM_cont s).measurable inc_memb.measurable]
    have : lmulM s ∘ (inc : Gp k r → Mt k r) = inc ∘ fun x => a * x := by
      funext x; rfl
    rw [this, ← Measure.map_map inc_memb.measurable (measurable_const_mul a), map_mul_left_eq_self]

end GlobalTheory.HaarDensChart

namespace GlobalTheory.HaarDensChart

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.HU GlobalTheory.MatHaarDensity

theorem haarDens : HaarDens := by
  intro k r hk
  obtain ⟨νh, hνh⟩ := exists_haarOn k r
  have hS : PI.IsMatGroup (UWb k r) := isMatGroup_uwb
  have hμ : PI.IsHaarOnM (UWb k r) νh := hνh
  obtain ⟨hlie, hsurj⟩ := GlobalTheory.T.closed_matrix_subgroup_theorem _ (UWb k r) hS
  obtain ⟨-, hcpt, hop⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ (UWb k r) νh hS hμ
  have hmem : ∀ X, expL (UWb k r) X ∈ UWb k r := fun X => by simpa [expL] using hlie X 1
  have hsurj' : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ UWb k r, (∀ i j, ‖(g - 1) i j‖ < δ) →
      ∃ X : lieE (UWb k r), ‖X‖ < ρ ∧ expL (UWb k r) X = g := by
    intro ρ hρ
    obtain ⟨δ, hδ, h⟩ := hsurj ρ hρ
    refine ⟨δ, hδ, fun g hg hg' => ?_⟩
    obtain ⟨X, hX, e⟩ := h g hg hg'
    exact ⟨X, mem_ball_zero_iff.1 hX, e⟩
  obtain ⟨δ₀, hδ₀, hi⟩ := exists_injOn (UWb k r)
  let φ : lieE (UWb k r) → Mt k r := expC k r
  have hc : Continuous φ := continuous_expL (UWb k r)
  have hi' : Set.InjOn φ (Metric.ball 0 δ₀) := fun X hX Y hY h => hi hX hY h
  have hψ : MeasurableEmbedding ((Metric.ball (0 : lieE (UWb k r)) δ₀).restrict φ) :=
    hc.continuousOn.measurableEmbedding Metric.isOpen_ball.measurableSet hi'
  let ν : Measure (lieE (UWb k r)) := (νh.comap ((Metric.ball (0 : lieE (UWb k r)) δ₀).restrict φ)).map Subtype.val
  have hν : ∀ A : Set (lieE (UWb k r)), MeasurableSet A → ν A = νh (φ '' (A ∩ Metric.ball 0 δ₀)) := by
    intro A hA
    simp only [ν]
    rw [Measure.map_apply measurable_subtype_coe hA, hψ.comap_apply]
    congr 1
    rw [Set.inter_comm, ← Subtype.image_preimage_coe, Set.image_image]
    rfl
  have hνb : ∀ (x : lieE (UWb k r)) (ρ : ℝ), ‖x‖ + ρ ≤ δ₀ → ν (Metric.ball x ρ) = νh (φ '' Metric.ball x ρ) := by
    intro x ρ h
    rw [hν _ Metric.isOpen_ball.measurableSet, Set.inter_eq_left.2]
    exact Metric.ball_subset_ball' (by simpa [add_comm] using h)
  have hfin : νh (φ '' Metric.ball 0 δ₀) < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.image_mono Metric.ball_subset_closedBall))
      (hcpt _ ((isCompact_closedBall (0 : lieE (UWb k r)) δ₀).image hc) (by
        rintro _ ⟨X, -, rfl⟩
        exact hmem X))
  haveI : IsFiniteMeasure ν := ⟨by
    rw [hν _ MeasurableSet.univ, Set.univ_inter]
    exact hfin⟩
  have hposh : ∀ ρ : ℝ, 0 < ρ → νh (φ '' Metric.ball 0 ρ) ≠ 0 := by
    intro ρ hr h
    obtain ⟨η, hη, H⟩ := hsurj ρ hr
    have hp := hop {g | ∀ i j, ‖(Matrix.of g - 1) i j‖ < η} (isOpen_near_one η)
      ⟨Matrix.of.symm 1, by intro i j; simpa using hη, hS.2.1⟩
    refine hp.ne' (measure_mono_null (fun g hg => ?_) (measure_union_null h hνh.2.2.1))
    by_cases hgS : Matrix.of g ∈ UWb k r
    · exact Or.inl (H _ hgS hg)
    · exact Or.inr hgS
  have hpos : ∀ ρ : ℝ, 0 < ρ → ν (Metric.ball 0 ρ) ≠ 0 := by
    intro ρ hr
    rw [hν _ Metric.isOpen_ball.measurableSet]
    intro h
    refine hposh (min ρ δ₀) (lt_min hr hδ₀) (measure_mono_null (Set.image_mono ?_) h)
    exact Set.subset_inter (Metric.ball_subset_ball (min_le_left _ _)) (Metric.ball_subset_ball (min_le_right _ _))
  have hsν : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : lieE (UWb k r), ‖x‖ < η →
      ∀ᶠ ρ in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * ρ)) ≤ ν (Metric.ball 0 ρ) ∧
        ν (Metric.ball 0 ρ) ≤ ν (Metric.ball x ((1 + ε) * ρ)) := by
    intro ε h0 h1
    obtain ⟨η, hη, H⟩ := sandwich (UWb k r) hS hmem hsurj' ε h0 h1
    refine ⟨min η (δ₀ / 2), lt_min hη (by linarith), fun x hx => ?_⟩
    have hx1 : ‖x‖ < η := hx.trans_le (min_le_left _ _)
    have hx2 : ‖x‖ < δ₀ / 2 := hx.trans_le (min_le_right _ _)
    obtain ⟨hiS, hi1⟩ := hS.2.2.2 _ (hmem x)
    have hi2 : (expL (UWb k r) x)⁻¹ * expL (UWb k r) x = 1 := mul_eq_one_comm.1 hi1
    have hτ : Continuous (lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) := lmulM_cont _
    have hτμ : νh.map (lmulM (expL (UWb k r) x)⁻¹) = νh := hνh.2.2.2 _ hiS
    filter_upwards [H x hx1, Ioo_mem_nhdsGT (show (0:ℝ) < δ₀ / 4 by linarith)] with ρ hr hr'
    obtain ⟨hr0, hr1⟩ := hr'
    have hm : MeasurableSet (φ '' Metric.ball 0 ρ) :=
      Metric.isOpen_ball.measurableSet.image_of_continuousOn_injOn hc.continuousOn
        (hi'.mono (Metric.ball_subset_ball (by linarith)))
    have hinv : νh (φ '' Metric.ball 0 ρ) =
        νh ((lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) ⁻¹' (φ '' Metric.ball 0 ρ)) := by
      rw [← Measure.map_apply hτ.measurable hm, hτμ]
    have hA : φ '' Metric.ball x ((1 - ε) * ρ) ⊆
        (lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) ⁻¹' (φ '' Metric.ball 0 ρ) := by
      rintro _ ⟨Y, hY, rfl⟩
      obtain ⟨Z, hZ, e⟩ := hr.1 Y (mem_ball_iff_norm.1 hY)
      refine ⟨Z, mem_ball_zero_iff.2 hZ, ?_⟩
      change expL (UWb k r) Z = (expL (UWb k r) x)⁻¹ * expL (UWb k r) Y
      rw [e, ← Matrix.mul_assoc, hi2, Matrix.one_mul]
    have hB : (lmulM (expL (UWb k r) x)⁻¹ : Mt k r → Mt k r) ⁻¹' (φ '' Metric.ball 0 ρ) ⊆
        φ '' Metric.ball x ((1 + ε) * ρ) := by
      rintro g ⟨Z, hZ, e⟩
      obtain ⟨Y, hY, e'⟩ := hr.2 Z (mem_ball_zero_iff.1 hZ)
      refine ⟨Y, mem_ball_iff_norm.2 hY, ?_⟩
      change expL (UWb k r) Z = (expL (UWb k r) x)⁻¹ * Matrix.of g at e
      change expL (UWb k r) Y = Matrix.of g
      rw [e', e, ← Matrix.mul_assoc, hi1, Matrix.one_mul]
    rw [hνb x _ (by nlinarith), hνb x _ (by nlinarith), hνb 0 ρ (by simp; linarith), hinv]
    exact ⟨measure_mono hA, measure_mono hB⟩
  obtain ⟨c, hc0, hct, hlim⟩ :=
    GlobalTheory.exists_density_origin_of_almost_homogeneous (lieE (UWb k r)) volume ν hpos hsν
  have hb : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : lieE (UWb k r), ‖x‖ < η →
      ENNReal.ofReal ((1 + ε)⁻¹ ^ Module.finrank ℝ (lieE (UWb k r))) * c ≤ upperDens volume ν x ∧
        upperDens volume ν x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ Module.finrank ℝ (lieE (UWb k r))) * c := by
    intro ε h0 h1
    obtain ⟨η, hη, H⟩ := hsν ε h0 h1
    exact ⟨η, hη, GlobalTheory.T.upperDensity_bounds_almost_homogeneous_measure _ volume ν c hct hlim ε η h0 h1 H⟩
  obtain ⟨hδ0, hδc⟩ := GlobalTheory.T.continuousAt_zero_of_squeeze_pow_bounds _ _ (upperDens volume ν) c hct hb
  obtain ⟨η₀, hη₀, H₀⟩ := hb (1 / 2) (by norm_num) (by norm_num)
  set a := ENNReal.ofReal (((1 + 1 / 2) / (1 - 1 / 2)) ^ Module.finrank ℝ (lieE (UWb k r)) : ℝ) * c with ha
  have hne : a ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct
  have hC : ∀ x : lieE (UWb k r), ‖x‖ < η₀ → upperDens volume ν x < ((a.toNNReal + 1 : ℝ≥0) : ℝ≥0∞) := by
    intro x hx
    refine lt_of_le_of_lt (H₀ x hx).2 ?_
    have h := ENNReal.coe_lt_coe.2 (lt_add_one a.toNNReal)
    rwa [ENNReal.coe_toNNReal hne] at h
  refine ⟨νh, hνh, upperDens volume ν, hδc, by rw [hδ0]; exact hc0, by rw [hδ0]; exact hct,
    min η₀ δ₀, lt_min hη₀ hδ₀, fun ρ hρ hρε => ?_⟩
  have e1 : νh (bBall k r ρ) = ν (Metric.ball 0 ρ) := by
    rw [hν _ Metric.isOpen_ball.measurableSet,
      Set.inter_eq_left.2 (Metric.ball_subset_ball (hρε.le.trans (min_le_right _ _)))]
    rfl
  rw [e1]
  exact GlobalTheory.T.measure_ball_eq_lintegral_upperMeasureDensity _ volume ν η₀ _ hC ρ (hρε.le.trans (min_le_left _ _))

end GlobalTheory.HaarDensChart
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AdelicModels

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (HA HR HFinIn AF Ainf IsCMExt IsHermND)
open Formalism.MainNotions.StandardLattice (finMat infMat IsInfEmb)
open GlobalTheory.Mem.Vol.Scale
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_real_equiv (I : AutInst) (hcm : IsCMExt I.F I.E I.cm.sig)
    (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ)) (hθ : ∀ v, IsInfEmb (I.φ v) (θ v)) :
    ∃ e : HA (Ainf I.F) I.cm.sig I.J ≃ₜ* I.Ginf, ∀ h v, uMat (e h v) =
      (I.P v)⁻¹ * ((HA.mat (Ainf I.F) I.cm.sig I.J h : GL (Fin I.n) (Ainf I.F ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Ainf I.F ⊗[I.F] I.E)).map (θ v) * I.P v := by
  obtain ⟨e, he, hc, hc', hs⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv I.F I.E I.cm.sig _ I.φ θ hcm
    (GlobalTheory.GaussDecay.isCMFam_of_over _ hcm I.φ I.φ_over) hθ
  choose p q s hsort using fun v => exists_sorts (I.ε v)
  have hd : ∀ v, IsUnit (I.P v).det := fun v => (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have h1 : ∀ v, (I.P v)⁻¹ * I.P v = 1 := fun v => Matrix.nonsing_inv_mul _ (hd v)
  have h2 : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v => Matrix.mul_nonsing_inv _ (hd v)
  have hJ : ∀ v, Formalism.UG.Jpq (p v) (q v) = (Formalism.REAL.Jm (I.ε v)).submatrix (s v) (s v) := fun v => by
    rw [← (hsort v).reindex_Jpq]
    ext a b
    simp
  obtain ⟨f, hf⟩ := GlobalTheory.Mem.InfGroup.exists_equiv he hc hc' (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Ainf I.F) I.cm.sig)
    (fun x i => by rw [← he, ← he, hs]) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Ainf I.F) I.J) p q
    (fun v => (I.P v)⁻¹.submatrix (s v) (Equiv.refl _)) (fun v => (I.P v).submatrix (Equiv.refl _) (s v))
    (fun v => by rw [Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_one_equiv])
    (fun v => by rw [Matrix.submatrix_mul_equiv, h2, Matrix.submatrix_one_equiv])
    (fun v => by
      have h3 : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Ainf I.F) I.J).map (θ v) = I.J.map (I.φ v) := by
        ext a b
        exact (hθ v).1 (I.J a b)
      rw [h3, hJ, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
        ← I.P_spec v]
      change (I.P v)⁻¹ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) * (I.P v)⁻¹ = _
      calc _ = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [h2]; simp)
  let g : (∀ v, Formalism.BasicNotions.UpqT (p v) (q v)) ≃ₜ* I.Ginf :=
    { toFun := fun x v => (hsort v).equiv (x v)
      invFun := fun y v => (hsort v).equiv.symm (y v)
      left_inv := fun x => funext fun v => (hsort v).equiv.symm_apply_apply _
      right_inv := fun x => funext fun v => (hsort v).equiv.apply_symm_apply _
      map_mul' := fun x y => funext fun v => map_mul (hsort v).equiv _ _
      continuous_toFun := continuous_pi fun v => (hsort v).equiv.continuous.comp (continuous_apply v)
      continuous_invFun := continuous_pi fun v => (hsort v).equiv.symm.continuous.comp (continuous_apply v) }
  refine ⟨f.trans g, fun h v => ?_⟩
  have h4 := hf h v
  change Matrix.reindex (s v) (s v) (Formalism.BasicNotions.UpqT.mat (f h v)) = (I.P v)⁻¹ * (h.1.1).map (θ v) * I.P v
  generalize Formalism.BasicNotions.UpqT.mat (f h v) = X at h4 ⊢
  generalize (h.1.1).map (θ v) = Y at h4 ⊢
  have h5 : Matrix.reindex (s v) (s v) X * (I.P v)⁻¹ = (I.P v)⁻¹ * Y := by
    ext a b
    have := congrFun (congrFun h4 ((s v).symm a)) b
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.coe_refl, id] at this
    rw [Matrix.mul_apply, Matrix.mul_apply, ← this, ← (s v).sum_comp]
    simp
  rw [← h5, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem bc_mem {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {γ : GL (Fin M) E}
    (hγ : γ ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R) γ ∈ HR R σ J := by
  have h : Formalism.UG.cT (σ : E →+* E) γ.1 * J * γ.1 = J := hγ
  have h2 := congrArg (fun X => Matrix.map X (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) h
  simp only [Matrix.map_mul] at h2
  change Formalism.UG.cT _ (γ.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) R)) * J.map _ * γ.1.map _ = J.map _
  rw [← h2]
  congr 2

theorem exists_adelic_equiv : ∀ I : AutInst, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt I.F I.E I.cm.sig ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND I.cm.sig I.J ∧ ∃ T : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J ≃ₜ* I.GA, (∀ h, (show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J from h) ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFinIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J ↔ T h ∈ I.GFset) ∧ (∀ h, I.fmat (T h).2 = (Formalism.MainNotions.StandardLattice.finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _)) ∧ ∀ v θ, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) θ → ∀ h, uMat ((T h).1 v) = (I.P v)⁻¹ * Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J θ h * I.P v := by
  intro I
  have hcm : IsCMExt I.F I.E I.cm.sig := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND I.F I.E I.cm).1
  refine ⟨hcm, ⟨fun i j => congrFun (congrFun I.J_herm i) j, I.J_det⟩, ?_⟩
  have hex := GlobalTheory.Mem.VolEmb.existsUnique_infEmb I.F I.E I.cm.sig hcm
  choose θ hθ hθu using fun v => hex (I.φ v)
  obtain ⟨er, her⟩ := exists_real_equiv I hcm θ hθ
  obtain ⟨ef, hef, -⟩ := GlobalTheory.T.exists_continuousMulEquiv_congruenceTopology_adelicUnitary I
  obtain ⟨sp, hsp⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split I.F I.E I.cm.sig I.n I.J
  let g : HA (Ainf I.F) I.cm.sig I.J × HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af I.F) I.cm.sig I.J ≃ₜ* I.GA :=
    { toFun := fun x => (er x.1, ef.symm x.2)
      invFun := fun y => (er.symm y.1, ef y.2)
      left_inv := fun x => Prod.ext (er.symm_apply_apply _) (ef.apply_symm_apply _)
      right_inv := fun x => Prod.ext (er.apply_symm_apply _) (ef.symm_apply_apply _)
      map_mul' := fun x y => Prod.ext (map_mul er _ _) (map_mul ef.symm _ _)
      continuous_toFun := (er.continuous.comp continuous_fst).prodMk (ef.symm.continuous.comp continuous_snd)
      continuous_invFun := (er.symm.continuous.comp continuous_fst).prodMk (ef.continuous.comp continuous_snd) }
  have hfin : ∀ h, I.fmat ((sp.trans g) h).2 =
      (finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _) := by
    intro h
    have h1 := hef (ef.symm (sp h).2)
    rw [ef.apply_symm_apply, (hsp h).1] at h1
    rw [h1]
    change I.fmat (ef.symm (sp h).2) = _
    ext a b
    exact ((Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm_apply_apply _).symm
  have hinf : ∀ v h, uMat (((sp.trans g) h).1 v) = (I.P v)⁻¹ * infMat I.cm.sig I.J (θ v) h * I.P v := by
    intro v h
    have h1 := her (sp h).1 v
    rw [(hsp h).2] at h1
    exact h1
  have hrat : ∀ (γ : GL (Fin I.n) I.E) (h : HA (AF I.F) I.cm.sig I.J),
      Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := I.F) (AF I.F)) γ = HA.mat _ _ _ h →
      (∀ v, uMat (((sp.trans g) h).1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat ((sp.trans g) h).2 =
        (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    intro γ h hh
    refine ⟨fun v => ?_, ?_⟩
    · rw [hinf]
      congr 2
      unfold infMat
      rw [← hh]
      ext a b
      rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply, ← (hθ v).1]
      change θ v (Algebra.TensorProduct.map _ _ ((1 : AF I.F) ⊗ₜ[I.F] γ.1 a b)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
    · rw [hfin]
      unfold finMat
      rw [← hh]
      ext a b
      rw [Matrix.map_apply, Matrix.map_apply, Matrix.map_apply]
      change Algebra.TensorProduct.comm I.F _ _
        (Algebra.TensorProduct.map _ _ ((1 : AF I.F) ⊗ₜ[I.F] γ.1 a b)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
  refine ⟨sp.trans g, fun h => ⟨?_, ?_⟩, hfin, fun v θ' hθ' h => ?_⟩
  · rintro ⟨γ, hγ, hh⟩
    exact ⟨γ, hγ, hrat γ h hh⟩
  · rintro ⟨γ, hγ, h1, h2⟩
    let h' : HA (AF I.F) I.cm.sig I.J :=
      (⟨_, bc_mem (AF I.F) I.cm.sig I.J hγ⟩ : HR (AF I.F) I.cm.sig I.J)
    obtain ⟨h3, h4⟩ := hrat γ h' rfl
    have : h = h' := (sp.trans g).injective (Prod.ext
      (funext fun v => Subtype.ext (Units.ext ((h1 v).trans (h3 v).symm)))
      (Subtype.ext (Units.ext (h2.trans h4.symm))))
    rw [this]
    exact ⟨γ, hγ, rfl⟩
  · rw [hθu v θ' hθ']
    exact hinf v h

end GlobalTheory.AdelicModels
end
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

theorem _root_.GlobalTheory.T.lowestKType_isKType_of_large_gaps : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ → (∀ a b : Fin n, ε a ≠ ε b → 2 * (n : ℝ) < |lam a - lam b|) → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) := by
  first | exact @GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub | exact GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub | (intros; apply GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub <;> assumption)
end
