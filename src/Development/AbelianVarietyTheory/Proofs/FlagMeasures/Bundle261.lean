module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle219
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle247
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle230
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle238
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle136
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle205
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeReferenceLatticeStabiliserBounds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordinateLatticeUniqueTermAlmostAllPlaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle246
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle037
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle046
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle091
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRepFormalDegreeBound
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle252
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibreNormal

theorem vol_discs (ι : Type) [Fintype ι] {M : ℝ} (hM : 0 ≤ M) :
    volume {x : ι → ℂ | ∀ p, ‖x p‖ ≤ M} = ENNReal.ofReal ((Real.pi * M ^ 2) ^ Fintype.card ι) := by
  have h : {x : ι → ℂ | ∀ p, ‖x p‖ ≤ M} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) M := by
    ext x; simp
  rw [h, volume_pi_pi, Finset.prod_const, Finset.card_univ, Complex.volume_closedBall,
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hM, mul_comm]
  congr 2
  exact (ENNReal.ofReal_coe_nnreal (p := NNReal.pi)).symm

theorem vol_ints (ι : Type) [Fintype ι] {M : ℝ} (hM : 0 ≤ M) :
    volume {x : ι → ℝ | ∀ p, |x p| ≤ M} = ENNReal.ofReal ((2 * M) ^ Fintype.card ι) := by
  have h : {x : ι → ℝ | ∀ p, |x p| ≤ M} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℝ) M := by
    ext x; simp
  rw [h, volume_pi_pi, Finset.prod_const, Finset.card_univ, Real.volume_closedBall,
    ENNReal.ofReal_pow (by positivity)]

def lowEquiv {r j : ℕ} (hj : j ≤ r) : Fin j ≃ {a : Fin r // a.val < j} where
  toFun b := ⟨Fin.castLE hj b, b.2⟩
  invFun a := ⟨a.1.val, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem vol_reindex {k r j : ℕ} (hj : j ≤ r) (T : Set (Fin j → Fin (k + 1) → ℂ)) :
    volume {B : {a : Fin r // a.val < j} → Fin (k + 1) → ℂ | (fun b : Fin j => B ⟨Fin.castLE hj b, b.2⟩) ∈ T} =
      volume T := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : {a : Fin r // a.val < j} => Fin (k + 1) → ℂ)
    (lowEquiv hj)).symm
  rw [← h.measure_preimage_equiv T]
  rfl

theorem card_UT (r : ℕ) : 2 * Fintype.card (UT r) ≤ r * (r - 1) := by
  have h : Fintype.card (UT r) = r.choose 2 := by
    rw [Fintype.card_subtype, ← Finset.univ_product_univ, Finset.card_product_filter_lt]
    simp
  rw [h, Nat.choose_two_right]
  exact Nat.mul_div_le _ _

theorem vol_box {k r j : ℕ} (β : Fin r → ℕ) (A : Set ({a : Fin r // a.val < j} → Fin (k + 1) → ℂ))
    (B : Set ({p : UT r // p.1.1.val < j} → ℂ)) (C : Set ({a : Fin r // a.val < j} → ℝ)) (D : Set (UToff β → ℂ)) :
    (volume : Measure (PSec k r j × (UToff β → ℂ))) ((A ×ˢ B ×ˢ C) ×ˢ D) =
      volume A * (volume B * volume C) * volume D := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Measure.volume_eq_prod, Measure.prod_prod]

theorem sEl_mem {k r j : ℕ} (β : Fin r → ℕ) (q : PSec k r j × (UToff β → ℂ)) : sEl k r j β q ∈ Nset k r :=
  isClosedSub_Nset.2.2.2.1 _ ((((Rad.radical k r).1 _ _).2.2.2 (Rad.skewM_skew _ _)).1) _ (UEmb.upper_mem _)

theorem ae_mem_range {k r j : ℕ} (β : Fin r → ℕ) {S : Set (Mat k r)} (hS : IsClosed S)
    (h : Set.range (rEl k r j β) ⊆ S) : ∀ᵐ ρ ∂(lebR0 k r j β), Matrix.of ρ ∈ S := by
  unfold lebR0
  have hS' : IsClosed {x : Mt k r | Matrix.of x ∈ S} := hS
  have hu : Measurable fun x : UTin β → ℂ =>
      (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r) := by
    have hU : Continuous (upperIn β) := by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [upperIn, upper]
      split_ifs <;> first | exact continuous_apply _ | exact continuous_const
    have heq : ∀ x, (upperIn β x)⁻¹ = (upperIn β x).adjugate := fun x => by
      rw [Matrix.inv_def, upperIn, UEmb.det_upper]; simp
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => Continuous.measurable ?_
    simp only [Matrix.of_symm_apply, uEmb, heq]
    split_ifs
    · exact hU.matrix_elem _ _
    · exact (hU.matrix_adjugate.matrix_elem _ _).star
    · exact continuous_const
    · exact continuous_const
  have hp : Measurable fun q : PTop k r j => (Matrix.of.symm (pTop k r j q) : Mt k r) := by
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => Continuous.measurable ?_
    simp only [Matrix.of_symm_apply, pTop, pOf, pEl, skewM, herm, bvec, dotProduct, Matrix.mulVec]
    split_ifs <;> fun_prop
  have hm : AEMeasurable (fun q => (Matrix.of.symm (rEl k r j β q) : Mt k r))
      (volume : Measure ((UTin β → ℂ) × PTop k r j)) := by
    unfold rEl
    apply Measurable.aemeasurable
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
    simp only [Matrix.of_symm_apply, Matrix.mul_apply]
    exact Finset.measurable_sum _ fun i _ =>
      (((measurable_pi_iff.1 (measurable_pi_iff.1 hu a)) i).comp measurable_fst).mul
        (((measurable_pi_iff.1 (measurable_pi_iff.1 hp i)) b).comp measurable_snd)
  rw [ae_map_iff hm hS'.measurableSet]
  exact Filter.Eventually.of_forall fun q => h ⟨q, rfl⟩

theorem N_sub_S {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, (isClosedSub_UWset z).2.2.1, n, hn, (Matrix.one_mul n).symm⟩

theorem Sg2_N {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {n x : Mat k r}
    (hn : n ∈ Nset k r) (hx : x ∈ GG k r) : Sg2 k r z (n * x) = Sg2 k r z x := by
  have := (TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z hz hT).2.1 x hx n (N_sub_S z hn) 1
    ⟨isClosedSub_GG.2.2.1, (Matrix.unitaryGroup _ ℂ).one_mem⟩
  rwa [Matrix.mul_one] at this

theorem fibre_volume : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → 1 ≤ j → j + 2 ≤ k → ∀ De : ℝ, DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yj k r hj z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR0 k r j β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset0 k r hj z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol0 k r j R₀ De y) := by
  intro k r j hj z z' g₀ β c hz hz' hT hN h1j hjk De hDe m hm a ha
  have hT' : 0 < Tz k r z' := by rw [(GlobalTheory.Amp.NfMid.normal0_middle k r j hj z z' g₀ β c hz hz' hT hN).1]; exact hT
  obtain ⟨hR, hRc⟩ := GlobalTheory.T.commonStabilizerSet_eq_range_normalForm k r j hj z z' g₀ β c hz hz' hT hN
  obtain ⟨P₀, hP₀, hY⟩ := GlobalTheory.T.flagGram_eq_gramDetProjection_normalForm k r j hj z z' g₀ β c hz hz' hT hN m hm
  obtain ⟨hnull, hvol⟩ := GlobalTheory.Amp.GramVol.vol_gram k j h1j hjk m hm P₀ hP₀
  obtain ⟨hYm, hEm⟩ := GlobalTheory.T.measurable_flagGramNumberNormalized_indicator k r j hj z z' g₀ hz hz' hT hT' hN.1
  have hsplit := GlobalTheory.T.lintegral_flagUnipotent_eq_stabilizer_times_section k r j β hN.2.2.2.1 hN.2.2.2.2.1
  have hB := fun R₀ hR₀ q => GlobalTheory.T.siegel_height_bound_section k r j hj z z' g₀ β c hz hz' hT hN De R₀ hDe hR₀ m hm q a ha
  have hY' := fun q => hY q a ha
  have hmul := (isClosedSub_GG (k := k) (r := r)).2.2.2.1
  have ht : uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m ∈ GG k r := by
    refine hmul _ (UEmb.uEmb_mem _ ?_) _ (Rad.mEmb_mem m hm)
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun b _ => Complex.ofReal_ne_zero.2 (ha b).ne'
  generalize uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m = t at *
  have hae : ∀ᵐ ρ ∂(lebR0 k r j β), Matrix.of ρ ∈ Rset k r g₀ := ae_mem_range β hRc.2.1 hR.ge
  have hst : ∀ q : PSec k r j × (UToff β → ℂ), sEl k r j β q * t ∈ GG k r := fun q => hmul _ (sEl_mem β q).1 _ ht
  have hassoc : ∀ (q : PSec k r j × (UToff β → ℂ)) (ρ : Mt k r),
      (Matrix.of (rmulM t (rmulM (sEl k r j β q) ρ)) : Mat k r) = Matrix.of ρ * (sEl k r j β q * t) :=
    fun q ρ => by rw [of_rmulM, of_rmulM, Matrix.mul_assoc]
  have hYρ : ∀ (q : PSec k r j × (UToff β → ℂ)) (ρ : Mt k r), Matrix.of ρ ∈ Rset k r g₀ →
      Yj k r hj z z' g₀ (Matrix.of ρ * (sEl k r j β q * t)) =
        gramProj P₀ fun b : Fin j => m⁻¹ *ᵥ q.1.1 ⟨Fin.castLE hj b, b.2⟩ := fun q ρ hρ => by
    rw [(GlobalTheory.Amp.YjInv.yj_invariant k r j hj z z' g₀ hz hz' hN.1 _ (hst q)).2.2 _ hρ, hY' q]
  have htm : Measurable (rmulM t : Mt k r → Mt k r) := (continuous_rmulM t).measurable
  constructor
  · set S : Set (Mt k r) := {n | Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r}
      (fun x => Yj k r hj z z' g₀ (Matrix.of x)) (rmulM t n) = 0} with hS
    have hSm : MeasurableSet S := (hYm.comp htm) (measurableSet_singleton 0)
    refine measure_mono_null (t := S) (fun n hn => ?_) ?_
    · exact Set.indicator_apply_eq_zero.2 fun _ => hn
    rw [← lintegral_indicator_one hSm, hsplit _ (measurable_one.indicator hSm)]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    have h0 : (volume : Measure (PSec k r j × (UToff β → ℂ)))
        (({B | (fun b : Fin j => B ⟨Fin.castLE hj b, b.2⟩) ∈
          {B : Fin j → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0}} ×ˢ Set.univ ×ˢ Set.univ) ×ˢ Set.univ) = 0 := by
      rw [vol_box, vol_reindex hj, hnull, zero_mul, zero_mul]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with q hq
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hae] with ρ hρ
    refine Set.indicator_of_notMem (fun hmem => hq ⟨⟨?_, trivial, trivial⟩, trivial⟩) _
    have hG : rmulM t (rmulM (sEl k r j β q) ρ) ∈ {x : Mt k r | Matrix.of x ∈ GG k r} := by
      rw [Set.mem_ofPred_eq, hassoc]; exact hmul _ hρ.1.1 _ (hst q)
    have h2 : Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r}
      (fun x => Yj k r hj z z' g₀ (Matrix.of x)) (rmulM t (rmulM (sEl k r j β q) ρ)) = 0 := hmem
    rw [Set.indicator_of_mem hG, hassoc, hYρ q ρ hρ] at h2
    exact h2
  · intro φ hφ R₀ y hR₀ hy
    have hM : 1 ≤ R₀ ^ (2 * r) * De := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR₀) hDe.1
    have hB' := hB R₀ hR₀
    unfold fibVol0
    generalize R₀ ^ (2 * r) * De = M at *
    have hM0 : 0 ≤ M := zero_le_one.trans hM
    rw [hsplit (fun n => φ n * (Eset0 k r hj z z' g₀ R₀ y).indicator 1 (rmulM t n)) (hφ.1.mul ((measurable_one.indicator (hEm R₀ y)).comp htm))]
    set Box : Set (PSec k r j × (UToff β → ℂ)) :=
      ({B | (fun b : Fin j => B ⟨Fin.castLE hj b, b.2⟩) ∈
          {B : Fin j → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ M) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y}} ×ˢ
        {x | ∀ p, ‖x p‖ ≤ 2 * r * M ^ 2} ×ˢ {x | ∀ p, |x p| ≤ 2 * r * M ^ 2}) ×ˢ {x | ∀ p, ‖x p‖ ≤ M} with hBox
    refine (lintegral_mono (g := Box.indicator 1) fun q => ?_).trans ((lintegral_indicator_one_le Box).trans ?_)
    · by_cases hq : q ∈ Box
      · rw [Set.indicator_of_mem hq]
        refine le_trans (lintegral_mono fun ρ => ?_) (hφ.2 (Matrix.of.symm (sEl k r j β q)) (sEl_mem β q))
        exact mul_le_of_le_one_right' (Set.indicator_le_self' (fun _ _ => zero_le_one) _)
      · rw [Set.indicator_of_notMem hq]
        refine (lintegral_eq_zero_of_ae_eq_zero ?_).le
        filter_upwards [hae] with ρ hρ
        refine mul_eq_zero_of_right _ (Set.indicator_of_notMem (fun hmem => hq ?_) _)
        obtain ⟨-, h1, h2, -, h3⟩ := hmem
        rw [hassoc] at h1 h2 h3
        rw [hYρ q ρ hρ] at h3
        rw [Sg2_N hz' hT' hρ.1 (hst q)] at h1
        have he : g₀ * (Matrix.of ρ * (sEl k r j β q * t)) =
            (g₀ * Matrix.of ρ * g₀⁻¹) * (g₀ * (sEl k r j β q * t)) := by
          rw [Matrix.mul_assoc (g₀ * Matrix.of ρ), Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hN.1),
            Matrix.mul_assoc]
        rw [he, Sg2_N hz hT hρ.2 (hmul _ hN.1 _ (hst q))] at h2
        obtain ⟨b1, b2, b3, b4⟩ := hB' q h1 (((TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z hz hT).2.2.2 _).2.1.trans h2)
        exact ⟨⟨⟨fun b => b2 _, h3⟩, b3, b4⟩, b1⟩
    · have hr : (0 : ℝ) ≤ 2 * r * M ^ 2 := by positivity
      rw [hBox, vol_box, vol_reindex hj, vol_discs _ hr, vol_ints _ hr, vol_discs _ hM0]
      refine (mul_le_mul_left (mul_le_mul_left (hvol M y hM hy) _) _).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have har := box_volume_arith r j (Fintype.card (UToff β)) (Fintype.card {p : UT r // p.1.1.val < j})
        (Fintype.card {a : Fin r // a.val < j}) M h1j hj
        ((Nat.mul_le_mul_left 2 (Fintype.card_subtype_le _)).trans (card_UT r))
        ((Nat.mul_le_mul_left 2 (Fintype.card_subtype_le _)).trans (card_UT r))
        ((Fintype.card_subtype_le _).trans (Fintype.card_fin r).le) hM
      have hK : (0 : ℝ) ≤ (Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) * (2 * y) ^ (2 * (k - 1 - j)) := by
        positivity
      refine le_trans (le_of_eq ?_) ((mul_le_mul_of_nonneg_right har hK).trans (le_of_eq ?_)) <;> ring

end GlobalTheory.Amp.FibreNormal
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.covolume_referenceLattice_stabiliser_bounds : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (β : Fin r → ℕ) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (z z' : ι → Fin (2 * r + k + 1) → ℂ) (g : ι → Mat k r), IsPlaces σ → Module.finrank K V = 2 * r + k + 1 → (∀ v, IsFrameOf N k (σ v) (2 * Formalism.HermitianLatticesTheory.vInv K) β (Φ v) (z v) (z' v) (g v)) → (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ L : Submodule (𝓞 K) V, IsUnimodMod H L (uPerp N.F N.F') (II N.F N.F') → N.F.z ∈ L → ∃ Ω : Set (ι → Mt k r), IsFund (realPts Φ (N.Gam (N.Ref L) : Set (V ≃ₗ[K] V))) (RP k r g) Ω ∧ ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) / (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι)) ≤ Measure.pi (fun _ : ι => lebR0 k r N.j β) Ω ∧ Measure.pi (fun _ : ι => lebR0 k r N.j β) Ω ≤ ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) * (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι)) := by
  first | exact @GlobalTheory.DegVol.RefCov.covol_ref | exact GlobalTheory.DegVol.RefCov.covol_ref | (intros; apply GlobalTheory.DegVol.RefCov.covol_ref <;> assumption)
end

section

noncomputable section
open NumberField MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegVol.UnipConj
variable {k r : ℕ} {ι : Type}

theorem of_conjM (a : Mat k r) (x : Mt k r) : Matrix.of (conjM a x) = a * Matrix.of x * a⁻¹ := rfl

theorem conjM_lmulM {a : Mat k r} (ha : IsUnit a.det) (m x : Mt k r) :
    conjM a (lmulM (Matrix.of m) x) = lmulM (Matrix.of (conjM a m)) (conjM a x) := by
  apply Matrix.of.injective
  have hl : ∀ (b : Mat k r) (y : Mt k r), Matrix.of (lmulM b y) = b * Matrix.of y := fun _ _ => rfl
  rw [of_conjM, hl, hl, of_conjM, of_conjM]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc a⁻¹ a, Matrix.nonsing_inv_mul a ha, Matrix.one_mul]

theorem mulVec_conj_iff (a M : Mat k r) (ha : IsUnit a.det) (w w' : Fin (2 * r + k + 1) → ℂ) :
    M *ᵥ (a *ᵥ w) = a *ᵥ w' ↔ (a⁻¹ * M * a) *ᵥ w = w' := by
  constructor
  · intro h
    have h' := congrArg (fun u => a⁻¹ *ᵥ u) h
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul a ha, Matrix.one_mulVec] at h'
    rw [← h', Matrix.mul_assoc]
  · intro h
    rw [← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv a ha, Matrix.one_mul]

theorem mem_realPts_iff {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (Γ : Set (V ≃ₗ[K] V)) (n : ι → Mat k r)
    (hn : ∀ v, IsUnit (n v).det) (m : ι → Mt k r) :
    m ∈ realPts (fun v y => n v *ᵥ Φ v y) Γ ↔ (fun v => conjM (n v)⁻¹ (m v)) ∈ realPts Φ Γ := by
  have key : ∀ v (w w' : Fin (2 * r + k + 1) → ℂ),
      (Matrix.of (m v) *ᵥ (n v *ᵥ w) = n v *ᵥ w') ↔ Matrix.of (conjM (n v)⁻¹ (m v)) *ᵥ w = w' := by
    intro v w w'
    rw [mulVec_conj_iff _ _ (hn v), of_conjM, Matrix.nonsing_inv_nonsing_inv _ (hn v)]
  simp only [realPts, Set.mem_ofPred_eq, key]

theorem mem_RP_iff (n₁ g n₂ : ι → Mat k r) (h₁ : ∀ v, n₁ v ∈ Nset k r) (h₂ : ∀ v, n₂ v ∈ Nset k r)
    (x : ι → Mt k r) :
    x ∈ RP k r g ↔ (fun v => conjM (n₂ v)⁻¹ (x v)) ∈ RP k r (fun v => n₁ v * g v * n₂ v) := by
  have hu : ∀ v, IsUnit (n₂ v).det := fun v => StabHaar.unit_of_GG (h₂ v).1
  simp only [RP, Set.mem_ofPred_eq]
  refine forall_congr' fun v => ?_
  rw [StabHaar.Rset_conj (g v) (h₁ v) (h₂ v), of_conjM, Matrix.nonsing_inv_nonsing_inv _ (hu v)]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu v), Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ (hu v)]

private theorem conjM_conjM_inv {a : Mat k r} (ha : IsUnit a.det) (y : Mt k r) :
    conjM a (conjM a⁻¹ y) = y := by
  have h := congrFun (StabHaar.conj_conj a a⁻¹) y
  rw [Matrix.mul_nonsing_inv a ha, StabHaar.conj_one] at h
  exact h

private theorem conjM_inv_conjM' {a : Mat k r} (ha : IsUnit a.det) (y : Mt k r) :
    conjM a⁻¹ (conjM a y) = y := by
  have h := congrFun (StabHaar.conj_conj a⁻¹ a) y
  rw [Matrix.nonsing_inv_mul a ha, StabHaar.conj_one] at h
  exact h

theorem isFund_conj_and_measure : ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (k r : ℕ) (ι : Type) [Fintype ι] (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (Γ : Set (V ≃ₗ[K] V)) (n₁ g n₂ : ι → Mat k r) (Ω : Set (ι → Mt k r)) (lam : Measure (Mt k r)), SigmaFinite lam → (∀ v, n₁ v ∈ Nset k r ∧ n₂ v ∈ Nset k r ∧ IsUnit (g v).det) → IsFund (realPts Φ Γ) (RP k r (fun v => n₁ v * g v * n₂ v)) Ω → IsFund (realPts (fun v y => n₂ v *ᵥ Φ v y) Γ) (RP k r g) ((fun (x : ι → Mt k r) v => conjM (n₂ v) (x v)) '' Ω) ∧ Measure.pi (fun v => lam.map (conjM (n₂ v)⁻¹)) Ω = Measure.pi (fun _ : ι => lam) ((fun (x : ι → Mt k r) v => conjM (n₂ v) (x v)) '' Ω) := by
  intro K V _ _ _ k r ι _ Φ Γ n₁ g n₂ Ω lam hlam hN hF
  have := hlam
  have hu : ∀ v, IsUnit (n₂ v).det := fun v => StabHaar.unit_of_GG (hN v).2.1.1
  have hui : ∀ v, IsUnit ((n₂ v)⁻¹).det := fun v => Matrix.isUnit_nonsing_inv_det _ (hu v)
  let e : ∀ _ : ι, Mt k r ≃ᵐ Mt k r := fun v => StabHaar.conjE (n₂ v)⁻¹ (hui v)
  let E : (ι → Mt k r) ≃ᵐ (ι → Mt k r) := MeasurableEquiv.piCongrRight e
  let Cf : (ι → Mt k r) → (ι → Mt k r) := fun x v => conjM (n₂ v) (x v)
  have hEC : ∀ y, E (Cf y) = y := fun y => funext fun v => conjM_inv_conjM' (hu v) (y v)
  have hCE : ∀ y, Cf (E y) = y := fun y => funext fun v => conjM_conjM_inv (hu v) (y v)
  have hC : Cf '' Ω = E ⁻¹' Ω := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show E (Cf x) ∈ Ω
      rw [hEC]
      exact hx
    · intro hy
      exact ⟨E y, hy, hCE y⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show MeasurableSet (Cf '' Ω)
    rw [hC]
    exact E.measurable hF.1
  · intro x hx
    have hx' : E x ∈ RP k r (fun v => n₁ v * g v * n₂ v) :=
      (mem_RP_iff n₁ g n₂ (fun v => (hN v).1) (fun v => (hN v).2.1) x).1 hx
    obtain ⟨m', ⟨hm'Γ, hm'Ω⟩, huniq⟩ := hF.2 (E x) hx'
    have hR : ∀ m, m ∈ realPts (fun v y => n₂ v *ᵥ Φ v y) Γ ↔ E m ∈ realPts Φ Γ :=
      fun m => mem_realPts_iff Φ Γ n₂ hu m
    have hM : ∀ m, E (mulP m x) = mulP (E m) (E x) := fun m =>
      funext fun v => conjM_lmulM (hui v) (m v) (x v)
    refine ⟨Cf m', ⟨(hR _).2 (by rw [hEC]; exact hm'Γ), ?_⟩, ?_⟩
    · show mulP (Cf m') x ∈ Cf '' Ω
      rw [hC]
      show E (mulP (Cf m') x) ∈ Ω
      rw [hM, hEC]
      exact hm'Ω
    · rintro m ⟨hmΓ, hmΩ⟩
      have hmΩ' : E (mulP m x) ∈ Ω := by
        have h0 : mulP m x ∈ Cf '' Ω := hmΩ
        rw [hC] at h0
        exact h0
      have h1 : E m = m' := huniq (E m) ⟨(hR m).1 hmΓ, by rw [← hM]; exact hmΩ'⟩
      rw [← h1, hCE]
  · have hmp : MeasurePreserving E (Measure.pi fun _ : ι => lam)
        (Measure.pi fun v => lam.map (e v)) :=
      haveI : ∀ v, SigmaFinite (lam.map (e v)) := fun v => (e v).sigmaFinite_map
      measurePreserving_pi _ _ (fun v => ⟨(e v).measurable, rfl⟩)
    show _ = Measure.pi (fun _ : ι => lam) (Cf '' Ω)
    rw [hC, hmp.measure_preimage_equiv]
    rfl
end GlobalTheory.DegVol.UnipConj
end
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver GlobalTheory.HL
open scoped Pointwise Classical

namespace GlobalTheory.HL.PrimeToOrbit

theorem coord_one_orbit {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ)
    (S : GlobalTheory.HL.Frames L r k) (hgg : S.gg = false) (hvG : vE L S.ϖ S.G = 0)
    (hDu : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1)
    {δ δ' : S.Datum} {Λ Λ' : Submodule L.O S.V} (hT : S.IsTerm δ Λ) (hT' : S.IsTerm δ' Λ') :
    ∃ h ∈ S.H0, h • δ = δ' := by
  have ha : S.a = 0 := by simp [GlobalTheory.HL.Frames.a, GlobalTheory.HL.Frames.vth, hgg, hvG]
  obtain ⟨-, -, hall⟩ := GlobalTheory.HL.GoodClass.one_class L r k S hgg hDu
  have hint : ∀ d Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun d Λ h =>
    (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.1
  have hdd : ∀ d d' Λ, S.IsTerm d Λ → S.IsTerm d' Λ → d' = d := fun d d' Λ h h' =>
    (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.2 d' h'
  have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S
  have hcom := GlobalTheory.HL.ComplAct.main L r k S
  have hcls := GlobalTheory.HL.FrameClass.frame_classes L r k S
  obtain ⟨s, hs, e⟩ := hall _ (hint _ _ hT)
  obtain ⟨s', hs', e'⟩ := hall _ (hint _ _ hT')
  have h1 := hact δ _ hT _ (S.St.inv_mem hs)
  have h1' := hact δ' _ hT' _ (S.St.inv_mem hs')
  have hFr₁ : S.Fr δ (s⁻¹ • Λ) = S.frameCls S.f S.f' := by
    rw [h1.2.2.2.2.1, e, smul_smul, inv_mul_cancel, one_smul]
  have hFr₁' : S.Fr δ' (s'⁻¹ • Λ') = S.frameCls S.f S.f' := by
    rw [h1'.2.2.2.2.1, e', smul_smul, inv_mul_cancel, one_smul]
  have hM : S.M δ (s⁻¹ • Λ) = S.M δ' (s'⁻¹ • Λ') := by
    have h3 : (S.fr δ (s⁻¹ • Λ), S.fr' δ (s⁻¹ • Λ)) ∈ S.Fr δ' (s'⁻¹ • Λ') := by
      rw [hFr₁', ← hFr₁]; exact (hcls _ _).1
    exact ((hcls _ _).2.1 _ h3).2
  obtain ⟨h, hh, e₁⟩ := GlobalTheory.HL.StdPlace.term_orbit L r k S ha h1.1 h1'.1 hM
  have h4 := (hcom δ' _ h1'.1 h hh).1
  rw [e₁] at h4
  refine ⟨h⁻¹, S.H0.inv_mem hh, ?_⟩
  have h5 : h • δ' = δ := hdd _ _ _ h1.1 h4
  rw [← h5, smul_smul, inv_mul_cancel, one_smul]

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → P.PrimeTo → ∀ (d d' : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d' t' → Datum.Rel d d' := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hdim hrel hpt d d' t t' ht ht'
  have := hM.loc
  have := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hdim hrel
  obtain ⟨-, -, hgg, hvG, -⟩ : _ ∧ _ ∧ (S.gg = false ∧ vE M.L S.ϖ S.G = 0 ∧ True) := by
    obtain ⟨a1, a2, a3⟩ := GlobalTheory.HL.CoordHeight.height_eq M hM H r k P S c
    obtain ⟨b1, b2, -⟩ := a3 hpt
    exact ⟨a1, a2, b1, b2, trivial⟩
  obtain ⟨-, -, -, -, hD, -⟩ := GlobalTheory.FrameBasic.main M.L r k S
  have hDu : ∀ l, S.D l ≠ 0 → S.D l ∈ M.L.O ∧ ∃ y ∈ M.L.O, S.D l * y = 1 := by
    intro l hl
    by_cases h0 : l = 0
    · have e : S.D l = 1 := by
        subst h0
        unfold GlobalTheory.HL.Frames.D GlobalTheory.HL.lead
        exact Matrix.det_isEmpty (n := Fin 0)
      rw [e]
      exact ⟨M.L.O.one_mem, 1, M.L.O.one_mem, mul_one 1⟩
    · have hmem : (l : ℕ) ∈ P.ends := by
        unfold LocNG.FPair.ends
        simp only [Finset.mem_filter, Finset.mem_range]
        rw [GlobalTheory.HL.CoordHeight.Dm_eq c]
        exact ⟨l.2, Nat.one_le_iff_ne_zero.mpr fun h => h0 (Fin.ext h), hD l hl⟩
      have := hpt.2.2 _ hmem
      rwa [GlobalTheory.HL.CoordHeight.Dm_eq c] at this
  have hT := ((GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c).1 d t ht).1
  have hT' := ((GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c).1 d' t' ht').1
  exact ((GlobalTheory.HL.CoordDatum.transport M hM H r k P S c).2.2.1 d d').2
    (coord_one_orbit M.L r k S hgg hvG hDu hT hT')

end GlobalTheory.HL.PrimeToOrbit
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.unitary_rep_matrixCoeff_integral_eq_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d c : ℝ) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : H), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → 12 * n * rkR ε < c → ‖w‖ = 1 → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) w⟫_ℂ ∂(muG ε) = ⟪u, w⟫_ℂ) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪w, σ (umat g) w⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → ∀ x y : UJ ε, ∫ m, ⟪w, σ (umat (x * m * y)) w⟫_ℂ ∂ν = 0 := by
  first | exact @GlobalTheory.ConstTermZero.constant_term_zero | exact GlobalTheory.ConstTermZero.constant_term_zero | (intros; apply GlobalTheory.ConstTermZero.constant_term_zero <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.local_L2_bound_height : ∀ (B : RowsAut) (U : Set B.I.GA), 1 ≤ B.I.n → IsCompact U → (∀ u ∈ U, u.2 ∈ B.I.Kset) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : B.I.L2 B.μf B.fund) (x : B.I.GA), ∫⁻ g in U, (‖B.I.ext y (x * g)‖₊ : ENNReal) ^ 2 ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (C * (tau1 B.I x)⁻¹ ^ (4 * B.I.n ^ 2 * B.I.f) * ‖y‖ ^ 2) := by
  first | exact @GlobalTheory.LocMass.local_mass_le | exact GlobalTheory.LocMass.local_mass_le | (intros; apply GlobalTheory.LocMass.local_mass_le <;> assumption)
end
