module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DensOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.Bundle005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarExpB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarPolB

@[expose] public section

section

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem compactMatrix_off_block {ε : Fin n → Bool} (w : KCo ε) {a b : Fin n} (h : ε a ≠ ε b) :
    kMat w a b = 0 := by
  have hab : a ≠ b := fun e => h (e ▸ rfl)
  unfold kMat
  rw [if_neg hab, dif_neg (fun h' => h h'.2), dif_neg (fun h' => h h'.2.symm)]

theorem compactMatrix_conjTranspose {ε : Fin n → Bool} (w : KCo ε) : (kMat w)ᴴ = -kMat w := by
  ext a b
  change star (kMat w b a) = -(kMat w a b)
  by_cases hab : a = b
  · subst hab
    simp only [kMat, if_true]
    simp [Complex.ext_iff]
  · have hba : b ≠ a := Ne.symm hab
    by_cases h1 : b < a ∧ ε a = ε b
    · have h2 : ¬ (a < b ∧ ε b = ε a) := fun h => lt_asymm h.1 h1.1
      simp only [kMat, if_neg hab, if_neg hba, dif_pos h1, dif_neg h2, star_neg, star_star]
    · by_cases h2 : a < b ∧ ε b = ε a
      · simp only [kMat, if_neg hab, if_neg hba, dif_pos h2, dif_neg h1, neg_neg]
      · simp only [kMat, if_neg hab, if_neg hba, dif_neg h2, dif_neg h1, star_zero, neg_zero]

theorem compactMatrix_comm_signature {ε : Fin n → Bool} (w : KCo ε) : kMat w * Jm ε = Jm ε * kMat w := by
  ext a b
  simp only [Jm, mul_diagonal, diagonal_mul]
  by_cases h : ε a = ε b
  · rw [h, mul_comm]
  · rw [compactMatrix_off_block w h]; simp

theorem compactMatrix_inK {ε : Fin n → Bool} (w : KCo ε) : inK ε (kMat w) := by
  refine ⟨?_, compactMatrix_comm_signature w⟩
  unfold inG
  rw [compactMatrix_conjTranspose, Matrix.neg_mul, compactMatrix_comm_signature, neg_add_cancel]

theorem exists_compact_exp {ε : Fin n → Bool} (w : KCo ε) :
    ∃ k : KG ε, toMK k = NormedSpace.exp (kMat w) :=
  exists_toMK (exp_mem_Kset (compactMatrix_inK w))

theorem compactMatrix_injective (ε : Fin n → Bool) : Function.Injective (kMat (ε := ε)) := by
  intro w w' h
  have h1 : ∀ a b, kMat w a b = kMat w' a b := fun a b => by rw [h]
  refine Prod.ext (funext fun a => ?_) (funext fun ab => ?_)
  · have h2 := congrArg Complex.im (h1 a a)
    simpa [kMat] using h2
  · have h2 := h1 ab.1.1 ab.1.2
    have hne : ab.1.1 ≠ ab.1.2 := ne_of_gt ab.2.1
    simp only [kMat, if_neg hne, dif_pos ab.2] at h2
    exact h2

theorem compactMatrix_continuous (ε : Fin n → Bool) :
    Continuous (fun w : KCo ε => (kMat w : Matrix (Fin n) (Fin n) ℂ)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  unfold kMat
  by_cases h0 : a = b
  · simp only [h0, if_true]; fun_prop
  · simp only [if_neg h0]
    by_cases h1 : b < a ∧ ε a = ε b
    · simp only [dif_pos h1]; fun_prop
    · simp only [dif_neg h1]
      by_cases h2 : a < b ∧ ε b = ε a
      · simp only [dif_pos h2]; fun_prop
      · simp only [dif_neg h2]; fun_prop

theorem compactMatrix_zero (ε : Fin n → Bool) : kMat (0 : KCo ε) = 0 := by
  ext a b
  simp only [kMat]
  split_ifs <;> simp

theorem continuous_matrix_exp_compact : Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  exact continuous_iff_continuousAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℂ) x).continuousAt

theorem exists_exp_injOn_nhds_zero : ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ (0 : Matrix (Fin n) (Fin n) ℂ) ∈ U ∧
    Set.InjOn (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) U := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] _)) 0 := by
    rw [ContinuousLinearEquiv.coe_refl]
    exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  exact ⟨_, (h.toOpenPartialHomeomorph _).open_source, h.mem_toOpenPartialHomeomorph_source,
    (h.toOpenPartialHomeomorph _).injOn⟩

def expCompactMatrix {ε : Fin n → Bool} (w : KCo ε) : Fin n → Fin n → ℂ :=
  (NormedSpace.exp (kMat w) : Matrix (Fin n) (Fin n) ℂ)

theorem continuous_exp_compactMatrix (ε : Fin n → Bool) : Continuous (expCompactMatrix (ε := ε)) :=
  continuous_matrix_exp_compact.comp (compactMatrix_continuous ε)

theorem exp_compact_injOn (ε : Fin n → Bool) : ∃ δ > 0, Set.InjOn (expCompactMatrix (ε := ε)) {w | ‖w‖ < δ} := by
  obtain ⟨U, hU, h0, hinj⟩ := (exists_exp_injOn_nhds_zero (n := n))
  have hV : IsOpen ((fun w : KCo ε => (kMat w : Matrix (Fin n) (Fin n) ℂ)) ⁻¹' U) :=
    hU.preimage (compactMatrix_continuous ε)
  have h0V : (0 : KCo ε) ∈ (fun w : KCo ε => (kMat w : Matrix (Fin n) (Fin n) ℂ)) ⁻¹' U := by
    show kMat (0 : KCo ε) ∈ U
    rw [compactMatrix_zero]; exact h0
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hV 0 h0V
  refine ⟨δ, hδ, fun w hw w' hw' h => compactMatrix_injective ε (hinj ?_ ?_ h)⟩
  · exact hball (by simpa using hw)
  · exact hball (by simpa using hw')

def expImageOfCompact {ε : Fin n → Bool} (B : Set (KCo ε)) : Set (KG ε) :=
  {k | ∃ w ∈ B, toMK k = NormedSpace.exp (kMat w)}

def compactToMatrixEntries (ε : Fin n → Bool) : KG ε → (Fin n → Fin n → ℂ) := fun k => toMK k

theorem measurableSet_exp_image {ε : Fin n → Bool} {B : Set (KCo ε)} (hB : MeasurableSet B)
    (hinj : Set.InjOn (expCompactMatrix (ε := ε)) B) : MeasurableSet (expImageOfCompact B) := by
  have hI : MeasurableSet (expCompactMatrix (ε := ε) '' B) :=
    hB.image_of_continuousOn_injOn (continuous_exp_compactMatrix ε).continuousOn hinj
  have hc : Continuous (compactToMatrixEntries ε) := (continuous_toM ε).comp continuous_subtype_val
  have hm : Measurable (compactToMatrixEntries ε) := hc.measurable
  have e : expImageOfCompact B = compactToMatrixEntries ε ⁻¹' (expCompactMatrix (ε := ε) '' B) := by
    ext k
    constructor
    · rintro ⟨w, hw, h⟩
      exact ⟨w, hw, h.symm⟩
    · rintro ⟨w, hw, h⟩
      exact ⟨w, hw, h.symm⟩
  rw [e]
  exact hm hI

theorem polarSet_product_eq {ε : Fin n → Bool} (B : Set (KCo ε)) (C : Set (PCoord ε → ℂ)) :
    polSet (B ×ˢ C) =
      (intMuCD_eM ε) ⁻¹' (intMuCD_pM ε '' (expImageOfCompact B ×ˢ C)) := by
  ext g
  constructor
  · rintro ⟨s, hs, hg⟩
    obtain ⟨k, hk⟩ := exists_compact_exp s.1
    refine ⟨(k, s.2), ⟨⟨s.1, hs.1, hk⟩, hs.2⟩, ?_⟩
    show toMK k * NormedSpace.exp (pmat s.2) = toM g
    rw [hk, hg]
  · rintro ⟨⟨k, z⟩, ⟨⟨w, hw, hk⟩, hz⟩, hg⟩
    refine ⟨(w, z), ⟨hw, hz⟩, ?_⟩
    have hg' : toMK k * NormedSpace.exp (pmat z) = toM g := hg
    rw [← hg', hk]

theorem polar_measure_product_eq {ε : Fin n → Bool} {B : Set (KCo ε)} {C : Set (PCoord ε → ℂ)}
    (hA : MeasurableSet (expImageOfCompact B)) (hC : MeasurableSet C) :
    muPolar ε (polSet (B ×ˢ C)) = (∫⁻ z in C, ENNReal.ofReal (Jac z)) * dk ε (expImageOfCompact B) := by
  let R := expImageOfCompact B ×ˢ C
  have hpolar : MeasurableEmbedding (intMuCD_pM ε) :=
    (show Topology.IsClosedEmbedding (intMuCD_pM ε) from polarM_isClosedEmbedding ε).measurableEmbedding
  have htoM : MeasurableEmbedding (intMuCD_eM ε) :=
    (show Topology.IsClosedEmbedding (intMuCD_eM ε) from isClosedEmbedding_toM ε).measurableEmbedding
  have hT : MeasurableSet (intMuCD_pM ε '' R) := hpolar.measurableSet_image.2 (hA.prod hC)
  have hrange : intMuCD_pM ε '' R ⊆ Set.range (intMuCD_eM ε) := by
    rintro _ ⟨kz, _, rfl⟩
    change polarM kz ∈ Set.range (fun g : UJ ε => toM g)
    rw [range_toM]
    exact polarM_inUJ kz
  rw [polarSet_product_eq]
  change Measure.comap (β := Fin n → Fin n → ℂ) (intMuCD_eM ε) (muPolarMat ε)
    ((intMuCD_eM ε) ⁻¹' (intMuCD_pM ε '' R)) = _
  rw [htoM.comap_apply, Set.image_preimage_eq_of_subset hrange]
  change (Measure.map (β := Fin n → Fin n → ℂ) (intMuCD_pM ε) ((dk ε).prod
    (volume.withDensity fun z => ENNReal.ofReal (Jac z)))) (intMuCD_pM ε '' R) = _
  rw [Measure.map_apply hpolar.measurable hT, Set.preimage_image_eq _ hpolar.injective,
    show R = expImageOfCompact B ×ˢ C from rfl, Measure.prod_prod, withDensity_apply _ hC, mul_comm]

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HExp

variable {n : ℕ}

section Normed

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem haar_exp_density {ε : Fin n → Bool} (μ : Measure (UJ ε)) [μ.IsHaarMeasure] :
    ∃ d : ℝ, 0 < d ∧ DensOn (fun S => μ (expSet S)) d := by
  letI mV : MeasurableSpace (gV ε) := borel _
  haveI : BorelSpace (gV ε) := ⟨rfl⟩
  let eC : GCo ε ≃L[ℝ] gV ε := (gE ε).toContinuousLinearEquiv
  let lam : Measure (gV ε) := Measure.map eC volume
  haveI : (volume : Measure (KCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  haveI : (volume : Measure (GCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hlamH : lam.IsAddHaarMeasure := eC.isAddHaarMeasure_map volume
  obtain ⟨c, hc0, hct, hup, hdown⟩ := (ujChart ε).exists_density_unif' inferInstance mV ⟨rfl⟩ _
    inferInstance inferInstance μ inferInstance lam (by exact hlamH)
  have himg : ∀ S : Set (GCo ε), (ujChart ε).img (eC '' S) = expSet S := by
    intro S
    ext g
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, h⟩
      exact ⟨s, hs, h⟩
    · rintro ⟨s, hs, h⟩
      exact ⟨eC s, ⟨s, hs, rfl⟩, h⟩
  have hmeas : ∀ S : Set (GCo ε), MeasurableSet S → MeasurableSet (eC '' S) := fun S hS =>
    eC.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hS
  have hlam : ∀ S : Set (GCo ε), MeasurableSet S → lam (eC '' S) = volume S := by
    intro S hS
    rw [Measure.map_apply eC.continuous.measurable (hmeas S hS), Set.preimage_image_eq S eC.injective]
  have hsmall : ∀ δ > 0, ∃ δ' > 0, ∀ S : Set (GCo ε), (∀ s ∈ S, ‖s‖ < δ') →
      eC '' S ⊆ ball (0 : gV ε) δ := by
    intro δ hδ
    obtain ⟨δ', hδ', h⟩ := Metric.continuousAt_iff.mp (eC.continuous.continuousAt (x := 0)) δ hδ
    refine ⟨δ', hδ', fun S hS => ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have := h (x := s) (by simpa using hS s hs)
    simpa using this
  set d := c.toReal with hd
  have hdpos : 0 < d := ENNReal.toReal_pos hc0 hct
  have hc : c = ENNReal.ofReal d := (ENNReal.ofReal_toReal hct).symm
  refine ⟨d, hdpos, fun η hη => ?_⟩
  have hU : ∃ δ > 0, ∀ S : Set (GCo ε), MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
      μ (expSet S) ≤ ENNReal.ofReal ((1 + η) * d) * volume S := by
    obtain ⟨δ, hδ, h⟩ := hup (Real.toNNReal ((1 + η) * d)) (by
      rw [hc]
      show ENNReal.ofReal d < ENNReal.ofReal ((1 + η) * d)
      rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      nlinarith)
    obtain ⟨δ', hδ', h'⟩ := hsmall δ hδ
    refine ⟨δ', hδ', fun S hS hSδ => ?_⟩
    have := h (eC '' S) (hmeas S hS) (h' S hSδ)
    rw [himg, hlam S hS] at this
    exact this
  have hL : ∃ δ > 0, ∀ S : Set (GCo ε), MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
      ENNReal.ofReal ((1 - η) * d) * volume S ≤ μ (expSet S) := by
    by_cases hη1 : (1 - η) * d ≤ 0
    · refine ⟨1, one_pos, fun S _ _ => ?_⟩
      rw [ENNReal.ofReal_of_nonpos hη1, zero_mul]
      exact bot_le
    · have hη1' : 0 < (1 - η) * d := not_le.mp hη1
      obtain ⟨δ, hδ, h⟩ := hdown (Real.toNNReal ((1 - η) * d)) (by
        rw [hc]
        show ENNReal.ofReal ((1 - η) * d) < ENNReal.ofReal d
        rw [ENNReal.ofReal_lt_ofReal_iff hdpos]
        nlinarith)
      obtain ⟨δ', hδ', h'⟩ := hsmall δ hδ
      refine ⟨δ', hδ', fun S hS hSδ => ?_⟩
      have := h (eC '' S) (hmeas S hS) (h' S hSδ)
      rw [himg, hlam S hS] at this
      exact this
  obtain ⟨δ1, hδ1, h1⟩ := hU
  obtain ⟨δ2, hδ2, h2⟩ := hL
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun S hS hSδ => ⟨?_, ?_⟩⟩
  · exact h1 S hS fun s hs => lt_of_lt_of_le (hSδ s hs) (min_le_left _ _)
  · exact h2 S hS fun s hs => lt_of_lt_of_le (hSδ s hs) (min_le_right _ _)

end Normed

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset Matrix MeasureTheory Metric

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HPol

variable {n : ℕ}

theorem haar_pol_density {ε : Fin n → Bool} (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (d : ℝ)
    (h : DensOn (fun S => μ (expSet S)) d) : DensOn (fun S => μ (polSet S)) d := by
  intro η hη
  set η' : ℝ := min (η / 3) (1 / 2) with hη'def
  have hη'0 : 0 < η' := lt_min (by positivity) (by norm_num)
  have hη'1 : η' ≤ 1 / 2 := min_le_right _ _
  have hη'3 : η' ≤ η / 3 := min_le_left _ _
  obtain ⟨δ1, hδ1, hE⟩ := h η' hη'0
  obtain ⟨δ4, hδ4, hE2⟩ := h 2 (by norm_num)
  obtain ⟨δ2, hδ2, hI⟩ := HPol.image_est ε hη'0
  obtain ⟨δ3, hδ3, hP⟩ := HPol.polSet_eq_expSet ε
  refine ⟨min (min δ2 δ3) (min (δ1 / 2) (δ4 / 2)),
    lt_min (lt_min hδ2 hδ3) (lt_min (by positivity) (by positivity)), fun S hS hsmall => ?_⟩
  have hs2 : ∀ s ∈ S, ‖s‖ < δ2 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_left _ _).trans (min_le_left _ _))
  have hs3 : ∀ s ∈ S, ‖s‖ < δ3 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_left _ _).trans (min_le_right _ _))
  have hs1 : ∀ s ∈ S, ‖s‖ < δ1 / 2 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_right _ _).trans (min_le_left _ _))
  have hs4 : ∀ s ∈ S, ‖s‖ < δ4 / 2 := fun s hs =>
    lt_of_lt_of_le (hsmall s hs) ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hmeas, hnorm, hup, hlo⟩ := hI S hS hs2
  have hsm1 : ∀ t ∈ HPol.Lm '' S, ‖t‖ < δ1 := by
    rintro _ ⟨s, hs, rfl⟩
    have := hs1 s hs
    linarith [hnorm s hs]
  have hsm4 : ∀ t ∈ HPol.Lm '' S, ‖t‖ < δ4 := by
    rintro _ ⟨s, hs, rfl⟩
    have := hs4 s hs
    linarith [hnorm s hs]
  obtain ⟨hEu, hEl⟩ := hE _ hmeas hsm1
  beta_reduce at hEu hEl ⊢
  rw [hP S hs3]
  have hsq1 : (1 + η') * (1 + η') ≤ 1 + η := by nlinarith
  have hsq2 : 1 - η ≤ (1 - η') * (1 - η') := by nlinarith
  constructor
  · calc μ (expSet (HPol.Lm '' S)) ≤ ENNReal.ofReal ((1 + η') * d) * volume (HPol.Lm '' S) := hEu
      _ ≤ ENNReal.ofReal ((1 + η') * d) * (ENNReal.ofReal (1 + η') * volume S) := by gcongr
      _ = (ENNReal.ofReal ((1 + η') * d) * ENNReal.ofReal (1 + η')) * volume S := by
        rw [mul_assoc]
      _ ≤ ENNReal.ofReal ((1 + η) * d) * volume S := by
        gcongr
        rcases le_or_gt 0 d with hd | hd
        · rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          calc (1 + η') * d * (1 + η') = ((1 + η') * (1 + η')) * d := by ring
            _ ≤ (1 + η) * d := mul_le_mul_of_nonneg_right hsq1 hd
        · rw [ENNReal.ofReal_of_nonpos (by nlinarith), zero_mul]
          exact zero_le
  · rcases le_or_gt 0 d with hd | hd
    · calc ENNReal.ofReal ((1 - η) * d) * volume S
          ≤ (ENNReal.ofReal ((1 - η') * d) * ENNReal.ofReal (1 - η')) * volume S := by
            gcongr
            rw [← ENNReal.ofReal_mul (mul_nonneg (by linarith) hd)]
            apply ENNReal.ofReal_le_ofReal
            calc (1 - η) * d ≤ ((1 - η') * (1 - η')) * d := mul_le_mul_of_nonneg_right hsq2 hd
              _ = (1 - η') * d * (1 - η') := by ring
        _ = ENNReal.ofReal ((1 - η') * d) * (ENNReal.ofReal (1 - η') * volume S) := by
            rw [mul_assoc]
        _ ≤ ENNReal.ofReal ((1 - η') * d) * volume (HPol.Lm '' S) := by gcongr
        _ ≤ μ (expSet (HPol.Lm '' S)) := hEl
    ·
      obtain ⟨hE2u, hE2l⟩ := hE2 _ hmeas hsm4
      beta_reduce at hE2u hE2l
      have h3 : ENNReal.ofReal ((1 + 2) * d) = 0 := ENNReal.ofReal_of_nonpos (by linarith)
      rw [h3, zero_mul] at hE2u
      have h0 : ENNReal.ofReal ((1 - 2) * d) * volume (HPol.Lm '' S) = 0 :=
        le_antisymm (hE2l.trans hE2u) (zero_le)
      have hpos : ENNReal.ofReal ((1 - 2) * d) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        linarith
      have hvL : volume (HPol.Lm '' S) = 0 := (mul_eq_zero.mp h0).resolve_left hpos
      rw [hvL] at hlo
      have hpos' : ENNReal.ofReal (1 - η') ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        linarith
      have hvS : volume S = 0 :=
        (mul_eq_zero.mp (le_antisymm hlo (zero_le))).resolve_left hpos'
      rw [hvS, mul_zero]
      exact zero_le

end ReciprocityTheory.ChartRestriction.DS
end
end
