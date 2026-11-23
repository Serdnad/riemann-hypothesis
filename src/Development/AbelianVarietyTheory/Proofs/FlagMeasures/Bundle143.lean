module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle131
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNilpotentAlgebraIsotropicFlagUnipotentRadi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeOneEqResidue
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaxCompactInterLeviIffFrame
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Formalism.DoubleCosetMeasures.StatementZ
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
public import Formalism.PeriodIntegrals.UpqRep
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle118
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle122
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePairNormalForm_geometry_summary : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), NFFull N.F N.F' N.j N.j_le N.c ∧ IsLift N.F N.F' N.Wt ∧ IsCompl N.Wt N.Pi ∧ Module.finrank K N.Wt + 2 * r + 1 = Module.finrank K V ∧ N.Wn = N.Wt ⊔ Submodule.span K {N.F.z} ∧ uPerp N.F N.F' = N.Wn ⊔ II N.F N.F' ∧ wSp N.F N.F' = N.Wt ⊔ II N.F N.F' ∧ wSp N.F' N.F = wSp N.F N.F' ∧ GlobalTheory.Mass.PD (GlobalTheory.Mass.hRes H.B.flip N.Wt) ∧ 1 ≤ N.T ∧ N.nD N.j ≠ 0 ∧ N.Pi = V0 N.F N.F' ⊔ N.Ist := by
  first | exact @GlobalTheory.DegCnt.NF.geometry | exact GlobalTheory.DegCnt.NF.geometry | (intros; apply GlobalTheory.DegCnt.NF.geometry <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeSubHaar

open Topology

open MeasureTheory NumberField Matrix Finset in
open Topology in
private theorem uMat_one_flag_measures {n : ℕ} {ε : Fin n → Bool} : _root_.Formalism.MainNotions.S.uMat (1 : _root_.Formalism.REAL.UJ ε) = 1 := by
  have h1 := _root_.GlobalTheory.GaugeSubLoc.uMat_mul (1 : _root_.Formalism.REAL.UJ ε) 1
  have h2 := _root_.GlobalTheory.GaugeSubLoc.uMat_mul_inv (1 : _root_.Formalism.REAL.UJ ε)
  rw [mul_one] at h1
  rw [inv_one, ← h1] at h2
  exact h2

open MeasureTheory NumberField Matrix Finset in
open Topology in
private theorem comap_subtype_val_haar_properties {n : ℕ} {ε : Fin n → Bool}
    (S : Subgroup (_root_.Formalism.REAL.UJ ε)) (hS : IsClosed (S : Set (_root_.Formalism.REAL.UJ ε))) (d : ℕ)
    (μ : Measure (_root_.Formalism.REAL.UJ ε)) (h : _root_.GlobalTheory.FlagMeas.IsGaugeSub (S : Set (_root_.Formalism.REAL.UJ ε)) d μ) :
    Measure.map (Subtype.val : S → _root_.Formalism.REAL.UJ ε) (μ.comap Subtype.val) = μ ∧
      (μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε)).IsMulLeftInvariant ∧
      IsFiniteMeasureOnCompacts (μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε)) ∧
      μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) ≠ 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hme : MeasurableEmbedding (Subtype.val : S → _root_.Formalism.REAL.UJ ε) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  set ν := μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) with hν
  have hmap : Measure.map Subtype.val ν = μ := by
    rw [hme.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 h1)
  have hinv : ν.IsMulLeftInvariant := by
    refine ⟨fun s => ?_⟩
    have key : Measure.map Subtype.val (Measure.map (s * ·) ν) = Measure.map Subtype.val ν := by
      rw [Measure.map_map hme.measurable (measurable_const_mul s)]
      have hcomp : (Subtype.val ∘ (s * ·)) =
          (fun g : _root_.Formalism.REAL.UJ ε => (s : _root_.Formalism.REAL.UJ ε) * g) ∘ Subtype.val := by
        funext x; rfl
      rw [hcomp, ← Measure.map_map (measurable_const_mul _) hme.measurable, hmap]
      exact h2 s s.2
    have := congrArg (Measure.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε)) key
    rwa [hme.comap_map, hme.comap_map] at this
  set f : _root_.Formalism.REAL.UJ ε → ℝ := fun g => √(_root_.Formalism.REAL.hs (_root_.Formalism.MainNotions.S.uMat g - 1)) with hfdef
  have hf : Continuous f := by
    simp only [hfdef, _root_.Formalism.REAL.hs]
    have := _root_.GlobalTheory.GaugeConst.continuous_uMat ε
    fun_prop
  have hf1 : f 1 = 0 := by simp [hfdef, _root_.Formalism.REAL.hs, uMat_one_flag_measures]
  revert h3
  change Filter.Tendsto _ _ (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) → _
  intro h3
  have hL0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hLtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hev := (h3.eventually (isOpen_Ioo.mem_nhds ⟨pos_iff_ne_zero.2 hL0, lt_top_iff_ne_top.2 hLtop⟩)).and
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] 0)
  obtain ⟨r, ⟨hpos, htop⟩, hr⟩ := hev.exists
  set B := {g | f g ≤ r} with hBdef
  have hB0 : μ B ≠ 0 := by
    intro h0
    change 0 < μ B / _ at hpos
    rw [h0, ENNReal.zero_div] at hpos
    exact lt_irrefl _ hpos
  have hBtop : μ B ≠ ⊤ := by
    intro h0
    change μ B / _ < ⊤ at htop
    rw [h0, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at htop
    exact lt_irrefl _ htop
  have hνB : ν (Subtype.val ⁻¹' B) = μ B := by rw [← hme.map_apply, hmap]
  refine ⟨hmap, hinv, ?_, ?_⟩
  · refine ⟨fun K hK => ?_⟩
    have hUo : IsOpen (Subtype.val ⁻¹' {g | f g < r} : Set S) :=
      (isOpen_lt hf continuous_const).preimage continuous_subtype_val
    have hUne : (Subtype.val ⁻¹' {g | f g < r} : Set S).Nonempty :=
      ⟨1, by simp only [Set.mem_preimage, Set.mem_setOf_eq, OneMemClass.coe_one, hf1]; exact hr⟩
    have hUtop : ν (Subtype.val ⁻¹' {g | f g < r}) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono (Set.preimage_mono
        (show {g | f g < r} ⊆ B from fun g (hg : f g < r) => (le_of_lt hg : f g ≤ r))))
      rw [hνB]; exact hBtop
    exact measure_lt_top_of_isCompact_of_isMulLeftInvariant _ hUo hUne hUtop hK
  · intro h0
    apply hB0
    rw [← hνB, h0, Measure.coe_zero, Pi.zero_apply]


open MeasureTheory NumberField Matrix Finset in
open Topology in
theorem _root_.GlobalTheory.GaugeSubHaar.isGaugeSub_haar : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (_root_.Formalism.REAL.UJ ε)), IsClosed (S : Set (_root_.Formalism.REAL.UJ ε)) → ∀ (d : ℕ) (μ : Measure (_root_.Formalism.REAL.UJ ε)), _root_.GlobalTheory.FlagMeas.IsGaugeSub (S : Set (_root_.Formalism.REAL.UJ ε)) d μ → SigmaFinite μ ∧ IsFiniteMeasureOnCompacts μ ∧ ∀ μ', _root_.GlobalTheory.FlagMeas.IsGaugeSub (S : Set (_root_.Formalism.REAL.UJ ε)) d μ' → μ' = μ := by
  intro n ε S hS d μ hμ
  have hme : MeasurableEmbedding (Subtype.val : S → _root_.Formalism.REAL.UJ ε) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  obtain ⟨hmap, hinv, hfin, hne⟩ := comap_subtype_val_haar_properties S hS d μ hμ
  set ν := μ.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) with hν
  have hfinμ : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => by
    rw [← hmap, hme.map_apply]
    exact (hS.isClosedEmbedding_subtypeVal.isCompact_preimage hK).measure_lt_top⟩
  haveI : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (_root_.Formalism.REAL.UJ ε) := inferInstance
  haveI : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  refine ⟨inferInstance, hfinμ, fun μ' hμ' => ?_⟩
  obtain ⟨hmap', hinv', hfin', -⟩ := comap_subtype_val_haar_properties S hS d μ' hμ'
  set ν' := μ'.comap (Subtype.val : S → _root_.Formalism.REAL.UJ ε) with hν'
  have hcover : ∃ k, ν (compactCovering S k) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering]
    exact measure_iUnion_null hcon
  obtain ⟨k, hk⟩ := hcover
  haveI : ν.IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_compactCovering S k) hk
  haveI : ν.IsHaarMeasure := { }
  have hsmul := Measure.isMulLeftInvariant_eq_smul ν' ν
  set c := ν'.haarScalarFactor ν with hc
  have hμc : μ' = c • μ := by
    rw [← hmap', hsmul, Measure.map_smul c hme.measurable.aemeasurable, hmap]
  obtain ⟨-, -, h3⟩ := hμ
  obtain ⟨-, -, h3'⟩ := hμ'
  rw [hμc] at h3'
  revert h3 h3'
  change Filter.Tendsto _ _ (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) →
    Filter.Tendsto _ _ (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) → _
  intro h3 h3'
  have hL0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume _ one_pos).ne'
  have hLtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h4 := ENNReal.Tendsto.const_mul h3 (Or.inr (ENNReal.coe_ne_top (r := c)))
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_div_assoc] at h3'
  have heq := tendsto_nhds_unique h4 h3'
  have hc1 : (c : ENNReal) = 1 := by
    rw [← ENNReal.mul_left_inj hL0 hLtop, one_mul]
    exact heq
  rw [hμc, ENNReal.coe_eq_one.1 hc1, one_smul]

end GlobalTheory.GaugeSubHaar
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.exists_nilpotentAlgebra_isotropicFlagUnipotentRadical : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∃ (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : Fin (dimN n j) → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) ∧ (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) ∧ (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) ∧ flagN ε W = {g | uMat g - 1 ∈ A} := by
  first | exact @GlobalTheory.RadicalAlg.exists_algebra_flagN | exact GlobalTheory.RadicalAlg.exists_algebra_flagN | (intros; apply GlobalTheory.RadicalAlg.exists_algebra_flagN <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.glNormOneAdelicQuotientVolume_one_eq_residue : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → glVol E 1 = ENNReal.ofReal (dedekindZeta_residue E * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E) := by
  first | exact @GlobalTheory.NormOneVol.glVol_one | exact GlobalTheory.NormOneVol.glVol_one | (intros; apply GlobalTheory.NormOneVol.glVol_one <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.iwasawa_decomposition_unitary_isotropicFlag : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → (∀ g : Formalism.REAL.UJ ε, ∃ u ∈ flagN ε W, ∃ m ∈ flagM ε W, ∃ k ∈ maxK ε, g = u * m * k) ∧ ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, u * m ∈ maxK ε → u = 1 := by
  first | exact @GlobalTheory.RealIwasawa.iwasawa | exact GlobalTheory.RealIwasawa.iwasawa | (intros; apply GlobalTheory.RealIwasawa.iwasawa <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.mem_maxCompact_inter_levi_iff_frame : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (p' q' : ℕ) (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (P : Matrix (Fin n) (Fin p') ℂ) (Q : Matrix (Fin n) (Fin q') ℂ), ((∀ i, (T i)ᴴ * T i = 1) ∧ (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) ∧ (∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0) ∧ (∀ i, (T i)ᴴ * P = 0) ∧ (∀ i, (T i)ᴴ * Q = 0) ∧ Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Formalism.REAL.Jm ε * P = P ∧ Formalism.REAL.Jm ε * Q = -Q ∧ (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * Pᴴ + Q * Qᴴ = 1 ∧ ∀ (l : Fin (a + 1)) (y : Fin n → ℂ), y ∈ W l ↔ (∑ i ∈ univ.filter (fun i : Fin a => i.val < l.val), T i * (T i)ᴴ) *ᵥ y = y) → ∀ g : Formalism.REAL.UJ ε, g ∈ maxK ε ∩ flagM ε W ↔ ∃ (k : ∀ i, Formalism.REAL.UJ (allPos (j i))) (u : Formalism.REAL.UJ (allPos p')) (v : Formalism.REAL.UJ (allPos q')), uMat g = (∑ i, (T i * uMat (k i) * (T i)ᴴ + Formalism.REAL.Jm ε * T i * uMat (k i) * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * uMat u * Pᴴ + Q * uMat v * Qᴴ := by
  first | exact @GlobalTheory.FlagLeviRange.mem_maxK_inter_flagM_iff | exact GlobalTheory.FlagLeviRange.mem_maxK_inter_flagM_iff | (intros; apply GlobalTheory.FlagLeviRange.mem_maxK_inter_flagM_iff <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem absArith_const (r : ℕ) (hr : 1 ≤ r) :
    (4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r) *
      Real.exp 1 ^ (r * (r + 2)) ≤ (4 * r : ℝ) ^ (44 * r ^ 3) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h4 : (4 : ℝ) ≤ 4 * r := by linarith
  have h1 : ((r : ℝ) + 1) * 24 ≤ (4 * r : ℝ) ^ 3 := by
    have : (r : ℝ) ≤ (r : ℝ) ^ 3 := le_self_pow₀ hr' (by norm_num)
    nlinarith
  have he : Real.exp 1 ≤ 4 * r := by
    have := Real.exp_one_lt_d9
    linarith
  have hexp : 11 * r ^ 2 + 3 + (24 * r ^ 3 + 1) + 2 * r + r * (r + 2) ≤ 44 * r ^ 3 := by
    have a1 : r ≤ r ^ 3 := Nat.le_self_pow (by norm_num) r
    have a2 : r ^ 2 ≤ r ^ 3 := Nat.pow_le_pow_right hr (by norm_num)
    nlinarith
  calc _ ≤ (4 * r : ℝ) ^ (11 * r ^ 2) * (4 * r : ℝ) ^ 3 * (4 * r : ℝ) ^ (24 * r ^ 3 + 1) *
        (4 * r : ℝ) ^ (2 * r) * (4 * r : ℝ) ^ (r * (r + 2)) := by
        gcongr
        linarith
    _ = (4 * r : ℝ) ^ (11 * r ^ 2 + 3 + (24 * r ^ 3 + 1) + 2 * r + r * (r + 2)) := by
        simp only [pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by linarith) hexp

theorem absArith_shift (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) :
    (Real.pi * Real.exp 1 / m) ^ (r * m) * 4 ^ m * (2 ^ r) ^ m ≤
      Real.exp 1 ^ (r * (r + 2)) *
        (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (0 : ℝ) < ((m + r + 2 : ℕ) : ℝ) := by positivity
  have hpe : 0 < Real.pi * Real.exp 1 := by positivity
  have h1 : (((m + r + 2 : ℕ) : ℝ) / m) ^ m ≤ Real.exp 1 ^ (r + 2) := by
    have h2 : ((m + r + 2 : ℕ) : ℝ) / m ≤ Real.exp (((r + 2 : ℕ) : ℝ) / m) := by
      have := Real.add_one_le_exp (((r + 2 : ℕ) : ℝ) / m)
      refine le_trans (le_of_eq ?_) this
      push_cast
      field_simp
      ring
    calc _ ≤ Real.exp (((r + 2 : ℕ) : ℝ) / m) ^ m := by gcongr
      _ = Real.exp 1 ^ (r + 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1
        field_simp
  have h3 : (((m + r + 2 : ℕ) : ℝ) / m) ^ (r * m) ≤ Real.exp 1 ^ (r * (r + 2)) := by
    rw [mul_comm r m, mul_comm r (r + 2), pow_mul, pow_mul]
    gcongr
  have h4 : (4 : ℝ) ^ m ≤ 4 ^ (r * m) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_left m hr)
  calc _ ≤ (Real.pi * Real.exp 1 / m) ^ (r * m) * 4 ^ (r * m) * (2 ^ r) ^ m := by gcongr
    _ = (((m + r + 2 : ℕ) : ℝ) / m) ^ (r * m) *
        (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m) := by
        rw [← pow_mul, ← mul_pow, ← mul_pow, ← mul_pow]
        congr 1
        field_simp
        ring
    _ ≤ _ := by gcongr

theorem absArith : ∀ (k r : ℕ) (H₁ De D : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → 1 ≤ H₁ → 1 ≤ De → 0 < D → ((4 * r : ℝ) ^ (11 * r ^ 2) * De ^ (12 * r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * 4 ^ (k - 2 - r) * ((r + 1) * 4 ^ (24 * r ^ 3 + 1))) * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ (k - 2 - r) ≤ absBd k r H₁ De D := by
  intro k r H₁ De D hr hk hH hDe hD
  obtain ⟨m, rfl⟩ : ∃ m, k = m + r + 2 := ⟨k - 2 - r, by omega⟩
  have hm : 1 ≤ m := by omega
  have hmk : m + r + 2 - 2 - r = m := by omega
  unfold absBd
  rw [hmk]
  have hA := absArith_const r hr
  have hB := absArith_shift r m hr hm
  have hC : De ^ (12 * r ^ 2) * De ^ (2 * r) ≤ De ^ (14 * r ^ 2) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hDe (by nlinarith)
  have hH0 : 0 ≤ H₁ := by linarith
  have hDe0 : 0 ≤ De := by linarith
  calc _ = ((4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r)) *
        ((Real.pi * Real.exp 1 / m) ^ (r * m) * 4 ^ m * (2 ^ r) ^ m) *
        (De ^ (12 * r ^ 2) * De ^ (2 * r)) * H₁ ^ (24 * r ^ 3) * (D ^ m)⁻¹ := by
        rw [div_pow (2 ^ r : ℝ) D m, div_eq_mul_inv ((2 ^ r : ℝ) ^ m)]
        ring
    _ ≤ ((4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r)) *
        (Real.exp 1 ^ (r * (r + 2)) *
          (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m)) *
        De ^ (14 * r ^ 2) * H₁ ^ (24 * r ^ 3) * (D ^ m)⁻¹ := by gcongr
    _ = ((4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r) *
        Real.exp 1 ^ (r * (r + 2))) * H₁ ^ (24 * r ^ 3) * De ^ (14 * r ^ 2) *
          (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m) * (D ^ m)⁻¹ := by
        ac_rfl
    _ ≤ _ := by gcongr

end GlobalTheory.Amp
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem volU_succ_eq_mul (m : ℕ) :
    volU (m + 1) = volU m * (2 * Real.pi ^ (m + 1) / (m.factorial : ℝ) * 2 ^ m) := by
  have h : (m + 1) * (m + 1 - 1) / 2 = m * (m - 1) / 2 + m := by
    have := Nat.triangle_succ m
    simpa using this
  unfold volU sphV
  rw [Finset.prod_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m)), h, pow_add]
  simp only [Nat.add_sub_cancel]
  ring

theorem vInv_pos_of_numberField (E : Type) [Field E] [NumberField E] : 0 < Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  have : (0 : ℝ) < |(discr E : ℝ)| := abs_pos.mpr (by exact_mod_cast discr_ne_zero E)
  positivity

theorem mass_ratio_mul_unitary_volume :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ), 1 ≤ M →
      Formalism.HermitianLatticesTheory.massRatioRightSide E M * volU M ^ Formalism.HermitianLatticesTheory.fDeg E =
        rankFac E M * volU (M - 1) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  intro E _ _ _ M hM
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have hv := vInv_pos_of_numberField E
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide rankFac
  simp only [Nat.add_sub_cancel]
  rw [volU_succ_eq_mul]
  set v := Formalism.HermitianLatticesTheory.vInv E
  set f := Formalism.HermitianLatticesTheory.fDeg E
  have h2 : 0 < 2 * v := by positivity
  have hfac : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hpi := Real.pi_pos.ne'
  have key : ((m.factorial : ℝ) * (v / Real.pi) ^ (m + 1)) *
      (2 * Real.pi ^ (m + 1) / (m.factorial : ℝ) * 2 ^ m) = (2 * v) ^ (m + 1) := by
    rw [div_pow, mul_pow]
    field_simp
    ring
  have hr : (2 * v) ^ ((f : ℝ) * (((m + 1 : ℕ) : ℝ) - 1 / 2)) =
      ((2 * v) ^ (m + 1)) ^ f / Real.sqrt ((2 * v) ^ f) := by
    rw [Real.sqrt_eq_rpow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul h2.le, ← Real.rpow_sub h2]
    congr 1
    push_cast
    ring
  rw [hr, ← key, mul_pow (volU m), mul_pow ((m.factorial : ℝ) * (v / Real.pi) ^ (m + 1))]
  ring

end GlobalTheory.FlagMeas
end

section

open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

instance borelMat (n : ℕ) : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))

def IsHaarKH (k r : ℕ) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) : Prop :=
  IsProbabilityMeasure μ ∧ μ (GlobalTheory.ThA.KH k r)ᶜ = 0 ∧
    (∀ a ∈ GlobalTheory.ThA.KH k r, μ.map (fun g => a * g) = μ) ∧
    ∀ U : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), IsOpen U → 1 ∈ U → 0 < μ U

def peak (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := (1 + (Matrix.trace g).re / n) / 2

def peakN {n : ℕ} (μ : Measure (Matrix (Fin n) (Fin n) ℂ)) (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ((peak n g ^ m / ∫ h, peak n h ^ m ∂μ : ℝ) : ℂ)

end GlobalTheory.KFinAvg

namespace GlobalTheory.KFinAvg
open Matrix

theorem isCompact_KH (k r : ℕ) : IsCompact (GlobalTheory.ThA.KH k r) := by
  have hc : IsClosed (PI.UpqRep.UH (PI.UpqRep.Hpk k r)) := by
    show IsClosed {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ | gᴴ * PI.UpqRep.Hpk k r * g = PI.UpqRep.Hpk k r}
    exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  exact (GlobalTheory.isCompact_unitaryGroup (Fin (2 * r + k + 1)) ℂ).inter_left hc

end GlobalTheory.KFinAvg
end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.localAmplitude_summand_at_term_orbit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ Λ, ∀ h ∈ S.St, P (h • Λ) ↔ P Λ) → ∀ Λ, S.IsTerm d Λ → IsLat L Λ → ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), o = Quotient.mk'' Λ → S.IsTerm d o.out ∧ (∃ h ∈ S.St, o.out = h • Λ) ∧ (if S.IsTerm d o.out ∧ P o.out then (S.mu o.out : ℂ) * S.om d o.out else 0) = (if P Λ then (S.mu Λ : ℂ) * S.om d Λ else 0) ∧ (if S.IsTerm d o.out ∧ P o.out then ENNReal.ofReal (S.mu o.out) else 0) = (if P Λ then ENNReal.ofReal (S.mu Λ) else 0) := by
  first | exact @GlobalTheory.HL.amp_summand_orbit | exact GlobalTheory.HL.amp_summand_orbit | (intros; apply GlobalTheory.HL.amp_summand_orbit <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianMass_eq_sum_frameClasses : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ h ∈ S.St, ∀ Λ, S.IsTerm d Λ → P Λ → P (h • Λ)) → S.mass d P = S.sumCls fun C => S.nT d C P := by
  first | exact @GlobalTheory.HL.mass_eq_sumCls | exact GlobalTheory.HL.mass_eq_sumCls | (intros; apply GlobalTheory.HL.mass_eq_sumCls <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem sumData_mass_eq_sumCls : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ P : S.Datum → Submodule L.O S.V → Prop, (∀ h ∈ S.St, ∀ d Λ, S.IsTerm d Λ → P d Λ → P d (h • Λ)) → (S.sumData fun d => S.mass d (P d)) = (S.sumCls fun C => S.sumData fun d => S.nT d C (P d)) ∧ ∀ h ∈ S.St, ∀ d C, S.nT d (h • C) (P d) = S.nT d C (P d) := by
  intro F _ _ _ _ _ E _ _ _ L r k S P hP
  refine ⟨?_, fun h hh d C => ?_⟩
  · have e : (fun d => S.mass d (P d)) = fun d => S.sumCls fun C => S.nT d C (P d) :=
      funext fun d => mass_eq_sumCls L r k S d (P d) fun h hh Λ => hP h hh d Λ
    rw [e]
    unfold Frames.sumData Frames.sumCls
    simp only [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun c => ?_
    split_ifs
    · exact tsum_congr fun o => mul_left_comm _ _ _
    · simp
  · unfold Frames.nT
    have e : ({Λ | S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = h • C} : Set (Submodule L.O S.V)) =
        (fun Λ => h • Λ) '' {Λ | S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = C} := by
      ext Λ
      constructor
      · rintro ⟨h1, h2, h3⟩
        have A := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ h1 h⁻¹ (S.St.inv_mem hh)
        refine ⟨h⁻¹ • Λ, ⟨A.1, hP _ (S.St.inv_mem hh) d Λ h1 h2, ?_⟩, smul_inv_smul h Λ⟩
        rw [A.2.2.2.2.1, h3, inv_smul_smul]
      · rintro ⟨Λ, ⟨h1, h2, h3⟩, rfl⟩
        have A := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ h1 h hh
        refine ⟨A.1, hP _ hh d Λ h1 h2, ?_⟩
        rw [A.2.2.2.2.1, h3]
    rw [e, (MulAction.injective h).encard_image]

end GlobalTheory.HL
end
