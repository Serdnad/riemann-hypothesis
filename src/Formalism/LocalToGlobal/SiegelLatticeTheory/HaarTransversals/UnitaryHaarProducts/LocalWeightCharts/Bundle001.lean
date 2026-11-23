module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NotMidCases
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory

namespace WlocSk

open HM

theorem uw_finite {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) : IsFiniteMeasure (hmeas (Formalism.QuantumDeterminants.UWset k r z) (uw_clsub z)) := by
  have : CompactSpace (Grp (Formalism.QuantumDeterminants.UWset k r z : Set (Mx k r)) (uw_clsub z)) :=
    isCompact_iff_compactSpace.mp (compactW z hz hT)
  refine ⟨?_⟩
  unfold hmeas
  rw [Measure.map_apply (val_cemb _ _).continuous.measurable MeasurableSet.univ, Set.preimage_univ]
  exact isCompact_univ.measure_lt_top

theorem haar_measure_unipotent_nilradical : HaarWN := by
  intro k r z hz hT
  exact ⟨hmeas (Formalism.QuantumDeterminants.UWset k r z) (uw_clsub z), haarNm k r, hmeas_haar _ _, haarNm_haar,
    uw_finite z hz hT, haarNm_compact⟩

end WlocSk
end
end

section

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas Matrix
open scoped ENNReal

namespace WlocSk

abbrev CSp (m d : ℕ) := (Fin m → ℂ) × (Fin d → ℝ)

instance instAddHaarCSp (m d : ℕ) : (volume : Measure (CSp m d)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

def NCoordHaar : Prop :=
  ∀ (k r : ℕ) (μN : Measure (Formalism.QuantumDeterminants.Mt k r)), IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    (∀ K : Set (Formalism.QuantumDeterminants.Mt k r), IsCompact K → μN K < ⊤) →
    ∃ (m d q : ℕ) (Φ : CSp m d → Formalism.QuantumDeterminants.Mt k r) (c : ℝ≥0∞) (κ : ℝ),
      1 ≤ q ∧ ((q * (2 * m + d) : ℕ) : ℝ) < N1H k r ∧ 0 < κ ∧ c ≠ ⊤ ∧ Measurable Φ ∧
      μN = c • (volume : Measure (CSp m d)).map Φ ∧
      ∀ t, 1 + ‖t‖ ≤ κ * Formalism.L2.SG.WuDecay.opn (Matrix.of (Φ t)) ^ q

def NChart : Prop :=
  ∀ (k r : ℕ), ∃ (m d q : ℕ) (Φ : CSp m d → Formalism.QuantumDeterminants.Mt k r) (κ : ℝ),
    1 ≤ q ∧ ((q * (2 * m + d) : ℕ) : ℝ) < N1H k r ∧ 0 < κ ∧ MeasurableEmbedding Φ ∧
    Set.range Φ = {x | Matrix.of x ∈ Formalism.QuantumDeterminants.Nset k r} ∧
    (∀ m₀ ∈ Formalism.QuantumDeterminants.Nset k r, ∃ T : CSp m d → CSp m d, MeasurePreserving T volume volume ∧
      ∀ t, Formalism.QuantumDeterminants.lmulM m₀ (Φ t) = Φ (T t)) ∧
    ∀ t, 1 + ‖t‖ ≤ κ * Formalism.L2.SG.WuDecay.opn (Matrix.of (Φ t)) ^ q

def NUniq : Prop :=
  ∀ (k r : ℕ) (μ μ' : Measure (Formalism.QuantumDeterminants.Mt k r)), IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ →
    IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ' → ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ μ = c • μ'

theorem nCoordHaar_of (hC : NChart) (hU : NUniq) : NCoordHaar := by
  intro k r μN hN _
  obtain ⟨m, d, q, Φ, κ, hq, hD, hκ, hΦ, hrange, hT, hgrow⟩ := hC k r
  have hmeasL : ∀ a : Mat k r, Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) a) := fun a => by
    have : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) a) := by
      unfold Formalism.QuantumDeterminants.lmulM
      exact continuous_const.matrix_mul continuous_id
    exact this.measurable
  have hH : IsHaarOn (Formalism.QuantumDeterminants.Nset k r) ((volume : Measure (CSp m d)).map Φ) := by
    refine ⟨hΦ.sigmaFinite_map, ?_, ?_, ?_⟩
    · intro h0
      rw [Measure.map_eq_zero_iff hΦ.measurable.aemeasurable] at h0
      exact isOpen_univ.measure_ne_zero (volume : Measure (CSp m d)) Set.univ_nonempty
        (by rw [h0, Measure.coe_zero, Pi.zero_apply])
    · rw [Measure.map_apply hΦ.measurable]
      · have : Φ ⁻¹' {x | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r} = ∅ := by
          ext t
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
          have : Φ t ∈ Set.range Φ := ⟨t, rfl⟩
          rw [hrange] at this
          exact this
        rw [this, measure_empty]
      · have hcl : MeasurableSet (Set.range Φ) := hΦ.measurableSet_range
        rw [hrange] at hcl
        exact hcl.compl
    · intro s hs
      obtain ⟨T, hTm, hTe⟩ := hT s hs
      rw [Measure.map_map (hmeasL s) hΦ.measurable]
      have : Formalism.QuantumDeterminants.lmulM s ∘ Φ = Φ ∘ T := funext hTe
      rw [this, ← Measure.map_map hΦ.measurable hTm.measurable, hTm.map_eq]
  obtain ⟨c, hc, hμ⟩ := hU k r μN _ hN hH
  exact ⟨m, d, q, Φ, c, κ, hq, hD, hκ, hc, hΦ.measurable, hμ, hgrow⟩

local instance instAlgCLM (n : ℕ) :
    Algebra ℂ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := ContinuousLinearMap.algebra
local instance instModCLM (n : ℕ) :
    Module ℂ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := ContinuousLinearMap.module

lemma opn_continuous (k r : ℕ) :
    Continuous fun m : Formalism.QuantumDeterminants.Mt k r => Formalism.L2.SG.WuDecay.opn (Matrix.of m) := by
  unfold Formalism.L2.SG.WuDecay.opn
  have : Continuous fun m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 * r + k + 1)) m := by
    let L : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →ₗ[ℂ]
        (EuclideanSpace ℂ (Fin (2 * r + k + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1))) :=
      { toFun := fun m => Matrix.toEuclideanCLM (𝕜 := ℂ) m
        map_add' := fun a b => map_add _ a b
        map_smul' := fun a b => map_smul _ a b }
    exact L.continuous_of_finiteDimensional
  exact continuous_norm.comp (this.comp continuous_id)

lemma finrank_CSp (m d : ℕ) : Module.finrank ℝ (CSp m d) = 2 * m + d := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_fin_fun]
  simp [Complex.finrank_real_complex, mul_comm]

theorem nIntDecay_of (h : NCoordHaar) : NIntDecay := by
  intro k r μN hN hNc
  obtain ⟨m, d, q, Φ, c, κ, hq, hD, hκ, hc, hΦ, hμ, hgrow⟩ := h k r μN hN hNc
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hD' : (Module.finrank ℝ (CSp m d) : ℝ) < N1H k r / q := by
    rw [finrank_CSp, lt_div_iff₀ hq0, mul_comm]; exact_mod_cast hD
  have hF : Measurable fun x : Formalism.QuantumDeterminants.Mt k r =>
      ENNReal.ofReal (Formalism.L2.SG.WuDecay.opn (Matrix.of x) ^ (-N1H k r)) :=
    ENNReal.measurable_ofReal.comp ((opn_continuous k r).measurable.pow_const _)
  rw [hμ, lintegral_smul_measure, lintegral_map hF hΦ]
  refine ENNReal.mul_lt_top hc.lt_top ?_
  set s := N1H k r / q with hs
  have hbound : ∀ t : CSp m d,
      ENNReal.ofReal (Formalism.L2.SG.WuDecay.opn (Matrix.of (Φ t)) ^ (-N1H k r)) ≤
        ENNReal.ofReal (κ ^ s) * ENNReal.ofReal ((1 + ‖t‖) ^ (-s)) := by
    intro t
    set o := Formalism.L2.SG.WuDecay.opn (Matrix.of (Φ t)) with ho
    have ho0 : 0 ≤ o := norm_nonneg _
    have h1 : 0 < 1 + ‖t‖ := by positivity
    have h2 : (1 + ‖t‖) / κ ≤ o ^ q := by
      rw [div_le_iff₀ hκ, mul_comm]; exact hgrow t
    have h3 : 0 < (1 + ‖t‖) / κ := div_pos h1 hκ
    have hoq : o ^ (-N1H k r) = (o ^ q) ^ (-s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ho0, hs]
      congr 1
      field_simp
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [hoq]
    calc (o ^ q) ^ (-s)
        ≤ ((1 + ‖t‖) / κ) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos h3 h2 (by
            have : 0 < s := lt_of_le_of_lt (Nat.cast_nonneg _) hD'
            linarith)
      _ = κ ^ s * (1 + ‖t‖) ^ (-s) := by
          rw [Real.div_rpow h1.le hκ.le, div_eq_mul_inv, ← Real.rpow_neg hκ.le, neg_neg, mul_comm]
  calc ∫⁻ t, ENNReal.ofReal (Formalism.L2.SG.WuDecay.opn (Matrix.of (Φ t)) ^ (-N1H k r))
      ≤ ∫⁻ t : CSp m d, ENNReal.ofReal (κ ^ s) *
          ENNReal.ofReal ((1 + ‖t‖) ^ (-s)) := lintegral_mono hbound
    _ = ENNReal.ofReal (κ ^ s) *
          ∫⁻ t : CSp m d, ENNReal.ofReal ((1 + ‖t‖) ^ (-s)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (finite_integral_one_add_norm hD')

end WlocSk
end
end

section

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas Matrix
open scoped InnerProductSpace ENNReal

namespace WlocSk

section Scale

variable {k r : ℕ} {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

lemma rconv_smul (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) (e : Mat k r → ℂ) (A : Mat k r → Vp) (cc : ℂ)
    (x : Mat k r) : rconv μ e (fun g => cc • A g) x = cc • rconv μ e A x := by
  unfold rconv
  simp_rw [smul_comm (e _) cc]
  exact integral_smul cc _

lemma integrable_smul_fun (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) (e : Mat k r → ℂ) (A : Mat k r → Vp) (cc : ℂ)
    (x : Mat k r) (h : Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => e (Matrix.of g) • A (x * Matrix.of g)) μ) :
    Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => e (Matrix.of g) • (fun y => cc • A y) (x * Matrix.of g)) μ := by
  simp_rw [smul_comm (e _) cc]
  exact h.smul cc

lemma l2SG_const_smul (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : Mat k r → Vp) (cc : ℂ) :
    l2SG ν (fun g => cc • A g) = (‖cc‖₊ : ℝ≥0∞) ^ 2 * l2SG ν A := by
  unfold l2SG
  rw [← lintegral_const_mul' _ _ (by simp)]
  congr 1
  funext x
  rw [nnnorm_smul, ENNReal.coe_mul, mul_pow]

lemma l2SG_Wf_eq_one (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : Mat k r → Vp) (h0 : l2SG ν A ≠ 0)
    (h1 : l2SG ν A < ⊤) : l2SG ν (Wf ν A) = 1 := by
  have hW : Wf ν A = fun g => (((Real.sqrt (l2SG ν A).toReal)⁻¹ : ℝ) : ℂ) • A g := by
    funext g; unfold Wf; congr 1; push_cast; rfl
  rw [hW, l2SG_const_smul]
  set t := (l2SG ν A).toReal with ht_def
  have ht : 0 < t := ENNReal.toReal_pos h0 h1.ne
  have hA : l2SG ν A = ENNReal.ofReal t := (ENNReal.ofReal_toReal h1.ne).symm
  have hn : (‖(((Real.sqrt t)⁻¹ : ℝ) : ℂ)‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal t⁻¹ := by
    rw [ENNReal.ofReal, ← ENNReal.coe_pow]
    congr 1
    apply NNReal.coe_injective
    rw [NNReal.coe_pow, coe_nnnorm, Real.coe_toNNReal _ (inv_nonneg.mpr ht.le), Complex.norm_real,
      Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt ht.le]
  rw [hn, hA, ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le), inv_mul_cancel₀ ht.ne', ENNReal.ofReal_one]

lemma lint_smul (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : Mat k r → Vp) (cc : ℂ) (f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
    (h : ∫⁻ x, ‖A (Matrix.of x)‖ₑ * f x ∂ν < ⊤) :
    ∫⁻ x, ‖(fun g => cc • A g) (Matrix.of x)‖ₑ * f x ∂ν < ⊤ := by
  simp_rw [enorm_smul, mul_assoc]
  rw [lintegral_const_mul' _ _ enorm_ne_top]
  exact ENNReal.mul_lt_top enorm_lt_top h

end Scale

def WlocShape : Prop :=
  BesselNVGap → CoefWeightedLoc → ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ)
    (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μG μS ν : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r),
    IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS →
    IsQuotMeas μG μS ν →
  ∃ W : Mat k r → Vp, (ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) ∧ IsSPsiEquiv z (psiGen k r z c) π W ∧
    (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      MeasureTheory.Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W x = W x) ∧
    ∫⁻ x, ‖W (Matrix.of x)‖ₑ ∂ν < ⊤ ∧ l2SG ν W = 1 ∧
    ∫⁻ x, ‖W (Matrix.of x)‖ₑ * ENNReal.ofReal (nuH k r z (Matrix.of x) ^ N1H k r) ∂ν < ⊤ ∧
    ∃ (α : Mat k r → ℂ) (Ω : Set (Mat k r)) (a : ℝ), IsCompact Ω ∧ (1 : Mat k r) ∈ Ω ∧
      Ω ⊆ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
      Measurable (fun g : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of g)) ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
        MeasureTheory.Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of g) • W (x * Matrix.of g)) μG ∧
        rconv μG α W x = W x) ∧
  ∃ (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (cc : ℂ) (x₀ : Mat k r) (ξ : Vp),
    IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW ∧ IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN ∧
    x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
    ∀ x, W x = cc • B0 z c σ π μW μN (σ x₀ w) ξ (σ x w)

theorem scWlocShape_of (hWN : HaarWN) (hEq : AEquiv) (hC : ACont) (hK : AKind) (hRp : AReprod)
    (hL : WavePacketL1L2) (hWt : AWeighted) (hNz : ANonzero) (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) :
    WlocShape := by
  intro hBNV hCW k r z c u v b hS H _ _ _ σ hσ Vp _ _ _ π hπ w hw μG μS ν hG hSμ hQ
  obtain ⟨μW, μN, hW, hN, hWf, hNc⟩ := hWN k r z hS.2.2.1 hS.2.2.2.1
  have hyp : Hyp k r z c u v b σ π w μG μS ν μW μN :=
    ⟨hS, hσ, hπ, hw, hG, hSμ, hQ, hW, hN, hWf, hNc⟩
  obtain ⟨x₀, hx₀, ξ, hne⟩ := hNz hBNV k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW
  have hL' := hL k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
  set A := Af z c σ π μW μN w x₀ ξ with hA_def
  set cc : ℂ := (((Real.sqrt (l2SG ν A).toReal)⁻¹ : ℝ) : ℂ) with hcc
  have hW' : Wf ν A = fun g => cc • A g := by
    funext g; unfold Wf; congr 1; rw [hcc]; push_cast; rfl
  refine ⟨Wf ν A, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, μW, μN, cc, x₀, ξ, hW, hN, hx₀, fun x => by rw [hW']; rfl⟩
  · rw [hW']
    exact (hC k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ).const_smul cc
  · intro h hh m hm g hg
    rw [hW']
    have := hEq k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ h hh m hm g hg
    change cc • Af z c σ π μW μN w x₀ ξ (h * m * g) =
      psiGen k r z c m • (π h) (cc • Af z c σ π μW μN w x₀ ξ g)
    rw [this, smul_comm cc (psiGen k r z c m), map_smul]
  · intro x hx
    obtain ⟨hi, he⟩ := hK k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ x hx
    rw [hW']
    exact ⟨integrable_smul_fun μG _ A cc x hi, by rw [rconv_smul, he]⟩
  · rw [hW']
    have := lint_smul ν A cc (fun _ => 1) (by simpa using hL'.1)
    simpa using this
  · exact l2SG_Wf_eq_one ν A hne hL'.2
  · rw [hW']
    exact lint_smul ν A cc _ (hWt k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ)
  · obtain ⟨α, Ω, a, hΩ, h1, hΩG, hαm, hα0, hαa, hα⟩ :=
      hRp k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
    refine ⟨α, Ω, a, hΩ, h1, hΩG, hαm, hα0, hαa, fun x hx => ?_⟩
    obtain ⟨hi, he⟩ := hα x hx
    rw [hW']
    exact ⟨integrable_smul_fun μG _ A cc x hi, by rw [rconv_smul, he]⟩

theorem scWlocExists_of (hWN : HaarWN) (hEq : AEquiv) (hC : ACont) (hK : AKind) (hRp : AReprod)
    (hL : WavePacketL1L2) (hWt : AWeighted) (hNz : ANonzero) (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) :
    WlocExists := by
  intro hBNV hCW k r z c u v b hS H _ _ _ σ hσ Vp _ _ _ π hπ w hw μG μS ν hG hSμ hQ
  obtain ⟨W, hWc, _⟩ := scWlocShape_of hWN hEq hC hK hRp hL hWt hNz hR hBNV hCW k r z c u v b hS H σ hσ
    Vp π hπ w hw μG μS ν hG hSμ hQ
  exact ⟨W, hWc⟩

end WlocSk
end
end

section

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Matrix
open scoped InnerProductSpace

namespace WlocSk

section Cayley

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

lemma cay_inv_mul {P : Mat k r} (hP : IsUnit P) : P⁻¹ * P = 1 :=
  Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).mp hP)

lemma cay_mul_inv {P : Mat k r} (hP : IsUnit P) : P * P⁻¹ = 1 :=
  Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP)

lemma cay_mem {P : Mat k r} (hP : IsCayley k r ε P) {g : Mat k r} (hg : g ∈ Gr k r) :
    P * g * P⁻¹ ∈ UJset ε := by
  have h2 := cay_mul_inv hP.1
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  rw [← hP.2] at hg'
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ := by rw [hg']
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h2]; simp

lemma cay_back {P : Mat k r} (hP : IsUnit P) (g : Mat k r) : P⁻¹ * (P * g * P⁻¹) * P = g := by
  have h1 := cay_inv_mul hP
  have h2 := cay_mul_inv hP
  calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

end Cayley

theorem sigma_decomposition : SigmaG := by
  intro k r ε lam H _ _ σ hσ
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨⟨h1, hmul⟩, hiso, hcont⟩ := hDS.2.2.1
  have hPu := hP.1.1
  have hσ' : ∀ g, σ g = σ (P⁻¹ * (P * g * P⁻¹) * P) := fun g => by rw [cay_back hPu]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have := h1
    simp only [Matrix.mul_one, cay_inv_mul hPu] at this
    exact this
  · intro a ha b hb
    have hab : P * (a * b) * P⁻¹ = P * a * P⁻¹ * (P * b * P⁻¹) := by
      calc P * (a * b) * P⁻¹ = P * a * (P⁻¹ * P) * b * P⁻¹ := by
            rw [cay_inv_mul hPu]; simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = P * a * P⁻¹ * (P * b * P⁻¹) := by simp only [Matrix.mul_assoc]
    rw [hσ' (a * b), hab]
    have := hmul _ (cay_mem hP.1 ha) _ (cay_mem hP.1 hb)
    simp only at this
    rw [this, cay_back hPu, cay_back hPu]
  · intro g hg v
    rw [hσ' g]
    exact hiso _ (cay_mem hP.1 hg) v
  · intro v
    have hc : Continuous fun g : Mat k r => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := (hcont v).comp hc.continuousOn (fun g hg => cay_mem hP.1 hg)
    refine this.congr (fun g _ => ?_)
    simp only [Function.comp]
    rw [cay_back hPu]

end WlocSk
end
end
