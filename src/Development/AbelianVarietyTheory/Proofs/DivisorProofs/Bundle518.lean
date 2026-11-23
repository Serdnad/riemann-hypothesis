module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle486
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBoxBoundedValuation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle404
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle473
import Formalism.DoubleCosetMeasures.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyEqZeroOfSimplicialRowExact
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
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.Fin4
noncomputable section

def pw (t : ℂ) : ℝ := (1 + ‖t‖ ^ 2) ^ (-(4 / 3 : ℝ))

theorem lintegral_pw_lt_top : ∫⁻ t : ℂ, ENNReal.ofReal (pw t) < ⊤ := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 8 / 3)
    (by rw [Complex.finrank_real_complex]; norm_num)
  convert h.lintegral_lt_top using 4
  simp only [pw]; norm_num

theorem gB_eq (w : Low 4 → ℂ) (p0 : ℕ) : gB p0 w =
    (colGram (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 1 ^ 2 * colGram (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 2 ^ 2)⁻¹ := by
  let M : Matrix (Fin 3) (Fin 3) ℂ := blkW p0 w
  show ∏ k : Fin 3, colGram M k.castSucc ^ (-2:ℤ) = (colGram M 1 ^ 2 * colGram M 2 ^ 2)⁻¹
  rw [Fin.prod_univ_three]
  have h0 : colGram M (Fin.castSucc 0) = 1 := by simp [colGram, lminor]
  rw [h0]
  simp only [one_zpow, one_mul, zpow_neg, mul_inv, inv_one]
  rfl

theorem pw_nonneg (t : ℂ) : 0 ≤ pw t := by unfold pw; positivity

theorem measurable_pw : Measurable fun t : ℂ => ENNReal.ofReal (pw t) := by
  unfold pw; fun_prop

theorem blkW_diag (w : Low 4 → ℂ) (p0 : ℕ) : ∀ i, (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) i i = 1 := by
  intro i; fin_cases i <;> simp [blkW, lowMat]

theorem blkW_upper (w : Low 4 → ℂ) (p0 : ℕ) :
    ∀ i j : Fin 3, i < j → (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) i j = 0 := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [blkW, lowMat]

theorem gB_eq_entries (p0 : ℕ) (pa pb pc : Low 4) (w : Low 4 → ℂ)
    (ha : (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 1 0 = w pa)
    (hb : (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 2 0 = w pb)
    (hc : (blkW (r := 4) p0 w : Matrix (Fin 3) (Fin 3) ℂ) 2 1 = w pc) :
    gB p0 w = ((1 + ‖w pa‖ ^ 2 + ‖w pb‖ ^ 2) ^ 2 *
      (1 + ‖w pc‖ ^ 2 + ‖w pa * w pc - w pb‖ ^ 2) ^ 2)⁻¹ := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.columnGramDeterminant_unitLower_three (blkW (r := 4) p0 w) (blkW_diag w p0) (blkW_upper w p0)
  rw [gB_eq, h1, h2, ha, hb, hc]

theorem lintegral_hB_lt_top_of_pos (p0 : ℕ) (pa pb pc : Low 4) (hab : pa ≠ pb) (hcb : pc ≠ pb)
    (hac : pa ≠ pc)
    (hg : ∀ w : Low 4 → ℂ, gB p0 w = ((1 + ‖w pa‖ ^ 2 + ‖w pb‖ ^ 2) ^ 2 *
      (1 + ‖w pc‖ ^ 2 + ‖w pa * w pc - w pb‖ ^ 2) ^ 2)⁻¹)
    (hmix : ∀ p : Low 4, p ≠ pa → p ≠ pb → p ≠ pc → (p.1.2 : ℕ) < p0 ∧ p0 ≤ (p.1.1 : ℕ)) :
    ∫⁻ w : Low 4 → ℂ, hB p0 w < ⊤ := by
  set S : Finset (Low 4) := {pa, pb, pc} with hS
  let f : Low 4 → ℂ → ℝ≥0∞ := fun p x =>
    if p ∈ S then ENNReal.ofReal (pw x) else (Metric.closedBall (0 : ℂ) 1).indicator 1 x
  have hf : ∀ p, Measurable (f p) := by
    intro p; by_cases hp : p ∈ S
    · simp only [f, hp, if_true]; exact measurable_pw
    · simp only [f, hp, if_false]; exact measurable_one.indicator measurableSet_closedBall
  let U : (Low 4 → ℂ) → ℝ≥0∞ := fun w => ∏ p, f p (w p)
  have hU : Measurable U := Finset.measurable_prod _ fun p _ => (hf p).comp (measurable_pi_apply p)
  have hUfin : ∫⁻ w, U w < ⊤ := by
    have := GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (μ := fun _ : Low 4 => (volume : Measure ℂ))
      (fun p => (hf p).aemeasurable)
    rw [volume_pi, this]
    refine ENNReal.prod_lt_top fun p _ => ?_
    by_cases hp : p ∈ S
    · simp only [f, hp, if_true]; exact lintegral_pw_lt_top
    · simp only [f, hp, if_false]
      rw [lintegral_indicator measurableSet_closedBall]
      simpa using (measure_closedBall_lt_top (μ := (volume : Measure ℂ)) (x := 0) (r := 1))
  have hUeq : ∀ w : Low 4 → ℂ, (∀ p, p ∉ S → ‖w p‖ ≤ 1) →
      U w = ENNReal.ofReal (pw (w pa)) * ENNReal.ofReal (pw (w pb)) * ENNReal.ofReal (pw (w pc)) := by
    intro w hw
    simp only [U, f]
    rw [Finset.prod_ite, Finset.prod_eq_one (s := Finset.univ.filter (fun p => p ∉ S)) ?_, mul_one]
    · rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hS, Finset.prod_insert, Finset.prod_insert,
        Finset.prod_singleton, mul_assoc]
      · simpa using hcb.symm
      · simp [hab, hac]
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [Set.indicator, hw p hp]
  have hpt : ∀ w, hB p0 w ≤ U w + U (Function.update w pb (w pb - w pa * w pc)) := by
    intro w
    by_cases hw : w ∈ {w : Low 4 → ℂ | ∀ p : Low 4, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
    · have hw' : ∀ p, p ∉ S → ‖w p‖ ≤ 1 := fun p hp => by
        have h1 : p ≠ pa := fun h => hp (by simp [hS, h])
        have h2 : p ≠ pb := fun h => hp (by simp [hS, h])
        have h3 : p ≠ pc := fun h => hp (by simp [hS, h])
        obtain ⟨k1, k2⟩ := hmix p h1 h2 h3
        exact hw p k1 k2
      have hw'' : ∀ p, p ∉ S → ‖Function.update w pb (w pb - w pa * w pc) p‖ ≤ 1 := fun p hp => by
        have : p ≠ pb := fun h => hp (by simp [hS, h])
        rw [Function.update_of_ne this]; exact hw' p hp
      rw [hUeq w hw', hUeq _ hw'']
      simp only [Function.update_self, Function.update_of_ne hab, Function.update_of_ne hcb]
      have n1 := pw_nonneg (w pa)
      have n2 := pw_nonneg (w pb)
      have n3 := pw_nonneg (w pc)
      have n4 := pw_nonneg (w pb - w pa * w pc)
      unfold hB
      rw [Set.indicator_of_mem hw, ← ENNReal.ofReal_mul n1, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul n1, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [hg w]
      have key := GlobalTheory.T.flagGram_density_inequality_complex (w pa) (w pb) (w pc)
      have e : pw (w pb - w pa * w pc) = (1 + ‖w pa * w pc - w pb‖ ^ 2) ^ (-(4 / 3 : ℝ)) := by
        simp only [pw, norm_sub_rev (w pb)]
      rw [e]
      simp only [pw]
      calc _ ≤ _ := key
        _ = _ := by ring
    · unfold hB; rw [Set.indicator_of_notMem hw]; exact zero_le'
  have hgm : Measurable fun w : Low 4 → ℂ => w pa * w pc :=
    (measurable_pi_apply pa).mul (measurable_pi_apply pc)
  have hgi : ∀ w v : Low 4 → ℂ, (∀ j, j ≠ pb → w j = v j) → w pa * w pc = v pa * v pc := by
    intro w v h; rw [h pa hab, h pc hcb]
  calc ∫⁻ w, hB p0 w ≤ ∫⁻ w, (U w + U (Function.update w pb (w pb - w pa * w pc))) :=
        lintegral_mono hpt
    _ = (∫⁻ w, U w) + ∫⁻ w, U (Function.update w pb (w pb - w pa * w pc)) :=
        lintegral_add_left hU _
    _ = (∫⁻ w, U w) + ∫⁻ w, U w := by
        rw [GlobalTheory.T.lintegral_update_sub_shear' pb (fun w => w pa * w pc) hgm hgi U hU]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hUfin, hUfin⟩

theorem lintegral_hB_four_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 3) → ∫⁻ w : Low 4 → ℂ, hB p0 w < ⊤ := by
  rintro p0 (rfl | rfl)
  · exact lintegral_hB_lt_top_of_pos 1 ⟨(2, 1), by decide⟩ ⟨(3, 1), by decide⟩ ⟨(3, 2), by decide⟩
      (by decide) (by decide) (by decide) (fun w => gB_eq_entries 1 _ _ _ w rfl rfl rfl) (by decide)
  · exact lintegral_hB_lt_top_of_pos 3 ⟨(1, 0), by decide⟩ ⟨(2, 0), by decide⟩ ⟨(2, 1), by decide⟩
      (by decide) (by decide) (by decide) (fun w => gB_eq_entries 3 _ _ _ w rfl rfl rfl) (by decide)
end
end GlobalTheory.IntBall.Fin4
end

section

open MeasureTheory Matrix ValuativeRel

namespace GlobalTheory.HeisUnit

theorem normSq_unif_mul_resCard_pow_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ},
    ∀ (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ)),
    Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _) →
    ∀ (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (g.valᵀ * Y)) →
    ∀ φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), ι φ0 = GlobalTheory.HeisUnit.intInd k n d → φ0 ≠ 0 →
    ∀ (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i0 : Fin n),
    (∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ T T' : Fin d → GlobalTheory.SplitFlip.Res k 1, T ≠ T' →
      ∫ y, Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (GlobalTheory.HeisUnit.cosetRep ϖ i0 T') φ0 y) ∂μ = 0) →
    ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 := by
  intro k _ _ _ _ n d ι hinj Tr hTr hTrIso S hS hSiso χ hχ φ0 hφ0 hι0 hne ϖ hϖ i0 horth
  classical
  set F := ∑ T : Fin d → SplitFlip.Res k 1, Tr (cosetRep ϖ i0 T) φ0 with hF
  have hFSB : F ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k) := Submodule.sum_mem _ fun T _ => (hTr _ φ0 hφ0).1
  have hSg : S (diagAt ϖ i0) φ0 = (χ ϖ : ℂ) • F := by
    apply hinj (hS _ φ0 hφ0) (Submodule.smul_mem _ _ hFSB)

    rw [hχ _ φ0 hφ0, map_smul, map_sum, det_diagAt, hι0]
    funext Y
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, (hTr _ φ0 hφ0).2, hι0]
    rw [intInd_diagAt_eq_sum ϖ hϖ]

  letI : MeasurableSpace (Fin n × Fin d → k) := borel _
  haveI : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → k) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  have hiso := hSiso (diagAt ϖ i0) φ0 hφ0 μ hμ
  rw [hSg] at hiso
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow] at hiso
  rw [lintegral_const_mul' _ _ (by simp [enorm_eq_nnnorm])] at hiso
  obtain ⟨hFtop, hFint, -, hFi⟩ := GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ F hFSB
  obtain ⟨h0top, h0int, h0ne, -⟩ := GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ φ0 hφ0
  have hN0 : (∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0ne hne, h0top⟩
  have hint : ∀ T T' : Fin d → SplitFlip.Res k 1, Integrable (fun y => Tr (cosetRep ϖ i0 T) φ0 y *
      (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y)) μ := fun T T' =>
    (GlobalTheory.T.schwartzBruhat_lintegral_sq_ne_top μ hμ _ (hTr _ φ0 hφ0).1).2.2.2 _ (hTr _ φ0 hφ0).1
  have hsum : ∫ y, F y * (starRingEnd ℂ) (F y) ∂μ =
      (Fintype.card (Fin d → SplitFlip.Res k 1) : ℂ) * ∫ y, φ0 y * (starRingEnd ℂ) (φ0 y) ∂μ := by
    have hpt : ∀ y, F y * (starRingEnd ℂ) (F y) = ∑ T : Fin d → SplitFlip.Res k 1, ∑ T' : Fin d → SplitFlip.Res k 1,
        Tr (cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y) := by
      intro y

      rw [hF, Finset.sum_apply, map_sum, Finset.sum_mul_sum]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun T _ => integrable_finsetSum _ fun T' _ => hint T T']
    simp_rw [integral_finsetSum _ fun T' _ => hint _ T']
    rw [Finset.card_univ.symm, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.sum_eq_single T (fun T' _ hT' => horth μ hμ T T' (Ne.symm hT')) (fun h => absurd (Finset.mem_univ _) h)]
    exact hTrIso μ hμ _ φ0 hφ0 φ0 hφ0
  rw [hFint, h0int] at hsum
  have hLF : (∫⁻ y, ‖F y‖ₑ ^ 2 ∂μ).toReal =
      (Fintype.card (Fin d → SplitFlip.Res k 1) : ℝ) * (∫⁻ y, ‖φ0 y‖ₑ ^ 2 ∂μ).toReal := by
    exact_mod_cast hsum
  have hiso' := congrArg ENNReal.toReal hiso
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm, hLF] at hiso'
  have hcard : (Fintype.card (Fin d → SplitFlip.Res k 1) : ℝ) = (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_eq_nat_card]
    have : Nat.card (SplitFlip.Res k 1) = GlobalTheory.SplitWeil.resCard k :=
      Nat.card_congr (Ideal.quotEquivOfEq (pow_one 𝓂[k])).toEquiv
    rw [this]; push_cast; ring
  rw [hcard] at hiso'
  apply mul_right_cancel₀ hN0
  linear_combination hiso'

end GlobalTheory.HeisUnit
end

section

open GlobalTheory.WeilM Matrix

theorem _root_.GlobalTheory.T.schwartzBruhat_reindex_rows : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A A' D : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (ν : kˣ →* ℂˣ) (e : A ≃ A'), (∀ f ∈ SB (Matrix A' D k), (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ SB (Matrix A D k)) ∧ (∀ f ∈ GlobalTheory.RankStrata.Nsp k A' D ν, (fun Y : Matrix A D k => f (Y.submatrix e.symm id)) ∈ GlobalTheory.RankStrata.Nsp k A D ν) := by
  first | exact @GlobalTheory.RankStrata.rowRenum_SB_Nsp | exact GlobalTheory.RankStrata.rowRenum_SB_Nsp | (intros; apply GlobalTheory.RankStrata.rowRenum_SB_Nsp <;> assumption)
end

section

open ValuativeRel Matrix


theorem _root_.GlobalTheory.T.integral_box_bounded_valuation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (Function.update (fun _ => m) i₀ (m - 1)) - ∑ b : Fin r → GlobalTheory.SplitFlip.Res k 1, GlobalTheory.RankCoinv.boxFn ϖ (Matrix.updateRow C i₀ ((fun l => (ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ᵥ* (H * C))) (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) := by
  first | exact @GlobalTheory.CountTranslates.boxFn_sub_sum_mem_lowRank | exact GlobalTheory.CountTranslates.boxFn_sub_sum_mem_lowRank | (intros; apply GlobalTheory.CountTranslates.boxFn_sub_sum_mem_lowRank <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem _root_.GlobalTheory.T.smooth_character_orbital_integral_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ (S : Set (Matrix (Fin n) (Fin d) k)),
    (∀ (E : GL (Fin n) k), ∀ Y ∈ S, E.val * Y ∈ S → E ∈ GlobalTheory.SplitWeil.KO k (Fin n)) →
    (∀ E ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ Y ∈ S, E.val * Y ∈ S) →
    ∀ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Y ∉ S → Φ Y = 0) →
    (∀ Y ∈ S, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y = 0) → Φ ∈ GlobalTheory.FullRankCoinv.augRk n d ν := by
  first | exact @GlobalTheory.FullRankCoinv.Average.mem_augRk_of_smallF_eq_zero | exact GlobalTheory.FullRankCoinv.Average.mem_augRk_of_smallF_eq_zero | (intros; apply GlobalTheory.FullRankCoinv.Average.mem_augRk_of_smallF_eq_zero <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix

theorem _root_.GlobalTheory.T.integrable_full_rank_zeta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    ∀ Y : Matrix (Fin n) (Fin d) k, Integrable (fun g : GL (Fin n) k =>
      Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) := by
  first | exact @GlobalTheory.FullRankCoinv.integrable_fibre_target | exact GlobalTheory.FullRankCoinv.integrable_fibre_target | (intros; apply GlobalTheory.FullRankCoinv.integrable_fibre_target <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem _root_.GlobalTheory.T.full_rank_normal_form_orbit : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ), n ≤ d →
    ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n → ∃ h : GL (Fin d) k, Y = GlobalTheory.FullRankCoinv.Y0 k n d * h.val := by
  first | exact @GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq | exact GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq | (intros; apply GlobalTheory.FullRankCoinv.exists_eq_normal_form_mul_of_rank_eq <;> assumption)
end

section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

theorem _root_.GlobalTheory.T.open_cover_finite_translates_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (S : Set (Matrix (Fin n) (Fin d) k)), IsOpen S →
    (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank = n → ∃ E : GL (Fin n) k, E.val * Y ∈ S) →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∃ s : Finset (GL (Fin n) k), ∀ Y, Ψ Y ≠ 0 → ∃ E ∈ s, E.val * Y ∈ S := by
  first | exact @GlobalTheory.FullRankCoinv.fullRk_support_finite_cover | exact GlobalTheory.FullRankCoinv.fullRk_support_finite_cover | (intros; apply GlobalTheory.FullRankCoinv.fullRk_support_finite_cover <;> assumption)
end

section

noncomputable section

open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.Reduce

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lact_mem {n d : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) {Ψ : Matrix (Fin n) (Fin d) k → ℂ}
    (hΨ : Ψ ∈ fullRk k n d) : lact ν g Ψ ∈ fullRk k n d := by
  have hmem : (fun Y => Ψ ((g.1)ᵀ * Y)) ∈ fullRk k n d := by
    let e : Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k :=
      { toFun := fun X => (g.1)ᵀ * X
        invFun := fun X => ((g⁻¹).1)ᵀ * X
        left_inv := fun X => by
          simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one,
            Matrix.one_mul]
        right_inv := fun X => by
          simp only [← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
            Matrix.one_mul]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    refine ⟨⟨hΨ.1.1.comp_continuous e.continuous, hΨ.1.2.comp_homeomorph e⟩, fun Y hY => hΨ.2 _ ?_⟩
    rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _
      (by rw [Matrix.det_transpose]; exact Matrix.isUnits_det_units g)]
  exact (fullRk k n d).smul_mem ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) hmem

theorem indicator_mem {n d : ℕ} {T : Set (Matrix (Fin n) (Fin d) k)} (hT : IsClopen T)
    {Ψ : Matrix (Fin n) (Fin d) k → ℂ} (hΨ : Ψ ∈ fullRk k n d) : T.indicator Ψ ∈ fullRk k n d := by
  refine ⟨⟨?_, ?_⟩, fun Y hY => ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ T
    · filter_upwards [hT.isOpen.mem_nhds hx, hΨ.1.1.eventually_eq x] with y hy h
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy, h]
    · filter_upwards [hT.compl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]
  · refine HasCompactSupport.mono hΨ.1.2 fun y hy h => hy ?_
    by_cases hy' : y ∈ T
    · rw [Set.indicator_of_mem hy', h]
    · exact Set.indicator_of_notMem hy' _
  · by_cases hy' : Y ∈ T
    · rw [Set.indicator_of_mem hy', hΨ.2 Y hY]
    · exact Set.indicator_of_notMem hy' _

end

theorem reduce_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ) (S : Set (Matrix (Fin n) (Fin d) k)), IsClopen S →
    (∀ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ Y : Matrix (Fin n) (Fin d) k, Integrable (fun g : GL (Fin n) k =>
      Φ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))
      (haarVol (GlobalTheory.SplitWeil.KO k (Fin n)))) →
    ∀ (s : Finset (GL (Fin n) k)), ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    (∀ Y, Ψ Y ≠ 0 → ∃ E ∈ s, E.val * Y ∈ S) →
    ∃ Φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, (∀ Y, Y ∉ S → Φ Y = 0) ∧ Ψ - Φ ∈ GlobalTheory.FullRankCoinv.augRk n d ν ∧
      ∀ Y, smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y = smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y := by
  intro k _ _ _ _ _ _ n d ν S hS hint s
  classical
  have hadd : ∀ Ψ ∈ fullRk k n d, ∀ Φ ∈ fullRk k n d, ∀ Y,
      smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν (Ψ + Φ) Y =
        smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Ψ Y + smallF (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) ν Φ Y := by
    intro Ψ hΨ Φ hΦ Y
    simp only [smallF, Pi.add_apply]
    rw [← integral_add (hint Ψ hΨ Y) (hint Φ hΦ Y)]
    congr 1; funext g; ring
  induction s using Finset.induction_on with
  | empty =>
    intro Ψ hΨ h
    refine ⟨Ψ, hΨ, fun Y _ => ?_, by simp, fun _ => rfl⟩
    by_contra h0
    simpa using h Y h0
  | insert E s _ ih =>
    intro Ψ hΨ h
    set T : Set (Matrix (Fin n) (Fin d) k) := (fun Y => E.val * Y) ⁻¹' S with hTdef
    have hT : IsClopen T := hS.preimage (by fun_prop)
    have h1 := indicator_mem hT hΨ
    have h2 := indicator_mem hT.compl hΨ
    have hsum : T.indicator Ψ + Tᶜ.indicator Ψ = Ψ := Set.indicator_self_add_compl T Ψ
    obtain ⟨Φ₂, hΦ₂, hS₂, ha₂, hF₂⟩ := ih _ h2 fun Y hY => by
      have hYT : Y ∈ Tᶜ := by
        by_contra hc
        exact hY (Set.indicator_of_notMem hc _)
      rw [Set.indicator_of_mem hYT] at hY
      obtain ⟨E', hE', hS'⟩ := h Y hY
      rcases Finset.mem_insert.1 hE' with rfl | hE'
      · exact absurd hS' hYT
      · exact ⟨E', hE', hS'⟩
    have hΦ₁ := lact_mem ν (invT E) h1
    refine ⟨lact ν (invT E) (T.indicator Ψ) + Φ₂, add_mem hΦ₁ hΦ₂, fun Y hY => ?_, ?_, fun Y => ?_⟩
    · have hn : (invT E).1ᵀ * Y ∉ T := by
        intro hc
        apply hY
        have hc' : E.val * ((invT E).1ᵀ * Y) ∈ S := hc
        rwa [invT_val, Matrix.transpose_transpose, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at hc'
      simp only [Pi.add_apply, hS₂ Y hY, lact, Set.indicator_of_notMem hn, mul_zero, add_zero]
    · have ha₁ : lact ν (invT E) (T.indicator Ψ) - T.indicator Ψ ∈ augRk n d ν :=
        Submodule.subset_span ⟨_, _, h1, rfl⟩
      have : Ψ - (lact ν (invT E) (T.indicator Ψ) + Φ₂) =
          (Tᶜ.indicator Ψ - Φ₂) - (lact ν (invT E) (T.indicator Ψ) - T.indicator Ψ) := by
        linear_combination -hsum
      rw [this]
      exact sub_mem ha₂ ha₁
    · rw [hadd _ hΦ₁ _ hΦ₂, UnitMinor.smallF_lact, hF₂, ← hadd _ h1 _ h2, hsum]

end GlobalTheory.FullRankCoinv.Reduce
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_factor_through_extendScalars_zmod : ∀ (Q q : ℕ) (hq : q ∣ Q) (I : Cx (ZMod Q)) (K : Cx (ZMod q)) (ρ : SemiMap I K), ∃ u : extCx (ZMod.castHom hq (ZMod q)) I ⟶ K, ∀ (U : Scheme.{0}) (s : ℤ) (a : Sec (I.X s) U), ρ.app U s a = Sec.map (u.f s) ((extπ (ZMod.castHom hq (ZMod q)) I).app U s a) := by
  first | exact @GlobalTheory.EtC.SemiMap.factor_extCx | exact GlobalTheory.EtC.SemiMap.factor_extCx | (intros; apply GlobalTheory.EtC.SemiMap.factor_extCx <;> assumption)
end

section

open GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.laurent_pi_bijective : ∀ (n : ℕ) (B : Fin n → Type) [∀ j, CommRing (B j)], Function.Bijective (Pi.ringHom (fun j => laurentMap (Pi.evalRingHom B j)) : LaurentPolynomial (∀ j, B j) →+* ∀ j, LaurentPolynomial (B j)) := by
  first | (exact @GlobalTheory.EtC.GmStep.laurentPi_bijective) | (exact GlobalTheory.EtC.GmStep.laurentPi_bijective) | (intros; apply GlobalTheory.EtC.GmStep.laurentPi_bijective  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

theorem _root_.GlobalTheory.T.etaleSpaceCohomology_eq_zero_of_simplicialRowExact : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (P : PSh) (g : disc.obj P ⟶ E), IsIso (g.app (op ⦋0⦌)) →
  ∀ (n : ℕ) (x : H R E F n), pull R g F n x = 0 →
  (∀ p : ℕ, p + 1 ≤ n → RowExact R E F ((n : ℤ) - ((p + 1 : ℕ) : ℤ)) p) → x = 0 := by
  first | (exact @GlobalTheory.EtC.vanish_of_rowExact) | (exact GlobalTheory.EtC.vanish_of_rowExact) | (intros; apply GlobalTheory.EtC.vanish_of_rowExact  <;> assumption)
end
