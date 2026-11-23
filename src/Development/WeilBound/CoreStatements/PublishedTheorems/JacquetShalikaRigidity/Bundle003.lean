module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace PKEq2

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem continuous_lastRow : Continuous (lastRow : GA E k → Fin k → Ad E) := by
  unfold lastRow
  refine continuous_pi fun c => continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact Continuous.matrix_elem Units.continuous_val i c
  · exact continuous_const

theorem lastRow_mir (p : GL (Fin k) E) (hp : IsMir (k - 1) p) (g : GA E k) :
    lastRow (ratGL E k p * g) = lastRow g := by
  funext c
  unfold lastRow
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · have hrow : ∀ j, (ratGL E k p).val i j = (1 : Matrix (Fin k) (Fin k) (Ad E)) i j := by
      intro j
      have := hp i j (Or.inl (by omega))
      simp only [ratGL] at *
      simp [this, Matrix.one_apply]
    rw [Units.val_mul, Matrix.mul_apply]
    simp_rw [hrow]
    simp [Matrix.one_apply]
  · rfl

theorem measurable_sumF [Countable (RowT E k k)] {f : GA E k → ℂ} (hf : Continuous f)
    (hfin : ∀ g, {ξ : RowT E k k | f (ratGL E k (gam ξ) * g) ≠ 0}.Finite) : Measurable (sumF f) := by
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (RowT E k k)))
    (f := fun T g => ∑ ξ ∈ T, f (ratGL E k (gam ξ) * g)) (fun T => ?_) ?_
  · exact Finset.measurable_sum _ fun ξ _ => (hf.comp (continuous_const.mul continuous_id)).measurable
  · rw [tendsto_pi_nhds]
    intro g
    have e : ∀ T : Finset (RowT E k k), (hfin g).toFinset ⊆ T →
        ∑ ξ ∈ T, f (ratGL E k (gam ξ) * g) = sumF f g := by
      intro T hT
      unfold sumF
      rw [tsum_eq_sum (s := T)]
      intro b hb
      by_contra h
      exact hb (hT ((hfin g).mem_toFinset.2 h))
    exact tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨_, fun T hT => (e T hT).symm⟩)

theorem fin_bd {X : ℂ} {B C x y : ℝ} (hB : 0 ≤ B) (hx : 0 ≤ x) (hxy : x ≤ y)
    (h : ‖X‖ₑ ≤ ENNReal.ofReal B * ENNReal.ofReal (C * x)) : ‖X‖ ≤ B * max C 0 * y := by
  rw [← ENNReal.ofReal_mul hB, ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff'] at h
  have h0 : C * x ≤ max C 0 * y :=
    calc C * x ≤ max C 0 * x := mul_le_mul_of_nonneg_right (le_max_left _ _) hx
      _ ≤ max C 0 * y := mul_le_mul_of_nonneg_left hxy (le_max_right _ _)
  have h1 : B * (C * x) ≤ B * max C 0 * y := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h0 hB
  have h2 : 0 ≤ B * max C 0 * y := mul_nonneg (mul_nonneg hB (le_max_right _ _)) (hx.trans hxy)
  rcases h with h | h <;> linarith [norm_nonneg X]

theorem enorm_conj' (z : ℂ) : ‖conj z‖ₑ = ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, RCLike.norm_conj]

end PKEq2

open PKEq2 in
theorem kernel_equality_second_of : D0 → N0 → H0 → ThetaDecaying → RowsInCompactSet → PoissonCutoffFormula → KEq2 := by
  intro hD0 hN0 hH0 hG4t hG5t hK12 E _ _ _ k hk ψ hψ S α' φ' hφ' U φ η s hcut hinv hcen
  obtain ⟨hDpos, hDmul, hDcont, hDrat, -, hDinv, -⟩ := hD0 E k
  obtain ⟨-, -, -, -, -, -, hcount, -, hperm, -⟩ := hN0 E k k hk le_rfl
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hinv' : ∀ γ g, φ (ratGL E k γ * g) = φ g := hinv
  have hinv2 : ∀ γ g, φ' (ratGL E k γ * g) = φ' g := hφ'.inv
  have hp1 : ∀ g : GA E k, (Dt g : ℂ) ^ (-(((k : ℂ) - k) / 2)) = 1 := fun g => by simp
  set V : (Fin k → Ad E) → XB E k := fun y => (η y : ℂ) • Rt E k (s y)⁻¹ φ with hV
  set F : GA E k → ℂ := fun g => (η (lastRow g) : ℂ) * φ (g * (s (lastRow g))⁻¹) with hF
  have hVc : Continuous V := hcut.contV
  have hVcpt : HasCompactSupport V := by
    have h1 : HasCompactSupport (fun y => (η y : ℂ)) := hcut.cpt.comp_left (g := Complex.ofReal) (by simp)
    exact h1.smul_right (f' := fun y => Rt E k (s y)⁻¹ φ)
  have hFV : ∀ x, F x = V (lastRow x) x := fun x => by simp [hF, hV]
  have hFc : Continuous F := by
    have : F = fun x => (V (lastRow x), x).1 (V (lastRow x), x).2 := funext hFV
    rw [this]
    exact continuous_eval.comp ((hVc.comp continuous_lastRow).prodMk continuous_id)
  have hFmir : ∀ p, IsMir (k - 1) p → ∀ x, F (ratGL E k p * x) = F x := by
    intro p hp x
    simp only [hF, lastRow_mir p hp, mul_assoc, hinv']
  have hsumInv : ∀ γ g, sumF F (ratGL E k γ * g) = sumF F g := by
    intro γ g
    obtain ⟨e, he⟩ := hperm γ
    unfold sumF
    rw [← e.tsum_eq (fun ξ => F (ratGL E k (gam ξ) * g))]
    refine tsum_congr fun ξ => ?_
    obtain ⟨p, hp, hpe⟩ := he ξ
    rw [← mul_assoc, ← map_mul, hpe, map_mul, mul_assoc, hFmir p hp]
  have hcpt : IsCompact (tsupport η) := hcut.cpt
  have hFzero : ∀ x, lastRow x ∉ tsupport η → F x = 0 := by
    intro x hx
    simp [hF, image_eq_zero_of_notMem_tsupport hx]
  have hfin : ∀ g, {ξ : RowT E k k | F (ratGL E k (gam ξ) * g) ≠ 0}.Finite := by
    intro g
    refine ((hG5t E k hk (tsupport η) hcpt).1 g).subset fun ξ hξ => ?_
    by_contra h
    exact hξ (hFzero _ h)
  have hSmeas : Measurable (sumF F) := measurable_sumF hFc hfin

  have hint : Integrable V (vecMeasure E (Fin k)) := hVc.integrable_of_hasCompactSupport hVcpt
  set W : XB E k := ∫ y, V y ∂vecMeasure E (Fin k) with hW
  have hI : ∀ g, (∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) ∂vecMeasure E (Fin k)) = W g := by
    intro g
    have := ContinuousLinearMap.integral_comp_comm (BoundedContinuousFunction.evalCLM ℂ g) hint
    rw [hW, ← BoundedContinuousFunction.evalCLM_apply (𝕜 := ℂ), ← this]
    simp [hV]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hp1, mul_one]
    exact hSmeas.mul (Complex.continuous_conj.comp φ'.continuous).measurable
  · simp only [hI]
    exact (W.continuous.mul (Complex.continuous_conj.comp φ'.continuous)).measurable
  · intro γ g
    simp only [hp1, mul_one]
    rw [hsumInv γ g, hinv2]
  · intro γ g
    simp only [mul_assoc, hinv', hinv2]
  · intro t g
    simp only [mul_assoc, hcen, hφ'.cen]
  · refine ⟨‖W‖ * ‖φ'‖, fun g => ?_⟩
    rw [hI, norm_mul, RCLike.norm_conj]
    exact mul_le_mul (W.norm_coe_le_norm g) (φ'.norm_coe_le_norm g) (norm_nonneg _) (norm_nonneg _)
  · intro M
    obtain ⟨B, hB⟩ := hVc.bounded_above_of_compact_support hVcpt
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
    obtain ⟨C, hC⟩ := (hG4t E k hk φ' hφ'.dec).2 (tsupport η) hcpt (k * M + k) (by nlinarith)
    refine ⟨B * max C 0, fun g hg => ?_⟩
    have hFbd : ∀ x, ‖F x‖ₑ ≤ ENNReal.ofReal B * (tsupport η).indicator (fun _ => (1 : ℝ≥0∞)) (lastRow x) := by
      intro x
      by_cases hx : lastRow x ∈ tsupport η
      · rw [Set.indicator_of_mem hx, mul_one, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (by rw [hFV]; exact ((V (lastRow x)).norm_coe_le_norm x).trans (hB _))
      · rw [Set.indicator_of_notMem hx, hFzero x hx]; simp
    set θ := ∑' ξ : RowT E k k, (tsupport η).indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) with hθ
    have hS : ‖sumF F g‖ₑ ≤ ENNReal.ofReal B * θ :=
      enorm_tsum_le_tsum_enorm.trans ((ENNReal.tsum_le_tsum fun ξ => hFbd _).trans_eq ENNReal.tsum_mul_left)
    have hx : Dt g ^ (-((k * M + k : ℕ) : ℝ) / k) ≤ (Dt g ^ M)⁻¹ := by
      have e : (-((k * M + k : ℕ) : ℝ) / k) = -(((M + 1 : ℕ) : ℝ)) := by push_cast; field_simp
      rw [e, Real.rpow_neg (hDpos g).le, Real.rpow_natCast]
      exact inv_anti₀ (pow_pos (hDpos g) _) (pow_le_pow_right₀ hg (by omega))
    refine fin_bd hB0 (Real.rpow_nonneg (hDpos g).le _) hx ?_
    simp only [hp1, mul_one]
    rw [enorm_mul, enorm_conj']
    calc ‖sumF F g‖ₑ * ‖φ' g‖ₑ ≤ (ENNReal.ofReal B * θ) * ‖φ' g‖ₑ := by gcongr
      _ = ENNReal.ofReal B * (θ * ‖φ' g‖ₑ) := mul_assoc _ _ _
      _ ≤ _ := by gcongr; exact hC g
  · obtain ⟨Cf, hCf, hft⟩ := hcut.ft
    obtain ⟨M, C, hC⟩ := (hG4t E k hk (fun x => φ' (invT x)) hφ'.dec').1 Cf hCf k le_rfl
    obtain ⟨C', hC'⟩ := hft M
    refine ⟨max C' 0 * max C 0, fun g _ => ?_⟩
    have hJ : ∀ (z : Fin k → Ad E), ‖∫ y, (η y : ℂ) * φ (g * (s y)⁻¹) * ψ (∑ i, y i * z i) ∂vecMeasure E (Fin k)‖ₑ ≤
        ENNReal.ofReal (max C' 0) * ENNReal.ofReal (Cf.indicator (fun _ => ((1 + ‖fun i => pInf E (z i)‖) ^ M)⁻¹)
          fun i => pFin E (z i)) := by
      intro z
      have h := hC' z g
      by_cases hz : (fun i => pFin E (z i)) ∈ Cf
      · rw [Set.indicator_of_mem hz] at h ⊢
        rw [← ENNReal.ofReal_mul (le_max_right _ _), ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
      · rw [Set.indicator_of_notMem hz] at h ⊢
        rw [← ofReal_norm, le_antisymm h (norm_nonneg _)]
        simp
    have hgg : invT (invT g) = g := ((hH0 E k).2.2.2.2.2.2 g g).2
    have hCg := hC (invT g)
    simp only [hgg, hDinv] at hCg
    have e1 : ((Dt g)⁻¹) ^ (-(k : ℝ) / k) = Dt g := by
      rw [neg_div, div_self hk0, Real.rpow_neg_one, inv_inv]
    rw [e1] at hCg
    have hK : (Dt g : ℂ) * sumF F g = _ := hK12 E k hk ψ hψ S U φ η s hcut hinv g
    rw [hp1, mul_one, ← mul_assoc, hK, add_mul, add_sub_cancel_left]
    refine fin_bd (le_max_right _ _) (hDpos g).le le_rfl ?_
    rw [enorm_mul, enorm_conj']
    calc _ ≤ (ENNReal.ofReal (max C' 0) * ∑' ξ : {ξ : Fin k → E // ξ ≠ 0}, ENNReal.ofReal (Cf.indicator
          (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* (invT g).val) i)‖) ^ M)⁻¹)
          fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* (invT g).val) i))) * ‖φ' g‖ₑ := by
          gcongr
          exact enorm_tsum_le_tsum_enorm.trans ((ENNReal.tsum_le_tsum fun ξ => hJ _).trans_eq ENNReal.tsum_mul_left)
      _ = ENNReal.ofReal (max C' 0) * (_ * ‖φ' g‖ₑ) := mul_assoc _ _ _
      _ ≤ _ := by gcongr

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace NormAverageBound

theorem norm_avg_le {G : Type} [AddCommGroup G] [TopologicalSpace G] (Γ : AddSubgroup G) (Φ : G → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (h : ∀ x, ‖Φ x‖ ≤ C) : ‖avg Γ Φ‖ ≤ C := by
  unfold GlobalTheory.CuspGeneric.avg
  split_ifs with hex
  · obtain ⟨-, -, h1⟩ := hex.choose_spec
    have hfin : hex.choose.1 hex.choose.2 < ⊤ := by rw [h1]; exact ENNReal.one_lt_top
    calc ‖∫ x in hex.choose.2, Φ x ∂hex.choose.1‖ ≤ C * hex.choose.1.real hex.choose.2 :=
          norm_setIntegral_le_of_norm_le_const hfin (fun x _ => h x)
      _ = C := by simp [Measure.real, h1]
  · simpa using hC

end NormAverageBound

open NormAverageBound in
theorem fourier_column_of : N0 → P0 → P1 → CornerEmbedding → FourierSeriesColumn := by
  intro hN0 hP0 hP1 hK5e E _ _ _ m k hk hkm ψ hψ ι hι F hF g
  obtain ⟨hFc, hFl, hFlaw, hFvan⟩ := hF
  have hPre : PositivityTheory.AdelicQuotientData.Pre ψ k F := ⟨hFc, hFl, hFlaw⟩
  obtain ⟨hcolPre, hcoef, -, -⟩ := hP1 E m ψ hψ k hk hkm F hPre
  obtain ⟨-, hcolL, -⟩ := hcolPre
  obtain ⟨hgamM, huniqM, -⟩ := hN0 E m k hk hkm.le
  obtain ⟨hgamK, -⟩ := hN0 E k k hk le_rfl
  obtain ⟨hex, hprops⟩ := hK5e E m k hkm.le
  obtain ⟨ιE, hιE⟩ := hex E
  obtain ⟨-, -, -, -, -, -, hrat, -⟩ := hprops ι hι
  have hlift : ∀ ρ : RowT E k k, ∃ ρ' : RowT E m k, ∀ i : Fin m,
      Subtype.val ρ' i = if h : (i : ℕ) < k then Subtype.val ρ ⟨i, h⟩ else 0 := by
    intro ρ
    refine ⟨Subtype.mk (fun i : Fin m => if h : (i : ℕ) < k then Subtype.val ρ ⟨i, h⟩ else 0) ⟨?_, ?_⟩,
      fun i => rfl⟩
    · obtain ⟨c, hc⟩ := Function.ne_iff.1 (Subtype.property ρ).1
      intro h0
      apply hc
      have h1 := congrFun h0 ⟨c, lt_trans c.isLt hkm⟩
      simpa [c.isLt] using h1
    · intro i hi
      simp [show ¬ (i : ℕ) < k by omega]
  choose lift hlift using hlift
  have hA : ∀ ρ : RowT E k k, coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g) =
      colT ψ k F (ι (ratGL E k (gam ρ) * g)) := by
    intro ρ
    rw [hcoef (lift ρ) (ι g), map_mul, hrat ιE hιE]
    have hBlk : PositivityTheory.jumpWindows.GlobalTheory k (ιE (gam ρ)) := by
      intro i c hic
      rw [hιE (gam ρ)]
      simp only [PositivityTheory.AdelicQuotientData.embM, Matrix.of_apply]
      rw [dite_eq_right (by omega)]
    obtain ⟨⟨ξ'', p⟩, ⟨hp, hγ⟩, -⟩ := huniqM _ hBlk
    have hξ : ξ'' = lift ρ := by
      apply Subtype.ext
      funext c
      have hrow := congrArg (fun γ : GL (Fin m) E => (γ : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ c) hγ
      simp only [hιE (gam ρ), Units.val_mul, Matrix.mul_apply] at hrow
      have hpr : ∀ l, (p : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ l =
          (1 : Matrix (Fin m) (Fin m) E) ⟨k - 1, by omega⟩ l := fun l => hp _ _ (Or.inl le_rfl)
      simp only [hpr, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true] at hrow
      rw [(hgamM ξ'').2 ⟨k - 1, by omega⟩ c (by show k - 1 + 1 = k; omega)] at hrow
      rw [← hrow, hlift ρ c]
      simp only [PositivityTheory.AdelicQuotientData.embM, Matrix.of_apply]
      by_cases hc : (c : ℕ) < k
      · rw [dite_eq_left ⟨by show k - 1 < k; omega, hc⟩, dite_eq_left hc]
        exact (hgamK ρ).2 _ _ (by show k - 1 + 1 = k; omega)
      · rw [dite_eq_right (fun h => hc h.2), dite_eq_right hc, Matrix.one_apply, if_neg]
        intro h
        apply hc
        rw [← h]
        show k - 1 < k
        omega
    rw [hγ, map_mul, mul_assoc, hcolL p hp, hξ]
  have hcoef0 : coefF ψ k (0 : UnipotentBlockColumnIndex m k k → E) F (ι g) = 0 := by
    have h0 := hFvan k (by omega) le_rfl (ι g)
    simpa [GlobalTheory.CuspGeneric.coefF, GlobalTheory.CuspGeneric.dot] using h0
  have hinj : Function.Injective
      (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) := by
    intro ρ₁ ρ₂ h
    apply Subtype.ext
    funext j
    have h1 := congrFun h (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m), (⟨k, hkm⟩ : Fin m))
      ⟨j.isLt, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k)
    beta_reduce at h1
    rw [hlift, hlift, dite_eq_left j.isLt, dite_eq_left j.isLt] at h1
    exact h1
  have hkey : ∀ t : UnipotentBlockColumnIndex m k k, t = (Subtype.mk ((⟨((Subtype.val t).1 : ℕ), ((Subtype.val t).1).isLt⟩ : Fin m),
      (⟨k, hkm⟩ : Fin m)) ⟨(Subtype.property t).1, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k) := by
    intro t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      show ((Subtype.val t).2 : ℕ) = k
      have h2 := Subtype.property t
      omega
  have hsurj : ∀ c : UnipotentBlockColumnIndex m k k → E, c ≠ 0 → ∃ ρ : RowT E k k,
      (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) = c := by
    intro c hc
    obtain ⟨ρ, hρ⟩ : ∃ ρ : RowT E k k, ∀ j : Fin k, Subtype.val ρ j =
        c (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m), (⟨k, hkm⟩ : Fin m)) ⟨j.isLt, le_rfl, le_rfl⟩ :
          UnipotentBlockColumnIndex m k k) := by
      refine ⟨Subtype.mk (fun j : Fin k => c (Subtype.mk ((⟨j, lt_trans j.isLt hkm⟩ : Fin m),
        (⟨k, hkm⟩ : Fin m)) ⟨j.isLt, le_rfl, le_rfl⟩ : UnipotentBlockColumnIndex m k k))
        ⟨?_, fun i hi => absurd hi (not_le.2 i.isLt)⟩, fun j => rfl⟩
      intro h0
      apply hc
      funext t
      rw [hkey t]
      exact congrFun h0 ⟨((Subtype.val t).1 : ℕ), (Subtype.property t).1⟩
    refine ⟨ρ, ?_⟩
    funext t
    show Subtype.val (lift ρ) (Subtype.val t).1 = c t
    rw [hlift, dite_eq_left (Subtype.property t).1, hρ]
    exact congrArg c (hkey t).symm
  have hoff : ∀ c : UnipotentBlockColumnIndex m k k → E,
      c ∉ Set.range (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) →
        coefF ψ k c F (ι g) = 0 := by
    intro c hc
    by_cases hc0 : c = 0
    · rw [hc0]; exact hcoef0
    · exact absurd (hsurj c hc0) (fun h => hc h)
  have hper : Per (ratV E (UnipotentBlockColumnIndex m k k)) (fun x => F (blkU x * ι g)) :=
    per_blk hFc (fun c h => hFl _ (isMir_blkU c) h) (ι g)
  obtain ⟨-, hP0b, hP0c⟩ := hP0 E ψ hψ (UnipotentBlockColumnIndex m k k)
  refine ⟨?_, ?_⟩
  · intro B hB
    have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
    have hpar : HasSum (fun c => coefF ψ k c F (ι g) * (starRingEnd ℂ) (coefF ψ k c F (ι g)))
        (avg (ratV E (UnipotentBlockColumnIndex m k k)) fun x => F (blkU x * ι g) * (starRingEnd ℂ) (F (blkU x * ι g))) :=
      hP0b _ _ hper hper
    have hS := (hinj.hasSum_iff (f := fun c => coefF ψ k c F (ι g) * (starRingEnd ℂ) (coefF ψ k c F (ι g)))
      (fun c hc => by simp only [hoff c hc, zero_mul])).2 hpar
    have hSle : ‖avg (ratV E (UnipotentBlockColumnIndex m k k)) fun x => F (blkU x * ι g) * (starRingEnd ℂ) (F (blkU x * ι g))‖ ≤ B ^ 2 :=
      norm_avg_le _ _ _ (sq_nonneg B) (fun x => by
        simpa [norm_mul, sq] using mul_le_mul (hB x) (hB x) (norm_nonneg _) hB0)
    have hre := ((Complex.hasSum_iff _ _).1 hS).1
    simp only [Function.comp_def, Complex.mul_conj, Complex.ofReal_re] at hre
    simp only [Complex.mul_conj] at hSle
    have hterm : ∀ ρ : RowT E k k, ‖colT ψ k F (ι (ratGL E k (gam ρ) * g))‖ₑ ^ 2 =
        ENNReal.ofReal (Complex.normSq (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g))) := by
      intro ρ
      rw [hA ρ, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Complex.normSq_eq_norm_sq]
    calc ∑' ρ : RowT E k k, ‖colT ψ k F (ι (ratGL E k (gam ρ) * g))‖ₑ ^ 2
        = ∑' ρ : RowT E k k, ENNReal.ofReal (Complex.normSq
            (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g))) := tsum_congr hterm
      _ = ENNReal.ofReal (∑' ρ : RowT E k k, Complex.normSq
            (coefF ψ k (fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1) F (ι g))) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ => Complex.normSq_nonneg _) hre.summable).symm
      _ ≤ ENNReal.ofReal (B ^ 2) := by
          rw [hre.tsum_eq]
          exact ENNReal.ofReal_le_ofReal (le_trans (Complex.re_le_norm _) hSle)
  · intro hfin
    have hfin' : {c : UnipotentBlockColumnIndex m k k → E | coefF ψ k c F (ι g) ≠ 0}.Finite := by
      refine (hfin.image (fun ρ : RowT E k k => fun t : UnipotentBlockColumnIndex m k k => Subtype.val (lift ρ) (Subtype.val t).1)).subset ?_
      intro c hc
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hc hcoef0
      obtain ⟨ρ, rfl⟩ := hsurj c hc0
      refine ⟨ρ, ?_, rfl⟩
      show colT ψ k F (ι (ratGL E k (gam ρ) * g)) ≠ 0
      rw [← hA ρ]
      exact hc
    have hs : HasSum (fun c => coefF ψ k c F (ι g)) (F (blkU (0 : UnipotentBlockColumnIndex m k k → GlobalTheory.CuspRep.Ad E) * ι g)) :=
      hP0c _ hper hfin'
    have hb0 : blkU (0 : UnipotentBlockColumnIndex m k k → GlobalTheory.CuspRep.Ad E) = 1 := by
      unfold GlobalTheory.CuspGeneric.blkU
      exact GlobalTheory.CuspGeneric.posU_zero _
    rw [hb0, one_mul] at hs
    have hs2 := (hinj.hasSum_iff (f := fun c => coefF ψ k c F (ι g)) hoff).2 hs
    show ∑' ρ : RowT E k k, colT ψ k F (ι (ratGL E k (gam ρ) * g)) = F (ι g)
    rw [← hs2.tsum_eq]
    exact tsum_congr fun ρ => (hA ρ).symm

end PositivityTheory.AdelicQuotientData

end
end

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

theorem ku_of : jumpWindows.G5 → D0 → KU := by
  intro hG hD E _ _ _ k ψ hψ φ u hφ h1
  obtain ⟨-, -, -, hW⟩ := hG E k ψ hψ
  have hWc : Continuous (Wh ψ φ) := (hW φ hφ).1
  obtain ⟨hpos, hmul, hcont, -⟩ := hD E k
  have hD1 : Dt (1 : GA E k) = 1 := by
    have h := hmul 1 1
    rw [show (1 : GA E k) * 1 = 1 from mul_one 1] at h
    exact mul_left_cancel₀ (hpos 1).ne' (h.symm.trans (mul_one _).symm)
  set F : GA E k → ℂ := fun c => conj (Wh ψ φ c) * (Dt c : ℂ) ^ ((u : ℂ) * Complex.I) with hF
  have hDc : Continuous fun c : GA E k => (Dt c : ℂ) := Complex.continuous_ofReal.comp hcont
  have hFc : Continuous F := (Complex.continuous_conj.comp hWc).mul
    (hDc.cpow continuous_const fun c => Complex.ofReal_mem_slitPlane.2 (hpos c))
  have hF1 : F 1 = 1 := by simp [F, h1, hD1]
  refine ⟨{c | Dt c ∈ Set.Ioo (1 / 2 : ℝ) 2} ∩ {c | 0 < (F c).re}, ?_, ?_⟩
  · apply IsOpen.mem_nhds
    · exact (isOpen_Ioo.preimage hcont).inter (isOpen_lt continuous_const (Complex.continuous_re.comp hFc))
    · simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo, hD1, hF1]
      norm_num
  · rintro c ⟨⟨ha, hb⟩, hc⟩
    exact ⟨ha.le, hb.le, hc⟩

end PositivityTheory.AdelicQuotientData

end
end
