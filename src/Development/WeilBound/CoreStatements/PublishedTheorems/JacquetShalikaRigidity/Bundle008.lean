module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle410
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle352
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle395
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle229
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle452
public import GroundTheory.AutomorphicForms.ReductionCore
public import GroundTheory.AutomorphicForms.ReductionMahler
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

namespace tableDegreeOneUnipotent

theorem mul_le_sq_add (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ _ := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ _ := le_self_add

theorem integ {X : Type} [MeasurableSpace X] {ν : Measure X} {f φ : X → ℂ}
    (hf : AEStronglyMeasurable f ν) (hφ : AEStronglyMeasurable φ ν)
    (h1 : ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν < ∞) (h2 : ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂ν < ∞) :
    Integrable (fun g => f g * conj (φ g)) ν := by
  refine ⟨hf.mul (Complex.continuous_conj.comp_aestronglyMeasurable hφ), ?_⟩
  show ∫⁻ g, ‖f g * conj (φ g)‖ₑ ∂ν < ∞
  calc ∫⁻ g, ‖f g * conj (φ g)‖ₑ ∂ν ≤ ∫⁻ g, (‖f g‖ₑ ^ 2 + ‖φ g‖ₑ ^ 2) ∂ν := by
        refine lintegral_mono fun g => ?_
        have hc : ‖conj (φ g)‖ₑ = ‖φ g‖ₑ := by simp [enorm_eq_nnnorm]
        rw [enorm_mul, hc]
        exact mul_le_sq_add _ _
    _ = ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν + ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂ν := lintegral_add_left' (hf.enorm.pow_const 2) _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨h1, h2⟩

theorem pre_of_good {E : Type} [Field E] [NumberField E] {k : ℕ} {ψ : AddChar (Ad E) ℂ} {m : ℕ}
    {f : GA E k → ℂ} (h : Good ψ m f) : Pre ψ m f :=
  ⟨h.cont, h.left, h.law⟩

theorem main (hU1 : U1) (hP1 : P1) (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ)
    (μ : Measure (GA E k)) [μ.IsHaarMeasure] (ψ : AddChar (Ad E) ℂ) (hψ : StdPsi ψ) :
    ∀ m, m < k → ∀ β, IsWt (nuP E k m) β → ∃ β', IsWt (nuP E k 0) β' ∧
      ∀ f φ, Pre ψ m f → Good ψ m φ → ∫⁻ g, ‖f g‖ₑ ^ 2 ∂μ.withDensity β < ∞ →
        ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂μ.withDensity β < ∞ →
        Integrable (fun g => whit ψ m f g * conj (whit ψ m φ g)) (μ.withDensity β') ∧
        ∫ g, f g * conj (φ g) ∂μ.withDensity β = ∫ g, whit ψ m f g * conj (whit ψ m φ g) ∂μ.withDensity β' := by
  intro m
  induction m with
  | zero =>
    intro _ β hβ
    refine ⟨β, hβ, fun f φ hf hφ h1 h2 => ⟨?_, rfl⟩⟩
    exact integ hf.cont.aestronglyMeasurable (pre_of_good hφ).cont.aestronglyMeasurable h1 h2
  | succ m ih =>
    intro hm β hβ
    obtain ⟨β1, hβ1, hL2, hip⟩ := hU1 E k μ ψ hψ (m + 1) (by omega) hm β hβ
    obtain ⟨β', hβ', h⟩ := ih (by omega) β1 hβ1
    refine ⟨β', hβ', fun f φ hf hφ h1 h2 => ?_⟩
    have hf' : Pre ψ m (colT ψ (m + 1) f) := (hP1 E k ψ hψ (m + 1) (by omega) hm f hf).1
    have hφ' : Good ψ m (colT ψ (m + 1) φ) := by
      refine { cont := ?_, left := ?_, law := ?_, van := ?_ }
      · exact _root_.GlobalTheory.T.continuous_unipotentColumnWhittakerTransform E k ψ hψ m φ hφ
      · exact _root_.GlobalTheory.T.unipotentColumnWhittakerTransform_mirabolic_invariant E k ψ hψ m φ hm hφ
      · intro j hj y g
        rcases Nat.lt_or_ge (m + 1) j with h | h
        · exact _root_.GlobalTheory.T.columnWhittakerTransform_keeps_later_law E k ψ m φ hφ j h y g
        · obtain rfl : j = m + 1 := by omega
          exact _root_.GlobalTheory.T.unipotentColumnWhittakerTransform_column_law E k ψ hψ m φ hφ y g
      · exact _root_.GlobalTheory.T.quotientAverage_unipotentBlock_columnTransform_eq_zero E k ψ hψ m φ hm hφ
    obtain ⟨hi, he⟩ := h _ _ hf' hφ' ((hL2 f hf).trans_lt h1) ((hL2 φ (pre_of_good hφ)).trans_lt h2)
    exact ⟨hi, (hip f φ hf hφ h1 h2).trans he⟩

end tableDegreeOneUnipotent

theorem unitaryGroupGeometricSide_of_quotient_identities : U1 → P1 → U2 := by
  intro hU1 hP1 E _ _ _ k μ _ ψ hψ
  exact tableDegreeOneUnipotent.main hU1 hP1 E k μ ψ hψ

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

namespace RowsCompactSum

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

theorem contFin : Continuous (fun (y : Fin k → Ad E) (i : Fin k) => pFin E (y i)) :=
  continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pFin E).comp (continuous_apply i)

theorem contInf : Continuous (fun (y : Fin k → Ad E) (i : Fin k) => pInf E (y i)) :=
  continuous_pi fun i => (GlobalTheory.CuspRep.GASplit.continuous_pInf E).comp (continuous_apply i)

theorem one_le (C₀ : Set (Fin k → Ad E)) (hC₀ : IsCompact C₀) (M : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y,
    C₀.indicator (fun _ => (1 : ℝ≥0∞)) y ≤ ENNReal.ofReal B * ENNReal.ofReal
      (((fun y (i : Fin k) => pFin E (y i)) '' C₀).indicator
        (fun _ => ((1 + ‖fun i => pInf E (y i)‖) ^ M)⁻¹) fun i => pFin E (y i)) := by
  obtain ⟨R, hR⟩ := hC₀.exists_bound_of_continuousOn (contInf (E := E) (k := k)).continuousOn
  refine ⟨(1 + max R 0) ^ M, by positivity, fun y => ?_⟩
  by_cases hy : y ∈ C₀
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (Set.mem_image_of_mem _ hy), ← ENNReal.ofReal_mul (by positivity)]
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have h0 : 0 < (1 + ‖fun i => pInf E (y i)‖) ^ M := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ h0, one_mul]
    apply pow_le_pow_left₀ (by positivity)
    have := hR y hy
    linarith [le_max_left R 0]
  · rw [Set.indicator_of_notMem hy]
    exact bot_le

theorem sum_le (hN : N0) (hG3 : ThetaSeriesBound) (hk : 1 ≤ k) (C₀ : Set (Fin k → Ad E)) (hC₀ : IsCompact C₀) (a : ℕ) (ha : k ≤ a) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ (g : GA E k) (r : ℝ), 0 < r → (∀ ξ, ξ ≠ 0 → r ≤ height g ξ) →
      ∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≤
        ENNReal.ofReal (B * (C * (r ^ a)⁻¹)) := by
  have hCf : IsCompact ((fun y (i : Fin k) => pFin E (y i)) '' C₀) := hC₀.image contFin
  obtain ⟨M, C, hMC⟩ := hG3 E k _ hCf a ha
  obtain ⟨B, hB, hB1⟩ := one_le C₀ hC₀ M
  have hlast := (hN E k k hk le_rfl).2.2.2.2.2.2.2.2.2
  refine ⟨B, max C 0, hB, le_max_right _ _, fun g r hr hrh => ?_⟩
  have hinj : Function.Injective (fun ξ : RowT E k k => (⟨ξ.1, ξ.2.1⟩ : {ξ : Fin k → E // ξ ≠ 0})) := by
    intro x y h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h
  let F : {ξ : Fin k → E // ξ ≠ 0} → ℝ≥0∞ := fun ξ => ENNReal.ofReal
    (((fun y (i : Fin k) => pFin E (y i)) '' C₀).indicator
      (fun _ => ((1 + ‖fun i => pInf E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i)‖) ^ M)⁻¹)
      fun i => pFin E (((fun i => algebraMap E (Ad E) (ξ.1 i)) ᵥ* g.val) i))
  have hF : ∑' ξ, F ξ ≤ ENNReal.ofReal (C * (r ^ a)⁻¹) := hMC g r hr hrh
  have h1 : ∀ ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≤
      ENNReal.ofReal B * F ⟨ξ.1, ξ.2.1⟩ := by
    intro ξ
    rw [hlast]
    exact hB1 _
  calc _ ≤ ∑' ξ : RowT E k k, ENNReal.ofReal B * F ⟨ξ.1, ξ.2.1⟩ := ENNReal.tsum_le_tsum h1
    _ ≤ ∑' ξ, ENNReal.ofReal B * F ξ := ENNReal.tsum_comp_le_tsum_of_injective hinj (fun ξ => ENNReal.ofReal B * F ξ)
    _ = ENNReal.ofReal B * ∑' ξ, F ξ := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (max C 0 * (r ^ a)⁻¹) := by
        gcongr
        refine hF.trans (ENNReal.ofReal_le_ofReal ?_)
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (B * (max C 0 * (r ^ a)⁻¹)) := (ENNReal.ofReal_mul hB).symm

theorem r_le (hD : D0) (hK : K1) (hk : 1 ≤ k) (g : GA E k) :
    0 < dmin g * Dt g ^ ((k : ℝ)⁻¹) ∧ ∀ ξ, ξ ≠ 0 → dmin g * Dt g ^ ((k : ℝ)⁻¹) ≤ height g ξ := by
  have hDt := (hD E k).1 g
  have hK' := hK E k hk
  have hp : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDt _
  refine ⟨mul_pos (hK'.2.1 g) hp, fun ξ hξ => ?_⟩
  have h1 := hK'.2.2.1 g ξ hξ
  have h2 : height g ξ = ht g ξ * Dt g ^ ((k : ℝ)⁻¹) := by
    unfold ht; field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 hp.le

end RowsCompactSum

theorem rows_compact_of_bound : D0 → N0 → H0 → ThetaSeriesBound → K1 → RowsInCompactSet := by
  intro hD hN _ hG3 hK E _ _ _ k hk C₀ hC₀
  refine ⟨fun g => ?_, fun a ha => ?_⟩
  · obtain ⟨B, C, hB, hC, h⟩ := RowsCompactSum.sum_le hN hG3 hk C₀ hC₀ k le_rfl
    obtain ⟨hr, hrh⟩ := RowsCompactSum.r_le hD hK hk g
    have hfin := h g _ hr hrh
    have hne : ∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g)) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin
    refine (ENNReal.finite_const_le_of_tsum_ne_top hne one_ne_zero).subset fun ξ hξ => ?_
    simp only [Set.mem_setOf_eq] at hξ ⊢
    rw [Set.indicator_of_mem hξ]
  · obtain ⟨B, C, hB, hC, h⟩ := RowsCompactSum.sum_le hN hG3 hk C₀ hC₀ a ha
    refine ⟨B * C, fun g => ?_⟩
    obtain ⟨hr, hrh⟩ := RowsCompactSum.r_le hD hK hk g
    have hDt := (hD E k).1 g
    have hd := (hK E k hk).2.1 g
    have hp : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDt _
    have hw0 : 0 ≤ wt a g := by unfold wt; exact pow_nonneg (le_min zero_le_one hd.le) _
    have hw : wt a g ≤ dmin g ^ a := by unfold wt; exact pow_le_pow_left₀ (le_min zero_le_one hd.le) (min_le_right _ _) _
    calc (∑' ξ : RowT E k k, C₀.indicator (fun _ => (1 : ℝ≥0∞)) (lastRow (ratGL E k (gam ξ) * g))) *
          ENNReal.ofReal (wt a g)
        ≤ ENNReal.ofReal (B * (C * ((dmin g * Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹)) * ENNReal.ofReal (wt a g) := by
          gcongr; exact h g _ hr hrh
      _ = ENNReal.ofReal (B * (C * ((dmin g * Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹) * wt a g) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (B * C * Dt g ^ (-(a : ℝ) / k)) := by
          apply ENNReal.ofReal_le_ofReal
          have he : Dt g ^ (-(a : ℝ) / k) = ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹ := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hDt.le, ← Real.rpow_neg hDt.le]
            congr 1; ring
          rw [he, mul_pow, mul_inv]
          have hda : 0 < dmin g ^ a := pow_pos hd _
          have hpa : 0 < (Dt g ^ ((k : ℝ)⁻¹)) ^ a := pow_pos hp _
          calc B * (C * ((dmin g ^ a)⁻¹ * ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹)) * wt a g
              ≤ B * (C * ((dmin g ^ a)⁻¹ * ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹)) * dmin g ^ a := by
                gcongr
            _ = B * C * ((Dt g ^ ((k : ℝ)⁻¹)) ^ a)⁻¹ := by field_simp

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

namespace PRSPole

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem bnd (hJS : GlobalTheory.Published.JacquetShalikaBound) {m : ℕ} (π : CuspSub E m) (hπ : IsNormalised π)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (α : Off E S → Fin m → ℂˣ) (hα : SatOff (CG.mk π) S α) :
    ∀ w a, ‖(α w a : ℂ)‖ ≤ Real.sqrt (nq w) := by
  intro w a
  have hu : (CG.mk π).IsUnitary :=
    (CG.isUnitary_mk π).2 (GlobalTheory.Published.CuspFormsBoundedGL.isUnitary GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL hπ)
  have h := (hJS E m (CG.mk π) hu w.1 _ (hα w) (α w a)
    (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))).2
  show ‖((α w a : ℂˣ) : ℂ)‖ ≤ Real.sqrt ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ)
  rw [Real.sqrt_eq_rpow]
  exact h.le

end PRSPole

open Classical in
theorem rspole_of : GlobalTheory.Published.JacquetShalikaBound → jumpWindows.G1 → jumpWindows.StandardCharacterExists → W0 → E2 → M1 → KIR → KSec → CornerEmbedding → KLt1 → KLt2 → LastRowCutoff → KEq1 → KEq2 → ORT → KY → RSPole := by
  intro hJS _hG1 hG10 hW0 hE2 hM1 hKIR hKSec hK5e hKLt1 hKLt2 hK11 hKEq1 hKEq2 hORT hKY E _ _ _ m k π π' u hk
    hkm hπ hπ'
  obtain ⟨ψ, hψ, hcond⟩ := hG10 E
  have hm : 1 ≤ m := hk.trans hkm
  obtain ⟨S₁, hS₁⟩ := hKSec E k hk ψ hψ hcond π' hπ'
  obtain ⟨S₂, hS₂⟩ := hKIR E m hm ψ hψ hcond π hπ
  refine ⟨S₁ ∪ S₂, fun S hS α β hα hβ => ?_⟩
  have hS1 : S₁ ⊆ S := Finset.union_subset_left hS
  have hS2 : S₂ ⊆ S := Finset.union_subset_right hS
  obtain ⟨hCond, hsec⟩ := hS₁ S hS1
  obtain ⟨φ₀', hφ₀', h', φ', hφ'e, hsec⟩ := hsec β hβ
  have hαb := PRSPole.bnd hJS π hπ S α hα
  have hβb := PRSPole.bnd hJS π' hπ' S β hβ
  let μ : Measure (GA E k) := by
    set_option synthInstance.maxHeartbeats 400000 in
      exact Measure.haar
  obtain ⟨⟨b, hb⟩, -⟩ := hW0 E k μ hk
  rcases hkm.lt_or_eq with hlt | heq
  · obtain ⟨ι, hι⟩ := ((hK5e E m k hkm).1 (Ad E))
    obtain ⟨U, hU, hUd⟩ := hKLt1 E m k hk hlt ψ hψ S hCond ι hι α β u φ' hsec
    obtain ⟨φ, -, hprep⟩ := hS₂ S hS2 α hα (m ^ 3) k hlt U hU ⊤ isClosed_univ (fun _ _ _ => trivial)
      (fun _ _ => trivial)
    have hdat := hUd (m ^ 3) (Nat.one_le_pow _ _ hm) φ hprep
    have hgrow := hKLt2 E m k hk hlt ψ hψ S hCond ι hι α β φ' hsec U φ hprep
    obtain ⟨Z, hZd, hZe, hZ1⟩ := hE2 E k μ hk b hb _ _ hgrow
    obtain ⟨ZS, σ₀, hZSd, hZS0, hZSe⟩ := hM1 E k μ hk b hb ψ hψ S m α β u _ _ hkm hαb hβb hdat
    refine ⟨Z, ZS, max 1 σ₀, hZd, hZSd.differentiableOn, fun σ _ => hZS0 σ, fun s hs => ?_, fun _ => hZ1 ?_⟩
    · rw [hZe s (lt_of_le_of_lt (le_max_left _ _) hs), hZSe s (lt_of_le_of_lt (le_max_right _ _) hs), mul_assoc]
    · simp
  · subst heq
    obtain ⟨U, hU, hUd⟩ := hKEq1 E k hk ψ hψ S hCond α β u φ' hsec
    let φ'' : XB E k := if π = π' then 0 else φ'
    obtain ⟨Y, hYc, hYi, hYm, hYz⟩ := hKY E k μ hk b hb φ''
    have hforms : ∀ x : XB E k, (∃ φ ∈ π.V, (x : GA E k → ℂ) = φ.1) → x ∈ Y := by
      rintro x ⟨φ₁, hφ₁, hx⟩
      have hx' : ∀ g, x g = φ₁.1 g := congrFun hx
      refine (hYm x).2 ⟨fun t g => by rw [hx', hx']; exact hπ φ₁ hφ₁ t g, fun h => ?_⟩
      by_cases he : π = π'
      · have e0 : φ'' = 0 := if_pos he
        rw [e0]
        simp
      · have e1 : φ'' = φ' := if_neg he
        have hO := hORT E k μ hk b hb π π' hπ hπ' he φ₁ hφ₁ φ₀' hφ₀' h h'
        rw [e1]
        simp only [hx', hφ'e]
        exact hO
    obtain ⟨φ, hφY, hprep⟩ := hS₂ S hS2 α hα (k + 1) (k - 1) (by omega) U hU Y hYc hYi hforms
    obtain ⟨η, s, hcut⟩ := hK11 E k hk ψ hψ S hCond U hU φ hprep.smooth hprep.lev
    have hdat := hUd φ hprep η s hcut
    have hcen := ((hYm φ).1 hφY).1
    have hgrow := hKEq2 E k hk ψ hψ S β φ' hsec U φ η s hcut hprep.inv hcen
    obtain ⟨Z, hZd, hZe, hZ1⟩ := hE2 E k μ hk b hb _ _ hgrow
    obtain ⟨ZS, σ₀, hZSd, hZS0, hZSe⟩ := hM1 E k μ hk b hb ψ hψ S k α β u _ _ le_rfl hαb hβb hdat
    refine ⟨Z, ZS, max 1 σ₀, hZd, hZSd.differentiableOn, fun σ _ => hZS0 σ, fun s hs => ?_, fun hne => hZ1 ?_⟩
    · rw [hZe s (lt_of_le_of_lt (le_max_left _ _) hs), hZSe s (lt_of_le_of_lt (le_max_right _ _) hs), mul_assoc]
    · have hne' : π ≠ π' := fun e => hne (by rw [e])
      have e1 : φ'' = φ' := if_neg hne'
      have hz := hYz φ hφY ψ S U η s hcut
      rw [e1] at hz
      exact hz

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

namespace DeterminantHeight

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem dt_eq (g : GA E k) :
    Dt g = (GroundTheory.Global.IdeleGroup.ideleModule E (AdelicGLn.det E k g) : ℝ) := rfl

theorem dt_maxCompact {κ : GA E k} (hκ : κ ∈ _root_.GroundTheory.Automorphic.Reduction.maxCompact) : Dt κ = 1 := by
  rw [dt_eq]; exact mem_normOneGL.1 (maxCompact_le_normOneGL hκ)

theorem dt_diag (γ : GL (Fin k) E) : Dt (AdelicGLn.diagonal E k γ) = 1 := by
  rw [dt_eq]; exact mem_normOneGL.1 (rationalGL_le_normOneGL ⟨γ, rfl⟩)

theorem dt_mul (g h : GA E k) : Dt (g * h) = Dt g * Dt h := by
  rw [dt_eq, dt_eq, dt_eq, map_mul, map_mul, Positive.val_mul]

theorem adeleAbs_pos {b : GA E k} (hb : b ∈ adelicBorel) (i : Fin k) :
    0 < adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) := by
  rw [← IsUnit.unit_spec (isUnit_apply_self_of_mem_adelicBorel hb i), adeleAbs_units]
  exact (GroundTheory.Global.IdeleGroup.ideleModule E _).2

theorem dt_borel {b : GA E k} (hb : b ∈ adelicBorel) :
    Dt b = ∏ i, adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) := by
  have hu : ∀ i, IsUnit ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) :=
    isUnit_apply_self_of_mem_adelicBorel hb
  have hdet : AdelicGLn.det E k b = ∏ i, (hu i).unit := by
    ext
    rw [AdelicGLn.coe_det, Matrix.det_of_isUpperTriangular hb, Units.coe_prod]
    simp
  rw [dt_eq, hdet, map_prod (GroundTheory.Global.IdeleGroup.ideleModule E), coe_finset_prod_pos]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← adeleAbs_units, IsUnit.unit_spec]

theorem height_last {b : GA E k} (hb : b ∈ adelicBorel) (L : Fin k) (hL : (L : ℕ) + 1 = k) :
    height b (Pi.single L 1) = adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) L L) := by
  have hu := isUnit_apply_self_of_mem_adelicBorel hb L
  have hrow : ratVec (Pi.single L (1 : E)) ᵥ* (b : Matrix (Fin k) (Fin k) (Ad E)) =
      Pi.single L ((b : Matrix (Fin k) (Fin k) (Ad E)) L L) := by
    have : ratVec (Pi.single L (1 : E)) = Pi.single L (1 : Ad E) := by
      ext l
      by_cases hl : l = L
      · subst hl; simp [ratVec]
      · simp [ratVec, Pi.single_eq_of_ne hl]
    rw [this, single_one_vecMul]
    ext l
    by_cases hl : l = L
    · subst hl; simp [Matrix.row]
    · have hlt : l < L := lt_of_le_of_ne (Fin.le_iff_val_le_val.2 (by omega)) hl
      simp [Matrix.row, Pi.single_eq_of_ne hl, hb hlt]
  rw [Reduction.height, hrow, ← IsUnit.unit_spec hu, adelicNorm_single_units, adeleAbs_units]

end DeterminantHeight

theorem minkowski_bound_of : D0 → MinkowskiBoundAlt := by
  intro _ E _ _ _ k hk
  obtain ⟨t₀, ht₀, hred⟩ := GroundTheory.Automorphic.Reduction.exists_reduced (K := E)
  set s : ℝ := min t₀ 1 with hs
  have hs0 : 0 < s := lt_min ht₀ one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  refine ⟨(s ^ k)⁻¹, fun g => ?_⟩
  obtain ⟨γ, b, hb, κ, hκ, heq, hr⟩ := hred k g
  set L : Fin k := ⟨k - 1, by omega⟩ with hLdef
  have hL : (L : ℕ) + 1 = k := by simp [L]; omega
  set a : Fin k → ℝ := fun i => adeleAbs ((b : Matrix (Fin k) (Fin k) (Ad E)) i i) with hadef
  have ha : ∀ i, 0 < a i := fun i => DeterminantHeight.adeleAbs_pos hb i
  refine ⟨Pi.single L 1 ᵥ* (γ : Matrix (Fin k) (Fin k) E), ?_, ?_⟩
  · intro h
    have h2 := congrArg (fun y => y ᵥ* ((γ⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E)) h
    simp only [vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one,
      zero_vecMul] at h2
    have := congrFun h2 L
    simp at this
  · have hH : Reduction.height g (Pi.single L 1 ᵥ* (γ : Matrix (Fin k) (Fin k) E)) = a L := by
      rw [← height_diagonal_mul, heq, height_mul_maxCompact _ hκ, DeterminantHeight.height_last hb L hL]
    have hD : Dt g = ∏ i, a i := by
      have h1 : Dt (AdelicGLn.diagonal E k γ * g) = Dt g := by
        rw [DeterminantHeight.dt_mul, DeterminantHeight.dt_diag, one_mul]
      rw [← h1, heq, DeterminantHeight.dt_mul, DeterminantHeight.dt_maxCompact hκ, mul_one, DeterminantHeight.dt_borel hb]
    have hchain : ∀ d : ℕ, ∀ i : Fin k, (i : ℕ) + d = k - 1 → s ^ d * a L ≤ a i := by
      intro d
      induction d with
      | zero =>
        intro i hi
        have : i = L := Fin.ext (by simp [L]; omega)
        subst this; simp
      | succ d ih =>
        intro i hi
        have hi' : (i : ℕ) + 1 < k := by omega
        have h1 := ih ⟨(i : ℕ) + 1, hi'⟩ (by simp; omega)
        have h2 := hr i ⟨(i : ℕ) + 1, hi'⟩ rfl
        calc s ^ (d + 1) * a L = s * (s ^ d * a L) := by ring
          _ ≤ s * a ⟨(i : ℕ) + 1, hi'⟩ := mul_le_mul_of_nonneg_left h1 hs0.le
          _ ≤ t₀ * a ⟨(i : ℕ) + 1, hi'⟩ := mul_le_mul_of_nonneg_right (min_le_left _ _) (ha _).le
          _ ≤ a i := h2
    have hlow : ∀ i, s ^ k * a L ≤ a i := fun i =>
      (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs0.le hs1 (by omega : k - 1 - (i : ℕ) ≤ k))
        (ha L).le).trans (hchain (k - 1 - (i : ℕ)) i (by omega))
    have hsa : 0 < s ^ k * a L := mul_pos (pow_pos hs0 k) (ha L)
    have hprod : (s ^ k * a L) ^ k ≤ Dt g := by
      rw [hD]
      calc (s ^ k * a L) ^ k = ∏ _i : Fin k, s ^ k * a L := by simp
        _ ≤ ∏ i, a i := Finset.prod_le_prod₀ (fun _ _ => hsa.le) (fun i _ => hlow i)
    have hDt : 0 < Dt g := by rw [hD]; exact Finset.prod_pos fun i _ => ha i
    have hDpos : 0 < Dt g ^ ((k : ℝ)⁻¹) := Real.rpow_pos_of_pos hDt _
    have hDk : (Dt g ^ ((k : ℝ)⁻¹)) ^ k = Dt g := Real.rpow_inv_natCast_pow hDt.le (by omega)
    have hle : s ^ k * a L ≤ Dt g ^ ((k : ℝ)⁻¹) :=
      (pow_le_pow_iff_left₀ hsa.le hDpos.le (by omega : k ≠ 0)).1 (hprod.trans hDk.ge)
    have hsk : 0 < s ^ k := pow_pos hs0 k
    rw [ht, hH, div_le_iff₀ hDpos, inv_mul_eq_div, le_div_iff₀ hsk]
    linarith

end PositivityTheory.AdelicQuotientData

end
end
