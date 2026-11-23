module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle147
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle054
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.InnerProductSpace.Trace
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

open MeasureTheory Matrix ValuativeRel

namespace GlobalTheory.SBNorm

theorem schwartzBruhat_memL2_inner_self : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}
    (μ : @Measure (Fin n × Fin d → k) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ f ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k),
      ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ ∧
      ∫ y, f y * (starRingEnd ℂ) (f y) ∂μ = (((∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) ∧
      (f ≠ 0 → ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ 0) ∧
      ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
  intro k _ _ _ _ n d μ hμ f hf
  letI : MeasurableSpace (Fin n × Fin d → k) := borel _
  haveI : BorelSpace (Fin n × Fin d → k) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hfc : Continuous f := hf.1.continuous
  have hint : ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k), Integrable (fun y => f y * (starRingEnd ℂ) (g y)) μ := by
    intro g hg
    have hgc : Continuous g := hg.1.continuous
    exact (hfc.mul (Complex.continuous_conj.comp hgc)).integrable_of_hasCompactSupport
      (hf.2.mul_right (f' := fun y => (starRingEnd ℂ) (g y)))
  have hpt : ∀ y, ‖f y * (starRingEnd ℂ) (f y)‖ₑ = ‖f y‖ₑ ^ 2 := by
    intro y
    rw [enorm_mul, pow_two]
    congr 1
    simp [enorm_eq_nnnorm]
  have hfin : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have := (hint f hf).2
    unfold HasFiniteIntegral at this
    simp_rw [hpt] at this
    exact this.ne
  refine ⟨hfin, ?_, ?_, hint⟩
  · have h1 : ∀ y, f y * (starRingEnd ℂ) (f y) = (((‖f y‖ ^ 2 : ℝ)) : ℂ) := by
      intro y
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [h1]
    rw [integral_complex_ofReal]
    congr 1
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun y => ‖f y‖ ^ 2)
      (Filter.Eventually.of_forall fun y => by positivity)
      ((hfc.norm.pow 2).aestronglyMeasurable)]
    congr 1
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  · intro hne
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (funext h)
    have hmeas : Measurable fun y => ‖f y‖ₑ ^ 2 := (hfc.measurable.enorm).pow_const 2
    rw [← pos_iff_ne_zero, lintegral_pos_iff_support hmeas]
    have hsupp : Function.support (fun y => ‖f y‖ₑ ^ 2) = f ⁻¹' {0}ᶜ := by
      ext y
      simp
    rw [hsupp]
    exact (hf.1 ({0}ᶜ)).measure_pos μ ⟨x, hx⟩

end GlobalTheory.SBNorm
end

section

open Filter Topology

namespace GlobalTheory.LinSchur


open Classical in
theorem exists_finset_eq_sum_cind {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (L : AddSubgroup X) (hL : IsOpen (L : Set X)) (f : X → ℂ) (hf : f ∈ GlobalTheory.WeilM.SB X)
    (hper : ∀ Y, ∀ C ∈ L, f (Y + C) = f Y) :
    ∃ F : Finset X, f = ∑ y ∈ F, f y • GlobalTheory.LinSchur.cind L y := by
  have hK : IsCompact (tsupport f) := hf.2
  obtain ⟨F0, -, hcov⟩ := hK.elim_nhds_subcover (fun x => {Y | Y - x ∈ L}) (fun x _ =>
    (hL.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp))
  refine ⟨(F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, ?_⟩
  have hmk : ∀ y ∈ (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, ∀ Y : X,
      Y - y ∈ L ↔ (QuotientAddGroup.mk Y : X ⧸ L) = QuotientAddGroup.mk y := by
    intro y _ Y
    rw [QuotientAddGroup.eq, ← neg_mem_iff]
    simp [sub_eq_add_neg, add_comm]
  funext Y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.LinSchur.cind]
  by_cases hex : ∃ y ∈ (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out, Y - y ∈ L
  · obtain ⟨y, hy, hYy⟩ := hex
    rw [Finset.sum_eq_single y]
    · rw [if_pos hYy, mul_one]
      have := hper y (Y - y) hYy
      rw [add_sub_cancel] at this
      exact this
    · intro y' hy' hne
      rw [if_neg, mul_zero]
      intro hY'
      apply hne
      obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hy'
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hy
      have e1 := (hmk _ hy' Y).mp hY'
      have e2 := (hmk _ hy Y).mp hYy
      simp only [QuotientAddGroup.out_eq'] at e1 e2
      rw [← e1, ← e2]
    · intro h; exact absurd hy h
  · push_neg at hex
    rw [Finset.sum_eq_zero (fun y hy => by rw [if_neg (hex y hy), mul_zero])]
    apply image_eq_zero_of_notMem_tsupport
    intro hY
    have := hcov hY
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at this
    obtain ⟨y0, hy0, hYy0⟩ := this
    have hmem : (QuotientAddGroup.mk y0 : X ⧸ L).out ∈
        (F0.image (QuotientAddGroup.mk (s := L))).image Quotient.out :=
      Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨y0, hy0, rfl⟩, rfl⟩
    apply hex _ hmem
    rw [hmk _ hmem, QuotientAddGroup.out_eq']
    rw [← QuotientAddGroup.eq_iff_sub_mem.mpr hYy0]

end GlobalTheory.LinSchur
end

section

namespace SchrodingerSchwartzBruhat
section
open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SchrSB

theorem eq_one_of_pow_two_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ (2 ^ n) - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.PositiveFormRecursion.main
  | exact _root_.GlobalTheory.PositiveFormRecursion.main
  | (apply _root_.GlobalTheory.PositiveFormRecursion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PositiveFormRecursion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PositiveFormRecursion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PositiveFormRecursion.main ..)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLocallyConstant_addChar (ψ : AddChar k ℂ) (hψ : Continuous ψ) : IsLocallyConstant ψ := by
  have hb := IsValuativeTopology.hasBasis_nhds_zero' k
  have hU : ψ ⁻¹' Metric.ball 1 (1 / 2) ∈ nhds (0 : k) :=
    hψ.continuousAt.preimage_mem_nhds (by
      rw [AddChar.map_zero_eq_one]; exact Metric.ball_mem_nhds _ (by norm_num))
  obtain ⟨γ, hγ, hsub⟩ := hb.mem_iff.mp hU
  have hker : ∀ x, ValuativeRel.valuation k x < γ → ψ x = 1 := by
    intro x hx
    have h2 : ∀ n : ℕ, ValuativeRel.valuation k ((2 ^ n : ℕ) • x) < γ := by
      intro n
      induction n with
      | zero => simpa using hx
      | succ n ih =>
        have e : (2 ^ (n + 1) : ℕ) • x = (2 ^ n : ℕ) • x + (2 ^ n : ℕ) • x := by
          rw [pow_succ, mul_two, add_smul]
        rw [e]
        exact Valuation.map_add_lt _ ih ih
    apply eq_one_of_pow_two_pow_near
    intro n
    have h3 : ψ ((2 ^ n : ℕ) • x) ∈ Metric.ball (1 : ℂ) (1 / 2) := hsub (h2 n)
    rw [AddChar.map_nsmul_eq_pow, Metric.mem_ball, dist_eq_norm] at h3
    exact h3
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hn : {y : k | ValuativeRel.valuation k (y - x) < γ} ∈ nhds x := by
    have hc : ContinuousAt (fun y : k => y - x) x := by fun_prop
    exact hc.preimage_mem_nhds (by simpa using hb.mem_of_mem hγ)
  filter_upwards [hn] with y hy
  have e : ψ y = ψ (y - x) * ψ x := by
    rw [← AddChar.map_add_eq_mul]; simp
  rw [e, hker _ hy, one_mul]

theorem schr_mem_SB : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), GlobalTheory.WeilM.schr ψ0 w φ ∈ GlobalTheory.WeilM.SB (κ → k) := by
  intro k _ _ _ _ _ ψ0 hψ κ _ w φ hφ
  obtain ⟨h1, h2⟩ : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hl := isLocallyConstant_addChar ψ0 hψ
  have hcont : Continuous fun x : κ → k => x ⬝ᵥ w.2 + ⅟(2 : k) * (w.1 ⬝ᵥ w.2) := by
    refine Continuous.add ?_ continuous_const
    exact continuous_id.dotProduct continuous_const
  have hs : HasCompactSupport fun x : κ → k => φ (x + w.1) :=
    h2.comp_homeomorph (Homeomorph.addRight w.1)
  have hf : IsLocallyConstant fun x : κ → k => φ (x + w.1) :=
    h1.comp_continuous (continuous_add_const w.1)
  refine ⟨?_, ?_⟩
  · exact (hl.comp_continuous hcont).mul hf
  · exact HasCompactSupport.mul_left hs

end GlobalTheory.CompanionTheory.SchrSB

end

end SchrodingerSchwartzBruhat
section

open MeasureTheory Matrix

theorem _root_.GlobalTheory.Adopt.schroedingerOperatorHeisenberg_preserves_schwartzBruhat : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)] (ψ0 : AddChar k ℂ), Continuous ψ0 →
    ∀ {κ : Type} [Fintype κ] (w : (κ → k) × (κ → k)), ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), GlobalTheory.WeilM.schr ψ0 w φ ∈ GlobalTheory.WeilM.SB (κ → k) := by
  first | exact @SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB | exact SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB | (intros; apply SchrodingerSchwartzBruhat.GlobalTheory.CompanionTheory.SchrSB.schr_mem_SB <;> assumption)

end
end

section

open GlobalTheory.WeilM
open scoped Matrix

namespace GlobalTheory.SiegelUnip
open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

abbrev adR (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n) (Fin n ⊕ Fin n) R := fromCols 1 (-1)

abbrev adC (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n ⊕ Fin n) (Fin n) R := fromRows 1 (-1)

abbrev dgC (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n ⊕ Fin n) (Fin n) R := diagCols (Fin n)

theorem adR_mul_dgC : adR n R * dgC n R = 0 := by
  simp [diagCols, fromCols_mul_fromRows]

theorem adR_mul_adC : adR n R * adC n R = 2 • (1 : Matrix (Fin n) (Fin n) R) := by
  simp [fromCols_mul_fromRows, two_smul]

theorem dbl_mul_dgC (J₀ : Matrix (Fin n) (Fin n) R) : dbl J₀ * dgC n R = adC n R * J₀ := by
  rw [dbl, dgC, diagCols, fromBlocks_mul_fromRows, adC, fromRows_mul]
  simp

theorem dgC_tr_mul_dbl (J₀ : Matrix (Fin n) (Fin n) R) : (dgC n R)ᵀ * dbl J₀ = J₀ * adR n R := by
  rw [dbl, dgC, diagCols, transpose_fromRows, fromCols_mul_fromBlocks, adR, mul_fromCols]
  simp

theorem dgC_tr_dbl_dgC (J₀ : Matrix (Fin n) (Fin n) R) : (dgC n R)ᵀ * dbl J₀ * dgC n R = 0 := by
  rw [dgC_tr_mul_dbl, Matrix.mul_assoc, adR_mul_dgC, Matrix.mul_zero]

theorem adR_tr : (adR n R)ᵀ = adC n R := by
  simp [adR, adC, transpose_fromCols]

theorem dgC_map {R₀ : Type} [CommRing R₀] [Algebra R₀ R] (c : R →ₐ[R₀] R) : (dgC n R).map c = dgC n R := by
  rw [dgC, diagCols, fromRows_map, Matrix.map_one _ (map_zero c) (map_one c)]

theorem adR_map {R₀ : Type} [CommRing R₀] [Algebra R₀ R] (c : R →ₐ[R₀] R) : (adR n R).map c = adR n R := by
  rw [adR, fromCols_map, Matrix.map_neg _ (map_neg c), Matrix.map_one _ (map_zero c) (map_one c)]

end GlobalTheory.SiegelUnip


open Matrix GlobalTheory.SiegelUnip in
theorem GlobalTheory.siegel_unip_corner : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] [Algebra R₀ R] [Invertible (2 : R)] (c : R →ₐ[R₀] R) {n : ℕ} (J₀ : Matrix (Fin n) (Fin n) R) (x : Matrix (Fin n) (Fin n) R), xᵀ * J₀ + J₀ * x.map c = 0 → ∃ p : UG c (dbl J₀), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) * diagCols (Fin n) = diagCols (Fin n) * (1 : Matrix (Fin n) (Fin n) R) ∧ ∀ h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R, Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * (h * p.1.1) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) = Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) + Matrix.fromCols (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R) * h * diagCols (Fin n) * x := by
  intro R₀ R _ _ _ _ c n J₀ x hx
  set N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := GlobalTheory.SiegelUnip.dgC n R * x * GlobalTheory.SiegelUnip.adR n R with hN
  have hNN : N * N = 0 := by
    rw [hN, show GlobalTheory.SiegelUnip.dgC n R * x * GlobalTheory.SiegelUnip.adR n R * (GlobalTheory.SiegelUnip.dgC n R * x * GlobalTheory.SiegelUnip.adR n R) = GlobalTheory.SiegelUnip.dgC n R * x * (GlobalTheory.SiegelUnip.adR n R * GlobalTheory.SiegelUnip.dgC n R) * x * GlobalTheory.SiegelUnip.adR n R by
      simp only [Matrix.mul_assoc], GlobalTheory.SiegelUnip.adR_mul_dgC, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]
  have hsq : (⅟(2 : R) • N) * (⅟(2 : R) • N) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hNN, smul_zero, smul_zero]
  have hPQ : (1 + ⅟(2 : R) • N) * (1 - ⅟(2 : R) • N) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hsq]; abel
  have hQP : (1 - ⅟(2 : R) • N) * (1 + ⅟(2 : R) • N) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hsq]; abel
  have hc2 : c (⅟(2 : R)) = ⅟(2 : R) := by
    refine (invOf_eq_right_inv ?_).symm
    have := congrArg c (mul_invOf_self (2 : R))
    rwa [map_mul, map_ofNat, map_one] at this
  have hNc : N.map c = GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R := by
    change (GlobalTheory.SiegelUnip.dgC n R * x * GlobalTheory.SiegelUnip.adR n R).map (c.toRingHom : R → R) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    exact congrArg₂ _ (congrArg₂ _ (GlobalTheory.SiegelUnip.dgC_map c) rfl) (GlobalTheory.SiegelUnip.adR_map c)
  have hPc : (1 + ⅟(2 : R) • N).map c = 1 + ⅟(2 : R) • (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R) := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_one _ (map_zero c) (map_one c), ← hNc]
    congr 1
    ext i j
    simp [hc2]
  have hNt : Nᵀ = GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ := by
    rw [hN, Matrix.transpose_mul, Matrix.transpose_mul, GlobalTheory.SiegelUnip.adR_tr, Matrix.mul_assoc]
  have hmem : (1 + ⅟(2 : R) • N)ᵀ * dbl J₀ * (1 + ⅟(2 : R) • N).map c = dbl J₀ := by
    rw [hPc, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul, hNt]
    have e1 : dbl J₀ * (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R) = GlobalTheory.SiegelUnip.adC n R * (J₀ * x.map c) * GlobalTheory.SiegelUnip.adR n R := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SiegelUnip.dbl_mul_dgC]; simp only [Matrix.mul_assoc]
    have e2 : GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀ = GlobalTheory.SiegelUnip.adC n R * (xᵀ * J₀) * GlobalTheory.SiegelUnip.adR n R := by
      rw [Matrix.mul_assoc, GlobalTheory.SiegelUnip.dgC_tr_mul_dbl]; simp only [Matrix.mul_assoc]
    have e3 : GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀ * (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R) = 0 := by
      rw [show GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀ * (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R) =
        GlobalTheory.SiegelUnip.adC n R * xᵀ * ((GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀ * GlobalTheory.SiegelUnip.dgC n R) * x.map c * GlobalTheory.SiegelUnip.adR n R by simp only [Matrix.mul_assoc],
        GlobalTheory.SiegelUnip.dgC_tr_dbl_dgC]
      simp
    have e4 : GlobalTheory.SiegelUnip.adC n R * (J₀ * x.map c) * GlobalTheory.SiegelUnip.adR n R + GlobalTheory.SiegelUnip.adC n R * (xᵀ * J₀) * GlobalTheory.SiegelUnip.adR n R = 0 := by
      rw [← Matrix.add_mul, ← Matrix.mul_add, add_comm, hx, Matrix.mul_zero, Matrix.zero_mul]
    calc (1 + ⅟(2 : R) • (GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ)) * dbl J₀ * (1 + ⅟(2 : R) • (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R))
        = dbl J₀ + ⅟(2 : R) • (dbl J₀ * (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R)) +
          ⅟(2 : R) • (GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀) +
          (⅟(2 : R) * ⅟(2 : R)) • (GlobalTheory.SiegelUnip.adC n R * xᵀ * (GlobalTheory.SiegelUnip.dgC n R)ᵀ * dbl J₀ * (GlobalTheory.SiegelUnip.dgC n R * x.map c * GlobalTheory.SiegelUnip.adR n R)) := by
          simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; abel
      _ = dbl J₀ + ⅟(2 : R) • (GlobalTheory.SiegelUnip.adC n R * (J₀ * x.map c) * GlobalTheory.SiegelUnip.adR n R + GlobalTheory.SiegelUnip.adC n R * (xᵀ * J₀) * GlobalTheory.SiegelUnip.adR n R) := by
          rw [e3, e1, e2, smul_zero, add_zero, smul_add, add_assoc]
      _ = dbl J₀ := by rw [e4, smul_zero, add_zero]
  let u : GL (Fin n ⊕ Fin n) R := ⟨1 + ⅟(2 : R) • N, 1 - ⅟(2 : R) • N, hPQ, hQP⟩
  refine ⟨⟨u, hmem⟩, ?_, fun h => ?_⟩
  · have hp : ((⟨u, hmem⟩ : UG c (dbl J₀)) : GL (Fin n ⊕ Fin n) R).1 = 1 + ⅟(2 : R) • N := rfl
    rw [hp]
    have hpd : N * GlobalTheory.SiegelUnip.dgC n R = 0 := by rw [hN, Matrix.mul_assoc, GlobalTheory.SiegelUnip.adR_mul_dgC, Matrix.mul_zero]
    have key : ((1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) + ⅟(2 : R) • N) * GlobalTheory.SiegelUnip.dgC n R =
        GlobalTheory.SiegelUnip.dgC n R * (1 : Matrix (Fin n) (Fin n) R) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hpd, smul_zero, add_zero, Matrix.mul_one]
    exact key
  · have hp : ((⟨u, hmem⟩ : UG c (dbl J₀)) : GL (Fin n ⊕ Fin n) R).1 = 1 + ⅟(2 : R) • N := rfl
    rw [hp]
    have e : GlobalTheory.SiegelUnip.adR n R * (h * N) * GlobalTheory.SiegelUnip.adC n R = (2 : R) • (GlobalTheory.SiegelUnip.adR n R * h * GlobalTheory.SiegelUnip.dgC n R * x) := by
      rw [hN, show GlobalTheory.SiegelUnip.adR n R * (h * (GlobalTheory.SiegelUnip.dgC n R * x * GlobalTheory.SiegelUnip.adR n R)) * GlobalTheory.SiegelUnip.adC n R = GlobalTheory.SiegelUnip.adR n R * h * GlobalTheory.SiegelUnip.dgC n R * x * (GlobalTheory.SiegelUnip.adR n R * GlobalTheory.SiegelUnip.adC n R) by
        simp only [Matrix.mul_assoc], GlobalTheory.SiegelUnip.adR_mul_adC, Matrix.mul_smul, Matrix.mul_one, two_smul, two_smul]
    rw [mul_add, mul_one, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, e, smul_smul,
      invOf_mul_self, one_smul, Matrix.mul_assoc (GlobalTheory.SiegelUnip.adR n R) h]
    rfl
end

section

noncomputable section

open Matrix NumberField
open scoped TensorProduct Classical

namespace GlobalTheory.LKTrip.HTGroup

theorem span_real_embedding_places (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] :
    Submodule.span ℝ (Set.range fun (a : F) (v : InfinitePlace F) => v.embedding a) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top
  | exact _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top
  | (apply _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EmbeddingRangeSpanTop.span_range_embedding_eq_top ..)

variable {p : ℕ} [Fact p.Prime]

theorem psiR_tmul (G : HTGroup p) (v : InfinitePlace G.F) (r : ℝ) (c : G.C) :
    G.psiR v (r ⊗ₜ c) = r • G.psi v c := by
  simp only [psiR, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]
  rfl

theorem psiR_pi_bijective (G : HTGroup p) :
    Function.Bijective (fun x : ℝ ⊗[ℚ] G.C => fun v : InfinitePlace G.F => G.psiR v x) := by
  let Ψ : ℝ ⊗[ℚ] G.C →ₐ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := Pi.algHom ℝ _ fun v => G.psiR v
  have hΨ : ∀ x, Ψ x = fun v => G.psiR v x := fun x => rfl
  set S := Ψ.range with hS
  have hsc : ∀ a : G.F, Ψ (1 ⊗ₜ algebraMap G.F G.C a) =
      fun v : InfinitePlace G.F => Matrix.scalar (Fin G.n) (v.embedding a) := by
    intro a; funext v; rw [hΨ]; dsimp only; rw [psiR_tmul, one_smul, G.psi_F]
  let sc : (InfinitePlace G.F → ℂ) →ₗ[ℝ] (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) :=
    { toFun := fun c v => Matrix.scalar (Fin G.n) (c v)
      map_add' := fun c d => by funext v; simp
      map_smul' := fun r c => by
        funext v
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [Matrix.scalar_apply, Matrix.scalar_apply]
        ext i j
        by_cases h : i = j <;> simp [Matrix.diagonal_apply, h] }
  have hscS : ∀ c : InfinitePlace G.F → ℂ, sc c ∈ S := by
    have htop := span_real_embedding_places G.F
    have hle : Submodule.span ℝ (Set.range fun (a : G.F) (v : InfinitePlace G.F) => v.embedding a) ≤
        (Subalgebra.toSubmodule S).comap sc := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.mem_comap.2 ((AlgHom.mem_range _).2 ⟨_, hsc a⟩)
    intro c
    exact hle (htop ▸ Submodule.mem_top)
  have hsingle : ∀ (v₁ : InfinitePlace G.F) (m : Matrix (Fin G.n) (Fin G.n) ℂ), Pi.single v₁ m ∈ S := by
    intro v₁ m
    have hspan := GlobalTheory.UPel.HT.RealRepBij.span_range_eq_top v₁.embedding (G.psi v₁) G.rankC (G.psi_F v₁)
    have hm : m ∈ Submodule.span ℂ (Set.range (G.psi v₁)) := hspan ▸ Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      have : (Pi.single v₁ (G.psi v₁ b) : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) =
          sc (Pi.single v₁ 1) * Ψ (1 ⊗ₜ b) := by
        funext v
        rw [hΨ]
        by_cases h : v = v₁
        · subst h; simp [sc, psiR_tmul]
        · simp [sc, h, psiR_tmul]
      rw [this]; exact S.mul_mem (hscS _) ((AlgHom.mem_range _).2 ⟨_, rfl⟩)
    | zero => simpa using S.zero_mem
    | add x y _ _ hx hy => rw [Pi.single_add]; exact S.add_mem hx hy
    | smul z x _ hx =>
      have : (Pi.single v₁ (z • x) : InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) =
          sc (Pi.single v₁ z) * Pi.single v₁ x := by
        funext v
        by_cases h : v = v₁
        · subst h; simp [sc, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
        · simp [sc, h]
      rw [this]; exact S.mul_mem (hscS _) hx
  have hsurj : Function.Surjective Ψ := by
    intro y
    have : y ∈ S := by
      rw [← Finset.univ_sum_single y]
      exact Subalgebra.sum_mem _ fun v _ => hsingle v (y v)
    exact (AlgHom.mem_range _).1 this
  have hc : 2 * Fintype.card (InfinitePlace G.F) = Module.finrank ℚ G.F := by
    rw [← InfinitePlace.card_add_two_mul_card_eq_rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero G.F]
    ring
  have hfin : Module.finrank ℝ (ℝ ⊗[ℚ] G.C) =
      Module.finrank ℝ (InfinitePlace G.F → Matrix (Fin G.n) (Fin G.n) ℂ) := by
    rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank ℚ G.F G.C, G.rankC, Module.finrank_pi_fintype]
    simp only [Module.finrank_matrix, Fintype.card_fin, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
    rw [← hc]; ring
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin (f := Ψ.toLinearMap)).2 hsurj, hsurj⟩

end GlobalTheory.LKTrip.HTGroup
end
end

section

namespace GlobalTheory.OpTrace

theorem hasTrace_sum_inner_of_range_le (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U]
    [CompleteSpace U] (L : Submodule ℂ U) [FiniteDimensional ℂ L] (T : U →L[ℂ] U)
    (hT : ∀ u, T u ∈ L) :
    HasTrace T (∑ j, inner ℂ (stdOrthonormalBasis ℂ L j : U)
      (T (stdOrthonormalBasis ℂ L j : U))) := by
  have hle : LinearMap.range (T : U →ₗ[ℂ] U) ≤ L := by
    rintro _ ⟨x, rfl⟩; exact hT x
  have := Submodule.finiteDimensional_of_le hle
  have h := hasTrace_of_finiteRank T
  rw [finRankTrace_eq (T : U →ₗ[ℂ] U) L hT,
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ L)] at h
  exact h

end GlobalTheory.OpTrace
end
