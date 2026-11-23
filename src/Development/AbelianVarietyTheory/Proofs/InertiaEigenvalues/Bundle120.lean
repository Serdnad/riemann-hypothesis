module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle096
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryGroupPositiveCharacterTrivialAndUnimodula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticIntegralTraceFormPerfect
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle097
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle058
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle018
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle098
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle103

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.EtaChar

theorem exists_unif (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] :
    ∃ π : F, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ x : F, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hc : IsCompact (Metric.ball (0 : F) 1) :=
    (isCompact_closedBall (0 : F) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball _ _)
      Metric.ball_subset_closedBall
  obtain ⟨π, hπm, hmax⟩ := hc.exists_isMaxOn ⟨0, Metric.mem_ball_self one_pos⟩ continuous_norm.continuousOn
  have hπ1 : ‖π‖ < 1 := by simpa using hπm
  have hle : ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖π‖ := fun y hy => hmax (by simpa using hy)
  obtain ⟨x0, hx0, hx01⟩ := NormedField.exists_norm_lt_one F
  have hπ0 : 0 < ‖π‖ := lt_of_lt_of_le hx0 (hle x0 hx01)
  refine ⟨π, hπ0, hπ1, fun x hx => ?_⟩
  set q := ‖π‖ with hq
  have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hqi : 1 < q⁻¹ := one_lt_inv₀ hπ0 |>.2 hπ1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hxp hqi
  have hqn : 0 < q ^ (n + 1) := zpow_pos hπ0 _
  have hz : ‖x * π ^ (n + 1)‖ = ‖x‖ * q ^ (n + 1) := by rw [norm_mul, norm_zpow]
  have hup : ‖x‖ * q ^ (n + 1) ≤ 1 := by
    calc ‖x‖ * q ^ (n + 1) ≤ q⁻¹ ^ (n + 1) * q ^ (n + 1) := mul_le_mul_of_nonneg_right hn2 hqn.le
      _ = 1 := by rw [_root_.inv_zpow, inv_mul_cancel₀ hqn.ne']
  have hlo : q < ‖x‖ * q ^ (n + 1) := by
    calc q = q⁻¹ ^ n * q ^ (n + 1) := by
            rw [_root_.inv_zpow, zpow_add_one₀ hπ0.ne', ← mul_assoc, inv_mul_cancel₀ (zpow_pos hπ0 n).ne', one_mul]
      _ < ‖x‖ * q ^ (n + 1) := mul_lt_mul_of_pos_right hn1 hqn
  have heq : ‖x‖ * q ^ (n + 1) = 1 := by
    by_contra hne
    have := hle (x * π ^ (n + 1)) (by rw [hz]; exact lt_of_le_of_ne hup hne)
    rw [hz] at this
    linarith
  refine ⟨-(n + 1), ?_⟩
  rw [_root_.zpow_neg]; exact eq_inv_of_mul_eq_one_left heq

theorem eta_eq_one_iff {F : Type} [NormedField F] (x : F) : eta x = 1 ↔ ∃ y : F, ‖x‖ = ‖y‖ ^ 2 := by
  unfold eta
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    norm_num

theorem eta_eq_neg_one_iff {F : Type} [NormedField F] (x : F) : eta x = -1 ↔ ¬ ∃ y : F, ‖x‖ = ‖y‖ ^ 2 := by
  unfold eta
  split_ifs with h
  · simp only [h, not_true_eq_false, iff_false]
    norm_num
  · simp [h]

theorem sq_iff_even {F : Type} [NormedField F] {π : F} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1)
    (hall : ∀ x : F, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) {x : F} {k : ℤ} (hk : ‖x‖ = ‖π‖ ^ k) :
    (∃ y : F, ‖x‖ = ‖y‖ ^ 2) ↔ Even k := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : ‖x‖ = 0 := by simpa using hy
      rw [hk] at this
      exact (zpow_pos h0 k).ne' this
    obtain ⟨j, hj⟩ := hall y hy0
    rw [hk, hj, ← zpow_natCast, ← _root_.zpow_mul] at hy
    have := zpow_right_injective₀ h0 h1.ne hy
    exact ⟨j, by rw [this]; push_cast; ring⟩
  · rintro ⟨j, rfl⟩
    refine ⟨π ^ j, ?_⟩
    rw [hk, norm_zpow, ← zpow_natCast, ← _root_.zpow_mul]
    congr 1
    push_cast; ring

theorem eta_of_exp {F : Type} [NormedField F] {π : F} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1)
    (hall : ∀ x : F, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) {x : F} {k : ℤ} (hk : ‖x‖ = ‖π‖ ^ k) :
    eta x = if Even k then 1 else -1 := by
  have := sq_iff_even h0 h1 hall hk
  by_cases h : Even k
  · rw [(eta_eq_one_iff x).2 (this.2 h)]; simp [h]
  · rw [(eta_eq_neg_one_iff x).2 (fun h' => h (this.1 h'))]; simp [h]

theorem eta_mul (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) : eta (x * y) = eta x * eta y := by
  obtain ⟨π, h0, h1, hall⟩ := exists_unif F
  obtain ⟨k, hk⟩ := hall x hx
  obtain ⟨l, hl⟩ := hall y hy
  have hkl : ‖x * y‖ = ‖π‖ ^ (k + l) := by rw [norm_mul, hk, hl, zpow_add₀ h0.ne']
  rw [eta_of_exp h0 h1 hall hk, eta_of_exp h0 h1 hall hl, eta_of_exp h0 h1 hall hkl]
  by_cases ek : Even k <;> by_cases el : Even l <;> simp [ek, el, Int.even_add]

theorem eta_of_norm_eq {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  have e : (∃ z : F, ‖x‖ = ‖z‖ ^ 2) ↔ (∃ z : F, ‖y‖ = ‖z‖ ^ 2) := by rw [h]
  by_cases hh : ∃ z : F, ‖x‖ = ‖z‖ ^ 2
  · rw [(eta_eq_one_iff x).2 hh, (eta_eq_one_iff y).2 (e.1 hh)]
  · rw [(eta_eq_neg_one_iff x).2 hh, (eta_eq_neg_one_iff y).2 (fun h' => hh (e.2 h'))]

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ x y : F, x ≠ 0 → y ≠ 0 → eta (x * y) = eta x * eta y) ∧ (∀ x : F, ‖x‖ = 1 → eta x = 1) ∧ (∀ x : F, x ≠ 0 → (eta x = 1 ↔ ∃ v : E, v * star v = algebraMap F E x)) ∧ IsLocallyConstant (fun x : {x : F // x ≠ 0} => eta x.1) := by
  intro F E _ _ _ _ hU
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  refine ⟨fun x y hx hy => eta_mul F x y hx hy, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · exact (eta_eq_one_iff x).2 ⟨1, by rw [hx, norm_one, one_pow]⟩
  · rw [eta_eq_one_iff]
    constructor
    · rintro ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact hx (norm_eq_zero.1 (by simpa using hy))
      obtain ⟨v, hv⟩ := GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E (x / y ^ 2) (by rw [norm_div, norm_pow, hy, div_self (by positivity)])
      refine ⟨v * algebraMap F E y, ?_⟩
      rw [star_mul', hU.star_fix y]
      calc v * algebraMap F E y * (star v * algebraMap F E y)
          = (v * star v) * algebraMap F E (y ^ 2) := by rw [map_pow]; ring
        _ = algebraMap F E x := by rw [hv, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hy0)]
    · rintro ⟨v, hv⟩
      obtain ⟨z, hz⟩ := hU.unram v
      refine ⟨z, ?_⟩
      have := congrArg norm hv
      rw [norm_algebraMap', norm_mul, hU.norm_star, hz] at this
      rw [← this, sq]
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hx : 0 < ‖x.1‖ := norm_pos_iff.2 x.2
    have hmem : {y : {x : F // x ≠ 0} | ‖y.1 - x.1‖ < ‖x.1‖} ∈ 𝓝 x := by
      have : IsOpen {y : {x : F // x ≠ 0} | ‖y.1 - x.1‖ < ‖x.1‖} :=
        isOpen_lt (continuous_norm.comp (continuous_subtype_val.sub continuous_const)) continuous_const
      exact this.mem_nhds (by simpa using hx)
    filter_upwards [hmem] with y hy
    apply eta_of_norm_eq
    have h2 : y.1 = x.1 + (y.1 - x.1) := by ring
    rw [h2, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hy), max_eq_left hy.le]

end GlobalTheory.EtaChar
end

section

open GlobalTheory.JR Matrix

theorem _root_.GlobalTheory.T.companionMatrixOfCoeffs_charpoly_coeff_eq : ∀ (k : Type) [CommRing k] (r : ℕ) (p : Fin r → k) (i : Fin r), (companion p).charpoly.coeff (i : ℕ) = p i := by
  first | exact @GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring | exact GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring | (intros; apply GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.GLCompact

theorem Bm_act {k : Type} [CommRing k] {r : ℕ} (g : GL (Fin r) k) (Y : Gl r k) :
    Bm (act g Y) = (g : Matrix (Fin r) (Fin r) k) * Bm Y := by
  have hcol : ∀ j : ℕ, ((act g Y).1 ^ j) *ᵥ (act g Y).2.1 =
      (g : Matrix (Fin r) (Fin r) k) *ᵥ ((Y.1 ^ j) *ᵥ Y.2.1) := by
    intro j
    simp only [act]
    rw [Units.conj_pow, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Units.inv_mul, Matrix.mul_one]
  ext i j
  simp only [Bm, Matrix.of_apply, Matrix.mul_apply, hcol]
  simp [Matrix.mulVec, dotProduct]

theorem continuous_Bm {k : Type} [NormedField k] {r : ℕ} : Continuous (fun Y : Gl r k => Bm Y) := by
  refine continuous_matrix fun i j => ?_
  simp only [Bm, Matrix.of_apply]
  exact (continuous_apply i).comp
    ((continuous_fst.pow (j : ℕ)).matrix_mulVec (continuous_fst.comp continuous_snd))

theorem continuous_Cm {k : Type} [NormedField k] {r : ℕ} : Continuous (fun Y : Gl r k => Cm Y) := by
  refine continuous_matrix fun i j => ?_
  simp only [Cm, Matrix.of_apply]
  exact (continuous_apply j).comp
    (((continuous_fst.comp (continuous_snd.comp continuous_snd))).matrix_vecMul
      (continuous_fst.pow (i : ℕ)))

end GlobalTheory.JR.GLCompact

private theorem isCompact_unit_box (F : Type) [NontriviallyNormedField F] [ProperSpace F] (n : ℕ) :
    IsCompact {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧
      ‖Z.2.2.2‖ ≤ 1} := by
  have hv : IsCompact (Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) :=
    isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hm : IsCompact {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} := by
    have h : {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} =
        Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1 := by
      ext A
      exact ⟨fun h i _ j _ => by simpa using h i j,
        fun h i j => by simpa using h i (Set.mem_univ i) j (Set.mem_univ j)⟩
    rw [h]
    exact isCompact_univ_pi fun _ => hv
  have h : {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧
      ‖Z.2.2.2‖ ≤ 1} = {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} ×ˢ
        ((Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) ×ˢ
          ((Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) ×ˢ Metric.closedBall (0 : F) 1)) := by
    ext Z; simp
  rw [h]
  exact hm.prod (hv.prod (hv.prod (isCompact_closedBall 0 1)))

theorem GlobalTheory.JR.orbG_integrand_hasCompactSupport : ∀ (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (n : ℕ) (Y : Gl n F), Delta (inv Y) ≠ 0 → HasCompactSupport (fun g : GL (Fin n) F => unitG n F (act g Y) * omega (act g Y)) := by
  intro F _ _ n Y hY
  have : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨-, -, hCB, -, -⟩ := GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F n
  have hdet : (Cm Y).det * (Bm Y).det ≠ 0 := by
    rw [← Matrix.det_mul, hCB Y]
    exact hY
  have hB : IsUnit (Bm Y).det := isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
  have hC : IsUnit (Cm Y).det := isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hdet)

  have hψ : Continuous (fun Z : Gl n F =>
      (Bm Z * (Bm Y)⁻¹, MulOpposite.op ((Cm Y)⁻¹ * Cm Z))) :=
    (GlobalTheory.JR.GLCompact.continuous_Bm.matrix_mul continuous_const).prodMk
      (MulOpposite.continuous_op.comp (continuous_const.matrix_mul GlobalTheory.JR.GLCompact.continuous_Cm))
  have hK := Units.isClosedEmbedding_embedProduct.isCompact_preimage
    ((isCompact_unit_box F n).image hψ)
  refine HasCompactSupport.intro hK ?_
  intro g hg
  have hgY : act g Y ∉ {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧
      (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧ ‖Z.2.2.2‖ ≤ 1} := by
    intro hmem
    refine hg ⟨act g Y, hmem, Prod.ext ?_ ?_⟩
    · show Bm (act g Y) * (Bm Y)⁻¹ = (g : Matrix (Fin n) (Fin n) F)
      rw [GlobalTheory.JR.GLCompact.Bm_act, Matrix.mul_nonsing_inv_cancel_right _ _ hB]
    · show MulOpposite.op ((Cm Y)⁻¹ * Cm (act g Y)) =
        MulOpposite.op ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      rw [GlobalTheory.JR.TransferFactor.Cm_act, Matrix.nonsing_inv_mul_cancel_left _ _ hC]
  have h0 : unitG n F (act g Y) = 0 := Set.indicator_of_notMem hgY _
  simp [h0]
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), (∀ ch : Matrix.unitaryGroup (Fin r) E →* ℝ, Continuous ch → (∀ g, 0 < ch g) → ∀ g, ch g = 1) ∧ ∀ M : Meas r F E, (letI := M.mU; M.μU.IsMulRightInvariant) := by
  first | exact @GlobalTheory.JR.UnitChar.posChar_trivial_and_unimodular | exact GlobalTheory.JR.UnitChar.posChar_trivial_and_unimodular | (intros; apply GlobalTheory.JR.UnitChar.posChar_trivial_and_unimodular <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) ∧ (∃ e : E, ‖e‖ ≤ 1 ∧ e + star e = 1) ∧ ∀ y : E, (∀ e : E, ‖e‖ ≤ 1 → ‖Algebra.trace F E (e * y)‖ < 1) → ‖y‖ < 1 := by
  first | exact @GlobalTheory.NTr.traceForm_perfect | exact GlobalTheory.NTr.traceForm_perfect | (intros; apply GlobalTheory.NTr.traceForm_perfect <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.TraceNondeg

theorem isNilpotent_of_trace_mul {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (w : A) (h : ∀ y : A, Algebra.trace F A (w * y) = 0) : IsNilpotent w := by
  classical
  let b := Module.finBasis F A
  have hn : IsNilpotent (Algebra.leftMulMatrix b w) := by
    apply ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow
    intro k hk _
    rw [← map_pow, ← Algebra.trace_eq_matrix_trace]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ']
    exact h _
  obtain ⟨m, hm⟩ := hn
  rw [← map_pow, ← map_zero (Algebra.leftMulMatrix b)] at hm
  exact ⟨m, Algebra.leftMulMatrix_injective b hm⟩

theorem minpoly_dvd_P {K : UQ} (B : InvAlg K) : minpoly K.E B.g ∣ B.P := by
  have h1 : minpoly K.E (Algebra.lmul K.E B.A B.g) = minpoly K.E B.g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A) (Algebra.lmul_injective) B.g
  rw [← h1]
  exact LinearMap.minpoly_dvd_charpoly _

theorem eq_zero_of_trace_mul_eq_zero : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    (∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f) →
    ∀ w : B.A, (∀ y, Algebra.trace K.E B.A (w * y) = 0) → w = 0 := by
  intro K B hP hgen w hw
  obtain ⟨m, hm⟩ := isNilpotent_of_trace_mul w hw
  obtain ⟨f, rfl⟩ := hgen w
  have hd : minpoly K.E B.g ∣ f ^ m := minpoly.dvd K.E B.g (by rw [map_pow]; exact hm)
  have hsq : Squarefree (minpoly K.E B.g) := (hP.of_dvd (minpoly_dvd_P B)).squarefree
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    rw [pow_zero] at hm
    exact (subsingleton_of_zero_eq_one hm.symm).elim _ _
  have hf : minpoly K.E B.g ∣ f := (hsq.dvd_pow_iff_dvd h0.ne').mp hd
  obtain ⟨q, rfl⟩ := hf
  rw [map_mul, minpoly.aeval, zero_mul]

end GlobalTheory.UnitLemma.TraceNondeg
end
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section
namespace GlobalTheory.UnitLemma.InvAlg.ClProd

variable {K : UQ} (B₁ B₂ : InvAlg K)

def mkU (a : B₁.Aˣ) (b : B₂.Aˣ) : (B₁.prod B₂).Aˣ where
  val := ((a : B₁.A), (b : B₂.A))
  inv := (((a⁻¹ : B₁.Aˣ) : B₁.A), ((b⁻¹ : B₂.Aˣ) : B₂.A))
  val_inv := Prod.ext a.mul_inv b.mul_inv
  inv_val := Prod.ext a.inv_mul b.inv_mul

def u₁ (x : (B₁.prod B₂).Aˣ) : B₁.Aˣ := Units.map (RingHom.fst B₁.A B₂.A).toMonoidHom x

def u₂ (x : (B₁.prod B₂).Aˣ) : B₂.Aˣ := Units.map (RingHom.snd B₁.A B₂.A).toMonoidHom x

def toPair : (B₁.prod B₂).Cl → B₁.Cl × B₂.Cl :=
  Quot.lift (fun x => (Quot.mk _ ⟨u₁ B₁ B₂ x.1, congrArg Prod.fst x.2⟩,
      Quot.mk _ ⟨u₂ B₁ B₂ x.1, congrArg Prod.snd x.2⟩)) (by
    rintro x y ⟨u, hu⟩
    refine Prod.ext (Quot.sound ⟨u₁ B₁ B₂ u, congrArg Prod.fst hu⟩)
      (Quot.sound ⟨u₂ B₁ B₂ u, congrArg Prod.snd hu⟩))

def ofPair : B₁.Cl × B₂.Cl → (B₁.prod B₂).Cl := fun p =>
  Quot.lift₂ (r := _) (s := _) (fun (a : {x : B₁.Aˣ // B₁.σ (x : B₁.A) = x})
      (b : {x : B₂.Aˣ // B₂.σ (x : B₂.A) = x}) =>
      (Quot.mk _ ⟨mkU B₁ B₂ a.1 b.1, Prod.ext a.2 b.2⟩ : (B₁.prod B₂).Cl))
    (by
      rintro a b c ⟨u, hu⟩
      exact Quot.sound ⟨mkU B₁ B₂ 1 u, Prod.ext
        (show ((a.1 : B₁.Aˣ) : B₁.A) = a.1 * (((1 : B₁.Aˣ) : B₁.A) * B₁.σ ((1 : B₁.Aˣ) : B₁.A)) by simp) hu⟩)
    (by
      rintro a b c ⟨u, hu⟩
      exact Quot.sound ⟨mkU B₁ B₂ u 1, Prod.ext hu
        (show ((c.1 : B₂.Aˣ) : B₂.A) = c.1 * (((1 : B₂.Aˣ) : B₂.A) * B₂.σ ((1 : B₂.Aˣ) : B₂.A)) by simp)⟩) p.1 p.2

def clEquiv : (B₁.prod B₂).Cl ≃ B₁.Cl × B₂.Cl where
  toFun := toPair B₁ B₂
  invFun := ofPair B₁ B₂
  left_inv := by
    intro k
    induction k using Quot.ind with
    | mk x => rfl
  right_inv := by
    rintro ⟨k₁, k₂⟩
    induction k₁ using Quot.ind with
    | mk a => induction k₂ using Quot.ind with
      | mk b => rfl

theorem card_cl_prod (K : UQ) (B₁ B₂ : InvAlg K) :
    Nat.card (B₁.prod B₂).Cl = Nat.card B₁.Cl * Nat.card B₂.Cl := by
  rw [Nat.card_congr (clEquiv B₁ B₂), Nat.card_prod]

end GlobalTheory.UnitLemma.InvAlg.ClProd
end
end

section

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem span_pow_eq_top_of_separable (K : UQ) (B : InvAlg K) (hs : B.P.Separable) :
    Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) = ⊤ := by
  classical
  have hP : B.P ≠ 0 := hs.ne_zero
  have hint : IsIntegral K.E B.g := Algebra.IsIntegral.isIntegral _
  have hz : minpoly K.E B.g ≠ 0 := minpoly.ne_zero hint
  have h0 : aeval (LinearMap.mulLeft K.E B.g) (minpoly K.E B.g) = 0 := by
    have := Polynomial.aeval_algHom_apply (Algebra.lmul K.E B.A) B.g (minpoly K.E B.g)
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hdvd : B.P ∣ minpoly K.E B.g := by
    rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP hz,
      Multiset.le_iff_subset ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP).1 hs.squarefree)]
    intro p hp
    rw [Polynomial.mem_normalizedFactors_iff hP] at hp
    rw [Polynomial.mem_normalizedFactors_iff hz]
    exact ⟨hp.1, hp.2.1, GlobalTheory.CuspGL.irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero _ _ _ hp.1 hp.2.2 h0⟩
  have hle : Module.finrank K.E B.A ≤ (minpoly K.E B.g).natDegree := by
    have h1 : B.P.natDegree = Module.finrank K.E B.A := LinearMap.charpoly_natDegree _
    rw [← h1]
    exact natDegree_le_of_dvd hdvd hz
  have hli : LinearIndependent K.E fun i : Fin (minpoly K.E B.g).natDegree => B.g ^ (i : ℕ) :=
    linearIndependent_pow B.g
  have hge := hli.fintype_card_le_finrank
  have htop := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin] at hge ⊢; omega)
  rw [eq_top_iff, ← htop]
  exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i, rfl⟩)

end GlobalTheory.UnitLemma.Unr
end
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.isReduced_of_separable_markedCharpoly : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsReduced B.A := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P | exact GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P | (intros; apply GlobalTheory.UnitLemma.InvAlg.isReduced_of_separable_P <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.StabIndex

theorem relIndex_ne_zero : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), IsLat K.O K.E L → ∀ c : K.O, c ≠ 0 →
    (∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) →
    (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  intro K B L hL c hc h
  have hfin : {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A (c * c)) L ≤ M ∧ M ≤ L}.Finite :=
    GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice K B L hL (c * c) (mul_ne_zero hc hc)
  exact relIndex_ne_zero_of_between K B L c hc hfin h

end GlobalTheory.UnitLemma.StabIndex
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable | exact GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable | (intros; apply GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable <;> assumption)
end
