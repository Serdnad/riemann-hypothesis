module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
public import GroundTheory.AutomorphicForms.RealGroupsHaar
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle202
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.MapWXi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle171
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle170
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle172
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle208
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle174
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
import GroundTheory.PAdicHodge.ACrisBdRGalois
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Basic
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL

noncomputable section

namespace GlobalTheory.CompanionTheory.SobGL.HaarDom

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem isOpenEmbedding_valG (n : ℕ) : Topology.IsOpenEmbedding (Units.val : G n → Mat n) :=
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  Units.isOpenEmbedding_val

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def coords {n : ℕ} (M : Mat n) : Idx n → ℝ :=
  fun p => if p.1 then (M p.2.1 p.2.2).re else (M p.2.1 p.2.2).im

theorem cm_apply {n : ℕ} (t : Idx n → ℝ) (i j : Fin n) :
    cm t i j = (t (true, i, j) : ℂ) + (t (false, i, j) : ℂ) * Complex.I := by
  simp only [cm, bs, Matrix.sum_apply, Matrix.smul_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  have key : ∀ f : Fin n → Fin n → ℂ, (∑ x, ∑ y, if x = i ∧ y = j then f x y else 0) = f i j := by
    intro f
    simp [ite_and, Finset.sum_ite_eq']
  simp [Matrix.single_apply, Finset.sum_add_distrib, key]

def cmE (n : ℕ) : (Idx n → ℝ) ≃ₗ[ℝ] Mat n where
  toFun := cm
  map_add' s t := by simp [cm, add_smul, Finset.sum_add_distrib]
  map_smul' c t := by simp [cm, mul_smul, Finset.smul_sum]
  invFun := coords
  left_inv t := by
    funext ⟨b, i, j⟩
    cases b <;> simp [coords, cm_apply]
  right_inv M := by
    ext i j
    simp [coords, cm_apply, Complex.re_add_im]

instance locallyCompactSpace_G (n : ℕ) : LocallyCompactSpace (G n) :=
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  (isOpenEmbedding_valG n).locallyCompactSpace
instance secondCountableTopology_G (n : ℕ) : SecondCountableTopology (G n) :=
  haveI : SecondCountableTopology (Mat n) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  (isOpenEmbedding_valG n).isEmbedding.secondCountableTopology

def aH (n : ℕ) : (Idx n → ℝ) ≃ₜ Mat n :=
  (cmE n).toContinuousLinearEquiv.toHomeomorph.trans (Homeomorph.addLeft (1 : Mat n))

open scoped GroundTheory.Automorphic ENNReal

attribute [local instance 2000] _root_.Units.instMeasurableSpace

def mu0 (n : ℕ) : Measure (Mat n) := Measure.map (cmE n) volume

instance isAddHaarMeasure_pushforward (n : ℕ) : (mu0 n).IsAddHaarMeasure :=
  (cmE n).toContinuousLinearEquiv.isAddHaarMeasure_map volume

theorem map_aH (n : ℕ) : Measure.map (aH n) volume = mu0 n := by
  have h1 : Measurable (cmE n) := (cmE n).toContinuousLinearEquiv.continuous.measurable
  have h2 : Measurable (fun x : Mat n => (1 : Mat n) + x) := (continuous_const.add continuous_id).measurable
  have : (aH n : (Idx n → ℝ) → Mat n) = (fun x : Mat n => (1 : Mat n) + x) ∘ (cmE n) := rfl
  rw [this, ← Measure.map_map h2 h1]
  exact map_add_left_eq_self (mu0 n) 1

theorem lint_chart {n : ℕ} (g : Mat n → ℝ≥0∞) (Q : Set (Idx n → ℝ)) :
    ∫⁻ t in Q, g (1 + cm t) = ∫⁻ x in aH n '' Q, g x ∂(mu0 n) := by
  have hemb := (aH n).measurableEmbedding
  rw [← map_aH, hemb.restrict_map, hemb.lintegral_map,
    Set.preimage_image_eq _ (aH n).injective]
  rfl

theorem lint_haar {n : ℕ} (g : Mat n → ℝ≥0∞) (S : Set (G n)) (hS : MeasurableSet S) :
    ∫⁻ y in S, g y.val ∂(GroundTheory.Automorphic.haarGLComplex (mu0 n)) =
      ∫⁻ x in Units.val '' S, GroundTheory.Automorphic.haarDensityGLComplex x * g x ∂(mu0 n) := by
  have hemb := GroundTheory.Automorphic.measurableEmbedding_val_GLComplex (n := Fin n)
  have hV : Measure.map Units.val ((GroundTheory.Automorphic.haarGLComplex (mu0 n)).restrict S) =
      ((mu0 n).restrict (Units.val '' S)).withDensity GroundTheory.Automorphic.haarDensityGLComplex := by
    have hVm : MeasurableSet (Units.val '' S) := hemb.measurableSet_image.2 hS
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, Measure.restrict_apply (hemb.measurable hs),
      GroundTheory.Automorphic.haarGLComplex_apply, ← restrict_withDensity hVm,
      Measure.restrict_apply hs, Set.image_preimage_inter]
  rw [← hemb.lintegral_map, hV,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      GroundTheory.Automorphic.measurable_haarDensityGLComplex
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  rfl

theorem lint_core {n : ℕ} (g : Mat n → ℝ≥0∞) (Q : Set (Idx n → ℝ)) (S : Set (G n)) (hS : IsCompact S)
    (h : ∀ t ∈ Q, ∃ y ∈ S, y.val = 1 + cm t) (B : ℝ) (hB0 : 0 < B)
    (hB : ∀ y ∈ S, (‖(y : Mat n).det‖ ^ 2) ^ n ≤ B) :
    ∫⁻ t in Q, g (1 + cm t) ≤
      ENNReal.ofReal B * ∫⁻ y in S, g y.val ∂(GroundTheory.Automorphic.haarGLComplex (mu0 n)) := by
  have hV : MeasurableSet (Units.val '' S) :=
    (hS.image Units.continuous_val).isClosed.measurableSet
  rw [lint_chart, lint_haar g S hS.measurableSet, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ∫⁻ x in aH n '' Q, g x ∂(mu0 n) ≤ ∫⁻ x in Units.val '' S, g x ∂(mu0 n) := by
        refine lintegral_mono_set ?_
        rintro _ ⟨t, ht, rfl⟩
        obtain ⟨y, hy, e⟩ := h t ht
        exact ⟨y, hy, e⟩
    _ ≤ _ := by
        refine setLIntegral_mono' hV ?_
        rintro _ ⟨y, hy, rfl⟩
        have hd : (y : Mat n).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
        have hpos : 0 < (‖(y : Mat n).det‖ ^ 2) ^ n := by positivity
        have h1 : 1 ≤ ENNReal.ofReal B * GroundTheory.Automorphic.haarDensityGLComplex (y : Mat n) := by
          rw [GroundTheory.Automorphic.haarDensityGLComplex, ← ENNReal.ofReal_mul hB0.le,
            ← ENNReal.ofReal_one]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [Fintype.card_fin, inv_pow, ← div_eq_mul_inv, one_le_div hpos]
          exact hB y hy
        calc g y.val = 1 * g y.val := (one_mul _).symm
          _ ≤ (ENNReal.ofReal B * GroundTheory.Automorphic.haarDensityGLComplex (y : Mat n)) * g y.val := by
              gcongr
          _ = _ := mul_assoc _ _ _

theorem dom_units (n : ℕ) (μ : Measure (G n)) [μ.IsHaarMeasure]
    (Q : Set (Idx n → ℝ)) (S : Set (G n)) (hQ : IsCompact Q) (hS : IsCompact S)
    (h : ∀ t ∈ Q, ∃ y ∈ S, y.val = 1 + cm t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Mat n → ℝ, ContinuousOn φ (GLs n) → (∀ y, 0 ≤ φ y) →
      ∫ t in Q, φ (1 + cm t) ≤ C * ∫ y in S, φ y.val ∂μ := by
  have hH := Measure.isMulLeftInvariant_eq_smul (GroundTheory.Automorphic.haarGLComplex (mu0 n)) μ
  set κ := Measure.haarScalarFactor (GroundTheory.Automorphic.haarGLComplex (mu0 n)) μ with hκ
  have hcont : Continuous (fun y : G n => (‖(y : Mat n).det‖ ^ 2) ^ n) :=
    (((Units.continuous_val.matrix_det).norm.pow _).pow _)
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hcont.continuousOn
  have hB1 : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hB2 : ∀ y ∈ S, (‖(y : Mat n).det‖ ^ 2) ^ n ≤ max B 1 := fun y hy =>
    ((le_abs_self _).trans (by simpa using hB y hy)).trans (le_max_left _ _)
  refine ⟨max B 1 * κ, by positivity, fun φ hφ h0 => ?_⟩
  have hmem : ∀ y : G n, (y : Mat n) ∈ GLs n := fun y =>
    ((isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
  have hf : Continuous (fun y : G n => φ y.val) :=
    hφ.comp_continuous Units.continuous_val hmem
  have hint2 : IntegrableOn (fun y : G n => φ y.val) S μ := hf.continuousOn.integrableOn_compact hS
  have hint1 : IntegrableOn (fun t => φ (1 + cm t)) Q := by
    refine ContinuousOn.integrableOn_compact hQ ?_
    refine hφ.comp (aH n).continuous.continuousOn ?_
    intro t ht
    obtain ⟨y, _, e⟩ := h t ht
    show 1 + cm t ∈ GLs n
    rw [← e]
    exact hmem y
  have key := lint_core (fun x => ENNReal.ofReal (φ x)) Q S hS h (max B 1) hB1 hB2
  rw [hH, Measure.restrict_smul, lintegral_smul_measure,
    ← ofReal_integral_eq_lintegral_ofReal hint1 (ae_of_all _ fun _ => h0 _),
    ← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun _ => h0 _)] at key
  have hR : 0 ≤ ∫ y in S, φ y.val ∂μ := integral_nonneg fun _ => h0 _
  have e : ENNReal.ofReal (max B 1) * κ • ENNReal.ofReal (∫ y in S, φ y.val ∂μ) =
      ENNReal.ofReal (max B 1 * κ * ∫ y in S, φ y.val ∂μ) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hB1.le, ENNReal.smul_def,
      ENNReal.ofReal_coe_nnreal, smul_eq_mul, mul_assoc]
  rw [e] at key
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key

end GlobalTheory.CompanionTheory.SobGL.HaarDom

namespace GlobalTheory.CompanionTheory.SobGL


open scoped GroundTheory.Automorphic in
theorem lebesgue_le_haar :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (Q : Set (Idx n → ℝ)) (S : Set (G n)), IsCompact Q → IsCompact S → (∀ t ∈ Q, ∃ y ∈ S, y.val = 1 + cm t) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Mat n → ℝ, ContinuousOn φ (GLs n) → (∀ y, 0 ≤ φ y) →
      ∫ t in Q, φ (1 + cm t) ≤ C * ∫ y in S, φ y.val ∂μ := by
  intro n m hB μ hμ Q S hQ hS h
  letI : MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) :=
    GroundTheory.Automorphic.matrixMeasurableSpaceComplex
  have e : m = Units.instMeasurableSpace := by
    exact hB.measurable_eq.trans
      (GroundTheory.Automorphic.borelSpace_GLComplex (n := Fin n)).measurable_eq.symm
  subst e
  exact HaarDom.dom_units n μ Q S hQ hS h

end GlobalTheory.CompanionTheory.SobGL
end
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem sharp_sub_mem_span_l_iff {l : ℕ} [Fact l.Prime] (A : PAlg l) (a b : A.A) :
    A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} ↔ a - b ∈ Ideal.span {A.pi} := by
  have key : ∀ x y : A.U, (Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) x =
      Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) y) ↔ x - y ∈ Ideal.span {(l : A.U)} := by
    intro x y
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, pow_one]
  rw [← (GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker A).2, RingHom.mem_ker, map_sub, sub_eq_zero,
    CrystallineSemistableComparison.PAlg.sharpMap_eq, CrystallineSemistableComparison.PAlg.sharpMap_eq]
  exact (key _ _).symm

theorem idem_pow {R : Type*} [CommRing R] {x : R} (h : IsIdempotentElem x) {k : ℕ} (hk : k ≠ 0) :
    x ^ k = x := by
  cases k with
  | zero => exact absurd rfl hk
  | succ n =>
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, ih (Nat.succ_ne_zero _), h.eq]

private theorem eq_zero_of_isIdempotentElem_of_mem_span_prime {l : ℕ} [Fact l.Prime] (A : PAlg l) {w : A.U}
    (hw : IsIdempotentElem w) (hl : w ∈ Ideal.span {(l : A.U)}) : w = 0 := by
  apply IsHausdorff.haus (GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U A).toIsHausdorff w
  intro n
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  cases n with
  | zero => simp
  | succ m =>
    have hp := Ideal.pow_mem_pow hl (m + 1)
    rwa [idem_pow hw (Nat.succ_ne_zero m)] at hp

theorem sharp_one_sub {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.A) (he : IsIdempotentElem e) :
    A.sharp (1 - e) = 1 - A.sharp e := by
  have h0 : A.sharp 0 = 0 := by
    apply eq_zero_of_isIdempotentElem_of_mem_span_prime A
    · show A.sharp 0 * A.sharp 0 = A.sharp 0
      rw [← map_mul, mul_zero]
    · rw [Ideal.mem_span_singleton]
      refine ⟨A.sharp 0, ?_⟩
      rw [← CrystallineSemistableComparison.PAlg.sharp_pi A, ← map_mul A.sharp, mul_zero]
  have hu : IsIdempotentElem (A.sharp e) := by
    show A.sharp e * A.sharp e = A.sharp e
    rw [← map_mul, he.eq]
  have hv : IsIdempotentElem (A.sharp (1 - e)) := by
    have h1e : (1 - e) * (1 - e) = 1 - e := by linear_combination he.eq
    show A.sharp (1 - e) * A.sharp (1 - e) = A.sharp (1 - e)
    rw [← map_mul, h1e]
  have huv : A.sharp e * A.sharp (1 - e) = 0 := by
    rw [← map_mul, mul_sub, mul_one, he.eq, sub_self, h0]
  have hw : IsIdempotentElem (1 - A.sharp e - A.sharp (1 - e)) := by
    show (1 - A.sharp e - A.sharp (1 - e)) * (1 - A.sharp e - A.sharp (1 - e)) =
      1 - A.sharp e - A.sharp (1 - e)
    linear_combination hu.eq + hv.eq + 2 * huv
  have hl : 1 - A.sharp e - A.sharp (1 - e) ∈ Ideal.span {(l : A.U)} := by
    have h1 : A.aToU1 1 - A.aToU1 e - A.aToU1 (1 - e) = 0 := by
      rw [← map_sub, sub_self]
    rw [CrystallineSemistableComparison.PAlg.sharpMap_eq, CrystallineSemistableComparison.PAlg.sharpMap_eq, CrystallineSemistableComparison.PAlg.sharpMap_eq, map_one] at h1
    have h2 : Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) (1 - A.sharp e - A.sharp (1 - e)) = 0 := by
      rw [map_sub, map_sub]
      exact h1
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one] at h2
    exact h2
  have hw0 := eq_zero_of_isIdempotentElem_of_mem_span_prime A hw hl
  linear_combination -hw0

theorem sharp_congruences : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l),
    (∀ (a b : A.A) (n : ℕ), a - b ∈ Ideal.span {A.pi} →
      A.sharp (a ^ l ^ n) - A.sharp (b ^ l ^ n) ∈ Ideal.span {(l : A.U) ^ (n + 1)}) ∧
    (∀ a b : A.A, A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} ↔ a - b ∈ Ideal.span {A.pi}) ∧
    ∀ e : A.A, IsIdempotentElem e → A.sharp (1 - e) = 1 - A.sharp e := by
  intro l _ A
  refine ⟨?_, fun a b => sharp_sub_mem_span_l_iff A a b, fun e he => sharp_one_sub A e he⟩
  intro a b n hab
  have h1 : A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} := (sharp_sub_mem_span_l_iff A a b).mpr hab
  rw [Ideal.mem_span_singleton] at h1 ⊢
  rw [map_pow, map_pow]
  exact dvd_sub_pow_of_dvd_sub h1 n

end GlobalTheory.CompanionTheory.Untilt
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.untilt_adic_complete : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), IsAdicComplete (Ideal.span {(l : A.U)}) A.U := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U | exact GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U | (intros; apply GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrCech.Omega
open GlobalTheory.CompanionTheory.GrForm GlobalTheory.CompanionTheory.GrVB

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem evLift_mul_sub {W : X.Opens} {P : ObjectProperty (Thick (LL q))} (hP : ∀ T, P T → InU W T) (z x : Γ(X, W))
    (T : P.FullSubcategory) :
    (show T.obj.B from evLift hP z T) * lft W T.obj x - lft W T.obj (z * x) ∈ T.obj.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [map_mul, mk_evLift, lft_spec _ (hP _ T.property), lft_spec _ (hP _ T.property), map_mul]

theorem rp_fAct {W : X.Opens} {P : ObjectProperty (Thick (LL q))} (hF : IsFil (sP P) (sFil P))
    (hP : ∀ T, P T → InU W T) {d r : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) (z : Γ(X, W)) (x : Idx r d → Γ(X, W)) (c : HU (GF q r) P r)
    (hc : Rp (W := W) P u x c) : Rp (W := W) P u (fun I => z * x I) (fAct hF hP r z c) := by
  obtain ⟨f, hf, rfl, hfs⟩ := hc
  refine ⟨(mulMor hF r (evLift hP z) (evLift_nat hP z)).pullC r f, ?_, rfl, ?_⟩
  · rw [CH.Mor.d_pullC, hf, map_zero]
  · intro s
    let uu : Fin d → ∀ T : P.FullSubcategory, (sP P).A.obj T := fun i T => u i T.obj
    have hl : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'), uu i T' - ((sP P).A.map φ).hom (uu i T) ∈ (sP P).J.S T' :=
      fun i {T T'} φ => sub_mem_of_lift φ.hom (hP _ T.property) (hP _ T'.property) (t i) _ _
        (hu i _ (hP _ T.property)) (hu i _ (hP _ T'.property))
    change Ideal.Quotient.mk _ (show (sP P).A.obj (s.obj (Fin.last r)) from evLift hP z (s.obj (Fin.last r))) *
      (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f s).1 = _
    rw [hfs s, ← map_mul, Ideal.Quotient.eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    have hw := wz_mem hF uu hl I.1 s
    have := J_mul_sFil P r _ (evLift_mul_sub hP z (x I) (s.obj (Fin.last r))) hw
    have e := units_mul_relation_rearrange_commRing (S := (sP P).A.obj (s.obj (Fin.last r)))
      (evLift hP z (s.obj (Fin.last r))) (wz uu I.1 s) (lft W (s.obj (Fin.last r)).obj (x I))
      (lft W (s.obj (Fin.last r)).obj (z * x I))
    exact Eq.mpr (congrArg (fun v => v ∈ (sFil P ((r : ℤ) + 1)).S (s.obj (Fin.last r))) e) this

theorem basis : KH.LocGr → KH.PolyTf → ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {W₀ : X.Opens} {d : ℕ}
    (c : Coord q W₀ d) (r : ℕ) (hr : r < s),
    ∃ ω : Idx r d → HU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) (St (TF l s) {W₀}) r,
      ∀ (W : X.Opens) (hW : IsAffineOpen W) (hle : W ≤ W₀) (Q : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))))
        (hQ : Q = St (TF l s) {W}) (hQ₀ : Q ≤ St (TF l s) {W₀}) (hF : IsFil (sP Q) (sFil Q)) (hQW : ∀ T, Q T → InU W T)
        (h : HU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) Q r),
        ∃! f : Idx r d → Γ(X, W), h = ∑ k, GlobalTheory.CompanionTheory.GrCech.fAct hF hQW r (f k) ((resU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) hQ₀).pull r (ω k)) := by
  classical
  intro hLoc hPoly O _ l s hb X q W₀ d c r hr
  have hL : StLoc := stLoc stFrame hLoc hPoly
  have hE : StExists := exists_of_cocycle stCocycle
  let u : Fin d → ∀ T : Thick (LL q), T.B := fun k T => lft W₀ T (c.t k)
  have hu : IsLift W₀ c.t u := fun k T h => lft_spec T h _
  choose ω hω using fun k : Idx r d => hE W₀ c.t u hu (SS q l s W₀) (ss_inU l s W₀) r (Pi.single k 1)
  refine ⟨ω, ?_⟩
  intro W hW hle Q hQ hQ₀ hF hQW h
  have hFree : Free W Q r u := free_at hL hb hle hW c hu hr hQ
  have hu' : IsLift W (fun i => rs hle (c.t i)) u := isLift_res hle hu fun _ => rfl
  have hrep : ∀ f : Idx r d → Γ(X, W), Rp (W := W) Q u f
      (∑ k, fAct hF hQW r (f k) ((resU (GF q r) hQ₀).pull r (ω k))) := by
    intro f
    have s1 := rp_sum hE stAdd hu' hQW Finset.univ
      (fun k I => f k * rs hle ((Pi.single k 1 : Idx r d → Γ(X, W₀)) I)) _
      (fun k _ => rp_fAct hF hQW hu' (f k) _ _
        (stRes W₀ W hle c.t u hu (SS q l s W₀) Q hQ₀ (ss_inU l s W₀) hQW r _ _ (hω k)))
    have e : (∑ k, fun I => f k * rs hle ((Pi.single k 1 : Idx r d → Γ(X, W₀)) I)) = f := by
      funext I
      rw [Finset.sum_apply, Finset.sum_eq_single I]
      · simp
      · intro b _ hb'
        simp [Pi.single_eq_of_ne (Ne.symm hb')]
      · simp
    rwa [e] at s1
  obtain ⟨x, hx⟩ := hFree.1 h
  refine ⟨x, rp_class hx (hrep x), fun y hy => ?_⟩
  have hy' : Rp (W := W) Q u y h := by
    rw [hy]
    exact hrep y
  exact rp_coef stAdd hu' hQW hFree hy' hx

end GlobalTheory.CompanionTheory.GrCech.Omega
end
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem lev_toB_ker {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ) :
    ∀ x : (per l K).P, (lev h k).toB x = 0 ↔ ∃ y : (per l K).P, (x : (per l K).B) = (per l K).tB ^ k * y := by
  have ht : (per l K).tB = algebraMap (BdRp l) (BdR l) (tBdR l) := by
    change DeRhamPotentiallySemistable.DRPst.iC l (tA l) = _
    change algebraMap (BdRp l) (BdR l) (ACris.iota ℂ_[l] l (tA l)) = _
    rw [show ACris.iota ℂ_[l] l (tA l) = tBdR l from ACris.iota_periodT (untilt_epsilon (p := l))]
  have hinj : Function.Injective (algebraMap (BdRp l) (BdR l)) :=
    IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
  have hp : ∀ x : ↥(algebraMap (BdRp l) (BdR l)).range, algebraMap (BdRp l) (BdR l) (pInv l x) = x := by
    intro x
    obtain ⟨z, hz⟩ := x.2
    have : pInv l x = z := by
      apply (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
        ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_eq.2
      exact Subtype.ext hz.symm
    rw [this, hz]
  intro x
  change pk l k (pInv l x) = 0 ↔ _
  rw [pk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨⟨algebraMap (BdRp l) (BdR l) z, z, rfl⟩, ?_⟩
    have := hp x
    rw [← hz, map_mul, map_pow, mul_comm] at this
    rw [ht]
    exact this.symm
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := y.2
    refine ⟨z, hinj ?_⟩
    rw [map_mul, map_pow, mul_comm, hp x, hz]
    rw [ht] at hy
    exact hy.symm

end GlobalTheory.CompanionTheory.LatC
end

section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem gP_kP {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (g : K.fixingSubgroup) (x : K) : gP l g (kP l K x) = kP l K x := by
  have h1 : (toBot g.1) • algClToBdR l (K.val x) = algClToBdR l ((toBot g.1) (K.val x)) :=
    gal_smul_algClToBdR _ _
  have h2 : (toBot g.1) (K.val x) = K.val x := (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ x.2
  rw [h2] at h1
  exact h1

theorem sigA_fix : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g (a : OK l K), (lev h k).σA g (algebraMap (OK l K) (lev h k).A a) = algebraMap (OK l K) (lev h k).A a := by
  intro l _ K M h k g a
  apply ι_injective (fk l k) (xi0 l) l M
  show gB h k g (pk l k (kP l K a)) = pk l k (kP l K a)
  show Ideal.quotientMap _ (gP l g) (h.galT k g) (Ideal.Quotient.mk _ (kP l K a)) = _
  rw [Ideal.quotientMap_mk, gP_kP]
  rfl

end GlobalTheory.CompanionTheory.LatC
end
