module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem conv_eq_sum_of_kernels : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) {ι ι' : Type} [Fintype ι] [Fintype ι'] (c : ι → ℂ) (c' : ι' → ℂ) (ks : ι → Mat n → (E.V →L[ℂ] E.V)) (ks' : ι' → Mat n → (E.V →L[ℂ] E.V)) (k k' : Mat n → (E.V →L[ℂ] E.V)), (∀ i, KReg (ks i)) → (∀ j, KReg (ks' j)) → (∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) → (∀ y ∈ GLs n, k' y = ∑ j, c' j • ks' j y) → ∀ x ∈ GLs n, conv μ E k k' x = ∑ i, ∑ j, (c i * c' j) • conv μ E (ks i) (ks' j) x := by
  intro hL n _ _ μ _ E ι ι' _ _ c c' ks ks' k k' hks hks' hk hk' x hx
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
  have hcinv : Continuous (fun y : G n => (y⁻¹ : G n).val) := Units.continuous_val.comp continuous_inv
  have hmem : ∀ y : G n, (y⁻¹ : G n).val * x ∈ GLs n := by
    intro y
    have h1 : ((y⁻¹ : G n).val).det ≠ 0 := hval _
    change ((y⁻¹ : G n).val * x).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero h1 hx
  have hint : ∀ i j, Integrable (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) μ := by
    intro i j
    obtain ⟨hc, R, hR⟩ := hks i
    have hcont : Continuous (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) := by
      have h1 : Continuous (fun y : G n => ks i y.val) := hc.comp_continuous hcv hval
      have h2 : Continuous (fun y : G n => ks' j ((y⁻¹ : G n).val * x)) :=
        (hks' j).1.comp_continuous (hcinv.mul continuous_const) hmem
      exact h1.mul h2
    have hsupp : HasCompactSupport (fun y : G n => ks i y.val * ks' j ((y⁻¹ : G n).val * x)) := by
      refine HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_
      intro y hy
      have hy' : R < lg y.val := not_le.1 hy
      simp [hR y.val (hval y) hy']
    exact hcont.integrable_of_hasCompactSupport hsupp
  have hpt : (fun y : G n => k y.val * k' ((y⁻¹ : G n).val * x))
      = fun y : G n => ∑ i, ∑ j, (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x)) := by
    funext y
    rw [hk y.val (hval y), hk' _ (hmem y), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
  have hi : ∀ i ∈ (Finset.univ : Finset ι), Integrable
      (fun y : G n => ∑ j, (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x))) μ :=
    fun i _ => MeasureTheory.integrable_finsetSum _ fun j _ => (hint i j).smul (c i * c' j)
  unfold conv
  rw [hpt, MeasureTheory.integral_finsetSum _ hi]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hj : ∀ j ∈ (Finset.univ : Finset ι'), Integrable
      (fun y : G n => (c i * c' j) • (ks i y.val * ks' j ((y⁻¹ : G n).val * x))) μ :=
    fun j _ => (hint i j).smul (c i * c' j)
  rw [MeasureTheory.integral_finsetSum _ hj]
  exact Finset.sum_congr rfl fun j _ => integral_smul (c i * c' j) _

end GlobalTheory.CompanionTheory.WaveMult
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem integral_conv_apply_eq {Γ V : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] (μ : Measure Γ) [μ.IsHaarMeasure]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (F F' : Γ → (V →L[ℂ] V)) (φ : Γ → V) (hF : Continuous F) (hF' : Continuous F') (hφ : Continuous φ)
    (cF : HasCompactSupport F) (cF' : HasCompactSupport F') :
    ∫ z, (∫ y, F y * F' (y⁻¹ * z) ∂μ) (φ z) ∂μ = ∫ y, F y (∫ z, F' z (φ (y * z)) ∂μ) ∂μ := by
  have h1 : ∀ z, (∫ y, F y * F' (y⁻¹ * z) ∂μ) (φ z) = ∫ y, F y (F' (y⁻¹ * z) (φ z)) ∂μ := by
    intro z
    have hc : Continuous fun y => F y * F' (y⁻¹ * z) :=
      hF.mul (hF'.comp ((continuous_inv).mul continuous_const))
    have hs : HasCompactSupport fun y => F y * F' (y⁻¹ * z) :=
      HasCompactSupport.intro cF fun y hy => by
        simp [image_eq_zero_of_notMem_tsupport hy]
    have := ContinuousLinearMap.integral_apply (hc.integrable_of_hasCompactSupport (μ := μ) hs) (φ z)
    simpa using this
  simp_rw [h1]
  have hcont : Continuous (Function.uncurry fun (z y : Γ) => F y (F' (y⁻¹ * z) (φ z))) := by
    have a1 : Continuous fun p : Γ × Γ => F p.2 := hF.comp continuous_snd
    have a2 : Continuous fun p : Γ × Γ => F' (p.2⁻¹ * p.1) :=
      hF'.comp (continuous_snd.inv.mul continuous_fst)
    have a3 : Continuous fun p : Γ × Γ => φ p.1 := hφ.comp continuous_fst
    exact a1.clm_apply (a2.clm_apply a3)
  have hsupp : HasCompactSupport (Function.uncurry fun (z y : Γ) => F y (F' (y⁻¹ * z) (φ z))) := by
    have hK : IsCompact ((fun p : Γ × Γ => (p.1 * p.2, p.1)) '' (tsupport F ×ˢ tsupport F')) :=
      (IsCompact.prod cF cF').image ((continuous_fst.mul continuous_snd).prodMk continuous_fst)
    refine HasCompactSupport.intro hK ?_
    rintro ⟨z, y⟩ hzy
    by_cases hy : y ∈ tsupport F
    · by_cases hy' : y⁻¹ * z ∈ tsupport F'
      · exact absurd ⟨(y, y⁻¹ * z), ⟨hy, hy'⟩, by simp⟩ hzy
      · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy']
    · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy]
  rw [integral_integral_swap_of_hasCompactSupport hcont hsupp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change ∫ z, F y (F' (y⁻¹ * z) (φ z)) ∂μ = F y (∫ z, F' z (φ (y * z)) ∂μ)
  rw [← integral_mul_left_eq_self (fun z => F y (F' (y⁻¹ * z) (φ z))) y]
  simp only [inv_mul_cancel_left]
  have hc : Continuous fun z => F' z (φ (y * z)) :=
    hF'.clm_apply (hφ.comp (continuous_const.mul continuous_id))
  have hs : HasCompactSupport fun z => F' z (φ (y * z)) :=
    HasCompactSupport.intro cF' fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]
  exact (F y).integral_comp_comm (hc.integrable_of_hasCompactSupport (μ := μ) hs)

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  (Matrix.isUnits_det_units y).ne_zero

theorem KReg.continuous_val {n : ℕ} {V : Type} [NormedAddCommGroup V] {k : Mat n → V} (hk : KReg k) :
    Continuous fun y : G n => k y.val :=
  hk.1.comp_continuous Units.continuous_val val_mem_GLs

theorem KReg.hasCompactSupport_val (hL : LgFacts) {n : ℕ} {V : Type} [NormedAddCommGroup V] {k : Mat n → V}
    (hk : KReg k) : HasCompactSupport fun y : G n => k y.val := by
  obtain ⟨R, hR⟩ := hk.2
  refine HasCompactSupport.intro ((hL n).2.2.2.2.1 R) fun y hy => ?_
  exact hR _ (val_mem_GLs y) (not_le.1 hy)

theorem act_conv : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), KReg k → KReg k' →
    ContinuousOn f (GLs n) → ∀ x ∈ GLs n, act μ E (conv μ E k k') f x = act μ E k (act μ E k' f) x := by
  intro hL n _ _ μ _ E k k' f hk hk' hf x hx
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨X, rfl⟩ : ∃ X : G n, X.val = x :=
    (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)
  have hφ : Continuous fun z : G n => f (X.val * z.val) :=
    hf.comp_continuous (continuous_const.mul Units.continuous_val) fun z => val_mem_GLs (X * z)
  have key := integral_conv_apply_eq μ (fun y : G n => k y.val) (fun y : G n => k' y.val)
    (fun z : G n => f (X.val * z.val)) hk.continuous_val hk'.continuous_val hφ
    (hk.hasCompactSupport_val hL) (hk'.hasCompactSupport_val hL)
  simp only [Units.val_mul, ← mul_assoc] at key
  exact key

end GlobalTheory.CompanionTheory.WaveMult
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem kReg_conv : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (k k' : Mat n → (E.V →L[ℂ] E.V)), KReg k → KReg k' → KReg (conv μ E k k') := by
  intro hL n _ _ μ _ E k k' hk hk'
  obtain ⟨hsub, -, -, -, hcG, -, -⟩ := hL n
  obtain ⟨hkc, R, hR⟩ := hk
  obtain ⟨hkc', R', hR'⟩ := hk'
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hmul : ∀ a ∈ GLs n, ∀ b ∈ GLs n, a * b ∈ GLs n := fun a ha b hb => by
    change (a * b).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero ha hb
  refine ⟨?_, R + R', fun x hx hlt => ?_⟩
  · have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
    have hci : Continuous (fun y : G n => (y⁻¹ : G n).val) := hcv.comp continuous_inv
    have h1 : ContinuousOn (fun p : Mat n × G n => k p.2.val) (GLs n ×ˢ Set.univ) :=
      hkc.comp (hcv.comp continuous_snd).continuousOn (fun p _ => hval p.2)
    have h2 : ContinuousOn (fun p : Mat n × G n => k' ((p.2⁻¹ : G n).val * p.1)) (GLs n ×ˢ Set.univ) :=
      hkc'.comp ((hci.comp continuous_snd).mul continuous_fst).continuousOn
        (fun p hp => hmul _ (hval _) _ hp.1)
    have h3 : ContinuousOn (Function.uncurry fun (x : Mat n) (y : G n) => k y.val * k' ((y⁻¹ : G n).val * x))
        (GLs n ×ˢ Set.univ) := h1.clm_comp h2
    exact continuousOn_integral_of_compact_support (hcG R) h3 (fun x y _ hy => by
      have : R < lg y.val := not_le.1 hy
      simp [hR _ (hval y) this])
  · have hz : ∀ y : G n, k y.val * k' ((y⁻¹ : G n).val * x) = 0 := fun y => by
      by_cases hy : R < lg y.val
      · simp [hR _ (hval y) hy]
      · have hm : (y⁻¹ : G n).val * x ∈ GLs n := hmul _ (hval _) _ hx
        have hle := hsub _ (hval y) _ hm
        have he : y.val * ((y⁻¹ : G n).val * x) = x := by
          rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
        rw [he] at hle
        have : R' < lg ((y⁻¹ : G n).val * x) := by linarith [not_lt.1 hy]
        rw [hR' _ hm this, mul_zero]
    change ∫ y : G n, k y.val * k' ((y⁻¹ : G n).val * x) ∂μ = 0
    rw [show (fun y : G n => k y.val * k' ((y⁻¹ : G n).val * x)) = fun _ => 0 from funext hz, integral_zero]

end GlobalTheory.CompanionTheory.WaveMult
end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem act_eq_sum_of_kernel : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) {ι : Type} [Fintype ι] (c : ι → ℂ) (ks : ι → Mat n → (E.V →L[ℂ] E.V)) (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), (∀ i, KReg (ks i)) → (∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) → ContinuousOn f (GLs n) → ∀ x ∈ GLs n, act μ E k f x = ∑ i, c i • act μ E (ks i) f x := by
  intro hL n _ _ μ _ E ι _ c ks k f hks hk hf x hx
  haveI := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
  have hmul : ∀ y : G n, x * y.val ∈ GLs n := fun y => by
    have h1 : x.det ≠ 0 := hx
    have h2 : y.val.det ≠ 0 := hval y
    change (x * y.val).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero h1 h2
  have hint : ∀ i, Integrable (fun y : G n => ks i y.val (f (x * y.val))) μ := by
    intro i
    obtain ⟨hc, R, hR⟩ := hks i
    have hcont : Continuous (fun y : G n => ks i y.val (f (x * y.val))) := by
      have h1 : Continuous (fun y : G n => ks i y.val) :=
        hc.comp_continuous hcv hval
      have h2 : Continuous (fun y : G n => f (x * y.val)) :=
        hf.comp_continuous (continuous_const.mul hcv) hmul
      exact h1.clm_apply h2
    have hsupp : HasCompactSupport (fun y : G n => ks i y.val (f (x * y.val))) := by
      refine HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_
      intro y hy
      have hy' : R < lg y.val := not_le.1 hy
      simp [hR y.val (hval y) hy']
    exact hcont.integrable_of_hasCompactSupport hsupp
  unfold act
  have hpt : (fun y : G n => k y.val (f (x * y.val)))
      = fun y : G n => ∑ i, c i • ks i y.val (f (x * y.val)) := by
    funext y
    rw [hk y.val (hval y)]
    simp [ContinuousLinearMap.sum_apply]
  have hi : ∀ i ∈ (Finset.univ : Finset ι),
      Integrable (fun y : G n => c i • ks i y.val (f (x * y.val))) μ :=
    fun i _ => (hint i).smul (c i)
  rw [hpt, MeasureTheory.integral_finsetSum _ hi]
  exact Finset.sum_congr rfl (fun i _ => integral_smul (c i) _)

end GlobalTheory.CompanionTheory.WaveMult
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem act_kReg_section : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (E : KMod n) (κ : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), KReg κ →
    ContinuousOn f (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ, κ (k₁.1 * y) = E.ρ k₁ * κ y) →
    ContinuousOn (act μ E κ f) (GLs n) ∧
      ∀ x ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, act μ E κ f (x * k₂.1) = E.ρ k₂⁻¹ (act μ E κ f x) := by
  intro hL n _ _ μ _ E κ f hκ hf hleft
  obtain ⟨-, -, -, -, hcG, -, -⟩ := hL n
  obtain ⟨hkc, R, hR⟩ := hκ
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hmul : ∀ a ∈ GLs n, ∀ b ∈ GLs n, a * b ∈ GLs n := fun a ha b hb => by
    change (a * b).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero ha hb
  refine ⟨?_, fun x _ k₂ => ?_⟩
  · have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
    have h1 : ContinuousOn (fun p : Mat n × G n => κ p.2.val) (GLs n ×ˢ Set.univ) :=
      hkc.comp (hcv.comp continuous_snd).continuousOn (fun p _ => hval p.2)
    have h2 : ContinuousOn (fun p : Mat n × G n => f (p.1 * p.2.val)) (GLs n ×ˢ Set.univ) :=
      hf.comp (continuous_fst.mul (hcv.comp continuous_snd)).continuousOn
        (fun p hp => hmul _ hp.1 _ (hval _))
    have h3 : ContinuousOn (Function.uncurry fun (x : Mat n) (y : G n) => κ y.val (f (x * y.val)))
        (GLs n ×ˢ Set.univ) := h1.clm_apply h2
    exact continuousOn_integral_of_compact_support (hcG R) h3 (fun x y _ hy => by
      have : R < lg y.val := not_le.1 hy
      simp [hR _ (hval y) this])
  · have hk : k₂.1 * (k₂⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel k₂)
    have hk' : (k₂⁻¹).1 * k₂.1 = 1 := congrArg Subtype.val (inv_mul_cancel k₂)
    let g : G n := ⟨(k₂⁻¹).1, k₂.1, hk', hk⟩
    change ∫ y : G n, κ y.val (f (x * k₂.1 * y.val)) ∂μ = E.ρ k₂⁻¹ (∫ y : G n, κ y.val (f (x * y.val)) ∂μ)
    rw [← integral_mul_left_eq_self (fun y : G n => κ y.val (f (x * k₂.1 * y.val))) g]
    have hpt : ∀ y : G n, κ (g * y).val (f (x * k₂.1 * (g * y).val)) =
        E.ρ k₂⁻¹ (κ y.val (f (x * y.val))) := fun y => by
      have e1 : (g * y).val = (k₂⁻¹).1 * y.val := rfl
      have e2 : x * k₂.1 * ((k₂⁻¹).1 * y.val) = x * y.val := by
        rw [mul_assoc, ← mul_assoc k₂.1, hk, one_mul]
      rw [e1, e2, hleft _ (hval y) k₂⁻¹]
      rfl
    simp_rw [hpt]
    exact (E.ρ k₂⁻¹).integral_comp_comm'
      (AddMonoidHomClass.isometry_of_norm (E.ρ k₂⁻¹) (E.iso _)).antilipschitz _

end GlobalTheory.CompanionTheory.WaveMult
end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem continuousOn_inv_GLs {n : ℕ} : ContinuousOn (fun y : Mat n => y⁻¹) (GLs n) := by
  have h : (fun y : Mat n => y⁻¹) = fun y => (y.det)⁻¹ • y.adjugate := by
    funext y
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact ((continuous_id.matrix_det).continuousOn.inv₀ (fun y hy => hy)).smul
    (continuous_id.matrix_adjugate).continuousOn

theorem unitary_matrix_inv {n : ℕ} (k : Matrix.unitaryGroup (Fin n) ℂ) :
    (k.1 : Mat n)⁻¹ = (k⁻¹).1 := by
  apply Matrix.inv_eq_left_inv
  have := congrArg Subtype.val (inv_mul_cancel k)
  simpa using this

theorem adjoint_rho_inv {n : ℕ} (E : KMod n) [CompleteSpace E.V] (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ContinuousLinearMap.adjoint (E.ρ k⁻¹) = E.ρ k := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  let f : E.V →ₗᵢ[ℂ] E.V := ⟨(E.ρ k : E.V →L[ℂ] E.V).toLinearMap, E.iso k⟩
  have h1 : E.ρ k (E.ρ k⁻¹ y) = y := by
    have : E.ρ k * E.ρ k⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun T : E.V →L[ℂ] E.V => T y) this
  have h2 := f.inner_map_map x (E.ρ k⁻¹ y)
  have h3 : f (E.ρ k⁻¹ y) = y := h1
  rw [h3] at h2
  exact h2

theorem adjoint_kernel_reg : LgFacts → ∀ (n : ℕ) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)), KReg k → (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) → (haveI := FiniteDimensional.complete ℂ E.V; KReg (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) ∧ ∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, ContinuousLinearMap.adjoint (k (k₁.1 * y * k₂.1)⁻¹) = E.ρ k₁ * ContinuousLinearMap.adjoint (k y⁻¹) * E.ρ k₂) := by
  intro hL n E k hk heq
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨hc, R, hR⟩ := hk
  refine ⟨⟨?_, R, ?_⟩, ?_⟩
  · have hinv : ContinuousOn (fun y : Mat n => k y⁻¹) (GLs n) :=
      hc.comp continuousOn_inv_GLs (fun y hy => inv_mem_GLs hy)
    exact (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E.V) (F := E.V)).continuous.comp_continuousOn hinv
  · intro y hy hlt
    have h1 : lg y⁻¹ = lg y := (hL n).2.1 y hy
    have h2 : k y⁻¹ = 0 := hR _ (inv_mem_GLs hy) (by rw [h1]; exact hlt)
    simp [h2]
  · intro y hy k₁ k₂
    have h1 : ((k₁.1 : Mat n) * y * k₂.1)⁻¹ = (k₂⁻¹).1 * y⁻¹ * (k₁⁻¹).1 := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, unitary_matrix_inv, unitary_matrix_inv, mul_assoc]
    rw [h1, heq _ (inv_mem_GLs hy)]
    have h2 : ContinuousLinearMap.adjoint (E.ρ k₂⁻¹ * k y⁻¹ * E.ρ k₁⁻¹)
        = ContinuousLinearMap.adjoint (E.ρ k₁⁻¹) * ContinuousLinearMap.adjoint (k y⁻¹)
          * ContinuousLinearMap.adjoint (E.ρ k₂⁻¹) := by
      simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp]
      rfl
    rw [h2, adjoint_rho_inv, adjoint_rho_inv]

end GlobalTheory.CompanionTheory.WaveMult
end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem lg_le_lg_mul_add (hL : LgFacts) {n : ℕ} {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) :
    lg x ≤ lg (x * y) + lg y := by
  have hdx : x.det ≠ 0 := hx
  have hdy : y.det ≠ 0 := hy
  have hxy : x * y ∈ GLs n := by
    change (x * y).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hdx hdy
  have hu : IsUnit y.det := isUnit_iff_ne_zero.mpr hdy
  have h1 := (hL n).1 (x * y) hxy y⁻¹ (inv_mem_GLs hy)
  have h2 := (hL n).2.1 y hy
  rw [Matrix.mul_nonsing_inv_cancel_right _ _ hu, h2] at h1
  exact h1

theorem wave_cpt_bounded_time : LgFacts → WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V),
    IsWave E u → Cpt (u 0) → ∀ T : ℝ, ∃ R : ℝ, ∀ t, |t| ≤ T → ∀ y ∈ GLs n, R < lg y → u t y = 0 := by
  intro hL hS n E u hu hc T
  obtain ⟨c, hc'⟩ := hS n
  obtain ⟨R₀, hR₀⟩ := hc
  refine ⟨R₀ + |c| * (1 + |T|), fun t ht x hx hlg => hc' E u hu t x hx fun y hy hly => ?_⟩
  have hxy : x * y ∈ GLs n := by
    change (x * y).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hx hy
  refine hR₀ (x * y) hxy ?_
  have h1 := lg_le_lg_mul_add hL hx hy
  have h2 : |t| ≤ |T| := ht.trans (le_abs_self T)
  have h3 : c * (1 + |t|) ≤ |c| * (1 + |T|) :=
    calc c * (1 + |t|) ≤ |c| * (1 + |t|) :=
          mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
      _ ≤ |c| * (1 + |T|) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg c)
  linarith

end GlobalTheory.CompanionTheory.WaveMult
end
end
