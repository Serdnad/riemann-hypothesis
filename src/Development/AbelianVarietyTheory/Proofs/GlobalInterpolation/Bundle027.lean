module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Mathlib.RingTheory.PowerSeries.Basic
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
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
  GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal Pointwise

namespace GlobalTheory.QuadricHaar

theorem exists_const {G H X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H]
    [BorelSpace H] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (a : G → X → X) (a_mul : ∀ g h x, a (g * h) x = a g (a h x)) (a_one : ∀ x, a 1 x = x)
    (a_meas : ∀ g, Measurable (a g)) (x₀ : X) (a_cont : Continuous fun g => a g x₀)
    (S : X → Prop) (j : H →* G) (ν : Measure X) (μ : Measure G) (μ' : Measure H)
    (hj : IsClosedEmbedding j) (hr : Set.range j = {g | a g x₀ = x₀})
    [IsFiniteMeasureOnCompacts ν] (hS : ∀ᵐ y ∂ν, S y) (hν : ∀ g, ν.map (a g) = ν)
    [μ.IsHaarMeasure] [μ'.IsHaarMeasure] :
    ∃ κ : ℝ≥0, ∀ s : X → G, (Measurable s ∧ ∀ y, S y → a (s y) x₀ = y) →
      ∀ f : G → ℝ≥0∞, Measurable f →
        ∫⁻ y, (∫⁻ g', f (s y * j g') ∂μ') ∂ν = κ * ∫⁻ g, f g ∂μ := by
  by_cases hex : ∃ s : X → G, Measurable s ∧ ∀ y, S y → a (s y) x₀ = y
  swap
  · exact ⟨0, fun s hs => (hex ⟨s, hs⟩).elim⟩
  obtain ⟨s₀, hs₀, hs₀'⟩ := hex
  have hjm : Measurable j := hj.continuous.measurable
  have key : ∀ (f : G → ℝ≥0∞) (b c : G), a b x₀ = a c x₀ →
      ∫⁻ g', f (b * j g') ∂μ' = ∫⁻ g', f (c * j g') ∂μ' := by
    intro f b c h
    have : b⁻¹ * c ∈ Set.range j := by
      rw [hr]
      change a (b⁻¹ * c) x₀ = x₀
      rw [a_mul, ← h, ← a_mul, inv_mul_cancel, a_one]
    obtain ⟨k, hk⟩ := this
    rw [← lintegral_mul_left_eq_self (fun g' => f (b * j g')) k]
    refine lintegral_congr fun g' => ?_
    rw [map_mul, hk, ← mul_assoc, mul_inv_cancel_left]
  have hp : Measurable fun p : X × H => s₀ p.1 * j p.2 :=
    (hs₀.comp measurable_fst).mul (hjm.comp measurable_snd)
  set m : Measure G := (ν.prod μ').map fun p : X × H => s₀ p.1 * j p.2 with hm
  have hint : ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ g, f g ∂m = ∫⁻ y, (∫⁻ g', f (s₀ y * j g') ∂μ') ∂ν := by
    intro f hf
    rw [hm, lintegral_map hf hp]
    exact lintegral_prod _ (hf.comp hp).aemeasurable
  have hmeas : ∀ f : G → ℝ≥0∞, Measurable f →
      Measurable fun y => ∫⁻ g', f (s₀ y * j g') ∂μ' := fun f hf =>
    (hf.comp hp).lintegral_prod_right'
  haveI : m.IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    refine Measure.ext_of_lintegral _ fun f hf => ?_
    rw [lintegral_map hf (measurable_const_mul h),
      hint (fun g => f (h * g)) (hf.comp (measurable_const_mul h)), hint f hf]
    have e : ∫⁻ y, (∫⁻ g', f (s₀ y * j g') ∂μ') ∂ν =
        ∫⁻ y, (∫⁻ g', f (s₀ (a h y) * j g') ∂μ') ∂ν := by
      conv_lhs => rw [← hν h]
      rw [lintegral_map (hmeas f hf) (a_meas h)]
    rw [e]
    have hS' : ∀ᵐ y ∂ν, S (a h y) := by
      refine ae_of_ae_map (p := S) (a_meas h).aemeasurable ?_
      rw [hν h]; exact hS
    refine lintegral_congr_ae ?_
    filter_upwards [hS, hS'] with y h1 h2
    rw [← key f (h * s₀ y) _ (by rw [a_mul, hs₀' y h1, hs₀' _ h2])]
    simp only [mul_assoc]
  haveI : IsFiniteMeasureOnCompacts m := by
    refine ⟨fun K hK => ?_⟩
    have hKm : MeasurableSet K := hK.measurableSet
    have hL : IsCompact ((fun g => a g x₀) '' K) := hK.image a_cont
    have hC : IsCompact (j ⁻¹' (K⁻¹ * K)) := hj.isCompact_preimage (hK.inv.mul hK)
    rw [← lintegral_indicator_one hKm, hint _ (measurable_one.indicator hKm)]
    have hle : ∀ᵐ y ∂ν, ∫⁻ g', K.indicator (1 : G → ℝ≥0∞) (s₀ y * j g') ∂μ' ≤
        ((fun g => a g x₀) '' K).indicator (fun _ => μ' (j ⁻¹' (K⁻¹ * K))) y := by
      filter_upwards [hS] with y hy
      by_cases hyL : y ∈ (fun g => a g x₀) '' K
      · rw [Set.indicator_of_mem hyL]
        obtain ⟨b, hb, hby⟩ := hyL
        rw [key _ (s₀ y) b (by rw [hs₀' y hy]; exact hby.symm),
          ← lintegral_indicator_one hC.measurableSet]
        refine lintegral_mono fun g' => ?_
        by_cases hg : b * j g' ∈ K
        · have : g' ∈ j ⁻¹' (K⁻¹ * K) :=
            ⟨b⁻¹, by simpa using hb, b * j g', hg, by simp⟩
          simp [Set.indicator_of_mem hg, Set.indicator_of_mem this]
        · simp [Set.indicator_of_notMem hg]
      · rw [Set.indicator_of_notMem hyL]
        refine le_of_eq ((lintegral_congr fun g' => ?_).trans lintegral_zero)
        refine Set.indicator_of_notMem (fun hg => hyL ⟨_, hg, ?_⟩) _
        have : j g' ∈ {g | a g x₀ = x₀} := hr ▸ Set.mem_range_self g'
        change a (s₀ y * j g') x₀ = y
        rw [a_mul, this, hs₀' y hy]
    refine (lintegral_mono_ae hle).trans_lt ?_
    rw [lintegral_indicator_const hL.measurableSet]
    exact ENNReal.mul_lt_top hC.measure_lt_top hL.measure_lt_top
  refine ⟨Measure.haarScalarFactor m μ, fun s hs f hf => ?_⟩
  have e := Measure.isMulLeftInvariant_eq_smul m μ
  calc ∫⁻ y, (∫⁻ g', f (s y * j g') ∂μ') ∂ν
      = ∫⁻ y, (∫⁻ g', f (s₀ y * j g') ∂μ') ∂ν := by
        refine lintegral_congr_ae ?_
        filter_upwards [hS] with y hy
        exact key f _ _ (by rw [hs.2 y hy, hs₀' y hy])
    _ = ∫⁻ g, f g ∂m := (hint f hf).symm
    _ = _ := by
        conv_lhs => rw [e]
        rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]

theorem quadric_haar : ∀ (P Q P' Q' : ℕ) (β : ℝ) (x₀ : Sp P Q) (j : UpqT P' Q' →* UpqT P Q)
    (ν : Measure (Sp P Q)) (μ : Measure (UpqT P Q)) (μ' : Measure (UpqT P' Q')),
    Topology.IsClosedEmbedding j → Set.range j = {g | act g x₀ = x₀} →
    IsFiniteMeasureOnCompacts ν → (∀ᵐ y ∂ν, qf y = β) → (∀ g : UpqT P Q, ν.map (act g) = ν) →
    μ.IsHaarMeasure → μ'.IsHaarMeasure →
    ∃ κ : ℝ≥0, ∀ s : Sp P Q → UpqT P Q, IsSection β x₀ s →
      ∀ f : UpqT P Q → ℝ≥0∞, Measurable f →
        ∫⁻ y, (∫⁻ g', f (s y * j g') ∂μ') ∂ν = κ * ∫⁻ g, f g ∂μ := by
  intro P Q P' Q' β x₀ j ν μ μ' hj hr h1 hS hν h2 h3
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P Q
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc P' Q'
  refine exists_const act (fun g h x => ?_) (fun x => Matrix.one_mulVec x) (fun g => ?_) x₀ ?_
    (fun y => qf y = β) j ν μ μ' hj hr hS hν
  · exact (Matrix.mulVec_mulVec x (UpqT.mat g) (UpqT.mat h)).symm
  · exact (continuous_const.matrix_mulVec continuous_id).measurable
  · exact GlobalTheory.UpqTopology.continuous_mat.matrix_mulVec continuous_const

end GlobalTheory.QuadricHaar
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

theorem rowE_apply (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (P : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b P = ∑ s : Fin n, X (a, s) * pderiv (b, s) P := by
  simp [rowE, LinearMap.sum_apply]

theorem rowE_X (R : Type) [CommRing R] (r n : ℕ) (a b c : Fin r) (t : Fin n) :
    rowE R r n a b (X (c, t)) = if b = c then X (a, t) else 0 := by
  rw [rowE_apply]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single t]
    · simp
    · intro s _ hs
      rw [pderiv_X_of_ne (by simp [Ne.symm hs])]; simp
    · simp
  · refine Finset.sum_eq_zero fun s _ => ?_
    rw [pderiv_X_of_ne (by simp [Ne.symm h])]; simp

theorem rowE_mul (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (P Q : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b (P * Q) = rowE R r n a b P * Q + P * rowE R r n a b Q := by
  simp only [rowE_apply, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Derivation.leibniz, smul_eq_mul]; ring

theorem rowE_C (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (x : R) :
    rowE R r n a b (C x) = 0 := by
  simp [rowE_apply]

theorem glRel_rowE (R : Type) [CommRing R] (r n : ℕ) : GlRel (rowE R r n) := by
  intro a b c d
  refine LinearMap.ext fun P => ?_
  induction P using MvPolynomial.induction_on with
  | C x => split_ifs <;> simp [rowE_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    obtain ⟨e, t⟩ := v
    have hX : (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) (X (e, t)) =
        ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) (X (e, t)) := by
      simp only [LinearMap.sub_apply, Module.End.mul_apply, rowE_X]
      split_ifs <;> simp_all [rowE_X]
    have hL : ∀ P Q, (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) (P * Q) =
        (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) P * Q +
          P * (rowE R r n a b * rowE R r n c d - rowE R r n c d * rowE R r n a b) Q := by
      intro P Q
      simp only [LinearMap.sub_apply, Module.End.mul_apply, rowE_mul, map_add (f := _)]; ring
    have hR : ∀ P Q, ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) (P * Q) =
        ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) P * Q +
          P * ((if b = c then rowE R r n a d else 0) - (if d = a then rowE R r n c b else 0)) Q := by
      intro P Q
      split_ifs <;> simp [rowE_mul] <;> ring
    rw [hL, hR, hp, hX]

theorem rowE_eq_rowDiv (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (P : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b P = rowDiv R a b 1 P ∧ rowDiv R a b 0 P = P := by
  induction P using MvPolynomial.induction_on with
  | C x => simp [rowE_C, rowDiv, rowGen, Polynomial.algebraMap_apply, Polynomial.coeff_C]
  | add p q hp hq =>
    simp only [rowDiv, map_add (f := _), Polynomial.coeff_add] at *
    exact ⟨by rw [hp.1, hq.1], by rw [hp.2, hq.2]⟩
  | mul_X p v hp =>
    obtain ⟨e, t⟩ := v
    simp only [rowDiv, map_mul] at *
    have h0 : (rowGen R a b (X (e, t) : MvPolynomial (Fin r × Fin n) R)).coeff 0 = X (e, t) := by
      simp only [rowGen, aeval_X]; split_ifs <;> simp
    have h1 : (rowGen R a b (X (e, t) : MvPolynomial (Fin r × Fin n) R)).coeff 1 =
        if b = e then X (a, t) else 0 := by
      simp only [rowGen, aeval_X]
      by_cases h : e = b
      · simp [h, Polynomial.coeff_C]
      · simp [h, Ne.symm h, Polynomial.coeff_C]
    refine ⟨?_, by rw [Polynomial.mul_coeff_zero, hp.2, h0]⟩
    rw [rowE_mul, rowE_X, Polynomial.coeff_mul, Finset.Nat.antidiagonal_succ]
    simp [hp.1, hp.2, h0, h1, add_comm]

theorem map_rowE {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r n : ℕ) (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (rowE R r n a b f) = rowE S r n a b (map φ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rowE_apply, map_sum, map_mul, map_X, pderiv_map]

theorem map_rowE_pow {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r n k : ℕ) (a b : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ ((rowE R r n ^ k) a b f) = (rowE S r n ^ k) a b (map φ f) := by
  induction k generalizing a b f with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ k ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pow_succ, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply, map_sum, ih, map_rowE]

theorem map_gel {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r n k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (gel R r n k f) = gel S r n k (map φ f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gel, Matrix.trace, Matrix.diag, LinearMap.sum_apply, map_sum, map_rowE_pow]

theorem rowOperators_main : ∀ (R : Type) [CommRing R] (r n : ℕ), GlRel (rowE R r n) ∧
    (∀ a b f, rowE R r n a b f = rowDiv R a b 1 f) ∧
    ∀ (S : Type) [CommRing S] (φ : R →+* S) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R),
      map φ (gel R r n k f) = gel S r n k (map φ f) := by
  intro R _ r n
  exact ⟨glRel_rowE R r n, fun a b f => (rowE_eq_rowDiv R r n a b f).1,
    fun S _ φ k f => map_gel φ r n k f⟩

end GlobalTheory.Alc
end
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem rowE_apply_eq_sum (R : Type) [CommRing R] (r n : ℕ) (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    rowE R r n a b f = ∑ s : Fin n, X (a, s) * pderiv (b, s) f := by
  simp [rowE, LinearMap.sum_apply]

theorem weight_rowW_eq_sum {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) d a = ∑ s : Fin n, d (a, s) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, rowW, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp

theorem weight_rowW_single {r n : ℕ} (v : Fin r × Fin n) :
    Finsupp.weight (rowW r n) (Finsupp.single v 1) = Pi.single v.1 1 := by
  simp [Finsupp.weight_apply, rowW]

theorem X_mul_monomial_pderiv_term {R : Type} [CommRing R] {r n : ℕ} (a b : Fin r) (s : Fin n)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    X (a, s) * pderiv (b, s) (monomial d c) =
      monomial (Finsupp.single (a, s) 1 + (d - Finsupp.single (b, s) 1)) (c * (d (b, s) : R)) := by
  rw [pderiv_monomial, X, monomial_mul, one_mul]

end GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem rowE_diag_monomial {R : Type} [CommRing R] {r n : ℕ} (a : Fin r) (μ : Fin r → ℕ)
    (d : Fin r × Fin n →₀ ℕ) (c : R) (hd : Finsupp.weight (rowW r n) d = μ) :
    rowE R r n a a (monomial d c) = (μ a : R) • monomial d c := by
  rw [rowE_apply_eq_sum]
  have hterm : ∀ s : Fin n, X (a, s) * pderiv (a, s) (monomial d c) = monomial d (c * (d (a, s) : R)) := by
    intro s
    rw [X_mul_monomial_pderiv_term]
    by_cases h : d (a, s) = 0
    · simp [h]
    · rw [add_comm, tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))]
  simp_rw [hterm]

  rw [← map_sum, ← Finset.mul_sum, smul_monomial, smul_eq_mul, mul_comm]
  congr 2
  rw [← hd, weight_rowW_eq_sum]
  push_cast
  rfl

theorem rowE_monomial_eq_zero {R : Type} [CommRing R] {r n : ℕ} (a b : Fin r) (μ : Fin r → ℕ)
    (d : Fin r × Fin n →₀ ℕ) (c : R) (hd : Finsupp.weight (rowW r n) d = μ) (hb : μ b = 0) :
    rowE R r n a b (monomial d c) = 0 := by
  rw [rowE_apply_eq_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have h0 : d (b, s) = 0 := by
    have h1 : ∑ t : Fin n, d (b, t) = 0 := by rw [← weight_rowW_eq_sum, hd, hb]
    exact (Finset.sum_eq_zero_iff.mp h1) s (Finset.mem_univ _)
  rw [X_mul_monomial_pderiv_term, h0]
  simp

theorem rowE_monomial_weight {R : Type} [CommRing R] {r n : ℕ} (a b : Fin r) (μ μ' : Fin r → ℕ)
    (d : Fin r × Fin n →₀ ℕ) (c : R) (hd : Finsupp.weight (rowW r n) d = μ)
    (hμ : μ' + Pi.single b 1 = μ + Pi.single a 1) :
    IsWeightedHomogeneous (rowW r n) (rowE R r n a b (monomial d c)) μ' := by
  rw [rowE_apply_eq_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun s _ => ?_
  rw [X_mul_monomial_pderiv_term]
  by_cases h : d (b, s) = 0
  · rw [h]; simp only [Nat.cast_zero, mul_zero, map_zero]
    exact isWeightedHomogeneous_zero R _ _
  · refine isWeightedHomogeneous_monomial _ _ _ ?_
    have hle : Finsupp.single (b, s) 1 ≤ d := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h)
    have hsplit : Finsupp.weight (rowW r n) (d - Finsupp.single (b, s) 1) + Pi.single b 1 = μ := by
      rw [← weight_rowW_single (b, s), ← map_add (f := _), tsub_add_cancel_of_le hle, hd]
    rw [map_add (f := _), weight_rowW_single]
    apply add_right_cancel (b := Pi.single b 1)
    rw [hμ, ← hsplit]
    simp only
    abel

theorem rowE_rowWeight : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ) (f : MvPolynomial (Fin r × Fin n) R),
    IsWeightedHomogeneous (rowW r n) f μ → (∀ a, rowE R r n a a f = (μ a : R) • f) ∧
      ∀ a b, a ≠ b → (μ b = 0 → rowE R r n a b f = 0) ∧
        ∀ μ' : Fin r → ℕ, μ' + Pi.single b 1 = μ + Pi.single a 1 →
          IsWeightedHomogeneous (rowW r n) (rowE R r n a b f) μ' := by
  intro R _ r n μ f hf
  have hmon : ∀ d ∈ f.support, Finsupp.weight (rowW r n) d = μ := fun d hd => hf (mem_support_iff.mp hd)
  refine ⟨fun a => ?_, fun a b _ => ⟨fun hb => ?_, fun μ' hμ => ?_⟩⟩
  · conv_lhs => rw [f.as_sum]
    conv_rhs => rw [f.as_sum]

    rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun d hd => rowE_diag_monomial a μ d _ (hmon d hd)
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [f.as_sum, map_sum]
    exact Finset.sum_eq_zero fun d hd => rowE_monomial_eq_zero a b μ d _ (hmon d hd) hb
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [f.as_sum, map_sum]
    exact IsWeightedHomogeneous.sum _ _ _ fun d hd => rowE_monomial_weight a b μ μ' d _ (hmon d hd) hμ

end GlobalTheory.Alc
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem hcRow_succ (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) (i : Fin N) (k : ℕ) :
    ∑ l, (hcMat R μ ^ (k+1)) i l =
      shift R μ i * ∑ l, (hcMat R μ ^ k) i l - ∑ j ∈ Finset.univ.filter (fun j => i < j), ∑ l, (hcMat R μ ^ k) j l := by
  rw [pow_succ']
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hpt : ∀ j : Fin N, hcMat R μ i j * ∑ l, (hcMat R μ ^ k) j l =
      (if j = i then shift R μ i * ∑ l, (hcMat R μ ^ k) j l else 0) +
      (if i < j then -∑ l, (hcMat R μ ^ k) j l else 0) := by
    intro j
    simp only [hcMat, Matrix.of_apply]
    by_cases h1 : j = i
    · subst h1; simp
    · by_cases h2 : i < j
      · simp [h1, h2]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, Finset.sum_ite_eq' , ← Finset.sum_filter,
    Finset.sum_neg_distrib]
  simp [sub_eq_add_neg]

end GlobalTheory.Alc

namespace GlobalTheory.Alc

def hcRowSeries (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (i : Fin N) : PowerSeries R :=
  PowerSeries.mk fun k => ∑ l, (hcMat R μ ^ k) i l

theorem hcRowSeries_eq (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) (i : Fin N) :
    (1 - PowerSeries.C (shift R μ i) * PowerSeries.X) * hcRowSeries R μ i =
      1 - PowerSeries.X * ∑ j ∈ Finset.univ.filter (fun j => i < j), hcRowSeries R μ j := by
  ext n
  cases n with
  | zero => simp [hcRowSeries, sub_mul, mul_assoc, Matrix.one_apply]
  | succ k =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hcRowSeries, sub_mul, mul_assoc, PowerSeries.coeff_succ_X_mul, map_sum, hcRow_succ]

end GlobalTheory.Alc

namespace GlobalTheory.Alc

theorem hcTelescope (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) :
    ∀ d, d ≤ N →
      (1 - PowerSeries.X * ∑ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), hcRowSeries R μ j) *
        ∏ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), (1 - PowerSeries.C (shift R μ j) * PowerSeries.X) =
      ∏ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), (1 - PowerSeries.C (shift R μ j + 1) * PowerSeries.X) := by
  intro d
  induction d with
  | zero =>
    intro _
    have : Finset.univ.filter (fun j : Fin N => N - 0 ≤ j.val) = ∅ := by
      ext j; simp
    rw [this]; simp
  | succ d ih =>
    intro hd
    set i : Fin N := ⟨N - d - 1, by omega⟩ with hi
    have hS : Finset.univ.filter (fun j : Fin N => N - (d+1) ≤ j.val) =
        insert i (Finset.univ.filter (fun j : Fin N => N - d ≤ j.val)) := by
      ext j; simp [hi, Fin.ext_iff]; omega
    have hnot : i ∉ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val) := by
      simp [hi]; omega
    have hgt : Finset.univ.filter (fun j : Fin N => i < j) = Finset.univ.filter (fun j : Fin N => N - d ≤ j.val) := by
      ext j; simp [hi, Fin.lt_iff_val_lt_val]; omega
    have h := hcRowSeries_eq R N μ i
    rw [hgt] at h
    have IH := ih (by omega)
    rw [hS, Finset.sum_insert hnot, Finset.prod_insert hnot, Finset.prod_insert hnot]
    rw [map_add (f := _), map_one]
    linear_combination (1 - PowerSeries.C (shift R μ i) * PowerSeries.X - PowerSeries.X) * IH
      - PowerSeries.X * (∏ j ∈ Finset.univ.filter (fun j : Fin N => N - d ≤ j.val), (1 - PowerSeries.C (shift R μ j) * PowerSeries.X)) * h

theorem hcVal_generating (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R) :
    (1 - PowerSeries.X * PowerSeries.mk (hcVal R μ)) * ∏ i, (1 - PowerSeries.C (shift R μ i) * PowerSeries.X) =
      ∏ i, (1 - PowerSeries.C (shift R μ i + 1) * PowerSeries.X) := by
  have h := hcTelescope R N μ N le_rfl
  have hU : Finset.univ.filter (fun j : Fin N => N - N ≤ j.val) = Finset.univ := by
    ext j; simp
  have hmk : PowerSeries.mk (hcVal R μ) = ∑ j, hcRowSeries R μ j := by
    ext n; simp [hcVal, hcRowSeries, map_sum]
  rw [hU] at h
  rw [hmk]
  exact h

end GlobalTheory.Alc
end
