module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureClosedCompactDecomp
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle021
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle049
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherNormalizationHomogeneous
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle059
public import Mathlib.Topology.Algebra.Group.Quotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousSectionQuotient
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Order.Real
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle060
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Instances.Matrix
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle027
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle001
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.PullHomeoApply

@[expose] public section

section

open Matrix Topology

namespace GlobalTheory.CompanionTheory.AnnihOpen

theorem isOpen_annihilator_of_isCompact :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)),
      IsCompact (A : Set (Fin n → k)) → IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  intro k _ _ _ _ ψ hψ n A hA
  let H : AddSubgroup (Fin n → k) :=
    { carrier := {ξ | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1}
      zero_mem' := by
        intro a _
        simp
      add_mem' := by
        intro x y hx hy a ha
        rw [add_dotProduct, AddChar.map_add_eq_mul, hx a ha, hy a ha, one_mul]
      neg_mem' := by
        intro x hx a ha
        rw [neg_dotProduct, AddChar.map_neg_eq_inv, hx a ha, inv_one] }
  have hdot : Continuous fun p : (Fin n → k) × (Fin n → k) => p.1 ⬝ᵥ p.2 :=
    continuous_fst.dotProduct continuous_snd
  have hcoe : Continuous fun z : Circle => (z : ℂ) := continuous_iff_le_induced.mpr fun U a ↦ a
  have hcont : Continuous fun p : (Fin n → k) × (Fin n → k) =>
      ‖((ψ (p.1 ⬝ᵥ p.2) : Circle) : ℂ) - 1‖ :=
    ((hcoe.comp (hψ.comp hdot)).sub continuous_const).norm
  have hU : IsOpen {p : (Fin n → k) × (Fin n → k) | ‖((ψ (p.1 ⬝ᵥ p.2) : Circle) : ℂ) - 1‖ < 1} :=
    isOpen_lt hcont continuous_const
  have hsub : ({0} : Set (Fin n → k)) ×ˢ (A : Set (Fin n → k)) ⊆
      {p : (Fin n → k) × (Fin n → k) | ‖((ψ (p.1 ⬝ᵥ p.2) : Circle) : ℂ) - 1‖ < 1} := by
    rintro ⟨x, a⟩ ⟨hx, -⟩
    have hx0 : x = 0 := hx
    subst hx0
    simp
  obtain ⟨V, W, hV, -, h0V, hAW, hVW⟩ := generalized_tube_lemma isCompact_singleton hA hU hsub
  have hmem : (H : Set (Fin n → k)) ∈ 𝓝 (0 : Fin n → k) := by
    refine Filter.mem_of_superset (hV.mem_nhds (h0V rfl)) ?_
    intro ξ hξ a ha
    apply GlobalTheory.CharDualMat.circle_eq_one_of_pow_near
    intro m
    have hma : m • a ∈ (A : Set (Fin n → k)) := SetLike.mem_coe.mpr (A.nsmul_mem ha m)
    have h1 := hVW (Set.mk_mem_prod hξ (hAW hma))
    rw [Set.mem_setOf_eq, dotProduct_smul, AddChar.map_nsmul_eq_pow, Circle.coe_pow] at h1
    exact h1
  exact AddSubgroup.isOpen_of_mem_nhds H hmem

end GlobalTheory.CompanionTheory.AnnihOpen
end

section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem lintegral_one_add_normSq_rpow_ne_top :
    ∀ (n : ℕ) (t : ℝ), (n : ℝ) < t →
    ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-t)) ≠ ⊤ := by
  intro n t ht
  have ht0 : 0 < t := lt_of_le_of_lt n.cast_nonneg ht
  have hdim : (Module.finrank ℝ (Fin n → ℂ) : ℝ) < 2 * t := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    linarith
  have hint := integrable_rpow_neg_one_add_norm_sq (E := Fin n → ℂ) (μ := volume) hdim
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun v => ?_) hint.lintegral_lt_top)
  apply ENNReal.ofReal_le_ofReal

  have hS0 : 0 ≤ ∑ i, Complex.normSq (v i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hnorm : ‖v‖ ≤ Real.sqrt (∑ i, Complex.normSq (v i)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    have h1 : ‖v i‖ ^ 2 ≤ ∑ j, Complex.normSq (v j) := by
      rw [← Complex.normSq_eq_norm_sq]
      exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i)
    simpa [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt h1
  have hab : 1 + ‖v‖ ^ 2 ≤ 1 + ∑ i, Complex.normSq (v i) := by
    have h2 := pow_le_pow_left₀ (norm_nonneg v) hnorm 2
    rw [Real.sq_sqrt hS0] at h2
    linarith
  have ha : 0 < 1 + ‖v‖ ^ 2 := by positivity
  rw [show -(2 * t) / 2 = -t by ring, Real.rpow_neg (by linarith), Real.rpow_neg ha.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos ha t) (Real.rpow_le_rpow ha.le hab ht0.le)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end

section

open MeasureTheory Topology Pointwise
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.QKAvg

theorem mass_const {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (Q K : Subgroup G) [LocallyCompactSpace Q]
    (hdec : ∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) (δ : Q →* ℝ≥0) (hδc : Continuous δ)
    (hΔ : ∀ q : Q, Measure.modularCharacterFun q = δ q) (ν : Measure Q) [ν.IsHaarMeasure]
    [SecondCountableTopology Q] {E : Set G} (hEm : MeasurableSet E)
    (hEK : ∀ g, ∀ k ∈ K, g * k ∈ E ↔ g ∈ E) (g : G) :
    ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * g) * (δ q : ℝ≥0∞) ∂ν =
      ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν := by
  obtain ⟨q0, hq0, k, hk, rfl⟩ := hdec g
  obtain ⟨p, hp⟩ : ∃ p : Q, p.1 = q0 := ⟨⟨q0, hq0⟩, rfl⟩
  have hF : Measurable fun q : Q => E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) :=
    ((measurable_one.indicator hEm).comp measurable_subtype_coe).mul hδc.measurable.coe_nnreal_ennreal
  have hpt : ∀ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) * (δ q : ℝ≥0∞) =
      (δ p⁻¹ : ℝ≥0∞) * (E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞)) := by
    intro q
    have hmem : q.1 * (q0 * k) ∈ E ↔ (q * p).1 ∈ E := by
      rw [← mul_assoc, Subgroup.coe_mul, hp]
      exact hEK _ k hk
    have h2 : (δ q : ℝ≥0∞) = (δ (q * p) : ℝ≥0∞) * (δ p⁻¹ : ℝ≥0∞) := by
      rw [← ENNReal.coe_mul, ← map_mul, mul_inv_cancel_right]
    have h3 : E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) = E.indicator (1 : G → ℝ≥0∞) (q * p).1 := by
      classical
      by_cases hm : (q * p).1 ∈ E
      · rw [Set.indicator_apply, Set.indicator_apply, if_pos (hmem.mpr hm), if_pos hm]
        rfl
      · rw [Set.indicator_apply, Set.indicator_apply, if_neg (fun h => hm (hmem.mp h)), if_neg hm]
    rw [h3, h2]
    ring
  have hΔp : (Measure.modularCharacterFun p : ℝ≥0∞) = (δ p : ℝ≥0∞) := by
    rw [hΔ p]
  calc ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * (q0 * k)) * (δ q : ℝ≥0∞) ∂ν
      = ∫⁻ q : Q, (δ p⁻¹ : ℝ≥0∞) * (E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞)) ∂ν := by
        congr 1
        funext q
        exact hpt q
    _ = (δ p⁻¹ : ℝ≥0∞) * ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q * p).1 * (δ (q * p) : ℝ≥0∞) ∂ν :=
        lintegral_const_mul _ (hF.comp (measurable_mul_const p))
    _ = (δ p⁻¹ : ℝ≥0∞) * ((Measure.modularCharacterFun p : ℝ≥0∞) *
          ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν) :=
        congrArg (fun t => (δ p⁻¹ : ℝ≥0∞) * t) (GlobalTheory.HaarQK.lintegral_mul_right_modular ν hF p)
    _ = ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν := by
        rw [hΔp, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul, inv_mul_cancel, map_one, ENNReal.coe_one,
          one_mul]

theorem lintegral_mul_right_of_modular_law : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (Q K : Subgroup G) [LocallyCompactSpace Q], IsClosed (Q : Set G) → IsCompact (K : Set G) → (∀ g, ∃ q ∈ Q, ∃ k ∈ K, g = q * k) → ∀ δ : Q →* ℝ≥0, Continuous δ → (∀ q : Q, Measure.modularCharacterFun q = δ q) → ∀ κ : Measure K, κ.IsHaarMeasure → ∀ s : G → ℝ≥0∞, Measurable s → (∀ (q : Q) (h : G), s (q * h) = (δ q : ℝ≥0∞) * s h) → ∀ g, ∫⁻ k, s (k * g) ∂κ = ∫⁻ k, s k ∂κ := by
  intro G _ _ _ _ _ _ _ _ μ _ _ Q K _ hQ hK hdec δ hδc hΔ κ hκ s hs hsq g
  haveI := hκ
  haveI : SecondCountableTopology Q := GlobalTheory.HaarQK.secondCountable_subgroup Q
  obtain ⟨ν, hν⟩ : ∃ ν : Measure Q, ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  haveI := hν
  obtain ⟨c, hc0, hctop, hdecomp⟩ :=
    GlobalTheory.lintegral_haar_eq_mul_iterated_closed_compact G μ Q K hQ hK hdec ν κ
  obtain ⟨S, hSc, hS1⟩ := exists_compact_mem_nhds (1 : G)
  set E : Set G := S * (K : Set G) with hE
  have hEc : IsCompact E := hSc.mul hK
  have hEm : MeasurableSet E := hEc.isClosed.measurableSet
  have hEK : ∀ h : G, ∀ k ∈ K, h * k ∈ E ↔ h ∈ E := by
    intro h k hk
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      have hab' : a * b = h * k := hab
      refine ⟨a, ha, b * k⁻¹, K.mul_mem hb (K.inv_mem hk), ?_⟩
      show a * (b * k⁻¹) = h
      rw [← mul_assoc, hab', mul_inv_cancel_right]
    · rintro ⟨a, ha, b, hb, hab⟩
      have hab' : a * b = h := hab
      refine ⟨a, ha, b * k, K.mul_mem hb hk, ?_⟩
      show a * (b * k) = h * k
      rw [← mul_assoc, hab']
  set M := ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) q.1 * (δ q : ℝ≥0∞) ∂ν with hMdef
  have hmass : ∀ t : G, ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (q.1 * t) * (δ q : ℝ≥0∞) ∂ν = M :=
    fun t => mass_const Q K hdec δ hδc hΔ ν hEm hEK t
  have hT : IsCompact (((↑) : Q → G) ⁻¹' E) := hQ.isClosedEmbedding_subtypeVal.isCompact_preimage hEc
  have hMeq : M = ∫⁻ q in ((↑) : Q → G) ⁻¹' E, (δ q : ℝ≥0∞) ∂ν := by
    rw [hMdef, ← lintegral_indicator (hEm.preimage measurable_subtype_coe)]
    refine lintegral_congr fun q => ?_
    by_cases hq : q.1 ∈ E
    · simp [Set.indicator_apply, hq]
    · simp [Set.indicator_apply, hq]
  have hMtop : M ≠ ⊤ := by
    rw [hMeq]
    exact (setLIntegral_lt_top_of_isCompact hT.measure_lt_top.ne hT hδc).ne
  have hδ0 : ∀ q : Q, (δ q : ℝ≥0∞) ≠ 0 := by
    intro q hq
    have h1 := map_mul_eq_one δ (mul_inv_cancel q)
    rw [ENNReal.coe_eq_zero] at hq
    rw [hq, zero_mul] at h1
    exact zero_ne_one h1
  have hM0 : M ≠ 0 := by
    rw [hMeq]
    intro h0
    rw [lintegral_eq_zero_iff hδc.measurable.coe_nnreal_ennreal] at h0
    have h1 : ∀ᵐ q ∂(ν.restrict (((↑) : Q → G) ⁻¹' E)), False :=
      h0.mono fun q hq => hδ0 q hq
    rw [ae_iff] at h1
    have hTz : ν (((↑) : Q → G) ⁻¹' E) = 0 := by simpa using h1
    have hV : ((↑) : Q → G) ⁻¹' S ∈ 𝓝 (1 : Q) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hS1
    have hpos := Measure.measure_pos_of_mem_nhds ν hV
    have hsub : ((↑) : Q → G) ⁻¹' S ⊆ ((↑) : Q → G) ⁻¹' E := fun q hq =>
      ⟨q.1, hq, 1, K.one_mem, mul_one _⟩
    have := measure_mono (μ := ν) hsub
    rw [hTz] at this
    exact (lt_irrefl 0 (hpos.trans_le this))
  have hin : ∀ a b : G, ∫⁻ q : Q, E.indicator (1 : G → ℝ≥0∞) (↑q * a) * s (↑q * b) ∂ν = M * s b := by
    intro a b
    have h1 : ∀ q : Q, E.indicator (1 : G → ℝ≥0∞) (↑q * a) * s (↑q * b) =
        E.indicator (1 : G → ℝ≥0∞) (↑q * a) * (δ q : ℝ≥0∞) * s b := by
      intro q
      rw [hsq q b, mul_assoc]
    have hmeas : Measurable fun q : Q => E.indicator (1 : G → ℝ≥0∞) (↑q * a) * (δ q : ℝ≥0∞) :=
      ((measurable_one.indicator hEm).comp ((measurable_mul_const a).comp measurable_subtype_coe)).mul
        hδc.measurable.coe_nnreal_ennreal
    rw [lintegral_congr h1, lintegral_mul_const _ hmeas, hmass a]
  have hA : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) h * s (h * g) ∂μ = c * (M * ∫⁻ k : K, s (↑k * g) ∂κ) := by
    have hmA : Measurable fun h : G => E.indicator (1 : G → ℝ≥0∞) h * s (h * g) :=
      (measurable_one.indicator hEm).mul (hs.comp (measurable_mul_const g))
    rw [hdecomp (fun h : G => E.indicator (1 : G → ℝ≥0∞) h * s (h * g)) hmA]
    congr 1
    rw [← lintegral_const_mul' M _ hMtop]
    refine lintegral_congr fun k => ?_
    simp only [mul_assoc]
    exact hin (↑k) (↑k * g)
  have hB : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h ∂μ = c * (M * ∫⁻ k : K, s ↑k ∂κ) := by
    have hmB : Measurable fun h : G => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h :=
      ((measurable_one.indicator hEm).comp (measurable_mul_const g⁻¹)).mul hs
    rw [hdecomp (fun h : G => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h) hmB]
    congr 1
    rw [← lintegral_const_mul' M _ hMtop]
    refine lintegral_congr fun k => ?_
    simp only [mul_assoc]
    exact hin (↑k * g⁻¹) ↑k
  have hI : ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) h * s (h * g) ∂μ =
      ∫⁻ h, E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h ∂μ := by
    rw [← lintegral_mul_right_eq_self (fun h => E.indicator (1 : G → ℝ≥0∞) (h * g⁻¹) * s h) g]
    simp only [mul_inv_cancel_right]
  rw [hA, hB] at hI
  exact (ENNReal.mul_right_inj hM0 hMtop).mp ((ENNReal.mul_right_inj hc0 hctop).mp hI)

end GlobalTheory.CompanionTheory.QKAvg
end

section

open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ModChar

theorem modularCharacterFun_semidirect :
    ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [T2Space Q] [SecondCountableTopology Q] [MeasurableSpace Q] [BorelSpace Q] (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [LocallyCompactSpace M], IsClosed (N : Set Q) → IsClosed (M : Set Q) → (∀ q, ∃ n ∈ N, ∃ m ∈ M, q = n * m) → (∀ x, x ∈ N → x ∈ M → x = 1) → ∀ (νN : Measure N) (νM : Measure M), νN.IsHaarMeasure → νN.IsMulRightInvariant → νM.IsHaarMeasure → νM.IsMulRightInvariant → ∀ δ : Q →* ℝ≥0, (∀ n ∈ N, δ n = 1) → (∀ m ∈ M, νN.map (fun n : N => MulAut.conjNormal m n) = (δ m)⁻¹ • νN) → ∀ q : Q, Measure.modularCharacterFun q = δ q := by
  intro Q _ _ _ _ _ _ _ _ N M _ _ _ hN hM hgen hdisj νN νM hNH hNR hMH hMR δ hδN hδM q
  haveI := hNH
  haveI := hNR
  haveI := hMH
  haveI := hMR
  haveI : BorelSpace N := Subtype.borelSpace (fun x => x ∈ (N : Set Q))
  haveI : BorelSpace M := Subtype.borelSpace (fun x => x ∈ (M : Set Q))
  haveI : SecondCountableTopology N :=
    TopologicalSpace.Subtype.secondCountableTopology (N : Set Q)
  haveI : SecondCountableTopology M :=
    TopologicalSpace.Subtype.secondCountableTopology (M : Set Q)
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.semidirect_product_homeomorph_of_closed_complement Q N M hN hM hgen hdisj
  let Ψ : (M × N) ≃ₜ Q := (Homeomorph.prodComm M N).trans Φ
  have hΨ : ∀ p : M × N, Ψ p = (p.2 : Q) * (p.1 : Q) := fun p => hΦ (p.2, p.1)
  have hΨm : Measurable Ψ := Ψ.continuous.measurable
  set ρ : Measure Q := (νM.prod νN).map Ψ with hρ
  have hconj : ∀ (m : Q) (n : N), ((MulAut.conjNormal m n : N) : Q) = m * n * m⁻¹ :=
    fun m n => MulAut.conjNormal_apply m n
  haveI : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun K hK => ?_⟩
    rw [hρ, show ((νM.prod νN).map Ψ) K = (νM.prod νN) (Ψ ⁻¹' K) from
      Ψ.toMeasurableEquiv.map_apply K]
    have : IsCompact (Ψ ⁻¹' K) := by
      have := hK.image Ψ.symm.continuous
      rwa [Ψ.symm.image_eq_preimage_symm, Ψ.symm_symm] at this
    exact this.measure_lt_top
  haveI : ρ.IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    rw [hρ, show ((νM.prod νN).map Ψ) U = (νM.prod νN) (Ψ ⁻¹' U) from
      Ψ.toMeasurableEquiv.map_apply U]
    exact (hU.preimage Ψ.continuous).measure_ne_zero _ (hne.preimage Ψ.surjective)
  haveI : ρ.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨⟨m₀, n₀⟩, rfl⟩ := Ψ.surjective g
    have hmul : Measurable (fun y : Q => y * Ψ (m₀, n₀)) := measurable_mul_const _
    have hc : Continuous (fun p : M × N => (MulAut.conjNormal (p.1 : Q) n₀ : N)) := by
      have h : Continuous (fun p : M × N => (p.1 : Q) * n₀ * (p.1 : Q)⁻¹) := by fun_prop
      exact Topology.IsInducing.subtypeVal.continuous_iff.2
        (h.congr fun p => (hconj _ _).symm)
    let T : M × N → M × N := fun p => (p.1 * m₀, p.2 * MulAut.conjNormal (p.1 : Q) n₀)
    have hT : MeasurePreserving T (νM.prod νN) (νM.prod νN) := by
      refine MeasurePreserving.skew_product (f := fun m : M => m * m₀)
        (g := fun (m : M) (n : N) => n * MulAut.conjNormal (m : Q) n₀)
        (measurePreserving_mul_right νM m₀) ?_ (Filter.Eventually.of_forall fun m => ?_)
      · exact (continuous_snd.mul hc).measurable
      · exact (measurePreserving_mul_right νN _).map_eq
    have hcomp : (fun y : Q => y * Ψ (m₀, n₀)) ∘ Ψ = Ψ ∘ T := by
      funext ⟨m, n⟩
      simp only [Function.comp, T, hΨ, Subgroup.coe_mul, hconj]
      group
    rw [hρ, Measure.map_map hmul hΨm, hcomp, ← Measure.map_map hΨm hT.measurable, hT.map_eq]
  refine GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_eq_of_map_left_mul Q ρ δ ?_ q
  intro q₀
  obtain ⟨⟨m₀, n₀⟩, rfl⟩ := Ψ.surjective q₀
  have hmul : Measurable (fun y : Q => Ψ (m₀, n₀) * y) := measurable_const_mul _
  have hcm : Continuous (fun n : N => (MulAut.conjNormal (m₀ : Q) n : N)) := by
    have h : Continuous (fun n : N => (m₀ : Q) * n * (m₀ : Q)⁻¹) := by fun_prop
    exact Topology.IsInducing.subtypeVal.continuous_iff.2
      (h.congr fun p => (hconj _ _).symm)
  let f₁ : M → M := fun m => m₀ * m
  let f₂ : N → N := fun n => n₀ * MulAut.conjNormal (m₀ : Q) n
  have hf₁ : Measurable f₁ := measurable_const_mul _
  have hf₂ : Measurable f₂ := (continuous_const.mul hcm).measurable
  have hcomp : (fun y : Q => Ψ (m₀, n₀) * y) ∘ Ψ = Ψ ∘ Prod.map f₁ f₂ := by
    funext ⟨m, n⟩
    simp only [Function.comp, Prod.map, f₁, f₂, hΨ, Subgroup.coe_mul, hconj]
    group
  have hνM : νM.map f₁ = νM := (measurePreserving_mul_left νM m₀).map_eq
  have hνN : νN.map f₂ = (δ m₀)⁻¹ • νN := by
    have : f₂ = (fun n : N => n₀ * n) ∘ (fun n : N => (MulAut.conjNormal (m₀ : Q) n : N)) := rfl
    rw [this, ← Measure.map_map (measurable_const_mul _) hcm.measurable, hδM _ m₀.2,
      Measure.map_smul (c := (δ m₀)⁻¹) (f := fun x : N => n₀ * x)
        (measurable_const_mul _).aemeasurable,
      (measurePreserving_mul_left νN n₀).map_eq]
  have hδ : δ (Ψ (m₀, n₀)) = δ m₀ := by
    rw [hΨ]
    simp [map_mul, hδN _ n₀.2]
  rw [hρ, Measure.map_map hmul hΨm, hcomp,
    ← Measure.map_map hΨm (hf₁.prodMap hf₂), ← Measure.map_prod_map νM νN hf₁ hf₂, hνM, hνN,
    Measure.prod_smul_right,
    Measure.map_smul (c := (δ m₀)⁻¹) (f := Ψ) hΨm.aemeasurable, hδ]

end GlobalTheory.CompanionTheory.ModChar
end

section

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem lintegral_sq_add_sq_rpow_neg :
    ∀ s : ℝ, 1 / 2 < s → ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ a : ℝ, 0 < a → ∀ m : ℝ,
    ∫⁻ d : ℝ, ENNReal.ofReal ((a ^ 2 + (d - m) ^ 2) ^ (-s)) = C * ENNReal.ofReal (a ^ (1 - 2 * s)) := by
  intro s hs
  have hint : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-s)) := by
    have h0 := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * s)
      (by simp; linarith)
    have e : -(2 * s) / 2 = -s := by ring
    simpa [Real.norm_eq_abs, sq_abs, e] using h0
  refine ⟨∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s)), hint.lintegral_lt_top.ne, ?_⟩
  intro a ha m
  have hF : Measurable fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s)) := by fun_prop
  rw [lintegral_sub_right_eq_self (fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))) m]
  have hpt : ∀ t : ℝ, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) =
      ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) * ENNReal.ofReal ((1 + t ^ 2) ^ (-s)) := by
    intro t
    rw [← ENNReal.ofReal_mul (by positivity), show a ^ 2 + (a * t) ^ 2 = a ^ 2 * (1 + t ^ 2) by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast a 2,
      ← Real.rpow_mul ha.le]
  have hpow : a ^ (1 - 2 * s) = a * a ^ ((2 : ℕ) * -s : ℝ) := by
    rw [show (1 - 2 * s) = 1 + ((2 : ℕ) * -s : ℝ) by push_cast; ring, Real.rpow_add ha,
      Real.rpow_one]
  calc ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
      = ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
          ∂(ENNReal.ofReal |a| • Measure.map (a * ·) volume) := by
        rw [Real.smul_map_volume_mul_left ha.ne']
    _ = ENNReal.ofReal |a| * ∫⁻ t, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) := by
        rw [lintegral_smul_measure, lintegral_map hF (measurable_const_mul a), smul_eq_mul]
    _ = ENNReal.ofReal a * (ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) *
          ∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s))) := by
        rw [abs_of_pos ha]
        simp_rw [hpt]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul ha.le, ← hpow, mul_comm]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end

section

set_option backward.isDefEq.respectTransparency false
open MvPolynomial

theorem _root_.GlobalTheory.T.noether_normalization_homogeneous : ∀ (K : Type) [Field K] [Infinite K] (N : ℕ) (I : Ideal (MvPolynomial (Fin (N + 1)) K)), I ≠ ⊤ → (∀ f ∈ I, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ I) → ∃ (e m : ℕ) (y : Fin m → MvPolynomial (Fin (N + 1)) K), 0 < e ∧ (∀ i, (y i).IsHomogeneous e) ∧ AlgebraicIndependent K (fun i => Ideal.Quotient.mk I (y i)) ∧ Module.Finite (Algebra.adjoin K (Set.range fun i => Ideal.Quotient.mk I (y i))) (MvPolynomial (Fin (N + 1)) K ⧸ I) := by
  first | exact @GlobalTheory.CompanionTheory.ConeNoether.main | exact GlobalTheory.CompanionTheory.ConeNoether.main | (intros; apply GlobalTheory.CompanionTheory.ConeNoether.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.homogeneous_integral_expression : ∀ {K σ : Type} [Field K] {m : ℕ} (I : Ideal (MvPolynomial σ K)), (∀ f ∈ I, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ I) → ∀ (e : ℕ), 0 < e → ∀ (y : Fin m → MvPolynomial σ K), (∀ k, (y k).IsHomogeneous e) → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k))) (MvPolynomial σ K ⧸ I) → ∀ (w : ℕ) (a : MvPolynomial σ K), a.IsHomogeneous (e * w) → ∃ (s : ℕ) (c : ℕ → MvPolynomial (Fin m) K), 0 < s ∧ (∀ l, (c l).IsHomogeneous ((s - l) * w)) ∧ a ^ s + ∑ l ∈ Finset.range s, MvPolynomial.aeval y (c l) * a ^ l ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.Geo.exists_hom_relation | exact GlobalTheory.CompanionTheory.Geo.exists_hom_relation | (intros; apply GlobalTheory.CompanionTheory.Geo.exists_hom_relation <;> assumption)
end

section

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

theorem _root_.GlobalTheory.T.exists_continuous_section_quotient : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G] (H : Subgroup G), IsClosed (H : Set G) → ∃ s : G ⧸ H → G, Continuous s ∧ ∀ c : G ⧸ H, ((s c : G) : G ⧸ H) = c := by
  first | exact @GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section | exact GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section | (intros; apply GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section <;> assumption)
end

section

open scoped ENNReal


theorem _root_.GlobalTheory.T.lattice_sum_decay_bound : ∀ {S P : Type} [Fintype P] (m : S → P → ℤ) (b : P → ℝ), (∀ p, 0 < b p) → ∀ (h : S → ℝ≥0∞), Set.InjOn m {ξ | h ξ ≠ 0} → (∀ ξ, h ξ ≤ ∏ p, ENNReal.ofReal (((1 + |(m ξ p : ℝ)| / b p) ^ 2)⁻¹)) → ∑' ξ, h ξ ≤ ∏ p, ENNReal.ofReal (1 + 2 * b p) := by
  first | exact @GlobalTheory.CompanionTheory.Count.tsum_le_prod_of_injOn | exact GlobalTheory.CompanionTheory.Count.tsum_le_prod_of_injOn | (intros; apply GlobalTheory.CompanionTheory.Count.tsum_le_prod_of_injOn <;> assumption)
end
