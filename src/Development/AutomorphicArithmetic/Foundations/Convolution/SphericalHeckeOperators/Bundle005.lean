module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.Bundle004
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ElemMatch
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem integral_conv {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {f₁ f₂ : G → ℂ}
    (h₁ : HasCompactSupport f₁) (h₂ : HasCompactSupport f₂)
    (r₁ : ∀ g, ∀ k ∈ K, f₁ (g * k) = f₁ g) (l₂ : ∀ g, ∀ k ∈ K, f₂ (k * g) = f₂ g)
    (r₂ : ∀ g, ∀ k ∈ K, f₂ (g * k) = f₂ g) :
    ∫ x, groupConv μ f₁ f₂ x ∂μ = (∫ x, f₁ x ∂μ) * ∫ x, f₂ x ∂μ := by
  have key := integral_integral_swap_of_coset μ K hK (F := fun y z => f₁ y * f₂ (y⁻¹ * z))
    h₁ (h₁.mul h₂) ?_ ?_ ?_
  · simp only [groupConv]
    rw [← key, ← integral_mul_const]
    congr 1
    funext y
    rw [integral_const_mul, integral_mul_left_eq_self f₂ y⁻¹]
  · intro y z h
    have h' := mul_ne_zero_iff.1 h
    exact ⟨subset_tsupport _ h'.1, y, subset_tsupport _ h'.1, y⁻¹ * z, subset_tsupport _ h'.2,
      mul_inv_cancel_left y z⟩
  · intro y z k hk
    simp only [r₁ y k hk, mul_inv_rev, mul_assoc, l₂ _ _ (inv_mem hk)]
  · intro y z k hk
    simp only [← mul_assoc, r₂ _ k hk]

private theorem meas_dco {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] {a : Fin n → ℤ} (ha : Antitone a) :
    MeasurableSet (dco F a) := by
  have h := ((dcoShape F n a ha).2.2.1.1.isOpen_fiber 1).measurableSet
  convert h using 1
  ext g
  by_cases hg : g ∈ dco F a <;> simp [uFn, hg]

private theorem int_uFn {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) {a : Fin n → ℤ}
    (ha : Antitone a) : ∫ x, uFn F a x ∂μ = (μ.real (dco F a) : ℂ) := by
  have := integral_indicator_const (μ := μ) (1 : ℂ) (meas_dco (F := F) ha)
  rw [Complex.real_smul, mul_one] at this
  exact this

theorem UpperTheory.ConvolutionTheory.H.thMul :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] (a b : Fin n → ℤ), Antitone a → Antitone b →
      groupConv μ (th μ a) (th μ b) = th μ (a + b) := by
  intro F _ _ _ _ n _ _ μ _ a b ha hb
  have hab : Antitone (a + b) := ha.add hb
  obtain ⟨-, hmul, hca, hIa⟩ := dcoShape F n a ha
  obtain ⟨-, -, hcb, hIb⟩ := dcoShape F n b hb
  let K : OpenSubgroup (GL (Fin n) F) := ⟨iwahori F n, isOpen_iwahori F n⟩
  have hKc : IsCompact (K : Set (GL (Fin n) F)) :=
    isCompact_iwahori F n
  have hI : (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 := by
    have h1 : μ (K : Set (GL (Fin n) F)) ≠ 0 := K.isOpen.measure_ne_zero μ ⟨1, K.one_mem⟩
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨h1, hKc.measure_lt_top.ne⟩)
  set φ := groupConv μ (uFn F a) (uFn F b) with hφ
  have hl : ∀ g, ∀ y ∈ iwahori F n, φ (y * g) = φ g := by
    intro g y hy
    simp only [hφ, groupConv]
    rw [← integral_mul_left_eq_self _ y]
    congr 1
    funext x
    rw [(hIa x y hy).1, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hr : ∀ g, ∀ y ∈ iwahori F n, φ (g * y) = φ g := fun g y hy =>
    groupConv_mul_right (fun g => (hIb g y hy).2) g
  have hφe : φ = φ (torusPow F n (a + b)) • uFn F (a + b) := by
    funext g
    by_cases hg : g ∈ dco F (a + b)
    · rw [Pi.smul_apply, uFn, Set.indicator_of_mem hg, Pi.one_apply, smul_eq_mul, mul_one]
      obtain ⟨x, hx, y, hy, rfl⟩ := hg
      rw [hr _ y hy, hl _ x hx]
    · rw [Pi.smul_apply, uFn, Set.indicator_of_notMem hg, smul_zero]
      have : ∀ y, uFn F a y * uFn F b (y⁻¹ * g) = 0 := by
        intro y
        by_contra h
        have h' := mul_ne_zero_iff.1 h
        have := hmul b hb _ (Set.mem_of_indicator_ne_zero h'.1) _ (Set.mem_of_indicator_ne_zero h'.2)
        rw [mul_inv_cancel_left] at this
        exact hg this
      simp only [hφ, groupConv, this, integral_zero]
  set c := φ (torusPow F n (a + b)) with hc
  have hint : c * (μ.real (dco F (a + b)) : ℂ) = (μ.real (dco F a) : ℂ) * (μ.real (dco F b) : ℂ) := by
    have h := integral_conv μ K hKc hca.2 hcb.2 (fun g k hk => (hIa g k hk).2)
      (fun g k hk => (hIb g k hk).1) (fun g k hk => (hIb g k hk).2)
    rw [int_uFn μ ha, int_uFn μ hb, ← hφ] at h
    rw [← h, ← int_uFn μ hab, ← integral_const_mul, hφe]
    rfl
  have va := dcoVol F n μ a ha
  have vb := dcoVol F n μ b hb
  have vab := dcoVol F n μ (a + b) hab
  rw [halfModulus_add] at vab
  have hcI : c = (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ) := by
    apply mul_right_cancel₀ hI
    calc c * _ = c * ((halfModulus F a * halfModulus F b) ^ 2 * (μ.real (dco F (a + b)) : ℂ)) := by rw [vab]
      _ = (halfModulus F a * halfModulus F b) ^ 2 * (c * (μ.real (dco F (a + b)) : ℂ)) := by ring
      _ = (halfModulus F a ^ 2 * (μ.real (dco F a) : ℂ)) * (halfModulus F b ^ 2 * (μ.real (dco F b) : ℂ)) := by
        rw [hint]; ring
      _ = _ := by rw [va, vb]
  funext g
  have e : groupConv μ (th μ a) (th μ b) g =
      (halfModulus F a / (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ)) *
        (halfModulus F b / (μ.real (iwahori F n : Set (GL (Fin n) F)) : ℂ)) * φ g := by
    simp only [hφ, groupConv, th, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  rw [e, hφe, hcI, th, halfModulus_add]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

private theorem quot_smul {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) (H : Subgroup G) (ν : Measure H)
    (c : ℂ) (F : G → ℂ) :
    PositivityTheory.Rg.Tf.Loc.quotIntegral μ H ν (fun g => c * F g) = c * PositivityTheory.Rg.Tf.Loc.quotIntegral μ H ν F := by
  unfold PositivityTheory.Rg.Tf.Loc.quotIntegral
  split_ifs with h
  · rw [← integral_const_mul]
    simp only [mul_assoc]
  · simp

private theorem match_smul {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} [TopologicalSpace k] [TopologicalSpace E]
    [MeasurableSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)]
    {σ : E ≃ₐ[k] E} {μE : Measure (GL (Fin n) E)} {μk : Measure (GL (Fin n) k)} {φ : GL (Fin n) E → ℂ} {f : GL (Fin n) k → ℂ}
    (h : UpperTheory.ConvolutionTheory.Loc.Match σ μE μk φ f) (c : ℂ) : UpperTheory.ConvolutionTheory.Loc.Match σ μE μk (c • φ) (c • f) := by
  refine ⟨fun δ γ x μδ μγ h1 h2 h3 h4 h5 => ?_, fun γ μγ h1 h2 h3 => ?_⟩
  · have := h.1 δ γ x μδ μγ h1 h2 h3 h4 h5
    unfold PositivityTheory.Rg.Tf.Loc.twOrbIntegralC PositivityTheory.Rg.Tf.Loc.orbIntegralC at this ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [quot_smul, quot_smul, this]
  · have := h.2 γ μγ h1 h2 h3
    unfold PositivityTheory.Rg.Tf.Loc.orbIntegralC at this ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [quot_smul, this, mul_zero]

private theorem half_eq {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {l : ℕ} (hq : qF E = qF k ^ l)
    {n : ℕ} (a : Fin n → ℤ) : halfModulus k ((l : ℤ) • a) = halfModulus E a := by
  have hs : sqrtQ E = sqrtQ k ^ l := by
    have h1 : NNReal.sqrt (qF E : NNReal) = NNReal.sqrt (qF k : NNReal) ^ l := by
      rw [NNReal.sqrt_eq_iff_eq_sq, ← pow_mul, mul_comm, pow_mul, NNReal.sq_sqrt, hq, Nat.cast_pow]
    rw [sqrtQ, sqrtQ, h1, NNReal.coe_pow, Complex.ofReal_pow]
  have hr : rhoPair ((l : ℤ) • a) = (l : ℤ) * rhoPair a := by
    simp only [rhoPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [halfModulus_eq, halfModulus_eq, hs, hr, ← zpow_natCast, ← zpow_mul, mul_neg]

private theorem incl_diagPow {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} (ϖ : kˣ) (a : Fin n → ℤ) :
    (PositivityTheory.Rg.Tf.Loc.incl (PositivityTheory.Rg.Tf.Loc.diagPow ϖ a) : GL (Fin n) E) =
      PositivityTheory.Rg.Tf.Loc.diagPow (Units.map (algebraMap k E : k →* E) ϖ) a := by
  ext i j
  change algebraMap k E (Matrix.diagonal (fun i => ((ϖ ^ a i : kˣ) : k)) i j) =
    Matrix.diagonal (fun i => (((Units.map (algebraMap k E : k →* E) ϖ) ^ a i : Eˣ) : E)) i j
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.diagonal_apply_ne _ h]

theorem UpperTheory.ConvolutionTheory.H.thMatch :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], PositivityTheory.Rg.Tf.Loc.IsUnramifiedLoc k E →
      ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
      ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
        (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)) [μE.IsHaarMeasure] [μk.IsHaarMeasure],
      ∀ a : Fin n → ℤ, StrictAnti a → UpperTheory.ConvolutionTheory.Loc.Match σ μE μk (th μE a) (th μk ((Module.finrank k E : ℤ) • a)) := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ hu σ hσ n _ _ _ _ μE μk hE hk a ha
  obtain ⟨-, hIk, ⟨ϖ, hϖ⟩, hfk⟩ := defBridge k n
  obtain ⟨-, hIE, -, hfE⟩ := defBridge E n
  obtain ⟨hq, hun⟩ := unrQ k E hu
  have h := UpperTheory.ConvolutionTheory.Loc.elemMatch k E hu σ hσ n μE μk hE hk ϖ hϖ a ha
  rw [incl_diagPow, hfE _ (hun ϖ hϖ), hfk ϖ hϖ, hIk, hIE] at h
  have hne : μE.real (iwahori E n : Set (GL (Fin n) E)) ≠ 0 := by
    rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨((isOpen_iwahori E n).measure_pos μE ⟨1, one_mem _⟩).ne', (isCompact_iwahori E n).measure_lt_top.ne⟩
  have hne' : (μE.real (iwahori E n : Set (GL (Fin n) E)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hne
  have h2 := match_smul h (halfModulus E a / (μE.real (iwahori E n : Set (GL (Fin n) E)) : ℂ))
  rw [smul_smul] at h2
  unfold th
  rw [half_eq hq]
  convert h2 using 2
  · rw [← measureReal_def, ← measureReal_def, Complex.ofReal_div]
    field_simp
end
