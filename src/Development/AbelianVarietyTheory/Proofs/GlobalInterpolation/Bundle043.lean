module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle015
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryLieVolumeBallSplitBasisVector
public import Formalism.LandauZeroFreeBounds.Statement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionConjEqZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrderNeTop
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle041
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumMulGaussSumInvOfIsPrimitive
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumIntervalIntegralLeOfSpaced
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle040
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle042
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
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

section

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber

namespace GlobalTheory.ThetaWeberRoad

theorem jacobiProduct_of_thetaWeber {τ : UpperHalfPlane} (hTW : ThetaWeber τ)
    (hw : weberF τ * weberF₁ τ * weberF₂ τ = ((Real.sqrt 2 : ℝ) : ℂ)) : JacobiProduct τ := by
  obtain ⟨h1, h2, h3⟩ := hTW
  unfold JacobiProduct
  rw [h1, h2, h3]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  linear_combination (ModularForm.eta (τ : ℂ)) ^ 3 *
    (weberF τ * weberF₁ τ * weberF₂ τ + ((Real.sqrt 2 : ℝ) : ℂ)) * hw +
    ModularForm.eta (τ : ℂ) ^ 3 * hs

theorem thetaWeberStatement_of (hTL : Formalism.L2.Th1.F.ThetaLine) (hSB : Formalism.L2.Th1.F.SgStarBasic)
    (hSA : Formalism.L2.Th1.F.SgStarAdd) : ThetaWeberStatement := by
  have hTW := GlobalTheory.T.thetaConstEqEtaWeberSq_of_tripleProduct GlobalTheory.T.jacobiTripleProduct_twoVariableTheta
  have hJ : ∀ τ : UpperHalfPlane, JacobiProduct τ := fun τ ↦
    jacobiProduct_of_thetaWeber (hTW τ) (GlobalTheory.T.weberFunction_product_eq_sqrt_two τ)
  have hH := GlobalTheory.T.halfPeriodDiffThetaFourth_of_sigmaStar_addition hSA (GlobalTheory.T.gaussianOddJacobiTheta_eq_deriv_mul_sgStar hTL hSB) (GlobalTheory.T.hasDerivAt_oddJacobiTheta_zero_eta_cube GlobalTheory.T.jacobiTripleProduct_twoVariableTheta) hJ
  intro τ
  exact ⟨hH τ, hJ τ, hTW τ, GlobalTheory.T.weberFunctionsRootsOfCubic_of_halfPeriodDiff τ (hH τ) (hJ τ) (hTW τ)⟩

end GlobalTheory.ThetaWeberRoad
end

section

open GlobalTheory.MomN Formalism.L2.Th1.H

theorem _root_.GlobalTheory.T.latticeJetsAreBoundedMoments_of_tensorFourthPower : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (n : Type) [Fintype n] (ω : ℂ_[q]) (Λ : AddSubgroup (n → ℂ)) (G : (n → ℂ) → ℂ), ContDiff ℂ ⊤ G → LatInt ι ω (pow4 Λ) (tens4 G) → LatInt ι ω Λ G := by
  first | exact @GlobalTheory.MomRoot.jets_root | exact GlobalTheory.MomRoot.jets_root | (intros; apply GlobalTheory.MomRoot.jets_root <;> assumption)
end

section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

theorem _root_.GlobalTheory.T.trace_glMatrixUnit_pow_highestWeight_mod : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (N : ℕ) (E : Matrix (Fin N) (Fin N) (Module.End R V)), GlRel E → ∀ (M : Submodule R V), (∀ a b, ∀ f ∈ M, E a b f ∈ M) → ∀ (μ : Fin N → R) (v : V), (∀ a b, a < b → E a b v ∈ M) → (∀ a, E a a v - μ a • v ∈ M) → ∀ k : ℕ, (E ^ k).trace v - hcVal R μ k • v ∈ M := by
  first | exact @GlobalTheory.Alc.trace_pow_hw | exact GlobalTheory.Alc.trace_pow_hw | (intros; apply GlobalTheory.Alc.trace_pow_hw <;> assumption)
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.unitaryLie_volume_ball_split_basis_vector : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), SignCompat e → ∀ (lam : Measure (lieU P Q)) (lam' : Measure (lieU P' Q')), IsOmegaLeb lam → IsOmegaLeb lam' → ∀ r : ℝ, lam (ballU P Q r) = (2 : ℝ≥0∞) ^ (P' + Q') * ((volume : Measure (ℝ × Sp P' Q')).prod lam') {p | tanGauge p.1 + l1 (p.2 : Matrix (Fin P' ⊕ Fin Q') (Fin P' ⊕ Fin Q') ℂ) < r} := by
  first | exact @GlobalTheory.OmegaSplit.omega_split | exact GlobalTheory.OmegaSplit.omega_split | (intros; apply GlobalTheory.OmegaSplit.omega_split <;> assumption)
end

section

open Complex DirichletCharacter

namespace GlobalTheory.LandauPageRegion

theorem inRegion_mono {c c' : ℝ} (h : c ≤ c') (q : ℕ) [NeZero q] {s : ℂ}
    (hs : Formalism.ZeroFreeDirichlet.InRegion c q s) : 1 - c' / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL : 0 ≤ Real.log ((q : ℝ) * (|s.im| + 2)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
    nlinarith
  have hdiv : c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c' / Real.log ((q : ℝ) * (|s.im| + 2)) :=
    div_le_div_of_nonneg_right h hL
  have hs' : 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := hs
  linarith

private theorem real_zero_of_mem_zeroFreeRegion {c₁ c₂ c₃ c : ℝ} (hc₁ : c ≤ c₁) (hc₂ : c ≤ c₂) (hc₃ : c ≤ c₃)
    (hA : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), χ ≠ 1 → LFunction χ s = 0 →
      (χ ^ 2 ≠ 1 ∨ s.im ≠ 0) → s.re < 1 - c₁ / Real.log (q * (|s.im| + 2)))
    (hC : ∀ (q : ℕ) [NeZero q] (s : ℂ), s ≠ 1 → LFunction (1 : DirichletCharacter ℂ q) s = 0 →
      s.re < 1 - c₃ / Real.log (q * (|s.im| + 2)))
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {s : ℂ}
    (hs : Formalism.ZeroFreeDirichlet.InRegion c q s) (hz : Formalism.ZeroFreeDirichlet.IsLZero χ s) :
    χ ≠ 1 ∧ χ ^ 2 = 1 ∧ s.im = 0 ∧ 1 - c₂ / Real.log (2 * q) ≤ s.re ∧
      LFunction χ (s.re : ℂ) = 0 ∧ s = (s.re : ℂ) := by
  obtain ⟨hne, hL⟩ := hz
  have h1 : χ ≠ 1 := by
    rintro rfl
    have hs1 : s ≠ 1 := hne.resolve_left (fun h => h rfl)
    have h3 := hC q s hs1 hL
    have h4 := inRegion_mono hc₃ q hs
    linarith
  have h2 : ¬ (χ ^ 2 ≠ 1 ∨ s.im ≠ 0) := by
    intro h
    have h3 := hA q χ s h1 hL h
    have h4 := inRegion_mono hc₁ q hs
    linarith
  push Not at h2
  obtain ⟨hsq, him⟩ := h2
  have hseq : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [him])
  refine ⟨h1, hsq, him, ?_, ?_, hseq⟩
  · have h4 := inRegion_mono hc₂ q hs
    rw [him, abs_zero, zero_add, mul_comm] at h4
    exact h4
  · rw [← hseq]
    exact hL

theorem main : Formalism.ZeroFreeDirichlet.ZFRDirichlet := by
  obtain ⟨c₁, hc₁, hA⟩ := GlobalTheory.ZeroFreeComplex.zero_free_region
  obtain ⟨c₂, hc₂, hB⟩ := GlobalTheory.RealZeroNearOne.main
  obtain ⟨c₃, hc₃, hC⟩ := GlobalTheory.ZeroFreePrincipal.zero_free
  refine ⟨min c₁ (min c₂ c₃), lt_min hc₁ (lt_min hc₂ hc₃), ?_⟩
  intro q _ χ s hs hz
  have m₁ : min c₁ (min c₂ c₃) ≤ c₁ := min_le_left _ _
  have m₂ : min c₁ (min c₂ c₃) ≤ c₂ := (min_le_right _ _).trans (min_le_left _ _)
  have m₃ : min c₁ (min c₂ c₃) ≤ c₃ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨h1, hsq, him, hre, hL, hseq⟩ := real_zero_of_mem_zeroFreeRegion m₁ m₂ m₃ hA hC hs hz
  have hself := hB q χ χ s.re s.re h1 h1 hsq hsq hre hre hL hL
  refine ⟨hsq, h1, him, ?_, ?_⟩
  · rw [hseq]
    exact hself.2.2
  · intro χ' s' hs' hz'
    obtain ⟨h1', hsq', -, hre', hL', hseq'⟩ := real_zero_of_mem_zeroFreeRegion m₁ m₂ m₃ hA hC hs' hz'
    obtain ⟨hχ, hβ, -⟩ := hB q χ' χ s'.re s.re h1' h1 hsq' hsq hre' hre hL' hL
    refine ⟨hχ, ?_⟩
    rw [hseq', hseq, hβ]

end GlobalTheory.LandauPageRegion
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem _root_.GlobalTheory.T.integralClosure_completedCMAlgebra_compact_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : HeightOneSpectrum (𝓞 F), IsCompact (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E)) ∧ IsOpen (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E)) := by
  first | exact @GlobalTheory.CompletedOrder.isCompact_isOpen_integralClosure | exact GlobalTheory.CompletedOrder.isCompact_isOpen_integralClosure | (intros; apply GlobalTheory.CompletedOrder.isCompact_isOpen_integralClosure <;> assumption)
end

section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.MultSieve

theorem norm_sq_gaussSum {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar (N := q))‖ ^ 2 = q := by
  have h := GlobalTheory.GaussInt.gaussSum_mul_gaussSum_inv_of_isPrimitive hχ (ZMod.isPrimitive_stdAddChar q)
  rw [← star_gaussSum_eq] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simpa using h

theorem sum_norm_sq_char {q : ℕ} [NeZero q] (F : ZMod q → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2
      = q.totient * ∑ b : ZMod q, if IsUnit b then ‖F b‖ ^ 2 else 0 := by
  classical
  apply Complex.ofReal_injective
  have key : ∀ χ : DirichletCharacter ℂ q, ((‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2 : ℝ) : ℂ)
      = ∑ b : ZMod q, ∑ c : ZMod q, (χ⁻¹ b * χ c) * (F b * (starRingEnd ℂ) (F c)) := by
    intro χ

    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    have : (starRingEnd ℂ) (χ⁻¹ c) = χ c := by
      have := MulChar.star_apply' χ⁻¹ c
      rwa [inv_inv] at this
    rw [map_mul, this]; ring
  rw [Complex.ofReal_sum]
  simp_rw [key]
  rw [Finset.sum_comm, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  by_cases hb : IsUnit b
  · have h1 : ∀ c : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ⁻¹ b * χ c
        = if b = c then (q.totient : ℂ) else 0 := by
      intro c
      rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb c]
      refine Finset.sum_congr rfl fun χ _ => ?_
      obtain ⟨u, rfl⟩ := hb
      rw [MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
    simp [h1, hb, Complex.mul_conj']
  · simp [hb, MulChar.map_nonunit _ hb]

theorem sum_primitive_le {q : ℕ} [NeZero q] (s : Finset ℕ) (a : ℕ → ℂ) :
    ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ q | χ.IsPrimitive}, ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2
      ≤ ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        ‖∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * n * (((b : ℝ) / q : ℝ) : ℂ))‖ ^ 2 := by
  classical
  set F : ZMod q → ℂ := fun b => ∑ n ∈ s, a n * ZMod.stdAddChar ((n : ZMod q) * b) with hF
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have h1 : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      q * ‖∑ n ∈ s, a n * χ (n : ZMod q)‖ ^ 2 = ‖∑ b : ZMod q, χ⁻¹ b * F b‖ ^ 2 := by
    intro χ hχ
    have hχ' : (χ⁻¹).IsPrimitive := by
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
    rw [← norm_sq_gaussSum hχ', ← mul_pow, ← norm_mul]
    congr 2
    simp only [hF, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h := gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := q)) hχ' (n : ZMod q)
    rw [inv_inv] at h
    rw [mul_left_comm, mul_comm (gaussSum _ _), ← h, gaussSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [AddChar.mulShift_apply]; ring
  have h2 : ∑ b : ZMod q, (if IsUnit b then ‖F b‖ ^ 2 else 0)
      = ∑ b ∈ (Finset.range q).filter (fun b => Nat.Coprime b q),
        ‖∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * n * (((b : ℝ) / q : ℝ) : ℂ))‖ ^ 2 := by
    rw [Finset.sum_filter]
    symm
    refine Finset.sum_nbij' (fun b => (b : ZMod q)) (fun b => b.val) (by simp)
      (fun b _ => by simpa using ZMod.val_lt b)
      (fun b hb => ZMod.val_cast_of_lt (by simpa using hb)) (by simp) ?_
    intro b _
    refine if_congr (ZMod.isUnit_iff_coprime b q).symm ?_ rfl
    congr 2
    refine Finset.sum_congr rfl fun n _ => ?_
    have := ZMod.stdAddChar_coe (N := q) ((n * b : ℕ) : ℤ)
    push_cast at this
    rw [this]
    congr 2
    push_cast; ring
  rw [← h2]
  have h3 : {χ : DirichletCharacter ℂ q | χ.IsPrimitive}
      = ↑(Finset.univ.filter fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) := by simp
  rw [h3, finsum_mem_coe_finset]
  refine le_of_mul_le_mul_left ?_ hq
  rw [Finset.mul_sum, Finset.sum_congr rfl fun χ hχ => h1 χ (Finset.mem_filter.1 hχ).2]
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun _ _ _ => by positivity).trans ?_
  rw [sum_norm_sq_char]
  refine mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le q)
    (Finset.sum_nonneg fun b _ => by split_ifs <;> positivity)

theorem farey_spaced (Q q r b c : ℕ) (hq : q ≤ Q) (hr : r ≤ Q) (hb : b < q) (hc : c < r)
    (hne : (b : ℝ) / q ≠ (c : ℝ) / r) (k : ℤ) :
    1 / (Q : ℝ) ^ 2 ≤ |(b : ℝ) / q - (c : ℝ) / r - k| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hb1 : (b : ℝ) / q < 1 := (div_lt_one hq0).2 (by exact_mod_cast hb)
  have hc1 : (c : ℝ) / r < 1 := (div_lt_one hr0).2 (by exact_mod_cast hc)
  have hb0 : 0 ≤ (b : ℝ) / q := by positivity
  have hc0 : 0 ≤ (c : ℝ) / r := by positivity
  have hk : (b : ℝ) / q - (c : ℝ) / r - k ≠ 0 := by
    intro h
    have h1 : (k : ℝ) < 1 := by linarith
    have h2 : (-1 : ℝ) < k := by linarith
    have h1' : k < 1 := by exact_mod_cast h1
    have h2' : -1 < k := by exact_mod_cast h2
    have : k = 0 := by omega
    subst this
    apply hne
    simp at h
    linarith
  have he : (b : ℝ) / q - (c : ℝ) / r - k = ((b * r - c * q - k * q * r : ℤ) : ℝ) / (q * r) := by
    push_cast; field_simp
  rw [he] at hk ⊢
  have hm : (b * r - c * q - k * q * r : ℤ) ≠ 0 := by
    intro h; rw [h] at hk; simp at hk
  have hm1 : (1 : ℝ) ≤ |((b * r - c * q - k * q * r : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hm
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * r)]
  have hq' : (q : ℝ) ≤ Q := by exact_mod_cast hq
  have hr' : (r : ℝ) ≤ Q := by exact_mod_cast hr
  rw [sq]
  gcongr

theorem reduced_inj {q r b c : ℕ} (hq : 0 < q) (hr : 0 < r) (hb : Nat.Coprime b q)
    (hc : Nat.Coprime c r) (h : (b : ℝ) / q = (c : ℝ) / r) : q = r ∧ b = c := by
  have := Rat.div_int_inj (a := b) (b := q) (c := c) (d := r) (by exact_mod_cast hq)
    (by exact_mod_cast hr) (by simpa using hb) (by simpa using hc)
    (by apply Rat.cast_injective (α := ℝ); push_cast; exact h)
  omega

end GlobalTheory.MultSieve

namespace GlobalTheory

theorem multiplicative_large_sieve : ∀ (Q M N : ℕ) (a : ℕ → ℂ), 1 ≤ Q → ∑ q ∈ Finset.range Q, ∑ᶠ χ ∈ {χ : DirichletCharacter ℂ (q + 1) | χ.IsPrimitive}, ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod (q + 1))‖ ^ 2 ≤ ((Q : ℝ) ^ 2 + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  intro Q M N a hQ
  classical
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  set P := (Finset.range Q).sigma
    (fun q => (Finset.range (q + 1)).filter (fun b => Nat.Coprime b (q + 1))) with hP
  set φ : (Σ _ : ℕ, ℕ) → ℝ := fun p => (p.2 : ℝ) / ((p.1 + 1 : ℕ) : ℝ) with hφ
  have hmem : ∀ p ∈ P, p.1 < Q ∧ p.2 < p.1 + 1 ∧ Nat.Coprime p.2 (p.1 + 1) := by
    intro p hp
    simpa only [hP, Finset.mem_sigma, Finset.mem_range, Finset.mem_filter] using hp
  have hinj : Set.InjOn φ P := by
    rintro ⟨q, b⟩ hp ⟨r, c⟩ hp' h
    obtain ⟨h1, h2⟩ := MultSieve.reduced_inj (Nat.succ_pos q) (Nat.succ_pos r)
      (hmem _ hp).2.2 (hmem _ hp').2.2 h
    obtain rfl : q = r := by omega
    obtain rfl : b = c := h2
    rfl
  have h := additive_large_sieve M N a (P.image φ) (1 / (Q : ℝ) ^ 2) (by positivity)
    (by rw [div_le_one (by positivity)]; nlinarith) ?_
  · rw [Finset.sum_image hinj, one_div_one_div, hP, Finset.sum_sigma] at h
    exact (Finset.sum_le_sum fun q _ => MultSieve.sum_primitive_le _ a).trans h
  · intro x hx y hy hxy k
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 hy
    exact MultSieve.farey_spaced Q _ _ _ _ (hmem _ hp).1 (hmem _ hp').1 (hmem _ hp).2.1
      (hmem _ hp').2.1 hxy k

end GlobalTheory
end

section

open Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.finite_quadratic_characters_in_adjoint' : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (r : Γ →* GL (Fin n) k), Set.Finite {χ : Γ →* ℤˣ | ∃ X : Matrix (Fin n) (Fin n) k, X ≠ 0 ∧ ∀ g, ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((χ g : ℤ) : k) • (X * ((r g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))} := by
  first | exact @GlobalTheory.finite_quadratic_characters_in_adjoint | exact GlobalTheory.finite_quadratic_characters_in_adjoint | (intros; apply GlobalTheory.finite_quadratic_characters_in_adjoint <;> assumption)
end

section

open Formalism.MainNotions.N

namespace GlobalTheory

theorem _root_.GlobalTheory.commute_on_ker_of_commute_on_ker_inter :
    ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ₀ : Γ →* GL (Fin n) k) (η₀ η : Γ →* ℤˣ), (∀ X : Matrix (Fin n) (Fin n) k, (∀ g, ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((η g : ℤ) : k) • (X * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0) → (∀ X : Matrix (Fin n) (Fin n) k, (∀ g, ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = (((η * η₀) g : ℤ) : k) • (X * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0) → ∀ Y : Matrix (Fin n) (Fin n) k, (∀ g, η₀ g = 1 → η g = 1 → ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) → ∀ g, η₀ g = 1 → ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro Γ k _ _ _ n ρ₀ η₀ η hη hηη₀ Y hY g hg
  obtain ⟨Y₁, Y₂, rfl, h₁, h₂⟩ :=
    _root_.GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel Γ k n ρ₀ ρ₀ η₀.ker 1 η Y
      (fun g hg h1 => by simpa using hY g (MonoidHom.mem_ker.mp hg) h1)
  obtain ⟨A, B, hAB, hA, hB⟩ :=
    _root_.GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel Γ k n ρ₀ ρ₀ ⊤ η η₀ Y₂
      (fun g _ h1 => by simpa using h₂ g (MonoidHom.mem_ker.mpr h1))
  have hA0 : A = 0 := hη A (fun g => hA g (Subgroup.mem_top g))
  have hB0 : B = 0 := hηη₀ B (fun g => hB g (Subgroup.mem_top g))
  have hY₂ : Y₂ = 0 := by rw [hAB, hA0, hB0, add_zero]
  subst hY₂
  simpa using h₁ g (MonoidHom.mem_ker.mpr hg)

end GlobalTheory
end

section

open Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.exists_rep_agreeing_on_kernels : ∀ (Γ k : Type) [Group Γ] [Field k] (n : ℕ) (ρ₀ ρ' : Γ →* GL (Fin n) k) (η₀ η : Γ →* ℤˣ) (P : GL (Fin n) k) (s : Γ), η₀ s = 1 → η s = -1 → (∀ g, η₀ g = 1 → η g = 1 → ρ' g = P⁻¹ * ρ₀ g * P) → (∀ Y : Matrix (Fin n) (Fin n) k, (∀ g, η₀ g = 1 → η g = 1 → ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) → ((ρ₀ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) → ∃ ρ : Γ →* GL (Fin n) k, (∀ g, η₀ g = 1 → ρ g = ρ₀ g) ∧ ∀ g, η g = 1 → ρ g = P * ρ' g * P⁻¹ := by
  first | exact @GlobalTheory.exists_rep_patch_twist | exact GlobalTheory.exists_rep_patch_twist | (intros; apply GlobalTheory.exists_rep_patch_twist <;> assumption)
end

section

open Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.twistedIntertwiner_decomp_of_quadraticKernel' : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (σ σ' : Γ →* GL (Fin n) k) (S : Subgroup Γ) (χ η : Γ →* ℤˣ) (X : Matrix (Fin n) (Fin n) k), (∀ g ∈ S, η g = 1 → ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((χ g : ℤ) : k) • (X * ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → ∃ X₁ X₂ : Matrix (Fin n) (Fin n) k, X = X₁ + X₂ ∧ (∀ g ∈ S, ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X₁ = ((χ g : ℤ) : k) • (X₁ * ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) ∧ (∀ g ∈ S, ((σ' g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X₂ = (((χ * η) g : ℤ) : k) • (X₂ * ((σ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) := by
  first | exact @GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel | exact GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel | (intros; apply GlobalTheory.twistedIntertwiner_decomp_of_quadraticKernel <;> assumption)
end

end

section

@[expose] public section

open Formalism.MainNotions.N
theorem _root_.GlobalTheory.T.intertwiner_zero_of_character_twist : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ₀ : Γ →* GL (Fin n) k) (η₀ η : Γ →* ℤˣ), (∀ X : Matrix (Fin n) (Fin n) k, (∀ g, ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = ((η g : ℤ) : k) • (X * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0) → (∀ X : Matrix (Fin n) (Fin n) k, (∀ g, ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X = (((η * η₀) g : ℤ) : k) • (X * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) → X = 0) → ∀ Y : Matrix (Fin n) (Fin n) k, (∀ g, η₀ g = 1 → η g = 1 → ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) → ∀ g, η₀ g = 1 → ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * Y = Y * ((ρ₀ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  first | exact @GlobalTheory.commute_on_ker_of_commute_on_ker_inter | exact GlobalTheory.commute_on_ker_of_commute_on_ker_inter | (intros; apply GlobalTheory.commute_on_ker_of_commute_on_ker_inter <;> assumption)

end
end
