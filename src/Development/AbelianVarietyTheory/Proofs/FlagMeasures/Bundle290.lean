module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle278
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
import Formalism.FormalDegreeBessel.FinalG
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle119
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle137
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LatExistsOfSteps
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle285
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle106
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle080
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTotalMassLeGenericMass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.MeasureTheory.Function.L2Space
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.InnerInt

theorem hpk_det_isUnit (k r : ℕ) : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1

theorem gg_mul {k r : ℕ} {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  (uHGroup _ (Hpk k r) (hpk_det_isUnit k r)).2.1 a ha b hb

theorem gg_inv {k r : ℕ} {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det ∧ a⁻¹ ∈ GG k r :=
  (uHGroup _ (Hpk k r) (hpk_det_isUnit k r)).2.2 a ha

theorem inner_map_of_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (u v : H) : ⟪T u, T v⟫_ℂ = ⟪u, v⟫_ℂ :=
  (⟨T.toLinearMap, fun v => hT v⟩ : H →ₗᵢ[ℂ] H).inner_map_map u v

theorem star_coef_mul_eq {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (hσ : IsURepOn (GG k r) σ) (w : H) {y s x : Mat k r}
    (hy : y ∈ GG k r) (hs : s ∈ GG k r) (hx : x ∈ GG k r) :
    star (coef σ w w (y⁻¹ * (s * x))) = coef σ (σ y w) (σ x w) s⁻¹ := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hσ
  obtain ⟨hyu, hyi⟩ := gg_inv hy
  obtain ⟨hsu, hsi⟩ := gg_inv hs
  have e1 : σ (y⁻¹ * (s * x)) = (σ y⁻¹).comp ((σ s).comp (σ x)) := by
    rw [hmul _ hyi _ (gg_mul hs hx), hmul _ hs _ hx]
  have e2 : ∀ v, σ y (σ y⁻¹ v) = v := by
    intro v
    have h := hmul _ hy _ hyi
    rw [Matrix.mul_nonsing_inv _ hyu, h1] at h
    have := congrArg (fun T : H →L[ℂ] H => T v) h
    simpa using this.symm
  have e3 : ∀ v, σ s⁻¹ (σ s v) = v := by
    intro v
    have h := hmul _ hsi _ hs
    rw [Matrix.nonsing_inv_mul _ hsu, h1] at h
    have := congrArg (fun T : H →L[ℂ] H => T v) h
    simpa using this.symm
  simp only [coef]
  rw [e1, ← starRingEnd_apply, inner_conj_symm]
  simp only [ContinuousLinearMap.comp_apply]
  have i1 := inner_map_of_norm (σ y) (hiso y hy) (σ y⁻¹ (σ s (σ x w))) w
  rw [e2] at i1
  rw [← i1]
  have i2 := inner_map_of_norm (σ s⁻¹) (hiso _ hsi) (σ s (σ x w)) (σ y w)
  rw [e3] at i2
  rw [← i2]

end GlobalTheory.SgInf.InnerInt


open GlobalTheory.SgInf.InnerInt in
theorem GlobalTheory.SgInf.inner_integral_eq_be : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ W : Mat k r → Wp, IsSPsiEquiv z (psiGen k r z c) π W → ∀ y ∈ GG k r, ∀ x : Mt k r, Matrix.of x ∈ GG k r → ∫ s, star (coef σ w w (y⁻¹ * (Matrix.of s * Matrix.of x))) • W (Matrix.of s * Matrix.of x) ∂μS = be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of x) w) (W (Matrix.of x)) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hstd hside W hW y hy x hx
  have hσ : IsURepOn (GG k r) σ := hstd.2.1
  have hdec : Decay σ (DD σ w : Set H) a := hstd.2.2.2.2.2.2.2.1
  have hz := hside.1
  have hT := hside.2.1
  have hπ := hside.2.2.1
  have hhaar := hside.2.2.2.1
  have hSG : Sset k r z ⊆ GG k r := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT).2.2.2.1.1
  have hpis := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ
  have huni := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hhaar
  have hstab : ∀ g ∈ GG k r, ∀ v ∈ (DD σ w : Set H), σ g v ∈ (DD σ w : Set H) := by
    intro g hg v hv
    have hle : Submodule.map (σ g).toLinearMap (DD σ w) ≤ DD σ w := by
      rw [DD, Submodule.map_span_le]
      rintro _ ⟨g', hg', rfl⟩
      have : (σ g).toLinearMap (σ g' w) = σ (g * g') w := by
        rw [hσ.1.2 g hg g' hg']; rfl
      rw [this]; exact mem_DD σ w (gg_mul hg hg')
    exact hle ⟨v, hv, rfl⟩
  have hD := GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hstd hside (DD σ w : Set H) hstab hdec
    (σ y w) (mem_DD σ w hy) (σ (Matrix.of x) w) (mem_DD σ w hx)
  have hFi := hD.1
  have hGi := hFi.apply_continuousLinearMap (W (Matrix.of x))
  have hm : AEStronglyMeasurable (fun s : Mt k r => (coef σ (σ y w) (σ (Matrix.of x) w) (Matrix.of s) •
      PiS (psiGen k r z c) π (Matrix.of s)⁻¹) (W (Matrix.of x))) (μS.map invM) := by
    rw [huni.2]; exact hGi.aestronglyMeasurable
  have hmap := integral_map measurable_invM.aemeasurable hm
  rw [huni.2] at hmap
  unfold be
  rw [ContinuousLinearMap.integral_apply hFi, hmap]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := ae_iff.2 hhaar.2.2.1
  filter_upwards [hae] with s hs
  have hsG := hSG hs
  have hdet := (gg_inv hsG).1
  obtain ⟨h, hh, m, hm', hsm⟩ := hs
  rw [of_invM, Matrix.nonsing_inv_nonsing_inv _ hdet, ContinuousLinearMap.smul_apply,
    star_coef_mul_eq σ hσ w hy hsG hx]
  congr 1
  rw [hsm, hW h hh m hm' _ hx, (hpis.1 h hh m hm').2, ContinuousLinearMap.smul_apply]
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.SInt

theorem sint_eq_inner_be : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∫ t, ⟪v, σ (Matrix.of t)⁻¹ v⟫_ℂ * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS = ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide v hv ξ
  have hURep : IsURepOn (GG k r) σ := hStd.2.1
  have hDecay : Decay σ (DD σ w : Set H) a := hStd.2.2.2.2.2.2.2.1
  obtain ⟨hz, hT, hπ, hHaar, -⟩ := id hSide
  have hstab : ∀ g ∈ GG k r, ∀ u ∈ (DD σ w : Set H), σ g u ∈ (DD σ w : Set H) :=
    (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hURep).1
  have hint := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hstab hDecay v hv v hv).1
  let f : Mt k r → (Wp →L[ℂ] Wp) := fun s =>
    coef σ v v (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ Wp ξ)
  have hL : ∀ A, L A = ⟪ξ, A ξ⟫_ℂ := fun A => rfl
  have hRHS : ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ = ∫ s, L (f s) ∂μS := by
    rw [← hL]; exact (L.integral_comp_comm hint).symm
  have hunim : μS.map invM = μS := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hHaar).2
  have hmeas : AEStronglyMeasurable (fun s => L (f s)) μS :=
    L.continuous.comp_aestronglyMeasurable hint.aestronglyMeasurable
  have hsub : ∀ᵐ t ∂μS, Matrix.of t ∈ Sset k r z := ae_iff.2 hHaar.2.2.1
  have hchange : ∫ s, L (f s) ∂μS = ∫ t, L (f (invM t)) ∂μS := by
    conv_lhs => rw [← hunim]
    exact integral_map measurable_invM.aemeasurable (by rw [hunim]; exact hmeas)
  rw [hRHS, hchange]
  refine integral_congr_ae ?_
  filter_upwards [hsub] with t ht
  have hGG : Matrix.of t ∈ GG k r := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT).2.2.2.1.1 ht
  have hu : IsUnit (Matrix.of t : Mat k r).det :=
    ((uHGroup _ (Hpk k r) (Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1)).2.2 _ hGG).1
  have hadj := ((GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ).2.2.1 _ ht).2
  simp only [hL, f, coef, of_invM, Matrix.nonsing_inv_nonsing_inv _ hu,
    ContinuousLinearMap.smul_apply, inner_smul_right]
  rw [← hadj, ContinuousLinearMap.adjoint_inner_left]

end GlobalTheory.SgInf.SInt
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem afun_inner_eq_integral : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ x : Mt k r, Matrix.of x ∈ GG k r → ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ = ∫ s, coef σ u v (Matrix.of (lmulM (Matrix.of s) x)) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of (lmulM (Matrix.of s) x)), ξ⟫_ℂ ∂μS := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ x hx
  have hσ : IsURepOn (GG k r) σ := hStd.2.1
  have hDec : Decay σ (DD σ w) a := hStd.2.2.2.2.2.2.2.1
  have hzb : inWb k r z := hSide.1
  have hTz : 0 < Tz k r z := hSide.2.1
  have hπ : IsURepOn (UWset k r z) π := hSide.2.2.1
  have hμS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  have hstab := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hσ).1
  have hSsub : Sset k r z ⊆ GG k r := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hzb hTz).2.2.2.1.1
  have hD1 := GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hstab hDec
  have hxu : σ (Matrix.of x) u ∈ DD σ w := hstab _ hx u hu
  have hxu₁ : σ (Matrix.of x) u₁ ∈ DD σ w := hstab _ hx u₁ hu₁
  obtain ⟨hint, -, -, -⟩ := hD1 _ hxu v hv
  obtain ⟨-, heq₁, -, -⟩ := hD1 _ hxu₁ v hv
  have hPi := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hzb hTz hπ
  have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := by rw [ae_iff]; exact hμS.2.2.1
  show ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x),
      be (psiGen k r z c) π μS σ (σ (Matrix.of x) u) v ξ⟫_ℂ = _
  rw [be, ContinuousLinearMap.integral_apply hint, ← integral_inner (hint.apply_continuousLinearMap ξ)]
  refine integral_congr_ae ?_
  filter_upwards [hae] with s hs
  have hsG : Matrix.of s ∈ GG k r := hSsub hs
  have hmul : σ (Matrix.of s * Matrix.of x) = (σ (Matrix.of s)).comp (σ (Matrix.of x)) :=
    hσ.1.2 _ hsG _ hx
  have hcoef : coef σ (σ (Matrix.of x) u) v (Matrix.of s) =
      coef σ u v (Matrix.of (lmulM (Matrix.of s) x)) := by
    show ⟪v, σ (Matrix.of s) (σ (Matrix.of x) u)⟫_ℂ = ⟪v, σ (Matrix.of s * Matrix.of x) u⟫_ℂ
    rw [hmul]; rfl
  have hadj := ((hPi.2.2.1) _ hs).2
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, hcoef]
  congr 1
  rw [← hadj, ContinuousLinearMap.adjoint_inner_right]
  congr 1
  show PiS (psiGen k r z c) π (Matrix.of s) (be (psiGen k r z c) π μS σ (σ (Matrix.of x) u₁) v ξ) =
    be (psiGen k r z c) π μS σ (σ (Matrix.of s * Matrix.of x) u₁) v ξ
  rw [hmul, ContinuousLinearMap.comp_apply, (heq₁ _ hs).1]
  rfl

end GlobalTheory.SgInf
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem coef_mul_inner_Afun_eq_integral : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ y : Mt k r, Matrix.of y ∈ GG k r → coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ = ∫ t, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ y hy
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hSG : Sset k r z ⊆ GG k r := hcl.2.2.2.1.1
  have hstab : ∀ g ∈ GG k r, ∀ x ∈ DD σ w, σ g x ∈ DD σ w := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hStd.2.1).1
  have hu₂ : σ (Matrix.of y) u₁ ∈ DD σ w := hstab _ hy u₁ hu₁
  have hint := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w : Set H) hstab
    hStd.2.2.2.2.2.2.2.1 _ hu₂ v hv).1
  have hint2 := hint.apply_continuousLinearMap ξ
  have hA : Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y) =
      ∫ s, (coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹) ξ ∂μS := by
    unfold Afun be
    exact ContinuousLinearMap.integral_apply hint ξ
  have hinner : ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ =
      ∫ s, ⟪(coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹) ξ, ξ⟫_ℂ ∂μS := by
    rw [hA, ← inner_conj_symm, ← integral_inner hint2, ← integral_conj]
    congr 1; funext s; rw [inner_conj_symm]
  rw [hinner, ← integral_const_mul]
  have hS0 : μS {x | Matrix.of x ∉ Sset k r z} = 0 := hSide.2.2.2.1.2.2.1
  refine integral_congr_ae ?_
  have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := by
    rw [ae_iff]; simpa using hS0
  filter_upwards [hae] with s hs
  have hmul : σ (Matrix.of s * Matrix.of y) = (σ (Matrix.of s)).comp (σ (Matrix.of y)) :=
    hStd.2.1.1.2 _ (hSG hs) _ hy
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left]
  have hc : coef σ (σ (Matrix.of y) u₁) v (Matrix.of s) = coef σ u₁ v (Matrix.of s * Matrix.of y) := by
    simp only [coef, hmul, ContinuousLinearMap.comp_apply]
  rw [hc, mul_assoc]
  rfl

end GlobalTheory.SgInf
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.FolnerLimit

theorem mul_mem_GG {k r : ℕ} {g g' : Mat k r} (hg : g ∈ GG k r) (hg' : g' ∈ GG k r) : g * g' ∈ GG k r := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 : g'ᴴ * Hpk k r * g' = Hpk k r := hg'
  show (g * g')ᴴ * Hpk k r * (g * g') = Hpk k r
  calc (g * g')ᴴ * Hpk k r * (g * g') = g'ᴴ * (gᴴ * Hpk k r * g) * g' := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1, h2]

theorem DD_stable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (w : H) :
    ∀ g ∈ GG k r, ∀ v ∈ (DD σ w : Set H), σ g v ∈ (DD σ w : Set H) := by
  intro g hg v hv
  have hv' : v ∈ DD σ w := hv
  show σ g v ∈ DD σ w
  unfold DD at hv'
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g', hg', rfl⟩ := hx
    have := hσ.1.2 g hg g' hg'
    have h2 : σ g (σ g' w) = σ (g * g') w := by rw [this]; rfl
    rw [h2]
    exact mem_DD σ w (mul_mem_GG hg hg')
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add (f := _)]; exact (DD σ w).add_mem (ihx hx) (ihy hy)
  | smul c x hx ih => rw [map_smul]; exact (DD σ w).smul_mem c (ih hx)

theorem measurable_overlap {k r : ℕ} (μ : Measure (Mt k r)) [SFinite μ] {Ω : Set (Mt k r)}
    (hΩ : MeasurableSet Ω) :
    Measurable fun p : Mt k r => μ {s | s ∈ Ω ∧ lmulM (Matrix.of p) s ∈ Ω} := by
  have hc : Continuous fun q : Mt k r × Mt k r => lmulM (Matrix.of q.1) q.2 :=
    Continuous.matrix_mul (A := fun q : Mt k r × Mt k r => (Matrix.of q.1 : Mat k r))
      (B := fun q : Mt k r × Mt k r => (Matrix.of q.2 : Mat k r)) continuous_fst continuous_snd
  have hm : MeasurableSet {q : Mt k r × Mt k r | q.2 ∈ Ω ∧ lmulM (Matrix.of q.1) q.2 ∈ Ω} :=
    (measurable_snd hΩ).inter (hc.measurable hΩ)
  exact measurable_measure_prodMk_left hm

theorem tendsto_of_integrable {k r : ℕ} {S : Set (Mat k r)} {μ : Measure (Mt k r)} (hμ : IsHaarOn S μ)
    {Om : ℕ → Set (Mt k r)} (hO : IsFolner S μ Om) {f : Mt k r → ℂ} (hf : Integrable f μ) :
    Filter.Tendsto (fun j => (∫ p, ((μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j}).toReal : ℂ) * f p ∂μ)
      / ((μ (Om j)).toReal : ℂ)) Filter.atTop (nhds (∫ p, f p ∂μ)) := by
  haveI : SigmaFinite μ := hμ.1
  have hae : ∀ᵐ p ∂μ, (Matrix.of p : Mat k r) ∈ S := hμ.2.2.1
  have heq : ∀ j, (∫ p, ((μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j}).toReal : ℂ) * f p ∂μ)
      / ((μ (Om j)).toReal : ℂ) =
      ∫ p, (((μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j} / μ (Om j)).toReal : ℝ) : ℂ) * f p ∂μ := by
    intro j
    rw [← integral_div]
    congr 1
    funext p
    rw [ENNReal.toReal_div]
    push_cast
    ring
  simp only [heq]
  refine tendsto_integral_of_dominated_convergence (fun p => ‖f p‖) (fun j => ?_) hf.norm (fun j => ?_) ?_
  · refine AEStronglyMeasurable.mul ?_ hf.1
    have := ((measurable_overlap μ (hO.1 j).1).div_const (μ (Om j))).ennreal_toReal
    exact (Complex.measurable_ofReal.comp this).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    have h1 : μ {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j} / μ (Om j) ≤ 1 :=
      ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono fun s hs => hs.1)
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h1
  · filter_upwards [hae] with p hp
    have h1 := GlobalTheory.T.folner_single_translate_proportion_tendsto_one k r S μ Om hO _ hp
    have h2 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1
    have h3 := (Complex.continuous_ofReal.tendsto _).comp h2
    have h4 := h3.mul_const (f p)
    simpa [Function.comp_def] using h4

theorem folner_limit : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ Om : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om → ∀ y ∈ DD σ w, ∀ ξ : Wp, Filter.Tendsto (fun j => (∫ p, ((μS {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j}).toReal : ℂ) * (coef σ y y (Matrix.of p) * ⟪ξ, PiS (psiGen k r z c) π (Matrix.of p)⁻¹ ξ⟫_ℂ) ∂μS) / ((μS (Om j)).toReal : ℂ)) Filter.atTop (nhds ⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide Om hO y hy ξ
  have hint := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w)
    (DD_stable hStd.2.1 w) hStd.2.2.2.2.2.2.2.1 y hy y hy).1
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ Wp ξ)
  have hL : ∀ T : Wp →L[ℂ] Wp, L T = ⟪ξ, T ξ⟫_ℂ := fun T => rfl
  have hfun : (fun p : Mt k r => L (coef σ y y (Matrix.of p) • PiS (psiGen k r z c) π (Matrix.of p)⁻¹)) =
      fun p => coef σ y y (Matrix.of p) * ⟪ξ, PiS (psiGen k r z c) π (Matrix.of p)⁻¹ ξ⟫_ℂ := by
    funext p
    rw [map_smul, hL, smul_eq_mul]
  have hf := L.integrable_comp hint
  have hI := L.integral_comp_comm hint
  rw [hfun] at hf hI
  have := tendsto_of_integrable hSide.2.2.2.1 hO hf
  rw [hI] at this
  exact this

end GlobalTheory.SgInf.FolnerLimit
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.genLin_tamagawa_volume : GenLinVolume := by
  first | exact @GlobalTheory.FlagMeas.genLinVolume | exact GlobalTheory.FlagMeas.genLinVolume | (intros; apply GlobalTheory.FlagMeas.genLinVolume <;> assumption)
end

section

noncomputable section

open Formalism.MainNotions.ArithmeticCylinders IsDedekindDomain MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MultTranslate

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
  {θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}

theorem isCuspFun_rTr {φ : GA D V → ℂ} (h : IsCuspFun V φ) (x : GA D V) : IsCuspFun V (rTr V x φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 g
  simpa only [rTr, mul_assoc] using h r C hC μ 𝓕 hμ h𝓕 (g * x)

theorem isMultMap_rTr {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {x : GA D V} (hx : x ∈ GfC V)
    (hJ : ∀ k ∈ J', x⁻¹ * k * x ∈ J ∧ χ' k = χ (x⁻¹ * k * x)) {T : MMap M} (h : IsMultMap θ M J χ T) :
    IsMultMap θ M J' χ' (postOn M (GlobalTheory.FinTranslate.rTrL V x) T) := by
  constructor
  · intro v
    exact GlobalTheory.FinTranslate.isAutFunSm_rTr θ V x hx _ (h.aut v)
  · intro v
    exact isCuspFun_rTr (h.cusp v) x
  · intro v k hk g
    change T v (g * k * x) = χ' k * T v (g * x)
    rw [(hJ k hk).2, ← h.lev v _ (hJ k hk).1]
    group
  · intro τ g hg v w hw
    funext y
    change T (Function.update v τ w) (y * x) = T v (y * atTau θ V τ g * x)
    rw [h.equiv τ g hg v w hw, mul_assoc,
      ← GlobalTheory.FinTranslate.comm_fin_real V hx (GlobalTheory.FinTranslate.atTau_mem θ V τ g), ← mul_assoc]
    rfl
  · intro τ v y
    exact h.cont τ v (y * x)

theorem postOn_mem_goodPart {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {x : GA D V} (hx : x ∈ GfC V)
    (hJ : ∀ k ∈ J', x⁻¹ * k * x ∈ J ∧ χ' k = χ (x⁻¹ * k * x)) {L L' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)}
    (hL : ∀ f, L' (rTr V x f) = rTr V x (L f)) {T : MMap M} (h : T ∈ goodPart θ M J χ L) :
    postOn M (GlobalTheory.FinTranslate.rTrL V x) T ∈ goodPart θ M J' χ' L' := by
  rw [mem_goodPart, GlobalTheory.MultMem.mem_mult_iff] at h ⊢
  refine ⟨isMultMap_rTr hx hJ h.1, fun v => ?_⟩
  change L' (rTr V x (T v)) = rTr V x (T v)
  rw [hL, h.2]

end GlobalTheory.MultTranslate

end
end

section

open Formalism.BasicNotions Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.St.Lat

theorem latExists_of_forms0 : ∀ D : D7, Formalism.L2.Forms.Forms0 D D.u₀ → LatExists D := by
  intro D hF
  refine GlobalTheory.St.Lat.latExists_of ?_ ?_ D ?_
  · exact GlobalTheory.T.exists_primitive_vector_norm_neg_hyperbolicPair
  · exact GlobalTheory.unramified_degree_one_of_ncard_placesOver
  · exact GlobalTheory.IsoOrthHyp.exists_isotropic_orth_hyp D hF

end GlobalTheory.St.Lat
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.datumStabilizer_preserves_termLattice_goodPlace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → P.PrimeTo → ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → LocNG.Datum.Stab d ≤ LocNG.Aut τ.abelian₂ := by
  first | exact @GlobalTheory.HL.StabLat.stab_le_aut | exact GlobalTheory.HL.StabLat.stab_le_aut | (intros; apply GlobalTheory.HL.StabLat.stab_le_aut <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitian_total_mass_le_generic_mass : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 d₁ : LocNG.Datum P) (t₁ : Term V M r), LocNG.IsTermOver P d₁ t₁ → ∀ Cl : Term V M r → Prop, (∀ t, Cl t ↔ ∃ s ∈ P.St, ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, A i j ∈ M.L.O ∧ A' i j ∈ M.L.O ∧ ∃ c ∈ M.L.O, A' i j - A i j = algebraMap F E (LocNG.theta M) * c) ∧ (∀ i j, j < i → A i j = 0 ∧ A' i j = 0) ∧ (∀ i, A i i = 1 ∧ A' i i = 1) ∧ (∀ j, t.f j = ∑ i, A i j • s (t₁.f i)) ∧ ∀ j, t.f' j = ∑ i, A' i j • s (t₁.f' i)) → ∀ g : ℝ≥0∞, g = ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : {t // t ∈ R.RT d.1 ∧ ¬ LocNG.BBne (H := H) t ∧ Cl t}, ENNReal.ofReal (LocNG.mu P t.1) → g ≠ ⊤ ∧ LocNG.nn R d0 ≤ ENNReal.ofReal (8 * P.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * g ∧ (P.PrimeTo → LocNG.nn R d0 = g) ∧ ((∃ t', LocNG.IsTermOver P d0 t') → g ≠ 0) := by
  first | exact @GlobalTheory.HL.AbsGenMass.total_le_generic | exact GlobalTheory.HL.AbsGenMass.total_le_generic | (intros; apply GlobalTheory.HL.AbsGenMass.total_le_generic <;> assumption)
end
