module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle247
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousMulEquivCongruenceTopologyAdelic
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle093
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle246
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightEventuallyZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle248
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Finiteness.Lattice
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.AverageDeriv

theorem hasDerivAt_average {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : G → (H →L[ℂ] H)} (hσ : IsURep σ) (w : H) {a : ℝ → G} (ha : Continuous a) (ha0 : a 0 = 1)
    {f f' : G → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (hf' : Continuous f')
    (hfc' : HasCompactSupport f')
    (hd : ∀ g t, HasDerivAt (fun s => f ((a s)⁻¹ * g)) (f' ((a t)⁻¹ * g)) t) :
    HasDerivAt (fun t => σ (a t) (∫ g, f g • σ g w ∂μ)) (∫ g, f' g • σ g w ∂μ) 0 := by
  obtain ⟨-, hmul, hnorm, hcont⟩ := hσ
  have hcw : Continuous fun g => σ g w := hcont w

  have key : ∀ t, σ (a t) (∫ g, f g • σ g w ∂μ) = ∫ g, f ((a t)⁻¹ * g) • σ g w ∂μ := by
    intro t
    have hint : Integrable (fun g => f g • σ g w) μ :=
      (hf.smul hcw).integrable_of_hasCompactSupport (hfc.smul_right)
    rw [← (σ (a t)).integral_comp_comm hint]
    rw [← integral_mul_left_eq_self (fun g => f ((a t)⁻¹ * g) • σ g w) (a t)]
    congr 1
    funext g
    rw [map_smul, inv_mul_cancel_left, hmul]
    rfl

  obtain ⟨C, hC⟩ := hf'.bounded_above_of_compact_support hfc'
  set K : Set G := (fun p : ℝ × G => a p.1 * p.2) '' (Set.Icc (-1 : ℝ) 1 ×ˢ tsupport f') with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.prod hfc').image ((ha.comp continuous_fst).mul continuous_snd)
  have hsupp : ∀ s ∈ Metric.ball (0 : ℝ) 1, ∀ g, g ∉ K → f' ((a s)⁻¹ * g) = 0 := by
    intro s hs g hg
    by_contra h
    apply hg
    refine ⟨(s, (a s)⁻¹ * g), ⟨?_, subset_tsupport _ h⟩, by simp⟩
    rw [Real.ball_eq_Ioo, zero_sub, zero_add] at hs
    exact Set.Ioo_subset_Icc_self hs
  have hbound_int : Integrable (K.indicator fun _ => C * ‖w‖) μ :=
    (continuousOn_const.integrableOn_compact hKc).integrable_indicator hKc.isClosed.measurableSet
  have hcont_tr : ∀ (k : G → ℂ), Continuous k → ∀ s : ℝ, Continuous fun g => k ((a s)⁻¹ * g) • σ g w :=
    fun k hk s => (hk.comp (continuous_const.mul continuous_id)).smul hcw
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun s g => f ((a s)⁻¹ * g) • σ g w) (F' := fun s g => f' ((a s)⁻¹ * g) • σ g w)
    (bound := K.indicator fun _ => C * ‖w‖) (Metric.ball_mem_nhds 0 one_pos)
    (Filter.Eventually.of_forall fun s => (hcont_tr f hf s).aestronglyMeasurable)
    (by
      simp only [ha0, inv_one, one_mul]
      exact (hf.smul hcw).integrable_of_hasCompactSupport (hfc.smul_right))
    (hcont_tr f' hf' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g s hs => by
      by_cases hg : g ∈ K
      · rw [Set.indicator_of_mem hg, norm_smul, hnorm]
        exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
      · rw [Set.indicator_of_notMem hg, hsupp s hs g hg, zero_smul, norm_zero])
    hbound_int
    (Filter.Eventually.of_forall fun g s _ => (hd g s).smul_const (σ g w))
  have hfun : (fun t => σ (a t) (∫ g, f g • σ g w ∂μ)) = fun t => ∫ g, f ((a t)⁻¹ * g) • σ g w ∂μ :=
    funext key
  rw [hfun]
  simpa only [ha0, inv_one, one_mul] using hder.2

theorem expU_zero {n : ℕ} {ε : Fin n → Bool} : expU (0 : gLie ε) = 1 := by
  apply Subtype.ext
  apply Units.ext
  refine (uMat_expU _).trans ?_
  simp

theorem expU_add {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (a b : ℝ) :
    expU ((a + b) • X) = expU (a • X) * expU (b • X) := by
  apply Subtype.ext
  apply Units.ext
  refine (uMat_expU _).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (uMat_expU (a • X)).symm (uMat_expU (b • X)).symm)
  rw [Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl _).smul_left a).smul_right b)

theorem expU_inv {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (t : ℝ) : (expU (t • X))⁻¹ = expU ((-t) • X) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← expU_add, add_neg_cancel, zero_smul, expU_zero]

theorem continuous_expU {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) : Continuous fun t : ℝ => expU (t • X) := by
  apply GlobalTheory.SobolevBound.continuous_expU <;> assumption

theorem hasDerivAt_exp_mul_entry {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) * Y) i j) ((X * (NormedSpace.exp (t • X) * Y)) i j) t := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) X t).mul_const Y
  let l : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h2 := (LinearMap.toContinuousLinearMap l).hasFDerivAt.comp_hasDerivAt t h
  have h3 : HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) * Y) i j)
      ((X * NormedSpace.exp (t • X) * Y) i j) t := h2
  rw [← mul_assoc]
  exact h3

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (X : gLie ε) (t : ℝ) (g : UJ ε) :
    uMat ((expU (t • X))⁻¹ * g) = NormedSpace.exp (t • (-X.1)) * uMat g := by
  rw [expU_inv]
  show uMat (expU ((-t) • X)) * uMat g = _
  rw [uMat_expU, Submodule.coe_smul, neg_smul, smul_neg]

theorem hasDerivAt_orbit_average : ∀ (B : RowsAut) (F : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ) (E : gInf B) (w : B.Hs), IsURep B.σs → ContDiff ℝ ∞ F → HasCompactSupport F → ∃ F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ, ContDiff ℝ ∞ F' ∧ HasCompactSupport F' ∧ HasDerivAt (orbit B E (∫ g, F (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I))) (∫ g, F' (fun v i j => uMat (g v) i j) • B.σs g w ∂(muInf B.I)) 0 := by
  intro B F E w hσ hF hFc

  have hμ : muInf B.I = Measure.pi (fun v => Formalism.REAL.muG (B.I.ε v)) := rfl
  haveI : (muInf B.I).IsMulLeftInvariant := by rw [hμ]; infer_instance
  haveI : IsFiniteMeasureOnCompacts (muInf B.I) := by rw [hμ]; infer_instance
  let c : B.I.Ginf → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
    fun g v i j => uMat (g v) i j
  have hc : Topology.IsClosedEmbedding c :=
    Topology.IsClosedEmbedding.piMap fun v => (Formalism.REAL.isClosedEmbeddingMatrix B.I.n (B.I.ε v)).1

  let Lm : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) →ₗ[ℝ]
      (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
    { toFun := fun M v i j => ∑ k, (-(E v).1) i k * M v k j
      map_add' := by
        intro M N
        funext v i j
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r M
        funext v i j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Complex.real_smul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => mul_left_comm _ _ _ }
  let L := LinearMap.toContinuousLinearMap Lm
  let F' : (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) → ℂ := fun M => fderiv ℝ F M (L M)
  have hF's : ContDiff ℝ ∞ F' := (contDiff_infty_iff_fderiv.1 hF).2.clm_apply L.contDiff
  have hF'c : HasCompactSupport F' := by
    refine (hFc.fderiv (𝕜 := ℝ)).mono' fun M hM => subset_tsupport _ ?_
    intro h0
    apply hM
    show fderiv ℝ F M (L M) = 0
    rw [h0]
    rfl
  refine ⟨F', hF's, hF'c, ?_⟩
  let a : ℝ → B.I.Ginf := fun t v => expU (t • E v)
  have ha : Continuous a := continuous_pi fun v => continuous_expU (E v)
  have ha0 : a 0 = 1 := by
    funext v
    show expU ((0 : ℝ) • E v) = 1
    rw [zero_smul, expU_zero]
  have hcc : Continuous c := hc.continuous
  have hd : ∀ g t, HasDerivAt (fun s => F (c ((a s)⁻¹ * g))) (F' (c ((a t)⁻¹ * g))) t := by
    intro g t
    let p : ℝ → (InfinitePlace B.I.F → Fin B.I.n → Fin B.I.n → ℂ) :=
      fun s v i j => (NormedSpace.exp (s • (-(E v).1)) * uMat (g v)) i j
    have hp : ∀ s, c ((a s)⁻¹ * g) = p s := by
      intro s
      funext v i j
      show uMat ((expU (s • E v))⁻¹ * g v) i j = _
      rw [uMat_inv_mul]
    have hp' : HasDerivAt p (L (p t)) t := by
      refine hasDerivAt_pi.2 fun v => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
      exact hasDerivAt_exp_mul_entry _ _ t i j
    have hFd : HasFDerivAt F (fderiv ℝ F (p t)) (p t) :=
      (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
    have h := hFd.comp_hasDerivAt t hp'
    simp only [hp]
    exact h
  have main := hasDerivAt_average (muInf B.I) hσ w (a := a) ha ha0 (f := fun g => F (c g))
    (f' := fun g => F' (c g)) (hF.continuous.comp hcc) (hFc.comp_isClosedEmbedding hc)
    (hF's.continuous.comp hcc) (hF'c.comp_isClosedEmbedding hc) hd
  exact main

end GlobalTheory.AverageDeriv
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.LocOver.WitChange

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

lemma img_mul (g k : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * k) Λ = img g (img k Λ) := by
  ext v
  simp only [img, Submodule.mem_map, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    LinearEquiv.mul_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨k u, ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, rfl⟩

lemma prF_e (Fr : FrameD H r) (a : Fin r) : Fr.prF (Fr.f a.castSucc) = 0 := by
  unfold FrameD.prF
  have h1 : ∑ c, H.h (Fr.f a.castSucc) (Fr.es c) • Fr.e c = Fr.f a.castSucc := by
    rw [Finset.sum_eq_single a]
    · rw [Fr.h_es, if_pos rfl, one_smul]; rfl
    · intro c _ hc; rw [Fr.h_es, if_neg (Ne.symm hc), zero_smul]
    · intro h; exact absurd (Finset.mem_univ a) h
  have h2 : ∑ c, H.h (Fr.f a.castSucc) (Fr.e c) • Fr.es c = 0 :=
    Finset.sum_eq_zero (fun c _ => by
      show H.h (Fr.f a.castSucc) (Fr.f c.castSucc) • Fr.es c = _
      rw [Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne), zero_smul])
  rw [h1, h2]; simp

lemma frame_projection_last_eq_self (Fr : FrameD H r) : Fr.prF (Fr.f (Fin.last r)) = Fr.f (Fin.last r) := by
  unfold FrameD.prF
  have h1 : ∑ c, H.h (Fr.f (Fin.last r)) (Fr.es c) • Fr.e c = 0 :=
    Finset.sum_eq_zero (fun c _ => by rw [H.h_herm (Fr.es c) _, Fr.h_sz, map_zero, zero_smul])
  have h2 : ∑ c, H.h (Fr.f (Fin.last r)) (Fr.e c) • Fr.es c = 0 :=
    Finset.sum_eq_zero (fun c _ => by
      show H.h (Fr.f (Fin.last r)) (Fr.f c.castSucc) • Fr.es c = _
      rw [Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last c).ne), zero_smul])
  rw [h1, h2]; simp

lemma frame_mem (Fr : FrameD H r) {L : Submodule M.L.O (H.Wb Fr.f)} (hL : Fr.IsInner L) (b : Fin (r + 1)) :
    Fr.f b ∈ Fr.LamStd L := by
  apply Formalism.MainNotions.BridgeLemma.f_mem_LamStd <;> assumption

end

theorem integral_change {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} (hOK : M.OK) {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
    (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L)
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (hA : Uni A) (hAO : ∀ a b, A a b ∈ M.L.O) :
    ∃ k ∈ Fr.N, (∀ b, k (Fr.f b) = ∑ a, A a b • Fr.f a) ∧ img k (Fr.LamStd L) = Fr.LamStd L := by
  obtain ⟨kl, hkl, hkle, hklz, hklL⟩ := GlobalTheory.T.unitriangular_change_frame_unipotent M hOK H r Fr L A hA hAO
  obtain ⟨y, hyL, hyz, hyes⟩ := GlobalTheory.T.exists_inner_lattice_vector_anisotropic M hOK H r Fr L hL
  have hx : ∑ a : Fin r, A a.castSucc (Fin.last r) • Fr.f a.castSucc ∈
      Submodule.span M.L.O (Set.range fun a : Fin r => Fr.f a.castSucc) :=
    Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ (⟨A a.castSucc (Fin.last r), hAO _ _⟩ : M.L.O) (Submodule.subset_span ⟨a, rfl⟩)
  obtain ⟨kz, hkz, hkzz, hkzX, hkzL⟩ := GlobalTheory.T.exists_unipotent_add_isotropic_to_anisotropic M hOK H r Fr L hL y hyL hyz hyes _ hx
  refine ⟨kz * kl, mul_mem hkz hkl, fun b => ?_, by rw [img_mul, hklL, hkzL]⟩
  induction b using Fin.lastCases with
  | last =>
    rw [LinearEquiv.mul_apply, hklz, hkzz, Fin.sum_univ_castSucc, hA.2, one_smul, add_comm]
  | cast c =>
    rw [LinearEquiv.mul_apply, hkle c]
    apply hkzX
    rw [Fin.sum_univ_castSucc, hA.1 _ _ (Fin.castSucc_lt_last c), zero_smul, add_zero]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem witness_change : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (k : ℕ) (P : FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (theta M) → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → ∀ (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (g g' : Fin (r + 1) → V), Uni A → Uni A' → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O ∧ A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (theta M)}) → Chg t.f A g → Chg t.f' A' g' → IsTermOver P d ⟨t.abelian₂, g, g', t.T, t.T'⟩ := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r k P hk hrel d t ht A A' g g' hA hA' hAA hg hg'
  obtain ⟨hT, hT', ⟨n, hn, hf, hLam⟩, ⟨n', hn', hf', hLam'⟩, hadm⟩ := ht
  obtain ⟨kA, hkA, hkAf, hkAL⟩ := integral_change hOK P.A d.L d.hL A hA (fun a b => (hAA a b).1)
  obtain ⟨kB, hkB, hkBf, hkBL⟩ := integral_change hOK P.B d.L' d.hL' A' hA' (fun a b => (hAA a b).2.1)
  have hfΛ : ∀ a, t.f a ∈ t.abelian₂ := by
    intro a; rw [hf, hLam]; exact ⟨P.A.f a, frame_mem P.A d.hL a, rfl⟩
  refine ⟨hT, hT', ⟨n * kA, mul_mem hn hkA, ?_, ?_⟩, ⟨n' * kB, mul_mem hn' hkB, ?_, ?_⟩, ?_⟩
  · funext b
    show g b = n (kA (P.A.f b))

    rw [hg b, hkAf b, map_sum, hf]
    simp only [map_smul]
  · show t.abelian₂ = _
    rw [img_mul, hkAL, hLam]
  · funext b
    show g' b = n' (kB (P.B.f b))

    rw [hg' b, hkBf b, map_sum, hf']
    simp only [map_smul]
  · show t.abelian₂ = _
    rw [img_mul, hkBL, hLam']
  · intro gg hgg
    obtain ⟨had, hio⟩ := hadm gg hgg
    refine ⟨fun b => ?_, hio⟩
    have hθ : theta M = (gg.q : F) := by simp [theta, hgg]
    show g' b - g b ∈ H.smulLat (algebraMap F E (gg.q : F)) t.abelian₂
    have e1 : g' b - g b = ∑ a, (A' a b • (t.f' a - t.f a) - (A a b - A' a b) • t.f a) := by
      rw [hg b, hg' b, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [smul_sub, sub_smul]; abel
    rw [e1]
    refine Submodule.sum_mem _ fun a _ => Submodule.sub_mem _ ?_ ?_
    · exact Submodule.smul_mem _ (⟨A' a b, (hAA a b).2.1⟩ : M.L.O) (had a)
    · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hAA a b).2.2
      rw [hθ] at hc
      rw [← hc]
      have h1 : algebraMap F E (gg.q : F) • t.f a ∈ H.smulLat (algebraMap F E (gg.q : F)) t.abelian₂ :=
        Submodule.subset_span ⟨t.f a, hfΛ a, rfl⟩
      rw [smul_assoc]
      exact Submodule.smul_mem _ c h1

end GlobalTheory.LocOver.WitChange
end
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.blockPerpEmbedding_of_diagonal_frame : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ) (j : Formalism.REAL.UJ ε' → Formalism.REAL.UJ ε), GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → (∀ g, Formalism.MainNotions.S.uMat (j g) *ᵥ x₀ = x₀ ∧ Formalism.MainNotions.S.uMat (j g) * B = B * Formalism.MainNotions.S.uMat g) → ∀ (P Q P' Q' : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin (n + 1)) (f' : Fin P' ⊕ Fin Q' ≃ Fin n) (hf : Sorts ε f) (hf' : Sorts ε' f'), IsPerpEmb (fun i => x₀ (f i)) (B.submatrix f f') (fun g => hf.equiv.symm (j (hf'.equiv g))) := by
  first | exact @GlobalTheory.PerpSort.isPerpEmb_of_sorts | exact GlobalTheory.PerpSort.isPerpEmb_of_sorts | (intros; apply GlobalTheory.PerpSort.isPerpEmb_of_sorts <;> assumption)
end

section

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical

theorem _root_.GlobalTheory.T.exists_continuousMulEquiv_congruenceTopology_adelicUnitary : ∀ (I : AutInst), ∃ e : I.Gf ≃ₜ* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA (Af I.F) I.cm.sig I.J, (∀ x, ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Af I.F) I.cm.sig I.J (e x) : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) = (I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) ∧ ∀ x, x ∈ I.Kset ↔ GlobalTheory.Mem.Vol.StabHat I.F (I.L : Set (Fin I.n → I.E)) ((I.fmat x).map (Algebra.TensorProduct.comm I.F I.E (Af I.F))) := by
  first | exact @GlobalTheory.CongTop.Swap.exists_continuousMulEquiv_adelic | exact GlobalTheory.CongTop.Swap.exists_continuousMulEquiv_adelic | (intros; apply GlobalTheory.CongTop.Swap.exists_continuousMulEquiv_adelic <;> assumption)
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocalDensityValue

def placeHom (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Fv F v →+ AF F :=
  (AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom

theorem continuous_placeHom (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (placeHom F v) :=
  Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v)

def localChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) : AddChar (Fv F v) ℂ :=
  ψ.compAddMonoidHom (placeHom F v)

theorem isLocalChar (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) (v : HeightOneSpectrum (𝓞 F)) (m : ℤ)
    (hm : ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp m) :
    GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.IsLocalChar F v (localChar F ψ v) := by
  refine ⟨hψ.1.comp (continuous_placeHom F v), fun t => hψ.2.1 _, ?_⟩
  by_contra h
  push Not at h
  obtain ⟨t, ht⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (m + 1))
  have := (hm t).1 fun s _ => h _
  rw [ht, WithZero.exp_le_exp] at this
  omega

end GlobalTheory.LocalDensityValue
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.KFinCoefSplit

variable {k r : ℕ}

theorem kfin_smul {R : Rep k r} (a : ℂ) {v : R.H} (hv : R.KFin v) : R.KFin (a • v) := by
  obtain ⟨S, hfd, hv, hst⟩ := hv
  exact ⟨S, hfd, S.smul_mem a hv, hst⟩

theorem kfin_sum {R : Rep k r} {ι : Type} [Fintype ι] (x : ι → R.H) (hx : ∀ c, R.KFin (x c)) :
    R.KFin (∑ c, x c) := by
  choose S hfd hS hst using hx
  refine ⟨⨆ c, S c, inferInstance, Submodule.sum_mem _ fun c _ => Submodule.mem_iSup_of_mem c (hS c),
    fun g hg y hy => ?_⟩
  have hle : (⨆ c, S c) ≤ (⨆ c, S c).comap (R.σ g : R.H →ₗ[ℂ] R.H) :=
    iSup_le fun c z hz => Submodule.mem_iSup_of_mem c (hst c g hg z hz)
  exact hle hy

theorem kfin_coef_mul_split : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (om om' : ι → ℂ) (v v' : R.H), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → R.KFin v → R.KFin v' → (∀ I, (RI I).KFin (∑ c, pr I c (tm R om v c)) ∧ (RI I).KFin (∑ c, pr I c (tm R om' v' c))) ∧ ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om * ⟪v, R.σ g v'⟫_ℂ = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (tm R om v c), (RI I).σ g (∑ c, pr I c (tm R om' v' c))⟫_ℂ := by
  intro hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI om om' v v' hR hRI hF hT hv hv'
  obtain ⟨-, -, -, -, hRT, -, hRK, -, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR
  have hadj := (GlobalTheory.TensAdj.tens_adj hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hF hT).2.2.2.2
  have hkf := (GlobalTheory.tensor_decomposition_kfinite hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT.raw).2.1
  have hp : ∀ I (a : ι → ℂ) (w : R.H), R.KFin w → (RI I).KFin (∑ c, pr I c (tm R a w c)) := fun I a w hw =>
    kfin_sum _ fun c => hkf I c _ (kfin_smul (a c) hw)
  exact ⟨fun I => ⟨hp I om v hv, hp I om' v' hv'⟩,
    fun g hg => hadj om om' v (hRT v (hRK v hv)) v' (hRT v' (hRK v' hv')) g hg⟩

end GlobalTheory.KFinCoefSplit
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.framePairCoordinates_localHeight_eq_residueCard : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), P.Hp = S.Hp ∧ LocNG.qF F = S.q ∧ (P.PrimeTo → S.gg = false ∧ vE M.L S.ϖ S.G = 0 ∧ ∀ l, S.D l ≠ 0 → vE M.L S.ϖ (S.D l * M.L.cj (S.D l)) = 0) := by
  first | exact @GlobalTheory.HL.CoordHeight.height_eq | exact GlobalTheory.HL.CoordHeight.height_eq | (intros; apply GlobalTheory.HL.CoordHeight.height_eq <;> assumption)
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

theorem _root_.GlobalTheory.T.highest_weight_eventually_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V), IsURepOn (UJset ε) σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E (LamOf ε lam) u, ∀ y : H, ∀ᶠ g : UJ ε in nhds 1, ∑ a, ∑ b, Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) * (⟪y, σ (toMK k) (u : H)⟫_ℂ * ⟪σ (toMK k) (u : H), (at1 G a b : V)⟫_ℂ) ∂(muK ε)) (umat g) = 0 := by
  first | exact @GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero | exact GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero | (intros; apply GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePairNormalForm_invVol_skew_layer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) (N.Gam Λ ⊓ N.ZI) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  first | exact @GlobalTheory.DegCnt.WtSkew.invVol_skew_le | exact GlobalTheory.DegCnt.WtSkew.invVol_skew_le | (intros; apply GlobalTheory.DegCnt.WtSkew.invVol_skew_le <;> assumption)
end
