module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle293
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAndMass
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle336
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.ContinuousOfMemCcSmooth
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.FrameIsoReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {w : InfinitePlace F}

theorem cT_star (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j; rfl

theorem signFrame_map (h : IsCMExt F E σ) (τ : EmbOver E w) {ε : Fin n → Bool}
    {b : GL (Fin n) (w.Completion ⊗[F] E)} (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) :
    (b.1.map (infEmb τ))ᴴ * J.map τ.1 * b.1.map (infEmb τ) = Formalism.REAL.Jm ε := by
  have h1 : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1 * JR w.Completion J * b.1).map (infEmb τ) =
      (Matrix.diagonal fun i => if ε i then (1 : w.Completion ⊗[F] E) else -1).map (infEmb τ) :=
    congrArg (fun M => M.map (infEmb τ)) hb
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero _)] at h1
  have h2 : (JR w.Completion J).map (infEmb τ) = J.map τ.1 := by ext r s; simp [JR, inclR]
  have h3 : (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1).map (infEmb τ) =
      (b.1.map (infEmb τ))ᴴ := by
    ext i j; exact (infEmb_sigR h τ _).symm
  rw [h2, h3] at h1
  rw [h1, Formalism.REAL.Jm]
  congr 1; funext i; split_ifs <;> simp

section Frame

variable (σ J) (h : IsCMExt F E σ) (τ : EmbOver E w) (ε : Fin n → Bool) (b : GL (Fin n) (w.Completion ⊗[F] E))

abbrev fB : Matrix (Fin n) (Fin n) ℂ := b.1.map (infEmb τ)

abbrev fBi : Matrix (Fin n) (Fin n) ℂ := (b⁻¹).1.map (infEmb τ)

theorem fBi_mul : fBi τ b * fB τ b = 1 := by
  rw [fBi, fB, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem fB_mul : fB τ b * fBi τ b = 1 := by
  rw [fBi, fB, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem inFrame_eq (g : GArch σ J w) :
    GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g = fBi τ b * (archEquiv J h τ g).1.1 * fB τ b := by
  rw [archEquiv_val]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame, Units.val_mul, Matrix.map_mul]

include h in
theorem isEmbedding_inFrame : Topology.IsEmbedding (GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b) := by
  have e : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b =
      (fun x : Matrix (Fin n) (Fin n) ℂ => fBi τ b * x * fB τ b) ∘ GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ) := by
    funext g
    exact (inFrame_eq σ J h τ b g).trans rfl
  have hc : Topology.IsEmbedding fun x : Matrix (Fin n) (Fin n) ℂ => fBi τ b * x * fB τ b :=
    Function.LeftInverse.isEmbedding (f := fun x => fB τ b * x * fBi τ b) (fun x => by
      simp only [← mul_assoc, fB_mul, one_mul]; rw [mul_assoc, fB_mul, mul_one])
      ((continuous_const.mul continuous_id).mul continuous_const)
      ((continuous_const.mul continuous_id).mul continuous_const)
  rw [e]
  exact hc.comp (GlobalTheory.Orb.isEmbedding_archMat J h τ)

variable {ε}

include h in
theorem inFrame_mem (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) (g : GArch σ J w) :
    Formalism.REAL.inUJ ε (GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g) := by
  have hS : (fB τ b)ᴴ * J.map τ.1 * fB τ b = Formalism.REAL.Jm ε := signFrame_map h τ hb
  have hA : ((archEquiv J h τ g).1.1)ᴴ * J.map τ.1 * (archEquiv J h τ g).1.1 = J.map τ.1 := by
    rw [← cT_star]; exact (archEquiv J h τ g).2
  rw [Formalism.REAL.inUJ, inFrame_eq σ J h]
  set A := (archEquiv J h τ g).1.1
  set T := J.map τ.1
  set B := fB τ b
  set Bi := fBi τ b
  have hT : Biᴴ * (Bᴴ * T * B) * Bi = T := by
    have : Biᴴ * (Bᴴ * T * B) * Bi = (B * Bi)ᴴ * T * (B * Bi) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, fB_mul, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  calc (Bi * A * B)ᴴ * Formalism.REAL.Jm ε * (Bi * A * B)
      = Bᴴ * Aᴴ * (Biᴴ * (Bᴴ * T * B) * Bi) * A * B := by
        rw [← hS]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Bᴴ * (Aᴴ * T * A) * B := by rw [hT]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hA, hS]

def hom0 : GArch σ J w →* (Matrix (Fin n) (Fin n) ℂ)ˣ :=
  (Units.map (infEmb τ).mapMatrix.toMonoidHom).comp ((MulAut.conj b⁻¹).toMonoidHom.comp (matHom _ σ J))

theorem coe_archimedeanFrameConjMatrixHom (g : GArch σ J w) : ((hom0 σ J τ b g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
    GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g := by
  simp [hom0, GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame, MulAut.conj_apply]

include h in
theorem exists_inFrame_eq (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) (a : Formalism.REAL.UJ ε) :
    ∃ g : GArch σ J w, GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g = ((a : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
  have hS : (fB τ b)ᴴ * J.map τ.1 * fB τ b = Formalism.REAL.Jm ε := signFrame_map h τ hb
  let bU : (Matrix (Fin n) (Fin n) ℂ)ˣ := Units.map (infEmb τ).mapMatrix.toMonoidHom b
  have hbU : (bU : Matrix (Fin n) (Fin n) ℂ) = fB τ b := rfl
  have hbUi : ((bU⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = fBi τ b := by
    rw [← map_inv]; rfl
  let yU : (Matrix (Fin n) (Fin n) ℂ)ˣ := bU * (a : (Matrix (Fin n) (Fin n) ℂ)ˣ) * bU⁻¹
  set x := ((a : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
  have hx : xᴴ * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε := a.2
  have hy : (yU : Matrix (Fin n) (Fin n) ℂ) = fB τ b * x * fBi τ b := by
    simp only [yU, Units.val_mul, hbU, hbUi, x]
  set T := J.map τ.1
  set B := fB τ b
  set Bi := fBi τ b
  have hT : Biᴴ * (Bᴴ * T * B) * Bi = T := by
    have : Biᴴ * (Bᴴ * T * B) * Bi = (B * Bi)ᴴ * T * (B * Bi) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, fB_mul, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hmem : yU ∈ Formalism.UG.UJ (starRingEnd ℂ) T := by
    change Formalism.UG.cT (starRingEnd ℂ) (yU : Matrix (Fin n) (Fin n) ℂ) * T * (yU : Matrix (Fin n) (Fin n) ℂ) = T
    rw [cT_star, hy]
    calc (B * x * Bi)ᴴ * T * (B * x * Bi) = Biᴴ * (xᴴ * (Bᴴ * T * B) * x) * Bi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = T := by rw [hS, hx, ← hS, hT]
  refine ⟨(archEquiv J h τ).symm ⟨yU, hmem⟩, ?_⟩
  rw [inFrame_eq σ J h, MulEquiv.apply_symm_apply]
  change Bi * (yU : Matrix (Fin n) (Fin n) ℂ) * B = x
  rw [hy]
  simp only [← Matrix.mul_assoc, fBi_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, fBi_mul, Matrix.mul_one, Matrix.one_mul]

def frameHom (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) : GArch σ J w →* Formalism.REAL.UJ ε :=
  (hom0 σ J τ b).codRestrict _ fun g => by
    change Formalism.REAL.inUJ ε _
    rw [coe_archimedeanFrameConjMatrixHom]; exact inFrame_mem σ J h τ b hb g

theorem frameHom_val (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) (g : GArch σ J w) :
    Formalism.REAL.coeMatrixAlt ε (frameHom σ J h τ b hb g) = GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.inFrame σ J τ b g := coe_archimedeanFrameConjMatrixHom σ J τ b g

theorem frameHom_bijective (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) : Function.Bijective (frameHom σ J h τ b hb) := by
  refine ⟨fun g g' e => (isEmbedding_inFrame σ J h τ b).injective ?_, fun a => ?_⟩
  · rw [← frameHom_val σ J h τ b hb, ← frameHom_val σ J h τ b hb, e]
  · obtain ⟨g, hg⟩ := exists_inFrame_eq σ J h τ b hb a
    exact ⟨g, Formalism.REAL.injective_coeMatrix ε ((frameHom_val σ J h τ b hb g).trans hg)⟩

def frameEquiv (hb : GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsSignFrame σ J ε b) : GArch σ J w ≃ₜ* Formalism.REAL.UJ ε :=
  { MulEquiv.ofBijective _ (frameHom_bijective σ J h τ b hb) with
    continuous_toFun := ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding).continuous_iff.2
      ((isEmbedding_inFrame σ J h τ b).continuous.congr fun g => (frameHom_val σ J h τ b hb g).symm)
    continuous_invFun := (isEmbedding_inFrame σ J h τ b).continuous_iff.2 ((Formalism.REAL.continuous_coeMatrix ε).congr fun x => by
      have := frameHom_val σ J h τ b hb ((MulEquiv.ofBijective _ (frameHom_bijective σ J h τ b hb)).symm x)
      exact (congrArg (Formalism.REAL.coeMatrixAlt ε)
        ((MulEquiv.ofBijective _ (frameHom_bijective σ J h τ b hb)).apply_symm_apply x).symm).trans this) }

end Frame

end GlobalTheory.FrameIsoReal
end
end

section

open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.SplitWeil NumberField IsDedekindDomain
open GlobalTheory.AutomorphicL2Unitary (conv)

noncomputable section

namespace GlobalTheory.Orb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  [Submodule.IsFullLattice E L] {μa : ∀ w, Measure (GArch σ J w)} {μf : ∀ v, Measure (GLoc σ J v)}
  {μ : Measure (GAd σ J)} {fa fa' : ∀ w, GArch σ J w → ℂ} {ff ff' : ∀ v, GLoc σ J v → ℂ}


omit [NumberField E] [Submodule.IsFullLattice E L] in
theorem unitLoc_mul_translate {v : HeightOneSpectrum (𝓞 F)} {y : GLoc σ J v} (hy : y ∈ stabLoc σ J L v) :
    (fun x => unitLoc σ J L v x * unitLoc σ J L v (x⁻¹ * y)) = unitLoc σ J L v := by
  funext x
  by_cases hx : x ∈ stabLoc σ J L v
  · simp [unitLoc, hx, mul_mem (inv_mem hx) hy]
  · simp [unitLoc, hx]

theorem conv_unitLoc {v : HeightOneSpectrum (𝓞 F)} (ν : Measure (GLoc σ J v)) :
    conv ν (unitLoc σ J L v) (unitLoc σ J L v) = (ν.real (stabLoc σ J L v) : ℂ) • unitLoc σ J L v := by
  funext y
  by_cases hy : y ∈ stabLoc σ J L v
  · rw [conv, unitLoc_mul_translate hy, unitLoc]
    refine (integral_indicator_const _ (isOpen_stabLoc σ J L v).measurableSet).trans ?_
    rw [Pi.smul_apply, indicator_of_mem hy, Complex.real_smul]
    rfl
  · have : ∀ x, unitLoc σ J L v x * unitLoc σ J L v (x⁻¹ * y) = 0 := fun x => by
      by_cases hx : x ∈ stabLoc σ J L v
      · simp [unitLoc, hy, Subgroup.mul_mem_cancel_left _ (inv_mem hx)]
      · simp [unitLoc, hx]
    rw [conv]
    simp only [this, integral_zero]
    simp [unitLoc, hy]

theorem IsFinFamily.conv (hf : IsFinFamily σ J L ff) (hf' : IsFinFamily σ J L ff')
    (h1 : ∀ᶠ v in cofinite, μf v (stabLoc σ J L v) = 1) : IsFinFamily σ J L fun v => conv (μf v) (ff v) (ff' v) := by
  refine ⟨fun v => conv_mem_SB (hf.1 v) (hf'.1 v), ?_⟩
  filter_upwards [hf.2, hf'.2, h1] with v e e' e1
  rw [e, e', conv_unitLoc, Measure.real, e1]
  simp

theorem IsFinFamily.mul_translate (hf : IsFinFamily σ J L ff) (hf' : IsFinFamily σ J L ff') (y : GAd σ J) :
    IsFinFamily σ J L fun v x => ff v x * ff' v (x⁻¹ * proj σ J v y) := by
  refine ⟨fun v => ⟨(hf.1 v).1.mul ((hf'.1 v).1.comp_continuous (by fun_prop)), (hf.1 v).2.mul_right⟩, ?_⟩
  filter_upwards [hf.2, hf'.2, eventually_proj_mem_stabLoc σ J L y] with v e e' hy
  rw [e, e', unitLoc_mul_translate hy]

end GlobalTheory.Orb
end
end

section

open Set Filter GlobalTheory.AdelicU NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology ComplexConjugate ContDiff Matrix

noncomputable section

namespace GlobalTheory.Orb

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def IsSmoothRealFam (u : P → GAd σ J) : Prop :=
  (∀ t, projFin σ J (u t) = 1) ∧
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) i j, ContDiff ℝ ∞ fun t => archMat σ J τ (projArch σ J w (u t)) i j


omit [NumberField E] in
theorem isSmoothRealFam_one : IsSmoothRealFam fun _ : P => (1 : GAd σ J) :=
  ⟨fun _ => map_one _, fun _ _ _ _ => contDiff_const⟩


omit [NumberField E] in
theorem IsSmoothRealFam.mul {u v : P → GAd σ J} (hu : IsSmoothRealFam u) (hv : IsSmoothRealFam v) :
    IsSmoothRealFam fun t => u t * v t := by
  refine ⟨fun t => by rw [map_mul, hu.1, hv.1, one_mul], fun w τ i j => ?_⟩
  simp only [map_mul, Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (hu.2 w τ i k).mul (hv.2 w τ k j)


omit [NumberField E] in
theorem IsSmoothRealFam.comp {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] {u : P → GAd σ J}
    (hu : IsSmoothRealFam u) {p : Q → P} (hp : ContDiff ℝ ∞ p) : IsSmoothRealFam fun t => u (p t) :=
  ⟨fun _ => hu.1 _, fun w τ i j => (hu.2 w τ i j).comp hp⟩


omit [NumberField E] in
theorem isSmoothRealFam_prod {k : ℕ} {u : Fin k → P → GAd σ J} (hu : ∀ i, IsSmoothRealFam (u i)) :
    IsSmoothRealFam fun t => (List.ofFn fun i => u i t).prod := by
  induction k with
  | zero => simpa using isSmoothRealFam_one
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (hu 0).mul (ih fun i => hu i.succ)


omit [NumberField E] in
theorem infCoord_mul (x : GInf σ J) (y : GAd σ J) : infCoord σ J (x * projInf σ J y) =
    fun w τ i j => ∑ k, infCoord σ J x w τ i k * archMat σ J τ (projArch σ J w y) k j := by
  funext w τ i j
  simp only [infCoord, archCoord, matCoord, map_mul, Matrix.mul_apply, projInfArch_projInf]

theorem IsSmoothRealFam.contDiff {u : P → GAd σ J} (hu : IsSmoothRealFam u) {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J)
    (g : GAd σ J) : ContDiff ℝ ∞ fun t => f (g * u t) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ⟨-, Φ, hΦ, e⟩, b, -, rfl⟩ := hf
    simp only [infFin, map_mul, hu.1, mul_one, e, infCoord_mul]
    refine (hΦ.comp (contDiff_pi.2 fun w => contDiff_pi.2 fun τ => contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
      ContDiff.sum fun k _ => contDiff_const.mul (hu.2 w τ k j))).mul contDiff_const
  | zero => exact contDiff_const
  | add f f' _ _ h h' => exact h.add h'
  | smul a f _ h => exact h.const_smul a

theorem IsSmoothRealFam.deriv_mem_ccInf {u : ℝ → GAd σ J} (hu : IsSmoothRealFam u) (hc : Continuous u)
    (h0 : u 0 = 1) {a : GInf σ J → ℂ} (ha : a ∈ CcInf σ J) :
    (fun x => deriv (fun t => a (x * projInf σ J (u t))) 0) ∈ CcInf σ J := by
  obtain ⟨hs, Φ, hΦ, e⟩ := ha
  refine ⟨.intro hs fun x hx => ?_, fun y => fderiv ℝ Φ y fun w τ i j =>
    ∑ k, y w τ i k * deriv (fun t => archMat σ J τ (projArch σ J w (u t)) k j) 0, ?_, fun x => ?_⟩
  · have h1 : Tendsto (fun t => x * projInf σ J (u t)) (𝓝 0) (𝓝 x) := by
      simpa [h0] using (continuous_const.mul ((continuous_projInf σ J).comp hc)).tendsto (f := fun t => x * projInf σ J (u t)) 0
    rw [EventuallyEq.deriv_eq (f := fun _ => (0 : ℂ)) (h1.eventually (notMem_tsupport_iff_eventuallyEq.1 hx)),
      deriv_const]
  · refine (hΦ.fderiv_right (m := ∞) le_rfl).clm_apply ?_
    exact contDiff_pi.2 fun w => contDiff_pi.2 fun τ => contDiff_pi.2 fun i => contDiff_pi.2 fun j =>
      ContDiff.sum fun k _ => (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 (contDiff_pi.1 contDiff_id w) τ) i) k).mul
        contDiff_const
  · have h1 : HasDerivAt (fun t => infCoord σ J (x * projInf σ J (u t))) (fun w τ i j =>
        ∑ k, infCoord σ J x w τ i k * deriv (fun t => archMat σ J τ (projArch σ J w (u t)) k j) 0) 0 := by
      simp only [infCoord_mul]
      exact hasDerivAt_pi.2 fun w => hasDerivAt_pi.2 fun τ => hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j =>
        HasDerivAt.fun_sum fun k _ => ((hu.2 w τ k j).differentiable (by simp) 0).hasDerivAt.const_mul _
    have h2 := (hΦ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt 0 h1
    simp only [h0, map_one, mul_one] at h2
    simp only [e]
    exact h2.deriv

theorem IsSmoothRealFam.deriv_mem_ccAd {u : ℝ → GAd σ J} (hu : IsSmoothRealFam u) (hc : Continuous u)
    (h0 : u 0 = 1) {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    (fun g => deriv (fun t => f (g * u t)) 0) ∈ CcAd σ J := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hf
    convert infFin_mem_ccAd (hu.deriv_mem_ccInf hc h0 ha) hb using 1
    funext g
    simp only [infFin, map_mul, hu.1, mul_one, deriv_mul_const_field]
  | zero =>
    simp only [Pi.zero_apply, deriv_const]
    exact (CcAd σ J).zero_mem
  | add f f' hf hf' h h' =>
    convert (CcAd σ J).add_mem h h' using 1
    funext g
    exact deriv_fun_add ((hu.contDiff hf g).differentiable (by simp) 0) ((hu.contDiff hf' g).differentiable (by simp) 0)
  | smul c f _ h =>
    convert (CcAd σ J).smul_mem c h using 1
    funext g
    exact deriv_fun_const_smul_field c _

theorem isSmoothRealFam_embArch (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {x : P → GArch σ J w}
    (hx : ∀ i j, ContDiff ℝ ∞ fun t => archMat σ J τ (x t) i j) :
    IsSmoothRealFam (fun t => embArch σ J w (x t)) ∧ Continuous fun t => embArch σ J w (x t) := by
  refine ⟨⟨fun t => projFin_embArch σ J w _, fun w' τ' i j => ?_⟩, (continuous_embArch σ J w).comp
    ((isEmbedding_archMat J h τ).continuous_iff.2 (continuous_pi fun i => continuous_pi fun j => (hx i j).continuous))⟩
  by_cases e : w' = w
  · subst e
    simp only [projArch_embArch_self]
    rcases infEmb_eq_or_conj h τ τ' with e | e
    · simpa only [archMat_apply, e] using hx i j
    · simp only [archMat_apply, e]
      exact Complex.conjCLE.contDiff.comp (hx i j)
  · simp only [projArch_embArch_ne σ J e]
    exact contDiff_const

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_exp_smul_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • X) : Matrix (Fin n) (Fin n) ℂ) i j := by
  have : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
    contDiff_iff_contDiffAt.2 fun A => (NormedSpace.exp_analytic (𝕂 := ℝ) A).contDiffAt
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).contDiff.comp
    (h.comp (contDiff_id.smul contDiff_const))

end

end General

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem isSmoothRealFam_oneP (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) :
    IsSmoothRealFam (oneP θ V τ X) ∧ Continuous (oneP θ V τ X) ∧ oneP θ V τ X 0 = 1 := by
  choose x hx using fun t : ℝ => exists_archEquiv_eq V (embOverOf D τ) rfl
    (GlobalTheory.SmoothAutCheck.exp_mem_UH (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) hX t)
  have e : oneP θ V τ X = fun t => embArch _ _ _ (x t) := funext fun t => by
    rw [oneP, ← hx, atTau_archEquiv hθ V _ rfl]
  have h := isSmoothRealFam_embArch (isCMExt_host D) (embOverOf D τ) (x := x) fun i j => by
    simp only [archMat_eq_archEquiv _ (isCMExt_host D), hx]
    exact contDiff_exp_smul_entry X i j
  refine ⟨e ▸ h.1, e ▸ h.2, ?_⟩
  have h1 := atTau_archEquiv hθ V (embOverOf D τ) rfl 1
  rw [map_one, map_one] at h1
  rw [oneP, zero_smul, NormedSpace.exp_zero]
  exact h1

theorem ccGA_smooth_and_Rder_mem (D : D7) (V : HSp D)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (f : GA D V → ℂ)
    (hf : f ∈ CcGA V) :
    (∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)) ∧
    ∀ τ, ∀ X ∈ lieAt V τ, Rder θ V τ X f ∈ CcGA V :=
  ⟨fun _ _ _ hX g => (isSmoothRealFam_prod fun i => (isSmoothRealFam_oneP hθ (hX i)).1.comp
      (contDiff_apply ℝ (fun _ => ℝ) i)).contDiff hf g,
    fun _ _ hX => have h := isSmoothRealFam_oneP hθ hX; h.1.deriv_mem_ccAd h.2.1 h.2.2 hf⟩

end Record

end GlobalTheory.Orb
end
end

section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

theorem _root_.GlobalTheory.T.isLogDerivQExpansion_upperTriangular_action : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n : ℕ) (g : GQ), ent g 1 0 = 0 → 0 < ent g 0 0 → 0 < ent g 1 1 → algebraMap ℚ Ω (ent g 0 0 / ent g 1 1) ∈ A →
  ∀ (f : X.K) (φ : HahnSeries ℚ Ω), IsDl X A l n 1 f φ →
    IsDl X A l n 1 (X.sl g f) (HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) φ) := by
  first | exact @GlobalTheory.DlUp.isDl_sl_upper | exact GlobalTheory.DlUp.isDl_sl_upper | (intros; apply GlobalTheory.DlUp.isDl_sl_upper <;> assumption)
end

section

namespace GlobalTheory.DefiniteDecompObj

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

theorem doubleCosets_mass : ∀ D : D7, DefClassDecomp D :=
  GlobalTheory.DefiniteDecomp.defClassDecomp

end GlobalTheory.DefiniteDecompObj
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.cm_theta_torsion_translate_integral_series : ∀ D : D7, GL3Theta.transl D := by
  first | exact @GlobalTheory.ThetaTransl.transl_holds | exact GlobalTheory.ThetaTransl.transl_holds | (intros; apply GlobalTheory.ThetaTransl.transl_holds <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.theta_cube_relation_integral_formalGroup_biadditive : ∀ D : D7, GL3Theta.cube D ∧ GL3Theta.addInt D ∧ GL3Theta.beBiadd D := by
  first | exact @GlobalTheory.ThetaCube.cube_addInt_beBiadd | exact GlobalTheory.ThetaCube.cube_addInt_beBiadd | (intros; apply GlobalTheory.ThetaCube.cube_addInt_beBiadd <;> assumption)
end
