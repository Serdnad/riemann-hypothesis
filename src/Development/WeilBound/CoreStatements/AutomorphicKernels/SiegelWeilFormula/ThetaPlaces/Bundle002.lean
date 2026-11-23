module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.RelReal
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit

set_option linter.unusedSectionVars false

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def archimedeanEmbeddingTensor (B : Base F E) (w : InfinitePlace F) : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ :=
  (infEmb (B.emb w)).comp (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)).toRingHom

theorem thW_eq (B : Base F E) (w : InfinitePlace F) (z : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E) :
    thW B w z = starRingEnd ℂ (archimedeanEmbeddingTensor B w z) := rfl

theorem archimedean_embedding_tmul (B : Base F E) (w : InfinitePlace F) (a : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (x : E) :
    archimedeanEmbeddingTensor B w (a ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding w (a w) * (B.emb w).1 x := rfl

theorem thW_th' (B : Base F E) (w : InfinitePlace F) (y : AE F E) :
    thW B w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (B.emb w) y) := by
  have h : Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = compInf F E w y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  show starRingEnd ℂ (infEmb (B.emb w) (Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y))) = _
  rw [h]
  rfl

theorem archimedean_embedding_family (B : Base F E) :
    Formalism.IndefR.DatumF.IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) (archimedeanEmbeddingTensor B) := by
  intro w
  refine ⟨fun x => ?_, ?_⟩
  · rw [archimedean_embedding_tmul]
    show InfinitePlace.Completion.extensionEmbedding w 1 * (B.emb w).1 x = (B.emb w).1 x
    rw [map_one, one_mul]
  · have : (fun a : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F => archimedeanEmbeddingTensor B w (a ⊗ₜ[F] (1 : E))) =
        fun a => InfinitePlace.Completion.extensionEmbedding w (a w) := by
      funext a; rw [archimedean_embedding_tmul, map_one, mul_one]
    rw [this]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w)

theorem thW_infEmb (B : Base F E) (w : InfinitePlace F) :
    Formalism.MainNotions.StandardLattice.IsInfEmb (ComplexEmbedding.conjugate (B.emb w).1) (thW B w) := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [thW_eq, (archimedean_embedding_family B w).1 x]
    rfl
  · exact Complex.continuous_conj.comp (archimedean_embedding_family B w).2

theorem isCMFam_conj (B : Base F E) (h : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ) :
    GlobalTheory.Mem.Vol.IsCMFam (fun w : InfinitePlace F => ComplexEmbedding.conjugate (B.emb w).1) := by
  have hT := GlobalTheory.BotLValue.isCMType_embOver h B.emb
  have cc : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := fun φ => star_star φ
  beta_reduce at hT
  constructor
  · intro i j e
    simp only [InfinitePlace.mk_conjugate_eq] at e
    obtain ⟨k, -, hk⟩ := hT (B.emb i).1
    have hi := hk i (Or.inl rfl)
    have hj : j = k := by
      refine hk j ?_
      rcases InfinitePlace.mk_eq_iff.1 e with e' | e'
      · exact Or.inl e'
      · right
        show (B.emb i).1 = ComplexEmbedding.conjugate (B.emb j).1
        rw [← e', cc]
    rw [hi, hj]
  · intro φ
    obtain ⟨k, hk, -⟩ := hT φ.embedding
    beta_reduce at hk
    refine ⟨k, ?_⟩
    simp only [InfinitePlace.mk_conjugate_eq]
    rcases hk with e | e
    · rw [← e, InfinitePlace.mk_embedding]
    · rw [show (B.emb k).1 = ComplexEmbedding.conjugate φ.embedding by
          rw [e, cc],
        InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

theorem isPlaces_thW' (B : Base F E) (hB : B.IsGood σ) : Gen.IsPlaces σ B.ψ (thW B) (fun _ => -1) := by
  have : IsTotallyReal F := hB.cm.1
  refine ⟨fun w => GlobalTheory.Mem.VolExists.infEmb_continuous (thW_infEmb B w),
    GlobalTheory.Mem.VolExists.infEmb_bijective hB.cm (isCMFam_conj B hB.cm) (fun w => thW_infEmb B w),
    fun w z => GlobalTheory.Mem.VolExists.infEmb_sigR hB.cm (thW_infEmb B w) z, fun _ => by norm_num, fun x => ?_⟩
  have hs := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).2.2 (archimedeanEmbeddingTensor B) (archimedean_embedding_family B) x
  have hs' : B.ψ ((x, 0) : AF F) = _ := hs
  change B.ψ ((x, 0) : AF F) = _
  rw [hs']
  congr 1
  have hr : ∀ w, starRingEnd ℂ (archimedeanEmbeddingTensor B w (x ⊗ₜ[F] (1 : E))) = archimedeanEmbeddingTensor B w (x ⊗ₜ[F] (1 : E)) := fun w => by
    rw [archimedean_embedding_tmul, map_one, mul_one, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w),
      Complex.conj_ofReal]
  simp only [thW_eq, hr]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

end PositivityTheory.SiegelWeilFormula.ThetaDictR

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.ThetaDictR

open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_one {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ ((1 : AF F) ⊗ₜ[F] x) = τ.1 x := by
  simp [piInf, compInf, infEmb_tmul]

theorem norm_inv_mul_self {z : ℂ} (hz : z ≠ 0) (him : z.im = 0) :
    ((‖z‖⁻¹ : ℝ) : ℂ) * z = if 0 < z.re then 1 else -1 := by
  have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
  have hn : ‖z‖ = |z.re| := by rw [hz', Complex.norm_real, Real.norm_eq_abs]; simp
  have hre : z.re ≠ 0 := fun h => hz (by rw [hz', h]; simp)
  rw [hn]
  split_ifs with hpos
  · rw [abs_of_pos hpos, hz']
    push_cast
    rw [Complex.ofReal_re]
    exact inv_mul_cancel₀ (by exact_mod_cast hre)
  · have hneg : z.re < 0 := lt_of_le_of_ne (not_lt.1 hpos) hre
    rw [abs_of_neg hneg, hz']
    push_cast
    rw [Complex.ofReal_re, inv_neg, neg_mul, inv_mul_cancel₀ (by exact_mod_cast hre)]

theorem isFrames_of' {d : SD σ} (R : RD d) (η : E) (hη : η ≠ 0) (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ)
    (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) (hηζ : (σ η = η ∧ R.ζ = 1) ∨ (σ η = -η ∧ R.ζ = Complex.I))
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ))
    (th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y))
    (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star) :
    Gen.IsFrames (Jd d η) θ (εsW R η) fr := by
  intro w
  set τ := (d.B.emb w).1 with hτ
  set a := τ η with ha
  set c := cW d.B η w with hc
  have hθ1 : ∀ x : E, θ w ((1 : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) ⊗ₜ[F] x) = star (τ x) := fun x => by
    have := th w ((1 : AF F) ⊗ₜ[F] x)
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, piInf_one] at this
    exact this
  have hmat : (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (Jd d η)).map (θ w) = a • d.A.J.map τ := by
    ext i j
    simp only [Matrix.map_apply, HeckeCharacterZeroLocus.SiegelWeilU.JR, Jd, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
      HeckeCharacterZeroLocus.SiegelWeilU.inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, hθ1]
    rw [← hcm.2.2.2, herm, map_mul]
  have hcs : star c = c := Complex.conj_ofReal _
  have hfrH : ((fr w).1)ᴴ = c • ((R.fr w).1)ᵀ := by
    rw [frc w, Matrix.conjTranspose_smul]
    change star c • _ = _
    rw [hcs]
    congr 1
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hζ : R.ζ ≠ 0 := by
    rcases hηζ with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> simp
  have hfr' : (R.fr w).1ᵀ * d.A.J.map τ * (R.fr w).1.map star = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by
    have := congrArg (fun M => R.ζ⁻¹ • M) (R.hfr w)
    simp only [smul_smul, inv_mul_cancel₀ hζ, one_smul] at this
    rw [this]
  have ha0 : a ≠ 0 := (map_ne_zero τ).2 hη
  have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hcc : c * c = ((‖a‖⁻¹ : ℝ) : ℂ) := by
    rw [hc, cW, ← Complex.ofReal_mul, ← Real.rpow_add hapos]
    norm_num [Real.rpow_neg_one]
  set z := a / R.ζ * ((R.sg w : ℤ) : ℂ) with hz
  have hsg : ‖((R.sg w : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or (R.sg w) with h | h <;> rw [h] <;> simp
  have hsg0 : ((R.sg w : ℤ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hsg; simp at hsg
  have hsgim : (((R.sg w : ℤ) : ℂ)).im = 0 := by simp
  have hz0 : z ≠ 0 := mul_ne_zero (div_ne_zero ha0 hζ) hsg0
  have hzn : ‖z‖ = ‖a‖ := by
    rw [hz, norm_mul, norm_div, hsg]
    rcases hηζ with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> simp
  have hzim : z.im = 0 := by
    have hconj := hcm.2.2.2 τ η
    rcases hηζ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hconj
      have him : a.im = 0 := by
        have := congrArg Complex.im hconj
        change a.im = (star a).im at this
        simp at this; linarith
      rw [hz, h2, div_one, Complex.mul_im, him, hsgim]; ring
    · rw [h1, map_neg] at hconj
      have hre : a.re = 0 := by
        have := congrArg Complex.re hconj
        change (-a).re = (star a).re at this
        simp at this; linarith
      rw [hz, h2, Complex.div_I, Complex.mul_im, hsgim]
      simp [Complex.mul_im, hre]
  have key : (fr w).1ᴴ * (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (Jd d η)).map (θ w) * (fr w).1 =
      (((‖z‖⁻¹ : ℝ) : ℂ) * z) • (1 : Matrix (Fin d.m) (Fin d.m) ℂ) := by
    rw [hfrH, hmat, frc w, show ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = c from rfl]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hfr', smul_smul, hzn, ← hcc, hz]
    congr 1
    field_simp
  change (fr w).1ᴴ * (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (Jd d η)).map (θ w) * (fr w).1 = _
  rw [key, norm_inv_mul_self hz0 hzim]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [εsW, sgn, hz, ha, hτ]
  · simp [hij]

end PositivityTheory.SiegelWeilFormula.ThetaDictR

end
end
