module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle027
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Bundle002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ExistsGlCol
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.MemRatVIff
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isFrames_of'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (η : E) (hη : η ≠ 0) (hcm : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ)
    (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) (hηζ : (σ η = η ∧ R.ζ = 1) ∨ (σ η = -η ∧ R.ζ = Complex.I))
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ))
    (th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y))
    (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star) :
    Gen.IsFrames (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) θ (_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.εsW_k R η) fr := by
  intro w
  set τ := (d.B.emb w).1 with hτ
  set a := τ η with ha
  set c := cW d.B η w with hc
  have hθ1 : ∀ x : E, θ w ((1 : HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) ⊗ₜ[F] x) = star (τ x) := fun x => by
    have := th w ((1 : AF F) ⊗ₜ[F] x)
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, piInf_one] at this
    exact this
  have hmat : (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η)).map (θ w) = a • d.A.J.map τ := by
    ext i j
    simp only [Matrix.map_apply, HeckeCharacterZeroLocus.SiegelWeilU.JR, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
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
  have key : (fr w).1ᴴ * (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η)).map (θ w) * (fr w).1 =
      (((‖z‖⁻¹ : ℝ) : ℂ) * z) • (1 : Matrix (Fin d.m) (Fin d.m) ℂ) := by
    rw [hfrH, hmat, frc w, show ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = c from rfl]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hfr', smul_smul, hzn, ← hcc, hz]
    congr 1
    field_simp
  change (fr w).1ᴴ * (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η)).map (θ w) * (fr w).1 = _
  rw [key, norm_inv_mul_self hz0 hzim]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [_root_.PositivityTheory.SiegelWeilFormula.ThetaDictR.εsW_k, sgn, hz, ha, hτ]
  · simp [hij]
end PositivityTheory.SiegelWeilFormula.ThetaDictR
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp PositivityTheory.SiegelWeilFormula.kfour
namespace PositivityTheory.SiegelWeilFormula.Afc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem eps_eq_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {ε ε' : ℤˣ} (hε : FrameEq σ d.Y d.b ε) (hε' : FrameEq σ L.Y L.b ε') : ε = ε' := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have hnL : 1 ≤ L.n := L.ok.hn
  have key : ∀ (s : ℤ), (∀ i j, σ (d.Y.J j i) = (s : E) * d.Y.J i j) → (∀ i j, σ (L.Y.J j i) = (s : E) * L.Y.J i j) →
      ε = ε' := fun s h1 h2 =>
    Units.ext ((eps_of_sign hσ d.ok.hn hε s h1).trans (eps_of_sign hσ hnL hε' s h2).symm)
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩ <;> rcases L.ok.sign with ⟨hA', hY'⟩ | ⟨hA', hY'⟩
  · exact key (-1) (fun i j => by rw [hY]; simp) (fun i j => by rw [hY']; simp)
  · exact (not_herm_skew d.ok.hm hA hA').elim
  · exact (not_herm_skew d.ok.hm hA' hA).elim
  · exact key 1 (fun i j => by rw [hY]; simp) (fun i j => by rw [hY']; simp)
end PositivityTheory.SiegelWeilFormula.Afc
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem th_JR_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) :
    HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) = inclR (F := F) (E := E) (AF F) η • (incM F d.A.J)ᵀ := by
  ext i j
  simp [HeckeCharacterZeroLocus.SiegelWeilU.JR, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, incM, th_inclR_eq, Matrix.transpose_apply, map_mul]
theorem th_mem_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (g : GL (Fin d.m) (AE F E)) :
    g ∈ UG (cA σ) (incM F d.A.J) ↔ g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := by
  have hc : IsUnit (inclR (F := F) (E := E) (AF F) η) := (Ne.isUnit hη).map _
  have hm : (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) =
      (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ) := by
    ext i j; exact th_sigR_eq _
  show (g : Matrix (Fin d.m) (Fin d.m) (AE F E))ᵀ * incM F d.A.J * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ) =
      incM F d.A.J ↔ HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) (g : Matrix (Fin d.m) (Fin d.m) (AE F E)) *
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)) = HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η)
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_JR_k, HeckeCharacterZeroLocus.SiegelWeilU.cT, hm]
  set L := (g : Matrix (Fin d.m) (Fin d.m) (AE F E))ᵀ * incM F d.A.J * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ)
  have hL : ((g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ))ᵀ *
      (inclR (F := F) (E := E) (AF F) η • (incM F d.A.J)ᵀ) * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)) =
      inclR (F := F) (E := E) (AF F) η • Lᵀ := by
    simp only [L, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [hL]
  constructor
  · intro h; rw [h]
  · intro h
    have h2 := congrArg (fun M => (hc.unit⁻¹ : (AE F E)ˣ) • M) h
    simp only [Units.smul_def, smul_smul] at h2
    have h3 : ((hc.unit⁻¹ : (AE F E)ˣ) : AE F E) * inclR (F := F) (E := E) (AF F) η = 1 := by
      exact hc.val_inv_mul
    rw [h3, one_smul, one_smul] at h2
    have := congrArg Matrix.transpose h2
    simpa using this
def thE_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : UA σ d.A.J ≃* HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) :=
  MulEquiv.subgroupCongr (Subgroup.ext (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_mem_iff_k d hη))
theorem thE_cont_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη) :=
  continuous_subtype_val.subtype_mk _
theorem thE_symm_cont_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).symm :=
  continuous_subtype_val.subtype_mk _
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def zInv_k (z : InfinitePlace F → Fin d.m → Fin d.n → ℂ) : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ :=
  fun i => if i.2.2.2 then (z i.1 i.2.1 i.2.2.1).re else (z i.1 i.2.1 i.2.2.1).im
variable (d) in
def zLE_k : (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d → ℝ) ≃ₗ[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k (d := d)
  invFun := _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zInv_k (d := d)
  map_add' u v := by
    funext w a j
    apply Complex.ext <;> simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k]
  map_smul' c u := by
    funext w a j
    apply Complex.ext <;> simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k]
  left_inv u := by
    funext i
    obtain ⟨w, a, j, b⟩ := i
    cases b <;> simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zInv_k]
  right_inv z := by
    funext w a j
    apply Complex.ext <;> simp [_root_.PositivityTheory.SiegelWeilFormula.KFP.zOf_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zInv_k]
theorem hg_sch_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM)
    {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg' : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) : ∃ h : 𝓢(_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d, ℂ), ⇑h = _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f g := by
  obtain ⟨L, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.archEquiv_k d R
  let Zc : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) :=
    (EuclideanSpace.equiv (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℝ).trans (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.zLE_k d).toContinuousLinearEquiv
  let c : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → (Fin d.m × Fin d.n × Fin 2 → AF F) := fun u y k =>
    (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (Zc u) k)) (y k) : AF F)
  have hc1 : ∀ u y, (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c u y k).1) = L.symm (Zc u) := by
    intro u y
    funext k
    exact RingEquiv.apply_symm_apply _ _
  have hjn : ∀ u y, _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y = d.cmb (c u y) := by
    intro u y
    refine (_root_.PositivityTheory.SiegelWeilFormula.KFP.exists_jn_k R u y).unique ⟨_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k R u y, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k R u y⟩ ⟨?_, ?_⟩
    · rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_eq_iff_k]
      intro w
      rw [← hL (c u y) w, hc1, ContinuousLinearEquiv.apply_symm_apply]
      rfl
    · funext k
      show (d.crd (d.cmb (c u y)) k).2 = y k
      rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb'_k]
  haveI := hνf
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := Pi.borelSpace
  have hint : ∀ g' ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), Integrable (fun y => g' y * star (g y)) νf := by
    intro g' hg''
    have hc : Continuous (fun y => g' y * star (g y)) :=
      hg''.1.continuous.mul (continuous_star.comp hg'.1.continuous)
    exact hc.integrable_of_hasCompactSupport (hg''.2.mul_right (f' := fun y => star (g y)))
  have key : ∀ Φ ∈ schA F (Fin d.m × Fin d.n × Fin 2), (∀ u, Integrable (fun y => Φ (c u y) * star (g y)) νf) ∧
      ∃ h : 𝓢(_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d, ℂ), ∀ u, h u = ∫ y, Φ (c u y) * star (g y) ∂νf := by
    intro Φ hΦ
    unfold schA at hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ hmem =>
      obtain ⟨φ, g', hg'', rfl⟩ := hmem
      have e : ∀ u y, pureA F φ g' (c u y) = φ (L.symm (Zc u)) * g' y := by
        intro u y
        simp only [pureA]
        rw [hc1]
      refine ⟨fun u => ?_, ⟨(∫ y, g' y * star (g y) ∂νf) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Zc.trans L.symm) φ,
        fun u => ?_⟩⟩
      · simp only [e, mul_assoc]
        exact (hint g' hg'').const_mul _
      · simp only [e, mul_assoc, integral_const_mul, SchwartzMap.smul_apply,
          SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, ContinuousLinearEquiv.trans_apply,
          smul_eq_mul]
        ring
    | zero => exact ⟨fun u => by simp, 0, fun u => by simp⟩
    | add Φ₁ Φ₂ _ _ h₁ h₂ =>
      obtain ⟨i1, k1, e1⟩ := h₁
      obtain ⟨i2, k2, e2⟩ := h₂
      refine ⟨fun u => ?_, k1 + k2, fun u => ?_⟩
      · simp only [Pi.add_apply, add_mul]
        exact (i1 u).add (i2 u)
      · simp only [Pi.add_apply, add_mul, SchwartzMap.add_apply, e1, e2]
        rw [integral_add (i1 u) (i2 u)]
    | smul a Φ _ h =>
      obtain ⟨i1, k1, e1⟩ := h
      refine ⟨fun u => ?_, a • k1, fun u => ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact (i1 u).const_mul a
      · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, SchwartzMap.smul_apply, e1, integral_const_mul]
  obtain ⟨-, h, eh⟩ := key (f ∘ d.cmb) hf
  refine ⟨h, funext fun u => ?_⟩
  rw [eh u]
  show _ = ∫ y, f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R u y) * star (g y) ∂νf
  simp only [hjn, Function.comp_apply]
end PositivityTheory.SiegelWeilFormula.KFP.OswGen
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem arc_apply_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) (i : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) :
    _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X i = if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im := rfl
theorem norm_arc_sq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) :
    ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2 = ∑ w, ∑ a, ∑ j, ‖R.loc w X a j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.arc_apply_k, if_true, Bool.false_eq_true, if_false,
    Real.norm_eq_abs, sq_abs]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring
theorem gauss_eq_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (X : Mx F E d.m d.n) :
    ((Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℝ) : ℂ) = ∏ w, gs (2 * Real.pi) (R.loc w X) := by
  rw [Complex.ofReal_exp, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.norm_arc_sq_k]
  simp only [gs]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_neg_distrib]
def lin_k (a : Fin d.m) (j : Fin d.n) (b : Bool) : PX d.m d.n :=
  if b then MvPolynomial.C (1 / 2) * (MvPolynomial.X (a, j, false) + MvPolynomial.X (a, j, true))
  else MvPolynomial.C (-Complex.I / 2) * (MvPolynomial.X (a, j, false) - MvPolynomial.X (a, j, true))
theorem evX_lin_k (a : Fin d.m) (j : Fin d.n) (b : Bool) (z : Fin d.m → Fin d.n → ℂ) :
    evX (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k (d := d) a j b) z = ((if b then (z a j).re else (z a j).im : ℝ) : ℂ) := by
  cases b
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k, evX, Bool.false_eq_true, if_false, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X,
      if_true]
    apply Complex.ext <;> simp <;> ring
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k, evX, if_true, Bool.false_eq_true, if_false, map_mul, map_add (f := _), MvPolynomial.eval_C,
      MvPolynomial.eval_X]
    apply Complex.ext <;> simp <;> ring
theorem fP_mul_k (P Q : PX d.m d.n) (u : Fin d.m → Fin d.n → ℂ) : fP (P * Q) u = evX P u * fP Q u := by
  simp only [fP, evX, map_mul]
  ring
theorem mul_coord_mem_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (i : _root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) {h : Mx F E d.m d.n → ℂ} (hh : h ∈ R.fock) :
    (fun X => ((_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X i : ℝ) : ℂ) * h X) ∈ R.fock := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.fock _root_.PositivityTheory.SiegelWeilFormula.RD_k.fockOn at hh ⊢
  induction hh using Submodule.span_induction with
  | mem h hmem =>
    obtain ⟨P, g, hg, rfl⟩ := hmem
    apply Submodule.subset_span
    refine ⟨Function.update P i.1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1), g, hg, ?_⟩
    funext X
    have e1 : ∏ w ∈ Finset.univ, fP (Function.update P i.1 (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1) w) (R.loc w X) =
        fP (_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.lin_k i.2.1 i.2.2.1 i.2.2.2 * P i.1) (R.loc i.1 X) * ∏ w ∈ Finset.univ.erase i.1, fP (P w) (R.loc w X) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i.1), Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun w hw => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
    have e2 : ∏ w ∈ Finset.univ, fP (P w) (R.loc w X) =
        fP (P i.1) (R.loc i.1 X) * ∏ w ∈ Finset.univ.erase i.1, fP (P w) (R.loc w X) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i.1)).symm
    dsimp only
    rw [e1, e2, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.fP_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.evX_lin_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.arc_apply_k]
    ring
  | zero =>
    convert Submodule.zero_mem _ using 1
    ext X
    simp
  | add h₁ h₂ _ _ i₁ i₂ =>
    convert Submodule.add_mem _ i₁ i₂ using 1
    funext X
    simp [mul_add]
  | smul a h _ i₁ =>
    convert Submodule.smul_mem _ a i₁ using 1
    ext X
    simp [smul_eq_mul, mul_comm, mul_assoc]
theorem poly_mem_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (Q : MvPolynomial (_root_.PositivityTheory.SiegelWeilFormula.KFP.Iw_k d) ℂ) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) :
    (fun X => MvPolynomial.eval (fun i => ((_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X i : ℝ) : ℂ)) Q * (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) *
      g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) ∈ R.fock := by
  have base : (fun X => (Real.exp (-(2 * Real.pi * ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X‖ ^ 2)) : ℂ) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X)) ∈ R.fock := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.fock _root_.PositivityTheory.SiegelWeilFormula.RD_k.fockOn
    apply Submodule.subset_span
    refine ⟨fun _ => 1, g, hg, ?_⟩
    funext X
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.gauss_eq_k]
    simp only [fP, evX, map_one, one_mul]
    rfl
  induction Q using MvPolynomial.induction_on with
  | C a =>
    convert Submodule.smul_mem _ a base using 1
    ext X
    simp [smul_eq_mul, mul_assoc]
  | add p q hp hq =>
    convert Submodule.add_mem _ hp hq using 1
    ext X
    simp [add_mul]
  | mul_X p i hp =>
    convert _root_.PositivityTheory.SiegelWeilFormula.KFP.OswGen.mul_coord_mem_k R i hp using 1
    ext X
    simp only [map_mul, MvPolynomial.eval_X]
    ring
end PositivityTheory.SiegelWeilFormula.KFP.OswGen
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem inFrame_dil_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) : inFrame d.b (R.ι w y) = Matrix.diagonal (dilV d.cm w i₀ τ) := by
  haveI := d.cm.1
  refine Place.mat_ext d.cm d.B.emb (fun u => ?_) ?_
  · have hD : (Matrix.diagonal (dilV d.cm w i₀ τ)).map (piInf (d.B.emb u)) =
        Matrix.diagonal (fun k => piInf (d.B.emb u) (dilV d.cm w i₀ τ k)) := Matrix.diagonal_map (map_zero _)
    rw [hD]
    simp_rw [piInf_dilV d.cm d.B.emb w u i₀ τ]
    by_cases hu : u = w
    · subst hu
      simp only [ite_true]
      have hat := R.at_w u y
      have hζ : R.ζ ≠ 0 := by
        rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
        · exact one_ne_zero
        · exact Complex.I_ne_zero
      have hZ : dZ d.n R.ζ⁻¹ * dZ d.n R.ζ = 1 := by
        simp only [dZ, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
          add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hζ, mul_inv_cancel₀ hζ, one_smul,
          smul_zero, Matrix.fromBlocks_one]
      have e1 : d.cw u (inFrame d.b (R.ι u y)) = dZ d.n R.ζ⁻¹ * (mR y * dZ d.n R.ζ) := by
        rw [← hat, ← Matrix.mul_assoc, hZ, Matrix.one_mul]
      show d.cw u _ = _
      rw [e1, hy, ← Matrix.fromBlocks_diagonal]
      simp only [dZ, Matrix.fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul,
        add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hζ, one_smul, Matrix.one_mul,
        smul_zero, mul_inv_cancel₀ hζ]
    · simp only [if_neg hu, Matrix.diagonal_one]
      exact R.off_w w u y hu
  · rw [R.off_f w y]
    ext i j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with hij
    · subst hij; exact (finOne_dilV d.cm w i₀ τ i).symm
    · rfl
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end
