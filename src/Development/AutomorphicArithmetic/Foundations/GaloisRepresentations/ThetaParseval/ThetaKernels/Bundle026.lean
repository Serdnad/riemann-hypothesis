module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.WeylElementTransposeMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle003
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.Bundle002
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HeightLattices.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
public import GroundTheory.AutomorphicForms.GL2.GJMatrixCoord
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaPlaces.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.CharP
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem auxiliaryExistence_holds : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨ν, 𝓕, hν, h𝓕, h1⟩ := exists_cov (F := F) (E := E) d.m d.n
  obtain ⟨i1, i2, i3, i4⟩ := doubled_group_topological_properties σ d.Y
  exact ⟨⟨ν, hν, 𝓕, h𝓕, h1⟩, exists_w d.ok.frame, i1, i2, i3, i4⟩
end PositivityTheory.SiegelWeilFormula.kfour
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.bb1 : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  rw [← incM_mul', ← Units.val_mul, mul_inv_cancel, Units.val_one, incM_one']
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.bb2 : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  rw [← incM_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, incM_one']
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.inFrame_mul (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  have hmul : mat2 (x * y) = mat2 x * mat2 y := rfl
  simp only [inFrame, hmul]
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 y) * incM F d.b.1
      = incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 y * incM F d.b.1 := by
        rw [d.bb1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.inFrame_one : inFrame d.b (1 : d.G) = 1 := by
  change incM F (d.b⁻¹).1 * 1 * incM F d.b.1 = 1
  simpa only [Matrix.mul_one] using d.bb2
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.inFrame_inj {x y : d.G} (h : inFrame d.b x = inFrame d.b y) : x = y := by
  have hx : mat2 x = incM F d.b.1 * inFrame d.b x * incM F (d.b⁻¹).1 := by
    simp only [inFrame, ← Matrix.mul_assoc, d.bb1, Matrix.one_mul]
    rw [Matrix.mul_assoc, d.bb1, Matrix.mul_one]
  have hy : mat2 y = incM F d.b.1 * inFrame d.b y * incM F (d.b⁻¹).1 := by
    simp only [inFrame, ← Matrix.mul_assoc, d.bb1, Matrix.one_mul]
    rw [Matrix.mul_assoc, d.bb1, Matrix.mul_one]
  have : mat2 x = mat2 y := by rw [hx, hy, h]
  exact Subtype.ext (Units.ext this)
end SD
end PositivityTheory.SiegelWeilFormula
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act.CL
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem ptEx'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    {X : Type} [TopologicalSpace X] (M M' : X → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (hM : Continuous M) (hM' : Continuous M') (h : ∀ c, M c * M' c = 1)
    (hu : ∀ c, (M c)ᵀ * kunf.jw d.n (((ε : ℤ) : AE F E)) * (M c).map (cA σ) = kunf.jw d.n (((ε : ℤ) : AE F E))) :
    ∃ f : X → d.G, Continuous f ∧ ∀ c, inFrame d.b (f c) = M c := by
  set B0 := incM F d.b.1 with hB0
  set Bi := incM F (d.b⁻¹).1 with hBi
  have e1 : B0 * Bi = 1 := GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv d.b
  have e2 : Bi * B0 = 1 := GlobalTheory.EisBL.DoubledParabolic.incM_inv_mul d.b
  have h' : ∀ c, M' c * M c = 1 := fun c => mul_eq_one_comm.1 (h c)
  let U : X → GL (Fin d.n ⊕ Fin d.n) (AE F E) := fun c => ⟨B0 * M c * Bi, B0 * M' c * Bi, by
      calc B0 * M c * Bi * (B0 * M' c * Bi) = B0 * (M c * (Bi * B0) * M' c) * Bi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e2, Matrix.mul_one, h, Matrix.mul_one, e1], by
      calc B0 * M' c * Bi * (B0 * M c * Bi) = B0 * (M' c * (Bi * B0) * M c) * Bi := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e2, Matrix.mul_one, h', Matrix.mul_one, e1]⟩
  have hU : ∀ c, U c ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    intro c
    obtain ⟨x, hx⟩ := kunf.exists_of_frame (Y := d.Y) hε (M c) (M' c) (h c) (hu c)
    have hx1 : x.1 = U c := by
      apply Units.ext
      show mat2 x = B0 * M c * Bi
      rw [← hx]
      show mat2 x = B0 * (Bi * mat2 x * B0) * Bi
      calc mat2 x = (B0 * Bi) * mat2 x * (B0 * Bi) := by rw [e1, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    exact hx1 ▸ x.2
  refine ⟨fun c => ⟨U c, hU c⟩, ?_, fun c => ?_⟩
  · refine continuous_induced_rng.2 ?_
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_const.matrix_mul hM).matrix_mul continuous_const
    · exact (continuous_const.matrix_mul hM').matrix_mul continuous_const
  · show Bi * (B0 * M c * Bi) * B0 = M c
    calc Bi * (B0 * M c * Bi) * B0 = (Bi * B0) * M c * (Bi * B0) := by simp only [Matrix.mul_assoc]
      _ = M c := by rw [e2, Matrix.one_mul, Matrix.mul_one]
end PositivityTheory.SiegelWeilFormula.Act.CL
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.KWhit.Ht
namespace PositivityTheory.SiegelWeilFormula.HeightDict
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fin_std_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (t u : GL (Fin n) (AE F E)) (η : E) (hη : η ≠ 0) :
    (∀ v : HeightOneSpectrum (𝓞 F),
      Gen.IsCO (latM v ((t.1.map (GlobalTheory.AdelicU.compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ))) ∧
      Gen.IsCO (latM v (((inclR (F := F) (v.adicCompletion F) η) • u.1.map (GlobalTheory.AdelicU.compFin F E v)).map
        (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)))) ∧
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ((latM v ((t.1.map (GlobalTheory.AdelicU.compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)) :
        Set (Fin n → v.adicCompletion F ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v) ∧
      ((latM v (((inclR (F := F) (v.adicCompletion F) η) • u.1.map (GlobalTheory.AdelicU.compFin F E v)).map
        (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ)) : Set (Fin n → v.adicCompletion F ⊗[F] E)) =
          PositivityTheory.PfSWUS.Loc.latO d.bs v) := by
  classical
  have hinv1 : ∀ v : HeightOneSpectrum (𝓞 F),
      (t.1.map (compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) *
        ((t⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1 := by
    intro v
    have h := congrArg (fun M => (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ).mapMatrix
      ((compFin F E v).mapMatrix M)) (Units.mul_inv t)
    simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
  have hinv2 : ∀ v : HeightOneSpectrum (𝓞 F),
      ((inclR (F := F) (v.adicCompletion F) η) • u.1.map (compFin F E v)).map
          (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) *
        ((inclR (F := F) (v.adicCompletion F) η⁻¹) • (u⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v)).map
          (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ) = 1 := by
    intro v
    have hu : u.1.map (compFin F E v) * (u⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v) = 1 := by
      have h := congrArg (fun M => (compFin F E v).mapMatrix M) (Units.mul_inv u)
      simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
    have hc : inclR (F := F) (v.adicCompletion F) η * inclR (F := F) (v.adicCompletion F) η⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hη, map_one]
    have h2 : (inclR (F := F) (v.adicCompletion F) η • u.1.map (compFin F E v)) *
        (inclR (F := F) (v.adicCompletion F) η⁻¹ • (u⁻¹ : GL (Fin n) (AE F E)).1.map (compFin F E v)) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, hu, smul_smul, hc, one_smul]
    have h := congrArg (fun M => (HeckeCharacterZeroLocus.SiegelWeilU.sigR (v.adicCompletion F) σ).mapMatrix M) h2
    simpa only [map_mul, map_one, RingHom.mapMatrix_apply] using h
  refine ⟨fun v => ⟨latM_isCO v _ (Matrix.isUnit_det_of_right_inverse (hinv1 v)),
    latM_isCO v _ (Matrix.isUnit_det_of_right_inverse (hinv2 v))⟩, ?_⟩
  have ent : ∀ M : Matrix (Fin n) (Fin n) (AE F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      ∀ i j, compFin F E v (M i j) ∈ OE E v := fun M =>
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_OE (M i j)
  filter_upwards [ent t.1, ent (t⁻¹ : GL (Fin n) (AE F E)).1, ent u.1, ent (u⁻¹ : GL (Fin n) (AE F E)).1,
    ev_inclR (F := F) η, ev_inclR (F := F) η⁻¹, ev_lat_latO d.bs n] with v ht ht' hu hu' he he' hl
  refine ⟨?_, ?_⟩
  · rw [latM_eq_lat v _ _ (hinv1 v) (fun i j => OE_sig v (ht i j)) (fun i j => OE_sig v (ht' i j)), hl]
  · rw [latM_eq_lat v _ _ (hinv2 v) (fun i j => OE_sig v (OE_mul v he (hu i j)))
      (fun i j => OE_sig v (OE_mul v he' (hu' i j))), hl]
end PositivityTheory.SiegelWeilFormula.HeightDict
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
section SDl
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
def linRhoL_k (v : Mx F E d.m d.n) : d.Fn →ₗ[ℂ] d.Fn where
  toFun := d.dd.rho d.B.ψ (v * (incM F d.b.1.toCols₂)ᵀ)
  map_add' Φ Ψ := by
    funext y
    simp only [Darboux.rho, schr, Pi.add_apply]
    ring
  map_smul' a Φ := by
    funext y
    simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
theorem lin_T_sum_k {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (X : Mx F E d.m d.n) :
    d.T (∑ i ∈ s, c i • Φs i) X = ∑ i ∈ s, c i * d.T (Φs i) X := by

  change d.l (linRhoL_k d X (∑ i ∈ s, c i • Φs i)) = ∑ i ∈ s, c i * d.l (linRhoL_k d X (Φs i))
  simp only [map_sum, map_smul, smul_eq_mul]
theorem constantTerm_finsetSum {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (x : d.G) :
    d.sec0 (∑ i ∈ s, c i • Φs i) x = ∑ i ∈ s, c i * d.sec0 (Φs i) x := by

  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, map_sum, map_smul, smul_eq_mul]
theorem lin_om_mem_k (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ h
theorem lin_S_mem_k (g : UA σ d.A.J) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.S g Φ ∈ d.sch := d.ok.dbl.lin.pres g Φ h
theorem lin_sum_mem_k {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (h : ∀ i ∈ s, Φs i ∈ d.sch) :
    ∑ i ∈ s, c i • Φs i ∈ d.sch :=
  Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (h i hi)
theorem lin_thetaSum_sum_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn) (h : ∀ i ∈ s, Φs i ∈ d.sch) :
    thetaSum F (∑ i ∈ s, c i • Φs i) = ∑ i ∈ s, c i * thetaSum F (Φs i) := by
  have h1 := (hT F E σ d _ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_sum_mem_k d s c Φs h)).1
  have h2 : HasSum (fun X : Matrix (Fin d.m) (Fin d.n) E => ∑ i ∈ s, c i * d.T (Φs i) (incM F X))
      (∑ i ∈ s, c i * thetaSum F (Φs i)) :=
    hasSum_sum fun i hi => ((hT F E σ d _ (h i hi)).1).mul_left (c i)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_T_sum_k] at h1
  exact h1.unique h2
theorem lin_I_sum_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k) {ι : Type} (s : Finset ι) (c : ι → ℂ) (Φs : ι → d.Fn)
    (h : ∀ i ∈ s, Φs i ∈ d.sch) (x : d.G) : d.I (∑ i ∈ s, c i • Φs i) x = ∑ i ∈ s, c i * d.I (Φs i) x := by
  have e : ∀ g : UA σ d.A.J, thetaSum F (d.om x (d.S g (∑ i ∈ s, c i • Φs i))) =
      ∑ i ∈ s, c i * thetaSum F (d.om x (d.S g (Φs i))) := by
    intro g

    rw [map_sum, map_sum]
    simp only [map_smul]
    exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_thetaSum_sum_k d hT s c (fun i => d.om x (d.S g (Φs i))) fun i hi => _root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_om_mem_k d x (_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_S_mem_k d g (h i hi))
  have hint : ∀ i ∈ s, IntegrableOn (fun g => thetaSum F (d.om x (d.S g (Φs i)))) d.D d.μ :=
    fun i hi => ((hA F E σ d).2.2 _ (h i hi)).1 x
  show ⨍ g in d.D, thetaSum F (d.om x (d.S g (∑ i ∈ s, c i • Φs i))) ∂d.μ =
    ∑ i ∈ s, c i * ⨍ g in d.D, thetaSum F (d.om x (d.S g (Φs i))) ∂d.μ
  simp only [e, setAverage_eq]
  rw [integral_finsetSum s fun i hi => (hint i hi).const_mul (c i), Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, mul_smul_comm]
end SDl
theorem lin_psi_meas_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (M : Mx F E d.n d.n) :
    Measurable (fun β : nA σ d.Y d.b => d.B.ψ (-d.tt (M * β.1))) := by
  have key : ∀ β : nA σ d.Y d.b, d.B.ψ (-d.tt (M * β.1)) =
      ∏ i, ∏ k, d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * β.1 k i))) := by
    intro β

    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, ← Finset.sum_neg_distrib, lin_addChar_sum]
  rw [show (fun β : nA σ d.Y d.b => d.B.ψ (-d.tt (M * β.1))) = fun β =>
      ∏ i, ∏ k, d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * β.1 k i))) from funext key]
  have : OpensMeasurableSpace (AE F E) := ⟨le_rfl⟩
  refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun k _ => ?_
  have hc : Continuous fun y : AE F E => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (M i k * y))) :=
    d.ok.good.std.1.comp (IsModuleTopology.continuous_of_linearMap
      ((Algebra.trace (AF F) (AE F E)).comp (LinearMap.mulLeft (AF F) (M i k)))).neg
  exact hc.measurable.comp ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_subtype_coe))
theorem lin_fc_sum_k (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb lam 𝓖} (hcd : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖)
    (T : nF σ d.Y d.b) (hND : IsND T) (x : d.G) {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → d.G → ℂ)
    (hc : ∀ i, Continuous (f i)) (hi : ∀ i, ∀ γ ∈ rat2 σ d.Y, ∀ g, f i (γ * g) = f i g) :
    fc d.B.ψ d.b nb lam 𝓖 (∑ i ∈ s, c i • f i) T x = ∑ i ∈ s, c i * fc d.B.ψ d.b nb lam 𝓖 (f i) T x := by
  classical
  obtain ⟨hlin, -⟩ := hLB F E σ d (fun f => fc d.B.ψ d.b nb lam 𝓖 f T x) ⟨nb, lam, 𝓖, T, x, hcd, hND, rfl⟩
  have hfun : ∀ s : Finset ι, (∑ i ∈ s, c i • f i) = fun a => ∑ i ∈ s, c i * f i a := by
    intro s; funext a; simp [Finset.sum_apply]
  have hcs : ∀ s : Finset ι, Continuous (∑ i ∈ s, c i • f i) := by
    intro s; rw [hfun s]; exact continuous_finsetSum s fun i _ => continuous_const.mul (hc i)
  have his : ∀ s : Finset ι, ∀ γ ∈ rat2 σ d.Y, ∀ g, (∑ i ∈ s, c i • f i) (γ * g) = (∑ i ∈ s, c i • f i) g := by
    intro s γ hγ g; rw [hfun s]; exact Finset.sum_congr rfl fun i _ => by rw [hi i γ hγ g]
  induction s using Finset.induction_on with
  | empty =>
    have h0 := hlin 1 0 0 continuous_const continuous_const (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    simp only [one_smul, add_zero, one_mul] at h0
    simpa using h0
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, hlin (c j) (f j) _ (hc j) (hcs s) (hi j) (his s), ih]
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.ThetaDictR.PureB
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem crd_eq_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (u : GL (Fin d.n) (AE F E)) (η : E)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ))
    (th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y))
    (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star)
    (g : InfinitePlace F → GL (Fin d.n) ℂ)
    (gc : ∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1)
    (w : InfinitePlace F) (X : Fin d.n → Fin d.m → AF F ⊗[F] E) :
    Gen.crd (θ w) (fr w) (g w) (HeckeCharacterZeroLocus.SiegelWeilU.projInf X) = R.loc w (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) := by
  set c : ℂ := ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) with hcdef
  have hm : Nonempty (Fin d.m) := ⟨⟨0, d.ok.hm⟩⟩
  have hc : c ≠ 0 := by
    intro h0
    have h1 := frc w
    rw [← hcdef, h0, zero_smul] at h1
    have h2 : ((fr w)⁻¹).1 * (fr w).1 = 1 := Units.inv_mul (fr w)
    rw [h1, Matrix.mul_zero] at h2
    exact zero_ne_one h2
  have hfr : ((fr w)⁻¹).1 = c⁻¹ • (((R.fr w)⁻¹).1).map star := by
    refine Units.inv_eq_of_mul_eq_one_left ?_
    rw [frc w, ← hcdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, ← map_star_mul,
      Units.inv_mul]
    exact Matrix.map_one _ (star_zero _) (star_one _)
  have hN : ((d.cw w u.1)ᵀ).map star * ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star = 1 := by
    rw [← map_star_mul, ← Matrix.transpose_mul]
    have : d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1 * d.cw w u.1 = 1 := by
      unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw
      rw [← Matrix.map_mul (f := piInf (d.B.emb w)), Units.inv_mul]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [this, Matrix.transpose_one]
    exact Matrix.map_one _ (star_zero _) (star_one _)
  have hg : (g w).1 = c • ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star := by
    calc (g w).1 = (g w).1 * (((d.cw w u.1)ᵀ).map star * ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star) := by
          rw [hN, Matrix.mul_one]
      _ = c • ((d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ).map star := by
          rw [← Matrix.mul_assoc, gc w, ← hcdef, Matrix.smul_mul, Matrix.one_mul]
  have hX : Matrix.of (fun a j => θ w (HeckeCharacterZeroLocus.SiegelWeilU.projInf X j a)) = (d.cw w (toMx X)).map star := by
    ext a j
    simp only [Matrix.of_apply, HeckeCharacterZeroLocus.SiegelWeilU.projInf, th, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, toMx]
  have hZ : d.cw w (toMx X * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ) =
      d.cw w (toMx X) * (d.cw w (u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ := by
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw
    rw [Matrix.map_mul (f := piInf (d.B.emb w)), Matrix.transpose_map]
  unfold Gen.crd _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [hfr, hX, hg, hZ, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc, one_smul,
    map_star_mul, map_star_mul, Matrix.mul_assoc]
end PositivityTheory.SiegelWeilFormula.ThetaDictR.PureB
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
set_option linter.style.haveILetI false
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem meas_herm_top'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsTopologicalAddGroup (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧
    LocallyCompactSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧ SecondCountableTopology (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧
    BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧ Countable (MeasP.ratHerm F E σ d.n) := by
  have hCM : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ := d.ok.good.cm
  obtain ⟨⟨hLC, hSC, hT2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hLC; haveI := hSC; haveI := hT2
  obtain ⟨hTR, hLC', hSC', hT2', -, -, -, -, hcl, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := hTR; haveI := hLC'; haveI := hSC'; haveI := hT2'
  haveI : LocallyCompactSpace (Matrix (Fin d.n) (Fin d.n) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin d.n → Fin d.n → AF F ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin d.n) (Fin d.n) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin d.n → Fin d.n → AF F ⊗[F] E))
  haveI : Countable E := meas_countableE
  haveI : Countable (Matrix (Fin d.n) (Fin d.n) E) := inferInstanceAs (Countable (Fin d.n → Fin d.n → E))
  refine ⟨inferInstance, (hcl d.n).locallyCompactSpace,
    inferInstanceAs (SecondCountableTopology ((HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n : Set (Matrix (Fin d.n) (Fin d.n) (AF F ⊗[F] E))))),
    ⟨rfl⟩, ?_⟩
  have hc : (Set.range (AddMonoidHom.mapMatrix (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (E := E) (AF F)).toAddMonoidHom :
      Matrix (Fin d.n) (Fin d.n) E → Matrix (Fin d.n) (Fin d.n) (AF F ⊗[F] E))).Countable := Set.countable_range _
  haveI := hc.to_subtype
  refine Function.Injective.countable (f := fun x : MeasP.ratHerm F E σ d.n =>
    (⟨x.1.1, AddMonoidHom.mem_range.mp (AddSubgroup.mem_comap.mp x.2)⟩ : Set.range _)) ?_
  intro x y hxy
  have h := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext h)
theorem meas_mx_top'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsTopologicalAddGroup (Mx F E d.m d.n) ∧ LocallyCompactSpace (Mx F E d.m d.n) ∧
    SecondCountableTopology (Mx F E d.m d.n) ∧ BorelSpace (Mx F E d.m d.n) ∧ Countable d.ratM := by
  have hCM : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ := d.ok.good.cm
  obtain ⟨⟨hLC, hSC, hT2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hLC; haveI := hSC; haveI := hT2
  obtain ⟨hTR, hLC', hSC', hT2', -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := hTR; haveI := hLC'; haveI := hSC'; haveI := hT2'
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : Countable E := meas_countableE
  haveI : Countable (Matrix (Fin d.m) (Fin d.n) E) := inferInstanceAs (Countable (Fin d.m → Fin d.n → E))
  refine ⟨inferInstance, inferInstanceAs (LocallyCompactSpace (Fin d.m → Fin d.n → AE F E)),
    inferInstanceAs (SecondCountableTopology (Fin d.m → Fin d.n → AE F E)),
    ⟨(inferInstance : BorelSpace (Fin d.m → Fin d.n → AE F E)).measurable_eq⟩, ?_⟩
  let K : AddSubgroup (Mx F E d.m d.n) :=
    (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom).range
  have hle : d.ratM ≤ K := by
    refine (AddSubgroup.closure_le K).mpr ?_
    rintro _ ⟨X, rfl⟩
    exact ⟨X, rfl⟩
  have hc : (Set.range (AddMonoidHom.mapMatrix (inclR (F := F) (E := E) (AF F)).toAddMonoidHom :
      Matrix (Fin d.m) (Fin d.n) E → Mx F E d.m d.n)).Countable := Set.countable_range _
  haveI := hc.to_subtype
  refine Function.Injective.countable (f := fun x : d.ratM =>
    (⟨x.1, AddMonoidHom.mem_range.mp (hle x.2)⟩ : Set.range _)) ?_
  intro x y hxy
  have h := congrArg Subtype.val hxy
  exact Subtype.ext h
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end
