module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle181
public import GroundTheory.AutomorphicForms.GKModules.ZKFinite
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Translation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle194
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle034
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle023
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle011
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle031
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle196
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

section General

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_sq_map_eq {B : LinearMap.BilinForm ℝ L} {b : Module.Basis ι ℝ L} {ε : ι → ℝ}
    (hε : ∀ i, ε i * ε i = 1) (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y : L, B X Y = B Y X) (φ ψ : L →ₗ⁅ℝ⁆ L)
    (hφ : ∀ X Y, B (φ X) (φ Y) = B X Y) (hψ : ∀ X, φ (ψ X) = X) :
    ∑ j, ε j • (UniversalEnvelopingAlgebra.ι ℝ (φ (b j)) * UniversalEnvelopingAlgebra.ι ℝ (φ (b j))) =
      ∑ i, ε i • (UniversalEnvelopingAlgebra.ι ℝ (b i) * UniversalEnvelopingAlgebra.ι ℝ (b i)) := by
  set u := UniversalEnvelopingAlgebra.ι ℝ (L := L)
  have h1 : ∀ j, u (φ (b j)) = ∑ i, (ε i * B (b i) (φ (b j))) • u (b i) := fun j => by
    conv_lhs => rw [eq_sum_of_orthogonal hε horth (φ (b j))]

    simp only [map_sum, map_smul]
  have h2 : ∀ i, u (b i) = ∑ j, (ε j * B (φ (b j)) (b i)) • u (φ (b j)) := fun i => by
    have e := congrArg φ (eq_sum_of_orthogonal hε horth (ψ (b i)))
    rw [hψ] at e
    conv_lhs => rw [e]

    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hφ (b j) (ψ (b i)), hψ]
  calc ∑ j, ε j • (u (φ (b j)) * u (φ (b j)))
      = ∑ j, ε j • (u (φ (b j)) * ∑ i, (ε i * B (b i) (φ (b j))) • u (b i)) :=
        Finset.sum_congr rfl fun j _ => by rw [← h1 j]
    _ = ∑ i, ∑ j, (ε i * (ε j * B (φ (b j)) (b i))) • (u (φ (b j)) * u (b i)) := by
        simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hsymm (b i)]
        congr 1
        ring
    _ = ∑ i, ε i • ((∑ j, (ε j * B (φ (b j)) (b i)) • u (φ (b j))) * u (b i)) := by
        simp only [Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]
    _ = ∑ i, ε i • (u (b i) * u (b i)) :=
        Finset.sum_congr rfl fun i _ => by rw [← h2 i]

end General

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem archTraceForm_AdLie (g : archGroup E a) (X Y : (isExpLieAlgebra E a).lieSubalgebra) :
    archTraceForm E a ((isExpLieAlgebra E a).AdLie g X) ((isExpLieAlgebra E a).AdLie g Y) =
      archTraceForm E a X Y := by
  rw [archTraceForm_apply, archTraceForm_apply]
  congr 1
  have hgi : mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) *
      mat (((g : (ArchMatrix E a)ˣ)) : ArchMatrix E a) = 1 := by
    change (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) *
      (((g : (ArchMatrix E a)ˣ)) : ArchMatrix E a) = 1
    simp
  change Matrix.trace ((mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) * mat (X : ArchMatrix E a) *
      mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a)) *
    (mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) * mat (Y : ArchMatrix E a) *
      mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a))) = _
  generalize mat ((g : (ArchMatrix E a)ˣ) : ArchMatrix E a) = A at *
  generalize mat (((g⁻¹ : archGroup E a) : (ArchMatrix E a)ˣ) : ArchMatrix E a) = C at *
  generalize mat (X : ArchMatrix E a) = x
  generalize mat (Y : ArchMatrix E a) = y
  have e : A * x * C * (A * y * C) = A * (x * y * C) := by
    calc A * x * C * (A * y * C) = A * x * (C * A) * y * C := by simp only [Matrix.mul_assoc]
      _ = A * (x * y * C) := by rw [hgi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, hgi, Matrix.mul_one]

theorem AdLie_AdLie_inv (g : archGroup E a) (X : (isExpLieAlgebra E a).lieSubalgebra) :
    (isExpLieAlgebra E a).AdLie g ((isExpLieAlgebra E a).AdLie g⁻¹ X) = X := by
  have e := (isExpLieAlgebra E a).Ad_inv_Ad g⁻¹ ((isExpLieAlgebra E a).ofLie X)
  rw [inv_inv] at e
  exact Subtype.ext (congrArg Subtype.val e)

theorem AdU_casimir {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i * ε i = 1)
    (horth : ∀ i j, archTraceForm E a (b i) (b j) = if i = j then ε i else 0) (g : archGroup E a) :
    (isExpLieAlgebra E a).AdU g (casimir b ε) = casimir b ε := by

  simp only [casimir, map_sum, map_smul, map_mul, IsExpLieAlgebra.AdU_ι]
  exact sum_sq_map_eq hε horth archTraceForm_symm _ ((isExpLieAlgebra E a).AdLie g⁻¹)
    (archTraceForm_AdLie g) (AdLie_AdLie_inv g)

theorem toGL_surjective : Function.Surjective (toGL E a) := fun y => by
  refine ⟨archEquiv E a (Matrix.GeneralLinearGroup.map (infEq E).toRingHom y), ?_⟩
  simp only [toGL, ContinuousMulEquiv.symm_apply_apply]
  ext i j
  simp

theorem omegaOp_comm_rt (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0)
    (y : GL (Fin a) (Cinf E)) :
    GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε * rt E a (infGL E a y) = rt E a (infGL E a y) * GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  obtain ⟨u, rfl⟩ := toGL_surjective y
  rw [← infEmb_eq]
  have hrt : ∀ φ : Sm E a, smL E a (rt E a (infEmb E a u) φ) = rtInf u (smL E a φ) := fun _ => rfl
  refine LinearMap.ext fun ψ => smL_injective ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp, smL_omegaOp, hrt, uAction_rtInf,
    AdU_casimir b ε hε2 horth, hrt, smL_omegaOp]

end GlobalTheory.CompanionTheory.HCRep

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FibSim

theorem conj_scal {A : Type} [CommRing A] {M n : ℕ} (C : Matrix (Fin n) (Fin M) A)
    (D : Matrix (Fin M) (Fin n) A) (G' G J : Matrix (Fin M) (Fin M) A) (t : A)
    (h : G' * J * G = t • J) : (C * G' * J) * (G * D) = t • (C * J * D) := by
  calc (C * G' * J) * (G * D) = C * (G' * J * G) * D := by simp only [Matrix.mul_assoc]
    _ = t • (C * J * D) := by rw [h, Matrix.mul_smul, Matrix.smul_mul]

theorem fib_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (g : GL (Fin M) (R ⊗[F] E)) (l : R), IsUnit l → cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = (algebraMap R (R ⊗[F] E) l) • JR R J → ∀ a c : ℝ≥0, μ.map (actTup R g) = a • μ → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l) = c • ν → ∀ S, (m S).map (actTup R g) = (a / c) • m (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l S) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm g l hl hgl a c hmu hnu S
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor n M
  obtain ⟨hLH, hSH, hT2H, hBH, hG⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  obtain ⟨G, hGc, hGe⟩ := hG M J hJ
  have hKu := GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hσ R hR
  have hcont : ∀ h : GL (Fin M) (R ⊗[F] E),
      Continuous (actTup R h : (Fin n → Fin M → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E)) := by
    intro h
    refine continuous_pi fun b => ?_
    exact continuous_const.matrix_mulVec (continuous_apply b)
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := actTup R g
      invFun := actTup R g⁻¹
      left_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      right_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      continuous_toFun := hcont g
      continuous_invFun := hcont g⁻¹ }
  obtain ⟨u, rfl⟩ := hl
  let am := algebraMap R (R ⊗[F] E)
  have hinv : ∀ (v w : Rˣ) (_ : (v : R) * w = 1) (A : HermR R σ n),
      GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (v : R) (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (w : R) A) = A := by
    intro v w hvw A
    apply Subtype.ext
    rw [GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, smul_smul, ← map_mul, hvw,
      map_one, one_smul]
  have hcs : ∀ v : R, Continuous (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ v : HermR R σ n → HermR R σ n) := by
    intro v
    have hv : Continuous fun A : HermR R σ n => (A : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
      continuous_subtype_val
    exact (hv.const_smul (algebraMap R (R ⊗[F] E) v)).subtype_mk _
  let τh : HermR R σ n ≃ₜ HermR R σ n :=
    { toFun := GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (u : R)
      invFun := GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ ((u⁻¹ : Rˣ) : R)
      left_inv := hinv _ _ (by simp)
      right_inv := hinv _ _ (by simp)
      continuous_toFun := hcs _
      continuous_invFun := hcs _ }
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hBo : IsOpen B := by
    have : B = (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      rfl
    rw [this]
    exact hKu.isOpen_range.preimage continuous_subtype_val.matrix_det
  have hdet : ∀ (v : Rˣ) (A : HermR R σ n), A ∈ B → GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (v : R) A ∈ B := by
    intro v A hA
    show IsUnit ((GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (v : R) A : HermR R σ n) :
      Matrix (Fin n) (Fin n) (R ⊗[F] E)).det
    rw [GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, Matrix.det_smul]
    exact ((v.isUnit.map (algebraMap R (R ⊗[F] E))).pow _).mul hA
  have hBτ : τh '' B = B := by
    ext S'
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact hdet _ _ hS
    · intro hS'
      exact ⟨τh.symm S', hdet _ _ hS', τh.apply_symm_apply _⟩
  have hU : G ⁻¹' B = {X | IsUnit (gramR R σ J X).det} := by
    ext X
    show IsUnit _ ↔ IsUnit _
    rw [hGe]
  have hfam : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (G ⁻¹' B) ν B m := by
    rw [hU]
    exact hm
  have hgram : ∀ X : Fin n → Fin M → R ⊗[F] E, gramR R σ J (actTup R g X) =
      (algebraMap R (R ⊗[F] E) (u : R)) • gramR R σ J X := by
    intro X
    rw [GlobalTheory.CompanionTheory.SW.GramAlg.gramR_eq, GlobalTheory.CompanionTheory.SW.GramAlg.gramR_eq, GlobalTheory.CompanionTheory.SW.GramAlg.colM_actTup,
      cT_mul]
    exact conj_scal _ _ _ _ _ _ hgl
  have hcomm : ∀ X, G (e X) = τh (G X) := by
    intro X
    apply Subtype.ext
    show ((G (actTup R g X) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      ((GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (u : R) (G X) : HermR R σ n) :
        Matrix (Fin n) (Fin n) (R ⊗[F] E))
    rw [← hGe, GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, ← hGe]
    exact hgram X
  have htr := GlobalTheory.CompanionTheory.SW.isFibreFamily_transport _ _ _ μ ν (gramR R σ J) G Subtype.val
    Subtype.val_injective hGc hGe _ (gramR R σ J) G hGc hGe e τh hcomm B hBo m hfam
  rw [hBτ, hU] at htr
  have hmu' : μ.map e = a • μ := hmu
  have hnu' : ν.map τh = c • ν := hnu
  rw [hmu', hnu'] at htr
  have hnew : IsGramFib R σ J n (a • μ) (c • ν) (fun b => (m (τh.symm b)).map e) := htr
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h0 : μ.map e = 0 := by rw [hmu', zero_smul]
    have h1 : (μ.map e) Set.univ = μ Set.univ := by
      rw [e.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos μ Set.univ_nonempty).ne h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : ν.map τh = 0 := by rw [hnu', zero_smul]
    have h1 : (ν.map τh) Set.univ = ν Set.univ := by
      rw [τh.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos ν Set.univ_nonempty).ne h1
  haveI hμa : (a • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ ha0
  haveI hνc : (c • ν).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul ν hc0
  have hres := GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale F E σ hσ M J hJ R hR n μ ν m hμ hν hm a c ha0 hc0
  have huq := GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique F E σ hσ M J hJ R hR n (a • μ) (c • ν) _ hμa hνc hres _ hnew (τh S)
  have hs : τh.symm (τh S) = S := τh.symm_apply_apply S
  simp only [hs] at huq
  exact huq.symm

end GlobalTheory.CompanionTheory.SW.FibSim
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.SumDesc

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {I : Type 1} [DecidableEq I]

def sumPM (P : I → PM.{1} K ι) : PM.{1} K ι where
  M S := ⨁ i, (P i).M S
  res h := DirectSum.lmap fun i => (P i).res h
  res_id S h x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change DirectSum.lmap _ _ = _
      simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (P i).res_id]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  res_comp h h' x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change DirectSum.lmap _ (DirectSum.lmap _ _) = DirectSum.lmap _ _
      simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (P i).res_comp]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable (P : I → PM.{1} K ι)

def pr (i : I) (m : ℕ) : (sumPM P).cech.X m →ₗ[K] (P i).cech.X m :=
  LinearMap.pi fun t => (DirectSum.component K I (fun j => (P j).M (ent t)) i) ∘ₗ LinearMap.proj t

def inc (i : I) (m : ℕ) : (P i).cech.X m →ₗ[K] (sumPM P).cech.X m :=
  LinearMap.pi fun t => (DirectSum.lof K I (fun j => (P j).M (ent t)) i) ∘ₗ LinearMap.proj t

theorem component_res {S T : Finset ι} (h : S ⊆ T) (i : I) (x : (sumPM P).M S) :
    DirectSum.component K I (fun j => (P j).M T) i ((sumPM P).res h x) =
      (P i).res h (DirectSum.component K I (fun j => (P j).M S) i x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j x =>
    change DirectSum.component K I _ i (DirectSum.lmap _ _) = _
    rw [← DirectSum.lof_eq_of K, DirectSum.lmap_lof]
    by_cases e : j = i
    · subst e
      simp
    · simp [DirectSum.component.of, e]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem res_lof {S T : Finset ι} (h : S ⊆ T) (i : I) (x : (P i).M S) :
    (sumPM P).res h (DirectSum.lof K I (fun j => (P j).M S) i x) =
      DirectSum.lof K I (fun j => (P j).M T) i ((P i).res h x) := DirectSum.lmap_lof _ _ _

theorem pr_d (i : I) (m : ℕ) (z : (sumPM P).cech.X m) :
    pr P i (m + 1) ((sumPM P).cech.d m z) = (P i).cech.d m (pr P i m z) := by

  rw [Cos.d_apply, Cos.d_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul]
  congr 1

theorem inc_d (i : I) (m : ℕ) (y : (P i).cech.X m) :
    inc P i (m + 1) ((P i).cech.d m y) = (sumPM P).cech.d m (inc P i m y) := by

  rw [Cos.d_apply, Cos.d_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul]
  congr 1
  funext t
  exact (res_lof P _ i _).symm

theorem cochain_ext {m : ℕ} {z : (sumPM P).cech.X m} (h : ∀ i, pr P i m z = 0) : z = 0 := by
  funext t
  refine DFinsupp.ext fun i => ?_
  exact congrFun (h i) t

theorem pr_aug (i : I) (x : (sumPM P).M ∅) :
    pr P i 0 ((sumPM P).aug x) = (P i).aug (DirectSum.component K I (fun j => (P j).M ∅) i x) := by
  funext t
  exact component_res P _ i _

theorem aug_lof (i : I) (x : (P i).M ∅) :
    (sumPM P).aug (DirectSum.lof K I (fun j => (P j).M ∅) i x) = inc P i 0 ((P i).aug x) := by
  funext t
  exact res_lof P _ i _

theorem pr_inc_self (i : I) (m : ℕ) (y : (P i).cech.X m) : pr P i m (inc P i m y) = y := by
  funext t
  exact DirectSum.component.lof_self (M := fun j => (P j).M (ent t)) K i (y t)

theorem pr_inc_ne {i j : I} (e : j ≠ i) (m : ℕ) (y : (P j).cech.X m) : pr P i m (inc P j m y) = 0 := by
  funext t
  change DirectSum.component K I (fun j => (P j).M (ent t)) i (DirectSum.lof K I (fun j => (P j).M (ent t)) j (y t)) = 0
  rw [DirectSum.component.of, dite_eq_right e]

open Classical in
theorem decomp [Fintype ι] {m : ℕ} (z : (sumPM P).cech.X m) :
    ∃ F : Finset I, z = ∑ i ∈ F, inc P i m (pr P i m z) := by
  refine ⟨Finset.univ.biUnion fun t => DFinsupp.support (z t), sub_eq_zero.1 (cochain_ext P fun i => ?_)⟩

  rw [map_sub, map_sum]
  by_cases hi : i ∈ Finset.univ.biUnion fun t => DFinsupp.support (z t)
  · rw [Finset.sum_eq_single_of_mem i hi (fun j _ e => pr_inc_ne P e _ _), pr_inc_self, sub_self]
  · have hz : pr P i m z = 0 := by
      funext t
      by_contra hne
      exact hi (Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _, DFinsupp.mem_support_iff.2 hne⟩)
    rw [hz, Finset.sum_eq_zero (fun j hj => pr_inc_ne P (ne_of_mem_of_not_mem hj hi) _ _), sub_zero]

theorem sum_ex [Fintype ι] (h : ∀ i, (P i).Ex) : (sumPM P).Ex := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun m y hy => ?_⟩
  · refine cochain_ext P fun i => ?_
    change pr P i 1 ((sumPM P).cech.d 0 ((sumPM P).aug x)) = 0
    rw [pr_d, pr_aug]
    exact (h i).1 _
  · rw [one_smul]
    refine DFinsupp.ext fun i => ?_
    have h0 : (P i).aug (DirectSum.component K I (fun j => (P j).M ∅) i x) = 0 := by
      rw [← pr_aug, hx, map_zero]
    have h1 := (h i).2.1 _ h0
    rw [one_smul] at h1
    exact h1
  · obtain ⟨F, hF⟩ := decomp P y
    have hc : ∀ i, (P i).cech.d 0 (pr P i 0 y) = 0 := fun i => by
      rw [← pr_d]
      exact (congrArg (pr P i 1) hy).trans (map_zero _)
    choose c hc' using fun i => (h i).2.2.1 _ (hc i)
    refine ⟨∑ i ∈ F, DirectSum.lof K I (fun j => (P j).M ∅) i (c i), ?_⟩

    rw [one_smul, map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hF.symm
    rw [aug_lof, hc', one_smul]
  · obtain ⟨F, hF⟩ := decomp P y
    have hc : ∀ i, (P i).cech.d (m + 1) (pr P i (m + 1) y) = 0 := fun i => by
      rw [← pr_d]
      exact (congrArg (pr P i (m + 2)) hy).trans (map_zero _)
    choose c hc' using fun i => (h i).2.2.2 m _ (hc i)
    refine ⟨∑ i ∈ F, inc P i m (c i), ?_⟩
    rw [one_smul]
    change (sumPM P).cech.d m _ = y

    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hF.symm
    rw [← inc_d]
    have h2 := hc' i
    rw [one_smul] at h2
    exact congrArg (inc P i (m + 1)) h2

theorem sum_desc {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] {I : Type 1} [DecidableEq I]
    (A : I → Sy.{1} K ι) (h : ∀ i, (A i).Desc) : (sumSy A).Desc :=
  fun n => sum_ex (fun i => (A i).term n) fun i => h i n

end GlobalTheory.CompanionTheory.KunGlue.SumDesc
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

theorem _root_.GlobalTheory.T.forms_to_cech_smul :
    type_of% @GlobalTheory.CompanionTheory.OmBridge.formToCO_smul :=
  @GlobalTheory.CompanionTheory.OmBridge.formToCO_smul
end
