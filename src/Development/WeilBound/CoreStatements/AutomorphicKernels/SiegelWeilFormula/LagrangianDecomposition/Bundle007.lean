module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle003
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle005
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.Bundle001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.DiagonalColumnInclusion.IncMDiagCols
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ExistsSchwartzOneCpt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelPf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle006
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelC
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SubSplitOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle072
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSB
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem modelEx_wired (hD : SDarb) (hP : PartCharInv) (hC : ChartFacts) (hG : SiegelSmall) (hS : SmallS) : ModelEx :=
  modelEx_of hD PositivityTheory.SiegelWeilFormula.Ldexa.sEv bigT sliceFacts (opBox_of hP sliceFacts) (subSplit_of sliceFacts) hC hG hS

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F : Type} [Field F] [NumberField F]

theorem evalZero_mem_adelicSchwartzAdmittedForms (κ : Type) [Fintype κ] : ev0 (F := F) κ ∈ (adeleClass F).adm κ := by
  have e : ev0 (F := F) κ = GlobalTheory.MixUniq.ev0 κ := LinearMap.ext fun _ => rfl
  rw [e]
  exact GlobalTheory.MixUniq.adelicCoordinatesEvalZeroForm_mem_admissible κ

theorem schr_zero_fst {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (v : κ → AF F) (Ψ : (κ → AF F) → ℂ) :
    schr ψ (0, v) Ψ = fun x => ψ (x ⬝ᵥ v) * Ψ x := by
  funext x
  simp [schr]

theorem siegelSmall_of (hF : SliceFacts) (hAC : AdaptedChar) : SiegelSmall := by
  intro F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' om1 hsp1 hsr1 φ₀ hφ₀ h0 om' hbox
  intro l hl hinv p t hpt φ hφ
  change G2 σ Y at p
  have hψ : IsStd d.B.ψ := d.ok.good.std

  have hchar : ∀ (y : Fin d.m × Fin n × Fin 2 → AF F), ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2),
      l (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l φ := by
    intro y φ hφ
    obtain ⟨z, hz⟩ := (hAC F E σ d.m n d.bs d.A Y b dd' had' hb).2 y
    have := hinv z φ hφ
    rw [Darboux.rho, hz, schr_zero_fst] at this
    exact this
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F d.B.ψ hψ (Fin d.m × Fin n × Fin 2) l hl hchar

  have hbm : boxFun φ φ₀ ∈ schA F (K1 d.m n) := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ hφ φ₀ hφ₀
  have hb1 := hbox p φ hφ
  have hm1 : boxFun (om' p φ) φ₀ ∈ schA F (K1 d.m n) := hb1 ▸ hsp1.pres (j p) _ hbm
  have hmem : om' p φ ∈ schA F (Fin d.m × Fin n × Fin 2) := by
    have := (hF F _ _).1 _ hm1
    rwa [slice0_box_one _ h0] at this
  change l (om' p φ) = (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    (((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t))) : ℝ) ^
      ((Fintype.card (Fin d.m) : ℝ) / 2) : ℝ) : ℂ) * l φ
  rw [hc _ hmem, hc _ hφ]

  have hv : om' p φ 0 = ev0 (K1 d.m n) (om1 (j p) (boxFun φ φ₀)) := by
    rw [hb1]
    simp [ev0, boxFun, h0]

  obtain ⟨t', ht', hdet⟩ := jPar d h hb hj p t hpt
  have hkill : ∀ (z : Matrix (Fin d.m) (Fin d.n) (AE F E)), ∀ Ψ ∈ schA F (K1 d.m n),
      ev0 (K1 d.m n) ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).rho d.B.ψ
        (z * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ) Ψ) = ev0 (K1 d.m n) Ψ := by
    intro z Ψ _
    have h1 := (hAC F E σ d.m d.n d.bs d.A d.Y d.b dd0 had0 d.ok.frame).1 z
    rw [Darboux.rho, GlobalTheory.TowU.reindexD_e, h1]
    simp [ev0, schr]
  have key := hsr1 (ev0 (K1 d.m n)) (evalZero_mem_adelicSchwartzAdmittedForms _) hkill (j p) t' ht' (boxFun φ φ₀) hbm
  rw [hdet] at key
  change ev0 (K1 d.m n) (om1 (j p) (boxFun φ φ₀)) =
    (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    (((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t))) : ℝ) ^
      ((Fintype.card (Fin d.m) : ℝ) / 2) : ℝ) : ℂ) * ev0 (K1 d.m n) (boxFun φ φ₀) at key
  simp [ev0, boxFun, h0] at key
  rw [hv]
  simpa [ev0, mul_assoc, mul_comm, mul_left_comm] using congrArg (fun z : ℂ => c * z) key

end PositivityTheory.SiegelWeilFormula.Ald

end
end

section

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.ModuLR GlobalTheory.GaugeEx GlobalTheory.JacSubst

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem haarLc : HaarLc := by
  intro F E _ _ _ _ _ σ hcm m J hJ bs g μ hμ f
  letI mA : MeasurableSpace (Fin m × Fin 2 → AF F) := borel _
  haveI : BorelSpace (Fin m × Fin 2 → AF F) := ⟨rfl⟩
  letI mV : MeasurableSpace (Fin m → AE F E) := borel _
  haveI : BorelSpace (Fin m → AE F E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  let e := coordCE F E (Module.finBasis F E)
  haveI : LocallyCompactSpace (AE F E) := e.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin m) (Fin 1) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin m → Fin 1 → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin m) (Fin 1) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin 1 → AE F E))
  letI : MeasurableSpace (Matrix (Fin m) (Fin 1) (AE F E)) := borel _
  haveI : BorelSpace (Matrix (Fin m) (Fin 1) (AE F E)) := ⟨rfl⟩
  set t : GL (Fin m) (AE F E) := (g : GL (Fin m) (AE F E)) with ht
  have hdt : IsUnit (t : Matrix (Fin m) (Fin m) (AE F E)).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
  let φ := mulVecCE (t : Matrix (Fin m) (Fin m) (AE F E)) hdt
  obtain ⟨κ, _, _, Λ, hΛ, hdet, hχ⟩ :=
    @exists_matrix_restrictScalars_lrCE F E _ _ _ _ _ m (1 : ℕ) _ _ _ _ t (1 : GL (Fin 1) (AE F E))

  have hc : addEquivAddHaarChar φ = 1 := by
    have h1 : addEquivAddHaarChar φ = addEquivAddHaarChar (lrCE t (1 : GL (Fin 1) (AE F E))) := by
      rw [← addEquivAddHaarChar_transport (colCE (AE F E) m) φ]
      congr 1
      ext M i j
      rw [Fin.fin_one_eq_zero j]
      show ((t : Matrix (Fin m) (Fin m) (AE F E)) *ᵥ (fun k => M k 0)) i =
        ((t : Matrix (Fin m) (Fin m) (AE F E)) * M * ((1 : GL (Fin 1) (AE F E)) : Matrix (Fin 1) (Fin 1) (AE F E))) i 0
      rw [Units.val_one, Matrix.mul_one]
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    have hu : hΛ.unit = Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t) := by
      ext
      simp only [IsUnit.unit_spec, hdet, Units.coe_map, MonoidHom.coe_coe, map_one, one_pow, mul_one, pow_one]
    rw [h1, hχ, chi_AF_det, hu, ht, norm_det_unitary hcm hJ g, map_one]

  have hV : ∀ (ν : Measure (Fin m → AE F E)), ν.IsAddHaarMeasure → ν.map φ = ν := by
    intro ν hν
    haveI : ν.Regular := inferInstance
    have key := addEquivAddHaarChar_smul_map ν φ
    rwa [hc, one_smul] at key

  let cm : (Fin m × Fin 2 → AF F) ≃ᵐ (Fin m → AE F E) := (colv m bs).toHomeomorph.toMeasurableEquiv
  let pm : (Fin m → AE F E) ≃ᵐ (Fin m → AE F E) := φ.toHomeomorph.toMeasurableEquiv
  haveI : μ.IsAddHaarMeasure := hμ
  have hH : (μ.map cm).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ (colv m bs)
  have hmap : (μ.map cm).map pm = μ.map cm := hV _ hH
  have e1 : ∀ x, Lc bs (mat g) x = cm.symm (pm (cm x)) := fun x => by rw [Lc_eq_colv]; rfl
  calc ∫⁻ x, f (Lc bs (mat g) x) ∂μ = ∫⁻ x, (fun y => f (cm.symm (pm y))) (cm x) ∂μ := by simp_rw [e1]
    _ = ∫⁻ y, f (cm.symm (pm y)) ∂(μ.map cm) := (lintegral_map_equiv (fun y => f (cm.symm (pm y))) cm).symm
    _ = ∫⁻ y, f (cm.symm y) ∂((μ.map cm).map pm) := (lintegral_map_equiv (fun y => f (cm.symm y)) pm).symm
    _ = ∫⁻ y, f (cm.symm y) ∂(μ.map cm) := by rw [hmap]
    _ = ∫⁻ x, f (cm.symm (cm x)) ∂μ := lintegral_map_equiv (fun y => f (cm.symm y)) cm
    _ = ∫⁻ x, f x ∂μ := by simp

end PositivityTheory.SiegelWeilFormula.Ald

end
end
