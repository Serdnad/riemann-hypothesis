module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle046
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle053
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle055
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingGrp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle040
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.AdelicHomeomorphisms.IsTopologicalGroupG2
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.CountableRationalPointsDoubled
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.BddOfPer
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle054
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle039
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle005
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.BlockTriangularFrames.SiegelParabolicEqStabiliserCols
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.UnitaryGroupInverseFormula
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitW
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle032
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle044
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle027
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle045
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaEps
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fockMem_k : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k := by
  intro F E _ _ _ _ _ σ d R
  exact ⟨_root_.PositivityTheory.SiegelWeilFormula.KFock.fock_le_k d R, fun w Ψ hΨ => ⟨fun P => _root_.PositivityTheory.SiegelWeilFormula.KFock.away_tens_k R w Ψ hΨ P, _root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ⟩, fun w f hf => _root_.PositivityTheory.SiegelWeilFormula.KFock.fock_dec_k R w f hf⟩
theorem T_sub_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Φ' : d.Fn) : d.T (Φ - Φ') = d.T Φ - d.T Φ' := by
  have h := _root_.PositivityTheory.SiegelWeilFormula.KFock.T_add_k d (Φ - Φ') Φ'
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm
theorem T_inj_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) (e : d.T Φ = d.T Φ') : Φ = Φ' :=
  sub_eq_zero.mp ((hB F E σ d).2.2 _ (d.sch.sub_mem h h') (by rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.T_sub_k, e, sub_self]))
theorem linLift_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {V : Type} [AddCommGroup V] [Module ℂ V] (t : V →ₗ[ℂ] (Mx F E d.m d.n → ℂ))
    (ht : ∀ v, t v ∈ d.schM) : ∃ φ : V →ₗ[ℂ] d.Fn, ∀ v, φ v ∈ d.sch ∧ d.T (φ v) = t v := by
  choose φ0 hφ0 using fun v => (hB F E σ d).2.1 (t v) (ht v)
  refine ⟨{ toFun := φ0, map_add' := fun v v' => ?_, map_smul' := fun a v => ?_ }, fun v => hφ0 v⟩
  · refine _root_.PositivityTheory.SiegelWeilFormula.KFock.T_inj_k hB d (hφ0 (v + v')).1 (d.sch.add_mem (hφ0 v).1 (hφ0 v').1) ?_
    rw [_root_.PositivityTheory.SiegelWeilFormula.KFock.T_add_k, (hφ0 _).2, (hφ0 _).2, (hφ0 _).2, map_add (f := _)]
  · refine _root_.PositivityTheory.SiegelWeilFormula.KFock.T_inj_k hB d (hφ0 (a • v)).1 (d.sch.smul_mem a (hφ0 v).1) ?_
    rw [RingHom.id_apply, _root_.PositivityTheory.SiegelWeilFormula.KFock.T_smul_k, (hφ0 _).2, (hφ0 _).2, map_smul]
def tensP_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : PX d.m d.n →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun P := R.tens w (fP P) Ψ
  map_add' P Q := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, fP_add, Pi.add_apply, add_mul]
  map_smul' a P := by
    funext X
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, fP_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
theorem liftEx_of_k : _root_.PositivityTheory.SiegelWeilFormula.TBij_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k := by
  intro hB hF F E _ _ _ _ _ σ d R w Ψ hΨ
  obtain ⟨φ, hφ⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.linLift_k hB d (_root_.PositivityTheory.SiegelWeilFormula.KFock.tensP_k R w Ψ) fun P => (hF F E σ d R).1 (((hF F E σ d R).2.1 w Ψ hΨ).1 P)
  exact ⟨φ, hφ⟩
theorem liftEx_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k := _root_.PositivityTheory.SiegelWeilFormula.KFock.liftEx_of_k hB _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k
theorem liftSw1_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (hf : IsSw f)
    (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) : ∃ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ :=
  (hB F E σ d).2.1 _ (_root_.PositivityTheory.SiegelWeilFormula.KFock.tens_mem_k d R w f hf Ψ hΨ)
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.isW_eps (w : InfinitePlace F) {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ε = R.ε := by
  have hmem : (mat2 w₀)ᵀ * dbl (incM F d.Y.J) * (mat2 w₀).map (cA σ) = dbl (incM F d.Y.J) := w₀.2
  have hmat : mat2 w₀ = incM F d.b.1 * inFrame d.b w₀ * incM F (d.b⁻¹).1 := by
    simp only [inFrame, ← Matrix.mul_assoc]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.one_mul, Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.mul_one]
  have hc := congrArg (d.cw w) hmem
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, hmat,
    _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM h w] at hc
  set P := d.b.1.map (d.B.emb w).1
  set Pi := (d.b⁻¹).1.map (d.B.emb w).1
  set D := (dbl d.Y.J).map (d.B.emb w).1
  set Wc := wM d.n ((ε : ℤ) : ℂ)
  have hPiP : Pi * P = 1 := by
    simp only [Pi, P]
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ := _root_.PositivityTheory.SiegelWeilFormula.Krd.hQ_w_k d R.hε w
  apply eps_of_unit d.ok.hn ε R.ε
  calc Wcᵀ * Krd.Qc d.n R.ε * Wc.map star
      = (Pi * P)ᵀ * Wcᵀ * (Pᵀ * D * P.map star) * Wc.map star * (Pi * P).map star := by
        rw [hPiP, hQ, Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]
    _ = Pᵀ * ((P * Wc * Pi)ᵀ * D * (P * Wc * Pi).map star) * P.map star := by
        simp only [Matrix.transpose_mul, Krd.mapStar_mul, Matrix.mul_assoc]
    _ = Krd.Qc d.n R.ε := by rw [hc, hQ]
end RD
end PositivityTheory.SiegelWeilFormula
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
theorem a_dil_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) (h : d.G) : d.a (R.ι w y * h) = Real.exp (2 * τ) * d.a h ∧ 0 ≤ d.a h := by
  haveI := d.cm.1
  have hf := _root_.PositivityTheory.SiegelWeilFormula.AStep.inFrame_dil'_k R w i₀ τ y hy
  have h21 : (inFrame d.b (R.ι w y)).toBlocks₂₁ = 0 := by rw [hf, Matrix.toBlocks_fromBlocks₂₁]
  obtain ⟨t, ht, hdet⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.isPar_of_frame_k d (R.ι w y) h21
  have hdetU : Matrix.GeneralLinearGroup.det t = Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ) := by
    rw [← det_dilT d.cm w i₀ τ]
    apply Units.ext
    rw [hdet, hf, Matrix.toBlocks_fromBlocks₁₁]
    rfl
  refine ⟨?_, ?_⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.a_mul_par_k d ht h, hdetU, absE_adrU d.cm w τ]
  · obtain ⟨p, tp, hp, k, hk, rfl⟩ := d.ok.hgt.iwa h
    rw [d.ok.hgt.val p tp hp k hk]
    exact NNReal.coe_nonneg _
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KSing
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fourierStep_k (hCE : _root_.PositivityTheory.SiegelWeilFormula.CoefEx_k) (hFZ : _root_.PositivityTheory.SiegelWeilFormula.FourierZero_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
    (f : d.G → ℂ) (hf : Continuous f) (hinv : ∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g)
    (hL : ∀ L ∈ d.lamSet, L f = 0) (ψ₀ : (Fin d.n → Fin d.n → ℝ) → ℂ) (hψ : IsSingTest ψ₀)
    (nr : (Fin d.n → Fin d.n → ℝ) → GR d.n) (hnr : ∀ x, mR (nr x) = nU (herm x)) :
    ∀ z, ∫ x, f (R.ι w (nr x) * z) * ψ₀ x = 0 := by
  obtain ⟨-, -, hG, hLC, -, hSC⟩ := hAux F E σ d
  haveI := hG
  haveI := hLC
  haveI := hSC
  obtain ⟨nb, lam, 𝓖, hCD⟩ := hCE F E σ d
  obtain ⟨β, hβc, hβ⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSing.nbw_k d R w hCD.1 nr hnr
  have hnrc := cont_nr nr hnr
  have hφc : Continuous fun y : d.G => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x := by
    have hc : Continuous (Function.uncurry fun (y : d.G) (x : Fin d.n → Fin d.n → ℝ) => f (R.ι w (nr x) * y) * ψ₀ x) :=
      (hf.comp (((R.cont w).comp (hnrc.comp continuous_snd)).mul continuous_fst)).mul (hψ.1.comp continuous_snd)
    have h1 := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Fin d.n → Fin d.n → ℝ))) hc
      hψ.2.1.isCompact
    refine h1.congr fun y => ?_
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hφinv : ∀ β₀ ∈ nF σ d.Y d.b, ∀ g, (fun y : d.G => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) (nb β₀ * g) =
      (fun y : d.G => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) g := by
    intro β₀ hβ₀ g
    simp only
    congr 1
    funext x
    rw [hβ x, ← mul_assoc, ← _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hCD.1, add_comm, _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hCD.1, mul_assoc, hinv _ (_root_.PositivityTheory.SiegelWeilFormula.KSing.nb_rat_k d hCD.1 hβ₀)]
  have hφco : ∀ T g, fc d.B.ψ d.b nb lam 𝓖 (fun y : d.G => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) T g = 0 := by
    intro T g
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.fc_avg_k d R w hG hCD f hf hinv ψ₀ hψ.1 hψ.2.1 nr hnr β hβc hβ T g]
    by_cases hT : T.1.1.det = 0
    · obtain ⟨β', hβ'h, hβ'd, hβ'e⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSing.charW_k d R w hCD.1 nr hnr β hβ T
      simp_rw [hβ'e]
      rw [hψ.2.2 β' hβ'h (hβ'd hT), mul_zero]
    · have h0 := hL (fun f => fc d.B.ψ d.b nb lam 𝓖 f T g) ⟨nb, lam, 𝓖, T, g, hCD, hT, rfl⟩
      rw [show fc d.B.ψ d.b nb lam 𝓖 f T g = 0 from h0, zero_mul]
  intro z
  exact congrFun (hFZ F E σ d nb lam 𝓖 hCD _ hφc hφinv hφco) z
end PositivityTheory.SiegelWeilFormula.KSing
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KSplitW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem cw_iota_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) :
    d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by
  have h0 := Krd.zeta_ne R.hζ
  have e := congrArg (fun M => dZ d.n R.ζ⁻¹ * M) (R.at_w w y)
  simp only [← Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.one_mul] at e
  exact e
theorem law_w_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (x : d.G) :
    (d.cw w (inFrame d.b x))ᵀ * Krd.Qc d.n R.ε * (d.cw w (inFrame d.b x)).map star = Krd.Qc d.n R.ε := by
  have hx : (mat2 x)ᵀ * dbl (incM F d.Y.J) * (mat2 x).map (cA σ) = dbl (incM F d.Y.J) := x.2
  have hw := congrArg (d.cw w) hx
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k] at hw
  have hQ := _root_.PositivityTheory.SiegelWeilFormula.Krd.hQ_w_k d R.hε w
  set b := d.b.1.map (d.B.emb w).1 with hb
  set bi := (d.b⁻¹).1.map (d.B.emb w).1 with hbi
  set D := (dbl d.Y.J).map (d.B.emb w).1 with hD
  have hbbi : b * bi = 1 := by
    rw [hb, hbi, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hbib : bi * b = 1 := by
    rw [hb, hbi, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQ' : biᵀ * Krd.Qc d.n R.ε * bi.map star = D := by
    rw [← hQ]
    calc biᵀ * (bᵀ * D * b.map star) * bi.map star = (b * bi)ᵀ * D * (b * bi).map star := by
          rw [Matrix.transpose_mul, Krd.mapStar_mul]; simp only [Matrix.mul_assoc]
      _ = D := by rw [hbbi, Matrix.transpose_one, Krd.mapStar_one, Matrix.one_mul, Matrix.mul_one]
  have hZ : d.cw w (inFrame d.b x) = bi * d.cw w (mat2 x) * b := by
    simp only [inFrame, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k, hb, hbi]
  rw [hZ]
  exact Krd.conj_unit bi b (d.cw w (mat2 x)) _ _ hbib hQ' hw
theorem cw_inFrame_one_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) : d.cw w (inFrame d.b (1 : d.G)) = 1 := by
  rw [SiegelEisensteinSeries.Grp.inFrame_one, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_one_k]
theorem decompW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (g : d.G) :
    ∃ (x : d.G) (y : GR d.n), g = x * R.ι w y ∧ d.cw w (inFrame d.b x) = 1 := by
  have h0 := Krd.zeta_ne R.hζ
  set Zw := d.cw w (inFrame d.b g) with hZw
  let y : GR d.n := Krd.DM.mkG (dZ d.n R.ζ * Zw * dZ d.n R.ζ⁻¹) (Krd.inG_conj R.hζ Zw (_root_.PositivityTheory.SiegelWeilFormula.KSplitW.law_w_k d R w g))
  refine ⟨g * (R.ι w y)⁻¹, y, by rw [inv_mul_cancel_right], ?_⟩
  have hy : d.cw w (inFrame d.b (R.ι w y)) = Zw := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSplitW.cw_iota_k, Krd.DM.mR_mkG]
    simp only [← Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.one_mul]
    rw [Matrix.mul_assoc, Krd.dZ_inv_mul h0, Matrix.mul_one]
  have hinv : Zw * d.cw w (inFrame d.b g⁻¹) = 1 := by
    rw [hZw, ← _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, ← _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d, mul_inv_cancel, _root_.PositivityTheory.SiegelWeilFormula.KSplitW.cw_inFrame_one_k]
  have e : d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) * Zw = Zw := by
    have e0 : d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) * d.cw w (inFrame d.b (R.ι w y)) = Zw := by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, ← _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d, inv_mul_cancel_right]
    rwa [hy] at e0
  calc d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) = d.cw w (inFrame d.b (g * (R.ι w y)⁻¹)) * (Zw * d.cw w (inFrame d.b g⁻¹)) := by
        rw [hinv, Matrix.mul_one]
    _ = 1 := by rw [← Matrix.mul_assoc, e, hinv]
theorem commW_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (x : d.G) (hx : d.cw w (inFrame d.b x) = 1) (y : GR d.n) :
    x * R.ι w y = R.ι w y * x := by
  apply _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d]
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k]
    by_cases h : w' = w
    · subst h; rw [hx, Matrix.one_mul, Matrix.mul_one]
    · rw [R.off_w w w' y h, Matrix.one_mul, Matrix.mul_one]
  · rw [Krd.fin_mul, Krd.fin_mul, R.off_f]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
theorem finOne_one_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (i j : Fin d.n ⊕ Fin d.n) :
    finOne F • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) i j ∈ intHat F E := by
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq]; exact finOne_mem
  · rw [Matrix.one_apply_ne h, smul_zero]; exact zero_mem _
theorem iota_mem_K_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) (hy : InK (mR y)) : R.ι w y ∈ d.K := by
  have h0 := Krd.zeta_ne R.hζ
  rw [d.ok.stdK]
  refine ⟨fun w' => ?_, fun k' hk' i j => ?_⟩
  · change d.cw w' (inFrame d.b (R.ι w y)) * (d.cw w' (inFrame d.b (R.ι w y)))ᴴ = 1
    by_cases h : w' = w
    · subst h
      have hM : mR y * (mR y)ᴴ = 1 := mul_eq_one_comm.1 hy.2
      rw [_root_.PositivityTheory.SiegelWeilFormula.KSplitW.cw_iota_k, dZ_inv_ct R.hζ, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      have hD : dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ = 1 := by rw [← dZ_inv_ct R.hζ, Krd.dZ_mul_inv h0]
      calc (dZ d.n R.ζ)ᴴ * mR y * dZ d.n R.ζ * ((dZ d.n R.ζ)ᴴ * ((mR y)ᴴ * dZ d.n R.ζ))
          = (dZ d.n R.ζ)ᴴ * (mR y * (dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ) * (mR y)ᴴ) * dZ d.n R.ζ := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hD, Matrix.mul_one, hM, Matrix.mul_one, ← dZ_inv_ct R.hζ, Krd.dZ_inv_mul h0]
    · rw [R.off_w w w' y h, Matrix.conjTranspose_one, Matrix.mul_one]
  · have hk'' : ∃ z, k' = R.ι w z := by
      rcases hk' with rfl | hk'
      · exact ⟨y, rfl⟩
      · rw [Set.mem_singleton_iff] at hk'
        exact ⟨y⁻¹, by rw [hk', map_inv]⟩
    obtain ⟨z, rfl⟩ := hk''
    have e := congrFun (congrFun (R.off_f w z) i) j
    rw [Matrix.smul_apply, Matrix.smul_apply] at e
    rw [e]
    exact _root_.PositivityTheory.SiegelWeilFormula.KSplitW.finOne_one_mem_k d i j
theorem kSplit_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : d.G) (hk : k ∈ d.K) :
    ∃ y : GR d.n, (R.ι w y)⁻¹ * k ∈ d.K ∧ d.cw w (inFrame d.b ((R.ι w y)⁻¹ * k)) = 1 := by
  have h0 := Krd.zeta_ne R.hζ
  obtain ⟨x, y, hxy, hx⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplitW.decompW_k d R w k
  have hkx : (R.ι w y)⁻¹ * k = x := by rw [hxy, _root_.PositivityTheory.SiegelWeilFormula.KSplitW.commW_k d R w x hx y, inv_mul_cancel_left]
  have hU : d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1 := ((d.ok.stdK k).1 hk).1 w
  have hkw : d.cw w (inFrame d.b k) = (dZ d.n R.ζ)ᴴ * mR y * dZ d.n R.ζ := by
    rw [hxy, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, hx, Matrix.one_mul, _root_.PositivityTheory.SiegelWeilFormula.KSplitW.cw_iota_k, dZ_inv_ct R.hζ]
  have hD : dZ d.n R.ζ * (dZ d.n R.ζ)ᴴ = 1 := by rw [← dZ_inv_ct R.hζ, Krd.dZ_mul_inv h0]
  have hD' : (dZ d.n R.ζ)ᴴ * dZ d.n R.ζ = 1 := by rw [← dZ_inv_ct R.hζ, Krd.dZ_inv_mul h0]
  have hM : mR y = dZ d.n R.ζ * d.cw w (inFrame d.b k) * (dZ d.n R.ζ)ᴴ := by
    rw [hkw]; simp only [← Matrix.mul_assoc]; rw [hD, Matrix.one_mul, Matrix.mul_assoc, hD, Matrix.mul_one]
  have hU' : (d.cw w (inFrame d.b k))ᴴ * d.cw w (inFrame d.b k) = 1 := mul_eq_one_comm.1 hU
  have hK : InK (mR y) := by
    refine ⟨y.2, ?_⟩
    rw [hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc dZ d.n R.ζ * ((d.cw w (inFrame d.b k))ᴴ * (dZ d.n R.ζ)ᴴ) * (dZ d.n R.ζ * d.cw w (inFrame d.b k) * (dZ d.n R.ζ)ᴴ)
        = dZ d.n R.ζ * ((d.cw w (inFrame d.b k))ᴴ * ((dZ d.n R.ζ)ᴴ * dZ d.n R.ζ) * d.cw w (inFrame d.b k)) *
          (dZ d.n R.ζ)ᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hD', Matrix.mul_one, hU', Matrix.mul_one, hD]
  refine ⟨y, ?_, by rw [hkx]; exact hx⟩
  exact (d.K).mul_mem ((d.K).inv_mem (_root_.PositivityTheory.SiegelWeilFormula.KSplitW.iota_mem_K_k d R w y hK)) hk
end PositivityTheory.SiegelWeilFormula.KSplitW
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem goodAwayEx_k : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k := by
  intro F E _ _ _ _ _ σ d R w
  let g := (GlobalTheory.RealLift.intPts F (Fin d.m × Fin d.n × Fin 2)).indicator (1 : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ)
  have hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  let Ψ : Mx F E d.m d.n → ℂ := fun X =>
    (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' X)) * g fun k => (d.crd X k).2
  have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
  refine ⟨Ψ, _root_.PositivityTheory.SiegelWeilFormula.KFock.away_inv_k R w Ψ hΨ, fun h0 => ?_, fun f hf => _root_.PositivityTheory.SiegelWeilFormula.KFock.tens_mem_k d R w f hf Ψ hΨ⟩
  have h1 := congrFun h0 0
  have hc : (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 0 := by
    funext k
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd
    rw [Matrix.zero_apply, map_zero, Finsupp.zero_apply]
    rfl
  have hg0 : g (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 1 := by
    rw [hc]
    exact Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts _
  have hp : (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' 0)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w' _ => fP_one_ne _
  exact hp (by simpa [Ψ, hg0] using h1)
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
def SiegelSmall_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G) (ε : ℤˣ), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y → IsFrame2 σ Y b →
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j →
  ∀ (dd0 : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))) (Fin d.m × Fin d.n × Fin 2))
    (dd' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) (Fin d.m × Fin n × Fin 2)),
    IsAdapted d.bs d.A d.Y d.b dd0 → IsAdapted d.bs d.A Y b dd' →
  ∀ (om1 : d.G →* Module.End ℂ ((K1 d.m n → AF F) → ℂ)),
    IsSplitting (adeleClass F) d.B.ψ (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm) (actB (cA σ)) om1 →
    SiegelRule (cA σ) (adeleClass F) d.B.ψ (-1) (incM F d.A.J) (dbl (incM F d.Y.J))
      (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm) d.χ (diagCols (Fin d.n)) om1 →
  ∀ φ₀ ∈ schA F (Fin d.m × Fin 2), φ₀ 0 = 1 →
  ∀ (om' : G2 σ Y →* Module.End ℂ ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ)),
    (∀ g, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), om1 (j g) (boxFun φ' φ₀) = boxFun (om' g φ') φ₀) →
    SiegelRule (cA σ) (adeleClass F) d.B.ψ (-1) (incM F d.A.J) (dbl (incM F Y.J)) dd' d.χ (diagCols (Fin n)) om'
def SmallS_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (n : ℕ) (h : n + 1 = d.n) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E)
  (j : G2 σ Y →* d.G) (ε : ℤˣ), 1 ≤ n → _root_.PositivityTheory.SiegelWeilFormula.Ald.SignOK_k d Y → IsFrame2 σ Y b →
  d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = jeps d.n ε → b.1ᵀ * dbl Y.J * b.1.map σ = jeps n ε → _root_.PositivityTheory.SiegelWeilFormula.Ald.IsJ_k d h b j →
  ∀ (dd0 : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J))) (Fin d.m × Fin d.n × Fin 2))
    (dd' : Darboux (symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F Y.J))) (Fin d.m × Fin n × Fin 2)),
    IsAdapted d.bs d.A d.Y d.b dd0 → IsAdapted d.bs d.A Y b dd' →
  ∀ (S1 : ((d.κ → AF F) → ℂ) →ₗ[ℂ] ((K1 d.m n → AF F) → ℂ)) (S1' : ((K1 d.m n → AF F) → ℂ) →ₗ[ℂ] ((d.κ → AF F) → ℂ))
    (C : ℂ), C ≠ 0 →
    GlobalTheory.TowU.IsOp d.B.ψ (fun w => (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).e (d.dd.e.symm w)) S1 S1' →
    (∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S1 Φ (crdB d.bs X ∘ eK d.m h)) →
  ∃ S' : UA σ d.A.J →* Module.End ℂ ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ),
    IsUSplitting (adeleClass F) d.B.ψ dd' (fun (g : UA σ d.A.J) x => mat g * x) S' ∧
    ∀ g, ∀ Φ ∈ schA F (Fin d.m × Fin n × Fin 2), ev0 _ (S' g Φ) = ev0 _ Φ
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem eps_eq_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 := by
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  obtain ⟨ε', hε'⟩ := L.ok.frame.1
  have s := _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_sign_k d ε hε
  have s' := _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_sign_k L.sd ε' hε'
  refine ⟨ε, hε, ?_⟩
  suffices e : ε' = ε by rw [← e]; exact hε'
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩ <;> rcases L.ok.sign with ⟨hA', hY'⟩ | ⟨hA', hY'⟩
  · rw [s.1 hY, s'.1 hY']
  · exact (not_herm_skew d.ok.hm hA hA').elim
  · exact (not_herm_skew d.ok.hm hA' hA).elim
  · rw [s.2 hY, s'.2 hY']
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end
