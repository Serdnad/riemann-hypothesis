module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle038
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
import Development.WeilBound.ThetaLifts.SmallCones.Bundle001
import GroundTheory.GlobalFields.TateThesis.Bundle006
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle020
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle039
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.UnitaryGroupInverseFormula
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
public import Development.WeilBound.ThetaLifts.LatticeBasics.CompCA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle005
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
import Development.WeilBound.ThetaLifts.LatticeBasics.HgtFin
import Development.WeilBound.ThetaLifts.LatticeBasics.SkewTwo
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle026
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle001
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFPB
open PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem map_isHaar_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) [νf.IsAddHaarMeasure] :
    (Measure.map (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf)).IsAddHaarMeasure := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := Pi.borelSpace
  haveI : MeasurableAdd (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := inferInstance
  haveI : SigmaFinite νf := inferInstance
  haveI : ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact ContinuousAddEquiv.isAddHaarMeasure_map ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf) (_root_.PositivityTheory.SiegelWeilFormula.KFPB.jnpE_k R)
theorem exists_nuf'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : ∃ νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), νf.IsAddHaarMeasure ∧
    (Measure.map (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf)).IsAddHaarMeasure := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  exact ⟨Measure.addHaar, inferInstance, _root_.PositivityTheory.SiegelWeilFormula.KFPB.map_isHaar_k R _⟩
theorem integral_jnp'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg' : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) {b : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ} (hb : Continuous b) (hb1 : ∀ u, ‖b u‖ ≤ 1) :
    ∫ X, f X * star (b (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X))
        ∂(Measure.map (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf)) =
      ∫ u, star (b u) * _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f g u := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := Pi.borelSpace
  haveI : SigmaFinite νf := inferInstance
  set μ := (volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf with hμ
  let e : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d ≃ᵐ Mx F E d.m d.n := (_root_.PositivityTheory.SiegelWeilFormula.KFPB.jnpE_k R).toHomeomorph.toMeasurableEquiv
  have hmap : Measure.map (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) μ = Measure.map e μ := rfl
  have hH : (Measure.map e μ).IsAddHaarMeasure := _root_.PositivityTheory.SiegelWeilFormula.KFPB.map_isHaar_k R νf
  have hfi : Integrable (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2)) μ :=
    (integrable_map_equiv e f).1 (_root_.PositivityTheory.SiegelWeilFormula.KFock.int_schM_k d _ hH hf)
  obtain ⟨C, hC⟩ := hg'.1.continuous.bounded_above_of_compact_support hg'.2
  have hint : Integrable (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) * star (b p.1 * g p.2)) μ := by
    refine hfi.mul_bdd (c := C) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (continuous_star.comp ((hb.comp continuous_fst).mul (hg'.1.continuous.comp continuous_snd))).aestronglyMeasurable
    · rw [norm_star, norm_mul]
      calc ‖b p.1‖ * ‖g p.2‖ ≤ 1 * C := mul_le_mul (hb1 _) (hC _) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
  rw [hmap, integral_map_equiv]
  have he : ∀ p, e p = _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2 := fun p => rfl
  simp only [he, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k]
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k, star_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring
end PositivityTheory.SiegelWeilFormula.KFPB
end
end
end

section



section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd.DM
open PositivityTheory.SiegelWeilFormula.Krd.DC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem dblJ_det_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε) : (dbl d.Y.J).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det hε
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul] at this
  exact QR_det_ne E ε this.symm
def bX_k (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
  d.b.1 * X * (d.b⁻¹).1
theorem bX_unitary_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    {X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E} (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X)ᵀ * dbl d.Y.J * (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X).map σ = dbl d.Y.J :=
  conj_unitE (σ : E →+* E) d.b.1 (d.b⁻¹).1 X (dbl d.Y.J) (QR E d.n ε) (Units.mul_inv d.b) hε hX
def ratG_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) : d.G :=
  ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F))
    (Matrix.nonsingInvUnit (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X) (isUnit_iff_ne_zero.2 (det_ne_of (σ : E →+* E) (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_unitary_k d hε hX) (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.dblJ_det_k d hε)))),
    by
      show (incM F (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X))ᵀ * dbl (incM F d.Y.J) * (incM F (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X)).map (cA σ) = dbl (incM F d.Y.J)
      rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k d, incM_cA, incM_alt_bis, ← incM_mul, ← incM_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_unitary_k d hε hX]⟩
theorem ratG_mem_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX ∈ rat2 σ d.Y :=
  Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩
theorem inFrame_ratG_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX) = incM F X := by
  show incM F (d.b⁻¹).1 * incM F (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X) * incM F d.b.1 = incM F X
  rw [← incM_mul, ← incM_mul]
  congr 1
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
theorem inFrame_mul_k (x z : d.G) : inFrame d.b (x * z) = inFrame d.b x * inFrame d.b z := by
  show incM F (d.b⁻¹).1 * (mat2 x * mat2 z) * incM F d.b.1 =
    (incM F (d.b⁻¹).1 * mat2 x * incM F d.b.1) * (incM F (d.b⁻¹).1 * mat2 z * incM F d.b.1)
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 z) * incM F d.b.1 =
      incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 z * incM F d.b.1 := by
        rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]
theorem inFrame_inj_k {x z : d.G} (h : inFrame d.b x = inFrame d.b z) : x = z := by
  have e : ∀ u : d.G, mat2 u = incM F d.b.1 * inFrame d.b u * incM F (d.b⁻¹).1 := fun u => by
    simp only [inFrame, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.one_mul]
    rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.mul_one]
  apply Subtype.ext
  apply Units.ext
  show mat2 x = mat2 z
  rw [e x, e z, h]
end PositivityTheory.SiegelWeilFormula.Krd.DM
open PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.DM PositivityTheory.SiegelWeilFormula.Krd.DC in
theorem PositivityTheory.SiegelWeilFormula.Krd.denseW_k : _root_.PositivityTheory.SiegelWeilFormula.DenseW_k := by
  intro F E _ _ _ _ _ σ d R w y O hO hy
  have h0 := zeta_ne R.hζ
  have hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n R.ε := R.hε
  obtain ⟨X, hXU, hXO⟩ := exists_rat d.cm (d.B.emb w).1 R.hζ hO hy
  have hX := rat_unitary d.cm (d.B.emb w).1 R.ε X hXU
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_mem_k d hε X hX, _, hXO, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX * (R.ι w (Phi R.hζ ⟨_, hXU⟩))⁻¹,
    (inv_mul_cancel_right _ _).symm, fun y'' => ?_⟩
  set y' := Phi R.hζ ⟨X.map (d.B.emb w).1, hXU⟩ with hy'
  set A := inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX * (R.ι w y')⁻¹) with hA
  have hAC : A * inFrame d.b (R.ι w y') = incM F X := by
    rw [hA, ← _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k, inv_mul_cancel_right, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_ratG_k]
  have hC : d.cw w (inFrame d.b (R.ι w y')) = X.map (d.B.emb w).1 := by
    have e := R.at_w w y'
    rw [show mR y' = dZ d.n R.ζ * X.map (d.B.emb w).1 * dZ d.n R.ζ⁻¹ from rfl, Matrix.mul_assoc _ (dZ _ R.ζ⁻¹),
      dZ_inv_mul h0, Matrix.mul_one] at e
    have := congrArg (fun M => dZ d.n R.ζ⁻¹ * M) e
    simpa only [← Matrix.mul_assoc, dZ_inv_mul h0, Matrix.one_mul] using this
  have hdet := det_of_inU hXU
  have hAw : d.cw w A = 1 := by
    have e : d.cw w A * X.map (d.B.emb w).1 = X.map (d.B.emb w).1 := by
      have := congrArg (d.cw w) hAC
      rwa [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, hC, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k] at this
    calc d.cw w A = d.cw w A * X.map (d.B.emb w).1 * (X.map (d.B.emb w).1)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = 1 := by rw [e, Matrix.mul_nonsing_inv _ hdet]
  apply _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d _ (R.ι w y''), _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d (R.ι w y''), ← hA]
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k]
    by_cases hw : w' = w
    · subst hw; rw [hAw, Matrix.one_mul, Matrix.mul_one]
    · rw [R.off_w w w' y'' hw, Matrix.one_mul, Matrix.mul_one]
  · rw [fin_mul, fin_mul, R.off_f w y'', ← fin_mul, ← fin_mul, Matrix.mul_one, Matrix.one_mul]
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
section Mat
variable {ι R : Type} [Fintype ι] [DecidableEq ι] [Semiring R]
end Mat
theorem inFrame_one_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : inFrame d.b (1 : d.G) = 1 := by
  have e : mat2 (1 : d.G) = 1 := rfl
  simp only [inFrame, e, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k]
theorem quasiCharacter_conj_embed {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (g : L.sd.G) : IdentityOnLastRowsCols L.i₀ (inFrame d.b (L.j g)) := fun u hu v => L.j_out g u hu v
theorem q_conj'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {q : d.G} {lam : (AE F E)ˣ} (hq : IsQ F E L.i₀ (inFrame d.b q) lam) (g : L.sd.G) :
    IsQ F E L.i₀ (inFrame d.b (L.j g * q * (L.j g)⁻¹)) lam := by
  have hH : inFrame d.b (L.j g) * inFrame d.b (L.j g)⁻¹ = 1 := by
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, mul_inv_cancel, _root_.PositivityTheory.SiegelWeilFormula.Avac.inFrame_one_k]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k]
  refine isQ_conj hq hH (_root_.PositivityTheory.SiegelWeilFormula.Avac.quasiCharacter_conj_embed L g) ?_
  rw [← map_inv]
  exact _root_.PositivityTheory.SiegelWeilFormula.Avac.quasiCharacter_conj_embed L g⁻¹
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

section



section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Vf2
open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open PositivityTheory.ThK PositivityTheory.ThK.Vac PositivityTheory.ThKH.Iwas GlobalTheory.Doubling PositivityTheory.ThKG.Loc.Cone.Vf
open Formalism.UG (bc)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v : Pl F}
theorem exists_res_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (v : Pl F) : ∃ (K : Type) (_ : Field K) (r : intLoc F E v →+* K),
    Function.Surjective r ∧ (((∀ z, r z = 0 → r (cInt σ v z) = 0) ∧ ∃ κ, r (κ - cInt σ v κ) ≠ 0) ∨
      ∃ η, r η = 1 ∧ r (cInt σ v η) = 0) ∧ ∀ z, r z ≠ 0 → r (cInt σ v z) ≠ 0 → IsUnit z := by
  have hσ := hB.cm
  rcases _root_.GlobalTheory.KFinLoc.split_or_inert_k F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · let ρ : intLoc F E v →+* v.adicCompletionIntegers F := ((splitProj τ : Fv F v ⊗[F] E →+* Fv F v).comp
      (intLoc F E v).subtype).codRestrict (v.adicCompletionIntegers F).toSubring fun z => splitProj_mem τ z.2
    have mk : ∀ a b : v.adicCompletionIntegers F, (splitAlgEquiv hσ τ).symm (a.1, b.1) ∈ intLoc F E v := fun a b =>
      (mem_intLoc_iff_split hσ τ).2 ⟨by rw [splitProj_symm]; exact a.2, by rw [splitProj_comp_symm]; exact b.2⟩
    refine ⟨_, inferInstance, (IsLocalRing.residue _).comp ρ,
      IsLocalRing.residue_surjective.comp fun a => ⟨⟨_, mk a 0⟩, Subtype.ext (splitProj_symm hσ τ _)⟩,
      .inr ⟨⟨_, splitIdem_mem hσ τ⟩, ?_, ?_⟩, fun z h1 h2 => ?_⟩
    · exact (congrArg (IsLocalRing.residue _) (Subtype.ext (splitProj_splitIdem hσ τ) : ρ ⟨_, splitIdem_mem hσ τ⟩ = 1)).trans (map_one _)
    · exact (congrArg (IsLocalRing.residue _) (Subtype.ext ((splitProj_comp τ σ _).symm.trans (splitProj_comp_splitIdem hσ τ)) :
        ρ (cInt σ v ⟨_, splitIdem_mem hσ τ⟩) = 0)).trans (map_zero _)
    · obtain ⟨a, ha⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1).exists_right_inv
      obtain ⟨b, hb⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h2).exists_right_inv
      refine IsUnit.of_mul_eq_one ⟨_, mk a b⟩ (Subtype.ext (split_ext hσ τ ?_ ?_))
      · rw [Subring.coe_mul, map_mul, splitProj_symm, Subring.coe_one, map_one]; exact congrArg Subtype.val ha
      · rw [Subring.coe_mul, map_mul, splitProj_comp_symm, Subring.coe_one, map_one, splitProj_comp]; exact congrArg Subtype.val hb
  · have hu : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
    obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hu
    obtain ⟨ϖ, -, hv, -, -, ⟨x, hx, hx1⟩, -⟩ := exists_isUnramInv hσ hw hc
    let ρ : intLoc F E v →+* w.adicCompletionIntegers E :=
      ((toCompl hu).comp (intLoc F E v).subtype).codRestrict (w.adicCompletionIntegers E).toSubring fun z => toCompl_mem hu z.2
    have sj : Function.Surjective ρ := fun a => by
      obtain ⟨z, hz⟩ := (toCompl_bijective hw hu).2 a.1
      exact ⟨⟨z, (mem_intLoc_iff hw hu _).2 (hz ▸ a.2)⟩, Subtype.ext hz⟩
    have un : ∀ z, ((IsLocalRing.residue _).comp ρ) z ≠ 0 ↔ Valued.v (toCompl hu z.1) = 1 := fun z =>
      (IsLocalRing.residue_ne_zero_iff_isUnit _).trans HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
    refine ⟨_, inferInstance, (IsLocalRing.residue _).comp ρ, IsLocalRing.residue_surjective.comp sj,
      .inl ⟨fun z hz => by_contra fun h => (un z).2 ?_ hz, ?_⟩, fun z h1 _ => ?_⟩
    · rw [← hv, hc]
      exact (un (cInt σ v z)).1 h
    · obtain ⟨κ, hκ⟩ := sj ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hx⟩
      refine ⟨κ, (un _).2 ?_⟩
      change Valued.v (toCompl hu (κ.1 - sigR _ σ κ.1)) = 1
      rw [map_sub, ← hc, show toCompl hu κ.1 = x from congrArg Subtype.val hκ, Valuation.map_sub_swap, hx1]
    · obtain ⟨a, ha⟩ := ((IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1).exists_right_inv
      obtain ⟨z', rfl⟩ := sj a
      refine IsUnit.of_mul_eq_one z' (Subtype.ext ((toCompl_bijective hw hu).1 ?_))
      rw [Subring.coe_mul, map_mul, Subring.coe_one, map_one]; exact congrArg Subtype.val ha
theorem exists_beta_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s)
    (g : UG (cA σ) (dbl (incM F X.J))) {x y a₁ a₂ : Matrix (Fin n) (Fin n) (AE F E)}
    (hg : g.1.1 * (diagCols (Fin n) : Matrix _ _ (AE F E)) = Matrix.fromRows x y) (hx : x ∈ Pres v X) (hy : y ∈ Pres v X)
    (h1 : a₁ ∈ Pres v X) (h2 : a₂ ∈ Pres v X) (h : a₁ * x + a₂ * y = 1) (ax : At (evFin F v) (x - 1)) (ay : At (evFin F v) (y - 1)) :
    ∃ b b' t', Adj (cA σ) (incM F X.J) b b' ∧ b + b' = -1 ∧ b ∈ Pres v X ∧ t' ∈ Pres v X ∧ (y + b * (y - x)) * t' = 1 := by
  have hσ := cm_conj_conj hB.cm
  have cc := _root_.GlobalTheory.ThK.Dbl.cA_cA (F := F) hB.cm
  have hL := hX.lat
  obtain ⟨K, _, ρ, r1, r2, r3⟩ := _root_.GlobalTheory.ThK.Dbl.Vf2.exists_res_k hB v
  obtain ⟨P, p1, p2⟩ := Frames.exists_rational_frame X.L v
  obtain ⟨G', hG', g1, g2⟩ := Hgt.gram_loc (v := v) (herm_det hX).ne_zero hL.fg (I := IsIntegral ℤ) (fun z hz b => hz.mul b.2) hX.dual
    isIntegral_one (fun z hz => ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, ⟨z, hz⟩, by simp; rfl⟩) P p1 p2
  simp only [inv_one, one_mul] at g1 g2
  have ha := fr_iff (Frames.frame_of_rational P p1 p2)
  set G₀ := P.1ᵀ * X.J * P.1.map σ with hG₀
  let ι := inclR (F := F) (E := E) (Fv F v)
  set a : GL (Fin n) (Fv F v ⊗[F] E) := bc ι P
  let j := (intLoc F E v).subtype.mapMatrix (m := Fin n)
  have inj : Function.Injective j := fun A B e => Matrix.ext fun i k => Subtype.ext (congrFun₂ e i k)
  let G : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i k => ⟨_, (g1 i k).mem⟩
  let H : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i k => ⟨_, (g2 i k).mem⟩
  have eG : a.1ᵀ * (incM F X.J).map (compFin F E v) * a.1.map (sigR _ σ) = j G := by
    change _ = G₀.map ι
    rw [hG₀, Matrix.map_mul, Matrix.map_mul, show (incM F X.J).map (compFin F E v) = X.J.map ι from
      Matrix.ext fun i k => congrArg (· ⊗ₜ[F] X.J i k) (map_one (evFin F v))]
    rfl
  have jj : ∀ N N' : Matrix (Fin n) (Fin n) (intLoc F E v), j (Nᵀ * G * N'.map (cInt σ v)) = (j N)ᵀ * j G * (j N').map (sigR _ σ) :=
    fun N N' => by rw [map_mul, map_mul]; rfl
  obtain ⟨θ₀, hθ⟩ := _root_.GlobalTheory.exists_int_add_conj_eq_one_of_base_good_k B hB
  let θ : AE F E := inclR (F := F) (AF F) (θ₀ : E)
  have iθ : compFin F E v (-θ) ∈ intLoc F E v := by
    rw [map_neg]; exact neg_mem (tmul_mem_intLoc (show evFin F v 1 ∈ _ by rw [map_one]; exact one_mem _) θ₀)
  have b0 : Adj (cA σ) (incM F X.J) ((-θ) • 1) ((-cA σ θ) • 1) := Adj.one.smul (by rw [map_neg, cc])
  have hb0 : (-θ) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + (-cA σ θ) • 1 = -1 := by
    rw [← add_smul, ← neg_add, show θ + cA σ θ = inclR (F := F) (AF F) (θ₀ + σ θ₀ : E) from (map_add _ _ _).symm, hθ, map_one,
      neg_smul, one_smul]
  have pb0 := smul_mem_Pres hL iθ (one_mem (Pres v X))
  have lag := lag_of b0 hb0 g hg
  set b₀ := (-θ) • (1 : Matrix (Fin n) (Fin n) (AE F E))
  have pm := sub_mem hy hx
  obtain ⟨Nm, hNm⟩ := (ha _).1 pm
  obtain ⟨NM, hNM⟩ := (ha _).1 (add_mem hy (mul_mem pb0 pm))
  obtain ⟨NP, hNP⟩ := (ha _).1 (add_mem h1 h2)
  obtain ⟨NQ, hNQ⟩ := (ha _).1 (sub_mem (neg_mem h1) (mul_mem (add_mem h1 h2) pb0))
  obtain ⟨S, s1, s2⟩ := exists_skew (c := cInt σ v) (r := ρ) (G := G) (G' := H) (M := NM) (m := Nm) (P := NP) (Q := NQ)
    (fun z => Subtype.ext (by
      change sigR _ σ (sigR _ σ z.1) = z.1
      induction z.1 using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (hσ x)
      | add x y hx hy => simp only [map_add (f := _), hx, hy])) r1
    (fun i k => Subtype.ext (congrArg ι (by
      change σ (G₀ k i) = G₀ i k

      simp only [hG₀, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hX.herm, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)))
    (inj (by
      rw [map_mul, map_one]
      change G₀.map ι * G'.map ι = 1
      rw [← Matrix.map_mul, mul_eq_one_comm.1 hG', Matrix.map_one _ (map_zero _) (map_one _)])) r2 r3
    (inj (by
      rw [map_add (f := _), jj, jj, hNm, hNM, ← eG, ← gram_fr, ← gram_fr, ← Matrix.add_mul, ← Matrix.mul_add,
        ← Matrix.map_add _ (map_add _), lag, Matrix.map_zero _ (map_zero _), Matrix.mul_zero, Matrix.zero_mul, map_zero]))
    (inj (by
      rw [map_add (f := _), map_mul, map_mul, hNm, hNM, hNP, hNQ, ← map_mul, ← map_mul, ← map_add (f := _), map_one, ← map_one (fr v a), ← h]
      congr 1
      noncomm_ring))
  let SA : Matrix (Fin n) (Fin n) (AE F E) := (a.1 * j S * (a⁻¹).1).map (sgE E v)
  have aS : At (evFin F v) SA := fun u hu => Matrix.ext fun i k => at_sgE _ u hu
  have fS : fr v a SA = j S := by
    rw [fr_apply, show SA.map (compFin F E v) = a.1 * j S * (a⁻¹).1 from Matrix.ext fun _ _ => comp_sgE _]
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Units.inv_mul_cancel_left]
  have sk : SAᵀ * incM F X.J + incM F X.J * SA.map (cA σ) = 0 := by
    have k1 := gram_fr (σ := σ) a (incM F X.J) SA 1
    have k2 := gram_fr (σ := σ) a (incM F X.J) 1 SA
    have k3 := congrArg j s1
    have k4 := jj S 1
    have k5 := jj 1 S
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, map_one, mapc_one, fS, eG,
      Matrix.map_one _ (map_zero (sigR (Fv F v) σ)) (map_one _), Matrix.map_one _ (map_zero (cInt σ v)) (map_one _)] at k1 k2 k4 k5
    rw [map_add (f := _), k4, k5, ← k1, ← k2, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.map_add _ (map_add _), map_zero] at k3
    have u1 : IsUnit a.1ᵀ := (Matrix.isUnit_transpose _).2 a.isUnit
    have u2 : IsUnit (a.1.map (sigR (Fv F v) σ)) := a.isUnit.map (sigR (Fv F v) σ).mapMatrix
    rw [u2.mul_left_eq_zero, u1.mul_right_eq_zero] at k3
    refine Matrix.ext fun i k => eq_zero_of_at (v := v) (fun u hu => congrFun₂ (at_add (at_mul_left (M := SAᵀ)
      (fun u hu => congrArg Matrix.transpose (aS u hu)) _) (at_mul_right _ (N := SA.map (cA σ)) fun u hu => Matrix.ext fun i k => by
        change u • cA σ (SA i k) = 0
        rw [← map_smul, show u • SA i k = 0 from congrFun₂ (aS u hu) i k, map_zero]) u hu) i k) (congrFun₂ k3 i k)
  have am : At (evFin F v) (y - x) := by simpa using at_sub ay ax
  obtain ⟨t', pt, ht⟩ := exists_inv ha (f := y + (b₀ + SA) * (y - x)) (N := NM + S * Nm)
    (by rw [add_sub_right_comm]; exact at_add ay (at_mul_right _ am))
    (by rw [map_add (f := _), map_mul, hNm, hNM, ← fS, ← map_mul, ← map_add (f := _), add_mul, add_assoc]) s2
  exact ⟨b₀ + SA, _ + -SA, t', b0.add (by rw [Adj, mapc_neg, Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left sk),
    by rw [add_add_add_comm, add_neg_cancel, add_zero, hb0], add_mem pb0 ((ha _).2 ⟨S, fS.symm⟩), pt, ht⟩
end GlobalTheory.ThK.Dbl.Vf2
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
theorem linRedC_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k := by
  intro hT hTC hLB hU hS c F E _ _ _ _ _ σ d hE k cs Φs hK x hW nb lam 𝓖 hcd ε w hw T hND
  have hTT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k := hT.2.2.2.1
  have hTA : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k := hT.2.2.2.2
  have hsch : ∀ i ∈ (Finset.univ : Finset (Fin k)), Φs i ∈ d.sch := fun i _ => (hK i).1
  have hsum := _root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_sum_mem_k d Finset.univ cs Φs hsch
  have hIfun : d.I (∑ i, cs i • Φs i) = ∑ i, cs i • d.I (Φs i) := by
    funext y; rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_I_sum_k d hTT hTA Finset.univ cs Φs hsch y]; simp [Finset.sum_apply]
  have horb : d.orb T (d.om x (∑ i, cs i • Φs i)) = ∑ i, cs i * d.orb T (d.om x (Φs i)) := by
    rw [← hTC F E σ d _ hsum nb lam 𝓖 hcd T x, hIfun,
      _root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_fc_sum_k hLB d hcd T hND x Finset.univ cs (fun i => d.I (Φs i)) (fun i => ((hTA F E σ d).2.2 _ (hK i).1).2.1)
        (fun i => ((hTA F E σ d).2.2 _ (hK i).1).2.2)]
    exact Finset.sum_congr rfl fun i _ => by rw [hTC F E σ d _ (hK i).1 nb lam 𝓖 hcd T x]
  have horbc : c * d.orb T (d.om x (∑ i, cs i • Φs i)) = ∑ i, cs i * (c * d.orb T (d.om x (Φs i))) := by
    rw [horb, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  choose t ht using fun i => hU F E σ d (s0 d.m d.n) (d.sec0 (Φs i)) (hS F E σ d (Φs i) (hK i)) (hE (Φs i) (hK i))
  have hval := lin_holValueAt_sum Finset.univ cs
    (fun i z => ∫ β, flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
    (fun i => c * d.orb T (d.om x (Φs i))) (s0 d.m d.n) (fun i _ => hW i nb lam 𝓖 hcd ε w hw T hND)
  rw [horbc]
  refine hval.congr ⟨∑ i, |t i|, fun z hz => ?_⟩
  have hzi : ∀ i, t i < z.re := fun i => lt_of_le_of_lt
    ((le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i))) hz
  have hint : ∀ i, Integrable (fun β => flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) *
      d.B.ψ (-d.tt (T.1.1 * β.1))) lam := fun i =>
    ((ht i z (hzi i) nb lam 𝓖 hcd ε w hw x).1).mul_bdd (_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_psi_meas_k d T.1.1).aestronglyMeasurable
      (Eventually.of_forall fun β => (GlobalTheory.StdCharFromIsStd.norm_psi d.ok.good.std _).le)
  show ∑ i, cs i * ∫ β, flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam =
    ∫ β, flat d.a (d.sec0 (∑ i, cs i • Φs i)) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam
  refine (Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm).trans ?_
  refine (integral_finsetSum (μ := lam) Finset.univ
    (f := fun i β => cs i * (_root_.GlobalTheory.ThK.Dbl.flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) *
      d.B.ψ (-d.tt (T.1.1 * β.1)))) (fun i _ => (hint i).const_mul (cs i))).symm.trans ?_
  congr 1
  funext β
  simp only [_root_.GlobalTheory.ThK.Dbl.flat, constantTerm_finsetSum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end
