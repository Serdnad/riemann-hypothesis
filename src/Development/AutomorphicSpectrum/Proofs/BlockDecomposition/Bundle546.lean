module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.Bundle001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle340
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle525
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle469
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle524
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootExtensionLift
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorJacquetEigenRight
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle517
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle528
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.MapsExist
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusAdj

theorem conj_one_add {R : Type} [Ring R] (U A D Di : R) (h1 : D * Di = 1) (h2 : Di * D = 1) :
    D * (1 + (U - 1) * A) * Di = 1 + (D * U * Di - 1) * (D * A * Di) := by
  have k : D * U * Di * (D * A * Di) = D * (U * A) * Di := by
    calc D * U * Di * (D * A * Di) = D * U * (Di * D) * A * Di := by simp only [mul_assoc]
      _ = D * (U * A) * Di := by rw [h2]; simp only [mul_one, mul_assoc]
  calc D * (1 + (U - 1) * A) * Di = D * Di + (D * (U * A) * Di - D * A * Di) := by noncomm_ring
    _ = 1 + (D * U * Di * (D * A * Di) - D * A * Di) := by rw [h1, k]
    _ = 1 + (D * U * Di - 1) * (D * A * Di) := by noncomm_ring

theorem map_det_adj {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (A u t D Di : Matrix (Fin n) (Fin n) R)
    (h1 : D * Di = 1) (h2 : Di * D = 1) (hS : D * (u.map σ)ᵀ * Di = t) :
    σ (1 + A * (u - 1)).det = (1 + (t - 1) * (D * (A.map σ)ᵀ * Di)).det := by
  have e1 : (σ.mapMatrix (1 + A * (u - 1)))ᵀ = 1 + ((u.map σ)ᵀ - 1) * (A.map σ)ᵀ := by
    rw [map_add (f := _), map_mul, map_sub, map_one, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one]
    rfl
  have e2 : (D * (1 + ((u.map σ)ᵀ - 1) * (A.map σ)ᵀ) * Di).det = (1 + ((u.map σ)ᵀ - 1) * (A.map σ)ᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm D.det, mul_assoc, ← Matrix.det_mul, h1, Matrix.det_one, mul_one]
  rw [RingHom.map_det, ← Matrix.det_transpose, e1, ← e2, conj_one_add _ _ _ _ h1 h2, hS]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem rm_one : rm (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem adj_rm (d : GL (Fin n) E) (e : Matrix (Fin n) (Fin n) E) :
    rm d.val * ((rm e).map (conjAd E))ᵀ * rm (d⁻¹ : GL (Fin n) E).val = rm (sg d e) := by
  have h : ((rm e).map (conjAd E))ᵀ = rm (e.map (conjE E))ᵀ := by
    ext i j
    simp [rm, conjAd_algebraMap]
    rfl
  rw [h, sg, rm_mul, rm_mul]

theorem adj_inv (d : GL (Fin n) E) (t : GA E n) (ht : t ∈ adCent d) :
    rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ * rm (d⁻¹ : GL (Fin n) E).val = t.val := by
  have h : t⁻¹ * ratGL E n d * thetaA E n t = ratGL E n d := ht
  have hv : (t⁻¹ : GA E n).val * rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ = rm d.val :=
    congrArg Units.val h
  have h1 : rm d.val * rm (d⁻¹ : GL (Fin n) E).val = 1 := by
    rw [← rm_mul, Units.mul_inv, rm_one]
  calc rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ * rm (d⁻¹ : GL (Fin n) E).val
      = t.val * ((t⁻¹ : GA E n).val * rm d.val * ((t⁻¹ : GA E n).val.map (conjAd E))ᵀ) *
          rm (d⁻¹ : GL (Fin n) E).val := by
        simp only [← mul_assoc, Units.mul_inv, one_mul]
    _ = t.val := by rw [hv, mul_assoc, h1, mul_one]

theorem chi_sg (d : GL (Fin n) E) (e : Matrix (Fin n) (Fin n) E) (t : GA E n) (ht : t ∈ adCent d)
    (hc : t.val * rm (sg d e) = rm (sg d e) * t.val) : _root_.GlobalTheory.CompanionTheory.TorusCh.chi (sg d e) t = conjAd E (_root_.GlobalTheory.CompanionTheory.TorusCh.chi e t⁻¹) := by
  have h1 : rm d.val * rm (d⁻¹ : GL (Fin n) E).val = 1 := by
    rw [← rm_mul, Units.mul_inv, rm_one]
  have h2 : rm (d⁻¹ : GL (Fin n) E).val * rm d.val = 1 := by
    rw [← rm_mul, Units.inv_mul, rm_one]
  have hcom : (t.val - 1) * rm (sg d e) = rm (sg d e) * (t.val - 1) := by
    rw [sub_mul, mul_sub, hc, one_mul, mul_one]
  rw [_root_.GlobalTheory.CompanionTheory.TorusCh.chi, _root_.GlobalTheory.CompanionTheory.TorusCh.chi, map_det_adj (conjAd E) (rm e) _ t.val _ _ h1 h2 (adj_inv d t ht), adj_rm, hcom]

theorem lam_sg (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E)
    (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t : GA E n) (ht : t ∈ adCent d)
    (h1 : t.val * rm e = rm e * t.val) (h2 : t.val * rm (sg d e) = rm (sg d e) * t.val) :
    lam (sg d e) t = - lam e t := by
  rw [← lam_inv e he t h1, lam, lam, chi_sg d e t ht h2]
  exact GlobalTheory.CompanionTheory.DegPairingProof.logAbs_conj GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces _

end GlobalTheory.CompanionTheory.TorusAdj

end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}


variable (E r s) in
def blockOne (x : Lie E r) : Lie E (r + s) :=
  toL (Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
    (Matrix.fromBlocks (Matrix.of x) 0 0 1))

theorem contDiff_blockOne : ContDiff ℝ (⊤ : ℕ∞) (blockOne E r s) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  change ContDiff ℝ _ (fun x : Lie E r => Matrix.fromBlocks (Matrix.of x) 0 0 (1 : Matrix (Fin s) (Fin s) (Cinf E))
    ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i) ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j))
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i = i'
  generalize (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j = j'
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · exact contDiff_apply_apply ℝ i' j'
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const

theorem blockOne_val (y : GL (Fin r) (Cinf E)) :
    blockOne E r s (toL (y : Matrix (Fin r) (Fin r) (Cinf E))) =
      toL ((lev (Cinf E) r s (y, 1) : GL _ _) : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) := by
  have hv (g : GL (Fin r) (Cinf E) × GL (Fin s) (Cinf E)) :
      (GlobalTheory.SmGL.emb₂ (Cinf E) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) g).val =
        Matrix.reindex (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))
          (Matrix.fromBlocks g.1.val 0 0 g.2.val) := by
    ext i j
    simp [GlobalTheory.SmGL.emb₂, GlobalTheory.SmGL.leviEmb, GlobalTheory.SmGL.leviTwo,
      GlobalTheory.SmGL.two, Matrix.reindex_apply, Matrix.blockDiagonal']
    rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm i with a | a <;>
      rcases (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).symm j with b | b <;> simp
  rw [lev, hv]
  rfl

theorem exists_val_of_mem_invSet {x : Lie E r} (hx : x ∈ invSet E r) :
    ∃ y : GL (Fin r) (Cinf E), x = toL (y : Matrix (Fin r) (Fin r) (Cinf E)) :=
  ⟨(show IsUnit (Matrix.of x) from hx).unit, rfl⟩

theorem toL_val_mem_invSet (y : GL (Fin r) (Cinf E)) :
    toL (y : Matrix (Fin r) (Fin r) (Cinf E)) ∈ invSet E r :=
  show IsUnit (Matrix.of (Matrix.of.symm (y : Matrix (Fin r) (Fin r) (Cinf E)))) from y.isUnit

theorem sm_lev_slice (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (F : GA E (r + s) → ℂ)
    (hF : F ∈ Sm E (r + s)) : (fun m : GA E r => F (lev (Ad E) r s (m, 1))) ∈ Sm E r := by
  intro g
  have hmaps : Set.MapsTo (blockOne E r s) (invSet E r) (invSet E (r + s)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := exists_val_of_mem_invSet hx
    rw [blockOne_val]
    exact toL_val_mem_invSet _
  have hcomp := (hF (lev (Ad E) r s (g, 1))).comp contDiff_blockOne.contDiffOn hmaps
  refine hcomp.congr fun x hx => ?_
  obtain ⟨y, rfl⟩ := exists_val_of_mem_invSet hx
  rw [Function.comp_apply, blockOne_val, chart_val, chart_val]
  have e1 : lev (Ad E) r s (infGL E r y, 1) = infGL E (r + s) (lev (Cinf E) r s (y, 1)) := by
    rw [← lev_infGL, map_one]
  rw [← e1, lev_mul_one]

end GlobalTheory.CompanionTheory.CTFin.Slice1
end
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

theorem _root_.GlobalTheory.T.constant_term_unseen_statement_b : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E (r + s))), Cofin J → ∀ J₂ : Set (Module.End ℂ (Sm E s)), Cofin J₂ → (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) → ∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ z ∈ J₂, z G = 0) → ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)), ∃ (L₂ : Subgroup (GL (Fin s) (Af E))) (ρ₂ : Representation ℂ (Kinf E s) W), IsOpen (L₂ : Set (GL (Fin s) (Af E))) ∧ GlobalTheory.Published.AutFin.IsContRep ρ₂ ∧ ∀ F ∈ goodCT L ρ J, ∀ m₁ : GA E r, ∃ G ∈ genSpace L₂ ρ₂ J₂, ∀ m₂ : GA E s, G.1 m₂ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.Slice2.slice2 | exact GlobalTheory.CompanionTheory.CTFin.Slice2.slice2 | (intros; apply GlobalTheory.CompanionTheory.CTFin.Slice2.slice2 <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD

theorem _root_.GlobalTheory.T.smooth_conjugate_inverse_mem : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ {φ : GA E a → ℂ}, φ ∈ Sm E a → (fun g => star (φ (invA E a g))) ∈ Sm E a := by
  first | exact @GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm | exact GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm | (intros; apply GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm <;> assumption)
end

section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC

theorem continuous_unipotent_block_family {X R : Type} [TopologicalSpace X] [TopologicalSpace R] [Zero R] [One R] {n : ℕ}
    {f : X → Matrix (Fin n) (Fin n) R} (hf : Continuous f) :
    Continuous fun x => blk4 (1 : Matrix (Fin n) (Fin n) R) (f x) 0 1 := by
  unfold blk4
  exact (continuous_const.matrix_fromBlocks hf continuous_const continuous_const).matrix_submatrix _ _

theorem unipotent_block_mul_add {R : Type} [CommRing R] {n : ℕ} (b c : Matrix (Fin n) (Fin n) R) :
    blk4 (1 : Matrix (Fin n) (Fin n) R) b 0 1 * blk4 1 c 0 1 = blk4 1 (b + c) 0 1 := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [add_comm]

theorem continuous_nb {D : D7} {p : ℕ} {nb : hermA D p → G D p} (hnb : IsNMap nb) : Continuous nb := by
  have emb := isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D p)
  rw [emb.continuous_iff, Units.continuous_iff]
  have hv : Continuous fun b : hermA D p => (b.1 : Mx D p p) := continuous_subtype_val
  have hm : ∀ b, (AdelicU.matHom _ D.sp.cm.sig (Jst D p) (nb b)).1 = blk4 1 b.1 0 1 := hnb
  constructor
  · refine (continuous_unipotent_block_family hv).congr fun b => ?_
    exact (hm b).symm
  · refine (continuous_unipotent_block_family hv.neg).congr fun b => ?_
    symm
    refine Units.inv_eq_of_mul_eq_one_right ?_
    simp only [Function.comp]
    rw [hm b, unipotent_block_mul_add]
    simp [blk4]

end GlobalTheory.CompanionTheory.MuC
end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
noncomputable section

namespace GlobalTheory.CompanionTheory.MuC

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

theorem isNMap_add : ∀ {D : D7} {p : ℕ} {nb : hermA D p → G D p} (hnb : IsNMap nb) (x y : hermA D p), nb (x + y) = nb x * nb y := by
  intro D p nb hnb x y
  apply mat_inj
  rw [mat_mul, hnb, hnb, hnb, submatrix_fromBlocks_mul]
  simp [add_comm]

end GlobalTheory.CompanionTheory.MuC
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.cech_hodge_degeneration_natural : ∀ (K : Type) [Field K] [CharZero K],
    ∃ e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a j : ℕ),
      HT.Hdg q a (a + j) ≃ₗ[K] (cechH (Fk q U a) (Vk q U a) a).cx.H j,
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [Smooth p]
      (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι) (a : ℕ)
      (hG : ∀ T, KC q U a T → KC p W a ((pullM u hu a).G.obj T))
      (hτ : ∀ α T, Vk q U a α T → Vk p W a (τ α) ((morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG).G.obj T))
      (j : ℕ) (c : (cechH (Fk p W a) (Vk p W a) a).X j) (h0 : (cechH (Fk p W a) (Vk p W a) a).cx.d j c = 0)
      (h1 : (cechH (Fk q U a) (Vk q U a) a).cx.d j (fun i =>
        (morU (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG) (U := capT (Vk p W a) (τ ∘ i))
          (U' := capT (Vk q U a) i) fun T hT k => hτ (i k) T (hT k)).pull a (c (τ ∘ i))) = 0),
      HT.pullH u hu a (a + j) ((e p W a j).symm ((cechH (Fk p W a) (Vk p W a) a).cx.cls c h0)) =
        (e q U a j).symm ((cechH (Fk q U a) (Vk q U a) a).cx.cls _ h1) := by
  first | exact @GlobalTheory.CompanionTheory.OmGlobSite.glob_site | exact GlobalTheory.CompanionTheory.OmGlobSite.glob_site | (intros; apply GlobalTheory.CompanionTheory.OmGlobSite.glob_site <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrystallineFirstChernTorsionFree

section Core

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
  {κ : O →+* b.R ⧸ b.I}

def precomp {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick ((B.schFn q).cr b ht κ)} {D : E.LineData X}
    (Λ₀ : B.CLift g D) (h : C' ⥤ C) : B.CLift (h ⋙ g) D where
  p c := Λ₀.p (h.obj c)
  hp c := Λ₀.hp (h.obj c)
  w φ := Λ₀.w (h.map φ)
  hw φ hh := Λ₀.hw (h.map φ) hh

end Core

section Main

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} {γ : DividedPowers I} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {l s : ℕ}

theorem dpow_vanish {T : Thick (nlFun γ 0 X q (κA O I))} (hT : TF l s T) (k : ℕ) (hk : s ≤ k) (x : T.B) (hx : x ∈ T.J) :
    (k.factorial : T.B) * T.δ.dpow (k + 1) x = 0 := by
  have h1 : T.δ.dpow (k + 1) x ∈ T.pdPow s := by
    rw [pdPow_eq]
    refine Ideal.subset_span ⟨[(k + 1, x)], ?_, ?_, ?_⟩
    · intro z hz
      rw [List.mem_singleton] at hz
      rw [hz]
      exact hx
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega
    · simp
  rw [hT.1] at h1
  rw [(Ideal.mem_bot.1 h1), mul_zero]

theorem lifts_of_mem (D : E.LineData X) (T : Thick (nlFun γ 0 X q (κA O I))) (h : ∃ V ∈ 𝒱D D, InU V T) :
    ∃ a : Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ D.Y, a ≫ D.f = pt T := by
  obtain ⟨V, ⟨σ, hσ⟩, hV⟩ := h
  have hr : Set.range (pt T) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hV (show x ∈ (⊤ : Scheme.Opens _) from trivial)
  refine ⟨IsOpenImmersion.lift V.ι (pt T) hr ≫ σ, ?_⟩
  rw [Category.assoc, hσ, IsOpenImmersion.lift_fac]

end Main

theorem existsUnique_isFirstChernTorsionFree : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (D : E.LineData X), sSup (𝒱D D) = ⊤ → ∃! z, IsFirstChernThickening (TS γ q l s {⊤}) D s z := by
  intro O A _ _ _ I γ X q l s D hD
  have hle : St (TF l s) (𝒱D D) ≤ TS γ q l s {⊤} := fun T h => ⟨h.1, ⊤, rfl, fun _ _ => trivial⟩
  have hU : Used (TF l s : ObjectProperty (Thick (nlFun γ 0 X q (κA O I)))) := Or.inl ⟨rfl, l, s, rfl⟩
  have hb := (GlobalTheory.T.cech_refinement_cohomology_bijective (TF l s) hU (𝒱D D) {⊤} hle (by rintro W rfl; rw [hD]) 2).2.2
  let Q : ObjectProperty (Thick (nlFun γ 0 X q (κA O I))) := TS γ q l s {⊤}
  let Q' : ObjectProperty (Thick (nlFun γ 0 X q (κA O I))) := St (TF l s) (𝒱D D)
  let G₀ : Q'.FullSubcategory ⥤ Thick ((B.schFn q).cr (nlBase A I γ 0) rfl (κA O I)) := Q'.ι
  obtain ⟨Λ₀⟩ := GlobalTheory.T.exists_crystalline_lift (q := q) (b := nlBase A I γ 0) (ht := rfl) (κ := κA O I) G₀ D
    (fun T => lifts_of_mem D T.obj T.property.2)
  have hz₀ := (GlobalTheory.T.crystalline_cocycle_closed G₀ D (RingHom.id A) s (fun T k hk x hx => dpow_vanish T.property.1 k hk x hx)).1 Λ₀
  obtain ⟨x, hx⟩ := hb.2 ((CH.cx _).cls _ hz₀)
  refine ⟨x, ?_, ?_⟩
  · intro C _ G hG Λ₁
    let G₁ : C ⥤ Thick ((B.schFn q).cr (nlBase A I γ 0) rfl (κA O I)) := G ⋙ Q.ι
    have hcl := GlobalTheory.T.crystalline_cocycle_closed G₁ D (RingHom.id A) s
      (fun T k hk x hx => dpow_vanish (G.obj T).property.1 k hk x hx)
    let G' : C ⥤ Q'.FullSubcategory := Q'.lift (G ⋙ Q.ι) fun T => ⟨(G.obj T).property.1, hG T⟩
    let Λ' : B.CLift G₁ D := precomp Λ₀ G'
    refine ⟨hcl.1 Λ₁, ?_⟩
    refine (hcl.2 Λ₁ Λ' (hcl.1 Λ₁) (hcl.1 Λ')).trans ?_
    have e1 : (CH.Mor.restrict (CH.modF (sP Q).A) G).pull 2 x =
        (CH.Mor.restrict (CH.modF (sP Q').A) G').pull 2 ((incl hle).o.pull 2 x) := by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl
    rw [e1, hx]
    rfl
  · intro y hy
    apply hb.1
    obtain ⟨h1, h2⟩ := hy _ (ObjectProperty.ιOfLE hle) (fun T => T.property.2) Λ₀
    have e : (incl hle).o.pull 2 y = (CH.Mor.restrict (CH.modF (sP Q).A) (ObjectProperty.ιOfLE hle)).pull 2 y := by
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl
    rw [hx, e]
    exact h2.symm

end GlobalTheory.CompanionTheory.CrystallineFirstChernTorsionFree
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.witt_acris_flat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K), Module.Flat (WittVector l r.k) (CrystallineSemistableComparison.Pb.AW r) := by
  first | exact @GlobalTheory.CompanionTheory.FlatW.flat_AW | exact GlobalTheory.CompanionTheory.FlatW.flat_AW | (intros; apply GlobalTheory.CompanionTheory.FlatW.flat_AW <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.root_extension_lift : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (k : Bool) (n : ℕ) (𝓛 : Lift s.a (fun k => (s.T k : s.R)) (bs l k n).R (bs l k n).I (κb κ k n)) (δ : DividedPowers ((bs l k n).I.map 𝓛.i)) (hδ : IsDPMorphism (bs l k n).γ δ 𝓛.i) (hp : (bs l k n).p ≠ 0) (hn : IsNilpotent ((bs l k n).p : (bs l k n).R)) (X : RootExt l 𝓛.D 𝓛.t) (θ : liftObj s (b := bs l k n) rfl 𝓛 δ hδ hp hn ⟶ (gE F κ k n).obj 𝒯.obj), n ≠ 0 → (∀ j, θ.φ (𝓛.t j) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j 0 : 𝒯.A.A))) → ∃ e : X.E →+* 𝒯.A.Acr n, Function.Bijective e ∧ (∀ z, e (algebraMap 𝓛.D X.E z) = θ.φ z) ∧ ∀ j m, e (X.r j m) = 𝒯.A.toAcr n (WittVector.teichmuller l (𝒯.c j m : 𝒯.A.A)) := by
  first | exact @GlobalTheory.CompanionTheory.TowerAcr.tower_acr | exact GlobalTheory.CompanionTheory.TowerAcr.tower_acr | (intros; apply GlobalTheory.CompanionTheory.TowerAcr.tower_acr <;> assumption)
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.hecke_operator_jacquet_eigen_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ m : ℕ, 1 ≤ m → ∀ (d : Fin 2 → ℕ) (hd : ∑ a, d a = N), 0 < d 0 → 0 < d 1 → ∀ T : Module.End ℂ (fixed π (Zls.Km k N m)), Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N (d 0))) T → ∀ v : fixed π (Zls.Km k N m), (Submodule.Quotient.mk ((T v : fixed π (Zls.Km k N m)) : V) : Jacquet π (unipRad k (stdBlocks d hd))) = Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) (v : V)) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeJacquet.hecke_omega_jacquet | exact GlobalTheory.CompanionTheory.HeckeJacquet.hecke_omega_jacquet | (intros; apply GlobalTheory.CompanionTheory.HeckeJacquet.hecke_omega_jacquet <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Gram

theorem inner_facts : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (ρ : D.what₂.Tau), Continuous (fun y : Mx D V.rank r => (inner V y y : Mx D r r)) ∧ ∀ y : Mx D V.rank r, (inner V y y : Mx D r r) ∈ hermA D r ∧ compAt θ ρ (inner V y y : Mx D r r) = (compAt θ ρ y).conjTranspose * gramAt D V ρ * compAt θ ρ y := by
  intro D θ hθ V r ρ
  haveI := (Formalism.IndefR.Eqv.ae_facts D).1
  refine ⟨?_, fun y => ⟨?_, ?_⟩⟩
  · change Continuous (fun y : Mx D V.rank r => GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA V * y))
    exact GlobalTheory.MixModel.continuous_adj.matrix_mul (continuous_const.matrix_mul continuous_id)
  · change GlobalTheory.MixModel.adj (GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA V * y)) = GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.gA V * y)
    rw [GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_adj, GlobalTheory.MixModel.adj_gA, Matrix.mul_assoc]
  · change compAt θ ρ (GlobalTheory.MixModel.adj y * (GlobalTheory.MixModel.rat (Formalism.BasicNotions.HSpace.gram V) * y)) = _
    rw [GlobalTheory.CompanionTheory.WSum.compAt_mul', GlobalTheory.CompanionTheory.WSum.compAt_mul', GlobalTheory.CompanionTheory.WSum.compAt_adj hθ, GlobalTheory.CompanionTheory.WSum.compAt_rat hθ, Matrix.mul_assoc]
    rfl

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Gram
end
end
