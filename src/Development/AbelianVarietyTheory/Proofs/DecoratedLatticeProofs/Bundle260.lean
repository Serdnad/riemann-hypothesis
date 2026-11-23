module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtAndIsTheta
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle230
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle231
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle233
import Formalism.LocalRingCardinality.DataHost
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle199
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas

@[expose] public section

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.SiegelLaw

theorem value_zero_parabolic : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)), IsWeilSch ψ χ θ V μ ω → ∀ (Φ : schwartzA θ V.rank n), ∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g : G D n, (ω (p * g) Φ).1 0 = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (s0 V n + (n : ℂ) / 2) * (ω g Φ).1 0 := by
  intro D n V ψ χ θ μ ω hω Φ p hp a ha g
  obtain ⟨m, v, b, e, hm, hv⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hp a ha
  have e' : ω (p * g) Φ = ω m (ω v (ω g Φ)) := by
    rw [e, map_mul, map_mul]; rfl
  have z1 : ((0 : Mx D V.rank n) * a.1 : Mx D V.rank n) = 0 := Matrix.zero_mul _
  have z2 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by
    rw [GlobalTheory.StdUnn.inner, adj_zero, Matrix.zero_mul]
  have hs : s0 V n + (n : ℂ) / 2 = (V.rank : ℂ) / 2 := by rw [s0]; ring
  rw [e', hω.levi m _ hm, z1, hω.unip v b hv, z2, hs]
  simp [halfTr]

end GlobalTheory.StdUnn.SiegelLaw
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.HeightExists

variable {D : D7} {n : ℕ}

theorem lower_eq_zero {p : G D n} (hp : p ∈ P D n) (i j : Fin n) :
    mat p (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inl j)) = 0 := by
  have h := (hp (Pi.single (finSumFinEquiv (.inl j)) 1)).1 (by
    ext k
    have : (finSumFinEquiv (Sum.inr k : Fin n ⊕ Fin n)) ≠ finSumFinEquiv (.inl j) := by
      rw [Ne, finSumFinEquiv.apply_eq_iff_eq]; simp
    simp only [LinearMap.funLeft_apply, Pi.single_eq_of_ne this, Pi.zero_apply])
  have h2 := congrFun h i
  simp only [LinearMap.funLeft_apply, Matrix.mulVec_single_one, Pi.zero_apply] at h2
  exact h2

theorem blkA_mul {p q : G D n} (hq : q ∈ P D n) : blkA (mat (p * q)) = blkA (mat p) * blkA (mat q) := by
  ext i j
  have e : mat (p * q) = mat p * mat q := rfl
  simp only [e, blkA, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [lower_eq_zero hq, mul_zero, Finset.sum_const_zero, add_zero]

theorem blkA_one : blkA (mat (1 : G D n)) = 1 := by
  have e : mat (1 : G D n) = 1 := rfl
  rw [e, blkA, Matrix.submatrix_one_equiv, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

def leviBlock : P D n →* GL (Fin n) (AE D) :=
  MonoidHom.toHomUnits ⟨⟨fun p => blkA (mat p.1), blkA_one⟩, fun p q => blkA_mul q.2⟩

theorem continuous_mat : Continuous (mat : G D n → Mx D (n + n) (n + n)) :=
  Units.continuous_val.comp (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous

theorem continuous_leviBlock : Continuous (leviBlock (D := D) (n := n)) := by
  have hA : Continuous fun g : G D n => blkA (mat g) :=
    continuous_matrix fun i j => continuous_mat.matrix_elem _ _
  rw [Units.continuous_iff]
  refine ⟨hA.comp continuous_subtype_val, ?_⟩
  refine (hA.comp (continuous_subtype_val.comp continuous_inv)).congr fun p => ?_
  rw [← map_inv]; rfl

theorem continuous_detGL : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) (AE D) → (AE D)ˣ) := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  rw [Units.continuous_iff]
  refine ⟨Units.continuous_val.matrix_det, (Units.continuous_coe_inv.matrix_det).congr fun g => ?_⟩
  rw [← map_inv]; rfl

theorem isCompact_K : IsCompact (K D n : Set (G D n)) :=
  haveI := isLattice_stdLattice (E := D.host.E) (n := n + n)
  isCompact_levelAll (isCMExt_host D) _ _ _

theorem isClosed_P : IsClosed (P D n : Set (G D n)) := by
  haveI := t2Space_adeleRing' (F := D.host.F)
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  haveI := t2Space_tensorProduct_finiteExtension (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have : (P D n : Set (G D n)) = ⋂ x ∈ upperHalf D n, ({g | (mat g).mulVec x ∈ upperHalf D n} ∩
      {g | (mat g⁻¹).mulVec x ∈ upperHalf D n}) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq, SetLike.mem_coe]
    refine ⟨fun h x hx => ⟨(h x).1 hx, ((P D n).inv_mem h x).1 hx⟩, fun h x => ⟨fun hx => (h x hx).1, fun hx => ?_⟩⟩
    have := (h _ hx).2
    change (mat g⁻¹).mulVec ((mat g).mulVec x) ∈ _ at this
    rwa [Matrix.mulVec_mulVec, show mat g⁻¹ * mat g = mat (g⁻¹ * g) from rfl, inv_mul_cancel,
      show mat (1 : G D n) = 1 from rfl, Matrix.one_mulVec] at this
  have hU : IsClosed (upperHalf D n : Set (Fin (n + n) → AE D)) :=
    isClosed_eq (f := fun (x : Fin (n + n) → AE D) (i : Fin n) => x (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)))
      (g := fun _ => 0) (continuous_pi fun i => continuous_apply _) continuous_const
  rw [this]
  exact isClosed_biInter fun x _ => (hU.preimage (continuous_mat.matrix_mulVec continuous_const)).inter
    (hU.preimage ((continuous_mat.comp continuous_inv).matrix_mulVec continuous_const))

end GlobalTheory.StdUnn.HeightExists

namespace GlobalTheory.StdUnn


open HeightExists in
theorem exists_height : ∀ (D : D7) (n : ℕ), ∃ H : G D n → ℝ≥0, IsHeight H := by
  intro D n
  let δ : P D n →* ℝ≥0 := (absA D).comp (Matrix.GeneralLinearGroup.det.comp leviBlock)
  have hc : Continuous δ := continuous_absE.comp (continuous_detGL.comp continuous_leviBlock)
  haveI := t2Space_adeleRing' (F := D.host.F)
  have ht := triv_of_isCompact (δ := δ) isClosed_P hc isCompact_K
  refine ⟨iwAbs δ (K D n), fun p hp a ha k hk => ?_⟩
  rw [show a = leviBlock (D := D) (n := n) ⟨p, hp⟩ from Units.ext ha.symm]
  exact iwAbs_mul_of_triv ht ⟨p, hp⟩ hk

end GlobalTheory.StdUnn

end
end

section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.StdUnn



theorem exists_realPar_of_isCharAF : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ θ : InfFam D, IsInfFam θ → ∃ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l := by
  intro D ψ hψ θ hθ
  obtain ⟨ψ₀, h₀, a, -, ha⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  set y : D.host.E := algebraMap D.host.F D.host.E a with hy_def
  have hyc : IsCMField.complexConj D.host.E y = y :=
    (IsCMField.complexConj_eq_self_iff D.host.E y).2 a.2
  have hreal : ∀ τ, (tauE D τ y).im = 0 := by
    intro τ
    have h := IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y
    rw [hyc] at h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  refine ⟨fun τ => -(tauE D τ y).re, ?_⟩
  intro x
  have e1 : psiInf D.host.F ψ x = psiInf D.host.F ψ₀ (algebraMap D.host.F (Ainf D.host.F) a * x) := by
    simp only [psiInf]
    rw [ha]
    congr 1
    show (algebraMap D.host.F (Ainf D.host.F) a * x, algebraMap D.host.F (Af D.host.F) a * 0) = _
    rw [mul_zero]; rfl
  rw [e1, h₀.2.2 θ hθ]
  congr 1
  have e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y := by
    intro ρ
    have e3 : (algebraMap D.host.F (Ainf D.host.F) a * x) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul',
        ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one]
    rw [e3, map_mul, (hθ ρ).1]
  simp only [e2]
  have e4 : ∀ ρ, (((-(tauE D ρ y).re : ℝ)) : ℂ) = -tauE D ρ y := by
    intro ρ
    apply Complex.ext <;> simp [hreal ρ]
  simp only [e4, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun ρ _ => ?_
  ring

end GlobalTheory.StdUnn
end
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

theorem _root_.GlobalTheory.T.mem_wittStabilizer_of_keeps_isotropic_real_places : ∀ {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T), q ∈ GinfC T → (∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E), (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) → q ∈ stab d := by
  first | exact @GlobalTheory.Core.Rk.IwGlob.mem_stab_of_keeps | exact GlobalTheory.Core.Rk.IwGlob.mem_stab_of_keeps | (intros; apply GlobalTheory.Core.Rk.IwGlob.mem_stab_of_keeps <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical


theorem _root_.GlobalTheory.T.finite_monomials_with_prescribed_placeDegree : ∀ (D : D7) (m n : ℕ) (d : D.what₂.Tau → ℕ), {α : FVar D m n →₀ ℕ | ∀ τ, (∑ v ∈ α.support with v.1 = τ, α v) = d τ}.Finite := by
  first | exact @GlobalTheory.finite_monomials_of_placeDegree | exact GlobalTheory.finite_monomials_of_placeDegree | (intros; apply GlobalTheory.finite_monomials_of_placeDegree <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical


theorem _root_.GlobalTheory.T.exists_central_realPoint_unit_scalar_single_place : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (S : HSp D) (τ : D.what₂.Tau) (ζ : ℂ), ‖ζ‖ = 1 → ∃ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∧ ∀ ρ : D.what₂.Tau, ρ ≠ τ → compAt θ ρ (Formalism.L2.Theta.mt S z) = 1 := by
  first | exact @GlobalTheory.CentralUnit.exists_central_of_norm_one | exact GlobalTheory.CentralUnit.exists_central_of_norm_one | (intros; apply GlobalTheory.CentralUnit.exists_central_of_norm_one <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.integrable_mul_heightPow_of_bounded_factor : ∀ {G : Type} [MeasurableSpace G] [TopologicalSpace G] [OpensMeasurableSpace G] (μ : Measure G) (z m : G → ℂ) (H : G → ℝ) (C : ℝ) (b t : ℕ), Integrable z μ → Integrable m μ → Continuous H → (∀ g, 0 < H g ∧ H g ≤ 1) → t ≤ b → (∀ g, ‖z g‖ ≤ C * H g ^ ((b : ℝ) / 2) * ‖m g‖) → Integrable (fun g => z g * ((H g : ℝ) : ℂ) ^ (((0 : ℝ) : ℂ) - (t : ℂ) / 2)) μ := by
  first | exact @GlobalTheory.realZeta_integrable_mul_heightPow | exact GlobalTheory.realZeta_integrable_mul_heightPow | (intros; apply GlobalTheory.realZeta_integrable_mul_heightPow <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)

noncomputable section

namespace GlobalTheory.NrmVol

theorem measurableSet_suppQ : ∀ (D : D7) (v : FinPl D) (a b r : ℕ),
    MeasurableSet (GlobalTheory.NrmVol.suppQ (a := a) (b := b) v r) := by
  intro D v a b r
  haveI : BorelSpace (Fv D.host.F v) := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv D.host.F v)
  haveI : OpensMeasurableSpace (Matrix (Fin b) (Fin a) (Fv D.host.F v)) :=
    inferInstanceAs (OpensMeasurableSpace (Fin b → Fin a → Fv D.host.F v))
  have hentry : ∀ i j, Continuous fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => x i j :=
    fun i j => (continuous_apply j).comp (continuous_apply i)
  have htop : Continuous fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => topL r x := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    unfold topL
    by_cases h : i.val < b ∧ j.val < a
    · simp only [dif_pos h]; exact hentry _ _
    · simp only [dif_neg h]; exact continuous_const
  have hdet : Continuous fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => (topL r x).det :=
    htop.matrix_det
  have hball : IsOpen {y : Fv D.host.F v | Valued.v y < 1} := by
    simpa using Valued.isOpen_ball (Fv D.host.F v) 1
  have hsph : IsOpen {y : Fv D.host.F v | Valued.v y = 1} := by
    simpa using Valued.isOpen_sphere (Fv D.host.F v) (r := 1) one_ne_zero
  have hcb : IsOpen {y : Fv D.host.F v | Valued.v y ≤ 1} := by
    simpa using Valued.isOpen_closedBall (Fv D.host.F v) (r := 1) one_ne_zero
  have h1 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | IsUnit (topL r x).det} := by
    have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | IsUnit (topL r x).det} =
        (fun x => (topL r x).det) ⁻¹' {0}ᶜ := by
      ext x; simp [isUnit_iff_ne_zero]
    rw [this]
    exact (isOpen_compl_singleton.preimage hdet).measurableSet
  have h2 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | Valued.v (topL r x).det = 1} :=
    (hsph.preimage hdet).measurableSet
  have h3 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) |
      ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F} := by
    have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F} =
        ⋂ i, ⋂ j, (fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => x i j) ⁻¹' {y | Valued.v y ≤ 1} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
        HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => (hcb.preimage (hentry i j)).measurableSet
  have h4 : MeasurableSet {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) |
      ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1} := by
    have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1} =
        ⋂ i, ⋂ j, {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | r ≤ i.val → j.val < r → Valued.v (x i j) < 1} := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
    by_cases hij : r ≤ i.val ∧ j.val < r
    · have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | r ≤ i.val → j.val < r → Valued.v (x i j) < 1} =
          (fun x : Matrix (Fin b) (Fin a) (Fv D.host.F v) => x i j) ⁻¹' {y | Valued.v y < 1} := by
        ext x; simp [hij.1, hij.2]
      rw [this]
      exact (hball.preimage (hentry i j)).measurableSet
    · have : {x : Matrix (Fin b) (Fin a) (Fv D.host.F v) | r ≤ i.val → j.val < r → Valued.v (x i j) < 1} =
          Set.univ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro h h'
        exact absurd ⟨h, h'⟩ hij
      rw [this]
      exact MeasurableSet.univ
  have : suppQ (a := a) (b := b) v r =
      {x | IsUnit (topL r x).det} ∩ {x | Valued.v (topL r x).det = 1} ∩
        {x | ∀ i j, x i j ∈ v.adicCompletionIntegers D.host.F} ∩
        {x | ∀ i j, r ≤ i.val → j.val < r → Valued.v (x i j) < 1} := by
    ext x
    simp only [suppQ, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
  rw [this]
  exact ((h1.inter h2).inter h3).inter h4

end GlobalTheory.NrmVol
end
end
