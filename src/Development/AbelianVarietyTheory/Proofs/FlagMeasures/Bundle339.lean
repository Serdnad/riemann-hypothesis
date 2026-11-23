module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle055
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle077
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle076
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle316
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle328
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitRowLatticeMiddleIffGluedLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle330
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle331
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfUnimodularLatticesAtPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryHostFieldArithmeticConditionsProof
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle002
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeTermAdaptedNormalForm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle045
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle241
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

@[expose] public section

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.StCoord

theorem zh_eq (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T')
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k)
    (c : GCoord Z F0 F0' FP G) : G.Zh = ZhatL F0 F0' := by
  have hs : ∀ x : D.host.E, D.conjF x = star x := fun x => by
    rw [D.conjF_eq]; exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
  funext a b
  have := c.h_eq (frame F0' b) (frame F0 a)
  simp only [GFrames.Zh, Matrix.of_apply, c.f_eq, c.f'_eq]
  simp only [hs]
  exact this

theorem stab_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), (∀ x ∈ G.St, ∃ B : Formalism.L2.SG.PairVal.MatR D, IsUpUni B ∧ (∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) ∧ ∀ a b : Fin (D.R.rS + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → B a b = 0) ∧ ∀ B : Formalism.L2.SG.PairVal.MatR D, IsUpUni B → (∀ a b : Fin (D.R.rS + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → B a b = 0) → ∃! x, x ∈ G.St ∧ ∀ b, x (G.f' b) = ∑ a, B a b • G.f' a := by
  intro D X Y u u' _ _ w F00 F'0 FP hw _ _ G c
  have hZ : Formalism.MainNotions.S.ZhatOM G.Zh = Formalism.MainNotions.S.ptMat w := by rw [zh_eq D _ F00 F'0 FP G c]; exact hw
  have hinv : ∀ x, (D.conjF : D.host.E →+* D.host.E) ((D.conjF : D.host.E →+* D.host.E) x) = x := by
    intro x
    have hs : ∀ x : D.host.E, D.conjF x = star x := fun x => by
      rw [D.conjF_eq]; exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
    show D.conjF (D.conjF x) = x
    rw [hs, hs, star_star]
  obtain ⟨hb1, hb2⟩ := GlobalTheory.T.unitriangularStabilizer_pointMatrix_blockDiagonal (D.conjF : D.host.E →+* D.host.E) hinv D.R.rS w G.Zh hZ
  have up : ∀ s : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E,
      ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ↔ Formalism.MainNotions.S.IsUpUni s := by
    intro s
    constructor
    · rintro ⟨h1, h2⟩ i j; exact ⟨h1 i j, fun h => h ▸ h2 i⟩
    · intro h; exact ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2 rfl⟩
  refine ⟨fun x hx => ?_, fun B hB hBb => ?_⟩
  · obtain ⟨s, s', hs, hs', hf, hf'⟩ := GlobalTheory.T.globalFrameStabilizer_acts_unitriangular _ _ _ G x hx
    have hZs := (GlobalTheory.T.hermitianStabiliser_rational_unitriangular_pairs _ _ _ G s s' hs hs').2 ⟨x, hx, hf, hf'⟩
    exact ⟨s', (up s').1 hs', hf', hb1 s s' ((up s).1 hs) ((up s').1 hs') hZs⟩
  · obtain ⟨s, hs, hZs⟩ := hb2 B hB hBb
    obtain ⟨h, hh, -, hh'⟩ := (GlobalTheory.T.hermitianStabiliser_rational_unitriangular_pairs _ _ _ G s B ((up s).2 hs) ((up B).2 hB)).1 hZs
    refine ⟨h, ⟨hh, hh'⟩, fun y ⟨hy, hy'⟩ => ?_⟩
    have h1 : h⁻¹ * y = 1 := by
      refine GlobalTheory.T.rationalCommonStabiliser_eq_one_of_fixes_second_frame _ _ _ G _ (G.St.mul_mem (G.St.inv_mem hh) hy) fun b => ?_
      show h.symm (y (G.f' b)) = G.f' b
      rw [hy', ← hh' b, LinearEquiv.symm_apply_apply]
    calc y = h * (h⁻¹ * y) := by group
      _ = h := by rw [h1, mul_one]

end GlobalTheory.HL.StCoord
end

section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.coordinateLattice_selfDual_isFullRank : ∀ (D : D7) (X : HidaSetting D), IsLat ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) := by
  first | exact @GlobalTheory.St.G.coordLat_isLat | exact GlobalTheory.St.G.coordLat_isLat | (intros; apply GlobalTheory.St.G.coordLat_isLat <;> assumption)
end

section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.splitRowLattice_middle_iff_gluedLattice : ∀ (D : D7) (u : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), 1 ≤ Tu D u → IsBase D u F0 → IsRowLat D F0 Λ → (IsSplit D F0 Λ → Λ ⊓ toO (hS D) (Wb D) ∈ glueSet D u (L0X D Λ (lf D F0)) ∧ Lsub Λ (lf D F0) = (Λ ⊓ toO (hS D) (Wb D)) ⊔ toO (hS D) F0.X) ∧ (∀ L' : LatW D, ∀ L ∈ glueSet D u L', IsRowLat D F0 (XS D F0 ⊔ L ⊔ YS D) ∧ IsSplit D F0 (XS D F0 ⊔ L ⊔ YS D) ∧ (XS D F0 ⊔ L ⊔ YS D) ⊓ toO (hS D) (Wb D) = L) := by
  first | exact @GlobalTheory.LoopC.RowGlue.main | exact GlobalTheory.LoopC.RowGlue.main | (intros; apply GlobalTheory.LoopC.RowGlue.main <;> assumption)
end

section

noncomputable section
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
namespace GlobalTheory.TypeAsm.FramePf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ka_div (D : D7) : D.host.ka / (2 * Real.pi) = (2 * D.host.v)⁻¹ := by
  have h0 : 0 < D.host.rdE := GlobalTheory.TypeAsm.GramPf.rdE_pos' D
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [Formalism.BasicNotions.Host.ka, Formalism.BasicNotions.Host.v]
  field_simp

theorem two_v_pos (D : D7) : 0 < 2 * D.host.v := by
  have h0 : 0 < D.host.rdE := GlobalTheory.TypeAsm.GramPf.rdE_pos' D
  simp only [Formalism.BasicNotions.Host.v]
  linarith

theorem phiV_frame (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau) (a : Fin D.R.rS) :
    GlobalTheory.TypeAsm.phiV C τ (X.eX a) =
                 (((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) ∧
    GlobalTheory.TypeAsm.phiV C τ (X.fY a) =
                 ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  obtain ⟨hQiQ, _, _, hfr⟩ := C.isT τ
  obtain ⟨h1, h2⟩ := hfr a a rfl
  have hc : ((2 * D.host.v) ^ (D.R.rS - a.val) : ℝ) ≠ 0 := pow_ne_zero _ (two_v_pos D).ne'
  have hfp : frS D ^ (D.R.rS - a.val) = ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) := by
    unfold frS
    rw [ka_div, ← Complex.ofReal_pow, inv_pow]
  unfold GlobalTheory.TypeAsm.phiV
  constructor
  · have e : rv X.B.I (vOf X τ) (X.crd (X.eX a)) =
        ((((2 * D.host.v) ^ (D.R.rS - a.val)) : ℝ) : ℂ) • (C.Q τ *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1) := by
      rw [h1, hfp, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hc, Complex.ofReal_one, one_smul]
      rfl
    rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec]
    rfl
  · have e : rv X.B.I (vOf X τ) (X.crd (X.fY a)) =
        ((((2 * D.host.v) ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • (C.Q τ *ᵥ Pi.single (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) 1) := by
      rw [h2, hfp, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_inv, inv_inv, smul_smul,
        ← Complex.ofReal_mul, inv_mul_cancel₀ hc, Complex.ofReal_one, one_smul]
      rfl
    rw [e, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec]
    rfl

end GlobalTheory.TypeAsm.FramePf
end
end

section


theorem _root_.GlobalTheory.T.orbitalIntegralTensorBoundHyp_proof : GlobalTheory.TypeAsm.TensC := by
  first | exact @GlobalTheory.TensHS.tensC_holds | exact GlobalTheory.TensHS.tensC_holds | (intros; apply GlobalTheory.TensHS.tensC_holds <;> assumption)
end

section


theorem _root_.GlobalTheory.T.strict_fundamentalSet_integralStabilizer_exists : GlobalTheory.TypeAsm.FundC := by
  first | exact @GlobalTheory.TypeAsm.fundC_holds | exact GlobalTheory.TypeAsm.fundC_holds | (intros; apply GlobalTheory.TypeAsm.fundC_holds <;> assumption)
end

section


theorem _root_.GlobalTheory.T.definite_quotient_model_exists : GlobalTheory.TypeAsm.EmbC := by
  first | exact @GlobalTheory.TypeAsm.embC | exact GlobalTheory.TypeAsm.embC | (intros; apply GlobalTheory.TypeAsm.embC <;> assumption)
end

section


theorem _root_.GlobalTheory.T.gapC_holds : GlobalTheory.TypeAsm.GapC := by
  first | exact @GlobalTheory.TypeAsm.gapC | exact GlobalTheory.TypeAsm.gapC | (intros; apply GlobalTheory.TypeAsm.gapC <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.parameter_size_constraints : ∀ (Ca Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D), HostC →
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → 1 ≤ C' → 1 ≤ Cl → CT ≤ Ca →
    Module.finrank ℚ D.host.E = 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E ∧ D.R.m = 2 * D.R.rS + 2 ∧ Cl ≤ (D.R.m : ℝ) ∧
    D.R.m ^ 4 ≤ Formalism.HermitianLatticesTheory.fDeg D.host.E ∧ D.R.m ^ 5 * Formalism.HermitianLatticesTheory.fDeg D.host.E ≤ D.R.k ∧
    Cl * ((D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b) ≤ D.R.k ∧ Real.log (Formalism.HermitianLatticesTheory.fDeg D.host.E : ℝ) ≤ Real.sqrt D.R.rS ∧
    2 ≤ large₂.sc.b ∧ 1 ≤ Formalism.HermitianLatticesTheory.vInv D.host.E ∧ 2 * Formalism.HermitianLatticesTheory.vInv D.host.E ≤ large₂.sc.b ∧
    ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (gS D : ℝ) ∧
    ∀ u : D.what₂.Word, 1 ≤ Tu D u ∧ (Tu D u : ℝ) ≤ large₂.sc.b ^ (Ca * (D.R.m : ℝ)) := by
  first | exact @GlobalTheory.TypeAsm.pairsPar | exact GlobalTheory.TypeAsm.pairsPar | (intros; apply GlobalTheory.TypeAsm.pairsPar <;> assumption)
end

section

open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowsOrb.ExGenus

open Formalism.HermitianLatticesTheory

private theorem full_of_unimodular {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) (hu : IsUnimodular h L) :
    Submodule.IsFullLattice K L := by
  letI := hL
  refine { span_eq_top := ?_ }
  let W := Submodule.span K (L : Set V)
  change W = ⊤
  by_contra hw
  let b := Module.finBasis K V
  let e : V ≃ₗ⋆[K] V := (b.equivFun.trans (starLinearEquiv K)).trans b.equivFun.symm
  let g : V →ₗ[K] Module.Dual K W :=
    (LinearMap.domRestrict' W).comp (h.comp e.toLinearMap)
  have hd : Module.finrank K (Module.Dual K W) < Module.finrank K V := by
    rw [Subspace.dual_finrank_eq]
    exact Submodule.finrank_lt hw
  obtain ⟨x, hx, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hd)
  have hm (a : K) : a • e x ∈ L := by
    rw [← hu, dualBasic_mem_dual]
    intro y hy
    have hz : h (e x) y = 0 :=
      congrArg (fun f : Module.Dual K W => f ⟨y, Submodule.subset_span hy⟩)
        (LinearMap.mem_ker.mp hx)
    have hz' : h y (e x) = 0 := by
      exact hs.eq_iff.mp hz
    simp [LinearMap.map_smul, hz']
  let i : K →ₗ[𝓞 K] L :=
    ((LinearMap.toSpanSingleton K _ (e x)).restrictScalars (𝓞 K)).codRestrict L hm
  letI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL.fg
  letI : Module.Finite (𝓞 K) K := Module.Finite.of_injective i fun a b hab =>
    smul_left_injective K (fun hzero => hx0 (e.map_eq_zero_iff.mp hzero))
      (congrArg Subtype.val hab)
  exact RingOfIntegers.not_isField K
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 K) K) (Field.toIsField K))


theorem mem_genus_of_isUnimodular : ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.TypeAsm.Std D large₂ → ∀ (X : HidaSetting D) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ → Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → Λ ∈ Formalism.HermitianLatticesTheory.genus (VS D).hT (VS D).L0 := by
  intro D large₂ hS _ _ Λ hΛ hU
  have hCM : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := (GlobalTheory.TypeAsm.hostC D large₂ hS).1

  have hloc : ∀ L : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsLattice D.host.E L →
      (Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT L ↔
        ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → Formalism.HermitianLatticesTheory.IsUnimodularAt (VS D).hT P L) :=
    fun L hL => (Formalism.HermitianLatticesTheory.locDual (𝓞 D.host.E) D.host.E (VS D).V (VS D).hT (VS D).herm
      Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range L hL.fg).2
  have hΛfull := full_of_unimodular (VS D).hT (VS D).herm hΛ hU
  have hL0full := full_of_unimodular (VS D).hT (VS D).herm
    (VS D).standardTuple_isLattice (VS D).baseLattice_isUnimodular
  refine ⟨hΛfull, fun P hP => ?_⟩

  exact GlobalTheory.Mass.UnimodLoc.exists_isom_of_isUnimodularAt D.host.E (VS D).V (VS D).hT hCM (VS D).herm
    (VS D).nondeg (VS D).L0 Λ hL0full hΛfull P hP
    ((hloc _ (VS D).standardTuple_isLattice).1 (VS D).baseLattice_isUnimodular P hP) ((hloc Λ hΛ).1 hU P hP)

end GlobalTheory.RowsOrb.ExGenus
end

section


theorem _root_.GlobalTheory.T.rowLattice_term_adaptedNormalForm : GlobalTheory.TypeAsm.TermC := by
  first | exact @GlobalTheory.TermRow.termC_holds | exact GlobalTheory.TermRow.termC_holds | (intros; apply GlobalTheory.TermRow.termC_holds <;> assumption)
end

section

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
variable {D : D7} {X : HidaSetting D}

def frCls {Y : Full X} {u : D.what₂.Word} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (t : GTu Y u) :
    Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS) :=
  {G | GlobalTheory.DegAsm.FrEqv (F0 X u) Λ (Ft t) G}

def clsOm (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (b : Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS)) : ℝ :=
  if h : ∃ t : GTu Y u, t.lam = Λ ∧ frCls Λ t = b then omT h.choose else 0

theorem frCls_eq_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) {Y : Full X} {u : D.what₂.Word}
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (t t' : GTu Y u) :
    frCls Λ t = frCls Λ t' ↔ GlobalTheory.DegAsm.FrEqv (F0 X u) Λ (Ft t) (Ft t') := by
  have hE := (GlobalTheory.DegAsm.frEqv_invariants D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) (dI D) Λ).1
  constructor
  · intro h
    have : Ft t' ∈ frCls Λ t := by rw [h]; exact hE.refl _
    exact this
  · intro h
    ext G
    exact ⟨fun hG => hE.trans (hE.symm h) hG, fun hG => hE.trans h hG⟩

theorem clsOm_nonneg (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) (b : Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS)) : 0 ≤ clsOm Y u Λ b := by
  unfold clsOm
  split_ifs with h
  · exact ((GlobalTheory.DegAsm.WeightInf.main D.host.E (VS D).V (HV D) hK D.R.rS).2 _ _ _ _).1
  · exact le_rfl

theorem clsOm_frCls (hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E) {Y : Full X} {u : D.what₂.Word}
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (t : GTu Y u) (ht : t.lam = Λ) : clsOm Y u Λ (frCls Λ t) = omT t := by
  have hex : ∃ s : GTu Y u, s.lam = Λ ∧ frCls Λ s = frCls Λ t := ⟨t, ht, rfl⟩
  unfold clsOm
  rw [dite_eq_left hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have hq := (frCls_eq_iff hK Λ _ _).1 h2
  have := ((GlobalTheory.DegAsm.frEqv_invariants D.host.E (VS D).V (HV D) hK D.R.rS (F0 X u) (dI D) Λ).2 _ _ hq).1
  unfold omT
  rw [h1, ht]
  exact this
end

end GlobalTheory.TypeAsm.PerRow
end
end
