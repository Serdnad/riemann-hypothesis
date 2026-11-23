module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramLocPfB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle049
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle341
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle065

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.KappaOffDiagonal Formalism.L2.SG.RowsConc

noncomputable section

namespace GlobalTheory.Core.Deg

theorem pgC_le_two_at_record : ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X),
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → PgC Y ≤ 2 := by
  intro C' Cl Cg cb Cw cT CT C0 D large₂ X Y hH
  have hPg := Formalism.L2.SG.Pf.SatGram.tt_eq' Formalism.L2.SG.Pf.splitPrimeLoc_holds
    Formalism.L2.SG.Pf.SatGramLoc.reduction_structure_holds Y.TR
  unfold Formalism.L2.SG.RowsConc.PgC
  rw [hPg, Formalism.L2.SG.KappaOffDiagonal.PgLe.finrank_F X]
  obtain ⟨⟨hS0, -, -⟩, hP⟩ := hH
  obtain ⟨-, -, -, hfk, -⟩ := hS0
  have hg := hP.2.1
  have hb := Formalism.MainNotions.KappaEndpoints.two_le_scale_b D large₂
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have h0 := Formalism.L2.SG.KappaOffDiagonal.PgLe.one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 0 : ℝ) D.R.f hk hb (hg 0).1 hf
  have h1 := Formalism.L2.SG.KappaOffDiagonal.PgLe.one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 1 : ℝ) D.R.f hk hb (hg 1).1 hf
  calc (1 + 3 / (D.host.g 0 : ℝ)) ^ D.R.f * (1 + 3 / (D.host.g 1 : ℝ)) ^ D.R.f
      ≤ Real.exp (1 / 4) * Real.exp (1 / 4) :=
        mul_le_mul h0 h1 (by positivity) (Real.exp_pos _).le
    _ ≤ 2 := Formalism.L2.SG.KappaOffDiagonal.PgLe.exp_quarter_mul_exp_quarter_le_two

end GlobalTheory.Core.Deg
end
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

noncomputable section
namespace GlobalTheory.Core.Deg

theorem exp_le_inv_one_sub_pg (x : ℝ) (hx1 : x < 1) : Real.exp x * (1 - x) ≤ 1 := by
  have h := Real.add_one_le_exp (-x)
  have hp := Real.exp_pos x
  have : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith

theorem one_factor_sharp (k b g : ℝ) (f : ℕ) (hk : 1 ≤ k) (hb : 2 ≤ b) (hg : (k * b) ^ 8 ≤ g) (hf : (f : ℝ) ≤ k) :
    (1 + 3 / g) ^ f ≤ Real.exp (3 / 256) := by
  have hb8 : (256 : ℝ) ≤ b ^ 8 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hb 8
    norm_num at this ⊢; linarith
  have hk8 : k ≤ k ^ 8 := le_self_pow₀ hk (by norm_num)
  have hkb : 256 * k ≤ (k * b) ^ 8 := by
    rw [mul_pow]
    have : 256 * k ≤ k ^ 8 * 256 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hb8 (by positivity : (0 : ℝ) ≤ k ^ 8)]
  have hg0 : 0 < g := by nlinarith
  have hx : (f : ℝ) * (3 / g) ≤ 3 / 256 := by
    rw [mul_div_assoc', div_le_div_iff₀ hg0 (by norm_num)]
    nlinarith
  calc (1 + 3 / g) ^ f ≤ Real.exp (3 / g) ^ f := by
        apply pow_le_pow_left₀ (by positivity)
        have := Real.add_one_le_exp (3 / g)
        linarith
    _ = Real.exp (f * (3 / g)) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (3 / 256) := Real.exp_le_exp.2 hx

theorem exp_pair_le_six_fifths : Real.exp (3 / 256) * Real.exp (3 / 256) ≤ 6 / 5 := by
  rw [← Real.exp_add]
  have h := exp_le_inv_one_sub_pg (3 / 256 + 3 / 256) (by norm_num)
  have hp := Real.exp_pos (3 / 256 + 3 / 256 : ℝ)
  norm_num at h ⊢
  nlinarith

theorem pgC_le_six_fifths : ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X),
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → PgC Y ≤ 6 / 5 := by
  intro C' Cl Cg cb Cw cT CT C0 D large₂ X Y hH
  have hPg := Formalism.L2.SG.Pf.SatGram.tt_eq' Formalism.L2.SG.Pf.splitPrimeLoc_holds
    Formalism.L2.SG.Pf.SatGramLoc.reduction_structure_holds Y.TR
  unfold Formalism.L2.SG.RowsConc.PgC
  rw [hPg, Formalism.L2.SG.KappaOffDiagonal.PgLe.finrank_F X]
  obtain ⟨⟨hS0, -, -⟩, hP⟩ := hH
  obtain ⟨-, -, -, hfk, -⟩ := hS0
  have hg := hP.2.1
  have hb := Formalism.MainNotions.KappaEndpoints.two_le_scale_b D large₂
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have h0 := one_factor_sharp (D.R.k : ℝ) large₂.sc.b (D.host.g 0 : ℝ) D.R.f hk hb (hg 0).1 hf
  have h1 := one_factor_sharp (D.R.k : ℝ) large₂.sc.b (D.host.g 1 : ℝ) D.R.f hk hb (hg 1).1 hf
  calc (1 + 3 / (D.host.g 0 : ℝ)) ^ D.R.f * (1 + 3 / (D.host.g 1 : ℝ)) ^ D.R.f
      ≤ Real.exp (3 / 256) * Real.exp (3 / 256) :=
        mul_le_mul h0 h1 (by positivity) (Real.exp_pos _).le
    _ ≤ 6 / 5 := exp_pair_le_six_fifths

end GlobalTheory.Core.Deg
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TorusCong

open Formalism.L2.SG.Pf.unitaryCongruence GlobalTheory.St.G.FrameClose

theorem one_sub_T_zmod : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), ∃ M : ℕ, Nat.Coprime M X.B.g ∧ ZMod' X.B.I X.B.g ((M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) := by
  intro D X u
  obtain ⟨c', hc', hm⟩ := X.xu_z u
  obtain ⟨-, hz0, -⟩ := X.vectorsInLattice
  set z' : VA X.B.I := X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) with hz'
  have hm' : (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) ∈ mL X.B.I X.B.g := hm
  have hzz : hA X.B.I z' z' = -(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    rw [hz', Formalism.L2.SG.PoincareInHH.Cut.hA_fmat, HidaSetting.zR, Formalism.L2.SG.PoincareInHH.Cut.hA_crd, X.zu_norm,
      map_neg, map_natCast, map_neg, map_natCast]
  set m : VA X.B.I := (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (z' - X.z0) with hmdef
  set w0 : VA X.B.I := (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.z0 with hw0def
  have hw0 : w0 ∈ X.B.I.Lf := nat_smul_mem c' hz0
  have hw : m + w0 ∈ X.B.I.Lf := add_mem (mL_le X.B.g hm') hw0
  have h1 : ZMod' X.B.I X.B.g (hA X.B.I m (m + w0)) := zmod_of_mL hm' hw
  have h2 : ZMod' X.B.I X.B.g (hA X.B.I w0 m) := by
    rw [hA_symm]; exact Z_sig _ _ (zmod_of_mL hm' hw0)
  have hsplit : hA X.B.I (m + w0) (m + w0) - hA X.B.I w0 w0 = hA X.B.I m (m + w0) + hA X.B.I w0 m := by
    rw [hA_add_left, hA_add_right, hA_add_right]; ring
  have hmw : m + w0 = (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • z' := by
    rw [hmdef, hw0def, ← smul_add, sub_add_cancel]
  have hsq : ∀ x : VA X.B.I, hA X.B.I ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x) ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x)
      = (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * hA X.B.I x x := by
    intro x; rw [hA_nat_left, hA_smul_right]; ring
  have hA1 : ZMod' X.B.I X.B.g ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I z' z' - hA X.B.I X.z0 X.z0)) := by
    have e : (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I z' z' - hA X.B.I X.z0 X.z0) =
        hA X.B.I m (m + w0) + hA X.B.I w0 m := by
      rw [← hsplit, hmw, hw0def, hsq, hsq]; ring
    rw [e]; exact Z_add _ _ h1 h2
  have hA2 : ZMod' X.B.I X.B.g ((c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I X.z0 X.z0 + 1)) := by
    have := Z_smul X.B.I X.B.g (natCast_mem (IntAf X.B.I.F X.B.I.E) (c' ^ 2)) X.formsAtZero.1
    simpa [Nat.cast_pow] using this
  refine ⟨c' ^ 2, Nat.Coprime.pow_left 2 hc', ?_⟩
  have e : ((c' ^ 2 : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) =
      (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I z' z' - hA X.B.I X.z0 X.z0) +
      (c' : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ^ 2 * (hA X.B.I X.z0 X.z0 + 1) := by
    rw [hzz, Nat.cast_pow]; ring
  rw [e]; exact Z_add _ _ hA1 hA2

end GlobalTheory.TorusCong
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ScalW

theorem hMat_mem_hfin_comm : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (h : X.B.I.Gf), (∀ a, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.eV X a) = GlobalTheory.ScalW.eV X a ∧ GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.fV X a) = GlobalTheory.ScalW.fV X a) → GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.zV X u) = GlobalTheory.ScalW.zV X u → X.B.I.fmat h = GlobalTheory.ScalW.hMat X u c → h ∈ Hfin X u ∧ ∀ h' ∈ Hfin X u, h * h' = h' * h := by
  intro D X u c h hef hz hh
  have hfixV : ∀ v ∈ fixSet X u, GlobalTheory.ScalW.prj X u (incl X.B.I v) = incl X.B.I v := by
    rintro v ((⟨a, rfl⟩ | ⟨a, rfl⟩) | hv)
    · exact (hef a).1
    · exact (hef a).2
    · rw [Set.mem_singleton_iff.1 hv]; exact hz
  have hmem : h ∈ Hfin X u := by
    intro v hv
    show X.B.I.fmat h *ᵥ incl X.B.I v = incl X.B.I v
    rw [hh, hMat_mulVec, hfixV v hv, ← add_smul, add_sub_cancel, one_smul]
  refine ⟨hmem, fun h' hh' => ?_⟩
  have hg : ∀ v ∈ fixSet X u, X.B.I.fmat h' *ᵥ incl X.B.I v = incl X.B.I v :=
    Formalism.L2.SG.PoincareInHH.Cut.hfin_fix X u ⟨h', hh'⟩
  have hgi : ∀ v ∈ fixSet X u, X.B.I.fmat h'⁻¹ *ᵥ incl X.B.I v = incl X.B.I v :=
    Formalism.L2.SG.PoincareInHH.Cut.hfin_fix_inv X u ⟨h', hh'⟩
  have hE := Formalism.L2.SG.PoincareInHH.Cut.eR_mem_fix X u
  have hF := Formalism.L2.SG.PoincareInHH.Cut.fR_mem_fix X u
  have hZ := Formalism.L2.SG.PoincareInHH.Cut.zR_mem_fix X u
  have hmv : ∀ v, v ∈ fixSet X u → ∀ y, hA X.B.I (incl X.B.I v) (X.B.I.fmat h' *ᵥ y) = hA X.B.I (incl X.B.I v) y := by
    intro v hv y
    rw [GlobalTheory.St.G.FrameClose.hA_move, hgi v hv]
  have hprj : ∀ y, prj X u (X.B.I.fmat h' *ᵥ y) = prj X u y := by
    intro y
    simp only [prj, eV, fV, zV, hmv _ (hE _), hmv _ (hF _), hmv _ hZ]
  have hprj2 : ∀ y, X.B.I.fmat h' *ᵥ prj X u y = prj X u y := by
    intro y
    simp only [prj, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, eV, fV, zV,
      hg _ (hE _), hg _ (hF _), hg _ hZ]
  have hM : X.B.I.fmat (h * h') = X.B.I.fmat (h' * h) := by
    rw [Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, hh]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun y => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hMat_mulVec, hMat_mulVec, hprj, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hprj2]
  exact Subtype.ext (Units.ext hM)

end GlobalTheory.ScalW
end
