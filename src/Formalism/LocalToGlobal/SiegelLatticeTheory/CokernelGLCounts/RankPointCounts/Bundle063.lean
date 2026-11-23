module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle056
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PtCellUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle052
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.VolumeIndexBStable
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle059
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle054
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle058
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle061
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.LocalCountConclusions.LocalCountZeroGlobalHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.NGCut.VanishingOrbitalPoints

theorem stepNormOne_of_ooVanish
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X)) :
    Formalism.L2.SG.NGCut.StepNormOne :=
  Formalism.L2.SG.NGCut.LeadingMinorIntegrality.stepNormOne_of hOV fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u'

theorem stepPoints_of_ooVanish
    (hOV : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X)) :
    Formalism.L2.SG.NGCut.StepPoints :=
  Formalism.L2.SG.NGCut.PtPf.stepPoints_of hOV fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u'



end Formalism.L2.SG.NGCut.VanishingOrbitalPoints
end
end

section

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def CondX (w : Point D.host.E (D.R.rS + 1)) (X : MatR D) : Prop :=
  ∀ a c : Fin (D.R.rS + 1), a < c → blkOf w.1 a.val = blkOf w.1 c.val →
    X (pinv w c) (pinv w a) ∈ ddPow D (c.val - a.val) ∧ bt D X⁻¹ a c ∈ ddPow D (c.val - a.val) ∧
      X (pinv w c) (pinv w a) - D.conjF (bt D X⁻¹ a c) ∈ qdPow D (c.val - a.val)

theorem entryShape_iff (w : Point D.host.E (D.R.rS + 1)) {β b : MatR D} (hβ : IsLoUni β) (hb : IsUpUni b)
    (hW : β * ptMat w * b = ptMat w) :
    EntryShape D β b ↔ CondX w ((ptMat w)⁻¹ * β * ptMat w) := by
  obtain ⟨hXb, hX, hXB⟩ := X_of_st w hβ hb hW
  set X := (ptMat w)⁻¹ * β * ptMat w with hXdef
  have hbX : b = X⁻¹ := by
    rw [hXb, Matrix.nonsing_inv_nonsing_inv _ (by rw [upU_det hb]; exact isUnit_one)]

  have hβX : β = ptMat w * X * (ptMat w)⁻¹ := by
    have hu := ptMat_isUnit w
    rw [hXdef, show ptMat w * ((ptMat w)⁻¹ * β * ptMat w) * (ptMat w)⁻¹ =
      (ptMat w * (ptMat w)⁻¹) * β * (ptMat w * (ptMat w)⁻¹) by simp only [Matrix.mul_assoc],
      Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]
  have hβij : ∀ i j, β i j = cv w i * X (pinv w i) (pinv w j) * (cv w j)⁻¹ := by
    intro i j; rw [hβX, conj'_apply]

  have hXiB : IsBlockDiagonalMatrix w X⁻¹ := by
    have hβi : IsLoUni β⁻¹ := by
      have := loU_inv (show LoU β from hβ); exact this
    have hW' : β⁻¹ * ptMat w * X = ptMat w := by
      have hu := ptMat_isUnit w
      have hβd : IsUnit β.det := by rw [loU_det (show LoU β from hβ)]; exact isUnit_one
      rw [hXdef, show β⁻¹ * ptMat w * ((ptMat w)⁻¹ * β * ptMat w) = β⁻¹ * (ptMat w * (ptMat w)⁻¹) * β * ptMat w by
        simp only [Matrix.mul_assoc], Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, Matrix.nonsing_inv_mul _ hβd,
        Matrix.one_mul]
    obtain ⟨h1, -, h3⟩ := X_of_st w hβi hX hW'
    have hXi : (ptMat w)⁻¹ * β⁻¹ * ptMat w = X⁻¹ := h1
    rw [← hXi]; exact h3
  rw [hbX]
  constructor
  · intro h a c hac hs
    obtain ⟨h1, h2, h3⟩ := h c a hac
    have hcv : cv w c = cv w a := (pval_eq_blk w a c hs).symm
    have key : ∀ x : D.host.E, cv w a * (x * (cv w a)⁻¹) = x := fun x => by
      rw [mul_comm x, ← mul_assoc, mul_inv_cancel₀ (cv_ne w a), one_mul]
    rw [hβij, hcv, mul_assoc, key] at h1 h3
    exact ⟨h1, h2, h3⟩
  · intro h i j hji
    by_cases hs : blkOf w.1 j.val = blkOf w.1 i.val
    · obtain ⟨h1, h2, h3⟩ := h j i hji hs
      have hcv : cv w i = cv w j := (pval_eq_blk w j i hs).symm
      have key : ∀ x : D.host.E, cv w j * (x * (cv w j)⁻¹) = x := fun x => by
        rw [mul_comm x, ← mul_assoc, mul_inv_cancel₀ (cv_ne w j), one_mul]
      rw [hβij, hcv, mul_assoc, key]
      exact ⟨h1, h2, h3⟩
    · have hs' : blkOf w.1 (pinv w i).val ≠ blkOf w.1 (pinv w j).val := by
        rw [blkOf_pinv, blkOf_pinv]; exact fun e => hs e.symm
      have hb0 : X⁻¹ j i = 0 := hXiB j i hs
      have hbt : bt D X⁻¹ j i = 0 := by simp [bt, hb0]
      rw [hβij, hXB _ _ hs', mul_zero, zero_mul, hbt, map_zero, sub_zero]
      exact ⟨FractionalIdeal.zero_mem _, FractionalIdeal.zero_mem _, FractionalIdeal.zero_mem _⟩

theorem mem_stabInt_iff_X (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word)
    (w : Point D.host.E (D.R.rS + 1)) (β : GLR D) (hβ : IsLoUni (β : MatR D)) {b : MatR D} (hb : IsUpUni b)
    (hW : (β : MatR D) * ptMat w * b = ptMat w) :
    β ∈ stabInt D u u' δ M w ↔ CondX w ((ptMat w)⁻¹ * (β : MatR D) * ptMat w) := by
  rw [stabIntShape D δ M hA u u' w β]
  constructor
  · rintro ⟨-, b', hb', hW', hE⟩
    exact (entryShape_iff w hβ hb' hW').1 hE
  · intro h
    exact ⟨hβ, b, hb, hW, (entryShape_iff w hβ hb hW).2 h⟩

end Formalism.L2.SG.Pf.StabIntSh
end
end

section

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem neg_one_pow_sq {R : Type*} [CommRing R] (k : ℕ) : (-1 : R) ^ k * (-1) ^ k = 1 := by
  rw [← mul_pow]; simp

theorem ρOf_eq (A B : Formalism.L2.SG.PairVal.MatR D) :
    Formalism.L2.SG.Pf.StabShape.ρOf Zd.δ Zd.M p A B =
      Formalism.L2.SG.LsDatumB.sgnP p * Formalism.L2.SG.Pf.TupGlob.locR Zd p A B * Formalism.L2.SG.LsDatumB.sgnP p := by
  unfold Formalism.L2.SG.Pf.StabShape.ρOf Formalism.L2.SG.Pf.TupGlob.locR
  cases hs : (Zd.M p).split with
  | none =>
    ext i j
    simp only [Formalism.L2.SG.Pf.StabShape.ρL, Formalism.L2.SG.LsDatumB.sgnP, Matrix.of_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.map_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, map_pow, map_neg, map_one]
    rw [frFac_cf, frFac_cf, inv_alg_cf]
    ring
  | some g =>
    ext i j
    apply g.e.injective
    simp only [Formalism.L2.SG.Pf.StabShape.ρG, glue, Formalism.L2.SG.LsDatumB.sgnP, Matrix.of_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.map_apply, Matrix.transpose_apply, Sg, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, map_pow, map_neg, map_one,
      AlgEquiv.apply_symm_apply, RingHom.comp_apply, adeleInfiniteComponent_apply, adele_ext_components, frFac_cf, AlgEquiv.commutes,
      Prod.algebraMap_apply, Prod.fst_mul, Prod.snd_mul, Prod.pow_fst, Prod.pow_snd, Prod.fst_neg, Prod.snd_neg,
      Prod.fst_one, Prod.snd_one, Algebra.algebraMap_self, RingHom.id_apply]
    have h2 : ∀ a, cfi Zd p a = (cf Zd p a)⁻¹ := fun a => eq_inv_of_mul_eq_one_right (cf_cfi Zd p a)
    have hs2 : ∀ k : ℕ, ((-1 : (D.s.atP p).Fp) ^ k) * (-1) ^ k = 1 := neg_one_pow_sq
    ext
    · simp only [Prod.fst_mul, Prod.pow_fst, Prod.fst_neg, Prod.fst_one, h2, div_eq_mul_inv]; ring
    · simp only [Prod.snd_mul, Prod.pow_snd, Prod.snd_neg, Prod.snd_one, h2, div_eq_mul_inv]
      linear_combination (-((g.e ((D.s.atP p).ιE (A j i))).2 * cf Zd p j * (cf Zd p i)⁻¹)) *
          hs2 (D.R.rS - i.val) +
        (-((g.e ((D.s.atP p).ιE (A j i))).2 * cf Zd p j * (cf Zd p i)⁻¹) *
          ((-1 : (D.s.atP p).Fp) ^ (D.R.rS - i.val) * (-1) ^ (D.R.rS - i.val))) * hs2 (D.R.rS - j.val)

end Formalism.L2.SG.Pf.FibD
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolAct

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.PairVal
  Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def sbs {D : Formalism.BasicNotions.D7} (b : MatR D) : MatR D := Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS * b * Formalism.L2.SG.Pf.StabilizerIndexVolumes.sgnM D.R.rS

def LiftData (γ : TermDef.Term D u u' F0 what₂) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (a' : GLR D) (b : MatR D) (ν m : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) : Prop :=
  IsLoUni (a' : MatR D) ∧ IsUpUni b ∧ (a' : MatR D) * ZhatOM (ZhatL (lf D F0) F') * b = ZhatOM (ZhatL (lf D F0) F') ∧
    Formalism.L2.SG.Pf.StabIntSh.EntryShape D (a' : MatR D) b ∧
    ν ∈ NLam γ.lam (lf D F0) ∧ m ∈ NLam γ.lam F' ∧
    (∀ c, ν (frame (lf D F0) c) = ∑ d, (a' : MatR D).conjTranspose d c • frame (lf D F0) d) ∧
    (∀ c, m (frame F' c) = ∑ d, sbs b d c • frame F' d) ∧
    F₂ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam (ZhatL (lf D F0) F') ∧
    TermDef.Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls F₂ ∧
    ∀ c, frame F₂ c = ν⁻¹ (m (frame F' c))

def MoveCZ : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ (a' : GLR D) (b : MatR D), IsLoUni (a' : MatR D) → IsUpUni b →
      (a' : MatR D) * ZhatOM (ZhatL (lf D F0) F') * b = ZhatOM (ZhatL (lf D F0) F') →
      Formalism.L2.SG.Pf.StabIntSh.EntryShape D (a' : MatR D) b →
      ∃ ν m F₂, LiftData u u' F0 what₂ γ F' a' b ν m F₂

def OntoCZ : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ F'' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam (ZhatL (lf D F0) F'),
      TermDef.Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls F'' →
      ∃ (a' : GLR D) (b : MatR D) (ν m : (VS D).V ≃ₗ[D.host.E] (VS D).V), LiftData u u' F0 what₂ γ F' a' b ν m F''

def FibreCZ : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∀ (a₁ : GLR D) (b₁ : MatR D) (ν₁ m₁ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F₁ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (a₂ : GLR D) (b₂ : MatR D) (ν₂ m₂ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (x₁ x₂ : GLR D), (x₁ : MatR D) = L⁻¹ * (a₁ : MatR D) * L → (x₂ : MatR D) = L⁻¹ * (a₂ : MatR D) * L →
      LiftData u u' F0 what₂ γ F' a₁ b₁ ν₁ m₁ F₁ → LiftData u u' F0 what₂ γ F' a₂ b₂ ν₂ m₂ F₂ →
      (CntLocal.NilradicalFlagMoved F0 γ.lam F₁ F₂ ↔ x₁⁻¹ * x₂ ∈ PairVal.stabAut D u u' F0 what₂ γ F' L)

end Formalism.L2.SG.Pf.ZsVolAct

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V))

theorem locFullC_holds : LocFullC Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ F'₂ φ φ' hF hT p M hM
  exact Formalism.L2.SG.Pf.LocalDenominators.exists_isLattice_eq_localLattice Zd p M hM.1.1.1.1 hM.1.1.1.2.1

theorem patchC_holds : PatchC Zd u u' F0 what₂ := patchC_of_full Zd (locFullC_holds Zd u u' F0 what₂)

variable {Zd u u' F0 what₂}

theorem frGlob_of_fstar (hA : FStarC Zd u u' F0 what₂) : Formalism.L2.SG.Pf.PCount.FrGlob Zd u u' F0 what₂ :=
  frGlob_of Zd hA (patchC_holds Zd u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BwdCut

def liftF {T' : D.host.E} (F' : LFlag (D.sp.Y 0) D.R.rS T') : LFlag (D.sp.Y 0) D.R.rS T' := ⟨F'.fl, F'.fl.z⟩

theorem isom_of_N0F {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0) : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
  hn.1

theorem mapL_lf {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0) :
    mapL n (isom_of_N0F hn) (lf D F0) = lf D F0 := by
  apply mapL_eq_self
  · intro a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simpa [frame, FlagG.fvec, lf] using hn.2.2.2.2
    · simpa [frame, FlagG.fvec, lf] using hn.2.2.2.1 i
  · exact hn.2.2.2.2

theorem zhatL_mapL_N0F {T' : D.host.E} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') : ZhatL (lf D F0) (mapL n (isom_of_N0F hn) F') = ZhatL (lf D F0) F' := by
  conv_lhs => rw [← mapL_lf hn]
  exact zhat_mapL n (isom_of_N0F hn) (lf D F0) F'

theorem mem_EZ_of {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ unipotentFrameFixers F0)
    (Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Formalism.HermitianLatticesTheory.gmap n Λ₂ = Λ)
    (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Z : PairVal.MatR D)
    (hT : IsTerm Λ₂ (gS D) (lf D F0) F'₂) (hA : AdmWit Λ₂ (gS D) (lf D F0) F'₂ 1)
    (hG : IsGeneric Λ₂ (gS D) (lf D F0) F'₂) (hO : FrameOK D Λ₂ F'₂) (hZ : ZhatL (lf D F0) F'₂ = Z) :
    mapL n (isom_of_N0F hn) F'₂ ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 Λ Z := by
  have hβ := isom_of_N0F hn
  have hF := mapL_lf hn
  subst hΛ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hF]
    refine ⟨(IsLift_mapL n hβ Λ₂ F'₂).2 hT.1, (IsAdmissible_mapL n hβ _ Λ₂ _ F'₂).2 hT.2.1, ?_⟩
    exact (gval_mapL n hβ (lf D F0) F'₂).symm ▸ hT.2.2
  · rw [← hF]
    exact (AdmWit_mapL n hβ _ Λ₂ _ F'₂ 1).2 hA
  · rw [← hF]
    exact (generic_isomorphism_holds (S := VS D) (r := D.R.rS) (gS D) _ _ n hβ Λ₂ (lf D F0) F'₂).2 hG
  · have h := (positive_definite_isomorphism D u' n hβ Λ₂ (lf D F0) F'₂).2 ⟨hT.1, hT.2.1, hO⟩
    exact h.2.2
  · exact (zhatL_mapL_N0F hn F'₂).trans hZ

theorem gmap_eq_of_image {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} {Λ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (h : (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (Λ : Set (VS D).V)) : Formalism.HermitianLatticesTheory.gmap n Λ₂ = Λ := by
  apply SetLike.coe_injective
  rw [coe_gmap]
  exact h

end BwdCut

open BwdCut

variable (u u' F0 what₂)

def BwdN : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∃ n ∈ unipotentFrameFixers F0,
        (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)

def BwdPair : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ', ∀ (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hn : n ∈ unipotentFrameFixers F0),
        (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V) →
        ∃ γ' : TermDef.Term D u u' F0 what₂, Corank.TermScal D γ γ' ∧
          Rep γ'.lam (lf D F0) (PD D γ'.lam (lf D F0) u') γ'.cls (mapL n (isom_of_N0F hn) (liftF F'₂))

variable {u u' F0 what₂}

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

namespace Formalism.L2.SG.LsDatumA

theorem modSide0G : ModSide0G := Formalism.L2.SG.LocalCountModules.localCountZeroGlobal_holds

theorem modSideUG : ModSideUG := Formalism.L2.SG.LocalCountModules.localCountUnitGlobal_holds

theorem integralClosureRank_and_residueTrdegLe (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.ThinScalesBound.T2 D := globalCount_of_split_mode D modSide0G modSideUG

end Formalism.L2.SG.LsDatumA
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolOrb

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.Coef Formalism.L2.SG.PairVal Formalism.L2.SG.Pf.ZsVolCut
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def StabInCZ : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    PairVal.stabAut D u u' F0 what₂ γ F' L ≤ CZ M δ u u' (ZhatL (lf D F0) F') L

def OrbActE : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    ∃ (X : Type) (_ : MulAction (CZ M δ u u' (ZhatL (lf D F0) F') L) X) (x : X),
      MulAction.stabilizer (CZ M δ u u' (ZhatL (lf D F0) F') L) x =
        (PairVal.stabAut D u u' F0 what₂ γ F' L).subgroupOf (CZ M δ u u' (ZhatL (lf D F0) F') L) ∧
      Nonempty (MulAction.orbit (CZ M δ u u' (ZhatL (lf D F0) F') L) x ≃
        PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F'))

def OrbFinE : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (L U : PairVal.MatR D), HypE M δ u u' F0 what₂ γ w F' L U →
    (PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).Finite

theorem orbStabE_of (h1 : StabInCZ M δ u u' F0 what₂) (h2 : OrbActE M δ u u' F0 what₂) (h3 : OrbFinE M δ u u' F0 what₂) :
    OrbStabE M δ u u' F0 what₂ (CZ M δ u u') := by
  intro γ w F' L U hH
  obtain ⟨X, inst, x, hstab, ⟨e⟩⟩ := h2 γ w F' L U hH
  have hidx : (PairVal.stabAut D u u' F0 what₂ γ F' L).relIndex (CZ M δ u u' (ZhatL (lf D F0) F') L) =
      (PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).ncard := by
    rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr e
  refine ⟨h1 γ w F' L U hH, hidx, ?_⟩
  have hne : (PairVal.orbT D u u' F0 what₂ γ (ZhatL (lf D F0) F')).Nonempty :=
    ⟨(e ⟨x, MulAction.mem_orbit_self x⟩).1, (e ⟨x, MulAction.mem_orbit_self x⟩).2⟩
  exact ((Set.ncard_pos (h3 γ w F' L U hH)).2 hne).ne'

end Formalism.L2.SG.Pf.ZsVolOrb

end
end
