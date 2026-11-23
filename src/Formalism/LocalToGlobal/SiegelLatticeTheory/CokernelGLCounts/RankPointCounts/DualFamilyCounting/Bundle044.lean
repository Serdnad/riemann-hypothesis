module

public import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HpkMulVecEs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle034
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NotIntDensOfSteps
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieLG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaExplicitAtOfEta
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle041
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcGlob
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle036
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowLatticeMass
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle042
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle038
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle033
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic

def sq2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem sq2_mul_sq2_eq_half : sq2 * sq2 = 1 / 2 := by
  unfold sq2
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

theorem star_sq2_eq_self : star sq2 = sq2 := by
  unfold sq2; rw [Complex.star_def, Complex.conj_ofReal]

def u1 (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val < r then sq2 else if r + k < i.val then -sq2 else 1

def u2 (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val < r then sq2 else if r + k < i.val then sq2 else 0

def Pu (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  (if j = i then u1 k r i else 0) + (if i = sig k r j then u2 k r i else 0)

theorem Pu_star (k r : ℕ) (i j : Fin (2 * r + k + 1)) : star (Pu k r i j) = Pu k r i j := by
  unfold Pu u1 u2
  split_ifs <;> simp [star_sq2_eq_self]

theorem PuJPu_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ((Pu k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pu k r) i j = Hpk k r i j := by
  have hJ : Formalism.REAL.Jm (epsK k r) = diagonal (dK k r) := rfl
  rw [hJ, Matrix.mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, Pu_star]
  unfold Pu
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Hpk_eq]
  have hi := i.isLt
  have hs := sig_val k r i
  have h2 := sq2_mul_sq2_eq_half
  by_cases hji : j = i
  · subst hji
    simp only [Fin.ext_iff]
    simp only [u1, u2, dK, epsK, sgn, decide_eq_true_eq]
    split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
    all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
      linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
  · by_cases hjs : j = sig k r i
    · subst hjs
      simp only [sig_sig]
      have hji' : ¬ (sig k r i).val = i.val := fun h => hji (Fin.ext h)
      simp only [Fin.ext_iff]
      simp only [u1, u2, dK, epsK, sgn, decide_eq_true_eq]
      split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
      all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
        linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
    · have h1 : ¬ i = j := fun h => hji h.symm
      have h2' : ¬ i = sig k r j := fun h => hjs ((eq_sig_iff k r i j).1 h)
      have h3 : ¬ sig k r j = sig k r i := fun h => hji ((sig_inj k r j i).1 h)
      rw [if_neg h1, if_neg hjs, if_neg h2', if_neg h3, if_neg hjs]
      norm_num

theorem PuPu_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ((Pu k r)ᴴ * Pu k r) i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j := by
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [conjTranspose_apply, Pu_star]
  unfold Pu
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hi := i.isLt
  have hs := sig_val k r i
  have h2 := sq2_mul_sq2_eq_half
  by_cases hji : j = i
  · subst hji
    simp only [Fin.ext_iff]
    simp only [u1, u2]
    split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
    all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
      linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
  · by_cases hjs : j = sig k r i
    · subst hjs
      simp only [sig_sig]
      have hji' : ¬ (sig k r i).val = i.val := fun h => hji (Fin.ext h)
      simp only [Fin.ext_iff]
      simp only [u1, u2]
      split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
      all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
        linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
    · have h1 : ¬ i = j := fun h => hji h.symm
      have h2' : ¬ i = sig k r j := fun h => hjs ((eq_sig_iff k r i j).1 h)
      have h3 : ¬ sig k r j = sig k r i := fun h => hji ((sig_inj k r j i).1 h)
      simp [h1, hjs, h2', h3]

theorem PuJPu (k r : ℕ) : (Pu k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pu k r = Hpk k r := by
  ext i j; exact PuJPu_apply k r i j

theorem PuPu (k r : ℕ) : (Pu k r)ᴴ * Pu k r = 1 := by
  ext i j; exact PuPu_apply k r i j

theorem exists_unitary {r k : ℕ} (ε : Fin (2 * r + k + 1) → Bool)
    (hs : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) :
    ∃ P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r ∧ Pᴴ * P = 1 := by
  obtain ⟨σ, hσ⟩ := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.PF.exists_perm ε hs
  refine ⟨Matrix.of fun i j => Pu k r (σ.symm i) j, ?_, ?_⟩
  · rw [← PuJPu k r]
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Formalism.REAL.Jm, mul_diagonal, conjTranspose_apply, of_apply]
    refine (Fintype.sum_equiv σ _ _ (fun m => ?_)).symm
    simp only [Equiv.symm_apply_apply, hσ m]
  · rw [← PuPu k r]
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [conjTranspose_apply, of_apply]
    refine (Fintype.sum_equiv σ _ _ (fun m => ?_)).symm
    simp only [Equiv.symm_apply_apply]

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FormulaCT : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word) (Lsp : LocSp D T.Y.M),
    Formalism.L2.SG.Pf.LocCP.LocTied D → Formalism.MainNotions.S.Cnt.Stand D u u' →
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
    Formula T.Y.δ Lsp u u' (T.X.Fu u) (T.Y.what₂ u) (cExpl D (T.X.Fu u) (T.Y.what₂ u))

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem formulaCT_of (hF : DualityBasisChange.FrameBasisL) : FormulaCT := by
  intro D T u u' Lsp hLT _ hT
  have hη : AtD.EtaLocAt D := fun p => Formalism.L2.SG.Pf.AlTieLG.etaLoc_of_tied hLT p
  have hDA := AtD.densAllAt_of D hF hη
  have hFE := Formalism.L2.SG.Pf.formulaExplicitAt_of D hDA
  have hR := T.Y.rowsOK u
  obtain ⟨Λ0, hΛ0⟩ := lattice_exists_holds D T u
  have hne : (T.Y.what₂ u).Nonempty := by
    obtain ⟨Λ', ⟨hΛ', -⟩, -⟩ := hR.2 Λ0 hΛ0
    exact ⟨Λ', hΛ'⟩
  refine ⟨cExpl_pos' D u (T.X.Fu u) (T.Y.what₂ u) hR hne, fun ϖ hϖ Z =>
    ⟨orbitFiniteR_of counting_iso_inverse D T.Y.δ T.Y.M T.Y.agree Lsp u u' hT (T.X.Fu u) (T.Y.what₂ u) hR Z,
      fun hP => ⟨?_, ?_⟩⟩⟩
  · obtain ⟨F', hz, hZ⟩ := rational_pair_holds D u u' hT (T.X.Fu u) (T.Y.what₂ u) hR Z hP
    obtain ⟨h1, h2⟩ := hDA T.Y.δ T.Y.M T.Y.agree Lsp u u' hT (T.X.Fu u) (T.Y.what₂ u) hR ϖ hϖ Z F' hz hZ hP
    by_cases hI : Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D (T.X.Fu u) F')
    · exact (h1 hI).2
    · obtain ⟨p, hp⟩ := h2 hI
      exact (hasProd_zero_of_exists_eq_zero ⟨p, hp⟩).multipliable
  · exact hFE T.Y.δ T.Y.M T.Y.agree Lsp u u' hT (T.X.Fu u) (T.Y.what₂ u) hR ϖ hϖ Z hP

end Formalism.L2.SG.Pf.Cnt
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.NcLeaves

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
  (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
  (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
  {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
  (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ncTieC_of_leaves (a' : ℝ) (ha : 0 < a')
    (hP : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos)
    (hM : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMass)
    (hMs : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InMasses)
    (hL : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InLevelS)
    (hO : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InOrdinary)
    (hT : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InTyped)
    (hV : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).InVolumes)
    (hVG : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volHa' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volG)
    (hχ : IsCharAF X.B.I.F ψ) (hstd : IsStdChar ψ)
    (hcong : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hRR : IsRowReps D F0 what₂)
    (hS : (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK * a' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' *
        ∏' v : PlX X,
          (omAt X.B.I.cm.sig X.B.I.J ψ v
            ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
            {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
              Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal)
    (hR : Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
        (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' =
      a' * 2 ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F)) *
        (Real.pi ^ D.R.k / (Nat.factorial (D.R.k - 1) : ℝ)) ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) *
        ((Tw u : ℕ) : ℝ) ^ (-((D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F) : ℕ) : ℤ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^
          (-(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3))
    (hVo : Formalism.L2.SG.Pf.NcVal.VolOrdV X u u' ψ) (hVt : Formalism.L2.SG.Pf.NcVal.VolTypV X u u' ψ)
    (hIx : Formalism.L2.SG.Pf.NcIdx.IndexTypC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq)
    (hOm : Formalism.L2.SG.Pf.NcVal.OmV X u' ψ) (hFD : Formalism.L2.SG.Pf.NcVal.FieldDict X u u')
    (hPC : ProdConv X u u' ψ) :
    NcTieC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq (Formalism.L2.SG.Pf.Cnt.cExpl D F0 what₂) :=
  Formalism.L2.SG.Pf.NcAsm.ncTieC_of' X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq hP hM hMs hL hO hT hV hVG
    (Formalism.L2.SG.Pf.NcGlob.normalizing_arithmetic_holds X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq a' ha hRR hS hR
      hχ hstd hcong hVo hVt hIx hOm
      (Formalism.L2.SG.Pf.NcVal.diffProd_holds X) PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_lattice_mass hFD hPC hP)

end Formalism.L2.SG.Pf.NcLeaves
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem Gp_mem (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0) (hd : ∀ a, X0 a a = 1)
    (hs : ∀ b a : Fin D.R.rS, b < a → X0 b a ∈ aaD D b * (aaD D a)⁻¹) (hxs : ∀ b, xs b ∈ aaLb X b) :
    ∀ b a, Gp D X0 xs b a ∈ aaD D b * aaD D a := by
  have hY := LatA.shape_mul X0⁻¹ (Gq D xs) (inv_up X0 hup hd) (inv_diag X0 hup hd) (LatA.shape_inv X0 hup hd hs)
    (gram_mem X xs hxs)
  intro b a
  unfold Gp
  rw [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun e _ => ?_
  rw [Matrix.conjTranspose_apply]
  rcases lt_trichotomy e a with h | h | h
  · rw [inv_up X0 hup hd a e h, star_zero, mul_zero]; exact Submodule.zero_mem _
  · subst h; rw [inv_diag X0 hup hd, star_one, mul_one]; exact hY b e
  · have hz : star (X0⁻¹ a e) ∈ aaD D a * (aaD D e)⁻¹ :=
      star_mem_iQ (show X0⁻¹ a e ∈ iQ D a e from LatA.shape_inv X0 hup hd hs a e h)
    have hYe : (X0⁻¹ * Gq D xs) b e ∈ aaD D e * aaD D b := by rw [mul_comm]; exact hY b e
    have key : star (X0⁻¹ a e) * (X0⁻¹ * Gq D xs) b e ∈ aaD D a * aaD D b := by
      rw [← LatA.aa_cancel2 e a b]; exact FractionalIdeal.mul_mem_mul hz hYe
    rw [mul_comm (aaD D b) (aaD D a), mul_comm ((X0⁻¹ * Gq D xs) b e)]
    exact key

theorem Gp_herm (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V) :
    (Gp D X0 xs)ᴴ = Gp D X0 xs := by
  have hG : (Gq D xs)ᴴ = Gq D xs := by
    refine Matrix.ext fun b c => ?_
    rw [Matrix.conjTranspose_apply]
    show star ((VS D).hT (xs c) (xs b)) = (VS D).hT (xs b) (xs c)
    rw [Alg.hsw, star_star]
  unfold Gp
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.mul_assoc]

theorem Xc_blkQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0) (hd : ∀ a, X0 a a = 1) (v : InfinitePlace X.B.I.F) :
    Xc X (blkQ X u X0 xs M) v = X0.map (embS D (X.pl v)) := by
  ext b a
  simp only [Xc, Matrix.map_apply]
  split_ifs with h1 h2
  · rfl
  · subst h2; rw [hd, map_one]
  · have : a < b := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)
    rw [hup b a this, map_zero]

theorem Gc_blkQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (hW : ∀ b, InW X (xs b)) (v : InfinitePlace X.B.I.F) :
    Gc X u (blkQ X u X0 xs M) v = (Gq D xs).map (embS D (X.pl v)) := by
  ext b c
  simp only [Gc, Matrix.map_apply]
  rw [show Gq D xs b c = (VS D).hT (xs b) (xs c) from rfl, rowV_gram X u v (xs b) (xs c) (hW c)]
  rfl

theorem Hc_blkQ (X0 : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (xs : Fin D.R.rS → (VS D).V)
    (M : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hup : ∀ b a : Fin D.R.rS, a < b → X0 b a = 0) (hd : ∀ a, X0 a a = 1) (hW : ∀ b, InW X (xs b))
    (v : InfinitePlace X.B.I.F) :
    Hc X u (blkQ X u X0 xs M) v = (Gp D X0 xs).map (embS D (X.pl v)) := by
  unfold Hc
  rw [Xc_blkQ X u X0 xs M hup hd v, Gc_blkQ X u X0 xs M hW v, map_inv' X0 hup hd]
  have hc : ((X0⁻¹).map (embS D (X.pl v)))ᴴ = ((X0⁻¹)ᴴ).map (embS D (X.pl v)) :=
    (Matrix.conjTranspose_map _ fun t => emb_star X v t).symm
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul]
  rfl

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end
