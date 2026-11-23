module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle052
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GflagSwap
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle057
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle036
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfQ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle047
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle018
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FinitePhaseSimp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle054
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalInvariants
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardMulConjEqLeOfFractionalIdeal
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfL

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem frFac_cf (a : Fin (D.R.rS + 1)) :
    frFac Zd.δ p a = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) := by
  rw [frFac_eq]; rfl

theorem inv_alg_cf (a : Fin (D.R.rS + 1)) :
    Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) := by
  have h1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) = 1 := by
    rw [← map_mul, cf_cfi, map_one]
  have hu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) := ⟨Units.mkOfMulEqOne _ _ h1, rfl⟩
  calc Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))
      = Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
          (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) := by
        rw [h1, mul_one]
    _ = _ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

theorem lOf_eq (A B : Formalism.L2.SG.PairVal.MatR D) :
    Formalism.L2.SG.Pf.StabShape.lOf Zd.δ Zd.M p A B = Formalism.L2.SG.Pf.TupGlob.locL Zd p A B := by
  unfold Formalism.L2.SG.Pf.StabShape.lOf Formalism.L2.SG.Pf.TupGlob.locL
  cases hs : (Zd.M p).split with
  | none =>
    ext i j
    simp only [Formalism.L2.SG.Pf.StabShape.lL, Matrix.of_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply,
      ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [frFac_cf, frFac_cf, RingHom.coe_coe, AlgEquiv.commutes, AlgEquiv.commutes, inv_alg_cf]
  | some g =>
    ext i j
    apply g.e.injective
    simp only [Formalism.L2.SG.Pf.StabShape.lG, glue, Matrix.of_apply, AlgEquiv.apply_symm_apply]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply, Matrix.transpose_apply, Sg,
      ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      RingHom.comp_apply, adeleInfiniteComponent_apply, adele_ext_components, frFac_cf, AlgEquiv.commutes, Prod.algebraMap_apply, map_mul, map_pow,
      map_neg, map_one, Prod.fst_mul, Prod.snd_mul, Prod.pow_fst, Prod.pow_snd, Prod.fst_neg, Prod.snd_neg,
      Prod.fst_one, Prod.snd_one, Algebra.algebraMap_self, RingHom.id_apply]
    have h1 : ∀ a, cf Zd p a ≠ 0 := fun a => left_ne_zero_of_mul_eq_one (cf_cfi Zd p a)
    have h2 : ∀ a, cfi Zd p a = (cf Zd p a)⁻¹ := fun a => eq_inv_of_mul_eq_one_right (cf_cfi Zd p a)
    ext
    all_goals (simp only [h2, div_eq_mul_inv]; try ring)

end Formalism.L2.SG.Pf.FibD
end
end

section

namespace Formalism.L2.SG.LsDatumA

def ModSide0G : Prop := Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSide0 M r n true)

def ModSideUG : Prop := Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSideU M r n true)

theorem modSide0_mode (h0G : ModSide0G) :
    Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSide0 M r n M.split.isSome) := by
  intro F _ _ _ E _ _ _ _ M hM r n
  cases h : M.split.isSome
  · exact modSide0L F E M hM r n
  · exact h0G F E M hM r n

theorem modSideU_mode (hUG : ModSideUG) :
    Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n : ℕ, ModSideU M r n M.split.isSome) := by
  intro F _ _ _ E _ _ _ _ M hM r n
  cases h : M.split.isSome
  · exact modSideUL F E M hM r n
  · exact hUG F E M hM r n

theorem globalCount_of_split_mode (D : Formalism.BasicNotions.D7) (h0G : ModSide0G) (hUG : ModSideUG) : Formalism.MainNotions.ThinScalesBound.T2 D :=
  globalCount_of_module D (fun F _ _ _ E _ _ _ _ M hM => modSide0_mode h0G F E M hM _ _)
    (fun F _ _ _ E _ _ _ _ M hM => modSideU_mode hUG F E M hM _ _)

end Formalism.L2.SG.LsDatumA
end

section

noncomputable section

open Module
open Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem X_le_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsFullLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F.fl.X ≤ UUE Λ F F' := by
  exact (Formalism.MainNotions.LatticeGluingRadicals.a_X_le (Formalism.MainNotions.LatticeGluingRadicals.a_HU Λ hΛ F F' hL.2 hL'.2)).1

theorem X'_le_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsFullLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F'.fl.X ≤ UUE Λ F F' := by
  exact (Formalism.MainNotions.LatticeGluingRadicals.a_X_le (Formalism.MainNotions.LatticeGluingRadicals.a_HU Λ hΛ F F' hL.2 hL'.2)).2

theorem z_mem_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F.fl.z ∈ UUE Λ F F' := by
  rw [← hL.2]
  exact Submodule.subset_span (Submodule.mem_sup_left (Submodule.mem_sup_left
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))))

theorem z'_mem_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') : F'.fl.z ∈ UUE Λ F F' := by
  rw [← hL'.2]
  exact Submodule.subset_span (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))

theorem yv_mem_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (hΛ : Submodule.IsFullLattice E Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (hL' : IsLift Λ F') :
    yv F.fl F'.fl ∈ UUE Λ F F' := by
  have hf : ∀ b, F'.fl.fvec b ∈ UUE Λ F F' := by
    intro b
    refine Fin.lastCases ?_ (fun i => ?_) b
    · rw [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
      exact z'_mem_UUE Λ hΛ.toIsLattice F F' hL hL'
    · rw [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
      exact X'_le_UUE Λ hΛ F F' hL hL' (Submodule.subset_span ⟨i, rfl⟩)
  unfold yv omp
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (hf b))) (Submodule.smul_mem _ _ (z_mem_UUE Λ hΛ.toIsLattice F F' hL hL'))

theorem hT_Hp_UUE (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    {h v : S.V} (hh : h ∈ Hp Λ F F') (hv : v ∈ UUE Λ F F') : S.hT h v = 0 := by
  rw [hT_swap v h, Formalism.L2.SG.NGCut.CorankRelation.hT_eq_zero_of_mem_Hp Λ F F' hh hv, star_zero]

theorem hT_UUE_Hp (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T')
    {h v : S.V} (hh : h ∈ Hp Λ F F') (hv : v ∈ UUE Λ F F') : S.hT v h = 0 :=
  Formalism.L2.SG.NGCut.CorankRelation.hT_eq_zero_of_mem_Hp Λ F F' hh hv

theorem hT_X_yv (F : FlagG S r T) (F' : FlagG S r T') {x : S.V} (hx : x ∈ F.X) : S.hT x (yv F F') = 0 := by
  have hker : F.X ≤ LinearMap.ker (S.hT (yv F F')) := by
    rw [Formalism.MainNotions.S.FlagG.X, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hT_swap]
    have h := brS_yv_e (F := F) (F' := F') a
    rw [Formalism.MainNotions.S.brS] at h
    rw [h, star_zero]
  have h1 : S.hT (yv F F') x = 0 := hker hx
  rw [hT_swap, h1, star_zero]

theorem hT_z_yv (F : FlagG S r T) (F' : FlagG S r T') : S.hT F.z (yv F F') = 0 := by
  have h := pairing_yVector_z (F := F) (F' := F')
  rwa [Formalism.MainNotions.S.brS] at h

theorem UUE_symm (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    UUE Λ F' F = UUE Λ F F' := by
  unfold Formalism.MainNotions.S.Lat.UUE Formalism.MainNotions.S.Lat.UU
  congr 1
  ac_rfl

theorem Hp_symm (Λ : Submodule (NumberField.RingOfIntegers E) S.V) (F : LFlag S r T) (F' : LFlag S r T') :
    Hp Λ F' F = Hp Λ F F' := by
  unfold Formalism.MainNotions.S.Lat.Hp
  rw [UUE_symm]

theorem line_pair (k : ℕ) (hdim : finrank E S.V = k + 2 * r + 1) (Λ : Submodule (NumberField.RingOfIntegers E) S.V)
    (hΛ : Submodule.IsFullLattice E Λ) (Fl : LFlag S r T) (F1 F2 : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hL : IsLift Λ Fl) (hL1 : IsLift Λ F1) (hL2 : IsLift Λ F2) (hG1 : Gval Fl F1 ≠ 0) (hG12 : Gval Fl F2 = Gval Fl F1)
    (hT : T ≠ 0) (hTs : star T = T) (hTh : Th Λ Fl F1 F2 β = Hp Λ Fl F1) :
    yv Fl.fl F2.fl - (brS S (yv Fl.fl F2.fl) (yv Fl.fl F1.fl) / brS S (yv Fl.fl F1.fl) (yv Fl.fl F1.fl)) •
        yv Fl.fl F1.fl ∈ Fl.fl.X ∧
      (brS S (yv Fl.fl F2.fl) (yv Fl.fl F1.fl) / brS S (yv Fl.fl F1.fl) (yv Fl.fl F1.fl)) *
        star (brS S (yv Fl.fl F2.fl) (yv Fl.fl F1.fl) / brS S (yv Fl.fl F1.fl) (yv Fl.fl F1.fl)) = 1 := by
  set y1 := yv Fl.fl F1.fl with hy1
  set y2 := yv Fl.fl F2.fl with hy2
  set c := brS S y2 y1 / brS S y1 y1 with hc
  have hG1' : Formalism.MainNotions.S.Gflag Fl.fl F1.fl ≠ 0 := hG1
  have hb1 : brS S y1 y1 ≠ 0 := by
    rw [hy1, brS_yv_yv Fl.fl F1.fl hTs]
    exact mul_ne_zero hT hG1'
  have hb12 : brS S y2 y2 = brS S y1 y1 := by
    rw [hy1, hy2, brS_yv_yv Fl.fl F2.fl hTs, brS_yv_yv Fl.fl F1.fl hTs]
    exact congrArg (T * ·) hG12
  obtain ⟨hfin, hk1⟩ := Formalism.L2.SG.NGCut.CorankRelation.finrank_Hp k hdim Λ hΛ Fl F1 hL hL1 hG1

  have hy2H : ∀ h ∈ Hp Λ Fl F1, S.hT h y2 = 0 := by
    intro h hh
    rw [← hTh] at hh
    unfold Formalism.MainNotions.S.Lat.Th at hh
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hh
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_ThPairs] at hp
    obtain ⟨-, hp2, hpX, -⟩ := hp
    have e : p.1 = (p.1 - p.2) + p.2 := by abel
    simp only [LinearMap.fst_apply]
    rw [e, map_add (f := _), LinearMap.add_apply, hT_X_yv Fl.fl F2.fl hpX,
      hT_Hp_UUE Λ Fl F2 hp2 (yv_mem_UUE Λ hΛ Fl F2 hL hL2), add_zero]
  have hv : y2 - c • y1 ∈ Fl.fl.X := by
    refine Formalism.L2.SG.NGCut.NormalVectorPairings.line Fl.fl hT (Hp Λ Fl F1) ?_ ?_ ?_ ?_ ?_ hb1 ?_ ?_
    · intro x hx h hh
      exact hT_UUE_Hp Λ Fl F1 hh (X_le_UUE Λ hΛ Fl F1 hL hL1 hx)
    · intro h hh
      exact hT_UUE_Hp Λ Fl F1 hh (z_mem_UUE Λ hΛ.toIsLattice Fl F1 hL hL1)
    · intro x hx hxH
      exact Formalism.L2.SG.NGCut.CorankRelation.Xsp_Hp_eq_zero Λ hΛ Fl F1 hL hL1 hG1 hx hxH
    · omega
    · rw [Formalism.L2.SG.NGCut.NormalVectorPairings.mem_Qsp]
      exact ⟨fun x hx => hT_X_yv Fl.fl F1.fl hx, hT_z_yv Fl.fl F1.fl,
        fun h hh => hT_Hp_UUE Λ Fl F1 hh (yv_mem_UUE Λ hΛ Fl F1 hL hL1)⟩
    · rw [Formalism.L2.SG.NGCut.NormalVectorPairings.mem_Qsp]
      refine ⟨fun x hx => ?_, ?_, fun h hh => ?_⟩
      · rw [map_sub, map_smul, hT_X_yv Fl.fl F2.fl hx, hT_X_yv Fl.fl F1.fl hx, smul_zero, sub_zero]
      · rw [map_sub, map_smul, hT_z_yv, hT_z_yv, smul_zero, sub_zero]
      · rw [map_sub, map_smul, hy2H h hh, hT_Hp_UUE Λ Fl F1 hh (yv_mem_UUE Λ hΛ Fl F1 hL hL1),
          smul_zero, sub_zero]
    · rw [sub_eq_add_neg, ← neg_smul, brS_add_left, brS_smul_left, hc]
      field_simp
      ring
  refine ⟨hv, ?_⟩

  set x := y2 - c • y1 with hx
  have hy2x : y2 = x + c • y1 := by
    rw [hx]
    abel
  have hxx : brS S x x = 0 := by
    rw [Formalism.MainNotions.S.brS]
    exact hT_X_X Fl.fl hv hv
  have hyx : brS S y1 x = 0 := by
    rw [Formalism.MainNotions.S.brS]
    exact hT_X_yv Fl.fl F1.fl hv
  have hxy : brS S x y1 = 0 := by
    rw [Formalism.MainNotions.S.brS, hT_swap, hT_X_yv Fl.fl F1.fl hv, star_zero]
  have hmod : brS S y2 y2 = c * star c * brS S y1 y1 := by
    rw [hy2x, brS_add_left, brS_add_right, brS_add_right, brS_smul_left, brS_smul_left,
      brS_smul_right, brS_smul_right, hxx, hxy, hyx]
    ring
  rw [hb12] at hmod
  have h1 : (1 : E) * brS S y1 y1 = c * star c * brS S y1 y1 := by rw [one_mul]; exact hmod
  exact (mul_right_cancel₀ hb1 h1).symm

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem coef_int (γ : TermDef.Term D u u' F0 what₂) {Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f)
    (hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a)) (c : Fin (D.R.rS + 1) → D.host.E)
    (hc : ∑ a, c a • frame (lf D F0) a ∈ Λ₂) : IsIntegral ℤ (c (Fin.last D.R.rS)) := by
  refine int_of_loc Zd fun p => ?_
  set m := ∑ a, c a • frame (lf D F0) a with hm
  have hbm : baseChange₂ D p m = ∑ a, ((D.s.atP p).ιE (c a) * (((hu p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep)) •
      (tLoc Zd p γ).f a := by

    rw [hm, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, baseChangeAt_frame_eq Zd p γ (hu p), Units.smul_def, smul_smul]
  have hspan : baseChange₂ D p m ∈ Submodule.span (D.s.atP p).Ep (Set.range (tLoc Zd p γ).f) := by
    rw [hbm]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h2 := (hprim p).2.2 _ (baseChange_mem_localLattice Zd hc p) hspan
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
  have hli := (hprim p).2.1
  have hz : ∑ a, (((o a : (Zd.M p).L.O) : (D.s.atP p).Ep) -
      (D.s.atP p).ιE (c a) * (((hu p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep)) • (tLoc Zd p γ).f a = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hbm, ← ho]
    simp only [sub_eq_zero]
    rfl
  have h3 := Fintype.linearIndependent_iff.1 hli _ hz (Fin.last D.R.rS)
  have key : ∀ {a : (D.s.atP p).Ep} (h : IsUnit a), a = 1 →
      (((h.unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep) = 1 := by
    intro a h ha
    subst ha
    have : h.unit = 1 := Units.ext (IsUnit.unit_spec h)
    rw [this, inv_one, Units.val_one]
  have hone := key (hu p (Fin.last D.R.rS)) (by rw [sgnP_last, frFac_last', mul_one])
  rw [hone, mul_one, sub_eq_zero] at h3
  rw [← h3]
  exact (o (Fin.last D.R.rS)).2

theorem exists_y (γ : TermDef.Term D u u' F0 what₂) {Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ₂ : Submodule.IsLattice D.host.E Λ₂) (hSD₂ : BwdNA.SD (VS D) Λ₂)
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f)
    (hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a)) (hzX : F0.z ∉ Xsp (lf D F0)) :
    ∃ y ∈ Λ₂, y ∈ orth (VS D) (Xsp (lf D F0)) ∧ (VS D).hT y F0.z = 1 := by
  obtain ⟨f, hfz, hfX⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hzX inferInstance
  let ρ : Module.Dual D.host.E (VS D).V := (f F0.z)⁻¹ • f
  have hρz : ρ F0.z = 1 := by
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hfz
  have hρX : ∀ x ∈ Xsp (lf D F0), ρ x = 0 := fun x hx => by
    have h1 : f x ∈ (Xsp (lf D F0)).map f := ⟨x, hx, rfl⟩
    rw [hfX, Submodule.mem_bot] at h1
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul, h1, mul_zero]
  have hρe : ∀ i : Fin D.R.rS, ρ (frame (lf D F0) i.castSucc) = 0 := fun i => by
    rw [frame_cs]; exact hρX _ (Submodule.subset_span ⟨i, rfl⟩)
  have hρl : ρ (frame (lf D F0) (Fin.last D.R.rS)) = 1 := by
    have : frame (lf D F0) (Fin.last D.R.rS) = F0.z := by simp [frame, FlagG.fvec]
    rw [this, hρz]
  obtain ⟨v, hv⟩ := BwdNA.riesz (VS D) ρ
  let U : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range (frame (lf D F0)))
  have hint : ∀ m ∈ Λ₂, m ∈ U → IsIntegral ℤ ((VS D).hT m v) := fun m hm hmU => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hmU
    have hρm : ρ m = c (Fin.last D.R.rS) := by

      rw [← hc, map_sum, Fin.sum_univ_castSucc]
      simp only [map_smul, smul_eq_mul, hρe, mul_zero, Finset.sum_const_zero, zero_add, hρl, mul_one]
    rw [BwdNA.hsw (VS D) v m, hv, hρm]
    exact BwdNA.isInt_star (coef_int Zd γ hprim hu c (by rw [hc]; exact hm))
  obtain ⟨w, hwΛ, hvw⟩ := BwdNA.dual_sum (VS D) Λ₂ hΛ₂ hSD₂ U v hint
  have hw : ∀ a, (VS D).hT w (frame (lf D F0) a) = ρ (frame (lf D F0) a) := fun a => by
    have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hvw _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [map_sub, sub_eq_zero] at h0
    rw [BwdNA.hsw (VS D) (frame (lf D F0) a) w, ← h0, ← BwdNA.hsw (VS D) (frame (lf D F0) a) v, hv]
  refine ⟨w, hwΛ, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => ?_, ?_⟩
  · change x ∈ Submodule.span D.host.E (Set.range F0.e) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [BwdNA.hsw (VS D) w (F0.e i), ← frame_cs, hw, hρe, star_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), LinearMap.add_apply, ha, hb, add_zero]
    | smul c x _ hx => rw [BwdNA.hT_smulL, hx, mul_zero]
  · have : frame (lf D F0) (Fin.last D.R.rS) = F0.z := by simp [frame, FlagG.fvec]
    rw [← this, hw, hρl]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP
end
end

section

namespace Formalism.L2.SG.Pf.StabIntSh

theorem stabIntShape (D : Formalism.BasicNotions.D7) : StabIntShapeC D :=
  stabIntShape_of locShapeL locShapeG locGlob shapeNZ

end Formalism.L2.SG.Pf.StabIntSh
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.LiftedPhaseAgreement

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

theorem liftAtSomeC_holds : Formalism.L2.SG.Pf.RowForm.LiftAtSomeC X Y u u' κ := by
  intro R ρ s hs
  have hA := Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u' s.1.toTerm
  have hG : s.1.toTerm.G ≠ 0 := by
    intro h
    apply s.2.1
    show Formalism.L2.SG.TermOp.Gt s.1 = 0
    simp [Formalism.L2.SG.TermOp.Gt, Formalism.L2.SG.TermOp.GTerm.G, h]
  exact hA hG hs

theorem phaseTieC_holds (hP : Formalism.MainNotions.S.Lat.PrimeHyp D u (Formalism.MainNotions.S.Lat.Tu D u')) :
    Formalism.L2.SG.Pf.RowForm.PhaseTieC X Y u u' κ :=
  Formalism.L2.SG.Pf.PhaseLiftCell.phaseAgreement_of_lift X Y u u' κ (liftAtSomeC_holds X Y u u' κ)
    (Formalism.L2.SG.Pf.FinitePhaseConjugation.finPhaseC_of (hNR := Formalism.L2.SG.Pf.normRepExists_of
      (Formalism.L2.SG.Pf.NormRepX.norm_representative_holds D u u' hP) (Formalism.L2.SG.Closed.TermFun_holds D u u') (Y.rowsOK u))
      (h1 := liftAtSomeC_holds X Y u u' κ))

end Formalism.L2.SG.Pf.LiftedPhaseAgreement
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}

theorem patchC_of_full (hL : LocFullC Zd u u' F0 what₂) : PatchC Zd u u' F0 what₂ :=
  patchC_of Formalism.L2.SG.Pf.LocalDenominators.latPatch_holds hL

end Formalism.L2.SG.Pf.FrameGlobalPatching
end
end

section

namespace Formalism.L2.SG.NGCut.NormalCount

theorem NormCountG_holds : Formalism.L2.SG.NGCut.NormalInvariants.NormCountG := by
  intro E _ _ _ J m hJ hm S hS
  exact Formalism.L2.SG.NGCut.TorsionTotientBound.card_mul_conj_eq_le_of_fractionalIdeal E J m hJ hm S hS

theorem NormCount_holds : Formalism.L2.SG.NGCut.NormalInvariants.NormCount :=
  Formalism.L2.SG.NGCut.NormalInvariants.normCount_of NormCountG_holds

end Formalism.L2.SG.NGCut.NormalCount
end
