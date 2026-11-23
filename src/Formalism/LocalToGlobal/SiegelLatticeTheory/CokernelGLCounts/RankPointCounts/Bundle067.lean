module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bridge
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.Bundle001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SplitG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousTensMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.MemSpanRIffSplit
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle007
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle398
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle059

@[expose] public section

section

noncomputable section

open scoped TensorProduct
open Matrix NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets PI.MassDataKppVolLemmas

namespace Formalism.L2.SG.Pf.MassDataX

section Swap

variable (I : Formalism.MainNotions.S.AutInst)

def sw : I.E ⊗[I.F] Af I.F →+* Af I.F ⊗[I.F] I.E := (swapE I).toRingEquiv.toRingHom

instance sw_surj : RingHomSurjective (sw I) := ⟨(swapE I).surjective⟩

def swV : (Fin I.n → I.E ⊗[I.F] Af I.F) →ₛₗ[sw I] (Fin I.n → Af I.F ⊗[I.F] I.E) where
  toFun v i := swapE I (v i)
  map_add' v w := funext fun i => map_add _ _ _
  map_smul' c v := funext fun i => by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rfl

theorem swV_apply (v : Fin I.n → I.E ⊗[I.F] Af I.F) (i : Fin I.n) : swV I v i = swapE I (v i) := rfl

theorem swV_injective : Function.Injective (swV I) := fun v w h =>
  funext fun i => (swapE I).injective (congrFun h i)

theorem swV_mem_span (T : Set (Fin I.n → I.E ⊗[I.F] Af I.F)) (v : Fin I.n → I.E ⊗[I.F] Af I.F) :
    swV I v ∈ Submodule.span (Af I.F ⊗[I.F] I.E) (swV I '' T) ↔ v ∈ Submodule.span (I.E ⊗[I.F] Af I.F) T := by
  rw [← Submodule.map_span]
  constructor
  · intro h
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp h
    rwa [swV_injective I hwv] at hw
  · intro hv
    exact Submodule.mem_map.mpr ⟨v, hv, rfl⟩

theorem sigR_swap (t : I.E ⊗[I.F] Af I.F) :
    sigR (Af I.F) I.cm.sig (swapE I t) = swapE I (Formalism.UG.sigR I.cm.sig (Af I.F) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, Formalism.UG.sigR, swapE]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem swapE_inclE_eq (a : I.E) :
    swapE I (Formalism.UG.inclE (F := I.F) (Af I.F) a) = inclR (Af I.F) a := by
  simp [swapE, Formalism.UG.inclE, inclR]

theorem hR_swV (x y : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hR (Af I.F) I.cm.sig I.J (swV I x) (swV I y) = swapE I (hA I x y) := by

  simp only [hR, hA, Formalism.UG.hform, JR, Matrix.map_apply, map_sum, map_mul, swV_apply, sigR_swap,
  swapE_inclE_eq]

theorem ratV_swV (w : Fin I.n → I.E) : ratV (F := I.F) (Af I.F) w = swV I (incl I w) := by
  funext i
  simp only [ratV, swV_apply, incl]
  exact (swapE_inclE_eq I (w i)).symm

end Swap

theorem nfinU_of_tf {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (y : X.B.I.Gf)
    (h : tf X.B.I hb y ∈ Nsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) : y ∈ X.NfinU u := by
  obtain ⟨hU, hP⟩ := h
  have hmat := Bridge_mat (I := X.B.I) (hb := hb) y
  have hlin : ∀ w : VA X.B.I, lin (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (tf X.B.I hb y) (swV X.B.I w) =
      swV X.B.I (X.B.I.fmat y *ᵥ w) := by
    intro w
    simp only [lin, Matrix.mulVecLin_apply, hmat]
    funext i
    rw [swV_apply]
    exact ((sw X.B.I).map_mulVec (X.B.I.fmat y) w i).symm
  have hsub : ∀ w : VA X.B.I, swV X.B.I ((X.B.I.fmat y - 1) *ᵥ w) =
      lin (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (tf X.B.I hb y) (swV X.B.I w) - swV X.B.I w := by
    intro w
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, hlin]
  have hspan : ∀ (s : Set (Fin D.R.rS)) (v : VA X.B.I),
      swV X.B.I v ∈ spanR (F := X.B.I.F) (Af X.B.I.F) (frameOf X u).e s ↔
        v ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' s) := by
    intro s v
    have himg : (fun a => ratV (F := X.B.I.F) (Af X.B.I.F) ((frameOf X u).e a)) '' s =
        swV X.B.I '' ((fun b => incl X.B.I (X.eR b)) '' s) := by
      rw [Set.image_image]
      exact Set.image_congr fun a _ => ratV_swV X.B.I _
    unfold spanR
    rw [himg]
    exact swV_mem_span X.B.I _ v
  have hperp : ∀ w : VA X.B.I, (∀ a, hA X.B.I (incl X.B.I (X.eR a)) w = 0) →
      InXperp (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) (swV X.B.I w) := by
    intro w hw a
    rw [ratV_swV, hR_swV]
    exact (congrArg (swapE X.B.I) (hw a)).trans (map_zero _)
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.NfinU Formalism.L2.SG.HidaSetting.Nfin
  rw [Set.mem_setOf_eq]
  refine ⟨fun a => ?_, ?_, fun w hw => ?_⟩
  · rw [← hspan, hsub]
    have h1 := hU a
    rw [ratV_swV] at h1
    exact h1
  · rw [← Set.image_univ, ← hspan, hsub]
    exact hP _ (hperp _ fun a => Formalism.L2.SG.Pf.SlabNDensePf.adelicHermitian_hyperbolicE_anisotropic_eq_zero (X := X) (u := u) a)
  · rw [← Set.image_univ, ← hspan, hsub]
    exact hP _ (hperp _ hw)

theorem strongApproxN_holds : MassDataMassesW.StrongApproxN := by
  intro D X u x hx
  have hb := Formalism.L2.SG.Closed.AdBridgeIso_holds X.B.I
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨p, rfl⟩ := (toHA X.B.I hb).surjective x
  have hsp := MassDataMassesW.split_toHA X hb MassDataMassesW.splitIso_holds p
  have hxf := ((PI.UnitaryGroupMassFormula.MeasWCore.mem_Nsub_iff X.B.I.cm.sig X.B.I.J PI.UnitaryGroupMassFormula.MeasWCore.splT_bijective
    (frameOf X u) _).1 hx).2
  have hxf' : tf X.B.I hb p.2 ∈ Nsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
    have e2 : haMap X.B.I.cm.sig X.B.I.J (sndA X.B.I.F) (toHA X.B.I hb p) = finHA X hb p.2 :=
      congrArg Prod.snd hsp
    rw [e2] at hxf
    exact hxf
  have hy : p.2 ∈ X.NfinU u := nfinU_of_tf X hb u p.2 hxf'
  have h1K : (1 : X.B.I.Gf) ∈ X.B.I.Kset :=
    (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 1 (Formalism.L2.SG.Closed.level_subgroup_is_group X).1
  have hUo : IsOpen {w : X.B.I.Gf | w⁻¹ * p.2 ∈ X.B.I.Kset} :=
    (Formalism.L2.SG.Pf.kset_open X.B.I).preimage (continuous_inv.mul continuous_const)
  have hyU : p.2 ∈ {w : X.B.I.Gf | w⁻¹ * p.2 ∈ X.B.I.Kset} := by
    show p.2⁻¹ * p.2 ∈ X.B.I.Kset
    rw [inv_mul_cancel]
    exact h1K
  obtain ⟨ν, hνGF, hν1, hν2, hνU⟩ := Formalism.L2.SG.Pf.SlabNDensePf.nilradical_strong_approximation D X u p.2 hy _ hUo hyU
  have hB := (MassDataMassesW.nRatBridge_holds X hb u ν).2 ⟨hνGF, hν1, hν2⟩
  refine ⟨(toHA X.B.I hb ν)⁻¹, Subgroup.inv_mem _ hB.1, Subgroup.inv_mem _ hB.2, ?_⟩
  rw [← map_inv, ← map_mul, MassDataMassesW.split_toHA X hb MassDataMassesW.splitIso_holds]
  exact (PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 hνU

end Formalism.L2.SG.Pf.MassDataX
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolGrp

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

theorem det_lo {l : Matrix (Fin n) (Fin n) R} (h1 : ∀ a, l a a = 1) (h2 : ∀ a b, a < b → l a b = 0) : l.det = 1 := by
  rw [Matrix.det_of_lowerTriangular l (fun i j hij => h2 i j hij)]
  exact Finset.prod_eq_one fun i _ => h1 i

theorem det_up {l : Matrix (Fin n) (Fin n) R} (h1 : ∀ a, l a a = 1) (h2 : ∀ a b, b < a → l a b = 0) : l.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h2 i j hij)]
  exact Finset.prod_eq_one fun i _ => h1 i

theorem inv_eq_adj {l : Matrix (Fin n) (Fin n) R} (h : l.det = 1) : l⁻¹ = l.adjugate := by
  rw [Matrix.inv_def, h, Ring.inverse_one, one_smul]

theorem adj_mem (S : Subring R) {l : Matrix (Fin n) (Fin n) R} (h : ∀ a b, l a b ∈ S) (i j : Fin n) :
    l.adjugate i j ∈ S := by
  let lS : Matrix (Fin n) (Fin n) S := fun a b => ⟨l a b, h a b⟩
  have e : l = S.subtype.mapMatrix lS := by
    ext a b
    rfl
  rw [e, ← RingHom.map_adjugate]
  exact (lS.adjugate i j).2

end Uni

section Int

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E] [TopologicalSpace E]
  [MeasurableSpace E] (Mp : Loc.Model F E) {n : ℕ}

theorem intLow_one : Formalism.MainNotions.S.TieN.IntLow Mp (1 : Matrix (Fin n) (Fin n) E) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply, h.ne], fun a b => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem intUp_one : Formalism.MainNotions.S.TieN.IntUp Mp (1 : Matrix (Fin n) (Fin n) E) :=
  ⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply, h.ne'], fun a b => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem intLow_mul {l l' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l)
    (h' : Formalism.MainNotions.S.TieN.IntLow Mp l') : Formalism.MainNotions.S.TieN.IntLow Mp (l * l') := by
  first | exact GlobalTheory.LowerIntegralMul.intLow_mul .. | (apply GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (intros; apply GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (apply @GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (intros; apply @GlobalTheory.LowerIntegralMul.intLow_mul <;> assumption) | (apply @GlobalTheory.LowerIntegralMul.intLow_mul <;> first | assumption | infer_instance) | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l l' h h' | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l l' h | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l l' | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n l | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp n | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› Mp | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E ‹_› | exact @GlobalTheory.LowerIntegralMul.intLow_mul F E | exact @GlobalTheory.LowerIntegralMul.intLow_mul F

theorem intUp_mul {l l' : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp l)
    (h' : Formalism.MainNotions.S.TieN.IntUp Mp l') : Formalism.MainNotions.S.TieN.IntUp Mp (l * l') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨fun a => ?_, fun a b hab => ?_, fun a b => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [h1, h1', mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [h2 a c h, zero_mul]
      · rw [h2' c a h, mul_zero]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [h2 a c h, zero_mul]
    · rw [h2' c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply]
    exact sum_mem fun c _ => mul_mem (h3 a c) (h3' c b)

theorem intLow_inv {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntLow Mp l) :
    Formalism.MainNotions.S.TieN.IntLow Mp l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hd := det_lo h1 h2
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => h2 i j hij)
  have hz : ∀ a b, a < b → l⁻¹ a b = 0 := fun a b hab => hb hab
  refine ⟨⟨fun a => ?_, hz, fun a b => ?_⟩, hli, hil⟩
  · have e := congrFun (congrFun hil a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, h1, one_mul] at e
    · simpa using e
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hz c a h, mul_zero]
      · rw [h2 a c h, zero_mul]
    · simp
  · rw [inv_eq_adj hd]
    exact adj_mem Mp.R h3 a b

theorem intUp_inv {l : Matrix (Fin n) (Fin n) E} (h : Formalism.MainNotions.S.TieN.IntUp Mp l) :
    Formalism.MainNotions.S.TieN.IntUp Mp l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hd := det_up h1 h2
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => h2 i j hij)
  have hz : ∀ a b, b < a → l⁻¹ a b = 0 := fun a b hab => hb hab
  refine ⟨⟨fun a => ?_, hz, fun a b => ?_⟩, hli, hil⟩
  · have e := congrFun (congrFun hil a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, h1, one_mul] at e
    · simpa using e
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [h2 a c h, zero_mul]
      · rw [hz c a h, mul_zero]
    · simp
  · rw [inv_eq_adj hd]
    exact adj_mem Mp.R h3 a b

end Int

theorem zhatOM_zhatOM {K : Type*} [CommRing K] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    ZhatOM (ZhatOM Z) = Z := by
  ext a b
  simp only [ZhatOM]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

end Formalism.L2.SG.Pf.ZsVolGrp

end
end
