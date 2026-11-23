module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesLocalDatumBlockTriangularLaw
import Formalism.LocalToGlobal.Columns.RowForms
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle084
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle375
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle014
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle065
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle078
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle072
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle061
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGLocModel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.LevelMove

section Mat

variable {κ : Type} [CommRing κ] {a b r t j : ℕ}

def IsTopB (r t : ℕ) (y : Matrix (Fin b) (Fin a) κ) (g : GL (Fin a) κ) : Prop :=
  LowZero a y ∧ g.val = topL a y ∧ g ∈ blockTri (blkOf r t)

theorem IsTopB.move (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t)
    {y : Matrix (Fin b) (Fin a) κ} {g : GL (Fin a) κ} {H : GL (Fin b) κ} (h : IsTopB r t y g)
    (hT : H ∈ blockTri (blkOf r t)) :
    IsTopB r t ((H⁻¹).val * y) ((upperLeftBlock hab H)⁻¹ * g) := by
  obtain ⟨h1, h2, h3⟩ := h
  have t2 := GlobalTheory.StepLaw.TypeDatum.mem_twoBlockTriangular_of_blockTriangular ea eb hT
  have tm := GlobalTheory.StepLaw.TypeDatum.top_mem hab t2 hT
  have hinv : upperLeftBlock hab H⁻¹ = (upperLeftBlock hab H)⁻¹ := extendOne_inv _ t2
  have e1 := GlobalTheory.StepLaw.TypeDatum.topL_mul hab (Subgroup.inv_mem _ t2) h1 1
  have e2 := GlobalTheory.StepLaw.TypeDatum.lowZero_mul (Subgroup.inv_mem _ t2) h1 1
  rw [Matrix.mul_one] at e1 e2
  rw [Matrix.mul_one] at e1
  refine ⟨e2, ?_, Subgroup.mul_mem _ (Subgroup.inv_mem _ tm) h3⟩
  rw [e1, hinv, ← h2, Units.val_mul]

theorem restrictBlock_inv_mul_block_triangular_move (hab : a ≤ b) (ha : r ≤ a) (hb : r ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t)
    {g : GL (Fin a) κ} {H : GL (Fin b) κ} (hg : g ∈ blockTri (blkOf r t)) (hT : H ∈ blockTri (blkOf r t)) :
    upperLeftBlock ha ((upperLeftBlock hab H)⁻¹ * g) = (upperLeftBlock hb H)⁻¹ * upperLeftBlock ha g := by
  have t2 := GlobalTheory.StepLaw.TypeDatum.mem_twoBlockTriangular_of_blockTriangular ea eb hT
  have tm := GlobalTheory.StepLaw.TypeDatum.top_mem hab t2 hT
  have le := blockTri_blkOf_le (κ := κ) (n := a) r t
  have m2 : upperLeftBlock ha ((upperLeftBlock hab H)⁻¹ * g) = upperLeftBlock ha (upperLeftBlock hab H)⁻¹ * upperLeftBlock ha g :=
    extendMatrixByIdentityAlongIndices_mul _ (le (Subgroup.inv_mem _ tm)) (le hg)
  have m3 : upperLeftBlock ha (upperLeftBlock hab H)⁻¹ = (upperLeftBlock ha (upperLeftBlock hab H))⁻¹ := extendOne_inv _ (le tm)
  rw [m2, m3, GlobalTheory.StepLaw.TypeDatum.restrictTopBlock_restrictTopBlock hab ha hb t2 hT]

theorem char_move (hab : a ≤ b) (ea : a = r + j * t) (eb : b = r + (j + 1) * t) {A : Type} [CommGroup A]
    (χ : ℕ → κˣ →* A) {g : GL (Fin a) κ} {H : GL (Fin b) κ} (hg : g ∈ blockTri (blkOf r t))
    (hT : H ∈ blockTri (blkOf r t)) :
    (∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab H)⁻¹ * g))) *
        (χ (j + 1) (Matrix.GeneralLinearGroup.det ((upperLeftBlock hab H)⁻¹ * g)))⁻¹ =
      (∏ c ∈ Finset.range (j + 1), χ (c + 1) (dBlk (blkOf r t) (c + 1) H))⁻¹ *
        χ (j + 1) (Matrix.GeneralLinearGroup.det H) *
        ((∏ c ∈ Finset.range j, χ (c + 1) (dBlk (blkOf r t) (c + 1) g)) *
          (χ (j + 1) (Matrix.GeneralLinearGroup.det g))⁻¹) := by
  have h := GlobalTheory.StepLaw.TypeDatum.char_law hab ea eb χ hg (Subgroup.one_mem _) hT
  have d1 : ∀ c, dBlk (blkOf r t) c (1 : GL (Fin a) κ) = 1 := fun c => blockDiagonalExtendByOnePrimeField_one _ _
  simp only [mul_one, d1, map_one, Finset.prod_const_one, one_mul] at h
  rw [inv_mul_eq_iff_eq_mul] at h
  rw [h]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Mat

section Dat

variable {D : D7} {a b r t k : ℕ} (ha : r ≤ a) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
  (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
  (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP))

theorem omegaG_of_top (g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1)) (hg : ∀ PP : ↥Pg, IsTopB r t (y PP.1) (g PP))
    (hm : (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H) :
    omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) χj y =
      ((P.chi ⟨_, hm⟩ * ∏ PP : ↥Pg, ((∏ c ∈ Finset.range k, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP))) *
        (χj PP.1 (Matrix.GeneralLinearGroup.det (g PP)))⁻¹) : ℂˣ) : ℂ) := by
  unfold omegaG
  split_ifs with h
  · have e : h.2.choose = g := funext fun PP =>
      Units.ext ((h.2.choose_spec.1 PP).trans (hg PP).2.1.symm)
    have e2 : (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B).P.chi
        ⟨fun PP => upperLeftBlock (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B).hr (h.2.choose PP), h.2.choose_spec.2.2⟩ =
        P.chi ⟨_, hm⟩ := by
      show P.chi _ = P.chi _
      congr 1
      exact Subtype.ext (funext fun PP => congrArg (fun x => upperLeftBlock ha x) (congrFun e PP))
    rw [e2]
    simp only [e, Finset.prod_mul_distrib, Units.val_mul, Units.coe_prod, Units.val_inv_eq_inv_val, mul_assoc]
    rfl
  · exfalso
    exact h ⟨fun PP hP => (hg ⟨PP, hP⟩).1, g, fun PP => (hg PP).2.1, fun PP => (hg PP).2.2, hm⟩

theorem omegaG_of_notTop (hg : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), (∀ PP : ↥Pg, IsTopB r t (y PP.1) (g PP)) ∧
      (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H) :
    omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) χj y = 0 := by
  unfold omegaG
  split_ifs with h
  · exfalso
    obtain ⟨h1, g, g1, g2, g3⟩ := h
    exact hg ⟨g, fun PP => ⟨h1 PP.1 PP.2, g1 PP, g2 PP⟩, g3⟩
  · rfl

end Dat

end GlobalTheory.ChainOnto.LevelMove

namespace GlobalTheory.ChainOnto

open LevelMove

theorem omegaG_levelP_move : ∀ (D : D7) (a b r t k : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + k * t → b = r + (k + 1) * t → ∀ (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (H : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)), (∀ PP ∈ Pg, H PP ∈ blockTri (blkOf r t)) → ∀ hP : (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)) ∈ P.H, ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP), omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) (χ (k + 1)) (fun PP => ((H PP)⁻¹).val * y PP) = (((P.chi ⟨_, hP⟩ * ∏ PP ∈ Pg, ∏ i ∈ Finset.range (k + 1), χ (i + 1) PP (dBlk (blkOf r t) (i + 1) (H PP)))⁻¹ * ∏ PP ∈ Pg, χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP)) : ℂˣ) : ℂ) * omegaG (Lev.datY a r t k ha Pg ∅ P χ ξ Lev.Frm.B) (χ (k + 1)) y := by
  intro D a b r t k ha hb ea eb Pg P χ ξ H hH hP y
  have hab : a ≤ b := by rw [ea, eb, add_mul]; omega
  by_cases h : ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1), (∀ PP : ↥Pg, IsTopB r t (y PP.1) (g PP)) ∧
      (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H
  · obtain ⟨g, hg, hm⟩ := h
    have hg' : ∀ PP : ↥Pg, IsTopB r t (((H PP.1)⁻¹).val * y PP.1) ((upperLeftBlock hab (H PP.1))⁻¹ * g PP) :=
      fun PP => (hg PP).move hab ea eb (hH _ PP.2)
    have hr : (fun PP : ↥Pg => upperLeftBlock ha ((upperLeftBlock hab (H PP.1))⁻¹ * g PP)) =
        (fun PP : ↥Pg => upperLeftBlock hb (H PP.1))⁻¹ * (fun PP : ↥Pg => upperLeftBlock ha (g PP)) :=
      funext fun PP => restrictBlock_inv_mul_block_triangular_move hab ha hb ea eb (hg PP).2.2 (hH _ PP.2)
    have hm' : (fun PP : ↥Pg => upperLeftBlock ha ((upperLeftBlock hab (H PP.1))⁻¹ * g PP)) ∈ P.H := by
      rw [hr]; exact P.H.mul_mem (P.H.inv_mem hP) hm
    have hc : P.chi ⟨_, hm'⟩ = (P.chi ⟨_, hP⟩)⁻¹ * P.chi ⟨_, hm⟩ := by
      rw [← map_inv, ← map_mul]; congr 1; exact Subtype.ext hr
    have hx : ∀ PP : ↥Pg, (∏ c ∈ Finset.range k, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) ((upperLeftBlock hab (H PP.1))⁻¹ * g PP))) *
        (χ (k + 1) PP.1 (Matrix.GeneralLinearGroup.det ((upperLeftBlock hab (H PP.1))⁻¹ * g PP)))⁻¹ =
        (∏ c ∈ Finset.range (k + 1), χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (H PP.1)))⁻¹ *
          χ (k + 1) PP.1 (Matrix.GeneralLinearGroup.det (H PP.1)) *
          ((∏ c ∈ Finset.range k, χ (c + 1) PP.1 (dBlk (blkOf r t) (c + 1) (g PP))) *
            (χ (k + 1) PP.1 (Matrix.GeneralLinearGroup.det (g PP)))⁻¹) :=
      fun PP => char_move hab ea eb (fun c => χ c PP.1) (hg PP).2.2 (hH _ PP.2)
    rw [omegaG_of_top ha Pg P χ ξ _ (fun PP => ((H PP)⁻¹).val * y PP) _ hg' hm', omegaG_of_top ha Pg P χ ξ _ y g hg hm,
      hc, ← Units.val_mul]
    congr 1
    rw [Finset.prod_congr rfl fun PP _ => hx PP, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
      ← Finset.prod_coe_sort Pg (fun PP => χ (k + 1) PP (Matrix.GeneralLinearGroup.det (H PP))),
      ← Finset.prod_coe_sort Pg (fun PP => ∏ i ∈ Finset.range (k + 1), χ (i + 1) PP (dBlk (blkOf r t) (i + 1) (H PP)))]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have h' : ¬ ∃ g : ∀ PP : ↥Pg, GL (Fin a) (kP PP.1),
        (∀ PP : ↥Pg, IsTopB r t ((fun PP => ((H PP)⁻¹).val * y PP) PP.1) (g PP)) ∧ (fun PP : ↥Pg => upperLeftBlock ha (g PP)) ∈ P.H := by
      rintro ⟨g, hg, hm⟩
      refine h ⟨fun PP => (upperLeftBlock hab (H PP.1)⁻¹)⁻¹ * g PP, fun PP => ?_, ?_⟩
      · have e : y PP.1 = ((H PP.1)⁻¹⁻¹).val * (((H PP.1)⁻¹).val * y PP.1) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_inv, mul_inv_cancel, Units.val_one, Matrix.one_mul]
        rw [e]
        exact (hg PP).move hab ea eb (Subgroup.inv_mem _ (hH _ PP.2))
      · have hr : (fun PP : ↥Pg => upperLeftBlock ha ((upperLeftBlock hab (H PP.1)⁻¹)⁻¹ * g PP)) =
            (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)⁻¹)⁻¹ * (fun PP : ↥Pg => upperLeftBlock ha (g PP)) :=
          funext fun PP => restrictBlock_inv_mul_block_triangular_move hab ha hb ea eb (hg PP).2.2 (Subgroup.inv_mem _ (hH _ PP.2))
        have i2 : (fun PP : ↥Pg => upperLeftBlock hb (H PP.1)⁻¹) = (fun PP : ↥Pg => upperLeftBlock hb (H PP.1))⁻¹ :=
          funext fun PP => extendOne_inv _ (blockTri_blkOf_le r t (hH _ PP.2))
        rw [hr, i2, inv_inv]
        exact P.H.mul_mem hP hm
    rw [omegaG_of_notTop ha Pg P χ ξ _ y h, omegaG_of_notTop ha Pg P χ ξ _ _ h', mul_zero]

end GlobalTheory.ChainOnto

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.multiplicitySpace_equivariant_real_points : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ (v : M.Vec) (b : GinfC V), ∃ w : M.Vec, (∀ τ, (w τ : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)) (v τ : M.H τ)) ∧ ∀ U ∈ Mult θ M J χ, U w = rTr V (b : GA D V) (U v) := by
  intro D θ V Sp M J χ hθ v b
  classical
  let g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ :=
    fun τ => infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)
  have hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun τ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V (b : GA D V) τ
  let w : M.Vec := fun τ => ⟨M.rep τ (g τ) (v τ : M.H τ),
    GlobalTheory.SmoothStable.rep_mem_sm D V Sp M τ (g τ) (hg τ) _ (v τ).2⟩
  have hb : GlobalTheory.AdelicScalar.realElt θ V g = (b : GA D V) := by
    have hR := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
    refine hR.2.2.1 _ (GlobalTheory.RealLift.prodAt_mem θ V _ g) _ b.2 fun τ => ?_
    have h := GlobalTheory.RealLift.infMat_prodAt hθ V (u := g) hg τ _
      (Finset.nodup_toList Finset.univ)
    rw [if_pos (Finset.mem_toList.2 (Finset.mem_univ _))] at h
    exact h
  refine ⟨w, fun τ => rfl, fun U hU => ?_⟩
  rw [← hb]
  induction hU using Submodule.span_induction with
  | mem U hU =>
    have equivOnList (l : List D.what₂.Tau) (hl : l.Nodup) :
        U (fun τ => if τ ∈ l then w τ else v τ) =
          rTr V (l.map fun τ => atTau θ V τ (g τ)).prod (U v) := by
      induction l with
      | nil =>
        funext x
        simp [rTr]
      | cons τ l ih =>
        rw [List.nodup_cons] at hl
        have h := hU.equiv τ (g τ) (hg τ) (fun ρ => if ρ ∈ l then w ρ else v ρ) (w τ) (by
          simp only [if_neg hl.1]
          rfl)
        rw [ih hl.2] at h
        have hprod : rTr V ((τ :: l).map fun ρ => atTau θ V ρ (g ρ)).prod (U v) =
            rTr V (atTau θ V τ (g τ)) (rTr V (l.map fun ρ => atTau θ V ρ (g ρ)).prod (U v)) := by
          funext x
          simp only [rTr, List.map_cons, List.prod_cons, mul_assoc]
        rw [hprod, ← h]
        congr 1
        funext ρ
        by_cases hρ : ρ = τ
        · subst ρ
          simp
        · rw [Function.update_of_ne hρ]
          simp [hρ]
    have h := equivOnList (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
    rw [GlobalTheory.AdelicScalar.realElt, ← h]
    congr 1
    funext τ
    simp
  | zero =>
    funext x
    simp [rTr]
  | add U U' _ _ h1 h2 =>
    funext x
    have h1x := congrFun h1 x
    have h2x := congrFun h2 x
    simp only [rTr, MultilinearMap.add_apply, Pi.add_apply] at h1x h2x ⊢
    rw [h1x, h2x]
  | smul c U _ h =>
    funext x
    have hx := congrFun h x
    simp only [rTr, MultilinearMap.smul_apply, Pi.smul_apply] at hx ⊢
    rw [hx]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.LevelOpen

theorem exists_open_princ : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Z : Finset (Pl D.host.E)), ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, Lev.finE V k ∈ Formalism.L2.DIV.St β ∧ ∀ PP ∈ Z, Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  intro D V β Z
  have hOpen : IsOpen (((Kg D.sp.cm V.gram β Z).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
    set N : ℕ := ∏ PP ∈ Z, Ideal.absNorm PP.asIdeal with hN
    have hN0 : 0 < N := Finset.prod_pos fun PP _ => Nat.pos_of_ne_zero (by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact PP.ne_bot)
    have hNm : ∀ PP ∈ Z, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hP => by
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun PP : Pl D.host.E => Ideal.absNorm PP.asIdeal) hP
      rw [hN, hc, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    let P : GA D V → Prop := fun k => ∀ i j, ∃ s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      (β⁻¹ * Lev.finE V k * β).1 i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) i j = N • s
    have hP : ∀ᶠ k in nhds (1 : GA D V), P k := by
      have hc := (GlobalTheory.Member.continuous_finHom_val D V).tendsto 1
      rw [map_one, Units.val_one] at hc
      exact hc.eventually (GlobalTheory.DefiniteEnd.eventually_cong β N hN0)
    have hP' : ∀ᶠ k in nhds (1 : GA D V), P k⁻¹ := by
      have : Filter.Tendsto (fun k : GA D V => k⁻¹) (nhds 1) (nhds 1) := by
        simpa using (continuous_inv (G := GA D V)).tendsto 1
      exact this.eventually hP
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hP.and hP') ?_)
    rintro k ⟨h1, h2⟩
    obtain ⟨y, hy, hred⟩ := GlobalTheory.DefiniteEnd.exists_int_of_entries _ (β⁻¹ * Lev.finE V k * β) N h1 (by
      rw [show (β⁻¹ * Lev.finE V k * β)⁻¹ = β⁻¹ * Lev.finE V k⁻¹ * β by rw [map_inv]; group]; exact h2)
    have hy' : frGL β y = Lev.finE V k := by
      show β * Formalism.UG.bc _ y * β⁻¹ = _
      rw [hy]; group
    have hSt : Lev.finE V k ∈ St β := ⟨y, hy'⟩
    refine ⟨⟨GlobalTheory.PrincInLevel.swap_mem_UPts _ _ _ (GlobalTheory.UnitarySplit.finHom_mem V k), hSt⟩, ?_⟩
    refine Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨hSt, ?_⟩
    rw [← hy', redFn_frGL]
    refine hred _ _ ?_
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hNm PP hP)
  
  refine ⟨_, hOpen, fun k hk => ?_⟩
  have hk' : Lev.finE V k ∈ Kg D.sp.cm V.gram β Z := hk
  have h1 : Lev.finE V k ∈ ⨅ PP ∈ Z, princAt β PP := hk'.2
  refine ⟨hk'.1.2, fun PP hP => ?_⟩
  exact (mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2

end GlobalTheory.ChainOnto.LevelOpen
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna
  Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One

namespace GlobalTheory.Core.OneCoset

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem frame_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (a : Fin (r + 1)) :
    frame (mapLF γ F) a = γ (frame F a) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  induction a using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast i => simp [frame, FlagG.fvec, mapFlag]

theorem Xflag_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) :
    Xflag (mapLF γ F) j = (Xflag F j).map (γ : S.V →ₗ[E] S.V) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  show Submodule.span E ((fun a => γ (F.fl.e a)) '' {i | i.1 < j}) =
    (Submodule.span E (F.fl.e '' {i | i.1 < j})).map (γ : S.V →ₗ[E] S.V)
  rw [Submodule.map_span, Set.image_image]
  rfl

theorem orth_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (x : S.V)
    (hx : x ∈ orth S (Xsp (mapLF γ F))) : γ.symm x ∈ orth S (Xsp F) := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro y hy
  have hy' : γ y ∈ Xsp (mapLF γ F) := by
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]; simpa using hy
  have := hx (γ y) hy'
  rw [← hγ y (γ.symm x)]
  simpa using this

end Gen

theorem conj_mem_NRat {D : D7} {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F : LFlag (D.sp.Y 0) D.R.rS T) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hn : n ∈ NRat F) : γ * n * γ⁻¹ ∈ NRat (mapLF γ F) := by
  obtain ⟨hn0, hn1, hn2⟩ := hn
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hγ hn0) ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ), ?_, ?_⟩
  · intro j x hx
    rw [Xflag_mapLF γ hγ] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨n y - y, hn1 j y hy, ?_⟩
    show γ (n y - y) = γ (n (γ.symm (γ y))) - γ y
    simp
  · intro x hx
    have h := hn2 _ (orth_mapLF γ hγ F x hx)
    rw [Formalism.L2.SG.NGCut.CorankRelation.mem_Xsp_mapLF γ hγ]
    show γ.symm (γ (n (γ.symm x)) - x) ∈ Xsp F
    simpa using h

theorem corankOne_of_same_flagDoubleCoset : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ∀ t t' : TauC Y u u', t.G ≠ 0 → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t' →
      nmlOf Y u u' t = nmlOf Y u u' t' → (Y.tO u u').s0 t t' = 1 := by
  intro D X Y u u' t t' hG hr hn
  have hlam : t.lam = t'.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hlam' : t.lam' = t'.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hr
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hlat : Submodule.IsFullLattice D.host.E t.lam :=
    { toIsLattice := hrow.2.1.1
      span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular
        (VS D).hT (VS D).herm (VS D).nondeg hrow.2.1.1 hrow.2.1.2.1 }
  have hLF : IsLift t.lam (lf D (X.Fu u)) := hrow.2.1.2.2.1
  have hLt : IsLift t.lam t.frame := t.rep.2.2.2.2.1
  have hLt' : IsLift t'.lam t'.frame := t'.rep.2.2.2.2.1
  have hGv : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
    rw [← Formalism.L2.SG.Pf.SatGram.gterm_G Y t]; exact hG
  have hone : ∀ {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T), (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F :=
    fun F => ⟨(Formalism.HermitianLatticesTheory.isom _).one_mem, fun j x _ => by simp, fun x _ => by simp⟩
  have hmem : t'.lin ∈ nmlOf Y u u' t := by
    rw [hn]; exact ⟨1, hone _, 1, hone _, by simp⟩
  obtain ⟨n, hn1, n', hn2, heq⟩ := hmem
  have hm : t.lin * n' * t.lin⁻¹ ∈ NRat t.frame := conj_mem_NRat t.lin t.rep.2.2.1 _ n' hn2
  have hβ : t'.lin * t.lin⁻¹ = n * (t.lin * n' * t.lin⁻¹) := by rw [heq]; group
  have hfr : ∀ a, frame t'.frame a = (n * (t.lin * n' * t.lin⁻¹)) (frame t.frame a) := by
    intro a
    unfold GTerm.frame
    rw [frame_mapLF t'.lin t'.rep.2.2.1, frame_mapLF t.lin t.rep.2.2.1, ← hβ]
    show t'.lin _ = t'.lin (t.lin.symm (t.lin _))
    simp
  have hTh := GlobalTheory.DcosetCompl.th_eq_hp D t.lam (lf D (X.Fu u)) t.frame t'.frame hlat rfl hLt.2 hLt'.2 n hn1 _ hm hfr
  rw [← hβ] at hTh
  have hs0 : Lat.s0 t.lam (lf D (X.Fu u)) t.frame t'.frame (t'.lin * t.lin⁻¹) D.R.k = 1 :=
    (Formalism.L2.SG.NGCut.CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t.lam hlat _ t.frame t'.frame _ hLF hLt hGv).2 hTh
  show s0T t t' = 1
  unfold s0T
  rw [if_pos ⟨hlam, hlam'⟩]
  exact hs0

end GlobalTheory.Core.OneCoset
end
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Diag

theorem kExp_absConv_tied : Formalism.L2.SG.ThmSOwn.KExpTied ∧ AbsConvTied :=
  ⟨Formalism.L2.SG.ThmSOwn.kExpTied_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.InHHC_holds
            Formalism.L2.SG.Closed.FundExistsC_holds Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.OOFundIndepC_holds
            Formalism.L2.SG.Closed.AmpWellDefC_holds Formalism.L2.SG.Closed.AbsConvC_outright Formalism.L2.SG.Closed.KExpansionC_holds,
    Formalism.L2.SG.RowsConc.absConvTied_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.FundExistsC_holds
      Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.AbsConvC_outright⟩

end GlobalTheory.Core.Diag
end
