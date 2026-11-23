module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle017
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsTrm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle352
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.DetMulEqSumProdMulDetSubmatrix
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle350
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle012
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle134
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle115
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModuleFormEqRadialFormOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle128
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TLFinal
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle015
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle035
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle018
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf

@[expose] public section

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass

open Formalism.MainNotions.S.Loc

section General

theorem linInd_of_change {R W ι : Type} [CommRing R] [AddCommGroup W] [Module R W] [Fintype ι] [DecidableEq ι]
    {v w : ι → W} (B : Matrix ι ι R) (hB : IsUnit B.det) (hv : LinearIndependent R v)
    (hw : ∀ j, w j = ∑ i, B i j • v i) : LinearIndependent R w := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg
  have h1 : ∑ i, (B.mulVec g) i • v i = 0 := by
    rw [← hg]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, hw, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  have h2 : B.mulVec g = 0 := funext (hv _ h1)
  have h3 : g = B⁻¹.mulVec (B.mulVec g) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec]
  intro i
  rw [h3, h2, Matrix.mulVec_zero, Pi.zero_apply]

theorem isUnit_ringInverse_of_ne {R : Type} [CommRing R] {y : R} (h : Ring.inverse y ≠ 0) :
    IsUnit (Ring.inverse y) := by
  by_cases hy : IsUnit y
  · obtain ⟨u, rfl⟩ := hy
    rw [Ring.inverse_unit]
    exact Units.isUnit _
  · exact absurd (Ring.inverse_non_unit y hy) h

theorem det_uni_eq_one {K : Type} [CommRing K] {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : Uni A) :
    A.det = 1 := by
  obtain ⟨hlow, hdiag⟩ := hA
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => hlow i j hij)]
  simp [hdiag]

end General

section Main

variable {D : D7}

theorem exists_place (D : D7) : Nonempty (PlF D) := by
  obtain ⟨P, hne, hP⟩ :=
    Ring.not_isField_iff_exists_prime.1 (NumberField.RingOfIntegers.not_isField D.host.F)
  exact ⟨⟨P, hP, hne⟩⟩

private theorem linearIndependent_frameD_of_T_ne_zero {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
    (Fr : LocNG.FrameD H r) (hT : Fr.T ≠ 0) : LinearIndependent E Fr.f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ y, H.h (∑ i, g i • Fr.f i) y = ∑ i, g i * H.h (Fr.f i) y := by
    intro y
    have hs : ∀ s : Finset (Fin (r + 1)),
        H.h (∑ i ∈ s, g i • Fr.f i) y = ∑ i ∈ s, g i * H.h (Fr.f i) y := by
      intro s
      refine Finset.induction_on s (by simp [H.h_zero_left]) ?_
      intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
    exact hs Finset.univ
  have hlast : g (Fin.last r) = 0 := by
    have hz := key (Fr.f (Fin.last r))
    rw [hg, H.h_zero_left, Fin.sum_univ_castSucc] at hz
    have hoff : ∀ i : Fin r, H.h (Fr.f i.castSucc) (Fr.f (Fin.last r)) = 0 :=
      fun i => Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last i))
    simp only [hoff, mul_zero, Finset.sum_const_zero, zero_add, Fr.h_zz] at hz
    have hu : IsUnit (-(algebraMap F E Fr.T)) := ((Ne.isUnit hT).map (algebraMap F E)).neg
    exact hu.mul_left_eq_zero.1 hz.symm
  intro i
  refine Fin.lastCases hlast (fun j => ?_) i
  have he := key (Fr.es j)
  rw [hg, H.h_zero_left, Fin.sum_univ_castSucc, hlast, zero_mul, add_zero] at he
  simp only [Fr.h_es, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at he
  exact he.symm

theorem local_pair_linInd (Z : LocDat D) (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS)
    (hR : P.RelG (LocNG.theta (Z.M p))) :
    LinearIndependent (D.s.atP p).Ep (Sum.elim P.A.f P.B.f) := by
  obtain ⟨hX, -, -, -, -, -, hN⟩ := hR
  obtain ⟨-, hT, -, hT', -⟩ := hN
  exact LinearIndependent.sum_type (linearIndependent_frameD_of_T_ne_zero P.A hT) (linearIndependent_frameD_of_T_ne_zero P.B hT')
    (disjoint_iff.2 hX)

end Main

section Final

variable {D : D7}

theorem base_frames_linInd (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ)
    (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (hR : ∀ p, (FP p).RelG (LocNG.theta (Z.M p))) :
    LinearIndependent D.host.E (Sum.elim (frame F) (frame F')) := by
  obtain ⟨p⟩ := exists_place D
  have hloc := local_pair_linInd Z p (FP p) (hR p)
  obtain ⟨hA, hA', -, -⟩ := hB p
  have hu : ∀ i, Sum.elim (FP p).A.f (FP p).B.f i =
      Sum.elim (frFac Z.δ p) (frFac Z.δ p) i • baseChange₂ D p (Sum.elim (frame F) (frame F') i) := by
    rintro (a | a)
    · simp only [Sum.elim_inl, hA]
    · simp only [Sum.elim_inr, hA']
  have hs : ∀ i, Ring.inverse (Sum.elim (frFac Z.δ p) (frFac Z.δ p) i) *
      Sum.elim (frFac Z.δ p) (frFac Z.δ p) i = 1 := by
    intro i
    have hne : Sum.elim (frFac Z.δ p) (frFac Z.δ p) i ≠ 0 := by
      intro h0
      apply hloc.ne_zero i
      rw [hu i, h0, zero_smul]
    refine Ring.inverse_mul_cancel _ ?_
    rcases i with a | a
    · exact isUnit_ringInverse_of_ne hne
    · exact isUnit_ringInverse_of_ne hne
  rw [Fintype.linearIndependent_iff] at hloc ⊢
  intro g hg
  have h1 : ∑ i, ((D.s.atP p).ιE (g i) * Ring.inverse (Sum.elim (frFac Z.δ p) (frFac Z.δ p) i)) •
      Sum.elim (FP p).A.f (FP p).B.f i = 0 := by
    have hmap := congrArg (baseChange₂ D p) hg

    rw [map_sum, map_zero] at hmap
    rw [← hmap]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu i, smul_smul, mul_assoc, hs i, mul_one, baseChange_smul₂]
  intro i
  have h2 := hloc _ h1 i
  have h3 : (D.s.atP p).ιE (g i) = 0 := by
    have h4 := congrArg (· * Sum.elim (frFac Z.δ p) (frFac Z.δ p) i) h2
    simpa only [mul_assoc, hs i, mul_one, zero_mul] using h4
  exact (map_eq_zero_iff _ (D.s.atP p).ιE.injective).1 h3

theorem changed_frames_linInd : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F G : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → Tri D.host.E (frame F) (frame G) → Tri D.host.E (frame F') (frame G') → LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) := by
  intro D Z FP Tn T'n F G F' G' hB hR hG hG'
  have hbase := base_frames_linInd Z FP Tn T'n F F' hB hR
  obtain ⟨A, hA, hcA⟩ := hG
  obtain ⟨A', hA', hcA'⟩ := hG'
  refine linInd_of_change (Matrix.fromBlocks A 0 0 A') ?_ hbase ?_
  · rw [Matrix.det_fromBlocks_zero₂₁, det_uni_eq_one hA, det_uni_eq_one hA', mul_one]
    exact isUnit_one
  · rintro (b | b)
    · simp only [Sum.elim_inl, Fintype.sum_sum_type, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
      exact hcA b
    · simp only [Sum.elim_inr, Fintype.sum_sum_type, Sum.elim_inl, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
      exact hcA' b

end Final
end GlobalTheory.GenMass
end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocOver

section MatrixFacts

variable {K : Type*} [Field K] {N : ℕ}

theorem upUni_inv_facts {U : Matrix (Fin N) (Fin N) K} (hU : IsUpUni U) :
    IsUpUni U⁻¹ ∧ U * U⁻¹ = 1 ∧ U⁻¹ * U = 1 := by
  have hbt : U.BlockTriangular id := fun i j hij => (hU i j).1 hij
  have hdet : U.det = 1 := by
    rw [Matrix.det_of_upperTriangular hbt]
    exact Finset.prod_eq_one fun i _ => (hU i i).2 rfl
  have hu : IsUnit U.det := by rw [hdet]; exact isUnit_one
  have h1 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hu
  have h2 : U⁻¹ * U = 1 := Matrix.nonsing_inv_mul U hu
  letI := Matrix.invertibleOfIsUnitDet U hu
  have hbt' : U⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  refine ⟨fun i j => ⟨fun hij => hbt' hij, fun hij => ?_⟩, h1, h2⟩
  subst hij
  have e := congrFun (congrFun h2 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at e
  · rw [(hU i i).2 rfl, mul_one] at e; simpa using e
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hbt' h, zero_mul]
    · rw [(hU k i).1 h, mul_zero]
  · simp

theorem loUni_inv_facts {L : Matrix (Fin N) (Fin N) K} (hL : IsLoUni L) :
    IsLoUni L⁻¹ ∧ L * L⁻¹ = 1 ∧ L⁻¹ * L = 1 := by
  have hT : IsUpUni L.transpose := fun i j => ⟨fun hij => (hL j i).1 hij, fun hij => by subst hij; simpa using (hL i i).2 rfl⟩
  obtain ⟨h0, -, -⟩ := upUni_inv_facts hT
  have hbt : L.transpose.BlockTriangular id := fun i j hij => (hT i j).1 hij
  have hdet : L.det = 1 := by
    rw [← Matrix.det_transpose, Matrix.det_of_upperTriangular hbt]
    exact Finset.prod_eq_one fun i _ => (hT i i).2 rfl
  have hu : IsUnit L.det := by rw [hdet]; exact isUnit_one
  refine ⟨fun i j => ?_, Matrix.mul_nonsing_inv L hu, Matrix.nonsing_inv_mul L hu⟩
  have e : L⁻¹ i j = (L.transpose)⁻¹ j i := by rw [← Matrix.transpose_nonsing_inv]; rfl
  rw [e]
  exact ⟨fun hij => (h0 j i).1 hij, fun hij => (h0 j i).2 hij.symm⟩

end MatrixFacts

theorem tw_tw {K : Type*} [CommRing K] {r : ℕ} (B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Formalism.MainNotions.BridgeLemma₂.rows_tw (Formalism.MainNotions.BridgeLemma₂.rows_tw B) = B := by
  have hs : ∀ n : ℕ, ((-1 : K) ^ n) * ((-1) ^ n) = 1 := by
    intro n; rw [← mul_pow]; simp
  ext i j
  simp only [Formalism.MainNotions.BridgeLemma₂.rows_tw, Matrix.of_apply]
  linear_combination (B i j * (-1) ^ (r - j.val) * (-1) ^ (r - j.val)) * hs (r - i.val) + B i j * hs (r - j.val)

theorem tw_upUni {K : Type*} [CommRing K] {r : ℕ} {B : Matrix (Fin (r + 1)) (Fin (r + 1)) K}
    (hB : IsUpUni B) : IsUpUni (Formalism.MainNotions.BridgeLemma₂.rows_tw B) := by
  intro i j
  refine ⟨fun hij => by simp [Formalism.MainNotions.BridgeLemma₂.rows_tw, (hB i j).1 hij], fun hij => ?_⟩
  subst hij
  simp only [Formalism.MainNotions.BridgeLemma₂.rows_tw, Matrix.of_apply, (hB i i).2 rfl, mul_one]
  rw [← mul_pow]; simp

variable {D : D7}

theorem zhatL_chg {T T' : D.host.E} {F F₂ : LFlag (D.sp.Y 0) D.R.rS T} {F₁ F₃ : LFlag (D.sp.Y 0) D.R.rS T'}
    {A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E}
    (h₂ : Chg (frame F) A (frame F₂)) (h₃ : Chg (frame F₁) A' (frame F₃)) :
    ZhatL F₂ F₃ = A.conjTranspose * ZhatL F F₁ * A' := by
  ext a b
  have e2 : F₂.fl.fvec a = ∑ c, A c a • F.fl.fvec c := h₂ a
  have e3 : F₃.fl.fvec b = ∑ d, A' d b • F₁.fl.fvec d := h₃ b
  simp only [ZhatL, Zhat, brS, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e2, e3]

  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
  Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [RingHom.id_apply, starRingEnd_apply]
  ring

theorem zhatL_leadMinor {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ : LFlag (D.sp.Y 0) D.R.rS T')
    {A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E} (hA : Uni A) (hA' : Uni A') (l : ℕ) :
    leadMinorE (A.conjTranspose * ZhatL F F₁ * A') l = leadMinorE (ZhatL F F₁) l := by
  unfold leadMinorE
  split_ifs with hl
  · exact Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant D.host.E _ l hl _ _ _
      (fun i => by simp [Matrix.conjTranspose_apply, hA.2 i])
      (fun i j hij => by simp [Matrix.conjTranspose_apply, hA.1 j i hij])
      (fun i => hA'.2 i) (fun i j hij => hA'.1 i j hij)
  · rfl

theorem base_frames_at_point : ∀ (D : D7) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ : LFlag (D.sp.Y 0) D.R.rS T') (w : Point D.host.E (D.R.rS + 1)), T ≠ 0 → T' ≠ 0 → IsInCell (ZhatOM (ZhatL F F₁)) w → (∃ (F00 : LFlag (D.sp.Y 0) D.R.rS T) (F'0 : LFlag (D.sp.Y 0) D.R.rS T'), Tri D.host.E (frame F) (frame F00) ∧ Tri D.host.E (frame F₁) (frame F'0) ∧ ZhatOM (ZhatL F00 F'0) = ptMat w) ∧ ∀ (F₂ : LFlag (D.sp.Y 0) D.R.rS T) (F₃ : LFlag (D.sp.Y 0) D.R.rS T'), Tri D.host.E (frame F) (frame F₂) → Tri D.host.E (frame F₁) (frame F₃) → IsInCell (ZhatOM (ZhatL F₂ F₃)) w ∧ Gval F₂ F₃ = Gval F F₁ := by
  intro D T T' F F₁ w hT hT' hcell
  obtain ⟨L, U, hL, hU, hZ⟩ := hcell
  refine ⟨?_, ?_⟩
  · obtain ⟨hLi, -, hLL⟩ := loUni_inv_facts hL
    obtain ⟨hUi, hUU, -⟩ := upUni_inv_facts hU
    have hA : Uni (L⁻¹).conjTranspose :=
      ⟨fun a b hba => by simp [Matrix.conjTranspose_apply, (hLi b a).1 hba],
        fun a => by simp [Matrix.conjTranspose_apply, (hLi a a).2 rfl]⟩
    have hA'u := tw_upUni hUi
    have hA' : Uni (Formalism.MainNotions.BridgeLemma₂.rows_tw U⁻¹) := ⟨fun a b hba => (hA'u a b).1 hba, fun a => (hA'u a a).2 rfl⟩
    obtain ⟨F00, h00⟩ := (GlobalTheory.T.unitriangularChange_rationalFlag_iff_rationalUnipotent D F hT).1 _ hA
    obtain ⟨F'0, h'0⟩ := (GlobalTheory.T.unitriangularChange_rationalFlag_iff_rationalUnipotent D F₁ hT').1 _ hA'
    refine ⟨F00, F'0, ⟨_, hA, h00⟩, ⟨_, hA', h'0⟩, ?_⟩
    rw [zhatL_chg h00 h'0, Formalism.MainNotions.BridgeLemma₂.rows_ZhatOM_mul, hZ, tw_tw, Matrix.conjTranspose_conjTranspose]
    calc L⁻¹ * (L * ptMat w * U) * U⁻¹ = (L⁻¹ * L) * ptMat w * (U * U⁻¹) := by simp only [Matrix.mul_assoc]
      _ = ptMat w := by rw [hLL, hUU, Matrix.one_mul, Matrix.mul_one]
  · rintro F₂ F₃ ⟨A, hA, h2⟩ ⟨A', hA', h3⟩
    have hZ2 := zhatL_chg h2 h3
    constructor
    · have hAl : IsLoUni A.conjTranspose := fun i j =>
        ⟨fun hij => by simp [Matrix.conjTranspose_apply, hA.1 j i hij],
          fun hij => by subst hij; simp [Matrix.conjTranspose_apply, hA.2 i]⟩
      have hAu : IsUpUni A' := fun i j => ⟨fun hij => hA'.1 i j hij, fun hij => by subst hij; exact hA'.2 i⟩
      refine ⟨A.conjTranspose * L, U * Formalism.MainNotions.BridgeLemma₂.rows_tw A', Formalism.MainNotions.BridgeLemma₂.rows_loUni_mul hAl hL,
        Formalism.MainNotions.BridgeLemma₂.rows_upUni_mul hU (tw_upUni hAu), ?_⟩
      rw [hZ2, Formalism.MainNotions.BridgeLemma₂.rows_ZhatOM_mul, hZ]
      simp only [Matrix.mul_assoc]
    · show Gflag F₂.fl F₃.fl = Gflag F.fl F₁.fl
      have hD : ∀ l, Dl F₂.fl F₃.fl l = Dl F.fl F₁.fl l := fun l => by
        show leadMinorE (ZhatL F₂ F₃) l = leadMinorE (ZhatL F F₁) l
        rw [hZ2]; exact zhatL_leadMinor F F₁ hA hA' l
      unfold Gflag
      rw [hD, hD]

end GlobalTheory.LocOver
end
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_roots_point_matrix_iff_same_block : ∀ (K : Type) [Field K] (n : ℕ) (w : Point K n) (a b : Fin n), (a, b) ∈ GlobalTheory.LoopV.roots (ptMat w) ↔ a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1 := by
  first | exact @GlobalTheory.roots_ptMat_iff | exact GlobalTheory.roots_ptMat_iff | (intros; apply GlobalTheory.roots_ptMat_iff <;> assumption)
end

section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.KB GlobalTheory.ThA Finset NumberField MeasureTheory Formalism.QuantumDeterminants Matrix

namespace GlobalTheory.ThA

theorem plExists : PlExists := by
  obtain ⟨Cb, -, hTL⟩ := Formalism.FourierDecayAlt.P.top_lift_exists
  refine ⟨Cb, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P Bs ν' m₀ l0 hl1 hl2 hk hW hW' hN hF hP

  obtain ⟨T, hz, hz', hπ, hπ', hTn⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq Bs
  have ez : (T.bs 0).z = Bs.z := hz
  have ez' : (T.bs 0).z' = Bs.z' := hz'
  have eπ : (T.bs 0).π = Bs.π := hπ
  have eπ' : (T.bs 0).π' = Bs.π' := hπ'

  let T' : D.LevTower P.k P.r Wp Wq :=
    { bs := fun j => Nat.rec (motive := fun j => B.RealPlaceData P.k (P.r - j) Wp Wq) Bs (fun n _ => T.bs (n + 1)) j
      z_lev := by
        intro j hj
        cases j with
        | zero =>
          have h0 := T.z_lev 0 hj
          rw [ez] at h0
          exact h0
        | succ n => exact (T.z_lev (n + 1) hj).trans ez
      z'_lev := by
        intro j hj
        cases j with
        | zero =>
          have h0 := T.z'_lev 0 hj
          rw [ez'] at h0
          exact h0
        | succ n => exact (T.z'_lev (n + 1) hj).trans ez'
      π_lev := by
        intro j hj y
        cases j with
        | zero =>
          have h0 := T.π_lev 0 hj y
          rw [eπ] at h0
          exact h0
        | succ n => exact (T.π_lev (n + 1) hj y).trans (congrFun eπ _)
      π'_lev := by
        intro j hj y
        cases j with
        | zero =>
          have h0 := T.π'_lev 0 hj y
          rw [eπ'] at h0
          exact h0
        | succ n => exact (T.π'_lev (n + 1) hj y).trans (congrFun eπ' _) }
  have hT'n : D.TowerNormalised T' := by
    intro j hj
    cases j with
    | zero => exact ⟨hW, hW', hN⟩
    | succ n => exact hTn (n + 1) hj

  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hP
  obtain ⟨L, st, hXL, hQQ, hq, hinv, hstar, hstart⟩ :=
    Formalism.FourierDecayAlt.P.level_start_actual Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hP X l0
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k P.r Wp Wq Bs
  have hD : P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 :=
    ⟨hP, hμ.1, hXL, hQQ, hq, hinv, hstar, hstart⟩
  obtain ⟨Θ, hΘ1, hΘ2⟩ := hTL Wp Wq P Bs X μ L st l0 hl1 hl2 hD

  obtain ⟨he1, he2, he3⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frameVec_facts Bs ν' m₀ hF
  obtain ⟨TP⟩ := Formalism.FourierDecayAlt.P.type_projectors_exist Wp Wq P Bs.z Bs.z' Bs.π Bs.π' (m₀ *ᵥ ν') hP he1 he2 he3
  exact ⟨⟨l0, T', ν', m₀, Θ, TP, ⟨hl1, hl2, hk⟩, hT'n, hF, hP, ⟨X, μ, L, st, hD, hΘ1⟩⟩, rfl, rfl, rfl, rfl, hΘ2⟩

end GlobalTheory.ThA
end

section

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
namespace GlobalTheory.TypeAsm.CompatPf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}

theorem fixedFrameOfWord_isotropic_eq_flag : (F0 X u).X = (X.Fu u).X := by
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa FlagG.X
  congr 1
  ext x
  constructor
  · rintro ⟨b, -, rfl⟩; exact ⟨b, (fv_cast _ b).symm⟩
  · rintro ⟨b, rfl⟩; exact ⟨b, b.2, fv_cast _ b⟩

theorem compatC : CompatC := by
  rintro D X Y u ⟨s₁, s₂⟩ ⟨-, -, hp⟩
  have hp' : rowOf Y.TR (Y.cs u) (Y.cs u) s₁ = rowOf Y.TR (Y.cs u) (Y.cs u) s₂ := hp
  have hl : s₁.lam = s₂.lam := congrArg (fun r => r.1.1) hp'
  have hl' : s₁.lam' = s₂.lam' := congrArg (fun r => r.2.1.1) hp'
  have hi : iotaOf Y.TR (Y.cs u) (Y.cs u) s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u) s₂ := congrArg (fun r => r.2.2) hp'
  have h := (Formalism.L2.SG.Pf.Act.ratIotaC' Y u u s₁ s₂ hl hl').1 (Formalism.L2.SG.Pf.iotaDict_fwd Y s₁ s₂ hl hl' hi)
  refine ⟨hl, hl', fun x hx => ?_⟩
  have hx2 : x ∈ GlobalTheory.HermLat.perp (HV D) (F0 X u).X := hx.2
  rw [GlobalTheory.HermLat.mem_perp_iff, fixedFrameOfWord_isotropic_eq_flag] at hx2
  have hx' : x ∈ Lrep s₁.lam (lf D (X.Fu u)) := by
    refine ⟨hx.1, ?_⟩
    show x ∈ orth (VS D) (X.Fu u).X
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    exact hx2
  have h2 := h x hx'
  unfold NgX at h2
  rw [sup_assoc, sup_idem] at h2
  rw [fixedFrameOfWord_isotropic_eq_flag]
  refine SetLike.le_def.1 (sup_le_sup ?_ le_rfl) h2
  rw [Submodule.ideal_span_singleton_smul]
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, hy, rfl⟩
end GlobalTheory.TypeAsm.CompatPf
end
end
