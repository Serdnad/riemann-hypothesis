module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsUnitriGlEquiv
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle129
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasis
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle156
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle158
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle157
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle154
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QuasiOfFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.BlockUni

theorem unitri_isUnit {R : Type} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (h0 : ∀ i j, j < i → A i j = 0) (h1 : ∀ i, A i i = 1) : IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hb : A.BlockTriangular id := fun i j h => h0 i j h
  rw [Matrix.det_of_upperTriangular hb]
  simp [h1]

theorem snoc_uni_iff : ∀ (R : Type) [CommRing R] (n σ : ℕ) (M : Matrix (Fin n) (Fin σ) R) (w : Fin n → R) (Y : Matrix (Fin n) (Fin n) R), (∃ U ∈ GlobalTheory.UniIndexPrime.uniSub (σ + 1) R, Y * Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) = Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) * (U : Matrix (Fin (σ + 1)) (Fin (σ + 1)) R)) ↔ ∃ u ∈ GlobalTheory.UniIndexPrime.uniSub σ R, ∃ v : Fin σ → R, Y * M = M * (u : Matrix (Fin σ) (Fin σ) R) ∧ Y *ᵥ w = w + M *ᵥ v := by
  intro R _ n σ M w Y
  set x : Matrix (Fin n) (Fin (σ+1)) R := Matrix.of (fun k => Fin.snoc (α := fun _ => R) (M k) (w k)) with hx
  have hxc : ∀ k i, x k (Fin.castSucc i) = M k i := by intro k i; simp [hx]
  have hxl : ∀ k, x k (Fin.last σ) = w k := by intro k; simp [hx]
  have col : ∀ (U : Matrix (Fin (σ+1)) (Fin (σ+1)) R) k j,
      (x * U) k j = ∑ i, M k i * U (Fin.castSucc i) j + w k * U (Fin.last σ) j := by
    intro U k j; rw [Matrix.mul_apply, Fin.sum_univ_castSucc]; simp only [hxc, hxl]
  have Ycol : ∀ k j, (Y * x) k (Fin.castSucc j) = (Y * M) k j := by
    intro k j; simp only [Matrix.mul_apply, hxc]
  have Ylast : ∀ k, (Y * x) k (Fin.last σ) = (Y *ᵥ w) k := by
    intro k; simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, hxl]
  constructor
  · rintro ⟨U, hU, hE⟩
    have hU' := (GlobalTheory.UniIndexPrime.mem_uniSub U).1 hU
    let u : Matrix (Fin σ) (Fin σ) R := Matrix.of fun i j => (U : Matrix _ _ R) (Fin.castSucc i) (Fin.castSucc j)
    have hu0 : ∀ i j, j < i → u i j = 0 := fun i j h =>
      hU'.1 (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc_lt_castSucc_iff.2 h)
    have hu1 : ∀ i, u i i = 1 := fun i => hU'.2 _
    refine ⟨(unitri_isUnit u hu0 hu1).unit, (GlobalTheory.UniIndexPrime.mem_uniSub _).2 ⟨hu0, hu1⟩,
      fun i => (U : Matrix _ _ R) (Fin.castSucc i) (Fin.last σ), ?_, ?_⟩
    · ext k j
      have h := congrFun (congrFun hE k) (Fin.castSucc j)
      rw [Ycol, col] at h
      rw [h, IsUnit.unit_spec, Matrix.mul_apply]
      have h0 : (U : Matrix _ _ R) (Fin.last σ) (Fin.castSucc j) = 0 := hU'.1 _ _ (Fin.castSucc_lt_last j)
      simp [h0, u]
    · ext k
      have h := congrFun (congrFun hE k) (Fin.last σ)
      rw [Ylast, col, hU'.2 (Fin.last σ)] at h
      rw [h]; simp only [Pi.add_apply, Matrix.mulVec, dotProduct]; ring
  · rintro ⟨u, hu, v, h1, h2⟩
    have hu' := (GlobalTheory.UniIndexPrime.mem_uniSub u).1 hu
    let U : Matrix (Fin (σ+1)) (Fin (σ+1)) R := Matrix.of fun a b =>
      Fin.lastCases (Fin.lastCases (1 : R) (fun _ => 0) b)
        (fun i => Fin.lastCases (v i) (fun j => (u : Matrix _ _ R) i j) b) a
    have Ucc : ∀ i j, U (Fin.castSucc i) (Fin.castSucc j) = (u : Matrix _ _ R) i j := by
      intro i j; simp [U]
    have Ucl : ∀ i, U (Fin.castSucc i) (Fin.last σ) = v i := by intro i; simp [U]
    have Ulc : ∀ j, U (Fin.last σ) (Fin.castSucc j) = 0 := by intro j; simp [U]
    have Ull : U (Fin.last σ) (Fin.last σ) = 1 := by simp [U]
    have hU0 : ∀ a b, b < a → U a b = 0 := by
      intro a b hab
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => exact absurd hab (lt_irrefl _)
        | cast j => exact Ulc j
      | cast i =>
        induction b using Fin.lastCases with
        | last => exact absurd hab (not_lt.2 (Fin.castSucc_lt_last i).le)
        | cast j => rw [Ucc]; exact hu'.1 i j (Fin.castSucc_lt_castSucc_iff.1 hab)
    have hU1 : ∀ a, U a a = 1 := by
      intro a
      induction a using Fin.lastCases with
      | last => exact Ull
      | cast i => rw [Ucc]; exact hu'.2 i
    refine ⟨(unitri_isUnit U hU0 hU1).unit, (GlobalTheory.UniIndexPrime.mem_uniSub _).2 ⟨hU0, hU1⟩, ?_⟩
    rw [IsUnit.unit_spec]
    ext k b
    induction b using Fin.lastCases with
    | last =>
      rw [Ylast, col, h2, Ull]
      simp only [Ucl, Pi.add_apply, Matrix.mulVec, dotProduct]; ring
    | cast j =>
      rw [Ycol, col, h1, Matrix.mul_apply]
      simp only [Ucc, Ulc]; ring

end GlobalTheory.BlockUni
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory

theorem glChar_transvection {R : Type} [CommRing R] (h2 : IsUnit (2 : R)) {n : ℕ}
    (α : GL (Fin n) R →* Circle) (i j : Fin n) (hij : i ≠ j) (t : R)
    (u : GL (Fin n) R) (hu : u.1 = Matrix.transvection i j t) : α u = 1 := by
  obtain ⟨w, hw⟩ := h2
  let f : Fin n → R := Function.update 1 i 2
  let g : Fin n → R := Function.update 1 i (↑w⁻¹ : R)
  have hfg : ∀ k, f k * g k = 1 := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [f, g, ← hw]
    · simp [f, g, hk]
  have hgf : ∀ k, g k * f k = 1 := fun k => by rw [mul_comm]; exact hfg k
  let d : GL (Fin n) R :=
    ⟨Matrix.diagonal f, Matrix.diagonal g,
      by rw [Matrix.diagonal_mul_diagonal]; simp [hfg],
      by rw [Matrix.diagonal_mul_diagonal]; simp [hgf]⟩
  have hcomm : d * u = u * u * d := by
    apply Units.ext
    have hfi : f i = 2 := by simp [f]
    have hfj : f j = 1 := by simp [f, hij.symm]
    change Matrix.diagonal f * u.1 = u.1 * u.1 * Matrix.diagonal f
    rw [hu, Matrix.transvection_mul_transvection_same _ _ hij]
    ext a b
    simp only [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
      Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply,
      Matrix.diagonal_apply, Matrix.one_apply]
    clear_value f g d
    clear hfg hgf
    split_ifs <;> subst_vars <;> simp_all <;> ring
  have h := congrArg α hcomm
  simp only [map_mul] at h
  have h' : α d * α u = α d * (α u * α u) := by rw [h]; exact mul_comm _ _ |>.trans (by rfl)
  have h'' := mul_left_cancel h'
  exact (mul_eq_left.mp h''.symm)

theorem glChar_eq_one_of_det_eq_one : ∀ (D : D7) (n : ℕ) (α : GL (Fin n) (AE D) →* Circle),
    Continuous α → ∀ a, Matrix.GeneralLinearGroup.det a = 1 → α a = 1 := by
  intro D n α _ a ha
  have h2 : IsUnit (2 : AE D) := by
    have h := (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map (algebraMap D.host.F (AE D))
    rwa [map_ofNat] at h
  have := GlobalTheory.T.special_linear_generated_by_transvections (AE D) (GlobalTheory.T.stableRangeOne_adeles_cmField D) n α.ker
    (fun i j hij t u hu => MonoidHom.mem_ker.mpr (glChar_transvection h2 α i j hij t u hu)) a ha
  exact MonoidHom.mem_ker.mp this

end GlobalTheory
end

section


open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HatLatV

variable {D : D7}

def cut (P : Pl D → Prop) (u : Af D.host.F ⊗[D.host.F] D.host.E) : AE D :=
  Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift ((GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) * u)

def cutHom (P : Pl D → Prop) : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D where
  toFun := cut P
  map_zero' := by
    show Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _ = 0
    rw [mul_zero]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift_zero
  map_add' a b := by
    show Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _ = Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _ + Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _
    rw [mul_add]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift_add _ _

theorem cut_tmul (P : Pl D → Prop) (a : Af D.host.F) (x : D.host.E) :
    cut P (a ⊗ₜ[D.host.F] x) = pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP P * a) ⊗ₜ[D.host.F] x := by
  unfold cut
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl



theorem cut_finPart (P : Pl D → Prop) (u : AE D) (hu : u ∈ idAt D P) : cut P (finPart D u) = u := by
  unfold idAt at hu
  rw [Ideal.mem_inf] at hu
  obtain ⟨hinf, hfin⟩ := hu
  rw [RingHom.mem_ker] at hinf
  have hoff : ∀ w : Pl D, ¬ P w → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D u) = 0 := by
    intro w hw
    have := (Submodule.mem_iInf _).1 hfin ⟨w, hw⟩
    exact (RingHom.mem_ker).1 this
  have hcut : (GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D u = finPart D u := by
    refine (sub_eq_zero.mp (GlobalTheory.SelfDualAt.eq_zero_of_compFin _ fun w => ?_)).symm
    rw [map_sub, map_mul]
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) =
        evalV D.host.F w (GlobalTheory.SelfDualAt.indP P) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [hc, GlobalTheory.SelfDualAt.evalV_indP]
    by_cases hw : P w
    · rw [if_pos hw, ← Algebra.TensorProduct.one_def, one_mul, sub_self]
    · rw [if_neg hw, TensorProduct.zero_tmul, zero_mul, sub_zero, hoff w hw]
  unfold cut
  rw [hcut]
  exact (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.eq_lift_of_infPart u hinf).symm

theorem mem_latV_of_hatL : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D),
    (∀ i, y i ∈ idAt D P) →
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → y ∈ latV S L P := by
  intro D S L P y hy hz
  have hlat : (fun i => finPart D (y i)) ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E)) :=
    (GlobalTheory.LevSplit.latHat_iff L _).2 hz
  have key : y = AddMonoidHom.compLeft (cutHom P) (Fin S.rank) (fun i => finPart D (y i)) :=
    funext fun i => (cut_finPart P (y i) (hy i)).symm
  rw [key]
  refine AddSubgroup.closure_induction
    (p := fun u _ => AddMonoidHom.compLeft (cutHom P) (Fin S.rank) u ∈ latV S L P) ?_ ?_ ?_ ?_ hlat
  · rintro _ ⟨a, ha, x, hx, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨GlobalTheory.SelfDualAt.indP P * a, ?_, ?_, 1, rfl, x, hx, ?_⟩
    · intro v
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP]
      split_ifs
      · rw [one_mul]; exact ha v
      · rw [zero_mul]; exact zero_mem _
    · intro v hv
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP, if_neg hv, zero_mul]
    · funext i
      show cut P (a ⊗ₜ[D.host.F] x i) = _
      rw [cut_tmul, one_mul]
  · rw [map_zero]; exact zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact add_mem ha hb
  · intro a _ ha
    rw [map_neg]; exact neg_mem ha

end GlobalTheory.HatLatV

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField

theorem _root_.GlobalTheory.T.exists_GL_embedding_unitaryAdelic_splitPlace_basis : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (b : Matrix (Fin S.rank) n k) (b' : Matrix n (Fin S.rank) k), b * b' = 1 → b' * b = 1 → ∃ gl : GL n k →* GA D S, (∀ g, SuppAt p.e S (gl g)) ∧ ∀ g, (mt S (gl g)).map p.pr = b * g.val * b' := by
  first | exact @GlobalTheory.GlEmbed.exists_gl | exact GlobalTheory.GlEmbed.exists_gl | (intros; apply GlobalTheory.GlEmbed.exists_gl <;> assumption)
end

section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

theorem _root_.GlobalTheory.T.nonempty_concreteRowData_of_finitenessBundle : Formalism.L2.SG.Pf.WuDecayOfGap → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (S : Formalism.L2.SG.SpectralTiesReal.STies D), 29 ≤ C' → 29 ≤ Cl → FinX S.Y → Formalism.L2.SG.Pf.LocCP.LocTied D → TFrameAt D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → Nonempty (Formalism.L2.SG.ThmSOwn.ConcK D) := by
  first | exact @GlobalTheory.Core.Diag.concK_of_finX | exact GlobalTheory.Core.Diag.concK_of_finX | (intros; apply GlobalTheory.Core.Diag.concK_of_finX <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_coprime_multiplier_unipotentPart_congr_zero : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf), m ∈ X.B.I.Kset → m ∈ X.NfinU u → ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0) := by
  first | exact @GlobalTheory.UkPart.ukPart_zmod | exact GlobalTheory.UkPart.ukPart_zmod | (intros; apply GlobalTheory.UkPart.ukPart_zmod <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_coprime_multiplier_levelCharacter_sum_congr : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (m : X.B.I.Gf), m ∈ X.B.I.Kset → ∃ c : ℕ, Nat.Coprime c X.B.g ∧ ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * ∑ a, (hA X.B.I (X.f0 a) ((X.B.I.fmat ((X.xu u)⁻¹ * m * X.xu u) - 1) *ᵥ nxt X.e0 X.z0 a) - hA X.B.I (incl X.B.I (X.fR a)) ((X.B.I.fmat m - 1) *ᵥ incl X.B.I (nxt X.eR (X.zR u) a)))) := by
  first | exact @GlobalTheory.NPartConj.nsum_cong | exact GlobalTheory.NPartConj.nsum_cong | (intros; apply GlobalTheory.NPartConj.nsum_cong <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.real_stabilizer_product_measure_isHaarOnSet : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word), IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  first | exact @GlobalTheory.MuSHaar.muS_isHaarOnSet | exact GlobalTheory.MuSHaar.muS_isHaarOnSet | (intros; apply GlobalTheory.MuSHaar.muS_isHaarOnSet <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_besselRational_cutoff_fundamentalDomain : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (Fs : Set X.B.I.GA), IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ β : X.B.I.GA → ENNReal, Measurable β ∧ (∀ x, ∑' σ : Srat X u, β ((σ : X.B.I.GA) * x) = 1) ∧ ∀ F : X.B.I.GA → ENNReal, Measurable F → (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) → ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ∫⁻ x, β x * F x ∂(X.B.I.muA X.B.μf) := by
  first | exact @GlobalTheory.Core.Mi.Fold.exists_cutoff_srat | exact GlobalTheory.Core.Mi.Fold.exists_cutoff_srat | (intros; apply GlobalTheory.Core.Mi.Fold.exists_cutoff_srat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.haar_finite_adele_disintegration_stabilizer_compact : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word), ∃ μSf : Measure (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)), μSf.IsHaarMeasure ∧ SigmaFinite μSf ∧ ∃ c : ℝ, 0 < c ∧ ∀ φ : X.B.I.Gf → ENNReal, Measurable φ → (∀ x, φ x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x = s * X.xu u * k) → ∫⁻ x, φ x ∂X.B.μf = ENNReal.ofReal c * ∫⁻ t, ∫⁻ k in X.K2, φ (t.1 * X.xu u * k) ∂X.B.μf ∂μSf := by
  first | exact @GlobalTheory.SfinHaar.disint_finPart | exact GlobalTheory.SfinHaar.disint_finPart | (intros; apply GlobalTheory.SfinHaar.disint_finPart <;> assumption)
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.adelic_GL_circle_character_trivial_on_det_one : ∀ (D : D7) (n : ℕ) (α : GL (Fin n) (AE D) →* Circle), Continuous α → ∀ a, Matrix.GeneralLinearGroup.det a = 1 → α a = 1 := by
  first | exact @GlobalTheory.glChar_eq_one_of_det_eq_one | exact GlobalTheory.glChar_eq_one_of_det_eq_one | (intros; apply GlobalTheory.glChar_eq_one_of_det_eq_one <;> assumption)

end
end
