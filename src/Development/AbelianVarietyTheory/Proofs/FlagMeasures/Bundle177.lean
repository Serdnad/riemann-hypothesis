module

public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.FormalDegreeBessel.FinalG
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GroupFactorizationHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle099
public import Mathlib.MeasureTheory.Constructions.Pi
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
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
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal

namespace GlobalTheory.Amp.RootMove

variable {k r : ℕ}

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
theorem _root_.GlobalTheory.Amp.RootMove.det_Hpk : IsUnit (_root_.Formalism.QuantumDeterminants.Hpk k r).det := by
  refine isUnit_iff_exists_inv.2 ⟨(_root_.Formalism.QuantumDeterminants.Hpk k r).det, ?_⟩
  rw [← Matrix.det_mul, _root_.Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.det_one]

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
theorem _root_.GlobalTheory.Amp.RootMove.unit_det {g : _root_.Formalism.MainNotions.S.MatKR k r} (hg : g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)) :
    IsUnit g.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg

def lr (a b : MatKR k r) : Mt k r → Mt k r := fun x => fun i j => (a * Matrix.of x * b) i j

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
theorem _root_.GlobalTheory.Amp.RootMove.continuous_lr (a b : _root_.Formalism.MainNotions.S.MatKR k r) :
    Continuous (_root_.GlobalTheory.Amp.RootMove.lr a b) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [_root_.GlobalTheory.Amp.RootMove.lr, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
private theorem isClosed_Nset' : IsClosed (_root_.Formalism.QuantumDeterminants.Nset k r) := by
  have hent : ∀ i j, Continuous fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => g i j :=
    fun i j => (continuous_apply j).comp (continuous_apply i)
  have e : _root_.Formalism.QuantumDeterminants.Nset k r = {g | gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * g = _root_.Formalism.QuantumDeterminants.Hpk k r} ∩
      ((⋂ (a : Fin r) (i : Fin (2 * r + k + 1)) (_ : (a : ℕ) ≤ i),
        {g | g i (_root_.Formalism.QuantumDeterminants.eI k r a) = if i = _root_.Formalism.QuantumDeterminants.eI k r a then 1 else 0}) ∩
      ⋂ (i : Fin (2 * r + k + 1)) (j : Fin (2 * r + k + 1)) (_ : r ≤ (j : ℕ)) (_ : (j : ℕ) ≤ r + k)
        (_ : r ≤ (i : ℕ)), {g | g i j = if i = j then 1 else 0}) := by
    ext g
    simp only [_root_.Formalism.QuantumDeterminants.Nset, _root_.Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsClosed.inter (isClosed_eq ?_ continuous_const) (IsClosed.inter ?_ ?_)
  · exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  · exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_eq (hent _ _) continuous_const
  · exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_eq (hent _ _) continuous_const

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
theorem _root_.GlobalTheory.Amp.RootMove.measurableSet_notR (g : _root_.Formalism.MainNotions.S.MatKR k r) :
    MeasurableSet {x : _root_.Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∉ _root_.Formalism.MainNotions.S.Rset k r g} := by
  have h1 : Continuous fun x : _root_.Formalism.QuantumDeterminants.Mt k r =>
      (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := continuous_id
  have h2 : Continuous fun x : _root_.Formalism.QuantumDeterminants.Mt k r =>
      (g * Matrix.of x * g⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
    (continuous_const.matrix_mul h1).matrix_mul continuous_const
  have hc : IsClosed {x : _root_.Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ _root_.Formalism.MainNotions.S.Rset k r g} :=
    (isClosed_Nset'.preimage h1).inter (isClosed_Nset'.preimage h2)
  exact hc.measurableSet.compl

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
theorem _root_.GlobalTheory.Amp.RootMove.measurable_rootCoords (z : Fin (2 * r + k + 1) → ℂ) (p : _root_.Formalism.MainNotions.S.Point ℂ (r + 1)) :
    Measurable (_root_.Formalism.MainNotions.S.rootCoords k r z p) := by
  refine Measurable.of_eval fun q => Continuous.measurable ?_
  by_cases hi : ((q : Fin (r + 1) × Fin (r + 1)).1 : ℕ) < r
  · simp only [_root_.Formalism.MainNotions.S.rootCoords, _root_.Formalism.MainNotions.S.flagMat, hi, dite_true, Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop
  · simp only [_root_.Formalism.MainNotions.S.rootCoords, _root_.Formalism.MainNotions.S.flagMat, hi, dite_false]
    exact continuous_const

open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
private theorem flagMat_conj_eq_of_mem_UWset {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ _root_.Formalism.QuantumDeterminants.UWset k r z)
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    _root_.Formalism.MainNotions.S.flagMat k r z (h * X * h⁻¹) = _root_.Formalism.MainNotions.S.flagMat k r z X := by
  have hfix : ∀ {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}, g ∈ _root_.Formalism.QuantumDeterminants.UWset k r z →
      ∀ c, g *ᵥ _root_.Formalism.QuantumDeterminants.fvec k r z c = _root_.Formalism.QuantumDeterminants.fvec k r z c := by
    intro g hg c
    obtain ⟨-, hb, hz⟩ := hg
    unfold _root_.Formalism.QuantumDeterminants.fvec
    split_ifs with hc
    · exact (hb _).1
    · exact hz
  obtain ⟨hU, hb, -⟩ := id hh
  have hrow : ∀ (a : Fin r) (j : Fin (2 * r + k + 1)),
      h (_root_.Formalism.QuantumDeterminants.eI k r a) j = if _root_.Formalism.QuantumDeterminants.eI k r a = j then 1 else 0 := by
    intro a j
    have hτ : _root_.Formalism.QuantumDeterminants.WeylGroupFacts.tau k r (_root_.Formalism.QuantumDeterminants.esI k r a) = _root_.Formalism.QuantumDeterminants.eI k r a := by
      have := a.isLt
      ext
      simp only [_root_.Formalism.QuantumDeterminants.WeylGroupFacts.tau, _root_.Formalism.QuantumDeterminants.esI, _root_.Formalism.QuantumDeterminants.eI]
      by_cases hc : 2 * r + k - (a : ℕ) < r ∨ r + k < 2 * r + k - (a : ℕ)
      · simp only [hc, ↓reduceIte]; omega
      · omega
    rw [← hτ]
    exact _root_.Formalism.QuantumDeterminants.WeylGroupFacts.row_of_fixed_col hU _ (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.col_of_fix (hb a).2) j
  ext i j
  simp only [_root_.Formalism.MainNotions.S.flagMat, Matrix.of_apply]
  split_ifs with hi
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfix (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh), _root_.Formalism.QuantumDeterminants.WeylGroupFacts.mulVec_apply_of_row _ _ (hrow _)]
  all_goals rfl


open MeasureTheory Matrix in
open scoped ENNReal in
variable {k r : ℕ} in
theorem _root_.GlobalTheory.Amp.RootMove.rootMeas_move : ∀ (D : _root_.Formalism.BasicNotions.D7) (z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (p : _root_.Formalism.MainNotions.S.Point ℂ (D.R.rS + 1)) (g a a' : _root_.Formalism.MainNotions.S.MatKR D.R.k D.R.rS) (μ : Measure (_root_.Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)), _root_.Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z → _root_.Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z' → 0 < _root_.Formalism.QuantumDeterminants.Tz D.R.k D.R.rS z → 0 < _root_.Formalism.QuantumDeterminants.Tz D.R.k D.R.rS z' → g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) → a ∈ _root_.Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z → a' ∈ _root_.Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z' → _root_.Formalism.MainNotions.S.IsRootMeasR D z z' p g μ → _root_.Formalism.MainNotions.S.IsRootMeasR D z z' p (a * g * a'⁻¹) (μ.map fun x => fun i j => (a' * Matrix.of x * a'⁻¹) i j) := by
  intro D z z' p g a a' μ hz hz' _ _ _ ha ha' hμ
  obtain ⟨h, hh, m, hm, rfl⟩ := ha
  obtain ⟨h', hh', m', hm', rfl⟩ := ha'
  obtain ⟨n, hn, n', hn', g₀, rfl, hZ, μ₀, hnull, hmap, rfl⟩ := hμ
  have hd : IsUnit h.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  have hd' : IsUnit h'.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh'.1
  have hdm' : IsUnit m'.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh ((_root_.Formalism.QuantumDeterminants.WeylGroupFacts.nset_iff m').1 hm').1
  have hc' : Continuous (_root_.GlobalTheory.Amp.RootMove.lr h' h'⁻¹) :=
    _root_.GlobalTheory.Amp.RootMove.continuous_lr h' h'⁻¹
  refine ⟨h * (m * n) * h⁻¹, (_root_.Formalism.QuantumDeterminants.uWNormal _ _ z hz h hh _ (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul hm hn)).1,
    h' * (n' * m'⁻¹) * h'⁻¹, (_root_.Formalism.QuantumDeterminants.uWNormal _ _ z' hz' h' hh' _ (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_mul hn' (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hm'))).1,
    h * g₀ * h'⁻¹, ?_, ?_, μ₀.map (_root_.GlobalTheory.Amp.RootMove.lr h' h'⁻¹), ?_, ?_, ?_⟩
  · rw [Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd,
      Matrix.nonsing_inv_mul_cancel_left _ _ hd']
  · have hF : h⁻¹ * _root_.Formalism.QuantumDeterminants.Fm _ _ z = _root_.Formalism.QuantumDeterminants.Fm _ _ z := _root_.Formalism.QuantumDeterminants.UW_F (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh)
    have hF' : h'⁻¹ * _root_.Formalism.QuantumDeterminants.Fm _ _ z' = _root_.Formalism.QuantumDeterminants.Fm _ _ z' := _root_.Formalism.QuantumDeterminants.UW_F (_root_.Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh')
    have hU : (h⁻¹)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h⁻¹ = _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hh.1
    have hU2 : (h⁻¹)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h := by
      conv_rhs => rw [← hU]
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]
    have key : (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h = (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
      rw [Matrix.mul_assoc, ← hU2, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hF]
    have E : (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (h * g₀ * h'⁻¹) * _root_.Formalism.QuantumDeterminants.Fm _ _ z' =
        (_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * g₀ * _root_.Formalism.QuantumDeterminants.Fm _ _ z' := by
      calc _ = ((_root_.Formalism.QuantumDeterminants.Fm _ _ z)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * h) * g₀ * (h'⁻¹ * _root_.Formalism.QuantumDeterminants.Fm _ _ z') := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [key, hF']
    rw [← hZ]
    unfold _root_.Formalism.MainNotions.S.ZhatO
    rw [_root_.Formalism.QuantumDeterminants.Zhat_eq, _root_.Formalism.QuantumDeterminants.Zhat_eq, E]
  · rw [Measure.map_apply hc'.measurable (_root_.GlobalTheory.Amp.RootMove.measurableSet_notR _)]
    refine measure_mono_null ?_ hnull
    intro x hx
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx ⊢
    intro hR
    apply hx
    obtain ⟨hR1, hR2⟩ := hR
    have e : (h * g₀ * h'⁻¹) * (h' * Matrix.of x * h'⁻¹) * (h * g₀ * h'⁻¹)⁻¹ =
        h * (g₀ * Matrix.of x * g₀⁻¹) * h⁻¹ := by
      simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd', Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_left _ _ hd']
    refine ⟨(_root_.Formalism.QuantumDeterminants.uWNormal _ _ z' hz' h' hh' _ hR1).1, ?_⟩
    change (h * g₀ * h'⁻¹) * (h' * Matrix.of x * h'⁻¹) * (h * g₀ * h'⁻¹)⁻¹ ∈ _
    rw [e]
    exact (_root_.Formalism.QuantumDeterminants.uWNormal _ _ z hz h hh _ hR2).1
  · rw [Measure.map_map (_root_.GlobalTheory.Amp.RootMove.measurable_rootCoords z' p) hc'.measurable]
    convert hmap using 2
    funext x
    have hx := flagMat_conj_eq_of_mem_UWset hh' (Matrix.of x)
    simp only [Function.comp_apply]
    unfold _root_.Formalism.MainNotions.S.rootCoords
    exact congrArg (fun M => fun q : ↥(_root_.Formalism.MainNotions.S.rootPat p) => M q.1.1 q.1.2) hx
  · have E : ∀ X : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
        (h' * m') * (n'⁻¹ * X * n') * (h' * m')⁻¹ =
          (h' * (n' * m'⁻¹) * h'⁻¹)⁻¹ * (h' * X * h'⁻¹) * (h' * (n' * m'⁻¹) * h'⁻¹) := by
      intro X
      simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hd',
        Matrix.nonsing_inv_nonsing_inv _ hdm', Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_left _ _ hd']
    rw [Measure.map_map, Measure.map_map]
    · congr 1
      funext x i j
      exact congrArg (fun M : Matrix _ _ ℂ => M i j) (E (Matrix.of x))
    all_goals exact (_root_.GlobalTheory.Amp.RootMove.continuous_lr _ _).measurable

end GlobalTheory.Amp.RootMove
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory

noncomputable def leftMulEntries {n : ℕ} (a : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (Fin n → Fin n → ℂ) ≃L[ℂ] (Fin n → Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x i j => ((a : Matrix (Fin n) (Fin n) ℂ) * Matrix.of x) i j
      invFun := fun x i j => (((a⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.of x) i j
      map_add' := fun x y => by
        have h := Matrix.mul_add (a : Matrix (Fin n) (Fin n) ℂ) (Matrix.of x) (Matrix.of y)
        exact h
      map_smul' := fun c x => by
        have h := Matrix.mul_smul (a : Matrix (Fin n) (Fin n) ℂ) c (Matrix.of x)
        exact h
      left_inv := fun x => by
        have h := Units.inv_mul_cancel_left a (Matrix.of x)
        exact h
      right_inv := fun x => by
        have h := Units.mul_inv_cancel_left a (Matrix.of x)
        exact h }

private lemma inUJ_of_mem_Kset' {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) : Formalism.REAL.inUJ ε g := by
  have hu : star g * g = 1 := Unitary.star_mul_self_of_mem hg.1
  unfold Formalism.REAL.inUJ
  rw [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, hu, Matrix.one_mul]

private lemma mul_mem_Kset {n : ℕ} {ε : Fin n → Bool} {g g' : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) (hg' : g' ∈ Formalism.REAL.Kset ε) : g * g' ∈ Formalism.REAL.Kset ε := by
  refine ⟨Submonoid.mul_mem _ hg.1 hg'.1, ?_⟩
  rw [Matrix.mul_assoc, hg'.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]

private lemma exists_UJ_umat_eq_of_mem_Kset {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.REAL.Kset ε) : ∃ k : Formalism.REAL.UJ ε, umat k = g :=
  ⟨⟨⟨g, star g, Unitary.mul_star_self_of_mem hg.1, Unitary.star_mul_self_of_mem hg.1⟩,
    inUJ_of_mem_Kset' hg⟩, rfl⟩

theorem exists_smooth_average_eq_of_mem_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (w : H), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → w ∈ lowKSub ε lam σ → w ≠ 0 → ∀ u ∈ lowKSub ε lam σ, ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧ u = ∫ g : UJ ε, F (fun i j => umat g i j) • σ (umat g) w ∂(muG ε) := by
  intro n ε H _ _ _ σ lam w hrep hK hw hw0 u hu
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have humat : Continuous fun g : Formalism.REAL.UJ ε => umat g :=
    Units.continuous_val.comp continuous_subtype_val
  have hcont : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) w :=
    (hrep.2.2 w).comp_continuous humat hmem
  have he : Continuous fun g : Formalism.REAL.UJ ε => (fun i j => umat g i j : Fin n → Fin n → ℂ) := humat

  have hint : ∀ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F → HasCompactSupport F →
      HasCompactSupport (fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j)) →
      Integrable (fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j) • σ (umat g) w) (muG ε) := by
    intro F hFd _ hFg
    have hc : Continuous fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j) := hFd.continuous.comp he
    exact (hc.smul hcont).integrable_of_hasCompactSupport
      (hFg.smul_right (f' := fun g : Formalism.REAL.UJ ε => σ (umat g) w))

  obtain ⟨α, hαs, hαc, hαfix⟩ := exists_smooth_fix_lowKSub n ε lam H σ hrep hK
  obtain ⟨F0, hF0d, hF0c, hF0e⟩ :=
    smoothOnG_exists_contDiff_compactSupport_extension n ε α hαs hαc
  have hF0g : HasCompactSupport (fun g : Formalism.REAL.UJ ε => F0 (fun i j => umat g i j)) := by
    have hfun : (fun g : Formalism.REAL.UJ ε => F0 (fun i j => umat g i j)) = fun g => α (umat g) :=
      funext fun g => (hF0e g).symm
    rw [hfun]
    exact hαc
  have hbase : ∫ g, F0 (fun i j => umat g i j) • σ (umat g) w ∂(muG ε) = w := by
    refine ext_inner_left ℂ fun v => ?_
    rw [← integral_inner (hint F0 hF0d hF0c hF0g) v]
    simp_rw [inner_smul_right, ← hF0e]
    exact hαfix w hw v

  let T : Submodule ℂ H :=
    { carrier := {v | ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
          HasCompactSupport (fun g : Formalism.REAL.UJ ε => F (fun i j => umat g i j)) ∧
          v = ∫ g, F (fun i j => umat g i j) • σ (umat g) w ∂(muG ε)}
      add_mem' := by
        rintro _ _ ⟨F1, h1d, h1c, h1g, rfl⟩ ⟨F2, h2d, h2c, h2g, rfl⟩
        refine ⟨fun y => F1 y + F2 y, h1d.add h2d, h1c.add h2c, h1g.add h2g, ?_⟩
        rw [← integral_add (hint F1 h1d h1c h1g) (hint F2 h2d h2c h2g)]
        simp only [add_smul]
      zero_mem' := by
        refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, HasCompactSupport.zero, ?_⟩
        simp
      smul_mem' := by
        rintro c _ ⟨F1, h1d, h1c, h1g, rfl⟩
        refine ⟨fun y => c * F1 y, contDiff_const.mul h1d, h1c.mul_left, h1g.mul_left, ?_⟩
        rw [← integral_smul]
        simp only [mul_smul] }

  have hgen : ∀ g ∈ Formalism.REAL.Kset ε, σ g w ∈ T := by
    intro g hg
    obtain ⟨k, rfl⟩ := exists_UJ_umat_eq_of_mem_Kset hg
    let a : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((k⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    have hshift : ∀ x : Formalism.REAL.UJ ε,
        leftMulEntries a (fun i j => umat x i j) = fun i j => umat (k⁻¹ * x) i j := fun x => rfl
    refine ⟨fun y => F0 (leftMulEntries a y), ?_, ?_, ?_, ?_⟩
    · exact hF0d.comp ((leftMulEntries a).contDiff.restrict_scalars ℝ)
    · exact hF0c.comp_homeomorph (leftMulEntries a).toHomeomorph
    · simp only [hshift]
      exact hF0g.comp_homeomorph (Homeomorph.mulLeft k⁻¹)
    · simp only [hshift]
      have hinv := integral_mul_left_eq_self (μ := muG ε)
        (fun x : Formalism.REAL.UJ ε => F0 (fun i j => umat (k⁻¹ * x) i j) • σ (umat x) w) k
      simp only [inv_mul_cancel_left] at hinv
      rw [← hinv]
      have hmul : ∀ x : Formalism.REAL.UJ ε, F0 (fun i j => umat x i j) • σ (umat (k * x)) w
          = σ (umat k) (F0 (fun i j => umat x i j) • σ (umat x) w) := by
        intro x
        rw [map_smul]
        congr 1
        show σ (umat k * umat x) w = σ (umat k) (σ (umat x) w)
        rw [hrep.1.2 _ (hmem k) _ (hmem x)]
        rfl
      simp_rw [hmul]
      rw [ContinuousLinearMap.integral_comp_comm _ (hint F0 hF0d hF0c hF0g), hbase]

  let S' : Submodule ℂ H := Submodule.span ℂ {v | ∃ g ∈ Formalism.REAL.Kset ε, v = σ g w}
  have hS'le : S' ≤ lowKSub ε lam σ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    exact hK.2.1 g hg w hw
  have hS'st : IsKStableOn ε σ S' := by
    intro g hg v hv
    have hle : S' ≤ S'.comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g', hg', rfl⟩
      show σ g (σ g' w) ∈ S'
      refine Submodule.subset_span ⟨g * g', mul_mem_Kset hg hg', ?_⟩
      rw [hrep.1.2 g (inUJ_of_mem_Kset' hg) g' (inUJ_of_mem_Kset' hg')]
      rfl
    exact hle hv
  have h1K : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Formalism.REAL.Kset ε :=
    ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩
  have hwS' : w ∈ S' := Submodule.subset_span ⟨1, h1K, by rw [hrep.1.1]; rfl⟩
  have hS'eq : S' = lowKSub ε lam σ := by
    rcases hK.2.2.1 S' hS'le hS'st with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hwS')) hw0
    · exact h
  have huS' : u ∈ S' := by rw [hS'eq]; exact hu
  have huT : u ∈ T := Submodule.span_le.2 (by rintro _ ⟨g, hg, rfl⟩; exact hgen g hg) huS'
  obtain ⟨F, hFd, hFc, _, hFu⟩ := huT
  exact ⟨F, hFd, hFc, hFu⟩

end GlobalTheory
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem measurePreserving_rearrange (V V' V'' : Type) [Fintype V] [Fintype V'] [Fintype V''] (β : V ≃ V')
    (σ : V ≃ V'') (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (Y : V'' → Type)
    [∀ w, MeasurableSpace (Y w)] (m : ∀ i, Measure (X i)) [∀ i, SigmaFinite (m i)] (ν : ∀ w, Measure (Y w))
    [∀ w, SigmaFinite (ν w)] (b : Fin a → ℝ) (c : V'' → ℝ) (hb : ∀ i, 0 ≤ b i) (hc : ∀ w, 0 ≤ c w) :
    MeasurePreserving
      (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v)))
      (((∏ i, ENNReal.ofReal (b i ^ Fintype.card V)) * ENNReal.ofReal (∏ w, c w)) •
        (Measure.pi fun i => Measure.pi fun _ : V' => m i).prod (Measure.pi ν))
      (Measure.pi fun v : V => (Measure.pi fun i => ENNReal.ofReal (b i) • m i).prod
        (ENNReal.ofReal (c (σ v)) • ν (σ v))) := by
  have hm : Measurable
      (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v))) := by
    fun_prop
  refine ⟨hm, ?_⟩
  refine (Measure.pi_eq_generateFrom
    (C := fun v => Set.image2 (· ×ˢ ·)
      (Set.pi Set.univ '' Set.pi Set.univ fun i => {s : Set (X i) | MeasurableSet s})
      {s : Set (Y (σ v)) | MeasurableSet s})
    (fun v => (generateFrom_eq_prod generateFrom_pi MeasurableSpace.generateFrom_measurableSet
      (IsCountablySpanning.pi fun _ => isCountablySpanning_measurableSet)
      isCountablySpanning_measurableSet))
    (fun _ => isPiSystem_pi.prod MeasurableSpace.isPiSystem_measurableSet)
    (fun v => (Measure.FiniteSpanningSetsIn.pi fun i =>
      (ENNReal.ofReal (b i) • m i).toFiniteSpanningSetsIn).prod
        (ENNReal.ofReal (c (σ v)) • ν (σ v)).toFiniteSpanningSetsIn) ?_).symm
  intro s hs
  choose t' ht' u hu hst using hs
  choose t ht htt using ht'
  have htm : ∀ v i, MeasurableSet (t v i) := fun v i => ht v i (Set.mem_univ _)
  have hs' : ∀ v, s v = (Set.pi Set.univ (t v)) ×ˢ u v := fun v => by rw [← hst v, htt v]
  have hsm : MeasurableSet (Set.pi Set.univ s) := by
    refine MeasurableSet.univ_pi fun v => ?_
    rw [hs' v]
    exact (MeasurableSet.univ_pi fun i => htm v i).prod (hu v)
  obtain ⟨u', hu'⟩ : ∃ u' : ∀ w, Set (Y w), ∀ v, u' (σ v) = u v :=
    ⟨Equiv.piCongrLeft (fun w => Set (Y w)) σ u, fun v => Equiv.piCongrLeft_apply_apply _ _ _ _⟩
  rw [Measure.map_apply hm hsm]
  have hpre : (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v))) ⁻¹'
      Set.pi Set.univ s =
      (Set.pi Set.univ fun i => Set.pi Set.univ fun v' => t (β.symm v') i) ×ˢ Set.pi Set.univ u' := by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, hs', Set.mem_prod, forall_and]
    refine and_congr ?_ ?_
    · rw [forall_comm]
      refine forall_congr' fun i => ?_
      rw [← β.forall_congr_right]
      simp only [Equiv.symm_apply_apply]
    · rw [← σ.forall_congr_right]
      simp only [hu']
  rw [hpre, Measure.smul_apply, Measure.prod_prod]
  simp only [hs', Measure.prod_prod, Measure.pi_pi, Measure.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  have h1 : ∏ i, ∏ v', m i (t (β.symm v') i) = ∏ v, ∏ i, m i (t v i) := by
    rw [Finset.prod_comm]
    exact β.symm.prod_comp fun v => ∏ i, m i (t v i)
  have h2 : ∏ w, ν w (u' w) = ∏ v, ν (σ v) (u v) := by
    rw [← σ.prod_comp]
    simp only [hu']
  have h3 : ENNReal.ofReal (∏ w, c w) = ∏ v, ENNReal.ofReal (c (σ v)) := by
    rw [ENNReal.ofReal_prod_of_nonneg fun w _ => hc w, ← σ.prod_comp]
  have h4 : ∏ i, ENNReal.ofReal (b i ^ Fintype.card V) = (∏ i, ENNReal.ofReal (b i)) ^ Fintype.card V := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => ENNReal.ofReal_pow (hb i) _
  rw [h1, h2, h3, h4]
  ring

end GlobalTheory.LeviIso
end
