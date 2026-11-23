module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.GramExtendZeroEmbedded
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle010
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle023
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle025
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
import Development.WeilBound.ThetaLifts.TowerModels.LeviAd
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle027
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

@[expose] public section

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Afc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem gram_incM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Matrix (Fin d.m) (Fin d.n) E) :
    d.gram (incM F X) (incM F X) = incM F (gE d.A.J σ X) := by
  have h1 : (incM F X).map (cA σ) = incM F (X.map σ) := by ext i j; rfl
  show (incM F X)ᵀ * incM F d.A.J * (incM F X).map (cA σ) = _
  rw [h1]
  simp only [gE, incM, ← Matrix.transpose_map, ← Matrix.map_mul]
theorem cond_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (X : Matrix (Fin d.m) (Fin d.n) E) (M : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    d.gram (incM F X) (incM F X) = (-2 : ℤ) • M ↔
      ∀ k l, inclR (F := F) (AF F) (gE d.A.J σ X k l) = (-2 : ℤ) • M k l := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.gram_incM_k, ← Matrix.ext_iff]
  rfl
theorem orb_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hmn : d.m < d.n) (T : nF σ d.Y d.b) (hT : IsND T) (Φ : d.Fn) : d.orb T Φ = 0 := by
  have hE : IsEmpty {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} := by
    refine ⟨fun ⟨X, hX⟩ => ?_⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.gram_incM_k] at hX
    have hdet := congrArg Matrix.det hX
    have h0 : (gE d.A.J σ X).det = 0 := by
      by_contra h
      have hu : IsUnit (gE d.A.J σ X) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
      have h1 := Matrix.rank_of_isUnit _ hu
      have h2 : (gE d.A.J σ X).rank ≤ d.m := by
        rw [gE, Matrix.mul_assoc]
        exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
      rw [h1, Fintype.card_fin] at h2
      omega
    have hm : ((gE d.A.J σ X).map (inclR (F := F) (AF F))).det = inclR (F := F) (AF F) (gE d.A.J σ X).det :=
      ((inclR (F := F) (AF F)).map_det _).symm
    rw [incM, hm, h0, map_zero, ← Int.cast_smul_eq_zsmul (AE F E), Matrix.det_smul, Fintype.card_fin] at hdet
    exact hT ((isUnit_neg_two_pow d.n).mul_right_eq_zero.1 hdet.symm)
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.orb, tsum_empty]
section Res
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def extendByZeroColumns (X' : Matrix (Fin d.m) (Fin L.n) E) : Matrix (Fin d.m) (Fin d.n) E := fun a => Function.extend L.em (X' a) 0
theorem extendZeroColumn_apply_embed (X' : Matrix (Fin d.m) (Fin L.n) E) (a : Fin d.m) (j : Fin L.n) : _root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X' a (L.em j) = X' a j :=
  L.inj.extend_apply _ _ _
theorem not_mem_range_k : L.i₀ ∉ Set.range L.em := fun h => ((L.rng L.i₀).2 h) rfl
theorem extendZeroColumn_apply_missing (X' : Matrix (Fin d.m) (Fin L.n) E) (a : Fin d.m) : _root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X' a L.i₀ = 0 :=
  Function.extend_apply' _ _ _ fun ⟨j, hj⟩ => _root_.PositivityTheory.SiegelWeilFormula.Afc.not_mem_range_k L ⟨j, hj⟩
theorem cases_idx_k (k : Fin d.n) : k = L.i₀ ∨ ∃ j, L.em j = k := by
  by_cases h : k = L.i₀
  · exact Or.inl h
  · exact Or.inr ((L.rng k).1 h)
theorem hermForm_extendZeroColumn_embed (X' : Matrix (Fin d.m) (Fin L.n) E) (i j : Fin L.n) :
    gE d.A.J σ (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X') (L.em i) (L.em j) = gE d.A.J σ X' i j := by
  simp only [gE_apply, _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_embed]
theorem hermForm_extendZeroColumn_left (X' : Matrix (Fin d.m) (Fin L.n) E) (l : Fin d.n) : gE d.A.J σ (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X') L.i₀ l = 0 := by
  simp [gE_apply, _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_missing]
theorem hermForm_extendZeroColumn_right (X' : Matrix (Fin d.m) (Fin L.n) E) (k : Fin d.n) : gE d.A.J σ (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X') k L.i₀ = 0 := by
  simp [gE_apply, _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_missing]
theorem gE_sub_k (X : Matrix (Fin d.m) (Fin d.n) E) (i j : Fin L.n) :
    gE d.A.J σ (X.submatrix id L.em) i j = gE d.A.J σ X (L.em i) (L.em j) := by
  simp only [gE_apply, Matrix.submatrix_apply, id]
theorem col_zero_k (X : Matrix (Fin d.m) (Fin d.n) E) (h : gE d.A.J σ X L.i₀ L.i₀ = 0) (a : Fin d.m) : X a L.i₀ = 0 := by
  have hA : Aniso σ d.A.J := _root_.GlobalTheory.ThK.Dbl.aniso_of_k d.ok.good (d.ok.sign.elim (fun h => Or.inl h.1) fun h => Or.inr h.1) d.ok.aniso
  have key := hA (fun i => X i L.i₀) (by
    rw [← h, gE_apply]
    simp only [form, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    ring)
  exact congrFun key a
theorem extension_by_zero_submatrix (X : Matrix (Fin d.m) (Fin d.n) E) (h : ∀ a, X a L.i₀ = 0) : _root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L (X.submatrix id L.em) = X := by
  ext a k
  rcases _root_.PositivityTheory.SiegelWeilFormula.Afc.cases_idx_k L k with rfl | ⟨j, rfl⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_missing, h]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_embed]; rfl
theorem submatrix_extendZeroColumn (X' : Matrix (Fin d.m) (Fin L.n) E) : (_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X').submatrix id L.em = X' := by
  ext a j
  exact _root_.PositivityTheory.SiegelWeilFormula.Afc.extendZeroColumn_apply_embed L X' a j
def eqv_k (T : nF σ d.Y d.b) (T' : nF σ L.Y L.b) (hs : L.IsSub T T') :
    {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} ≃
      {X : Matrix (Fin L.sd.m) (Fin L.sd.n) E // L.sd.gram (incM F X) (incM F X) = (-2 : ℤ) • T'.1.1} where
  toFun X := ⟨X.1.submatrix id L.em, by
    refine (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k L.sd _ _).2 fun i j => ?_
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).1 X.2 (L.em i) (L.em j)
    show inclR (F := F) (AF F) (gE d.A.J σ (X.1.submatrix id L.em) i j) = _
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.gE_sub_k, h, hs.2]
    rfl⟩
  invFun X' := ⟨_root_.PositivityTheory.SiegelWeilFormula.Afc.extendByZeroColumns L X'.1, by
    refine (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).2 fun k l => ?_
    rcases _root_.PositivityTheory.SiegelWeilFormula.Afc.cases_idx_k L k with rfl | ⟨i, rfl⟩
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.hermForm_extendZeroColumn_left, (hs.1 l).1, map_zero, smul_zero]
    rcases _root_.PositivityTheory.SiegelWeilFormula.Afc.cases_idx_k L l with rfl | ⟨j, rfl⟩
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.hermForm_extendZeroColumn_right, (hs.1 _).2, map_zero, smul_zero]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Afc.hermForm_extendZeroColumn_embed]
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k L.sd _ _).1 X'.2 i j
    refine h.trans ?_
    rw [hs.2]
    rfl⟩
  left_inv X := by
    refine Subtype.ext (_root_.PositivityTheory.SiegelWeilFormula.Afc.extension_by_zero_submatrix L X.1 (_root_.PositivityTheory.SiegelWeilFormula.Afc.col_zero_k L X.1 ?_))
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).1 X.2 L.i₀ L.i₀
    rw [(hs.1 L.i₀).1, smul_zero] at h
    exact kfour.inclR_injective (h.trans (map_zero _).symm)
  right_inv X' := Subtype.ext (_root_.PositivityTheory.SiegelWeilFormula.Afc.submatrix_extendZeroColumn L X'.1)
theorem orb_res_k (T : nF σ d.Y d.b) (T' : nF σ L.Y L.b) (hs : L.IsSub T T') (Φ : d.Fn) (Φ' : L.sd.Fn)
    (hr : L.IsRes Φ Φ') : d.orb T Φ = L.sd.orb T' Φ' := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.orb
  refine congrArg (fun f : UA σ d.A.J → ℂ => ⨍ g in d.D, f g ∂d.μ) (funext fun g => ?_)
  rw [← (_root_.PositivityTheory.SiegelWeilFormula.Afc.eqv_k L T T' hs).tsum_eq]
  refine tsum_congr fun X => ?_
  have hc : ∀ a, X.1 a L.i₀ = 0 := _root_.PositivityTheory.SiegelWeilFormula.Afc.col_zero_k L X.1 (by
    have h := (_root_.PositivityTheory.SiegelWeilFormula.Afc.cond_iff_k d _ _).1 X.2 L.i₀ L.i₀
    rw [(hs.1 L.i₀).1, smul_zero] at h
    exact kfour.inclR_injective (h.trans (map_zero _).symm))
  have hz : ∀ a, (mat g⁻¹ * incM F X.1) a L.i₀ = 0 := fun a => by
    simp [Matrix.mul_apply, incM, hc]
  rw [← hr.2 _ hz]
  congr 1
end Res
theorem orbRes_k : _root_.PositivityTheory.SiegelWeilFormula.OrbRes_k := fun _F _E _ _ _ _ _ _σ d =>
  ⟨fun hmn T hT Φ => _root_.PositivityTheory.SiegelWeilFormula.Afc.orb_zero_k d hmn T hT Φ, fun L T T' hs Φ Φ' hr => _root_.PositivityTheory.SiegelWeilFormula.Afc.orb_res_k L T T' hs Φ Φ' hr⟩
end PositivityTheory.SiegelWeilFormula.Afc
end
end
end

section



section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section Glue
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
def sc_k : (InfinitePlace F → ℂ) → AE F E := (Place.exists_sec d.cm d.B.emb).choose
theorem sc_cont_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d) := (Place.exists_sec d.cm d.B.emb).choose_spec.1
theorem sc_pi_k (x : InfinitePlace F → ℂ) (w : InfinitePlace F) : piInf (d.B.emb w) (_root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d x) = x w :=
  (Place.exists_sec d.cm d.B.emb).choose_spec.2.1 x w
theorem sc_fin_k (x : InfinitePlace F → ℂ) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d x = 0 := (Place.exists_sec d.cm d.B.emb).choose_spec.2.2.1 x
variable {p : Type} [Fintype p] [DecidableEq p]
def atM_k (w : InfinitePlace F) (Z : Matrix p p ℂ) : Matrix p p (AE F E) :=
  Matrix.of fun i j => _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_k d (fun w' => fam w Z w' i j) + finOne F • (1 : Matrix p p (AE F E)) i j
theorem cw_mul_k {q : Type} [Fintype q] (w : InfinitePlace F) (A B : Matrix q q (AE F E)) :
    d.cw w (A * B) = d.cw w A * d.cw w B :=
  Matrix.map_mul (f := piInf (d.B.emb w))
theorem cw_one_k {q : Type} [DecidableEq q] (w : InfinitePlace F) : d.cw w (1 : Matrix q q (AE F E)) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)
theorem cw_atM_k (w w' : InfinitePlace F) (Z : Matrix p p ℂ) : d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z) = fam w Z w' := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k, Matrix.of_apply, map_add (f := _), _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_pi_k, Place.piInf_finOne, add_zero]
theorem fin_atM_k (w : InfinitePlace F) (Z : Matrix p p ℂ) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z = finOne F • (1 : Matrix p p (AE F E)) := by
  ext i j
  simp only [Matrix.smul_apply, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k, Matrix.of_apply, smul_add, _root_.PositivityTheory.SiegelWeilFormula.Krd.sc_fin_k, zero_add, smul_smul, fin_idem]
theorem atM_mul_k (w : InfinitePlace F) (Z Z' : Matrix p p ℂ) : _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (Z * Z') = _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z * _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w Z' := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    unfold fam
    split_ifs <;> simp
  · rw [fin_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, ← fin_mul, Matrix.mul_one]
theorem atM_one_k (w : InfinitePlace F) : _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (1 : Matrix p p ℂ) = 1 := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_one_k]
    unfold fam
    split_ifs <;> rfl
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k]
theorem continuous_atM_k (w : InfinitePlace F) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k (p := p) d w) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine Continuous.add ((_root_.PositivityTheory.SiegelWeilFormula.Krd.sc_cont_k d).comp (continuous_pi fun w' => ?_)) continuous_const
  unfold fam
  split_ifs
  · exact (continuous_apply j).comp ((continuous_apply i).comp continuous_id)
  · exact continuous_const
end Glue
section Iota
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem bb_k : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  rw [← incM_mul, Units.mul_inv, incM_one]
theorem bb'_k : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  rw [← incM_mul, Units.inv_mul, incM_one]
def Zm_k (ζ : ℂ) (y : GR d.n) : M2 d.n := dZ d.n ζ⁻¹ * mR y * dZ d.n ζ
theorem Zm_mul_k {ζ : ℂ} (h : ζ ≠ 0) (y y' : GR d.n) : _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ (y * y') = _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y * _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k]
  rw [show mR (y * y') = mR y * mR y' from rfl]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dZ d.n ζ) (dZ d.n ζ⁻¹), dZ_mul_inv h, Matrix.one_mul]
theorem Zm_one_k {ζ : ℂ} (h : ζ ≠ 0) : _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ 1 = 1 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k]
  rw [show mR (1 : GR d.n) = 1 from rfl, Matrix.mul_one, dZ_inv_mul h]
def MxI_k (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  incM F d.b.1 * _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) * incM F (d.b⁻¹).1
theorem MxI_mul_k {ζ : ℂ} (h : ζ ≠ 0) (w : InfinitePlace F) (y y' : GR d.n) : _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ (y * y') = _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y * _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y' := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_mul_k d h, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_mul_k, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F (d.b⁻¹).1) (incM F d.b.1), _root_.PositivityTheory.SiegelWeilFormula.Krd.bb'_k, Matrix.one_mul]
theorem MxI_one_k {ζ : ℂ} (h : ζ ≠ 0) (w : InfinitePlace F) : _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ 1 = 1 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_one_k d h, _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_one_k, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k]
theorem inFrame_MxI_k (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) :
    incM F (d.b⁻¹).1 * _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y * incM F d.b.1 = _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, Matrix.mul_assoc]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.bb'_k, Matrix.mul_one, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb'_k, Matrix.one_mul]
theorem dbl_incM_k : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
  simp only [dbl, incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _)]
  congr 1
  ext i j
  simp
theorem cw_transpose_k {p q : Type} (w : InfinitePlace F) (A : Matrix p q (AE F E)) : d.cw w Aᵀ = (d.cw w A)ᵀ :=
  Matrix.transpose_map
theorem cw_incM_k {p q : Type} (w : InfinitePlace F) (M : Matrix p q E) : d.cw w (incM F M) = M.map (d.B.emb w).1 :=
  Matrix.ext fun i j => PositivityTheory.ThKG.Tow.Levi.piInf_incl (d.B.emb w) (M i j)
theorem map_sig_emb_k {p q : Type} (w : InfinitePlace F) (M : Matrix p q E) :
    (M.map σ).map (d.B.emb w).1 = (M.map (d.B.emb w).1).map star := by
  ext i j
  exact d.cm.2.2.2 _ _
theorem hQ_w_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (w : InfinitePlace F) :
    (d.b.1.map (d.B.emb w).1)ᵀ * (dbl d.Y.J).map (d.B.emb w).1 * (d.b.1.map (d.B.emb w).1).map star = Qc d.n ε := by
  have h := congrArg (fun M => M.map (d.B.emb w).1) hε
  simp only [Matrix.map_mul (f := (d.B.emb w).1), _root_.PositivityTheory.SiegelWeilFormula.Krd.map_sig_emb_k] at h
  rw [Matrix.transpose_map] at h
  rw [h]
  simp only [Qc, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
theorem fin_MxI_k (w : InfinitePlace F) (ζ : ℂ) (y : GR d.n) : finOne F • _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y = finOne F • 1 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, fin_mul, fin_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k, ← fin_mul, ← fin_mul, Matrix.mul_one, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k]
theorem MxI_unitary_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) :
    (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y)ᵀ * dbl (incM F d.Y.J) * (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y).map (cA σ) = dbl (incM F d.Y.J) := by
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k]
    have hM : d.cw w' (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y) = d.b.1.map (d.B.emb w').1 * fam w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) w' * (d.b⁻¹).1.map (d.B.emb w').1 := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    rw [hM]
    refine conj_unit _ _ _ _ _ ?_ (_root_.PositivityTheory.SiegelWeilFormula.Krd.hQ_w_k d hε w') ?_
    · rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · unfold fam
      split_ifs
      · exact (unitary_iff hζ (mR y)).2 y.2
      · rw [Matrix.transpose_one, mapStar_one, Matrix.one_mul, Matrix.mul_one]
  · have e1 : (finOne F • (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))).map (cA σ) = finOne F • 1 := by
      rw [map_cA_smul, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [fin_mul, fin_mul, ← Matrix.transpose_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_MxI_k, ← map_cA_smul, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_MxI_k, e1, Matrix.transpose_smul,
      Matrix.transpose_one, ← fin_mul, ← fin_mul, Matrix.mul_one, Matrix.one_mul]
def iotaF_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) : d.G :=
  ⟨⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y⁻¹, by rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_mul_k d (zeta_ne hζ), mul_inv_cancel, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_one_k d (zeta_ne hζ)],
    by rw [← _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_mul_k d (zeta_ne hζ), inv_mul_cancel, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_one_k d (zeta_ne hζ)]⟩, _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_unitary_k d hε hζ w y⟩
def iota_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) : GR d.n →* d.G where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.Krd.iotaF_k d hε hζ w
  map_one' := Subtype.ext (Units.ext (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_one_k d (zeta_ne hζ) w))
  map_mul' a b := Subtype.ext (Units.ext (_root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_mul_k d (zeta_ne hζ) w a b))
theorem inFrame_iota_k {ε : ℤˣ} {ζ : ℂ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) (y : GR d.n) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Krd.iota_k d hε hζ w y) = _root_.PositivityTheory.SiegelWeilFormula.Krd.atM_k d w (_root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y) :=
  _root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_MxI_k d w ζ y
theorem continuous_iota_k {ε : ℤˣ} {ζ : ℂ}
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0)
    (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (w : InfinitePlace F) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Krd.iota_k d hε hζ w) := by
  have hm : Continuous fun y : GR d.n => mR y := Units.continuous_val.comp continuous_subtype_val
  have hz : Continuous fun y : GR d.n => _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k d ζ y := (continuous_const.matrix_mul hm).matrix_mul continuous_const
  have hM : Continuous fun y : GR d.n => _root_.PositivityTheory.SiegelWeilFormula.Krd.MxI_k d w ζ y :=
    (continuous_const.matrix_mul ((_root_.PositivityTheory.SiegelWeilFormula.Krd.continuous_atM_k d w).comp hz)).matrix_mul continuous_const
  refine continuous_induced_rng.2 ?_
  refine Units.continuous_iff.2 ⟨hM, ?_⟩
  exact hM.comp continuous_inv
theorem iotaEx_k : _root_.PositivityTheory.SiegelWeilFormula.Krd.IotaEx_k := by
  intro F E _ _ _ _ _ σ d ε ζ hε hζ
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.iota_k d hε hζ, _root_.PositivityTheory.SiegelWeilFormula.Krd.continuous_iota_k d hε hζ, fun w y => ?_, fun w w' y hw => ?_, fun w y => ?_⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_iota_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    simp only [fam, if_true, _root_.PositivityTheory.SiegelWeilFormula.Krd.Zm_k]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, dZ_mul_inv (zeta_ne hζ), Matrix.one_mul]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_iota_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_atM_k]
    simp only [fam, if_neg hw]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.inFrame_iota_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.fin_atM_k]
end Iota
end PositivityTheory.SiegelWeilFormula.Krd
end
end
end

section



section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem T_eq_lin_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) (X : Mx F E d.m d.n) :
    d.T Φ X = (d.l ∘ₗ schrL d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ))) Φ := rfl
theorem T_sum_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {k : ℕ} (c : Fin k → ℂ) (Φs : Fin k → d.Fn) :
    d.T (∑ i, c i • Φs i) = ∑ i, c i • d.T (Φs i) := by
  funext X

  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.T_eq_lin_k, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_eq_lin_k]
theorem T_sub_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Ψ : d.Fn) : d.T (Φ - Ψ) = d.T Φ - d.T Ψ := by
  funext X
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.T_eq_lin_k, map_sub, Pi.sub_apply, _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_eq_lin_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_eq_lin_k]
def genF_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (P : InfinitePlace F → PX d.m d.n) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ)
    (X : Mx F E d.m d.n) : ℂ :=
  (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2
def genL_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (P : InfinitePlace F → PX d.m d.n) :
    ((Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k R P
  map_add' f g := by funext X; simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k, Pi.add_apply]; ring
  map_smul' c f := by funext X; simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
def pureGen_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : Set (Mx F E d.m d.n → ℂ) :=
  {f | ∃ P φ, Dense.Good φ ∧ f = _root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k R P (Dense.pf φ)}
theorem pureGen_sub_fock_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : _root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_k R ⊆ R.fock := by
  rintro _ ⟨P, φ, hφ, rfl⟩
  exact Submodule.subset_span ⟨P, Dense.pf φ, Dense.pf_mem hφ, rfl⟩
theorem fock_le_span_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_k R) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨P, g, hg, rfl⟩
  have := Dense.mem_span_pf hg
  clear hg
  have key : _root_.PositivityTheory.SiegelWeilFormula.KWhit.genL_k R P g ∈ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_k R) := by
    induction this using Submodule.span_induction with
    | mem x hx => obtain ⟨φ, hφ, rfl⟩ := hx; exact Submodule.subset_span ⟨P, φ, hφ, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  exact key
theorem isPureT_of_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (P : InfinitePlace F → PX d.m d.n)
    (φ : ∀ u : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → Fv F u) → ℂ) (hφ : Dense.Good φ) (Φ : d.Fn)
    (h : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k R P (Dense.pf φ)) : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureT_k R Φ := by
  refine ⟨P, φ, fun v => hφ.1 v, hφ.2.mono fun v hv => hv, ?_⟩
  rw [h]
  rfl
theorem pureSpan_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.PureSpan_k := by
  intro hT hF hPK F E _ _ _ _ _ σ d R Φ hΦ hTΦ
  have hB := hT.1 F E σ d
  have h1 : d.T Φ ∈ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_k R) := _root_.PositivityTheory.SiegelWeilFormula.KWhit.fock_le_span_k R hTΦ
  obtain ⟨k, c, gs, hsum⟩ := Submodule.mem_span_set'.1 h1
  have hpre : ∀ i : Fin k, ∃ Ψ ∈ d.sch, d.T Ψ = (gs i : Mx F E d.m d.n → ℂ) := fun i =>
    hB.2.1 _ ((hF F E σ d R).1 (_root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_sub_fock_k R (gs i).2))
  choose Φs hΦs hTs using hpre
  refine ⟨k, c, Φs, fun i => ⟨hPK F E σ d R (Φs i) (hΦs i) (hTs i ▸ _root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_sub_fock_k R (gs i).2), ?_⟩, ?_⟩
  · obtain ⟨P, φ, hφ, e⟩ := (gs i).2
    exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.isPureT_of_k R P φ hφ (Φs i) ((hTs i).trans e)
  · have hmem : Φ - ∑ i, c i • Φs i ∈ d.sch :=
      sub_mem hΦ.1 (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΦs i))
    have h0 : d.T (Φ - ∑ i, c i • Φs i) = 0 := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.T_sub_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_sum_k, ← hsum]
      simp only [hTs, sub_self]
    exact (sub_eq_zero.1 (hB.2.2 _ hmem h0))
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end
