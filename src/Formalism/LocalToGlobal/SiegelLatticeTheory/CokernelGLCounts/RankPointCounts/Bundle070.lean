module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle059
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle099
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle067
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle060
public import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle048
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle058
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle063
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle027
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle052
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfQ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationChange.CoefXOfMemXS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle062
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle066
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle037
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

namespace Formalism.L2.SG.Pf.ZsVolGrp

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ZsVolCut Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isLoUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsLoUni l) (h' : IsLoUni l') : IsLoUni (l * l') := by
  intro a b
  refine ⟨fun hab => ?_, fun hab => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge a c with hc | hc
    · rw [(h a c).1 hc, zero_mul]
    · rw [(h' c b).1 (lt_of_le_of_lt hc hab), mul_zero]
  · subst hab
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(h a a).2 rfl, (h' a a).2 rfl, mul_one]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hc' | hc'
      · rw [(h' c a).1 hc', mul_zero]
      · rw [(h a c).1 hc', zero_mul]
    · simp

theorem isUpUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsUpUni l) (h' : IsUpUni l') : IsUpUni (l * l') := by
  first | exact GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul .. | (apply GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (intros; apply GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (intros; apply @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption) | (apply @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> first | assumption | infer_instance) | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l l' h h' | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l l' h | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l l' | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n l | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› n | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R ‹_› | exact @GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul R

theorem isLoUni_one : IsLoUni (1 : Matrix (Fin n) (Fin n) R) := fun a b =>
  ⟨fun h => Matrix.one_apply_ne h.ne, fun h => by subst h; exact Matrix.one_apply_eq a⟩

theorem isUpUni_one : IsUpUni (1 : Matrix (Fin n) (Fin n) R) := fun a b =>
  ⟨fun h => Matrix.one_apply_ne h.ne', fun h => by subst h; exact Matrix.one_apply_eq a⟩

theorem isLoUni_inv {l : Matrix (Fin n) (Fin n) R} (h : IsLoUni l) : IsLoUni l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  have hd : l.det = 1 := det_lo (fun a => (h a a).2 rfl) (fun a b hab => (h a b).1 hab)
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => (h i j).1 hij)
  refine ⟨fun a b => ⟨fun hab => hb hab, fun hab => ?_⟩, hli, hil⟩
  subst hab
  have e := congrFun (congrFun hil a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, (h a a).2 rfl, one_mul] at e
  · simpa using e
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with hc' | hc'
    · rw [hb hc', mul_zero]
    · rw [(h a c).1 hc', zero_mul]
  · simp

theorem isUpUni_inv {l : Matrix (Fin n) (Fin n) R} (h : IsUpUni l) : IsUpUni l⁻¹ ∧ l⁻¹ * l = 1 ∧ l * l⁻¹ = 1 := by
  have hd : l.det = 1 := det_up (fun a => (h a a).2 rfl) (fun a b hab => (h a b).1 hab)
  have hu : IsUnit l.det := by rw [hd]; exact isUnit_one
  have hli : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l hu
  have hil : l * l⁻¹ = 1 := Matrix.mul_nonsing_inv l hu
  have := Matrix.invertibleOfIsUnitDet l hu
  have hb : l⁻¹.BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular (fun i j hij => (h i j).1 hij)
  refine ⟨fun a b => ⟨fun hab => hb hab, fun hab => ?_⟩, hli, hil⟩
  subst hab
  have e := congrFun (congrFun hil a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, (h a a).2 rfl, one_mul] at e
  · simpa using e
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with hc' | hc'
    · rw [(h a c).1 hc', zero_mul]
    · rw [hb hc', mul_zero]
  · simp

end Uni

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)

def stZ (Z L : Formalism.L2.SG.PairVal.MatR D) (hL : IsUnit L.det) : Subgroup (Formalism.L2.SG.PairVal.GLR D) where
  carrier := stZSet M δ u u' Z L
  one_mem' := by
    refine ⟨1, ?_, isLoUni_one, 1, isUpUni_one, by simp, fun p => ⟨1, 1, intLow_one _, intUp_one _, fun Z' => ?_⟩⟩
    · simp [Matrix.nonsing_inv_mul L hL]
    · simp [zhatOM_zhatOM]
  mul_mem' := by
    rintro x y ⟨x', hx, hxl, bx, hbx, hxZ, hxp⟩ ⟨y', hy, hyl, by', hby, hyZ, hyp⟩
    refine ⟨x' * y', ?_, ?_, by' * bx, isUpUni_mul hby hbx, ?_, fun p => ?_⟩
    · rw [Units.val_mul, hx, hy, Units.val_mul]
      calc L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * L * (L⁻¹ * (y' : Formalism.L2.SG.PairVal.MatR D) * L) =
          L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * (L * L⁻¹) * (y' : Formalism.L2.SG.PairVal.MatR D) * L := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv L hL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    · rw [Units.val_mul]
      exact isLoUni_mul hxl hyl
    · rw [Units.val_mul]
      calc (x' : Formalism.L2.SG.PairVal.MatR D) * (y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * (by' * bx) =
          (x' : Formalism.L2.SG.PairVal.MatR D) * ((y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * by') * bx := by
            simp only [Matrix.mul_assoc]
        _ = ZhatOM Z := by rw [hyZ, hxZ]
    · obtain ⟨l1, ρ1, hl1, hρ1, h1⟩ := hxp p
      obtain ⟨l2, ρ2, hl2, hρ2, h2⟩ := hyp p
      refine ⟨l1 * l2, ρ2 * ρ1, intLow_mul _ hl1 hl2, intUp_mul _ hρ2 hρ1, fun Z' => ?_⟩
      have e : ((x' * y' : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * (by' * bx) =
          (x' : Formalism.L2.SG.PairVal.MatR D) *
            ZhatOM (ZhatOM ((y' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * by')) * bx := by
        rw [zhatOM_zhatOM, Units.val_mul]
        simp only [Matrix.mul_assoc]
      rw [e, h1, h2]
      simp only [Matrix.mul_assoc]
  inv_mem' := by
    rintro x ⟨x', hx, hxl, bx, hbx, hxZ, hxp⟩
    obtain ⟨hxi, hxi1, hxi2⟩ := isLoUni_inv hxl
    obtain ⟨hbi, hbi1, hbi2⟩ := isUpUni_inv hbx
    have hZ : ((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * bx⁻¹ = ZhatOM Z := by
      rw [Matrix.coe_units_inv]
      calc (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * ZhatOM Z * bx⁻¹ =
          (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * ((x' : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z * bx) * bx⁻¹ := by rw [hxZ]
        _ = ZhatOM Z := by
          simp only [← Matrix.mul_assoc]
          rw [hxi1, Matrix.one_mul, Matrix.mul_assoc, hbi2, Matrix.mul_one]
    refine ⟨x'⁻¹, ?_, by rw [Matrix.coe_units_inv]; exact hxi, bx⁻¹, hbi, hZ, fun p => ?_⟩
    · rw [Matrix.coe_units_inv, Matrix.coe_units_inv, hx]
      have hLi := Matrix.nonsing_inv_mul L hL
      have hiL := Matrix.mul_nonsing_inv L hL
      refine Matrix.inv_eq_left_inv ?_
      calc L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * L * (L⁻¹ * (x' : Formalism.L2.SG.PairVal.MatR D) * L) =
          L⁻¹ * ((x' : Formalism.L2.SG.PairVal.MatR D)⁻¹ * (L * L⁻¹) * (x' : Formalism.L2.SG.PairVal.MatR D)) * L := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hiL, Matrix.mul_one, hxi1, Matrix.mul_one, hLi]
    · obtain ⟨l, ρ, hl, hρ, h⟩ := hxp p
      obtain ⟨hli, hli1, hli2⟩ := intLow_inv _ hl
      obtain ⟨hρi, hρi1, hρi2⟩ := intUp_inv _ hρ
      refine ⟨l⁻¹, ρ⁻¹, hli, hρi, fun Z' => ?_⟩
      have h2 := h (ZhatOM (((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * bx⁻¹))
      have e : (x' : Formalism.L2.SG.PairVal.MatR D) *
          ZhatOM (ZhatOM (((x'⁻¹ : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) * ZhatOM Z' * bx⁻¹)) * bx =
          ZhatOM Z' := by
        rw [zhatOM_zhatOM, Matrix.coe_units_inv]
        simp only [← Matrix.mul_assoc]
        rw [hxi2, Matrix.one_mul, Matrix.mul_assoc, hbi1, Matrix.mul_one]
      rw [e, zhatOM_zhatOM] at h2
      rw [h2]
      simp only [← Matrix.mul_assoc]
      rw [hli1, Matrix.one_mul]
      simp only [Matrix.mul_assoc, hρi2, Matrix.mul_one]

theorem mem_CZ (Z L : Formalism.L2.SG.PairVal.MatR D) (hL : IsUnit L.det) (a : Formalism.L2.SG.PairVal.GLR D) :
    a ∈ CZ M δ u u' Z L ↔ a ∈ stZSet M δ u u' Z L := by
  have e : CZ M δ u u' Z L = stZ M δ u u' Z L hL := by
    unfold CZ
    exact Subgroup.closure_eq (stZ M δ u u' Z L hL)
  rw [e]
  rfl

end Formalism.L2.SG.Pf.ZsVolGrp

end
end

section

noncomputable section

open scoped Classical Matrix
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_ddS_pow (t : 𝓞 D.host.F) (ht : t ∈ differentIdeal ℤ (𝓞 D.host.F)) (k : ℕ) :
    (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t) ^ k : 𝓞 D.host.E) : D.host.E) ∈ ddS D ^ k := by
  have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈
      Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) :=
    Ideal.mem_map_of_mem _ ht
  have h2 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) ∈ ddS D :=
    FractionalIdeal.mem_coeIdeal_of_mem _ h1
  have h3 := Submodule.pow_mem_pow (ddS D : Submodule (𝓞 D.host.E) D.host.E) h2 k
  rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_pow]
  push_cast
  exact h3

theorem dict_holds (Zd : LocDat D) : Formalism.L2.SG.Pf.TupGlob.Dict Zd := by
  intro A B hA hB hloc
  have hAu : IsLoUni A := fun i j => ⟨hA.2 i j, fun h => h ▸ hA.1 i⟩
  have hBu : IsUpUni B := Formalism.L2.SG.Pf.TupGlob.isUpUni_of hB
  have hsh : ∀ p, Formalism.L2.SG.Pf.StabIntSh.LocEntryShape D p A B := fun p =>
    (Formalism.L2.SG.Pf.StabIntSh.loc_iff Formalism.L2.SG.Pf.StabIntSh.locShapeL Formalism.L2.SG.Pf.StabIntSh.locShapeG (p := p)
      Zd.agree hAu hBu).1
      ⟨by rw [lOf_eq]; exact (hloc p).1, by rw [ρOf_eq]; exact Formalism.L2.SG.Pf.FibQ.sgn_conj_intUp Zd p (hloc p).2⟩
  have hES := (Formalism.L2.SG.Pf.StabIntSh.glob_iff Formalism.L2.SG.Pf.StabIntSh.locGlob Formalism.L2.SG.Pf.StabIntSh.shapeNZ A B).1 hsh
  refine ⟨fun c b hcb x hx => ?_, fun c b hcb x hx => ?_, fun P hP c b => ?_⟩
  · rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF]
    exact mem_aaF hcb hx (ddPow_conj Zd (by have := b.isLt; omega) (hES b c hcb).1)
  · rw [sg_entry]
    exact mem_aaF hcb hx (hES b c hcb).2.1
  · rcases lt_trichotomy c b with h | h | h
    · have hq := (hES b c h).2.2
      unfold Formalism.L2.SG.Pf.StabIntSh.qdPow Formalism.L2.SG.Pf.StabIntSh.qq at hq
      rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.mem_singleton_mul] at hq
      obtain ⟨z, hz, hzy⟩ := hq
      obtain ⟨t, ht, htP⟩ := diff_avoid P hP
      have hk : b.val - c.val ≤ D.R.rS := by have := b.isLt; omega
      have hz' := ddPow_conj Zd hk hz
      have hprod := FractionalIdeal.mul_mem_mul (mem_ddS_pow t ht (b.val - c.val)) hz'
      unfold Formalism.L2.SG.Pf.StabIntSh.ddPow at hprod
      rw [← zpow_natCast, ← zpow_add₀ (PI.NRCW.ddS_ne_zero D), add_neg_cancel, zpow_zero] at hprod
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 hprod
      refine ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t) ^ (b.val - c.val), fun hs => htP (P.isPrime.mem_of_pow_mem _ hs),
        o, ?_⟩
      rw [Matrix.conjTranspose_apply, PI.UnitaryGroupMassFormula.CntFormula.star_eq_conjF, sg_entry]
      have e1 : D.conjF (A b c) - Formalism.L2.SG.Pf.StabIntSh.bt D B c b =
          D.conjF (algebraMap (𝓞 D.host.E) D.host.E ((gS D : ℕ) : 𝓞 D.host.E) * z) := by
        have := congrArg D.conjF hzy
        simpa only [map_sub, Formalism.L2.SG.Pf.LocalDenominators.conjF_invol] using this
      rw [e1, map_mul, map_natCast, map_natCast, mul_left_comm, ← ho]
    · subst h
      refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.1 c, hB.1 c, ← pow_add, ← two_mul, pow_mul]
    · refine ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), 0, ?_⟩
      rw [Matrix.conjTranspose_apply, sg_entry]
      simp [Formalism.L2.SG.Pf.StabIntSh.bt, hA.2 b c h, hB.2 b c h]

end Formalism.L2.SG.Pf.FibD
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SRat {D : D7} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V) :=
  {s | s ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ (∀ j, ∀ x ∈ Xflag F (j + 1), s x - x ∈ Xflag F j) ∧ s F.fl.z - F.fl.z ∈ Xsp F}

def NmlPtDC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t1 t2 : TauC Y u u', Gt t1 ≠ 0 → Gt t2 ≠ 0 → ptPN t1 = γ → ptPN t2 = γ →
          (Y.tO u u').rowOf t1 = (Y.tO u u').rowOf t2 →
          ∃ σ ∈ SRat (lf D (X.Fu u)), ∃ s' ∈ SRat (lf D (X.Fu u')), t2.lin = σ * t1.lin * s'

def UnitaryNormalVectorCount : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
        ∀ t0 t1 t2 : TauC Y u u', Gt t0 ≠ 0 → Gt t1 ≠ 0 → Gt t2 ≠ 0 →
          RelC Y u u' t0 t1 → RelC Y u u' t0 t2 → t1.G = t0.G → t2.G = t0.G →
          (∃ σ ∈ SRat (lf D (X.Fu u)), ∃ s' ∈ SRat (lf D (X.Fu u')), t2.lin = σ * t1.lin * s') →
          coefA Y u u' t0 t1 = coefA Y u u' t0 t2 → coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2 →
          nmlOf Y u u' t1 = nmlOf Y u u' t2

theorem nmlSep_of (hP : NmlPtDC) (hG : UnitaryNormalVectorCount) : NmlSep := by
  intro Cg cb Cw cT CT C0
  obtain ⟨A1, B1, h1⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨A2, B2, h2⟩ := hG Cg cb Cw cT CT C0
  refine ⟨max A1 A2, max B1 B2, fun C' Cl hC hl D large₂ X Y u u' hctx γ hγ t0 t1 t2 g0 g1 g2 p0 p1 p2 r1 r2 ca ca' => ?_⟩
  have hdc := h1 C' Cl (le_of_max_le_left hC) (le_of_max_le_left hl) D large₂ X Y u u' hctx γ hγ t1 t2 g1 g2 p1 p2
    (r1.1.trans r2.1.symm)
  have e0 := gval_occ (t := t0) (hG := p0 ▸ hγ)
  have e1 := gval_occ (t := t1) (hG := p1 ▸ hγ)
  have e2 := gval_occ (t := t2) (hG := p2 ▸ hγ)
  have hG1 : t1.G = t0.G := by
    rw [Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t1), Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t0)]
    rw [e1, e0, p1, p0]
  have hG2 : t2.G = t0.G := by
    rw [Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t2), Formalism.L2.SG.Pf.SatGram.gterm_G (Y := Y) (t := t0)]
    rw [e2, e0, p2, p0]
  exact h2 C' Cl (le_of_max_le_right hC) (le_of_max_le_right hl) D large₂ X Y u u' hctx t0 t1 t2 g0 g1 g2 r1 r2
    hG1 hG2 hdc ca ca'

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

section

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

def hgt (q : FreeE w) : ℕ := q.1.2.val - q.1.1.val

theorem qbar_prop (q : FreeE w) :
    pinv w q.1.2 < pinv w q.1.1 ∧ blkOf w.1 (pinv w q.1.2).val = blkOf w.1 (pinv w q.1.1).val :=
  ⟨(pinv_lt_iff w q.1.1 q.1.2 q.2.2).1 q.2.1, by rw [blkOf_pinv, blkOf_pinv]; exact q.2.2.symm⟩

def qbar (q : FreeE w) : FreeE w := ⟨(pinv w q.1.2, pinv w q.1.1), qbar_prop w q⟩

def selfP (q : FreeE w) : Prop := qbar w q = q

def upperM (q : FreeE w) : Prop := (qbar w q).1.1 < q.1.1

def hpr (q : FreeE w) : ℕ := 2 * hgt w q + if upperM w q then 1 else 0

def sgq (q : FreeE w) : D.host.E := (-1) ^ (D.R.rS - q.1.1.val) * (-1) ^ (D.R.rS - q.1.2.val)

def Xmat (y : FreeE w → D.host.E) : MatR D := fun a c =>
  if a = c then 1 else if h : a < c ∧ blkOf w.1 a.val = blkOf w.1 c.val then y ⟨(a, c), h⟩ else 0

def trunc (y : FreeE w → D.host.E) (n : ℕ) : FreeE w → D.host.E := fun q => if hgt w q < n then y q else 0

def cf (y : FreeE w → D.host.E) (q : FreeE w) : D.host.E := ((Xmat w (trunc w y (hgt w q)))⁻¹) q.1.1 q.1.2


variable (D) in
def mOdd : ℕ := (gS D + 1) / 2

def τA (q : FreeE w) (y : FreeE w → D.host.E) : D.host.E :=
  if selfP w q then (mOdd D : D.host.E) * cf w y q
  else if upperM w q then sgq w (qbar w q) * D.conjF (-(y (qbar w q)) + cf w y (qbar w q))
  else 0


variable (D) in
def sLat (h : ℕ) (s : D.host.E) (_hs : D.conjF s = s) : AddSubgroup D.host.E where
  carrier := {z | z ∈ ddPow D h ∧ z + s * D.conjF z ∈ qdPow D h}
  zero_mem' := by
    refine ⟨FractionalIdeal.zero_mem _, ?_⟩
    simp only [map_zero, mul_zero, add_zero]; exact FractionalIdeal.zero_mem _
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨(ddPow D h : Submodule (𝓞 D.host.E) D.host.E).add_mem ha1 hb1, ?_⟩
    rw [map_add (f := _), show a + b + s * (D.conjF a + D.conjF b) = (a + s * D.conjF a) + (b + s * D.conjF b) by ring]
    exact (qdPow D h : Submodule (𝓞 D.host.E) D.host.E).add_mem ha2 hb2
  neg_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨(ddPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem ha1, ?_⟩
    rw [map_neg, show -a + s * -D.conjF a = -(a + s * D.conjF a) by ring]
    exact (qdPow D h : Submodule (𝓞 D.host.E) D.host.E).neg_mem ha2

theorem sgq_conj (q : FreeE w) : D.conjF (sgq w q) = sgq w q := by
  simp [sgq, map_pow, map_neg, map_one]

def Iq (q : FreeE w) : FI D := if selfP w q ∨ ¬ upperM w q then ddPow D (hgt w q) else qdPow D (hgt w q)

def Λq (q : FreeE w) : AddSubgroup D.host.E :=
  if selfP w q then sLat D (hgt w q) (sgq w q) (sgq_conj w q)
  else ((Iq w q : FI D) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup


variable (D) in
def TwistC : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → Odd (gS D) → ∀ (w : Point D.host.E (D.R.rS + 1)) (y : FreeE w → D.host.E),
      CondX w (Xmat w y) ↔ ∀ q, y q - τA w q y ∈ Λq w q



end Formalism.L2.SG.Pf.StabIntLat
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def BwdTerm' : Prop :=
  CtxP u u' F0 what₂ →
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
      (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
      (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
      StarHyp Zd γ Z F'₂ φ φ' →
      ∀ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ',
        (∃ n ∈ unipotentFrameFixers F0, (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)) →
        IsTerm Λ₂ (gS D) (lf D F0) (liftF F'₂) ∧ AdmWit Λ₂ (gS D) (lf D F0) (liftF F'₂) 1 ∧
          IsGeneric Λ₂ (gS D) (lf D F0) (liftF F'₂) ∧ FrameOK D Λ₂ (liftF F'₂)

variable {u u' F0 what₂}

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
