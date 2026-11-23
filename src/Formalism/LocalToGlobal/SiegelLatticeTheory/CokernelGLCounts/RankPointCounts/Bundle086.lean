module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle082
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxAt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabMul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle011
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle070
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle010
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle035

@[expose] public section

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdE
  Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.ProdEP2Cut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) {p : PlF D}

theorem loUni_of_int {l : MP p} (h : Formalism.MainNotions.S.TieN.IntLow (M p) l) : IsLoUni l :=
  fun i j => ⟨h.2.1 i j, fun e => e ▸ h.1 i⟩

theorem upUni_of_int {l : MP p} (h : Formalism.MainNotions.S.TieN.IntUp (M p) l) : IsUpUni l :=
  fun i j => ⟨h.2.1 i j, fun e => e ▸ h.1 i⟩

section
variable (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)

theorem conj_first_factor (x : GG p) :
    (((g0 M δ hA L U hL hU * x * (g0 M δ hA L U hL hU)⁻¹).1 : GLp p) : MP p) =
      lOf δ M p L U * ((x.1 : GLp p) : MP p) * lOf δ M p L⁻¹ U⁻¹ := by
  simp only [g0, Prod.fst_mul, Prod.fst_inv, Units.val_mul, Units.inv_mk]

theorem conj_second_factor (x : GG p) :
    ((((g0 M δ hA L U hL hU * x * (g0 M δ hA L U hL hU)⁻¹).2).unop : GLp p) : MP p) =
      ρOf δ M p L⁻¹ U⁻¹ * ((x.2.unop : GLp p) : MP p) * ρOf δ M p L U := by
  simp only [g0, Prod.snd_mul, Prod.snd_inv, MulOpposite.unop_mul, MulOpposite.unop_inv, MulOpposite.unop_op,
    Units.val_mul, Units.inv_mk]
  rw [Matrix.mul_assoc]

theorem cShape (w : Point D.host.E (D.R.rS + 1)) : CShapeAt M δ u u' w hA L U hL hU := by
  have hLL : lOf δ M p L⁻¹ U⁻¹ * lOf δ M p L U = 1 := lp_inv M δ hA L U hL hU
  have hLL' : lOf δ M p L U * lOf δ M p L⁻¹ U⁻¹ = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hLL
  have hUU : ρOf δ M p L U * ρOf δ M p L⁻¹ U⁻¹ = 1 := up_inv M δ hA L U hL hU
  have hUU' : ρOf δ M p L⁻¹ U⁻¹ * ρOf δ M p L U = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).mp hUU
  set Lp := lOf δ M p L U
  set Lpi := lOf δ M p L⁻¹ U⁻¹
  set Up := ρOf δ M p L U
  set Upi := ρOf δ M p L⁻¹ U⁻¹
  set Y := Y0 M δ u u' w p
  have key : ∀ a b : MP p, (Lp * a * Lpi) * (Lp * Y * Up) * (Upi * b * Up) = Lp * (a * Y * b) * Up := by
    intro a b
    calc (Lp * a * Lpi) * (Lp * Y * Up) * (Upi * b * Up) = Lp * a * (Lpi * Lp) * Y * (Up * Upi) * b * Up := by
          simp only [Matrix.mul_assoc]
      _ = Lp * (a * Y * b) * Up := by rw [hLL, hUU]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  ext x
  rw [mem_cj]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨_, _, hy3⟩ := y.2
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show Formalism.MainNotions.S.TieN.IntLow (M p) _
      rw [conj_first_factor]; exact hy1
    · show Formalism.MainNotions.S.TieN.IntUp (M p) _
      rw [conj_second_factor]; exact hy2
    · show _ * XP M δ u u' w L U * _ = XP M δ u u' w L U
      rw [conj_first_factor, conj_second_factor]
      show (Lp * _ * Lpi) * (Lp * Y * Up) * (Upi * _ * Up) = Lp * Y * Up
      rw [key]
      exact congrArg (fun z => Lp * z * Up) hy3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h1' : Formalism.MainNotions.S.TieN.IntLow (M p) (Lp * ((x.1 : GLp p) : MP p) * Lpi) := by
      have := h1; rw [show Formalism.MainNotions.S.TieN.IntLow (M p) _ = _ from rfl, conj_first_factor] at this; exact this
    have h2' : Formalism.MainNotions.S.TieN.IntUp (M p) (Upi * ((x.2.unop : GLp p) : MP p) * Up) := by
      have := h2; rw [show Formalism.MainNotions.S.TieN.IntUp (M p) _ = _ from rfl, conj_second_factor] at this; exact this
    have h3' : (Lp * ((x.1 : GLp p) : MP p) * Lpi) * (Lp * Y * Up) * (Upi * ((x.2.unop : GLp p) : MP p) * Up) =
        Lp * Y * Up := by
      have := h3
      change _ * XP M δ u u' w L U * _ = XP M δ u u' w L U at this
      rw [conj_first_factor, conj_second_factor] at this
      exact this
    rw [key] at h3'
    have hst : ((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p) = Y := by
      have := congrArg (fun z => Lpi * z * Upi) h3'
      calc ((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p)
          = (Lpi * Lp) * (((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p)) * (Up * Upi) := by
            rw [hLL, hUU, Matrix.one_mul, Matrix.mul_one]
        _ = Lpi * (Lp * (((x.1 : GLp p) : MP p) * Y * ((x.2.unop : GLp p) : MP p)) * Up) * Upi := by
            simp only [Matrix.mul_assoc]
        _ = Lpi * (Lp * Y * Up) * Upi := this
        _ = Y := by
            calc Lpi * (Lp * Y * Up) * Upi = (Lpi * Lp) * Y * (Up * Upi) := by simp only [Matrix.mul_assoc]
              _ = Y := by rw [hLL, hUU, Matrix.one_mul, Matrix.mul_one]
    have hlo : IsLoUni ((x.1 : GLp p) : MP p) := by
      have e : ((x.1 : GLp p) : MP p) = Lpi * (Lp * ((x.1 : GLp p) : MP p) * Lpi) * Lp := by
        calc ((x.1 : GLp p) : MP p) = (Lpi * Lp) * ((x.1 : GLp p) : MP p) * (Lpi * Lp) := by
              rw [hLL, Matrix.one_mul, Matrix.mul_one]
          _ = Lpi * (Lp * ((x.1 : GLp p) : MP p) * Lpi) * Lp := by simp only [Matrix.mul_assoc]
      rw [e]
      exact ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul
        (lOf_loUni M δ hA _ _ (ZsVolGrp.isLoUni_inv hL).1 (ZsVolGrp.isUpUni_inv hU).1) (loUni_of_int M h1'))
        (lOf_loUni M δ hA _ _ hL hU)
    have hup : IsUpUni ((x.2.unop : GLp p) : MP p) := by
      have e : ((x.2.unop : GLp p) : MP p) = Up * (Upi * ((x.2.unop : GLp p) : MP p) * Up) * Upi := by
        calc ((x.2.unop : GLp p) : MP p) = (Up * Upi) * ((x.2.unop : GLp p) : MP p) * (Up * Upi) := by
              rw [hUU, Matrix.one_mul, Matrix.mul_one]
          _ = Up * (Upi * ((x.2.unop : GLp p) : MP p) * Up) * Upi := by simp only [Matrix.mul_assoc]
      rw [e]
      exact ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul (ρOf_upUni M δ hA _ _ hL hU) (upUni_of_int M h2'))
        (ρOf_upUni M δ hA _ _ (ZsVolGrp.isLoUni_inv hL).1 (ZsVolGrp.isUpUni_inv hU).1)
    exact ⟨⟨x, hlo, hup, hst⟩, ⟨h1', h2'⟩, rfl⟩

end

end Formalism.L2.SG.Pf.ProdEP2Cut
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

theorem E_strict {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) (i j : Fin (D.R.rS + 1)) (hji : j ≤ i) :
    (X - Psi w X⁻¹) i j = 0 := by
  have hP := Psi_upU w (upU_inv hU) (blk_inv w hU hB)
  rw [Matrix.sub_apply]
  rcases eq_or_lt_of_le hji with h | h
  · subst h; rw [(hU _ _).2 rfl, (hP _ _).2 rfl, sub_self]
  · rw [(hU _ _).1 h, (hP _ _).1 h, sub_self]

theorem unitCons (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ q, Agree δ M q) {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) (hG : GrD X)
    {a c : Fin (D.R.rS + 1)} (hac : a < c)
    (hlow : ∀ i j : Fin (D.R.rS + 1), i < j → j.val - i.val < c.val - a.val →
      (X - Psi w X⁻¹) i j ∈ qdPow D (j.val - i.val)) :
    Psi w (X - Psi w X⁻¹) a c - (X - Psi w X⁻¹) a c ∈ qdPow D (c.val - a.val) := by
  have hXd : IsUnit X.det := by rw [upU_det hU]; exact isUnit_one
  have hXi := upU_inv hU
  have hBi := blk_inv w hU hB
  have hGi := grD_inv hU hG
  have hY := Psi_upU w hU hB
  have hGY := Psi_grD w δ M hA hB hG
  have hPi : Psi w X⁻¹ = (Psi w X)⁻¹ := Psi_inv w hXd
  have hYd : IsUnit (Psi w X).det := by rw [upU_det hY]; exact isUnit_one
  have hES := E_strict w hU hB
  have hPE : Psi w (X - Psi w X⁻¹) = Psi w X * (X - Psi w X⁻¹) * X⁻¹ := by
    rw [Psi_sub, Psi_Psi w hBi, hPi, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hXd,
      Matrix.mul_nonsing_inv _ hYd, Matrix.one_mul]
  have decomp : Psi w X * (X - Psi w X⁻¹) * X⁻¹ - (X - Psi w X⁻¹) =
      (Psi w X - 1) * (X - Psi w X⁻¹) * X⁻¹ + (X - Psi w X⁻¹) * (X⁻¹ - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel
  rw [hPE, ← Matrix.sub_apply, decomp, Matrix.add_apply]
  have hac' : a.val < c.val := hac
  refine (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem ?_ ?_
  · rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases h1 : a < i
    · have h1' : a.val < i.val := h1
      by_cases h2 : i < j
      · have h2' : i.val < j.val := h2
        by_cases h3 : j ≤ c
        · have h3' : j.val ≤ c.val := h3
          rw [show (Psi w X - 1) a i = Psi w X a i by rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt h1), sub_zero]]
          have m1 := hGY a i (le_of_lt h1)
          have m2 := hlow i j h2 (by omega)
          have m3 := hGi j c h3
          have := mem_qdPow_mul (mem_ddPow_mul_qd m1 m2) m3
          rwa [show i.val - a.val + (j.val - i.val) + (c.val - j.val) = c.val - a.val by omega] at this
        · rw [(hXi j c).1 (lt_of_not_ge h3), mul_zero]; exact FractionalIdeal.zero_mem _
      · rw [hES i j (not_lt.1 h2), mul_zero, zero_mul]; exact FractionalIdeal.zero_mem _
    · have h0 : (Psi w X - 1) a i = 0 := by
        rw [Matrix.sub_apply]
        rcases eq_or_lt_of_le (not_lt.1 h1) with h | h
        · rw [h, (hY _ _).2 rfl, Matrix.one_apply_eq, sub_self]
        · rw [(hY _ _).1 h, Matrix.one_apply_ne (ne_of_gt h), sub_self]
      rw [h0, zero_mul, zero_mul]; exact FractionalIdeal.zero_mem _
  · rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases h1 : a < j
    · have h1' : a.val < j.val := h1
      by_cases h2 : j < c
      · have h2' : j.val < c.val := h2
        rw [show (X⁻¹ - 1) j c = X⁻¹ j c by rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt h2), sub_zero]]
        have := mem_qdPow_mul (hlow a j h1 (by omega)) (hGi j c (le_of_lt h2))
        rwa [show j.val - a.val + (c.val - j.val) = c.val - a.val by omega] at this
      · have h0 : (X⁻¹ - 1) j c = 0 := by
          rw [Matrix.sub_apply]
          rcases eq_or_lt_of_le (not_lt.1 h2) with h | h
          · rw [h, (hXi _ _).2 rfl, Matrix.one_apply_eq, sub_self]
          · rw [(hXi _ _).1 h, Matrix.one_apply_ne (ne_of_gt h), sub_self]
        rw [h0, mul_zero]; exact FractionalIdeal.zero_mem _
    · rw [hES a j (not_lt.1 h1), zero_mul]; exact FractionalIdeal.zero_mem _

end Formalism.L2.SG.Pf.StabIntLat
end
end

section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)

def UP : Subgroup (GG p) where
  carrier := {x | IsLoUni ((x.1 : GLp p) : MP p) ∧ IsUpUni ((x.2.unop : GLp p) : MP p)}
  one_mem' := ⟨ZsVolGrp.isLoUni_one, ZsVolGrp.isUpUni_one⟩
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · show IsLoUni ((x.1 * y.1 : GLp p) : MP p)
      rw [Units.val_mul]; exact ZsVolGrp.isLoUni_mul hx1 hy1
    · show IsUpUni (((x.2 * y.2).unop : GLp p) : MP p)
      rw [MulOpposite.unop_mul, Units.val_mul]; exact ZsVolGrp.isUpUni_mul hy2 hx2
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · show IsLoUni ((x.1⁻¹ : GLp p) : MP p)
      rw [Matrix.coe_units_inv]; exact (ZsVolGrp.isLoUni_inv hx1).1
    · show IsUpUni (((x.2⁻¹).unop : GLp p) : MP p)
      rw [MulOpposite.unop_inv, Matrix.coe_units_inv]; exact (ZsVolGrp.isUpUni_inv hx2).1

instance actGG : MulAction (GG p) (MP p) where
  smul x X := ((x.1 : GLp p) : MP p) * X * ((x.2.unop : GLp p) : MP p)
  one_smul X := by show ((1 : GLp p) : MP p) * X * (((1 : (GLp p)ᵐᵒᵖ).unop : GLp p) : MP p) = X; simp
  mul_smul x y X := by
    show (((x * y).1 : GLp p) : MP p) * X * ((((x * y).2).unop : GLp p) : MP p) =
      ((x.1 : GLp p) : MP p) * (((y.1 : GLp p) : MP p) * X * ((y.2.unop : GLp p) : MP p)) * ((x.2.unop : GLp p) : MP p)
    simp only [Prod.fst_mul, Prod.snd_mul, MulOpposite.unop_mul, Units.val_mul, Matrix.mul_assoc]

theorem smul_def (x : GG p) (X : MP p) : x • X = ((x.1 : GLp p) : MP p) * X * ((x.2.unop : GLp p) : MP p) := rfl

def KU : Subgroup (UP p) := (KP M p).subgroupOf (UP p)

def Va (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) : Set (MP p) :=
  {v | IsLoUni v ∧ ∀ i j : Fin (D.R.rS + 1), i ≠ j → Loc.sameBlock a.blocks i j = true → v i j = 0}

def BlockRetr (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) : Prop :=
  ∃ π : UP p →* UP p,
    CountAb.Data (a.mat) (MulAction.stabilizer (UP p) a.mat) π.ker (KU M p) π ∧
    ∀ x : UP p, π x = 1 ↔ ((x : GG p).1 : GLp p).val ∈ Va p a

end Formalism.L2.SG.Pf.CountAt
end
end

section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cong

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem one_mem_R {p : PlF D} (a b : Fin (D.R.rS + 1)) :
    (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b ∈ (M p).R := by
  rw [Matrix.one_apply]
  split_ifs
  · exact (M p).R.one_mem
  · exact (M p).R.zero_mem

theorem mem_R_of_sub_one {p : PlF D} (hA : Agree δ M p) {X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep}
    (h : EntIn (latS (D.s.atP p) (ellP p)) (X - 1)) (a b : Fin (D.R.rS + 1)) : X a b ∈ (M p).R := by
  have e : X a b = (X - 1) a b + (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b := by
    rw [Matrix.sub_apply]; ring
  rw [e]
  exact (M p).R.add_mem (latS_R hA (h a b)) (one_mem_R M a b)

theorem cong_at {p : PlF D} (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    ∃ c : (D.s.atP p).Fp, c ≠ 0 ∧ c ∈ 𝒪[(D.s.atP p).Fp] ∧ ∀ k : ProdE.StP M δ u u' w p,
      EntIn (latS (D.s.atP p) c) ((k.1.1 : ProdE.MP p) - 1) → EntIn (latS (D.s.atP p) c) ((k.1.2.unop : ProdE.MP p) - 1) →
        k ∈ ProdE.AP M δ u u' w p ⊓ ProdE.CPL M δ u u' w hA L U hL hU := by
  set Lp := lOf δ M p L U
  set Lpi := lOf δ M p L⁻¹ U⁻¹
  set Up := ρOf δ M p L U
  set Upi := ρOf δ M p L⁻¹ U⁻¹
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLL : Lp * Lpi = 1 := by
    rw [← lOf_mul δ M hA, hLi.2.2, hUi.2.1, lOf_one δ M hA]
  have hUU : Upi * Up = 1 := by
    rw [← ρOf_mul δ M hA, hLi.2.2, hUi.2.1, ρOf_one δ M hA]
  have hLp := ProdE.lOf_loUni M δ hA L U hL hU
  have hLpi := ProdE.lOf_loUni M δ hA L⁻¹ U⁻¹ hLi.1 hUi.1
  have hUp := ProdE.ρOf_upUni M δ hA L U hL hU
  have hUpi := ProdE.ρOf_upUni M δ hA L⁻¹ U⁻¹ hLi.1 hUi.1
  obtain ⟨s1, hs10, hs1O, hs1⟩ := bounded_mat (L := D.s.atP p) Lp
  obtain ⟨s2, hs20, hs2O, hs2⟩ := bounded_mat (L := D.s.atP p) Lpi
  obtain ⟨s3, hs30, hs3O, hs3⟩ := bounded_mat (L := D.s.atP p) Up
  obtain ⟨s4, hs40, hs4O, hs4⟩ := bounded_mat (L := D.s.atP p) Upi
  refine ⟨ellP p * (s1 * s2 * s3 * s4),
    mul_ne_zero (ellP_ne p) (mul_ne_zero (mul_ne_zero (mul_ne_zero hs10 hs20) hs30) hs40),
    Subring.mul_mem _ (ellP_mem p) (Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hs1O hs2O) hs3O) hs4O),
    fun k h1 h2 => ?_⟩
  obtain ⟨hk1, hk2, -⟩ := k.2
  have hO12 : s1 * s2 * s3 * s4 ∈ 𝒪[(D.s.atP p).Fp] :=
    Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hs1O hs2O) hs3O) hs4O
  have h1l : EntIn (latS (D.s.atP p) (ellP p)) ((k.1.1 : ProdE.MP p) - 1) :=
    entIn_latS_of_eq (t := s1 * s2 * s3 * s4) rfl hO12 h1
  have h2l : EntIn (latS (D.s.atP p) (ellP p)) ((k.1.2.unop : ProdE.MP p) - 1) :=
    entIn_latS_of_eq (t := s1 * s2 * s3 * s4) rfl hO12 h2
  have h1c : EntIn (latS (D.s.atP p) (ellP p)) (Lp * ((k.1.1 : ProdE.MP p) - 1) * Lpi) :=
    entIn_sandwich hs1 hs2 (entIn_latS_of_eq (t := s3 * s4) (by ring) (Subring.mul_mem _ hs3O hs4O) h1)
  have h2c : EntIn (latS (D.s.atP p) (ellP p)) (Upi * ((k.1.2.unop : ProdE.MP p) - 1) * Up) :=
    entIn_sandwich hs4 hs3 (entIn_latS_of_eq (t := s1 * s2) (by ring) (Subring.mul_mem _ hs1O hs2O) h2)
  have e1 : Lp * (k.1.1 : ProdE.MP p) * Lpi - 1 = Lp * ((k.1.1 : ProdE.MP p) - 1) * Lpi := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hLL]
  have e2 : Upi * (k.1.2.unop : ProdE.MP p) * Up - 1 = Upi * ((k.1.2.unop : ProdE.MP p) - 1) * Up := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU]
  have hc1 := ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul hLp hk1) hLpi
  have hc2 := ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul hUpi hk2) hUp
  refine Subgroup.mem_inf.2 ⟨⟨⟨fun a => (hk1 a a).2 rfl, fun a b h => (hk1 a b).1 h,
    mem_R_of_sub_one M δ hA h1l⟩, ⟨fun a => (hk2 a a).2 rfl, fun a b h => (hk2 a b).1 h, mem_R_of_sub_one M δ hA h2l⟩⟩,
    ⟨⟨fun a => (hc1 a a).2 rfl, fun a b h => (hc1 a b).1 h, mem_R_of_sub_one M δ hA (by rw [e1]; exact h1c)⟩,
    ⟨fun a => (hc2 a a).2 rfl, fun a b h => (hc2 a b).1 h, mem_R_of_sub_one M δ hA (by rw [e2]; exact h2c)⟩⟩⟩

end Cong

end Formalism.L2.SG.Pf.ProdEApprox
end
end
