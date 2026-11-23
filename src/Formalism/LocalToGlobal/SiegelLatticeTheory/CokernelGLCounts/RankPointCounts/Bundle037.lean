module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PtCellUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StabilizerIndexVolumes.StabMul
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.BlockPermutation

open Formalism.MainNotions.S Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj

variable {K : Type*} [Field K]

theorem pval_pperm : ∀ (bs : List (K × ℕ)) (i : ℕ), i < (bs.map Prod.snd).sum →
    pval bs (pperm bs i) = pval bs i
  | [], i, h => by simp at h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hi : i < s
    · simp only [pperm, pval, hi, if_true]
      rw [if_pos (by omega)]
    · simp only [pperm, pval, hi, if_false]
      rw [if_neg (by omega), show s + pperm bs (i - s) - s = pperm bs (i - s) by omega]
      exact pval_pperm bs (i - s) (by omega)

theorem blkOf_pperm : ∀ (bs : List (K × ℕ)) (i : ℕ), i < (bs.map Prod.snd).sum →
    blkOf bs (pperm bs i) = blkOf bs i
  | [], i, h => by simp at h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hi : i < s
    · simp only [pperm, blkOf, hi, if_true]
      rw [if_pos (by omega)]
    · simp only [pperm, blkOf, hi, if_false]
      rw [if_neg (by omega), show s + pperm bs (i - s) - s = pperm bs (i - s) by omega]
      rw [blkOf_pperm bs (i - s) (by omega)]

theorem pperm_lt_iff : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i = blkOf bs j → (i < j ↔ pperm bs j < pperm bs i)
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [pperm, h1, h2, if_true]; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_false, add_left_inj] at hb
      simp only [pperm, h1, h2, if_false]
      have := pperm_lt_iff bs (i - s) (j - s) (by omega) (by omega) hb
      omega

theorem lt_of_blkOf_lt : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i < blkOf bs j → i < j ∧ pperm bs i < pperm bs j
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [blkOf, h1, h2, if_true] at hb; omega
    · simp only [pperm, h1, h2, if_true, if_false]; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_false, add_lt_add_iff_right] at hb
      simp only [pperm, h1, h2, if_false]
      have := lt_of_blkOf_lt bs (i - s) (j - s) (by omega) (by omega) hb
      omega

theorem pperm_add : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i = blkOf bs j → pperm bs i + i = pperm bs j + j
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [pperm, h1, h2, if_true]; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_false, add_left_inj] at hb
      simp only [pperm, h1, h2, if_false]
      have := pperm_add bs (i - s) (j - s) (by omega) (by omega) hb
      omega

theorem blkOf_mono : ∀ (bs : List (K × ℕ)) (i j : ℕ), i ≤ j → blkOf bs i ≤ blkOf bs j
  | [], i, j, _ => by simp [blkOf]
  | (t, s) :: bs, i, j, hij => by
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp [blkOf, h1, h2]
    · simp [blkOf, h1, h2]
    · omega
    · simp only [blkOf, h1, h2, if_false, add_le_add_iff_right]
      exact blkOf_mono bs (i - s) (j - s) (by omega)

theorem pval_eq_of_blk : ∀ (bs : List (K × ℕ)) (i j : ℕ), i < (bs.map Prod.snd).sum → j < (bs.map Prod.snd).sum →
    blkOf bs i = blkOf bs j → pval bs i = pval bs j
  | [], i, j, h, _, _ => by simp at h
  | (t, s) :: bs, i, j, hi, hj, hb => by
    simp only [List.map_cons, List.sum_cons] at hi hj
    by_cases h1 : i < s <;> by_cases h2 : j < s
    · simp only [pval, h1, h2, if_true]
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_true, if_false] at hb; omega
    · simp only [blkOf, h1, h2, if_false, add_left_inj] at hb
      simp only [pval, h1, h2, if_false]
      exact pval_eq_of_blk bs (i - s) (j - s) (by omega) (by omega) hb

section Pt

variable {N : ℕ} (p : Point K N)

theorem pval_pinv (a : Fin N) : pval p.1 (pinv p a).val = pval p.1 a.val :=
  pval_pperm p.1 a.val (by rw [p.2.2]; exact a.isLt)

theorem blkOf_pinv (a : Fin N) : blkOf p.1 (pinv p a).val = blkOf p.1 a.val :=
  blkOf_pperm p.1 a.val (by rw [p.2.2]; exact a.isLt)

theorem pinv_lt_iff (a b : Fin N) (hb : blkOf p.1 a.val = blkOf p.1 b.val) : a < b ↔ pinv p b < pinv p a :=
  pperm_lt_iff p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

theorem lt_of_blk_lt (a b : Fin N) (hb : blkOf p.1 a.val < blkOf p.1 b.val) : a < b ∧ pinv p a < pinv p b :=
  lt_of_blkOf_lt p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

theorem pinv_add (a b : Fin N) (hb : blkOf p.1 a.val = blkOf p.1 b.val) :
    (pinv p a).val + a.val = (pinv p b).val + b.val :=
  pperm_add p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

theorem pval_eq_blk (a b : Fin N) (hb : blkOf p.1 a.val = blkOf p.1 b.val) : pval p.1 a.val = pval p.1 b.val :=
  pval_eq_of_blk p.1 a.val b.val (by rw [p.2.2]; exact a.isLt) (by rw [p.2.2]; exact b.isLt) hb

end Pt

end Formalism.L2.SG.Pf.BlockPermutation
end
end

section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Split

variable {F K : Type*} [Field F] [CommRing K] [Algebra F K] {r : ℕ}

theorem smul_eq_of_cx (e : K ≃ₐ[F] F × F) {X Y : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : cx e X = cx e Y) :
    e.symm (1, 0) • X = e.symm (1, 0) • Y := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  apply e.injective
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
  have := congrFun (congrFun h i) j
  simp only [cx, Matrix.map_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_coe] at this
  ext
  · simp [this]
  · simp

theorem smul_eq_of_cy (e : K ≃ₐ[F] F × F) {X Y : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : cy e X = cy e Y) :
    e.symm (0, 1) • X = e.symm (0, 1) • Y := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  apply e.injective
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
  have := congrFun (congrFun h i) j
  simp only [cy, Matrix.map_apply, RingHom.comp_apply, RingHom.coe_snd, RingHom.coe_coe] at this
  ext
  · simp
  · simp [this]

theorem cx_diag (e : K ≃ₐ[F] F × F) (d : Fin (r + 1) → F) :
    cx e (Matrix.diagonal fun i => algebraMap F K (d i)) = Matrix.diagonal d := by
  ext i j
  simp only [cx, Matrix.map_apply, Matrix.diagonal_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_coe]
  split_ifs <;> simp [AlgEquiv.commutes]

theorem cy_diag (e : K ≃ₐ[F] F × F) (d : Fin (r + 1) → F) :
    cy e (Matrix.diagonal fun i => algebraMap F K (d i)) = Matrix.diagonal d := by
  ext i j
  simp only [cy, Matrix.map_apply, Matrix.diagonal_apply, RingHom.comp_apply, RingHom.coe_snd, RingHom.coe_coe]
  split_ifs <;> simp [AlgEquiv.commutes]

end Split

section Data

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp)

theorem mode_data {p : PlF D} (hA : Agree δ M p) :
    ∃ (ex ey : (D.s.atP p).Ep) (d di gg ggi : Fin (D.R.rS + 1) → (D.s.atP p).Ep),
      ex ∈ (D.s.atP p).O ∧ ey ∈ (D.s.atP p).O ∧ ex * ex = ex ∧ ey * ey = ey ∧ ex + ey = 1 ∧ ex * ey = 0 ∧
      (∀ i, d i * di i = 1) ∧ (∀ i, gg i * ggi i = 1) ∧
      ∀ a b : Formalism.L2.SG.PairVal.MatR D,
        ex • lOf δ M p a b = ex • (Matrix.diagonal d * a.map (D.s.atP p).ιE * Matrix.diagonal di) ∧
        ey • ρOf δ M p a b = ey • (Matrix.diagonal ggi * (a.map (D.s.atP p).ιE).transpose * Matrix.diagonal gg) := by
  obtain ⟨-, -, -, -, -, hsp⟩ := id hA
  cases hM : (M p).split with
  | none =>
    refine ⟨1, 0, fun i => (M p).L.cj (frFac δ p i), fun i => Ring.inverse ((M p).L.cj (frFac δ p i)),
      fun _ => 1, fun _ => 1, (D.s.atP p).O.one_mem, (D.s.atP p).O.zero_mem, mul_one 1, mul_zero 0, add_zero 1,
      mul_zero 1, fun i => Ring.mul_inverse_cancel _ ((frFac_unit δ M hA i).map _), fun _ => mul_one 1, fun a b => ⟨?_, ?_⟩⟩
    · simp only [lOf, hM, one_smul]
      exact lL_eq _ _ _ a
    · simp only [zero_smul]
  | some g =>
    rcases hR : (D.s.atP p).split with _ | sg
    · simp [hM, hR] at hsp
    · have hsp' : g.e = sg.e ∧ g.q = sg.q := by simpa [hM, hR] using hsp
      have hx := fun i => (split_units δ M hA g i).1
      have hy := fun i => (split_units δ M hA g i).2
      have hmemO : ∀ a b : (D.s.atP p).Fp, a ∈ 𝒪[(D.s.atP p).Fp] → b ∈ 𝒪[(D.s.atP p).Fp] →
          g.e.symm (a, b) ∈ (D.s.atP p).O := by
        intro a b ha hb
        rw [Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg, ← hsp'.1, AlgEquiv.apply_symm_apply]
        exact ⟨ha, hb⟩
      refine ⟨g.e.symm (1, 0), g.e.symm (0, 1),
        fun i => algebraMap _ _ ((g.e (frFac δ p i)).2), fun i => algebraMap _ _ ((g.e (frFac δ p i)).2)⁻¹,
        fun i => algebraMap _ _ ((g.e (frFac δ p i)).1), fun i => algebraMap _ _ ((g.e (frFac δ p i)).1)⁻¹,
        hmemO 1 0 (Subring.one_mem _) (Subring.zero_mem _), hmemO 0 1 (Subring.zero_mem _) (Subring.one_mem _),
        ?_, ?_, ?_, ?_, fun i => by rw [← map_mul, mul_inv_cancel₀ (hy i), map_one],
        fun i => by rw [← map_mul, mul_inv_cancel₀ (hx i), map_one], fun a b => ⟨?_, ?_⟩⟩
      · apply g.e.injective; simp
      · apply g.e.injective; simp
      · apply g.e.injective; simp
      · apply g.e.injective; simp
      · simp only [lOf, hM]
        apply smul_eq_of_cx
        rw [cx_lG, cx_mul, cx_mul, cx_diag, cx_diag]
        rfl
      · simp only [ρOf, hM]
        apply smul_eq_of_cy
        rw [cy_ρG, cy_mul, cy_mul, cy_diag, cy_diag]
        rfl

end Data

end Formalism.L2.SG.Pf.ProdEApprox
end
end

section

noncomputable section

namespace Formalism.L2.SG.LsDatumB

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Classical ValuativeRel

section Local

variable {D : Formalism.BasicNotions.D7}

abbrev MatP (D : Formalism.BasicNotions.D7) (p : PlF D) : Type :=
  Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ)

def kkOrb (p : PlF D) (Y : MatP D p) : Set (MatP D p) :=
  {Y' | ∃ l ρ : MatP D p, Formalism.MainNotions.S.TieN.IntLow (M p) l ∧ Formalism.MainNotions.S.TieN.IntUp (M p) ρ ∧ Y' = l * Y * ρ}

def IntP (p : PlF D) (Y : MatP D p) : Prop := ∀ a b, Y a b ∈ (M p).R

def InOrbP (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : Prop :=
  ∃ w₀, modPt δ T T' p w = some w₀ ∧
    ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
      Y = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2

def phL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : ℂ :=
  match modPt δ T T' p w with
  | none => 0
  | some w₀ =>
    if h : ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN w₀ → (D.s.atP p).Ep),
        Y = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 then
      dfac M δ T T' p w *
        (M p).psiR (Loc.simpleLow (Loc.uLow h.choose.1) + Loc.simpleUp (Loc.uUp w₀ h.choose.2))
    else 0

def wtL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : ℝ :=
  match modPt δ T T' p w with
  | none => 0
  | some w₀ =>
    (((Measure.pi fun _ : Loc.IL (D.R.rS + 1) => (M p).mu).prod (Measure.pi fun _ : Loc.IN w₀ => (M p).mu))
      {xy | Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp w₀ xy.2 ∈ kkOrb M p Y}).toReal

def thL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y : MatP D p) : Option ((M p).Cls D.R.rS) :=
  clsOf (M p) (Y + Matrix.of fun a b =>
    if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cornerSh δ T T' p w else 0)

def nIsoO (p : PlF D) (o o' : Option ((M p).Cls D.R.rS)) : ℕ :=
  match o, o' with
  | some c, some c' => (M p).nIso (Quotient.out c) (Quotient.out c')
  | _, _ => 0

def IsLCls (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)) : Prop :=
  ∃ Y, IntP M p Y ∧ InOrbP δ T T' p w Y ∧ O = kkOrb M p Y

def repL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)) : MatP D p :=
  if h : IsLCls M δ T T' p w O then h.choose else 0

def fL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O then
    phL M δ T T' p w (repL M δ T T' p w O) * (wtL M δ T T' p w (repL M δ T T' p w O) : ℂ) *
      (nIsoO M p τ (thL M δ T T' p w (repL M δ T T' p w O)) : ℂ)
  else 0

def gL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O ∧ thL M δ T T' p w (repL M δ T T' p w O) = τ then
    phL M δ T T' p w (repL M δ T T' p w O) * (wtL M δ T T' p w (repL M δ T T' p w O) : ℂ)
  else 0

def hL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O then
    phL M δ T T' p w (repL M δ T T' p w O) * (wtL M δ T T' p w (repL M δ T T' p w O) : ℂ)
  else 0

def kL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O then (nIsoO M p τ (thL M δ T T' p w (repL M δ T T' p w O)) : ℂ) else 0

def eL (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (τ : Option ((M p).Cls D.R.rS)) (O : Set (MatP D p)) : ℂ :=
  if IsLCls M δ T T' p w O ∧ thL M δ T T' p w (repL M δ T T' p w O) = τ then 1 else 0

def sgnP (p : PlF D) : MatP D p := Matrix.diagonal fun b : Fin (D.R.rS + 1) => (-1) ^ (D.R.rS - b.val)

def x0L (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) : Set (MatP D p) := kkOrb M p (modMat δ T T' p w)

end Local

section Glob

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

def nrep (γ : TermDef.Term D u u' F0 what₂) :
    Option (Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D) :=
  if h : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) × PairVal.MatR D ×
      PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 then some h.choose else none

def zT (γ : TermDef.Term D u u' F0 what₂) : PairVal.MatR D :=
  match nrep γ with
  | some x => ZhatL (lf D F0) x.2.1
  | none => 0

def ptT (γ : TermDef.Term D u u' F0 what₂) : Point D.host.E (D.R.rS + 1) :=
  match nrep γ with
  | some x => x.1
  | none => PairVal.junkPoint D u u'

variable (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)

def thT (γ : TermDef.Term D u u' F0 what₂) (p : PlF D) : Option ((M p).Cls D.R.rS) :=
  thL M δ (D.mem u).A.T (D.mem u').A.T p (ptT γ) (CntLocal.ZZP (M := M) δ u u' p (zT γ))

def locT (γ : TermDef.Term D u u' F0 what₂) (p : PlF D) : Set (MatP D p) :=
  kkOrb M p (CntLocal.ZZP (M := M) δ u u' p (zT γ) * sgnP p)

def dnT (L : CntLocal.LocSp D M) (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]) (γ : TermDef.Term D u u' F0 what₂) : ℝ :=
  ∏' p, CntLocal.densP L δ ϖ (CntLocal.Tn u) (CntLocal.Tn u') (zT γ) p

end Glob

end Formalism.L2.SG.LsDatumB
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

def cellEquiv (hD : Data W S N' K π) :
    Quotient (Setoid.ker (Formalism.L2.SG.Pf.ProdEP2Core.dcMap (Ak S K) (πk W S N' K π hD) (Hk W K g))) ≃
      Quotient (cellRel W N' K g) := by
  refine Equiv.ofBijective (Quotient.lift (fun k => (⟦toCell W S N' K π g hD k⟧ : Quotient (cellRel W N' K g)))
    (fun k₁ k₂ h => ?_)) ⟨?_, ?_⟩
  · apply Quotient.sound
    exact (cellRel_iff W S N' K π g hD k₁ k₂).2
      ((Formalism.L2.SG.Pf.ProdEP2Core.dcMap_eq_iff (Ak S K) (πk W S N' K π hD) (Hk W K g) k₁ k₂).1 h)
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | h k₁ =>
      induction y using Quotient.inductionOn with
      | h k₂ =>
        apply Quotient.sound
        have h2 := Quotient.exact hxy
        exact (Formalism.L2.SG.Pf.ProdEP2Core.dcMap_eq_iff (Ak S K) (πk W S N' K π hD) (Hk W K g) k₁ k₂).2
          ((cellRel_iff W S N' K π g hD k₁ k₂).1 h2)
  · intro y
    induction y using Quotient.inductionOn with
    | h c =>
      obtain ⟨k, rfl⟩ := toCell_surj W S N' K π g hD c
      exact ⟨⟦k⟧, rfl⟩

theorem card_cells (hD : Data W S N' K π) :
    Nat.card (Quotient (cellRel W N' K g)) = ((Hk W K g).map (πk W S N' K π hD)).index := by
  rw [← Nat.card_congr (cellEquiv W S N' K π g hD)]
  exact Formalism.L2.SG.Pf.ProdEP2Core.card_dc (Ak S K) (πk W S N' K π hD) (Hk W K g) (πk_id W S N' K π hD)

end Formalism.L2.SG.Pf.CountAb
end
end
