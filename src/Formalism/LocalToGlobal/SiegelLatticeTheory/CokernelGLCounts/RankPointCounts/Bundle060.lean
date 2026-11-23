module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle052
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle048
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle034
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AlTieFD
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarFrameLA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle057
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle054
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc
open Classical

namespace Formalism.L2.SG.Pf.TupGlob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

def StabApprox (u u' : D.what₂.Word) : Prop :=
  ∀ (w : Point D.host.E (D.R.rS + 1)) (Z₁ A₀ B₀ : PairVal.MatR D), AtMat w Z₁ → IsLo A₀ → IsUp B₀ →
    (∀ p, ∃ l ρ : MatP D p, TieN.IntLow (Zd.M p) l ∧ TieN.IntUp (Zd.M p) ρ ∧
      locL Zd p A₀ B₀ * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * locR Zd p A₀ B₀ =
        l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ) →
    ∃ X Y : PairVal.MatR D, IsLo X ∧ IsUp Y ∧
      X * (Z₁ * Sg D.host.E D.R.rS) * Y = Z₁ * Sg D.host.E D.R.rS ∧
      ∀ p, TieN.IntLow (Zd.M p) (locL Zd p (A₀ * X) (Y * B₀)) ∧ TieN.IntUp (Zd.M p) (locR Zd p (A₀ * X) (Y * B₀))

def Dict : Prop :=
  ∀ A B : PairVal.MatR D, IsLo A → IsUp B →
    (∀ p, TieN.IntLow (Zd.M p) (locL Zd p A B) ∧ TieN.IntUp (Zd.M p) (locR Zd p A B)) →
    IntFr A.conjTranspose ∧ IntFr (Sg D.host.E D.R.rS * B * Sg D.host.E D.R.rS) ∧
      TieG A.conjTranspose (Sg D.host.E D.R.rS * B * Sg D.host.E D.R.rS)

variable {Zd}

theorem isUpUni_of {K : Type*} [CommRing K] {n : ℕ} {U : Matrix (Fin n) (Fin n) K} (h : IsUp U) : IsUpUni U :=
  fun i j => ⟨fun hji => h.2 j i hji, by rintro rfl; exact h.1 i⟩

theorem isUp_conjT {n : ℕ} {A : Matrix (Fin n) (Fin n) D.host.E} (h : IsLo A) : IsUp A.conjTranspose :=
  ⟨fun a => by simp [Matrix.conjTranspose_apply, h.1 a],
    fun a b hab => by simp [Matrix.conjTranspose_apply, h.2 a b hab]⟩

theorem globMove_of (u u' : D.what₂.Word) (hS : StabApprox Zd u u') (hD : Dict Zd) : GlobMove D Zd.M Zd.δ u u' := by
  intro w Z₁ Z₂ _ hZ₁ hZ₂ htup
  have hZ₁' := hZ₁
  obtain ⟨L1, U1, hL1, hU1, e1⟩ := hZ₁
  obtain ⟨L2, U2, hL2, hU2, e2⟩ := hZ₂
  rw [Formalism.L2.SG.Pf.AtPt.zhatOM_eq] at e1 e2
  have lo : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsLoUni L → Formalism.DoubleCosetMeasures.IsLowUni L :=
    fun L h => ⟨fun i j hij => (h i j).1 hij, fun a => (h a a).2 rfl⟩
  have up : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, IsUpUni U → Formalism.DoubleCosetMeasures.IsUpUni U :=
    fun U h => ⟨fun i j hji => (h i j).1 hji, fun a => (h a a).2 rfl⟩
  have lo' : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsLowUni L → IsLo L :=
    fun L h => ⟨h.2, fun a b hab => h.1 hab⟩
  have up' : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsUpUni U → IsUp U :=
    fun U h => ⟨h.2, fun a b hab => h.1 hab⟩
  have detL : ∀ L : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsLowUni L →
      IsUnit L.det := fun L h => by
    rw [Matrix.det_of_lowerTriangular L h.1]
    simp [h.2]
  have detU : ∀ U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, Formalism.DoubleCosetMeasures.IsUpUni U →
      IsUnit U.det := fun U h => by
    rw [Matrix.det_of_upperTriangular h.1]
    simp [h.2]
  have hA₀lo : IsLo (L2 * L1⁻¹) :=
    isLo_mul (lo' _ (lo _ hL2)) (lo' _ (Formalism.DoubleCosetMeasures.isLowUni_inv (hx := lo _ hL1)))
  have hB₀up : IsUp (U1⁻¹ * U2) :=
    isUp_mul (up' _ (Formalism.DoubleCosetMeasures.isUpUni_inv (hx := up _ hU1))) (up' _ (up _ hU2))
  have hmove : Z₂ * Sg D.host.E D.R.rS = (L2 * L1⁻¹) * (Z₁ * Sg D.host.E D.R.rS) * (U1⁻¹ * U2) := by
    rw [e2, e1]
    have i1 : L1⁻¹ * L1 = 1 := Matrix.nonsing_inv_mul L1 (detL _ (lo _ hL1))
    have i2 : U1 * U1⁻¹ = 1 := Matrix.mul_nonsing_inv U1 (detU _ (up _ hU1))
    calc L2 * ptMat w * U2 = L2 * (L1⁻¹ * L1) * ptMat w * ((U1 * U1⁻¹) * U2) := by
          rw [i1, i2, Matrix.mul_one, Matrix.one_mul]
      _ = L2 * L1⁻¹ * (L1 * ptMat w * U1) * (U1⁻¹ * U2) := by simp only [Matrix.mul_assoc]
  have hstab : ∀ p, ∃ l ρ : MatP D p, TieN.IntLow (Zd.M p) l ∧ TieN.IntUp (Zd.M p) ρ ∧
      locL Zd p (L2 * L1⁻¹) (U1⁻¹ * U2) * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) *
          locR Zd p (L2 * L1⁻¹) (U1⁻¹ * U2) =
        l * (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₁ * LsDatumB.sgnP p) * ρ := by
    intro p
    have hmem := mem_kkOrb_self (M := Zd.M) p (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z₂ * LsDatumB.sgnP p)
    have ht := htup p
    unfold tupZ at ht
    rw [← ht] at hmem
    obtain ⟨l, ρ, hl, hρ, heq⟩ := hmem
    refine ⟨l, ρ, hl, hρ, ?_⟩
    rw [← locMove (Zd := Zd) u u' p hA₀lo hB₀up hmove]
    exact heq
  obtain ⟨X, Y, hX, hY, hXY, hint⟩ := hS w Z₁ (L2 * L1⁻¹) (U1⁻¹ * U2) hZ₁' hA₀lo hB₀up hstab
  obtain ⟨hIA, hIB, hT⟩ := hD (L2 * L1⁻¹ * X) (Y * (U1⁻¹ * U2)) (isLo_mul hA₀lo hX) (isUp_mul hY hB₀up) hint
  have hSg : Sg D.host.E D.R.rS =
      Matrix.diagonal (fun b : Fin (D.R.rS + 1) => (-1 : D.host.E) ^ (D.R.rS - b.val)) := by
    have h1 := (Formalism.L2.SG.Pf.AtPt.zhatOM_eq (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)).symm.trans
      (Formalism.L2.SG.Pf.zhatOM_eq_pv 1)
    simpa using h1
  have hsq : ∀ b : Fin (D.R.rS + 1), (-1 : D.host.E) ^ (D.R.rS - b.val) * (-1 : D.host.E) ^ (D.R.rS - b.val) = 1 := by
    intro b
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have hSS : Sg D.host.E D.R.rS * Sg D.host.E D.R.rS = 1 := by
    rw [hSg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext b
    exact hsq b
  refine ⟨(L2 * L1⁻¹ * X).conjTranspose, Sg D.host.E D.R.rS * (Y * (U1⁻¹ * U2)) * Sg D.host.E D.R.rS,
    isUpUni_of (isUp_conjT (isLo_mul hA₀lo hX)), isUpUni_of ?_, hIA, hIB, hT, ?_⟩
  · rw [hSg]
    exact isUp_conj (isUp_mul hY hB₀up) _ _ hsq
  · rw [Matrix.conjTranspose_conjTranspose]
    have h3 : Z₂ * Sg D.host.E D.R.rS =
        L2 * L1⁻¹ * X * (Z₁ * Sg D.host.E D.R.rS) * (Y * (U1⁻¹ * U2)) := by
      rw [hmove]
      conv_lhs => rw [← hXY]
      simp only [Matrix.mul_assoc]
    calc Z₂ = Z₂ * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS := by
          rw [Matrix.mul_assoc, hSS, Matrix.mul_one]
      _ = L2 * L1⁻¹ * X * Z₁ * (Sg D.host.E D.R.rS * (Y * (U1⁻¹ * U2)) * Sg D.host.E D.R.rS) := by
          rw [h3]
          simp only [Matrix.mul_assoc]

end Formalism.L2.SG.Pf.TupGlob
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.AlTieIdx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prod_one_sub_inv_pow_pos (q : ℝ) (hq : 1 < q) (s : Finset ℕ) (hs : ∀ j ∈ s, 1 ≤ j) :
    0 < ∏ j ∈ s, (1 - 1 / q ^ j) :=
  Finset.prod_pos fun j hj => by
    have h1 : 1 < q ^ j := one_lt_pow₀ hq (by have := hs j hj; omega)
    have h2 : 1 / q ^ j < 1 := by rw [div_lt_one (by linarith)]; exact h1
    linarith

theorem cardGL_A (g m : ℕ) [hg : Fact g.Prime] :
    (Nat.card (GL (Fin m) (ZMod g)) : ℝ) = (g : ℝ) ^ (m * m) * ∏ j ∈ Finset.Ioc 0 m, (1 - 1 / (g : ℝ) ^ j) := by
  have hq0 : (g : ℝ) ≠ 0 := by exact_mod_cast hg.out.ne_zero
  rw [Matrix.card_GL_field, ZMod.card, Nat.cast_prod]
  have hterm : ∀ i : Fin m, (((g ^ m - g ^ (i : ℕ) : ℕ)) : ℝ) = (g : ℝ) ^ m * (1 - 1 / (g : ℝ) ^ (m - i)) := by
    intro i
    rw [Nat.cast_sub (Nat.pow_le_pow_right hg.out.pos i.2.le), Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one,
      mul_one_div, div_eq_mul_inv, ← pow_sub₀ _ hq0 (Nat.sub_le m i), Nat.sub_sub_self i.2.le]
  rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul]
  congr 1
  rw [Fin.prod_univ_eq_prod_range (fun i => 1 - 1 / (g : ℝ) ^ (m - i)) m]
  have h1 : ∏ i ∈ Finset.range m, (1 - 1 / (g : ℝ) ^ (m - i)) =
      ∏ i ∈ Finset.range m, (fun j => 1 - 1 / (g : ℝ) ^ (j + 1)) (m - 1 - i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    show _ = 1 - 1 / (g : ℝ) ^ (m - 1 - i + 1)
    rw [show m - 1 - i + 1 = m - i by omega]
  rw [h1, Finset.prod_range_reflect (fun j => 1 - 1 / (g : ℝ) ^ (j + 1)) m, Finset.range_eq_Ico,
    Finset.prod_Ico_add' (fun j => 1 - 1 / (g : ℝ) ^ j) 0 m 1]
  have h2 : Finset.Ico (0 + 1) (m + 1) = Finset.Ioc 0 m := by ext; simp; omega
  rw [h2]

theorem idx_arith (g r k : ℕ) (hg : g.Prime) :
    (glkC k g : ℝ) * (nnC r k g : ℝ) / (ggC r k g : ℝ) =
      (g : ℝ) ^ (-(((r + 1) * (2 * k + 2 * r + 1) : ℕ) : ℤ)) /
        ∏ i ∈ Finset.Icc (k + 1) (2 * r + k + 1), (1 - 1 / (g : ℝ) ^ i) := by
  have : Fact g.Prime := ⟨hg⟩
  have hq : (1 : ℝ) < g := by exact_mod_cast hg.one_lt
  have hq0 : (g : ℝ) ≠ 0 := by linarith
  have hc : Fintype.card (Formalism.FourierDecayAlt.S3.Idx r k) = 2 * r + k + 1 := by
    simp only [Formalism.FourierDecayAlt.S3.Idx, Formalism.FourierDecayAlt.S3.Mid, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega
  have hG : (ggC r k g : ℝ) = (Nat.card (GL (Fin (2 * r + k + 1)) (ZMod g)) : ℝ) := by
    unfold ggC
    exact_mod_cast Nat.card_congr
      (Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod g) (ZMod g) (Fintype.equivFinOfCardEq hc)).toMulEquiv)
  have hN : (nnC r k g : ℝ) = (g : ℝ) ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) := by
    unfold nnC
    rw [MassDataIdxStIm.card_isN, ZMod.card]
    push_cast
    try rfl
  unfold glkC
  rw [hG, hN, cardGL_A, cardGL_A]
  have hIcc : Finset.Icc (k + 1) (2 * r + k + 1) = Finset.Ioc k (2 * r + k + 1) := by
    ext; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc, ← Finset.prod_Ioc_consecutive _ (Nat.zero_le k) (by omega : k ≤ 2 * r + k + 1)]
  have hA : 0 < ∏ j ∈ Finset.Ioc 0 k, (1 - 1 / (g : ℝ) ^ j) :=
    prod_one_sub_inv_pow_pos _ hq _ (fun j hj => (Finset.mem_Ioc.1 hj).1)
  have hB : 0 < ∏ j ∈ Finset.Ioc k (2 * r + k + 1), (1 - 1 / (g : ℝ) ^ j) :=
    prod_one_sub_inv_pow_pos _ hq _ (fun j hj => by have := (Finset.mem_Ioc.1 hj).1; omega)
  have hpow : (g : ℝ) ^ (k * k) * (g : ℝ) ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2) /
      (g : ℝ) ^ ((2 * r + k + 1) * (2 * r + k + 1)) = (g : ℝ) ^ (-(((r + 1) * (2 * k + 2 * r + 1) : ℕ) : ℤ)) := by
    rw [← pow_add, ← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hq0]
    congr 1
    rcases r with _ | s
    · simp; ring
    · simp only [Nat.add_sub_cancel]; push_cast; ring
  rw [← hpow]
  generalize (∏ j ∈ Finset.Ioc 0 k, (1 - 1 / (g : ℝ) ^ j)) = A at hA ⊢
  generalize (∏ j ∈ Finset.Ioc k (2 * r + k + 1), (1 - 1 / (g : ℝ) ^ j)) = B at hB ⊢
  have hA' := hA.ne'
  have hB' := hB.ne'
  have hgn : (g : ℝ) ^ ((2 * r + k + 1) * (2 * r + k + 1)) ≠ 0 := pow_ne_zero _ hq0
  field_simp
  try ring

variable {D : D7} (X : HidaSetting D)

theorem ratio_eq (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal / (MassDataIdxSteps.muP X p (MassDataIdxSteps.KvX X p)).toReal =
      (glkC D.R.k (gOf p) : ℝ) * (nnC D.R.rS D.R.k (gOf p) : ℝ) / (ggC D.R.rS D.R.k (gOf p) : ℝ) := by
  obtain ⟨j, hj, hj0, hμj, hB0, hBt⟩ := MassDataIdxSteps.measB_of X MassDataIdxSteps.haarIdx MassDataIdxSteps.redIdx u p
    (MassDataIdxSteps.stTop X p) (Formalism.L2.SG.Pf.MassDataX.stK_holds X p) (Formalism.L2.SG.Pf.MassDataX.stRed_holds X p)
    (Formalism.L2.SG.Pf.MassDataX.stImB_holds X hb u p)
  have h1 : (MassDataIdxSteps.muP X p (MassDataIdxSteps.KvX X p)).toReal =
      (j : ℝ) * (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal := by
    rw [hμj, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hpos : (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hB0, hBt⟩
  rw [h1, ← hj]
  rcases eq_or_ne (j : ℝ) 0 with h0 | h0
  · simp [h0]
  · rw [mul_comm (j : ℝ) (MassDataIdxSteps.muP X p (MassDataIdxSteps.KnatX X u p)).toReal, mul_comm (j : ℝ),
      div_mul_eq_div_div, div_self hpos, div_mul_eq_div_div, div_self hj0]

theorem gAt_eq (p : TypX X) : gAt X p.1 = gOf p := by
  unfold gAt gOf
  split_ifs <;> rfl

theorem aP_typed (u : D.what₂.Word) (p : TypX X) :
    aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u) =
      ∏ i ∈ Finset.Icc (D.R.k + 1) (2 * D.R.rS + D.R.k + 1), (1 - 1 / (gOf p : ℝ) ^ i) := by
  obtain ⟨hN, hη⟩ := Formalism.L2.SG.Pf.gSplitX_holds X p
  have hT := Formalism.L2.SG.Pf.AlTieFD.T_not_mem X u p
  unfold aP
  rw [if_neg (by unfold Tw; exact hT), X.n_eq, ← Formalism.MainNotions.S.dimS_eq D.R, hη, hN, gAt_eq X p]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp

theorem indexTypC_holds (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    Formalism.L2.SG.Pf.NcIdx.IndexTypC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq := by
  intro p
  refine (ratio_eq X hb u p).trans ?_
  rw [idx_arith (gOf p) D.R.rS D.R.k (MassDataIdxSteps.gOf_prime X p), aP_typed X u p, gAt_eq X p]

end Formalism.L2.SG.Pf.AlTieIdx
end
end

section

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

theorem gram_fvec_zero {r : ℕ} {T : E} (F : FlagG S r T) :
    ∀ i j, (i ≠ Fin.last r ∨ j ≠ Fin.last r) → gram S F.fvec F.fvec i j = 0 := by
  intro i j hij
  have hfe : ∀ a : Fin r, F.fvec (Fin.castSucc a) = F.e a := fun a => by simp [FlagG.fvec]
  have hfz : F.fvec (Fin.last r) = F.z := by simp [FlagG.fvec]
  simp only [gram]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp at hij
    | cast b =>
      rw [hfz, hfe, ← LinearMap.IsSymm.eq_iff S.herm]
      exact F.z_orth b
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [hfz, hfe]; exact F.z_orth a
    | cast b => rw [hfe, hfe]; exact F.e_iso a b

theorem gram_fvec_last {r : ℕ} {T : E} (F : FlagG S r T) :
    gram S F.fvec F.fvec (Fin.last r) (Fin.last r) = -T := by
  simp only [gram, FlagG.fvec, Fin.snoc_last]
  exact F.z_norm

theorem comb_frame {r : ℕ} {T : E} (F : FlagG S r T) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hA : ∀ a b, b < a → A a b = 0) (hA1 : ∀ a, A a a = 1) :
    (∀ a b, (a ≠ Fin.last r ∨ b ≠ Fin.last r) → S.hT (comb S F.fvec A a) (comb S F.fvec A b) = 0) ∧
      S.hT (comb S F.fvec A (Fin.last r)) (comb S F.fvec A (Fin.last r)) = -T := by
  have hg : ∀ a b, S.hT (comb S F.fvec A a) (comb S F.fvec A b) =
      star (A (Fin.last r) a) * (-T) * A (Fin.last r) b := by
    intro a b
    have e := congrFun (congrFun (show gram S (comb S F.fvec A) (comb S F.fvec A) = Aᴴ * (gram S F.fvec F.fvec * A) by
      rw [gram_comb_right, gram_comb_left]) a) b
    simp only [gram] at e
    rw [e, Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]
    · rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last r), gram_fvec_last, Matrix.conjTranspose_apply, mul_assoc]
      · intro c _ hc; rw [gram_fvec_zero F _ _ (Or.inr hc), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro c _ hc
      rw [Matrix.mul_apply, Finset.sum_eq_zero fun d _ => by rw [gram_fvec_zero F _ _ (Or.inl hc), zero_mul], mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hl : ∀ a, a ≠ Fin.last r → A (Fin.last r) a = 0 := fun a ha => hA _ _ (Fin.lt_last_iff_ne_last.2 ha)
  refine ⟨fun a b hab => ?_, ?_⟩
  · rw [hg]
    rcases hab with h | h
    · rw [hl a h, star_zero, zero_mul, zero_mul]
    · rw [hl b h, mul_zero]
  · rw [hg, hA1, star_one, one_mul, mul_one]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLA

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem star_frame_orthogonal (γ : TermDef.Term D u u' F0 what₂) :
    (∀ a b, (a ≠ Fin.last D.R.rS ∨ b ≠ Fin.last D.R.rS) → (VS D).hT (starFrame γ a) (starFrame γ b) = 0) ∧
      (VS D).hT (starFrame γ (Fin.last D.R.rS)) (starFrame γ (Fin.last D.R.rS)) = -((Tu D u' : ℕ) : D.host.E) := by
  obtain ⟨hξ1, hξ2⟩ := inv_unitri _ (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).1 (admissibility_witness_unitriangular γ.lam (lf D F0) (repF γ)).2
  exact FsLA.comb_frame (repF γ).fl
    (fun a b => (((admXi D γ.lam (lf D F0) (repF γ))⁻¹ a b : 𝓞 D.host.E) : D.host.E))
    (fun a b h => by simp [hξ1 a b h]) (fun a => by simp [hξ2 a])

variable (u u' F0 what₂)

def StarMinors : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    Z.det ≠ 0 ∧ (starZh (frame (lf D F0)) (starFrame γ)).det ≠ 0 ∧
      leadMinorE (starZh (frame (lf D F0)) (starFrame γ)) D.R.rS * Z.det =
        leadMinorE Z D.R.rS * (starZh (frame (lf D F0)) (starFrame γ)).det

variable {u u' F0 what₂}

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

namespace Formalism.L2.SG.NGVanish

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hsEmb_eq_zero {Wq Wp : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (A : Wq →L[ℂ] Wp)
    (h : Formalism.L2.SG.PackageTie.hsEmb A = 0) : A = 0 := by
  have hi : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := by
    intro i
    have := congrArg (fun v : Formalism.L2.SG.PackageTie.HS Wq Wp => WithLp.ofLp v i) h
    simpa [Formalism.L2.SG.PackageTie.hsEmb] using this
  have hA : (A : Wq →ₗ[ℂ] Wp) = 0 :=
    (stdOrthonormalBasis ℂ Wq).toBasis.ext (fun i => by simpa using hi i)
  ext x
  simpa using congrArg (fun f : Wq →ₗ[ℂ] Wp => f x) hA

def FormNGC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ ν, Pinned X u u' ν → ∀ t ∈ (Y.tO u u').ngSet, (Y.tO u u').vec t ≠ 0 →
        (∃ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) ∧
        ∀ w : Point D.host.E (D.R.rS + 1), toPts w = ptPN t → (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) →
          ∃ (c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (B : X.Vpi u' →L[ℂ] X.Vpi u'),
            OOt t = c • A.comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
              OO (ν (Formalism.L2.SG.RealObj.gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u')
                (Formalism.L2.SG.RealObj.gamW X u u' w)).comp B)

theorem stepTermVanish_of_form (h : FormNGC) : StepTermVanish := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a₀, b₀, h2⟩ := h Cg cb Cw cT CT C0
  refine ⟨a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u u' hc ν hν t ht hJ => ?_⟩
  by_contra hv
  obtain ⟨⟨w, hw, hrep⟩, hform⟩ := h2 C' Cl e1 e2 D large₂ X Y u u' hc ν hν t ht hv
  have hex : ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = ptPN t ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g :=
    ⟨w, hw, hrep⟩
  unfold J2of at hJ
  rw [dite_eq_left hex] at hJ
  have hJw : Jw Y u u' ν hex.choose = 0 :=
    hsEmb_eq_zero _ (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hJ))
  obtain ⟨c, A, B, hO⟩ := hform hex.choose hex.choose_spec.1 hex.choose_spec.2
  have key : ∀ (k χ c : ℂ) (A : X.Vpi u →L[ℂ] X.Vpi u) (Z : X.Vpi u' →L[ℂ] X.Vpi u)
      (B : X.Vpi u' →L[ℂ] X.Vpi u'), k • Z = 0 → k • (χ • (c • A.comp (Z.comp B))) = 0 := by
    intro k χ c A Z B hZ
    have hy : ∀ y, k • Z y = 0 := fun y => by simpa using congrArg (fun T => T y) hZ
    ext x
    simp only [smul_apply, ContinuousLinearMap.comp_apply, zero_apply]
    rw [smul_comm k χ, smul_comm k c, ← map_smul A k, hy]
    simp
  have hamp : ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0 := by
    unfold ampN
    rw [hO]
    unfold Jw at hJw
    exact key _ _ _ _ _ _ hJw
  apply hv
  show vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0
  unfold vec
  rw [hamp]
  simp
  rfl

end Formalism.L2.SG.NGVanish
end
end
