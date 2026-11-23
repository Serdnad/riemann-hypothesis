module

public import Formalism.HermitianCurvature.StatementJCT
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZAbs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZZLoc
public import Formalism.SelfDualUnimodular.LocalLatticeDictionary.Bundle001
public import Formalism.SelfDualUnimodular.LocalLatticeDictionary.SemiGenusLocal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictCore
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.SG.Pf.CarrierT

theorem polynomial_le_decay_threshold (r k i : ℝ) (hr : 0 ≤ r) (hk : 0 ≤ k) (hi0 : 0 ≤ i) (hi : i ≤ r) :
    9 * (i + 1) * (127 * (r + 1) ^ 3 * (20 * (r + 1) * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 1) +
      20 * (r + 1) * (1 + 3 * (r + 1)) * i +
      (6 * i + 3 * (r + 1)) * (5 + 3 * (r + 1) * (20 * (r + 1) + 2) * (2 * r + k + 1) + 20 * (r + 1) * r) ≤
    25000 * (2 * r + k + 1) ^ 7 := by
  lift r to NNReal using hr
  lift k to NNReal using hk
  lift i to NNReal using hi0
  calc _ ≤ 9 * ((r : ℝ) + 1) * (127 * ((r : ℝ) + 1) ^ 3 * (20 * ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 +
          (2 * (r : ℝ) + k + 1) ^ 3) + 1) +
        20 * ((r : ℝ) + 1) * (1 + 3 * ((r : ℝ) + 1)) * r +
        (6 * (r : ℝ) + 3 * ((r : ℝ) + 1)) * (5 + 3 * ((r : ℝ) + 1) * (20 * ((r : ℝ) + 1) + 2) *
          (2 * (r : ℝ) + k + 1) + 20 * ((r : ℝ) + 1) * r) := by gcongr
    _ ≤ 25000 * (2 * (r : ℝ) + k + 1) ^ 7 := by
      rw [← sub_nonneg]
      ring_nf
      positivity

def decayThreshold (Cc : ℝ) (k r : ℕ) : ℝ := (25000 + 21 * |Cc|) * (2 * (r : ℝ) + k + 1) ^ 7

section setting

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {Wp Wq : NumberField.InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem sliceBudget_decayThreshold (S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq) (Cc : ℝ) :
    Formalism.FourierDecayAlt.JCT.SliceBudget S (decayThreshold Cc S.G.k S.G.r) := by
  intro v i hi
  have hi' : (i : ℝ) ≤ S.G.r := by exact_mod_cast hi
  have hpoly := polynomial_le_decay_threshold (S.G.r : ℝ) (S.G.k : ℝ) (i : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hi'
  have hN : (S.Ntop : ℝ) = 20 * ((S.G.r : ℝ) + 1) := by
    simp only [Formalism.FourierDecayAlt.C.HidaSetting.Ntop, Formalism.FourierDecayAlt.C.Kst]
    push_cast
    ring
  have hn7 : (0 : ℝ) ≤ (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 7 := by positivity
  calc _ = 9 * ((i : ℝ) + 1) * (127 * ((S.G.r : ℝ) + 1) ^ 3 * (20 * ((S.G.r : ℝ) + 1) *
          (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) + 1) +
        20 * ((S.G.r : ℝ) + 1) * (1 + 3 * ((S.G.r : ℝ) + 1)) * i +
        (6 * (i : ℝ) + 3 * ((S.G.r : ℝ) + 1)) * (5 + 3 * ((S.G.r : ℝ) + 1) * (20 * ((S.G.r : ℝ) + 1) + 2) *
          (2 * (S.G.r : ℝ) + S.G.k + 1) + 20 * ((S.G.r : ℝ) + 1) * S.G.r) := by
        simp only [Formalism.FourierDecayAlt.P5.Auser, Formalism.FourierDecayAlt.P5.mmUser, Formalism.FourierDecayAlt.P5.nV, hN]
        push_cast
        rw [hN]
    _ ≤ 25000 * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 7 := hpoly
    _ ≤ decayThreshold Cc S.G.k S.G.r := by
        unfold decayThreshold
        nlinarith [abs_nonneg Cc]

theorem poly_le_decayThreshold (S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq) (Cc : ℝ) :
    Cc * ((S.G.r : ℝ) + 1) ^ 4 *
      ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) ≤ decayThreshold Cc S.G.k S.G.r := by
  have hN : (S.Ntop : ℝ) = 20 * ((S.G.r : ℝ) + 1) := by
    simp only [Formalism.FourierDecayAlt.C.HidaSetting.Ntop, Formalism.FourierDecayAlt.C.Kst]
    push_cast
    ring
  rw [hN]
  unfold decayThreshold
  have hs : (1 : ℝ) ≤ (S.G.r : ℝ) + 1 := by linarith [(Nat.cast_nonneg S.G.r : (0 : ℝ) ≤ S.G.r)]
  have hsn : (S.G.r : ℝ) + 1 ≤ 2 * (S.G.r : ℝ) + S.G.k + 1 := by
    linarith [(Nat.cast_nonneg S.G.r : (0 : ℝ) ≤ S.G.r), (Nat.cast_nonneg S.G.k : (0 : ℝ) ≤ S.G.k)]
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = (S.G.r : ℝ) + 1 := ⟨_, rfl⟩
  obtain ⟨n, hn_def⟩ : ∃ n : ℝ, n = 2 * (S.G.r : ℝ) + S.G.k + 1 := ⟨_, rfl⟩
  rw [← hs_def, ← hn_def]
  rw [← hs_def] at hs hsn
  rw [← hn_def] at hsn
  have hs0 : 0 ≤ s := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hX0 : 0 ≤ s ^ 4 * (20 * s * n ^ 2 + n ^ 3) :=
    mul_nonneg (pow_nonneg hs0 4) (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs0) (sq_nonneg n))
      (pow_nonneg hn0 3))
  have hX : s ^ 4 * (20 * s * n ^ 2 + n ^ 3) ≤ 21 * n ^ 7 := by
    have h4 : s ^ 4 ≤ n ^ 4 := pow_le_pow_left₀ hs0 hsn 4
    have h1 : 20 * s * n ^ 2 + n ^ 3 ≤ 21 * n ^ 3 := by nlinarith [sq_nonneg n]
    calc s ^ 4 * (20 * s * n ^ 2 + n ^ 3) ≤ n ^ 4 * (21 * n ^ 3) := by
          apply mul_le_mul h4 h1 (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs0) (sq_nonneg n))
            (pow_nonneg hn0 3)) (pow_nonneg hn0 4)
      _ = 21 * n ^ 7 := by ring
  have hn7 : 0 ≤ n ^ 7 := pow_nonneg hn0 7
  calc Cc * s ^ 4 * (20 * s * n ^ 2 + n ^ 3) = Cc * (s ^ 4 * (20 * s * n ^ 2 + n ^ 3)) := by ring
    _ ≤ |Cc| * (s ^ 4 * (20 * s * n ^ 2 + n ^ 3)) :=
        mul_le_mul_of_nonneg_right (le_abs_self Cc) hX0
    _ ≤ |Cc| * (21 * n ^ 7) := mul_le_mul_of_nonneg_left hX (abs_nonneg Cc)
    _ ≤ (25000 + 21 * |Cc|) * n ^ 7 := by nlinarith [abs_nonneg Cc]

end setting

end Formalism.L2.SG.Pf.CarrierT
end
end

section

namespace Formalism.L2.SG.Pf.LatDictZ

theorem zOrbit_of_open (hP : Z0.PrimPlaneLoc) (hA : Z0.AdelGlue) : LatDictZ.ZOrbit :=
  Z0.zOrbit_of (Z0.BR.semiGenusZ_of (Z3.semiGenusZLoc_of Z0.SGC.semi_genus_local hP)) hA
    Z0.LF.lattice_locally_finite

end Formalism.L2.SG.Pf.LatDictZ
end

section

noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting

variable {N r : ℕ} (ε : Fin N → Bool) (F G : Fin (r + 1) → Fin N → ℂ) (T T' : ℝ) (π : Fin (r + 1) → Fin (r + 1))
  (blk : Fin (r + 1) → ℕ)
  (hFF : ∀ a b, hJ ε (F a) (F b) = lastDiag (-(T : ℂ)) a b)
  (hGG : ∀ a b, hJ ε (G a) (G b) = lastDiag (-(T' : ℂ)) a b)
  (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a) (hanti : ∀ a b, blk a = blk b → a < b → π b < π a)
  (hZ : ∀ c b, Zm ε F G c b ≠ 0 ↔ c = π b)
  (hgap : 1 - (T : ℂ) * T' * ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r) *
    starRingEnd ℂ ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r))) ≠ 0)

include hFF hGG hπ hZ hgap in
theorem Yc_G {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (b : Fin (r + 1)) :
    Yc ε F G C *ᵥ G b = ∑ b', C b' b • G b' := by
  have hΓ := gram_unit (ε := ε) (F := F) (G := G) (T := T) (T' := T') (π := π) (hFF := hFF)
    (hGG := hGG) (hπ := hπ) (hZ := hZ) (hgap := hgap)
  have hW : Yc ε F G C * Wfg F G = Wfg F G * (1 + Mm ε F G C) := rankUpdate_mul _ _ _ hΓ
  have hGcol : G b = Wfg F G *ᵥ Pi.single (Sum.inr b) 1 := by
    funext p
    rw [Matrix.mulVec_single]
    simp [Wfg, Function.swap]
  rw [hGcol, Matrix.mulVec_mulVec, hW, ← Matrix.mulVec_mulVec, Matrix.mulVec_single]
  funext p
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Wfg, Mm, Matrix.one_apply, Finset.sum_apply, mul_comm]

include hFF hGG hπ hZ hgap in
theorem Yc_F {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (a : Fin (r + 1)) :
    Yc ε F G C *ᵥ F a = ∑ a', Am ε F G C a' a • F a' := by
  have hΓ := gram_unit (ε := ε) (F := F) (G := G) (T := T) (T' := T') (π := π) (hFF := hFF)
    (hGG := hGG) (hπ := hπ) (hZ := hZ) (hgap := hgap)
  have hW : Yc ε F G C * Wfg F G = Wfg F G * (1 + Mm ε F G C) := rankUpdate_mul _ _ _ hΓ
  have hFcol : F a = Wfg F G *ᵥ Pi.single (Sum.inl a) 1 := by
    funext p
    rw [Matrix.mulVec_single]
    simp [Wfg, Function.swap]
  rw [hFcol, Matrix.mulVec_mulVec, hW, ← Matrix.mulVec_mulVec, Matrix.mulVec_single]
  funext p
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Wfg, Mm, Matrix.one_apply, Finset.sum_apply, mul_comm]

theorem rowLast {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (k : Fin (r + 1)) :
    C (Fin.last r) k = if k = Fin.last r then 1 else 0 := by
  obtain ⟨hdiag, hup⟩ := hC
  split_ifs with hk
  · rw [hk]
    exact hdiag _
  · by_contra h
    have h1 := (hup _ _ h).1
    exact hk (le_antisymm (Fin.le_last k) h1)

include hπ hblk hanti in
theorem colMin {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (b : Fin (r + 1)) :
    C b (π (Fin.last r)) = if b = π (Fin.last r) then 1 else 0 := by
  obtain ⟨hdiag, hup⟩ := hC
  split_ifs with hb
  · rw [hb]
    exact hdiag _
  · by_contra h
    obtain ⟨hle, hbl⟩ := hup _ _ h
    have hlt : b < π (Fin.last r) := lt_of_le_of_ne hle hb
    have h2 := hanti b (π (Fin.last r)) hbl hlt
    rw [hπ] at h2
    exact absurd (Fin.le_last (π b)) (not_le.mpr h2)

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.RConvFExistsPf

open MeasureTheory
open scoped InnerProductSpace
open Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates

theorem convergent_reduction_exists : Formalism.L2.SG.Pf.RowDictPf.RConvFExists := by
  intro I μf _ _ hright hsc hborel fund hfund R hR f hf
  haveI := hsc
  haveI := hborel
  haveI : μf.IsMulRightInvariant := hright
  haveI : SigmaFinite (I.muA μf) := rr_muA_sigmaFinite I μf
  haveI : (I.muA μf).IsMulLeftInvariant := rr_muA_left I μf
  haveI : (I.muA μf).IsMulRightInvariant := rr_muA_right I μf
  have hfd := rr_FD_of I μf fund hfund
  have hreg := rr_IsReg_of I μf fund R hR

  have hemb : Measurable (fun g : I.Gf => ((1, g) : I.GA)) := by fun_prop
  obtain ⟨T, hT⟩ := wk_exists (μ := μf) (U := fun g => R (1, g))
    (fun g z => (rr_norm hfd hreg (1, g) z).le)
    (fun x y => ((rr_weak_meas hfd hreg x y).comp_measurable hemb).aestronglyMeasurable) hf
  exact ⟨T, hf, hT⟩

end Formalism.L2.SG.Pf.RConvFExistsPf
end
end
