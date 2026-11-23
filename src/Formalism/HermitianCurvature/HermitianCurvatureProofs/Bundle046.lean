module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle057
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
public import Formalism.HermitianCurvature.Bundle007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle044
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle037
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle043
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem hpk_mulVec (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ x) i = if i.val < r ∨ r + k < i.val then x ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -x i else x i := by
  rw [mulVec, dotProduct]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · have : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1 := by
        unfold Hpk
        rcases h with h | h
        · rw [if_pos ⟨h, by simp; omega⟩]
        · rw [if_neg (by simp; omega), if_pos ⟨by simp; omega, by simp; omega⟩]
      rw [this, one_mul]
    · intro j _ hj
      have : Hpk k r i j = 0 := by
        unfold Hpk
        have hj' : j.val ≠ 2 * r + k - i.val := fun e => hj (Fin.ext (by simpa using e))
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [this, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · rw [if_neg h, Finset.sum_eq_single i]
    · unfold Hpk
      rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩]
      split_ifs <;> ring
    · intro j _ hj
      have : Hpk k r i j = 0 := by
        unfold Hpk
        rw [if_neg (by omega), if_neg (by omega), if_neg (fun e => hj e.2.2.symm)]
      rw [this, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'

theorem hpk_symm' : (Hpk k r)ᵀ = Hpk k r := by
  apply GlobalTheory.DualFRep.gram_transpose <;> assumption

theorem hpk_conjT : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply, ← transpose_apply (Hpk k r) j i, hpk_symm']
  unfold Hpk
  split_ifs <;> simp

theorem herm_eq (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = ∑ i, star (y i) * (Hpk k r *ᵥ x) i := rfl

theorem herm_add_left (x x' y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (x + x') y = herm (Hpk k r) x y + herm (Hpk k r) x' y := by
  simp only [herm, mulVec_add, dotProduct_add]

theorem herm_smul_left (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (c • x) y = c * herm (Hpk k r) x y := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_sub_left (x x' y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (x - x') y = herm (Hpk k r) x y - herm (Hpk k r) x' y := by
  simp only [herm, mulVec_sub, dotProduct_sub]

theorem herm_add_right (x y y' : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (y + y') = herm (Hpk k r) x y + herm (Hpk k r) x y' := by
  simp only [herm, star_add, add_dotProduct]

theorem herm_smul_right (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x (c • y) = star c * herm (Hpk k r) x y := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

theorem herm_zero_left (y : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) 0 y = 0 := by
  simp [herm]

theorem herm_zero_right (x : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) x 0 = 0 := by
  simp [herm]

theorem herm_swap (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) x y = star (herm (Hpk k r) y x) := by
  simp only [herm]
  rw [star_dotProduct, star_mulVec, hpk_conjT, dotProduct_mulVec]

theorem herm_skew {ξ : B.Mat k r} (hξ : B.inLie k r ξ) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (ξ *ᵥ x) y = -herm (Hpk k r) x (ξ *ᵥ y) := by
  have h : ξᴴ * Hpk k r = -(Hpk k r * ξ) := eq_neg_of_add_eq_zero_left hξ
  simp only [herm]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h, neg_mulVec, dotProduct_neg, neg_neg]

theorem trace_xuv (ξ : B.Mat k r) (u v : Fin (2 * r + k + 1) → ℂ) :
    Matrix.trace (ξ * Xuv k r u v) = herm (Hpk k r) (ξ *ᵥ u) v - herm (Hpk k r) (ξ *ᵥ v) u := by
  have key : ∀ a b : Fin (2 * r + k + 1) → ℂ,
      Matrix.trace (ξ * vecMulVec a (star (Hpk k r *ᵥ b))) = herm (Hpk k r) (ξ *ᵥ a) b := by
    intro a b
    have hb : star (Hpk k r *ᵥ b) = star b ᵥ* Hpk k r := by
      rw [star_mulVec, hpk_conjT]
    rw [hb, herm, dotProduct_mulVec]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [Xuv, Matrix.mul_sub, Matrix.trace_sub, key, key]

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
end

section

namespace Formalism.FourierDecayAlt.P.GermFibreKernels

open Formalism.FourierDecayAlt NumberField

noncomputable section

def fs (r : ℕ) (g : ℝ) (b s : ℕ) (t : ℂ) : ℂ :=
  (((g / (2 * Real.pi)) ^ S6.nuBlock (r : ℤ) (b : ℤ) (s : ℤ) : ℝ) : ℂ) * Complex.I ^ (s - 1) * t

theorem toStd_append' (r : ℕ) (g : ℝ) : ∀ (P Q : C.LPt) (b : ℕ),
    D.toStd r g b (P ++ Q) = D.toStd r g b P ++ D.toStd r g (b + D.ptSize P) Q
  | [], Q, b => by simp [D.toStd, D.ptSize]
  | (s, t) :: rest, Q, b => by
    have ih := toStd_append' r g rest Q (b + s)
    simp only [List.cons_append, D.toStd, ih, D.ptSize, List.map_cons, List.sum_cons, add_assoc]

theorem toStd_germPts (r : ℕ) (g : ℝ) (h : C.LPt) (s : ℕ) (t c z : ℂ) :
    D.toStd r g 1 (h ++ [(s - 1, t), (1, c)]) =
      D.toStd r g 1 h ++ [(s - 1, fs r g (1 + D.ptSize h) (s - 1) t), (1, fs r g (1 + D.ptSize h + (s - 1)) 1 c)] ∧
    D.toStd r g 1 (h ++ [(s, z)]) = D.toStd r g 1 h ++ [(s, fs r g (1 + D.ptSize h) s z)] := by
  constructor
  · rw [toStd_append']
    simp [D.toStd, fs]
  · rw [toStd_append']
    simp [D.toStd, fs]

theorem roots_std (r : ℕ) (g : ℝ) (hg : 0 < g) (b s : ℕ) (hs : 2 ≤ s) (t c z : ℂ) :
    fs r g b s z ^ s = (-1) ^ (s + 1) * (fs r g (b + (s - 1)) 1 c * fs r g b (s - 1) t ^ (s - 1)) ↔
      z ^ s = c * t ^ (s - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 1 - 1 = m := by omega
  simp only [e1]
  unfold fs
  simp only [e1, e2, Nat.sub_self, pow_zero, mul_one]
  set q := g / (2 * Real.pi) with hq
  have hq0 : q ≠ 0 := (div_pos hg (by positivity)).ne'
  set L3 := ((q ^ S6.nuBlock (r : ℤ) (b : ℤ) ((m + 2 : ℕ) : ℤ) : ℝ) : ℂ) with hL3d
  set L2 := ((q ^ S6.nuBlock (r : ℤ) ((b + (m + 1) : ℕ) : ℤ) ((1 : ℕ) : ℤ) : ℝ) : ℂ) with hL2d
  set L1 := ((q ^ S6.nuBlock (r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) : ℂ) with hL1d
  have hL : L3 ^ (m + 2) = L2 * L1 ^ (m + 1) := by
    rw [hL3d, hL2d, hL1d, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hq0]
    congr 1
    unfold S6.nuBlock
    push_cast; ring
  have hI : (Complex.I ^ (m + 1)) ^ (m + 2) = (-1) ^ (m + 2 + 1) * (Complex.I ^ m) ^ (m + 1) := by
    rw [← pow_mul, ← pow_mul]
    have : (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1) := by ring
    rw [this, pow_add, pow_mul Complex.I 2, Complex.I_sq]
    have h3 : (-1 : ℂ) ^ (m + 2 + 1) = (-1) ^ (m + 1) := by
      rw [show m + 2 + 1 = (m + 1) + 2 by ring, pow_add]; norm_num
    rw [h3]; ring
  have hL3 : L3 ≠ 0 := Complex.ofReal_ne_zero.mpr (zpow_ne_zero _ hq0)
  set K := L3 ^ (m + 2) * (Complex.I ^ (m + 1)) ^ (m + 2) with hK
  have eL : (L3 * Complex.I ^ (m + 1) * z) ^ (m + 2) = K * z ^ (m + 2) := by rw [hK]; ring
  have eR : (-1) ^ (m + 2 + 1) * (L2 * c * (L1 * Complex.I ^ m * t) ^ (m + 1)) = K * (c * t ^ (m + 1)) := by
    rw [hK, hI, hL]; ring
  rw [eL, eR]
  have h0 : K ≠ 0 := mul_ne_zero (pow_ne_zero _ hL3) (pow_ne_zero _ (pow_ne_zero _ Complex.I_ne_zero))
  exact mul_right_inj' h0

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

theorem betaU_eq : U.betaU = 2 * Complex.I := by
  simp [U.betaU, Formalism.QuantumDeterminants.cStd]

theorem char_std (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < (S.g : ℝ)) (b s : ℕ) (hs : 2 ≤ s) (t z : ℂ) (ht : t ≠ 0) :
    G.psi U.betaU ((s : ℂ) * fs S.G.r (S.g : ℝ) b s z / fs S.G.r (S.g : ℝ) b (s - 1) t) =
      KB.psiL S (-((s : ℂ) * t⁻¹)) z := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 2 := ⟨s - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 1 - 1 = m := by omega
  rw [← GermRealisation.psi_neg_betaL]
  unfold fs
  simp only [e1, e2]
  set q := (S.g : ℝ) / (2 * Real.pi) with hq
  have hq0 : 0 < q := div_pos hg (by positivity)
  have hL : q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 2 : ℕ) : ℤ) =
      q⁻¹ * q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) := by
    rw [← zpow_neg_one, ← zpow_add₀ hq0.ne']
    congr 1
    unfold S6.nuBlock; push_cast; ring
  have hL1 : (q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) ≠ 0 := (zpow_pos hq0 _).ne'
  rw [hL]
  unfold G.psi
  congr 3
  rw [betaU_eq]
  unfold GermRealisation.betaL
  have hL1' : ((q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [Complex.ofReal_mul, Complex.ofReal_inv]
  generalize ((q ^ S6.nuBlock (S.G.r : ℤ) (b : ℤ) ((m + 1 : ℕ) : ℤ) : ℝ) : ℂ) = L at hL1' ⊢
  congr 1
  rw [hq]
  push_cast
  rw [pow_succ]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

end loc

end

end Formalism.FourierDecayAlt.P.GermFibreKernels
end

section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt

noncomputable section

def ptG (h' : C.LPt) (m : ℕ) : (ℂ × ℂ) ⊕ ℂ → C.LPt
  | Sum.inl q => h' ++ [(m + 1, q.1), (1, q.2)]
  | Sum.inr z => h' ++ [(m + 2, z)]

def yG {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ) (Φ : G.Mat (m + 2) → V) :
    (ℂ × ℂ) ⊕ ℂ → V
  | Sum.inl q => ((kapB m : ℝ) : ℂ) • G.OmBlock β (m + 1) Φ q.1 q.2
  | Sum.inr z => ((Real.pi ^ ((m + 2) * (m + 1) / 2) : ℝ) : ℂ) • G.OmLong β (m + 1) Φ z

def okG (m : ℕ) (Kc : Set ℂ) : (ℂ × ℂ) ⊕ ℂ → Prop
  | Sum.inl q => q.1 ≠ 0 ∧ q.2 * q.1 ^ (m + 1) ∈ Kc
  | Sum.inr z => ∃ D ∈ Kc, z ^ (m + 2) = (-1) ^ (m + 3) * D

theorem ptSize_ptG (h' : C.LPt) (m : ℕ) (q : (ℂ × ℂ) ⊕ ℂ) : D.ptSize (ptG h' m q) = D.ptSize h' + (m + 2) := by
  cases q <;> simp [ptG, D.ptSize, List.map_append, List.sum_append] <;> omega

def GermPlace : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (sg : ℂ) (w : List C.Letter) (f : B.Mat P0.k P0.r → (Wq →L[ℂ] Wp))
    (χ : ℝ → ℝ) (ε : ℝ) (h' : C.LPt) (m i : ℕ) (hi : i ≤ P0.r) (hsz : D.ptSize h' + (m + 2) = i),
    B.CkOn ⊤ (B.GV P0.k P0.r) f → (∃ R : ℝ, ∀ g ∈ B.GV P0.k P0.r, f g ≠ 0 → B.gN g ≤ R) → C6.IsCut0 χ →
    0 < ε → 2 ≤ P0.k → D.IsLocPt h' (D.ptSize h') →
    ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc →
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℂ V) (_ : CompleteSpace V)
      (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (Φ : G.Mat (m + 2) → V) (Cp Cst : ℝ),
      0 ≤ Cp ∧ (∀ u, (Bf u u).re ≤ (Cp * ‖u‖) ^ 2) ∧
      (∀ q1 q2, okG m Kc q1 → okG m Kc q2 →
        D.formLev T sg ⟨i, by omega⟩ w
          (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q1) (by rw [ptSize_ptG, hsz]))
          (KB.slv T (D.cutF T.base χ f ε) i hi w (ptG h' m q2) (by rw [ptSize_ptG, hsz])) =
        Bf (yG U.betaU m Φ q1) (yG U.betaU m Φ q2)) ∧
      ∀ t D : ℂ, t ≠ 0 → D ∈ Kc →
        ‖U.uD U.betaU m (U.Mlev P0.k (P0.r - i)) Φ t D - U.aD U.betaU m (U.Mlev P0.k (P0.r - i)) Φ t D‖ ≤
          Cst * ‖t‖

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

section

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

def phiG (Y : Finset H) (κ : H → H → ℂ) (K : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) : ℂ :=
  if Good x ∧ Good x' then phi Y κ K x x' else 0

def phiRG (Y : Finset H) (κ : H → H → ℂ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) : ℂ :=
  if Good x ∧ Good x' then phiR Y κ U P Q x x' else 0

theorem phiG_split (Y : Finset H) (κ : H → H → ℂ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ) (x x' : crystallineComparison.V f) :
    phiG Y κ U x x' = phiRG Y κ U P Q x x' + phiG Y κ P x x' + conj (phiG Y κ P x' x) - phiG Y κ Q x x' := by
  unfold phiG phiRG phiR
  by_cases hx : Good x
  · by_cases hx' : Good x'
    · simp only [hx, hx', and_self, if_true]
      ring
    · simp [hx, hx']
  · simp [hx]

theorem phiRG_psd (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (U P Q : Fin f → H × ℂ → H × ℂ → ℂ)
    (hblk : ∀ v (Xs : Finset ℂ), (∀ x ∈ Xs, x ≠ 0) → KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) (U v) (P v) (Q v))
    (T : Finset (crystallineComparison.V f)) : TB.PSDOn T (phiRG Y κ U P Q) := by
  classical
  set T' := T.filter (fun x => Good x) with hT'
  have hXs : ∀ v, ∀ z ∈ T'.image (fun x => x v), z ≠ 0 := by
    intro v z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hx).2 v
  let kv : Fin f → (H × ℂ ⊕ H × ℂ) → (H × ℂ ⊕ H × ℂ) → ℂ := fun v a b => match a, b with
    | .inl p, .inl q => U v p q
    | .inl p, .inr q => P v p q
    | .inr q, .inl p => conj (P v p q)
    | .inr p, .inr q => Q v p q
  have hMv : ∀ v, (Matrix.of fun a b : ((Y ×ˢ T'.image (fun x => x v)).disjSum
      (Y ×ˢ T'.image (fun x => x v))) => kv v a b).PosSemidef := by
    intro v
    have h := hblk v _ (hXs v)
    unfold KB.BlockPSD TB.PSDOn at h
    convert h using 1
    ext a b
    rcases a with ⟨a | a, ha⟩ <;> rcases b with ⟨b | b, hb⟩ <;> rfl
  let pt : Fin f → (T' × Y) × Bool → (H × ℂ ⊕ H × ℂ) := fun v i =>
    if i.2 then Sum.inl (i.1.2.1, i.1.1.1 v) else Sum.inr (i.1.2.1, i.1.1.1 v)
  have hpt : ∀ v i, pt v i ∈ (Y ×ˢ T'.image (fun x => x v)).disjSum (Y ×ˢ T'.image (fun x => x v)) := by
    intro v i
    have hm : (i.1.2.1, i.1.1.1 v) ∈ Y ×ˢ T'.image (fun x => x v) :=
      Finset.mem_product.mpr ⟨i.1.2.2, Finset.mem_image_of_mem _ i.1.1.2⟩
    by_cases hs : i.2
    · simp only [pt, hs, if_true]; exact Finset.inl_mem_disjSum.mpr hm
    · simp only [pt, hs]; exact Finset.inr_mem_disjSum.mpr hm
  let L : Matrix ((T' × Y) × Bool) ((T' × Y) × Bool) ℂ := fun i j =>
    κ i.1.2.1 j.1.2.1 * ∏ v, kv v (pt v i) (pt v j)
  have hL : L.PosSemidef := by
    have hk : (Matrix.of fun i j : (T' × Y) × Bool => κ i.1.2.1 j.1.2.1).PosSemidef := by
      have := hκ.submatrix (fun i : (T' × Y) × Bool => i.1.2)
      convert this using 1
      ext i j
      simp
    have hprod : ∀ s : Finset (Fin f), (Matrix.of fun i j : (T' × Y) × Bool =>
        κ i.1.2.1 j.1.2.1 * ∏ v ∈ s, kv v (pt v i) (pt v j)).PosSemidef := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hk
      | insert a s ha ih =>
        have hA := (hMv a).submatrix (fun i : (T' × Y) × Bool => (⟨pt a i, hpt a i⟩ :
          ((Y ×ˢ T'.image (fun x => x a)).disjSum (Y ×ˢ T'.image (fun x => x a)))))
        have hh := hA.hadamard ih
        have key : (Matrix.of fun i j : (T' × Y) × Bool =>
            κ i.1.2.1 j.1.2.1 * ∏ v ∈ insert a s, kv v (pt v i) (pt v j)) =
            ((Matrix.of fun a' b' : ((Y ×ˢ T'.image (fun x => x a)).disjSum
              (Y ×ˢ T'.image (fun x => x a))) => kv a a' b').submatrix
              (fun i => (⟨pt a i, hpt a i⟩ : ((Y ×ˢ T'.image (fun x => x a)).disjSum
                (Y ×ˢ T'.image (fun x => x a)))))
              (fun i => (⟨pt a i, hpt a i⟩ : ((Y ×ˢ T'.image (fun x => x a)).disjSum
                (Y ×ˢ T'.image (fun x => x a)))))).hadamard
            (Matrix.of fun i j : (T' × Y) × Bool => κ i.1.2.1 j.1.2.1 * ∏ v ∈ s, kv v (pt v i) (pt v j)) := by
          ext i j
          simp only [Matrix.hadamard_apply, Matrix.submatrix_apply, Matrix.of_apply, Finset.prod_insert ha]
          ring
        rw [key]
        exact hh
    exact hprod Finset.univ
  let sg : Bool → ℂ := fun s => if s then 1 else -1
  let R : Matrix ((T' × Y) × Bool) T ℂ := fun i x => if i.1.1.1 = x.1 then sg i.2 else 0
  have hR0 : ∀ x : T, ¬ Good x.1 → ∀ i, R i x = 0 := by
    intro x hx i
    have : i.1.1.1 ≠ x.1 := by
      intro he
      exact hx (he ▸ (Finset.mem_filter.mp i.1.1.2).2)
    simp [R, this]
  have hcol : ∀ x : T, ∀ hx : Good x.1, ∀ g : (T' × Y) × Bool → ℂ,
      ∑ i, R i x * g i = ∑ h : Y, (g ((⟨x.1, Finset.mem_filter.mpr ⟨x.2, hx⟩⟩, h), true)
        - g ((⟨x.1, Finset.mem_filter.mpr ⟨x.2, hx⟩⟩, h), false)) := by
    intro x hx g
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    rw [Fintype.sum_eq_single (⟨x.1, Finset.mem_filter.mpr ⟨x.2, hx⟩⟩ : T')]
    · refine Finset.sum_congr rfl fun h _ => ?_
      simp [R, sg, Fintype.sum_bool]
      ring
    · intro a ha
      have : a.1 ≠ x.1 := fun he => ha (Subtype.ext he)
      simp [R, this]
  have hstar : ∀ i x, star (R i x) = R i x := by
    intro i x
    simp only [R, sg]
    split_ifs <;> simp
  have hconjP : ∀ x y : crystallineComparison.V f, conj (phi Y κ P y x) =
      ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, conj (P v (h', y v) (h, x v)) := by
    intro x y
    unfold phi

    simp only [map_sum, map_mul, map_prod]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun h' hh' => ?_
    congr 1
    have := hκ.1.apply ⟨h, hh⟩ ⟨h', hh'⟩
    simpa using this
  unfold TB.PSDOn
  have hfin := hL.conjTranspose_mul_mul_same R
  rw [Matrix.mul_assoc] at hfin
  convert hfin using 1
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hstar, Matrix.of_apply]
  by_cases hx : Good x.1
  · by_cases hy : Good y.1
    · rw [hcol x hx]
      simp only [mul_comm (L _ _) (R _ y), hcol y hy]
      simp only [phiRG, phiR, hx, hy, and_self, if_true, hconjP]
      unfold phi
      simp only [← Finset.sum_coe_sort Y]
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
      simp only [L, pt, kv, if_true, Bool.false_eq_true, if_false]
      ring
    · have : ∀ j, R j y = 0 := hR0 y hy
      simp [this, phiRG, hy]
  · have : ∀ i, R i x = 0 := hR0 x hx
    simp [this, phiRG, hx]

theorem phi_bound (Y : Finset H) (κ : H → H → ℂ) (K : Fin f → H × ℂ → H × ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (x x' : crystallineComparison.V f) (hK : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ‖K v (h, x v) (h', x' v)‖ ≤ B) :
    ‖phi Y κ K x x'‖ ≤ (∑ h ∈ Y, ∑ h' ∈ Y, ‖κ h h'‖) * B ^ f := by
  unfold phi
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h hh => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun h' hh' => ?_)
  rw [norm_mul, norm_prod]
  gcongr
  calc ∏ v, ‖K v (h, x v) (h', x' v)‖ ≤ ∏ _v : Fin f, B :=
        Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) (fun v _ => hK v h hh h' hh')
    _ = B ^ f := by simp

end

end Formalism.FourierDecayAlt.P.PBC
end
