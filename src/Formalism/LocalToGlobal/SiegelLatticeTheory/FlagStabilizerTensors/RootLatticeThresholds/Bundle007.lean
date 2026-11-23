module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZ
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZPlane
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle006
public import Formalism.SharpRestriction.ParConsts
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

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

def kap (x : Fin N → ℂ) : Fin (r + 1) ⊕ Fin (r + 1) → ℂ :=
  ((Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G)⁻¹ *ᵥ (((Wfg F G)ᴴ * Formalism.REAL.Jm ε) *ᵥ x)

include hFF hGG hπ hZ hgap in
theorem kap_eq (x : Fin N → ℂ) :
    Matrix.fromBlocks (lastDiag (-(T : ℂ))) (Zm ε F G) (Zm ε F G)ᴴ (lastDiag (-(T' : ℂ))) *ᵥ kap ε F G x =
      Sum.elim (fun a => hJ ε (F a) x) (fun b => hJ ε (G b) x) := by
  rw [← gram_eq ε F G T T' π hFF hGG hπ hZ, kap, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (gram_unit ε F G T T' π hFF hGG hπ hZ hgap), Matrix.one_mulVec, wjx]

theorem Yc_sub (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (x : Fin N → ℂ) :
    Yc ε F G C *ᵥ x - x = ∑ a, ((Am ε F G C - 1) *ᵥ (kap ε F G x ∘ Sum.inl)) a • F a +
      ∑ b, ((C - 1) *ᵥ (kap ε F G x ∘ Sum.inr)) b • G b := by
  unfold Yc
  rw [Ymat_sub, Wfg_mulVec]
  unfold Mm
  rw [Matrix.fromBlocks_mulVec]
  simp [kap]

include hπ hZ in
theorem monoZ_mulVec (v : Fin (r + 1) → ℂ) (a : Fin (r + 1)) : (Zm ε F G *ᵥ v) a = Zm ε F G a (π a) * v (π a) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π a)]
  · intro j _ hj
    have : Zm ε F G a j = 0 := by by_contra h; exact hj (by rw [(hZ a j).1 h, hπ])
    rw [this, zero_mul]
  · simp

include hπ hZ in
theorem monoZh_mulVec (v : Fin (r + 1) → ℂ) (b : Fin (r + 1)) :
    ((Zm ε F G)ᴴ *ᵥ v) b = starRingEnd ℂ (Zm ε F G (π b) b) * v (π b) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π b)]
  · simp [Matrix.conjTranspose_apply]
  · intro j _ hj
    have : Zm ε F G j b = 0 := by by_contra h; exact hj ((hZ j b).1 h)
    simp [Matrix.conjTranspose_apply, this]
  · simp

include hFF hGG hπ hblk hanti hZ hgap in
theorem Yc_perpF {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (x : Fin N → ℂ)
    (hx : ∀ a, a ≠ Fin.last r → hJ ε (F a) x = 0) :
    Yc ε F G C *ᵥ x - x ∈ Submodule.span ℂ (F '' {a | a ≠ Fin.last r}) := by
  have hk := kap_eq ε F G T T' π hFF hGG hπ hZ hgap x
  rw [Matrix.fromBlocks_mulVec] at hk
  set κ := kap ε F G x
  have hG0 : ∀ j, j ≠ π (Fin.last r) → κ (Sum.inr j) = 0 := by
    intro j hj
    have ha : π j ≠ Fin.last r := fun h => hj (by rw [← h, hπ])
    have h1 := congrFun hk (Sum.inl (π j))
    simp only [Sum.elim_inl, Pi.add_apply] at h1
    rw [hx _ ha, lastDiag_mulVec, Pi.single_apply, if_neg ha, zero_add, monoZ_mulVec ε F G π hπ hZ, hπ] at h1
    have hz : Zm ε F G (π j) j ≠ 0 := (hZ _ _).2 rfl
    exact (mul_eq_zero.1 h1).resolve_left hz
  rw [Yc_sub]
  have h2 : ∑ b, ((C - 1) *ᵥ (κ ∘ Sum.inr)) b • G b = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    have : ((C - 1) *ᵥ (κ ∘ Sum.inr)) b = 0 := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π (Fin.last r))]
      · rw [Matrix.sub_apply, colMin π blk hπ hblk hanti hC, Matrix.one_apply]
        split_ifs <;> simp
      · intro j _ hj; simp [hG0 j hj]
      · simp
    rw [this, zero_smul]
  rw [h2, add_zero]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : a = Fin.last r
  · subst ha
    have : ((Am ε F G C - 1) *ᵥ (κ ∘ Sum.inl)) (Fin.last r) = 0 := by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hA : IsUB blk (Am ε F G C) := isUB_A π hπ hblk hanti _ hZ hC
      rw [Matrix.sub_apply, rowLast blk hA, Matrix.one_apply]
      by_cases hk : k = Fin.last r
      · subst hk; simp
      · simp [hk, Ne.symm hk]
    rw [this, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)

include hFF hGG hπ hblk hanti hZ hgap in
theorem Yc_perpG {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) (x : Fin N → ℂ)
    (hx : ∀ b, b ≠ Fin.last r → hJ ε (G b) x = 0) :
    Yc ε F G C *ᵥ x - x ∈ Submodule.span ℂ (G '' {b | b ≠ Fin.last r}) := by
  have hk := kap_eq ε F G T T' π hFF hGG hπ hZ hgap x
  rw [Matrix.fromBlocks_mulVec] at hk
  set κ := kap ε F G x
  have hF0 : ∀ i, i ≠ π (Fin.last r) → κ (Sum.inl i) = 0 := by
    intro i hi
    have hb : π i ≠ Fin.last r := fun h => hi (by rw [← h, hπ])
    have h1 := congrFun hk (Sum.inr (π i))
    simp only [Sum.elim_inr, Pi.add_apply] at h1
    rw [hx _ hb, lastDiag_mulVec, Pi.single_apply, if_neg hb, add_zero, monoZh_mulVec ε F G π hπ hZ, hπ] at h1
    have hz : starRingEnd ℂ (Zm ε F G i (π i)) ≠ 0 := by
      rw [map_ne_zero]; exact (hZ _ _).2 (hπ i).symm
    exact (mul_eq_zero.1 h1).resolve_left hz
  rw [Yc_sub]
  have hA : IsUB blk (Am ε F G C) := isUB_A π hπ hblk hanti _ hZ hC
  have h2 : ∑ a, ((Am ε F G C - 1) *ᵥ (κ ∘ Sum.inl)) a • F a = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    have : ((Am ε F G C - 1) *ᵥ (κ ∘ Sum.inl)) a = 0 := by
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (π (Fin.last r))]
      · rw [Matrix.sub_apply, colMin π blk hπ hblk hanti hA, Matrix.one_apply]
        split_ifs <;> simp
      · intro j _ hj; simp [hF0 j hj]
      · simp
    rw [this, zero_smul]
  rw [h2, zero_add]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : b = Fin.last r
  · subst hb
    have : ((C - 1) *ᵥ (κ ∘ Sum.inr)) (Fin.last r) = 0 := by
      rw [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Matrix.sub_apply, rowLast blk hC, Matrix.one_apply]
      by_cases hk : k = Fin.last r
      · subst hk; simp
      · simp [hk, Ne.symm hk]
    rw [this, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

section

namespace Formalism.L2.SG.Pf.LatDictZ

theorem anisotropic_vector_orbit : LatDictZ.ZOrbit :=
  zOrbit_of_open Z2.primitive_plane_local Z5.adelic_gluing

end Formalism.L2.SG.Pf.LatDictZ
end

section

noncomputable section

namespace Formalism.MainNotions

theorem raise_lt {eps : ℝ} {Fm : FamP eps} {y x : ℝ} (h : max Fm.x1 y < x) : Fm.x1 < x :=
  lt_of_le_of_lt (le_max_left _ _) h

def FamP.raise {eps : ℝ} (Fm : FamP eps) (y : ℝ) : FamP eps :=
  { Fm with
    x1 := max Fm.x1 y
    one_lt_family_threshold := lt_of_lt_of_le Fm.one_lt_family_threshold (le_max_left _ _)
    L_x := fun x i h => Fm.L_x x i (raise_lt h)
    o_le_Co := fun x i h => Fm.o_le_Co x i (raise_lt h)
    QS_le_Co := fun x i h => Fm.QS_le_Co x i (raise_lt h)
    bTop_eq := fun x h => Fm.bTop_eq x (raise_lt h)
    bTop_ge := fun x h => Fm.bTop_ge x (raise_lt h)
    bT_le := fun x h => Fm.bT_le x (raise_lt h)
    coverS := fun x h => Fm.coverS x (raise_lt h)
    params := fun x h => Fm.params x (raise_lt h)
    params_K := fun x h => Fm.params_K x (raise_lt h)
    parT := fun x h => Fm.parT x (raise_lt h)
    parT_K := fun x h => Fm.parT_K x (raise_lt h)
    sizes := fun x h => Fm.sizes x (raise_lt h)
    supp_sat := fun x h => Fm.supp_sat x (raise_lt h)
    tw_supp := fun x h => Fm.tw_supp x (raise_lt h)
    fills := fun x h => Fm.fills x (raise_lt h)
    lats0 := fun x h => Fm.lats0 x (raise_lt h)
    latTied := fun x h => Fm.latTied x (raise_lt h)
    nuDef := fun x h => Fm.nuDef x (raise_lt h)
    nprimeDef := fun x h => Fm.nprimeDef x (raise_lt h)
    rrDef := fun x h => Fm.rrDef x (raise_lt h)
    h_eq := fun x h => Fm.h_eq x (raise_lt h)
    ex := fun x h => Fm.ex x (raise_lt h)
    rho_le := fun x h => Fm.rho_le x (raise_lt h)
    drop_iff := fun x h => Fm.drop_iff x (raise_lt h)
    fixed := ⟨Fm.fixed.1, Fm.fixed.2.1, Fm.fixed.2.2.1, Fm.fixed.2.2.2.1, Fm.fixed.2.2.2.2.1, Fm.fixed.2.2.2.2.2.1,
      Fm.fixed.2.2.2.2.2.2.1, fun x h => Fm.fixed.2.2.2.2.2.2.2 x (raise_lt h)⟩ }

end Formalism.MainNotions
end
end
