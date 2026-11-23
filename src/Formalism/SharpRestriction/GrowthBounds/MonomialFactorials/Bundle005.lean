module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser
import Formalism.MahlerMeasure.MahlerMeasureProofs.FockBlocks
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle004
import Formalism.SharpRestriction.GrowthBounds.RootWeights.ValuationNonnegIffIntegral
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.ProjS

theorem goodCount_mem (p : ℕ) [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℤ_[p] Vs]
    (be : Vs → Vs → ℚ_[p]) (L : Submodule ℤ_[p] Vs) (D : ℤ) :
    ∃ x y : Fin (goodCount p be L D) → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0 := by
  set S : Set ℕ := {n | ∃ x y : Fin n → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
    ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0} with hS
  have h0 : (0 : ℕ) ∈ S := ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have hmem : sSup S ∈ S := by
    by_cases hb : BddAbove S
    · exact Nat.sSup_mem ⟨0, h0⟩ hb
    · rw [Nat.sSup_of_not_bddAbove hb]; exact h0
  exact hmem

section Lin

variable {k σ : Type} [Field k] {r : ℕ}

theorem harmonicProjection_add (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (y y' : MvPolynomial σ k) :
    tieP w e zv sv o n z (y + y') = tieP w e zv sv o n z y + tieP w e zv sv o n z y' := by
  unfold tieP
  simp only [mul_add, map_add (f := _), smul_add, Finset.sum_add_distrib]

theorem harmonicProjection_smul (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (c : k) (y : MvPolynomial σ k) :
    tieP w e zv sv o n z (c • y) = c • tieP w e zv sv o n z y := by
  unfold tieP
  simp only [mul_smul_comm, map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _

end Lin

section Block

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

theorem Pall_add (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    G.Pall p (r := r) j jp (u + v) = G.Pall p (r := r) j jp u + G.Pall p (r := r) j jp v := by
  unfold M.BlockData.Pall
  rw [← harmonicProjection_add]
  congr 1
  induction (List.finRange G.T.t) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons]; rw [ih, harmonicProjection_add]

theorem Pall_smul (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    G.Pall p (r := r) j jp (c • u) = c • G.Pall p (r := r) j jp u := by
  unfold M.BlockData.Pall
  rw [← harmonicProjection_smul]
  congr 1
  induction (List.finRange G.T.t) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons]; rw [ih, harmonicProjection_smul]

def Th (j : Fin G.T.t → ℕ) (jp : ℕ) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) : MvPolynomial (M.BVar N r G.T.t) ℚ_[p] :=
  (∏ i, G.Ehat p (r := r) i ^ j i) * G.Eplus p (r := r) ^ jp * G.Pall p (r := r) j jp u

theorem Th_add (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    Th p G j jp (u + v) = Th p G j jp u + Th p G j jp v := by
  unfold Th; rw [Pall_add, mul_add]

theorem Th_smul (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    Th p G j jp (c • u) = c • Th p G j jp u := by
  unfold Th; rw [Pall_smul, mul_smul_comm]

theorem Th_zero (j : Fin G.T.t → ℕ) (jp : ℕ) : Th p (r := r) G j jp (0 : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) = 0 := by
  have := Th_smul p (r := r) G j jp 0 0
  simpa using this

theorem zsmul_eq (c : ℤ_[p]) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) : c • u = (c : ℚ_[p]) • u :=
  (algebraMap_smul ℚ_[p] c u).symm

theorem Th_mem_PSZ (j : Fin G.T.t → ℕ) (jp : ℕ) (hl : G.LevelOK j jp) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hu : u ∈ Ljj p (r := r) G j jp) : Th p G j jp u ∈ G.PSZ p (r := r) := by
  unfold Ljj at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, g, hg, rfl⟩ := hx
    apply Submodule.subset_span
    simp only [Set.mem_iUnion]
    exact ⟨j, jp, hl, y, hy, g, hg, rfl⟩
  | zero => rw [Th_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Th_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [zsmul_eq, Th_smul, ← zsmul_eq]; exact Submodule.smul_mem _ c hx

def lvC (j : Fin G.T.t → ℕ) (jp : ℕ) : ℕ :=
  ((∏ i, (j i).factorial) * jp.factorial) ^ 2 *
    ((∏ i, (((G.lettersAt j jp).deg (G.letterAt (G.T.pos i)) +
        (G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)) + r + G.T.z i + 1 + j i - 1).choose (j i) *
      (G.T.z i).factorial)) *
    (((G.LL.deg G.uPos - jp) + (G.B - jp) + r + G.zPlus + 1 + jp - 1).choose jp * G.zPlus.factorial))

theorem Th_fock (hB : G.BlockOK) (hr : 1 ≤ r) (j : Fin G.T.t → ℕ) (jp : ℕ) (hl : G.LevelOK j jp)
    (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hu : u ∈ Ljj p (r := r) G j jp) (hv : v ∈ Ljj p (r := r) G j jp) :
    fockK (Th p G j jp u) (Th p G j jp v) = (lvC (r := r) G j jp : ℚ_[p]) * fockK u (G.phiAll p (r := r) j jp v) := by
  unfold Ljj at hu hv
  induction hu using Submodule.span_induction with
  | mem x hx =>
    induction hv using Submodule.span_induction with
    | mem x' hx' =>
      obtain ⟨y, hy, g, hg, rfl⟩ := hx
      obtain ⟨y', hy', g', hg', rfl⟩ := hx'
      have h := (fock_block_decomposition p N r G hB hr).2 j jp hl y hy.1 y' hy'.1 g hg g' hg'
      rw [fockK_smul_left, fockK_smul_right] at h
      have hf : ((∏ i, ((j i).factorial : ℚ_[p])) * (jp.factorial : ℚ_[p])) ≠ 0 :=
        mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
          (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      unfold Th lvC
      push_cast
      push_cast at h
      have hf2 : (∏ i, ((j i).factorial : ℚ_[p])) ^ 2 * (jp.factorial : ℚ_[p]) ^ 2 ≠ 0 := by
        rw [← mul_pow]; exact pow_ne_zero 2 hf
      field_simp at h
      rw [div_eq_iff hf2] at h
      rw [h]
      ring
    | zero => rw [Th_zero, fockK_zero_right, map_zero, fockK_zero_right, mul_zero]
    | add a b _ _ ha hb => rw [Th_add, fockK_add_right, ha, hb, map_add (f := _), fockK_add_right, mul_add]
    | smul c a _ ha =>
      rw [zsmul_eq, Th_smul, fockK_smul_right, ha, map_smul, fockK_smul_right]; ring
  | zero => rw [Th_zero, fockK_zero_left, fockK_zero_left, mul_zero]
  | add a b _ _ ha hb => rw [Th_add, fockK_add_left, ha, hb, fockK_add_left, mul_add]
  | smul c a _ ha => rw [zsmul_eq, Th_smul, fockK_smul_left, ha, fockK_smul_left]; ring

theorem Th_orth (hB : G.BlockOK) (hr : 1 ≤ r) (j j' : Fin G.T.t → ℕ) (jp jp' : ℕ) (hl : G.LevelOK j jp)
    (hl' : G.LevelOK j' jp') (hne : (j, jp) ≠ (j', jp'))
    (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hu : u ∈ Ljj p (r := r) G j jp) (hv : v ∈ Ljj p (r := r) G j' jp') :
    fockK (Th p G j jp u) (Th p G j' jp' v) = 0 := by
  unfold Ljj at hu hv
  induction hu using Submodule.span_induction with
  | mem x hx =>
    induction hv using Submodule.span_induction with
    | mem x' hx' =>
      obtain ⟨y, hy, g, hg, rfl⟩ := hx
      obtain ⟨y', hy', g', hg', rfl⟩ := hx'
      exact (fock_block_decomposition p N r G hB hr).1 j j' jp jp' hl hl' hne y hy.1 y' hy'.1 g hg g' hg'
    | zero => rw [Th_zero, fockK_zero_right]
    | add a b _ _ ha hb => rw [Th_add, fockK_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [zsmul_eq, Th_smul, fockK_smul_right, ha, mul_zero]
  | zero => rw [Th_zero, fockK_zero_left]
  | add a b _ _ ha hb => rw [Th_add, fockK_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [zsmul_eq, Th_smul, fockK_smul_left, ha, mul_zero]

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem depth_num (Y N s t r L CM C : ℝ) (hY : 1 ≤ Y) (hN : 1 ≤ N) (hs0 : 0 ≤ s) (hs : s ≤ N) (ht0 : 0 ≤ t)
    (ht : t ≤ s) (hr : 0 ≤ r) (hL : 0 ≤ L) (hCM : 0 ≤ CM) (hC : 18 * (1 + CM) + 20 ≤ C) :
    Y * (t * (Y * (3 * (s + 2) * r ^ 2 * L) + CM * (3 * (s + 2) * r ^ 2 * L)) + CM * (3 * (s + 2) * r ^ 2 * L)) +
      10 * (s + 1) * (r + 1) * L ≤ C * Y ^ 2 * N ^ 2 * (r + 1) ^ 2 * L := by
  have hA0 : 0 ≤ 3 * (s + 2) * r ^ 2 * L := by positivity
  have hB0 : 0 ≤ N * (r + 1) ^ 2 * L := by
    have : 0 ≤ N := by linarith
    positivity
  have hA : 3 * (s + 2) * r ^ 2 * L ≤ 9 * (N * (r + 1) ^ 2 * L) := by
    have h1 : s + 2 ≤ 3 * N := by linarith
    have h2 : r ^ 2 ≤ (r + 1) ^ 2 := by nlinarith
    have h3 : (s + 2) * r ^ 2 ≤ (3 * N) * (r + 1) ^ 2 := mul_le_mul h1 h2 (by positivity) (by linarith)
    have h4 := mul_le_mul_of_nonneg_right h3 hL
    linarith
  have htA : t * (3 * (s + 2) * r ^ 2 * L) ≤ N * (9 * (N * (r + 1) ^ 2 * L)) :=
    mul_le_mul (by linarith) hA hA0 (by linarith)
  have k1 := mul_le_mul_of_nonneg_left htA (sq_nonneg Y)
  have hYCM : 0 ≤ Y * CM := mul_nonneg (by linarith) hCM
  have k2 := mul_le_mul_of_nonneg_left htA hYCM
  have k3 := mul_le_mul_of_nonneg_left hA hYCM
  have k4 : 10 * (s + 1) * (r + 1) * L ≤ 20 * (N * (r + 1) ^ 2 * L) := by
    have h1 : s + 1 ≤ 2 * N := by linarith
    have h2 : r + 1 ≤ (r + 1) ^ 2 := by nlinarith
    have h3 : (s + 1) * (r + 1) ≤ (2 * N) * (r + 1) ^ 2 := mul_le_mul h1 h2 (by linarith) (by linarith)
    have h4 := mul_le_mul_of_nonneg_right h3 hL
    linarith
  have hY2 : Y ≤ Y ^ 2 := by nlinarith
  have h5 := mul_le_mul_of_nonneg_left hN (sq_nonneg Y)
  have hYN : Y * N ≤ Y ^ 2 * N := mul_le_mul_of_nonneg_right hY2 (by linarith)
  have hY1 : Y ≤ Y ^ 2 * N := by linarith
  have h1P : 1 ≤ Y ^ 2 * N := by nlinarith
  have hc0 : 0 ≤ CM * (9 * (N * (r + 1) ^ 2 * L)) := mul_nonneg hCM (by linarith)
  have m1 := mul_le_mul_of_nonneg_left hYN hc0
  have m2 := mul_le_mul_of_nonneg_left hY1 hc0
  have m3 := mul_le_mul_of_nonneg_left h1P (by linarith : (0:ℝ) ≤ 20 * (N * (r + 1) ^ 2 * L))
  have hP0 : 0 ≤ Y ^ 2 * N * (N * (r + 1) ^ 2 * L) := mul_nonneg (by linarith) hB0
  have m4 := mul_le_mul_of_nonneg_right (by linarith : 29 + 18 * CM ≤ C) hP0
  linarith [k1, k2, k3, k4, m1, m2, m3, m4]

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

theorem p25 (hF : HIFacts C0 X) : (25 : ℝ) ≤ (X.L.p : ℝ) := by
  have hmR : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hF.m4
  nlinarith [hF.p_ge]

theorem lgA_ge_one_facts (hF : HIFacts C0 X) : 1 ≤ lgA X.p X.L.a X.r := by
  unfold lgA
  have h : 0 ≤ Real.logb (X.p : ℝ) (8 * (X.L.a : ℝ) + X.r) := by
    unfold Real.logb
    apply div_nonneg
    · have h' := Real.log_natCast_nonneg (8 * X.L.a + X.r)
      push_cast at h'
      exact h'
    · exact Real.log_natCast_nonneg _
  linarith

theorem kap0A_nonneg_of_hiFacts (hF : HIFacts C0 X) : 0 ≤ kappaZeroExponent X.p X.L.a X.Nt X.r := by
  unfold kappaZeroExponent
  have h : 0 ≤ Real.logb (X.p : ℝ) (X.L.a : ℝ) :=
    div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  exact mul_nonneg (by positivity) h

theorem restDepth_proved {CYb Cde Ck CD Cb Cc : ℝ} (CM C : ℝ) (hCYb : 1 ≤ CYb) (hCM : 0 ≤ CM)
    (hC : 18 * (1 + CM) + 20 ≤ C) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : RestDepth C0 CE1 CE2 X CM C := by
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
  have hY : (1 : ℝ) ≤ X.L.Y := hH.1.1
  have hN : (1 : ℝ) ≤ (X.N₁ : ℝ) := by exact_mod_cast hH.1.2.2.2.2.2.1
  have hs : (X.s : ℝ) ≤ (X.N₁ : ℝ) := by exact_mod_cast (hH.1.2.2.2.2.1 X.j).2
  have ht : ((X.S C0 CE1 CE2).t : ℝ) ≤ (X.s : ℝ) := by
    have : (X.S C0 CE1 CE2).t ≤ X.s := Nat.sub_le _ _
    exact_mod_cast this
  have hL := lgA_ge_one_facts hF
  have hL0 : 0 ≤ lgA X.p X.L.a X.r := by linarith
  have hk := kap0A_nonneg_of_hiFacts hF
  constructor
  · unfold D1r kapS
    positivity
  · have h := depth_num X.L.Y X.N₁ X.s ((X.S C0 CE1 CE2).t : ℝ) X.r (lgA X.p X.L.a X.r) CM C hY hN (Nat.cast_nonneg _) hs
      (Nat.cast_nonneg _) ht (Nat.cast_nonneg _) hL0 hCM hC
    unfold D1r kapS levelPassageLoss depthD
    linarith

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestDirQ : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      ∑ x ∈ lv C0 CE1 CE2 X aTop b, rL C0 CE1 CE2 X aTop b x ≤
        Module.finrank ℚ_[X.p] (Submodule.span ℚ_[X.p]
          (((gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) :
            Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :
              Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])))

def RestDimBC : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      Module.finrank ℚ_[X.p] (Submodule.span ℚ_[X.p]
          (((gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) :
            Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :
              Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p]))) ≤
        bRank C0 CE1 CE2 X aTop aPlus b

variable {C0 CE1 CE2 X}

theorem restDir_of (hQ : RestDirQ C0 CE1 CE2 X) (hB : RestDimBC C0 CE1 CE2 X) : RestDir C0 CE1 CE2 X :=
  fun aTop hT aPlus hP b hk => (hQ aTop hT aPlus hP b hk).trans (hB aTop hT aPlus hP b hk)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

def phisB (j : Fin G.T.t → ℕ) (jp : ℕ) :
    MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
  (List.finRange G.T.t).foldr (fun i acc =>
    Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i), c))
      (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i + 1), c))
      ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)))
      (G.T.z i) ∘ₗ acc) LinearMap.id

def bePhi (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) : ℚ_[p] :=
  Formalism.GM.M.fockK (phisB p (r := r) G j jp u) v / (degFact G j jp : ℚ_[p])

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestPlusA (CM : ℝ) : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
              (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋ ≤
      bY C0 CE1 CE2 X aTop x.1 x.2 ⌊D1r C0 CE1 CE2 X CM⌋ * dXi X.r ((X.S C0 CE1 CE2).bPlus - x.2.2)

def RestRankL : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ≤ rL C0 CE1 CE2 X aTop x.1 x.2

def RestPlusB (CM : ℝ) : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    (∑ aPlus ∈ X.winA, (bLvl C0 CE1 CE2 X aTop aPlus x.1 x.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ)) ≤
      (X.winA.card : ℝ) *
        ((Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
            (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋ : ℝ) +
          5 / X.L.Y * (Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) : ℝ))

variable {C0 CE1 CE2 X}

theorem restPlus_of (CM : ℝ) (hY : 0 < X.L.Y) (hA : RestPlusA C0 CE1 CE2 X CM) (hR : RestRankL C0 CE1 CE2 X)
    (hB : RestPlusB C0 CE1 CE2 X CM) : RestPlus C0 CE1 CE2 X CM := by
  intro dl hdl aTop haTop x hx
  have hA' := hA dl hdl aTop haTop x hx
  have hR' := hR dl hdl aTop haTop x hx
  refine (hB dl hdl aTop haTop x hx).trans ?_
  refine mul_le_mul_of_nonneg_left (add_le_add (by exact_mod_cast hA') ?_) (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hR') (div_nonneg (by norm_num) hY.le)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem mem_levels_iff' {N : ℕ} (G : Formalism.GM.M.BlockData N) (x : (Fin G.T.t → ℕ) × ℕ) :
    x ∈ levels G ↔ G.LevelOK x.1 x.2 := by
  unfold levels
  simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨⟨fun i => ?_, ?_⟩, h⟩⟩
  · have hle := Finset.single_le_sum (s := Finset.univ) (f := fun a => G.LL.deg a)
      (fun a _ => Nat.zero_le _) (Finset.mem_univ (⟨min (G.T.pos i) (N - 1), by
        rcases Nat.eq_zero_or_pos N with h0 | h0
        · exact absurd G.uPos.2 (by omega)
        · omega⟩ : Fin N))
    have h1 := (h.1 i).1
    omega
  · have h2 := h.2
    have h3 := min_le_right (G.LL.deg G.uPos) G.B
    omega

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestBClvl : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b → ∀ l ∈ lv C0 CE1 CE2 X aTop b,
      Module.finrank (KK X.O) (Submodule.span (KK X.O)
        ((blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b).gens X.O (r := X.r) l.1 l.2)) ≤
      Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2)

theorem restBCdim_of (h : RestBClvl C0 CE1 CE2 X) : RestBCdim C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hk
  rw [finrank_blockLat X.O X.p X.r (Formalism.MainNotions.G.GLWeightTheory.valuation_properties_hold X.std.1.prime X.setting) (X.S C0 CE1 CE2) aTop aPlus X.m b]
  unfold blockRank
  simp only
  set D := blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b with hD
  have hU : Submodule.span (KK X.O) ((D.SSZ X.O (r := X.r) : Submodule X.O _) :
        Set (MvPolynomial (BVar (2 * X.s + 1) X.r D.T.t) (KK X.O))) ≤
      ⨆ l ∈ lv C0 CE1 CE2 X aTop b, Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2) := by
    rw [Submodule.span_le]
    intro x hx
    have hx' : x ∈ Submodule.span X.O (⋃ (j : Fin D.T.t → ℕ) (jp : ℕ) (_ : D.LevelOK j jp), D.gens X.O (r := X.r) j jp) := hx
    refine Submodule.span_induction (p := fun x _ => x ∈ ⨆ l ∈ lv C0 CE1 CE2 X aTop b,
        Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) ?_ ?_ ?_ ?_ hx'
    · intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨j, jp, hl, hy⟩ := hy
      have hmem : ((j, jp) : Lv C0 CE1 CE2 X) ∈ lv C0 CE1 CE2 X aTop b := by
        exact (mem_levels_iff' (gB C0 CE1 CE2 X aTop 0 b) (j, jp)).2 hl
      exact (le_iSup₂ (f := fun (l : Lv C0 CE1 CE2 X) (_ : l ∈ lv C0 CE1 CE2 X aTop b) =>
        Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) (j, jp) hmem) (Submodule.subset_span hy)
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      rw [algebra_compatible_smul (KK X.O) a x]
      exact Submodule.smul_mem _ _ hx
  have := span_SSZ_finite (O := X.O) (r := X.r) D
  have hfd : ∀ l ∈ lv C0 CE1 CE2 X aTop b,
      FiniteDimensional (KK X.O) (Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) := by
    intro l hl
    have hsub : Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2) ≤
        Submodule.span (KK X.O) ((D.SSZ X.O (r := X.r) : Submodule X.O _) :
          Set (MvPolynomial (BVar (2 * X.s + 1) X.r D.T.t) (KK X.O))) := by
      apply Submodule.span_mono
      intro y hy
      apply Submodule.subset_span
      refine Set.mem_iUnion.2 ⟨l.1, Set.mem_iUnion.2 ⟨l.2, Set.mem_iUnion.2 ⟨?_, hy⟩⟩⟩
      exact (mem_levels_iff' (gB C0 CE1 CE2 X aTop 0 b) l).1 hl
    exact Submodule.finiteDimensional_of_le hsub
  obtain ⟨hfd2, hle⟩ := finrank_biSup_le (fun l : Lv C0 CE1 CE2 X =>
    Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) (lv C0 CE1 CE2 X aTop b) hfd
  calc Module.finrank (KK X.O) (Submodule.span (KK X.O) ((D.SSZ X.O (r := X.r) : Submodule X.O _) :
          Set (MvPolynomial (BVar (2 * X.s + 1) X.r D.T.t) (KK X.O))))
      ≤ Module.finrank (KK X.O) (⨆ l ∈ lv C0 CE1 CE2 X aTop b,
          Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2) : Submodule (KK X.O) _) :=
        Submodule.finrank_mono hU
    _ ≤ ∑ l ∈ lv C0 CE1 CE2 X aTop b, Module.finrank (KK X.O) (Submodule.span (KK X.O) (D.gens X.O (r := X.r) l.1 l.2)) :=
        hle
    _ ≤ ∑ l ∈ lv C0 CE1 CE2 X aTop b,
          Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) :=
        Finset.sum_le_sum fun l hl => h aTop hT aPlus hP b hk l hl

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
