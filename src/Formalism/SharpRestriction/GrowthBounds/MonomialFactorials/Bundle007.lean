module

public import Formalism.SharpRestriction.GrowthBounds.CountingStatementReduction
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle006
import Formalism.MahlerMeasure.MahlerMeasureProofs.RemoveS
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

structure SegFacts (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : Prop where
  hF : HIFacts C0 X
  kP : ∀ i, ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.b'
  P1 : ∀ i, 1 ≤ (X.S C0 CE1 CE2).P X.p i
  PQ : ∀ i, (X.S C0 CE1 CE2).P X.p i ≤ (X.S C0 CE1 CE2).Qj X.p
  La4 : 4 * X.L.La C0 < (X.r : ℝ) + 1
  E0 : 0 ≤ (X.S C0 CE1 CE2).E0
  bTop : ∀ i, ((X.S C0 CE1 CE2).bTop i : ℝ) ≤ 5 / 2 * X.L.b'
  kb : ((X.r : ℝ) + 1) * X.L.b' ≤ (X.L.a : ℝ) / 4
  Y1 : 1 ≤ X.L.Y
  xa0 : 0 ≤ X.xa
  xa : X.xa ≤ 2 * X.L.J0 C0

theorem segFacts {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 2 ≤ CYb) (hCb : 1 ≤ Cb) (hCD : 0 ≤ CD) (hCE1 : 0 ≤ CE1)
    (hCE2 : 0 ≤ CE2) (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : SegFacts C0 CE1 CE2 X := by
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X (by linarith) hH
  obtain ⟨h0, -, hxa0, hxa, -, -, -, -, -, -⟩ := hH
  obtain ⟨hY, hpk, ⟨s0, hs0, -⟩, -, hseg, hN1, hm, hLa8, hb0, hbl, hbh, h12, hbw, hYb, hk2, hlog, hde, hpa, hCk,
    hband, hccl0, hccl1, hDLP, hcs, hbig⟩ := h0
  have hk : X.L.k = (X.L.m : ℝ) + 1 := rfl
  have hp25 := p25 hF
  have hp1 : 1 ≤ X.L.p := by
    have : (1 : ℝ) ≤ (X.L.p : ℝ) := by linarith
    exact_mod_cast this
  have hN : (1 : ℝ) ≤ X.L.N := by
    have : 1 ≤ X.L.TT.card := Finset.card_pos.2 ⟨s0, hs0⟩
    show (1 : ℝ) ≤ (X.L.TT.card : ℝ)
    exact_mod_cast this
  have hQ1 : (1 : ℝ) ≤ X.L.Q := by
    show (1 : ℝ) ≤ (X.L.p : ℝ) ^ X.L.G'
    exact one_le_pow₀ (by linarith)
  have hk1 : (1 : ℝ) ≤ X.L.k := by rw [hk]; have : (0 : ℝ) ≤ X.L.m := Nat.cast_nonneg _; linarith
  have hlogb : 0 ≤ Real.logb X.L.p X.L.a := Real.logb_nonneg (by linarith) hF.a1
  have hDLP0 : 0 ≤ X.L.DLP := by
    refine le_trans ?_ hDLP
    have : (0 : ℝ) ≤ (X.L.N1 : ℝ) ^ 5 + X.L.k ^ 3 := by positivity
    have : 0 ≤ X.L.N := by linarith
    positivity
  have hM : (1 : ℝ) ≤ X.L.cs + X.L.N * X.L.ccl + X.L.n' * X.L.ccl := by
    have h1 : 0 ≤ X.L.N * X.L.ccl := mul_nonneg (by linarith) hccl0
    have h2 : 0 ≤ (X.L.n' : ℝ) * X.L.ccl := mul_nonneg (Nat.cast_nonneg _) hccl0
    linarith
  have hkQ : X.L.k * X.L.Q ≤ X.L.b' := by
    refine le_trans ?_ hbig
    have e1 : X.L.k ≤ X.L.k ^ 3 := le_self_pow₀ hk1 (by norm_num)
    have e2 : X.L.Q ≤ X.L.Q ^ 4 := le_self_pow₀ hQ1 (by norm_num)
    calc X.L.k * X.L.Q = 1 * X.L.k * 1 * X.L.Q * 1 * 1 := by ring
      _ ≤ Cb * X.L.k ^ 3 * X.L.N * X.L.Q ^ 4 * (X.L.cs + X.L.N * X.L.ccl + X.L.n' * X.L.ccl) * X.L.Y := by
          gcongr
  have hPQ : ∀ i, (X.S C0 CE1 CE2).P X.p i ≤ (X.S C0 CE1 CE2).Qj X.p := fun i =>
    Nat.pow_le_pow_right (lt_of_lt_of_le zero_lt_one hp1) (Nat.sub_le _ _)
  have hQj : ((X.S C0 CE1 CE2).Qj X.p : ℝ) ≤ X.L.Q := by
    show ((X.L.p ^ segG X.L.TT X.j : ℕ) : ℝ) ≤ (X.L.p : ℝ) ^ X.L.G'
    push_cast
    exact pow_le_pow_right₀ (by exact_mod_cast hp1) (hseg X.j).1
  have hE0 : 0 ≤ (X.S C0 CE1 CE2).E0 := by
    show 0 ≤ errorTermBound CE1 CE2 X.L.p X.L.k X.L.N1 X.L.Q X.L.c X.L.a X.L.b' (X.L.La C0)
    unfold errorTermBound
    have h1 := hF.La0
    have h2 := hF.b0.le
    have h3 : (0 : ℝ) ≤ X.L.k := by linarith
    have h4 : (0 : ℝ) ≤ X.L.Q := by linarith
    positivity
  refine ⟨hF, fun i => ?_, fun i => Nat.one_le_pow _ _ (lt_of_lt_of_le zero_lt_one hp1), hPQ, ?_, hE0, fun i => ?_, ?_, hY, hxa0, hxa⟩
  · have h1 : ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.Q :=
      le_trans (by exact_mod_cast hPQ i) hQj
    have h2 : X.L.k * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ X.L.b' :=
      le_trans (mul_le_mul_of_nonneg_left h1 (by linarith)) hkQ
    exact h2
  · have hYb2 : 2 ≤ X.L.Yb := le_trans hCYb hYb
    have : 4 * X.L.La C0 ≤ 2 * X.L.Yb * X.L.N * X.L.La C0 := by
      have h0 := hF.La0
      have hYN : 2 ≤ X.L.Yb * X.L.N := by nlinarith only [hYb2, hN]
      have := mul_le_mul_of_nonneg_right hYN h0
      linarith only [this]
    have h2 : 4 * X.L.La C0 < X.L.k := by linarith
    exact h2
  · exact hF.bT_le _ (segPos_mem X.L.TT X.j i)
  · have h1 := hF.b_lt
    have h2 : ((X.r : ℝ) + 1) ^ 2 ≤ (X.L.p : ℝ) := hF.p_ge
    have hm4 : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hF.m4
    have hb := hF.b0
    have h4 : 4 * ((X.L.m : ℝ) + 1) ≤ (X.L.p : ℝ) := by nlinarith only [h2, hm4]
    have h5 := mul_le_mul_of_nonneg_right h4 hb.le
    have h3 : ((X.L.m : ℝ) + 1) * X.L.b' ≤ (X.L.a : ℝ) / 4 := by linarith only [h5, h1]
    exact h3

section Coarse

variable (hS : SegFacts C0 CE1 CE2 X)
include hS

theorem coarseC_lower (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (hD : DigitsOK X.p (X.S C0 CE1 CE2) aTop b)
    (i : Fin X.s) :
    (aTop i : ℝ) - ((X.r : ℝ) + 1) * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤
      (coarseC X.p (X.S C0 CE1 CE2) aTop b i : ℝ) * ((X.S C0 CE1 CE2).P X.p i : ℝ) := by
  set P := (X.S C0 CE1 CE2).P X.p i
  have hP : 1 ≤ P := hS.P1 i
  obtain ⟨h1, -, h3⟩ := hD
  obtain ⟨hle, hdvd⟩ := h3 i
  have e : coarseC X.p (X.S C0 CE1 CE2) aTop b i * P = aTop i - ∑ c, b.ry i c := Nat.div_mul_cancel hdvd
  have hρ : ∑ c, b.ry i c ≤ (X.r + 1) * P := by
    calc ∑ c, b.ry i c ≤ ∑ _c : Fin (X.r + 1), P := Finset.sum_le_sum fun c _ => (h1 i c).2.le
      _ = (X.r + 1) * P := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have e2 : ((coarseC X.p (X.S C0 CE1 CE2) aTop b i : ℕ) : ℝ) * (P : ℝ) = (aTop i : ℝ) - ((∑ c, b.ry i c : ℕ) : ℝ) := by
    rw [← Nat.cast_mul, e, Nat.cast_sub hle]
  rw [e2]
  have : ((∑ c, b.ry i c : ℕ) : ℝ) ≤ ((X.r : ℝ) + 1) * (P : ℝ) := by exact_mod_cast hρ
  linarith

theorem coarseA_upper (b : SegBlock X.s X.r) (i : Fin X.s) :
    (coarseA X.p (X.S C0 CE1 CE2) b i : ℝ) * ((X.S C0 CE1 CE2).P X.p i : ℝ) ≤ 5 / 2 * X.L.b' := by
  have h1 : coarseA X.p (X.S C0 CE1 CE2) b i * (X.S C0 CE1 CE2).P X.p i ≤ (X.S C0 CE1 CE2).bTop i :=
    (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
  have h2 : ((coarseA X.p (X.S C0 CE1 CE2) b i * (X.S C0 CE1 CE2).P X.p i : ℕ) : ℝ) ≤ ((X.S C0 CE1 CE2).bTop i : ℝ) := by
    exact_mod_cast h1
  push_cast at h2
  exact h2.trans (hS.bTop i)

theorem win_ge (aTop : Fin X.s → ℕ) (hT : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (i : Fin X.s) :
    (X.L.a : ℝ) ≤ aTop i := by
  have := (Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hT i)).1
  exact_mod_cast this

end Coarse

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Gens

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {ι : ℚ_[p] →+* KK O} {N r : ℕ} [NeZero r]

theorem map_Ehat (D : BlockData N) (i : Fin (gmB D).T.t) :
    map ι ((gmB D).Ehat p (r := r) i) = D.Ehat O (r := r) i := by
  unfold Formalism.GM.M.BlockData.Ehat Formalism.MainNotions.G.BlockData.Ehat

  simp only [map_add (f := _), map_mul, map_X, map_sum]
  rfl

theorem map_Eplus (D : BlockData N) :
    map ι ((gmB D).Eplus p (r := r)) = D.Eplus O (r := r) := by
  unfold Formalism.GM.M.BlockData.Eplus Formalism.MainNotions.G.BlockData.Eplus

  simp only [map_add (f := _), map_mul, map_X, map_sum]
  rfl

theorem map_gens (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y) (D : BlockData N)
    (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (Formalism.GM.M.BVar N r (gmB D).T.t) ℚ_[p])
    (hx : x ∈ (gmB D).gens p (r := r) j jp) : map ι x ∈ D.gens O (r := r) j jp := by
  obtain ⟨y, hy, g, hg, rfl⟩ := hx
  refine ⟨map ι y, map_YZ hint (D.lettersAt j jp) D.T.J D.T.thr y hy, map ι g, map_XiPolZ hint g hg, ?_⟩
  simp only [map_mul, map_prod, map_pow, map_X, map_Ehat, map_Eplus, map_rename]
  rfl

theorem map_smul_Q {σ : Type} (c : ℚ_[p]) (x : MvPolynomial σ ℚ_[p]) : map ι (c • x) = ι c • map ι x := by
  rw [smul_eq_C_mul, map_mul, map_C, smul_eq_C_mul]

theorem map_SSZ (hint : ∀ x : ℤ_[p], ∃ y : O, ι (x : ℚ_[p]) = algebraMap O (KK O) y) (D : BlockData N)
    (x : MvPolynomial (Formalism.GM.M.BVar N r (gmB D).T.t) ℚ_[p]) (hx : x ∈ (gmB D).SSZ p (r := r)) :
    map ι x ∈ Submodule.span (KK O) (D.SSZ O (r := r) : Set (MvPolynomial (BVar N r D.T.t) (KK O))) := by
  unfold Formalism.GM.M.BlockData.SSZ at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, hok, hx⟩ := hx
    have hm : MvPolynomial.map ι x ∈ D.gens O (r := r) j jp := map_gens hint D j jp x hx
    exact Submodule.subset_span (Submodule.subset_span
      (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hok, hm⟩⟩⟩))
  | zero =>
    rw [map_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add (f := _)]
    exact add_mem ha hb
  | smul a x _ hx =>
    rw [← algebraMap_smul ℚ_[p] a x, map_smul_Q]
    exact Submodule.smul_mem _ _ hx

abbrev intMap (σ : Type) : MvPolynomial σ ℤ_[p] →ₐ[ℤ_[p]] MvPolynomial σ ℚ_[p] :=
  MvPolynomial.mapAlgHom (Algebra.ofId ℤ_[p] ℚ_[p])

theorem mem_intPol_iff {σ : Type} (F : MvPolynomial σ ℚ_[p]) :
    F ∈ Formalism.GM.M.IntPol p σ ↔ F ∈ (intMap (p := p) σ).range := Iff.rfl

private theorem X_mem_intMap {σ : Type} (v : σ) :
    (X v : MvPolynomial σ ℚ_[p]) ∈ (intMap (p := p) σ).range :=
  ⟨X v, by simp⟩

theorem gens_int (D : Formalism.GM.M.BlockData N) (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (Formalism.GM.M.BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ D.gens p (r := r) j jp) : x ∈ Formalism.GM.M.IntPol p (Formalism.GM.M.BVar N r D.T.t) := by
  obtain ⟨y, hy, g, hg, rfl⟩ := hx
  rw [mem_intPol_iff]
  rw [Formalism.GM.M.YZ] at hy
  rw [Formalism.GM.M.XiPolZ] at hg
  have h1 : y ∈ Formalism.GM.M.PolZ p r (D.lettersAt j jp) := (Submodule.mem_inf.1 hy).2
  rw [Formalism.GM.M.PolZ] at h1
  have h2 : y ∈ Formalism.GM.M.IntPol p (Fin N × Fin r) := (Submodule.mem_inf.1 h1).2
  have hE : ∀ i, D.Ehat p (r := r) i ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range := by
    intro i
    unfold Formalism.GM.M.BlockData.Ehat
    exact add_mem (mul_mem (X_mem_intMap _) (X_mem_intMap _))
      (sum_mem fun c _ => mul_mem (X_mem_intMap _) (X_mem_intMap _))
  have hP : D.Eplus p (r := r) ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range := by
    unfold Formalism.GM.M.BlockData.Eplus
    exact add_mem (mul_mem (X_mem_intMap _) (X_mem_intMap _))
      (sum_mem fun c _ => mul_mem (X_mem_intMap _) (X_mem_intMap _))
  have hy' : rename (Formalism.GM.M.chainEmb N r D.T.t) y ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range := by
    obtain ⟨G, rfl⟩ := (mem_intPol_iff y).1 h2
    exact ⟨rename (Formalism.GM.M.chainEmb N r D.T.t) G, by simp [map_rename]⟩
  have hg' : g ∈ (intMap (p := p) (Formalism.GM.M.BVar N r D.T.t)).range :=
    (mem_intPol_iff g).1 (Submodule.mem_inf.1 hg).2
  refine mul_mem (mul_mem (mul_mem ?_ (pow_mem (X_mem_intMap _) _)) hy') hg'
  exact mul_mem (mul_mem (prod_mem fun i _ => pow_mem (hE i) _) (pow_mem hP _))
    (prod_mem fun i _ => pow_mem (X_mem_intMap _) _)

theorem SSZ_int (D : Formalism.GM.M.BlockData N) (x : MvPolynomial (Formalism.GM.M.BVar N r D.T.t) ℚ_[p])
    (hx : x ∈ D.SSZ p (r := r)) : x ∈ Formalism.GM.M.IntPol p (Formalism.GM.M.BVar N r D.T.t) := by
  unfold Formalism.GM.M.BlockData.SSZ at hx
  refine (Submodule.span_le.2 ?_) hx
  intro z hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨j, jp, -, hz⟩ := hz
  exact gens_int D j jp z hz

end Gens

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.ProjS

theorem exists_scal (p : ℕ) [hp : Fact p.Prime] (m Mx : ℕ) (hm : m ≠ 0) (h : padicValNat p m ≤ Mx) :
    ∃ c : ℤ_[p], (c : ℚ_[p]) * (m : ℚ_[p]) = (p : ℚ_[p]) ^ Mx := by
  have hm' : (m : ℚ_[p]) ≠ 0 := by exact_mod_cast hm
  have hn : ‖(m : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p m : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hm', Padic.valuation_natCast, Nat.padicValNat_def]
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  refine ⟨Padic.lift ((p : ℚ_[p]) ^ Mx / m) ?_, ?_⟩
  · rw [norm_div, norm_pow, Padic.norm_p, hn, div_le_one (zpow_pos hp0 _), inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ hp1 (by omega)
  · show (p : ℚ_[p]) ^ Mx / m * m = _
    field_simp

section Block

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

def expU (a : ℕ) : ℕ := (G.T.t + 1) * ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊

def expM : ℕ := (levels G).sup fun l => padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2)

theorem lvC_ne_zero (j : Fin G.T.t → ℕ) (jp : ℕ) : lvC (r := r) G j jp ≠ 0 := by
  unfold lvC
  refine mul_ne_zero (pow_ne_zero 2 (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _)
    (Nat.factorial_ne_zero _))) (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero ?_
      (Nat.factorial_ne_zero _)) (mul_ne_zero ?_ (Nat.factorial_ne_zero _)))
  · exact (Nat.choose_pos (by omega)).ne'
  · exact (Nat.choose_pos (by omega)).ne'

theorem degFact_ne_zero (j : Fin G.T.t → ℕ) (jp : ℕ) : degFact G j jp ≠ 0 := by
  unfold degFact
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)

def nLv (D : ℤ) (l : (Fin G.T.t → ℕ) × ℕ) : ℕ :=
  goodCount p (bejj p (r := r) G l.1 l.2) (Ljj p (r := r) G l.1 l.2) D

theorem nLv_mem (D : ℤ) (l : (Fin G.T.t → ℕ) × ℕ) :
    ∃ x y : Fin (nLv p (r := r) G D l) → MvPolynomial (M.BVar N r G.T.t) ℚ_[p],
      (∀ i, x i ∈ Ljj p (r := r) G l.1 l.2) ∧ (∀ i, y i ∈ Ljj p (r := r) G l.1 l.2) ∧
      ∀ i j, fockK (G.phiAll p (r := r) l.1 l.2 (x i)) (y j) =
        (if i = j then (p : ℚ_[p]) ^ D else 0) * (degFact G l.1 l.2 : ℚ_[p]) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := goodCount_mem p (bejj p (r := r) G l.1 l.2) (Ljj p (r := r) G l.1 l.2) D
  refine ⟨x, y, hx, hy, fun i j => ?_⟩
  have hd : (degFact G l.1 l.2 : ℚ_[p]) ≠ 0 := by exact_mod_cast degFact_ne_zero G _ _
  have h := hxy i j
  unfold bejj at h
  rw [div_eq_iff hd] at h
  exact h

theorem blkZ_gen (hB : G.BlockOK) (hr : 1 ≤ r) (U Mx : ℕ)
    (hLL : ∀ x ∈ G.PSZ p (r := r), ((p : ℚ_[p]) ^ U) • x ∈ G.SSZ p (r := r))
    (hM : ∀ l ∈ levels G, padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2) ≤ Mx) (D : ℤ) :
    ∃ (n : ℕ) (x y : Fin n → MvPolynomial (M.BVar N r G.T.t) ℚ_[p]),
      (∀ i, x i ∈ G.SSZ p (r := r)) ∧ (∀ i, y i ∈ G.SSZ p (r := r)) ∧
      (∀ i j, fockK (x i) (y j) =
        if i = j then (p : ℚ_[p]) ^ (D + 2 * (U : ℤ) + (Mx : ℤ)) else 0) ∧
      ∑ l ∈ levels G, Module.finrank ℤ_[p] (Ljj p (r := r) G l.1 l.2) ≤
        n + ∑ l ∈ levels G, badLvl p (r := r) G l.1 l.2 D := by
  classical
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hw := fun l : (Fin G.T.t → ℕ) × ℕ => nLv_mem p (r := r) G D l
  choose u v hu hv huv using hw
  have hsc : ∀ l : ↥(levels G), ∃ c : ℤ_[p],
      (c : ℚ_[p]) * ((lvC (r := r) G l.1.1 l.1.2 * degFact G l.1.1 l.1.2 : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ Mx := by
    intro l
    exact exists_scal p _ Mx (mul_ne_zero (lvC_ne_zero G _ _) (degFact_ne_zero G _ _)) (hM l.1 l.2)
  choose sc hsc' using hsc
  have hok : ∀ l : ↥(levels G), G.LevelOK l.1.1 l.1.2 := fun l => (Finset.mem_filter.1 l.2).2
  let I := Σ l : ↥(levels G), Fin (nLv p (r := r) G D l.1)
  let Xf : I → MvPolynomial (M.BVar N r G.T.t) ℚ_[p] := fun a => ((p : ℚ_[p]) ^ U) • Th p G a.1.1.1 a.1.1.2 (v a.1.1 a.2)
  let Yf : I → MvPolynomial (M.BVar N r G.T.t) ℚ_[p] := fun a =>
    sc a.1 • (((p : ℚ_[p]) ^ U) • Th p G a.1.1.1 a.1.1.2 (u a.1.1 a.2))
  have hX : ∀ a, Xf a ∈ G.SSZ p (r := r) := fun a => hLL _ (Th_mem_PSZ p G _ _ (hok a.1) _ (hv _ _))
  have hY : ∀ a, Yf a ∈ G.SSZ p (r := r) := fun a =>
    Submodule.smul_mem _ _ (hLL _ (Th_mem_PSZ p G _ _ (hok a.1) _ (hu _ _)))
  have hXY : ∀ a b : I, fockK (Xf a) (Yf b) = if a = b then (p : ℚ_[p]) ^ (D + 2 * (U : ℤ) + (Mx : ℤ)) else 0 := by
    rintro ⟨l, i⟩ ⟨l', k⟩
    simp only [Xf, Yf]
    rw [zsmul_eq, fockK_smul_left, fockK_smul_right, fockK_smul_right]
    by_cases hll : l = l'
    · subst hll
      rw [Th_fock p G hB hr _ _ (hok l) _ _ (hv _ _) (hu _ _), fockK_symm]
      have h1 := huv l.1 k i
      have h2 := hsc' l
      push_cast at h2
      by_cases hik : i = k
      · subst hik
        rw [if_pos rfl] at h1
        rw [h1, if_pos rfl]
        rw [zpow_add₀ hp0, zpow_add₀ hp0, zpow_natCast, ← h2, two_mul, zpow_add₀ hp0, zpow_natCast]
        ring
      · rw [if_neg (fun h => hik h.symm)] at h1
        rw [h1, if_neg]
        · ring
        · intro h
          rw [Sigma.mk.inj_iff] at h
          exact hik (eq_of_heq h.2)
    · have hne : (l.1.1, l.1.2) ≠ (l'.1.1, l'.1.2) := by
        intro h
        exact hll (Subtype.ext h)
      rw [Th_orth p G hB hr _ _ _ _ (hok l) (hok l') hne _ _ (hv _ _) (hu _ _), if_neg]
      · ring
      · intro h
        rw [Sigma.mk.inj_iff] at h
        exact hll h.1
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, fun i => Xf (e.symm i), fun i => Yf (e.symm i), fun i => hX _, fun i => hY _, ?_, ?_⟩
  · intro i j
    rw [hXY]
    simp only [e.symm.injective.eq_iff]
  · have hc : Fintype.card I = ∑ l ∈ levels G, nLv p (r := r) G D l := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      exact Finset.sum_coe_sort (levels G) (nLv p (r := r) G D)
    rw [hc, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun l _ => ?_
    unfold badLvl bad nLv
    exact le_add_tsub

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestLvlDim : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b → ∀ x ∈ lv C0 CE1 CE2 X aTop b,
      rL C0 CE1 CE2 X aTop b x ≤
        Module.finrank ℚ_[X.p] (Submodule.span ℚ_[X.p] ((gB C0 CE1 CE2 X aTop aPlus b).gens X.p (r := X.r) x.1 x.2))

def RestSumSpan : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      ∑ x ∈ lv C0 CE1 CE2 X aTop b,
          Module.finrank ℚ_[X.p] (Submodule.span ℚ_[X.p] ((gB C0 CE1 CE2 X aTop aPlus b).gens X.p (r := X.r) x.1 x.2)) ≤
        Module.finrank ℚ_[X.p] (Submodule.span ℚ_[X.p]
          (((gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) :
            Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :
              Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])))

variable {C0 CE1 CE2 X}

theorem restDirQ_of (h1 : RestLvlDim C0 CE1 CE2 X) (h2 : RestSumSpan C0 CE1 CE2 X) : RestDirQ C0 CE1 CE2 X :=
  fun aTop hT aPlus hP b hk =>
    (Finset.sum_le_sum fun x hx => h1 aTop hT aPlus hP b hk x hx).trans (h2 aTop hT aPlus hP b hk)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
