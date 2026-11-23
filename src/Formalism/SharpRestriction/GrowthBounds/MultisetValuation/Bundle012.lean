module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle010
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StmtNumEOf
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle009
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle011
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] {X : Sys p}

theorem nm_pinv_of_eO (Y : Pend X) (he : 0 < X.eO) : (p : Y.Kc)⁻¹ ∉ Y.Oc := by
  intro hmem
  have hinj := algebraMap_inj Y he
  have hpO : (p : X.G.O) ≠ 0 := fun h0 =>
    pow_ne_zero _ X.unif.ne_zero (X.eO_spec.eq_zero_iff.mp h0)
  have hpK : (p : X.G.Kf) ≠ 0 := by
    have := (map_ne_zero_iff _ hinj).mpr hpO
    rwa [map_natCast] at this
  have h1 : algebraMap X.G.Kf Y.Kc ((p : X.G.Kf)⁻¹) ∈ Y.Oc := by
    rwa [map_inv₀, map_natCast]
  obtain ⟨a, ha⟩ := (mem_intK (X := X)).mp ((Y.Oc_K _).mp h1)

  have h1eq : (p : X.G.O) * a = 1 := hinj (by
    rw [map_mul, ha, map_natCast, mul_inv_cancel₀ hpK, map_one])
  have hpu : IsUnit (p : X.G.O) := IsUnit.of_mul_eq_one _ h1eq
  exact X.unif.not_isUnit
    ((isUnit_pow_iff (Nat.pos_iff_ne_zero.mp he)).mp (X.eO_spec.isUnit_iff.mp hpu))

theorem nm_pinv_of_place (Y : Pend X) (v : X.Pl) : (p : Y.Kc)⁻¹ ∉ Y.Oc :=
  nm_pinv_of_eO Y (eO_pos X v)

theorem nm_hyp (Y : Pend X) (h : (p : Y.Kc)⁻¹ ∉ Y.Oc) : nm_Hyp Y.Oc p :=
  ⟨hp.out.one_lt, Y.Oc_val, Y.Oc_rank1, h⟩

theorem nm_ext (Y : Pend X) (h : (p : Y.Kc)⁻¹ ∉ Y.Oc) :
    ∃ (K' : Type) (_ : NormedField K') (_ : Algebra Y.Kc K'), IsUltrametricDist K' ∧ IsAlgClosed K' ∧
      ‖(p : K')‖ = (p : ℝ)⁻¹ ∧ (∀ x : Y.Kc, ‖algebraMap Y.Kc K' x‖ ≤ 1 ↔ x ∈ Y.Oc) ∧
      ∃ vp : K', vp ^ (p ^ 2 - 1) = (p : K') := by
  have hH := nm_hyp Y h
  have hc : 1 < nm_abs hH ((p : Y.Kc)⁻¹) := by
    rw [map_inv₀]
    show 1 < (nm_N Y.Oc p (p : Y.Kc))⁻¹
    rw [nm_N_p hH, inv_inv]
    exact nm_pR hH
  obtain ⟨K', i1, i2, hu, hac, hn⟩ :=
    nm_extG (nm_abs hH) (fun x y => nm_N_add hH x y) ((p : Y.Kc)⁻¹) hc
  refine ⟨K', i1, i2, hu, hac, ?_, ?_, ?_⟩
  · have := hn (p : Y.Kc)
    rw [map_natCast] at this
    exact this.trans (nm_N_p hH)
  · intro x
    rw [hn x]
    exact nm_N_le_one hH x
  · have h2 : 2 ≤ p := hp.out.two_le
    have hpos : 0 < p ^ 2 - 1 := by
      have : 4 ≤ p ^ 2 := by nlinarith
      omega
    exact IsAlgClosed.exists_pow_nat_eq (p : K') hpos

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

theorem tsum_rat_tail (g : ℕ → ℚ) (hs : Summable (fun e => (g e : ℝ))) (E N : ℕ) (Q : ℚ) (hQ1 : 1 < Q)
    (h4 : ∀ e, E ≤ e → g (e + N) = g e / Q) : ∃ q : ℚ, ∑' e, (g e : ℝ) = q := by
  have hsE : Summable (fun i => (g (i + E) : ℝ)) := (summable_nat_add_iff E).2 hs
  have h1 := hsE.sum_add_tsum_nat_add N
  have h2 : ∀ i, (g (i + N + E) : ℝ) = (g (i + E) : ℝ) / Q := by
    intro i
    rw [show i + N + E = i + E + N by omega, h4 (i + E) (by omega)]
    push_cast
    try rfl
  simp only [h2] at h1
  rw [tsum_div_const] at h1
  have h0 := hs.sum_add_tsum_nat_add E
  have hQ0 : (Q : ℝ) ≠ 0 := by
    have : (1 : ℝ) < Q := by exact_mod_cast hQ1
    linarith
  have hQ1' : (Q : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Q := by exact_mod_cast hQ1
    linarith
  have hT : ∑' i, (g (i + E) : ℝ) = (∑ i ∈ range N, (g (i + E) : ℝ)) * Q / (Q - 1) := by
    rw [eq_div_iff hQ1']
    field_simp at h1
    linarith
  refine ⟨∑ i ∈ range E, g i + (∑ i ∈ range N, g (i + E)) * Q / (Q - 1), ?_⟩
  rw [← h0, hT]
  push_cast
  ring

def fqT (P : ℕ) (α : ℤ) (c : ℕ → ℤ) (Ds : Finset ℕ) (e : ℕ) : ℚ :=
  if 2 * e + 1 ∈ Ds then 0 else max ((α : ℚ) / (P : ℚ) ^ (2 * e + 1) - (c e : ℚ)) 0

theorem fqT_cast (P : ℕ) (α : ℤ) (c : ℕ → ℤ) (Ds : Finset ℕ) (e : ℕ) :
    (if 2 * e + 1 ∈ Ds then (0 : ℝ) else max ((α : ℝ) / (P : ℝ) ^ (2 * e + 1) - (c e : ℝ)) 0) =
      (fqT P α c Ds e : ℝ) := by
  unfold fqT
  split_ifs
  · simp
  · push_cast
    try rfl

theorem tsum_rat (P N : ℕ) (hP : 2 ≤ P) (hN : 0 < N) (α : ℤ) (c : ℕ → ℤ) (hc : ∀ e, c (e + N) = c e)
    (Ds : Finset ℕ) :
    ∃ q : ℚ, ∑' e : ℕ, (if 2 * e + 1 ∈ Ds then (0 : ℝ) else
      max ((α : ℝ) / (P : ℝ) ^ (2 * e + 1) - (c e : ℝ)) 0) = q := by
  simp_rw [fqT_cast]
  by_cases hs : Summable (fun e => (fqT P α c Ds e : ℝ))
  swap
  · exact ⟨0, by rw [tsum_eq_zero_of_not_summable hs]; simp⟩
  have hP0 : (0 : ℚ) < P := by exact_mod_cast (by omega : 0 < P)
  have h1 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → 2 * e + 1 ∉ Ds := fun e he hmem => by
    have := Finset.le_sup (f := id) hmem
    simp only [id] at this
    omega
  have h2 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → |(α : ℚ)| * 2 < (P : ℚ) ^ (2 * e + 1) := by
    intro e he
    have a1 : α.natAbs * 2 < P ^ (2 * e + 1) :=
      calc α.natAbs * 2 < 2 * e + 1 := by omega
        _ < 2 ^ (2 * e + 1) := Nat.lt_two_pow_self
        _ ≤ P ^ (2 * e + 1) := Nat.pow_le_pow_left hP _
    have a2 : ((α.natAbs : ℕ) : ℚ) = |(α : ℚ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← a2]
    exact_mod_cast a1
  have h2' : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → |(α : ℚ) / (P : ℚ) ^ (2 * e + 1)| < 1 / 2 := by
    intro e he
    have hpos : (0 : ℚ) < (P : ℚ) ^ (2 * e + 1) := pow_pos hP0 _
    rw [abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
    linarith [h2 e he]
  have hcK : ∀ k e, c (e + k * N) = c e := by
    intro k
    induction k with
    | zero => intro e; simp
    | succ k ih => intro e; rw [Nat.succ_mul, ← add_assoc, hc, ih]
  have h3 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → 0 ≤ c e := by
    intro e0 he0
    by_contra hneg
    have hneg : c e0 ≤ -1 := by omega
    have tend := hs.tendsto_atTop_zero
    obtain ⟨M, hM⟩ := (tend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists_forall_of_atTop
    have hge : M ≤ e0 + M * N := by nlinarith
    have hlt : (fqT P α c Ds (e0 + M * N) : ℝ) < 1 / 2 := hM _ hge
    have hlt' : fqT P α c Ds (e0 + M * N) < 1 / 2 := by
      have : (fqT P α c Ds (e0 + M * N) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by push_cast; exact hlt
      exact Rat.cast_lt.1 this
    have hE1 : Ds.sup id + α.natAbs + 1 ≤ e0 + M * N := le_trans he0 (Nat.le_add_right _ _)
    unfold fqT at hlt'
    rw [if_neg (h1 _ hE1), hcK] at hlt'
    have b1 := abs_lt.1 (h2' _ hE1)
    have b2 : ((c e0 : ℤ) : ℚ) ≤ -1 := by exact_mod_cast hneg
    have b3 := le_max_left ((α : ℚ) / (P : ℚ) ^ (2 * (e0 + M * N) + 1) - (c e0 : ℚ)) 0
    linarith [b1.1]
  have h4 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e →
      fqT P α c Ds (e + N) = fqT P α c Ds e / (P : ℚ) ^ (2 * N) := by
    intro e he
    have he' : Ds.sup id + α.natAbs + 1 ≤ e + N := le_trans he (Nat.le_add_right _ _)
    unfold fqT
    rw [if_neg (h1 _ he), if_neg (h1 _ he'), hc]
    have hQ : (0 : ℚ) < (P : ℚ) ^ (2 * N) := pow_pos hP0 _
    rcases (h3 e he).eq_or_lt with h0 | h0
    · rw [← h0]
      simp only [Int.cast_zero, sub_zero]
      have : (α : ℚ) / (P : ℚ) ^ (2 * (e + N) + 1) = (α : ℚ) / (P : ℚ) ^ (2 * e + 1) / (P : ℚ) ^ (2 * N) := by
        rw [div_div, ← pow_add]
        congr 2
        ring
      rw [this, ← max_div_div_right hQ.le, zero_div]
    · have b2 : (1 : ℚ) ≤ ((c e : ℤ) : ℚ) := by exact_mod_cast h0
      have c1 := abs_lt.1 (h2' _ he)
      have c2 := abs_lt.1 (h2' _ he')
      rw [max_eq_right (by linarith [c2.2]), max_eq_right (by linarith [c1.2]), zero_div]
  have hQ1 : (1 : ℚ) < (P : ℚ) ^ (2 * N) := by
    have : (1 : ℚ) < P := by exact_mod_cast (by omega : 1 < P)
    exact one_lt_pow₀ this (by omega)
  exact tsum_rat_tail _ hs _ N _ hQ1 h4

theorem gA_rat {n' k1 : ℕ} (p t : ℕ) (hp : 2 ≤ p) (hn : 0 < n') (TT : Finset (Fin n'))
    (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) : ∃ q : ℚ, gA p t TT lam0 w j = q := by
  have h1 : ∀ s : Fin n', ∃ q : ℚ, ∑' e : ℕ,
      (if 2 * e + 1 ∈ dSet TT s then (0 : ℝ) else
        max ((al TT lam0 s : ℝ) / (p : ℝ) ^ (2 * e + 1) - (cap t TT lam0 w j (posAdd s (2 * e + 1)) : ℝ)) 0) = q := by
    intro s
    apply tsum_rat p n' hp hn (al TT lam0 s) (fun e => cap t TT lam0 w j (posAdd s (2 * e + 1))) _ (dSet TT s)
    intro e
    have : posAdd s (2 * (e + n') + 1) = posAdd s (2 * e + 1) := by
      unfold posAdd
      apply Fin.ext
      show (s.val + (2 * (e + n') + 1)) % n' = (s.val + (2 * e + 1)) % n'
      have : s.val + (2 * (e + n') + 1) = s.val + (2 * e + 1) + 2 * n' := by ring
      rw [this, Nat.add_mul_mod_self_right]
    simp only [this]
  choose q hq using h1
  refine ⟨∑ s ∈ TT, q s - (∑ s : Fin n', ((NN k1 t j : ℚ) * lgp p (al TT lam0 s) +
      (NN k1 t (j - 1) : ℚ) * (NN k1 t j : ℚ) * lgp p (lsz t TT lam0 w j s)) +
    ∑ s ∈ TT, ((lgp p (al TT lam0 s) : ℚ)) ^ 2), ?_⟩
  unfold gA de
  simp only [hq]
  push_cast
  ring

theorem restRat {p : ℕ} [Fact p.Prime] (X : Sys p) : RatCondition X := by
  intro v j
  have h := X.std v
  exact gA_rat p X.t (by have := h.five_le; omega) (by have := h.two_le; omega) _ _ _ j

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def PIvS (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ) :=
  ∏ s : Fin (X.G.P.n' v), ∏ c ∈ range (X.nuv v (j + 1) s 1).toNat,
    (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^ (X.colExp j I i0 v s c) * X.colFac j I v s c

theorem PI_eq_prod (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) : X.PI j I i0 = ∏ v, PIvS X j I i0 v := rfl

theorem PIvS_congr (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    PIvS X j I i0 v = PIvS X j I (fun _ => i0 v) v := rfl

theorem colExp_zero (j : ℕ) (I : X.ColCh j) (v : X.Pl) (s : Fin (X.G.P.n' v)) (c : ℕ) :
    X.colExp j I (fun _ => 0) v s c = 0 := by
  unfold Sys.colExp
  split_ifs <;> simp

theorem PIvS_zero (j : ℕ) (I : X.ColCh j) (v : X.Pl) : PIvS X j I (fun _ => 0) v = X.PIv j I v := by
  unfold PIvS Sys.PIv
  simp only [colExp_zero, pow_zero, one_mul]

def LowAtI (j : ℕ) (v : X.Pl) (i : ℕ) (g : ℝ) : Prop :=
  ∀ U : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc, IntR Y.Oc (inParamK p Y.Kc U) →
    ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      Y.geC (AddMonoidAlgebra.coeff (applyD (PIvS X j I (fun _ => i) v)
        (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)) * U))) n) g

variable {X Y}

theorem lowAtI_zero {j : ℕ} {v : X.Pl} {g : ℝ} : LowAtI X Y j v 0 g ↔ Y.LowAt j v g := by
  unfold LowAtI Pend.LowAt
  simp only [PIvS_zero]

theorem LowAtI.mono {j : ℕ} {v : X.Pl} {i : ℕ} {g g' : ℝ} (h : g' ≤ g) (hg : LowAtI X Y j v i g) :
    LowAtI X Y j v i g' :=
  fun U hU I n => Y.geC_mono h (hg U hU I n)

variable (X Y)

def PlacewiseLowerBoundEvenShift (D : Formalism.BasicNotions.D7) : Prop :=
  admitted D X Y → ∀ v, ∀ j < X.mm, Y.LowAt j v (X.gv v (j + 1) - X.alEven v)

def RestBU (D : Formalism.BasicNotions.D7) : Prop :=
  admitted D X Y → ∀ v, ∀ j < X.mm, ∀ i ∈ Icc 1 X.G.P.r, LowAtI X Y j v i (X.gv v (j + 1))

def EntryBoundOfHypotheses (D : Formalism.BasicNotions.D7) : Prop := admitted D X Y → VolumeRatio₂ D X Y

def RestPlaces (D : Formalism.BasicNotions.D7) : Prop :=
  admitted D X Y → ∀ j < X.mm, ∀ (i0 : X.Pl → ℕ) (gP : X.Pl → ℚ), (∀ v, LowAtI X Y j v (i0 v) (gP v)) →
    EntB X Y j i0 (∑ v, (gP v : ℝ))

variable {X Y}

theorem auxU_of_firstTheoremPlaceBound (D : Formalism.BasicNotions.D7) (h : EntryBoundOfHypotheses X Y D) (hA : admitted D X Y) : VolumeRatio₂ D X Y := h hA

theorem restEnt_of_rest (D : Formalism.BasicNotions.D7) (hP : RestPlaces X Y D) (h2 : PlacewiseLowerBoundEvenShift X Y D) (hB : RestBU X Y D)
    (hA : admitted D X Y) : EntCondition X Y := by
  intro j hj i0 gP hPl
  refine hP hA j hj i0 gP fun v => ?_
  rcases hPl v with ⟨h0, h1 | h1⟩ | ⟨h0, h1, h3⟩
  · rw [h0]; exact lowAtI_zero.2 h1
  · rw [h0]; exact lowAtI_zero.2 (Pend.LowAt.mono Y h1 (h2 hA v j hj))
  · exact LowAtI.mono h3 (hB hA v j hj (i0 v) (Finset.mem_Icc.2 ⟨h0, h1⟩))

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

theorem sSA_const (K' : Type) [Field K'] (j : ℕ) (v : X.Pl) (e : Fin (X.G.P.n' v)) (a : Fin (NN X.G.P.m X.t j))
    (b : Fin (NN X.G.P.m X.t (j + 1))) : MvPowerSeries.constantCoeff (X.sSA K' j v e a b) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ l ∈ range ((0 : X.ZA j →₀ ℕ).degree + 1),
    if (0 : X.ZA j →₀ ℕ) = Finsupp.single (⟨v, (posSub e (2 * l), a, b)⟩ : X.ZA j) (p ^ (2 * l))
      then ((-1 : K') ^ l) else 0) = 0
  refine Finset.sum_eq_zero fun l _ => if_neg fun h => ?_
  exact pow_ne_zero (2 * l) hp.out.ne_zero (Finsupp.single_eq_zero.1 h.symm)

theorem hhA_const (K' : Type) [Field K'] (j : ℕ) (v : X.Pl) (u : Fin (X.G.P.n' v) → K') :
    MvPowerSeries.constantCoeff (X.hhA K' j v u) = 0 := by
  unfold Sys.hhA

  simp only [map_sum, map_mul, sSA_const, mul_zero, Finset.sum_const_zero]

theorem coordZA_const (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    MvPowerSeries.constantCoeff (X.coordZA K' j x) = 0 := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;>

  simp only [Sys.coordZA, map_sum, map_mul, MvPowerSeries.constantCoeff_X, mul_zero, Finset.sum_const_zero]

theorem ThZA_mul (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (f g : MvPowerSeries (X.EA j ⊕ X.EA j) K') :
    X.ThZA K' j (f * g) = X.ThZA K' j f * X.ThZA K' j g :=
  MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZA_const X K' j)) f g

theorem all_places_of_restrictions (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y)
    (hE : RestSExpA X) (hI : RestSIntA X) : ExpansionsMultiply D X Y := by
  intro j hj La La' h1 h2 φ K' _ _ _ _ R' vp hvp hRp hR1
  obtain ⟨Ph, U, hTh, hU, _, hbe, hPh⟩ := hA.2.2.1 j hj La La' h1 h2 φ
  obtain ⟨u, hu, V, hV, hEq⟩ := hE (hA.1 p) Y.be hbe j Ph hPh Y.Kc K' vp hvp
  refine ⟨u, fun v s => hRp (hu v s), fun h' hh' => ?_⟩
  choose h0' G hG hGE using hh'
  have hW := hI j Y.Kc Y.Oc U hU K' R' vp hvp hRp hR1
  have hc : ∀ k : ℕ, (vp ^ (p + 1)) ^ k * ((k.factorial : K'))⁻¹ ∈ R' := fun k => hRp (piFact p K' vp hvp k)
  have e1 : atPi vp (MvPowerSeries.map (algebraMap Y.Kc K') (X.ThZA Y.Kc j (Y.ThA j La La' φ))) =
      (∏ v, expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * h' v))) *
        ((∏ v, expK (MvPowerSeries.C (vp ^ (p + 1)) * G v)) * V *
          atPi vp (MvPowerSeries.map (algebraMap Y.Kc K') (X.ThZA Y.Kc j U))) := by
    rw [hTh, ThZA_mul, map_mul, atPi_mul, hEq,
      Finset.prod_congr rfl fun v _ => exp_change K' (vp ^ (p + 1)) (X.hhA K' j v (u v)) (h' v) (G v)
        (hhA_const X K' j v (u v)) (h0' v) (hGE v), Finset.prod_mul_distrib]
    ring
  rw [e1]
  exact inProd_of_exp (pK'_ne p K') hc h' h0'
    (IntR_mul (IntR_mul (IntR_prod _ _ fun v _ => IntR_expK hc (hG v)) (IntR_mono hRp hV)) hW)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

open Classical in
theorem nc_loc (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (hT : GatTies D)
    (hL : Formalism.MainNotions.G.LatTied hT X Y) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D)
    (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w)) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) :
    nc_Loc D L X Y K hT u w hg t0 j := by
  obtain ⟨hal, hal0, hcap, hcap0⟩ := nc_ties X Y hT hL u w hg t0 ht0 j hj
  exact ⟨nc_gU_eq X Y hT hL u w hg t0 ht0 K j, growth_exclusion_sum_eq X Y hT hL u w hg t0 ht0 K j,
    hal, hal0, hcap, hcap0, fun s _ e he => nc_excl X Y hT hL u w hg t0 ht0 s e he⟩

def nc_Need2 (C₀ : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    C₀ ≤ K.dl1 → C₀ ≤ K.dl2 → C₀ ≤ K.Pr1 → (Formalism.MainNotions.G.rG L.sc < D.R.k ∧ 2 ≤ L.sc.x) → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        nc_De D L X Y K u w hg t0 j ∧
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

theorem nc_need_of (C₀ : ℝ) (h : nc_Need2 C₀) : nc_Need C₀ := by
  intro D L X Y K h1 h2 h3 h4 h5 hT hL u w hg hlog t0 ht0 j hj
  obtain ⟨hde, hpr⟩ := h D L X Y K h1 h2 h3 h4 h5 hT hL u w hg hlog t0 ht0 j hj
  exact ⟨nc_loc X Y K hT hL u w hg t0 ht0 j hj, hde, hpr⟩

theorem numerical_closed_of_need (C₀ : ℝ) (h : nc_Need2 C₀) : Formalism.MainNotions.FormalGroupSystem.NumericalComparisonUniform :=
  stmtNumE_of C₀ (nc_need_of C₀ h)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
