module

import Formalism.LocalToGlobal.CharacterGerms.MaximalOfValuationGeOne
public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Formalism.LocalToGlobal.CharacterGerms.Bundle029
public import Formalism.LocalToGlobal.CharacterGerms.Bundle027
public import Formalism.LocalToGlobal.CharacterGerms.Bundle033
import Formalism.LocalToGlobal.CharacterGerms.Bundle026
public import Formalism.LocalToGlobal.CharacterGerms.Bundle007
import Formalism.LocalToGlobal.CharacterGerms.Bundle008
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelf
public import Formalism.LocalToGlobal.CharacterGerms.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace ValuationNonnegativity

variable {C : Type} [Field C] {V : VF C}

theorem valuation_nonneg_iff {a : C} : V.Ge 0 a ↔ 0 ≤ V.v a := by
  unfold VF.Ge
  rw [WithTop.coe_zero]

theorem mm_zero : V.MM (0 : C) := by
  unfold VF.MM
  simp

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := by
  unfold VF.MM at *
  exact lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mm_sum {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) :=
  Finset.sum_induction f (fun x => V.MM x) (fun _ _ => mm_add) mm_zero h

theorem mm_mul_int {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  have h0 := valuation_nonneg_iff.mp ha
  unfold VF.MM at *
  rw [V.v.map_mul]
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left h0)

theorem mm_of_pow {a : C} {n : ℕ} (h : V.MM (a ^ n)) : V.MM a := by
  unfold VF.MM at *
  rw [V.v.map_pow] at h
  by_contra hle
  push_neg at hle
  exact absurd h (not_lt.mpr (nsmul_nonpos hle n))

theorem mm_pow {a : C} (ha : V.MM a) {n : ℕ} (hn : n ≠ 0) : V.MM (a ^ n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold VF.MM at *
  rw [V.v.map_pow, succ_nsmul]
  exact lt_of_lt_of_le ha (le_add_of_nonneg_left (nsmul_nonneg ha.le m))

theorem valuation_nonneg_of_pow {a : C} {n : ℕ} (h : V.Ge 0 (a ^ n)) (hn : n ≠ 0) : V.Ge 0 a := by
  rw [valuation_nonneg_iff] at *
  rw [V.v.map_pow] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_contra hlt
  push_neg at hlt
  rw [succ_nsmul] at h
  have h1 : m • V.v a ≤ 0 := nsmul_nonpos hlt.le m
  exact absurd h (not_le.mpr (lt_of_le_of_lt (le_of_le_of_eq (add_le_add h1 le_rfl) (zero_add _)) hlt))

theorem valuation_nonneg_div {x y : C} (hy : y ≠ 0) (h : V.v y ≤ V.v x) : V.Ge 0 (x / y) := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (fun h' => hy ((V.v.top_iff).mp h'))
  have hx : x = (x / y) * y := by field_simp
  rw [valuation_nonneg_iff]
  by_contra hlt
  push_neg at hlt
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have h2 : V.v x = ((s + r : ℝ) : WithTop ℝ) := by
    rw [hx, V.v.map_mul, ← hs, ← hr, WithTop.coe_add]
  rw [← hs] at hlt
  rw [h2, ← hr] at h
  have h3 : s < 0 := by exact_mod_cast hlt
  have h4 : r ≤ s + r := by exact_mod_cast h
  linarith

private theorem v_natCast_nonneg' (n : ℕ) : 0 ≤ V.v (n : C) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    refine le_trans (le_min ih ?_) (V.v.map_add _ _)
    rw [V.v.map_one]

theorem frob2 {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) :
    V.MM ((a + b) ^ V.l - a ^ V.l - b ^ V.l) := by
  apply Formalism.L2.FormalSeriesBounds.MaximalIdealCongruence.mm_add_pow <;> assumption

theorem frob_sum {ι : Type*} (s : Finset ι) (f : ι → C) (hf : ∀ i ∈ s, V.Ge 0 (f i)) :
    V.MM ((∑ i ∈ s, f i) ^ V.l - ∑ i ∈ s, f i ^ V.l) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_pow V.l_prime.ne_zero, sub_zero]; exact mm_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hs : V.Ge 0 (∑ j ∈ s, f j) := VF.Ge.sum fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have h1 := frob2 (hf i (Finset.mem_insert_self i s)) hs
    have h2 := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have e : (f i + ∑ j ∈ s, f j) ^ V.l - (f i ^ V.l + ∑ j ∈ s, f j ^ V.l) =
        ((f i + ∑ j ∈ s, f j) ^ V.l - f i ^ V.l - (∑ j ∈ s, f j) ^ V.l) +
          ((∑ j ∈ s, f j) ^ V.l - ∑ j ∈ s, f j ^ V.l) := by ring
    rw [e]; exact mm_add h1 h2

theorem exists_rel {N m : ℕ} (hm : m < N) (B : Fin N → Fin m → C) :
    ∃ β : Fin N → C, (∀ ν, V.Ge 0 (β ν)) ∧ (∃ ν, ¬ V.MM (β ν)) ∧ ∀ r, ∑ ν, β ν * B ν r = 0 := by
  let f : (Fin N → C) →ₗ[C] (Fin m → C) := Matrix.vecMulLinear (Matrix.of B)
  have hk : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hm)
  obtain ⟨β, hβ, hne⟩ := (Submodule.ne_bot_iff _).mp hk
  have hrel : ∀ r, ∑ ν, β ν * B ν r = 0 := fun r => by
    have := congrFun (LinearMap.mem_ker.mp hβ) r
    simpa [f, Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct] using this
  obtain ⟨ν1, hν1⟩ : ∃ ν, β ν ≠ 0 := by
    by_contra hc; push Not at hc; exact hne (funext hc)
  obtain ⟨ν0, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun ν => V.v (β ν))
    ⟨ν1, Finset.mem_univ _⟩
  have h0 : β ν0 ≠ 0 := by
    intro h
    have := hmin ν1 (Finset.mem_univ _)
    rw [h, V.v.map_zero, top_le_iff, AddValuation.top_iff] at this
    exact hν1 this
  refine ⟨fun ν => β ν / β ν0, fun ν => valuation_nonneg_div h0 (hmin ν (Finset.mem_univ _)), ⟨ν0, ?_⟩, fun r => ?_⟩
  · show ¬ V.MM (β ν0 / β ν0)
    rw [div_self h0]; unfold VF.MM; rw [V.v.map_one]; exact lt_irrefl 0
  · simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, hrel r, zero_div]

variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

theorem independence_bound_of_span_raw [IsAlgClosed C] (X : Cart V d I J) (a : ZMod d) (m : ℕ)
    (hR2 : ∀ (w : I → C) (x : ℕ → I ⊕ J → C), X.Good a w x → (∀ q, V.MM (X.c0' x q)) → ∀ c, V.MM (w c))
    (e : Fin m → J → C)
    (hspan : ∀ (w : I → C) (x : ℕ → I ⊕ J → C), X.Good a w x → (∀ c, V.MM (X.V2 x c)) →
      ∃ b : Fin m → C, ∀ q, V.MM (X.c0' x q ^ V.l - ∑ r, b r * e r q))
    (N : ℕ) (w : Fin N → I → C) (x : Fin N → ℕ → I ⊕ J → C) (hg : ∀ ν, X.Good a (w ν) (x ν))
    (hV : ∀ ν c, V.MM (X.V2 (x ν) c)) (hind : IndepMod V w) : N ≤ m := by
  by_contra hN; push Not at hN
  choose b hb using fun ν => hspan (w ν) (x ν) (hg ν) (hV ν)
  obtain ⟨β, hβi, ⟨ν0, hν0⟩, hrel⟩ := exists_rel (V := V) hN b
  have hl2 : 0 < V.l ^ 2 := pow_pos V.l_prime.pos 2
  choose c hc using fun ν => IsAlgClosed.exists_pow_nat_eq (β ν) hl2
  have hci : ∀ ν, V.Ge 0 (c ν) := fun ν => valuation_nonneg_of_pow (by rw [hc ν]; exact hβi ν) hl2.ne'
  have hG := Cart.Good.comb (X := X) Finset.univ (co := c) (fun ν _ => hci ν) (fun ν _ => hg ν)
  have hz : ∀ ν q, V.Ge 0 (X.c0' (x ν) q) := fun ν q => (hg ν).c0'_int q
  have hc0 : ∀ q, V.MM (X.c0' (∑ ν, teich V.l (c ν) (x ν)) q) := by
    intro q
    rw [Cart.c0'_comb]
    apply mm_of_pow (n := V.l)
    have h1 := frob_sum Finset.univ (fun ν => c ν ^ V.l * X.c0' (x ν) q)
      (fun ν _ => VF.Ge.mul_int ((hci ν).pow _) (hz ν q))
    have e1 : ∀ ν, (c ν ^ V.l * X.c0' (x ν) q) ^ V.l = β ν * X.c0' (x ν) q ^ V.l := by
      intro ν; rw [mul_pow, ← pow_mul, ← hc ν, sq]
    simp only [e1] at h1
    have h2 : V.MM (∑ ν, β ν * (X.c0' (x ν) q ^ V.l - ∑ r, b ν r * e r q)) :=
      mm_sum fun ν _ => mm_mul_int (hβi ν) (hb ν q)
    have h3 : ∑ ν, β ν * (∑ r, b ν r * e r q) = 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun r _ => ?_
      calc ∑ ν, β ν * (b ν r * e r q) = (∑ ν, β ν * b ν r) * e r q := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by rw [hrel r, zero_mul]
    have e2 : (∑ ν, c ν ^ V.l * X.c0' (x ν) q) ^ V.l =
        ((∑ ν, c ν ^ V.l * X.c0' (x ν) q) ^ V.l - ∑ ν, β ν * X.c0' (x ν) q ^ V.l) +
          ∑ ν, β ν * (X.c0' (x ν) q ^ V.l - ∑ r, b ν r * e r q) + ∑ ν, β ν * (∑ r, b ν r * e r q) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    rw [e2, h3, add_zero]
    exact mm_add h1 h2
  have hw := hR2 _ _ hG hc0
  have hcm := hind c hci (fun y => by
    have := hw y
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this)
  apply hν0
  rw [← hc ν0]
  exact mm_pow (hcm ν0) hl2.ne'

theorem even_val_add_two {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) :
    Even (a + 2).val ↔ Even a.val := by
  have h2d : 2 ∣ d := even_iff_two_dvd.mp hd
  rw [ZMod.val_add, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2d]
  have h2 : (2 : ZMod d).val % 2 = 0 := by
    rw [show (2 : ZMod d) = ((2 : ℕ) : ZMod d) by norm_num, ZMod.val_natCast, Nat.mod_mod_of_dvd _ h2d]
  omega

end ValuationNonnegativity

section Closed

variable {C : Type} [Field C]

end Closed

end Formalism.L2.FormalSeriesBounds
end
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

section Core

variable {Orb : Type} {d : ℕ} [NeZero d]

structure LabSGeoCore (C3 : IntChart T io y) (ι : T.Fr →+* C) (Y : FBChart C V (𝓞 E) (chD C3.ch))
    (lab : LabS E C Orb d) : Prop where
  e_eig : ∀ o (x : lab.II Dw o) a, linAct (Y.B.A.act a) (selfLieBasisVector C3 ι lab o x) =
    emA3 io ι (lab.tau o x.1) a • selfLieBasisVector C3 ι lab o x
  e_sat : ∀ o, ∃ w : Fin (chD C3.ch) → lab.II Dw o → C, (∀ x q, V.Ge 0 (w x q)) ∧
    ∀ q q' : lab.II Dw o, ∑ x, selfLieBasisVector C3 ι lab o q x * w x q' = if q = q' then 1 else 0
  e_full : ∀ o a (v : Fin (chD C3.ch) → C), (∀ x, linAct (Y.B.A.act x) v = emA3 io ι (lab.tau o a) x • v) →
    ∃ b : lab.II Dw o → C, (∀ q, q.1 ≠ a → b q = 0) ∧ v = ∑ q, b q • selfLieBasisVector C3 ι lab o q

theorem labSGeo_of (hstar : ∀ a : 𝓞 E, star a = H.bar a) {C3 : IntChart T io y} {ι : T.Fr →+* C} (hι : EmbOK T V ι)
    {Y : FBChart C V (𝓞 E) (chD C3.ch)} {lab : LabS E C Orb d} (ha : LabSArith V io ι lab)
    (h : LabSGeoCore C3 ι Y lab) : LabSGeo C3 ι Y lab := by
  refine {
    em_int := fun _ _ x => embedding_integral ι _ x
    em_conj := ?_
    e_int := fun _ _ i => a3uvec_int C3 hι _ i
    e_eig := h.e_eig
    e_sat := h.e_sat
    e_full := h.e_full }
  intro o a x
  rw [← ha.conj o a]
  exact (embedding_conjugate hstar ι _ x).symm

end Core

def RankMaximalSelfOfNondegenerate : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0),
    NDG Y → (Y.rawSelf p).RankHyp → ∀ Hc : ∀ g, (Y.rawSelf p).CartHyp V g, RawChart.RankMaximalCondition Hc

variable (Xo c)

theorem rank_maximal_self_charts_of_nondegenerate (h1 : RankMaximalSelfOfNondegenerate) (h2 : NondegenerateCharts Xo c) : RankMaximalSelfCharts Xo c :=
  fun hstar T io y C3 C _ _ V ι hι k Y hY _ d _ lab ha hg hr o Hc => by
    have hrank : (Y.rawSelf (selfOfLab ha hg o)).RankHyp := by
      refine { big_compl := (hr o).1, rk_big := ?_, rk_small := ?_ }
      · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab]
          convert (card_sigma_fst (fun b => Dw.mult (lab.tau o b)) a).trans ((hr o).2.1 a hb) using 2
          exact Finset.filter_congr (fun _ _ => Iff.rfl)
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
          exact (card_sigma_shift (fun b => Dw.mult (lab.tau o b)) lab.hd a).trans ((hr o).2.2.2.1 a hb)
      · refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab]
          convert (card_sigma_fst (fun b => Dw.mult (lab.tau o b)) a).trans ((hr o).2.2.1 a hb) using 2
          exact Finset.filter_congr (fun _ _ => Iff.rfl)
        · intro a hb
          simp only [FBChart.rawSelf, selfOfLab, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
          exact (card_sigma_shift (fun b => Dw.mult (lab.tau o b)) lab.hd a).trans ((hr o).2.2.2.2 a hb)
    exact h1 C V (𝓞 E) _ Y d _ (selfOfLab ha hg o) (h2 hstar T io y C3 C V ι hι k Y hY) hrank Hc

end Formalism.L2.FormalSeriesBounds
end
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem FBChart.uncurry_log_constantCoeff_chart (Y : FBChart C V O dd) (i : Fin dd) : MvPowerSeries.constantCoeff (un1 (Y.lg i)) = 0 := by
  rw [constantCoeff_uncurry, Y.lg_const]

theorem FBChart.uncurry_exp_log_eq_X (Y : FBChart C V O dd) (i : Fin dd) :
    MvPowerSeries.subst (fun j => un1 (Y.lg j)) (un1 (Y.ex i)) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  rw [uncurry_comp Y.lg_const, Y.ex_lg]
  exact uncurry_X i

theorem FBChart.uncurry_linear_combination (Y : FBChart C V O dd) (i : Fin dd) (μ : Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    MvPowerSeries.coeff μ (un1 (Y.lg i)) =
      MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  show MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = _
  rw [Y.lg_lin i _ (by rw [Finsupp.degree_mapDomain]; exact hμ), ← uncurry_X i]
  rfl

theorem FBChart.ex_lg_at' (Y : FBChart C V O dd) {τ : Type} (A : Fin dd → MvPowerSeries τ C)
    (hA : ∀ j, MvPowerSeries.constantCoeff (A j) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => MvPowerSeries.subst A (un1 (Y.lg j))) (un1 (Y.ex i)) = A i := by
  have hA' := MvPowerSeries.hasSubst_of_constantCoeff_zero hA
  have hL : MvPowerSeries.HasSubst (fun j => un1 (Y.lg j)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => Y.uncurry_log_constantCoeff_chart j
  rw [← MvPowerSeries.subst_comp_subst_apply hL hA', Y.uncurry_exp_log_eq_X, MvPowerSeries.subst_X hA']

theorem hom_of_lgLin (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C} {U : Fin dd → C} (hγ : IsCv V γ)
    (hlg : Y.LgLin γ U) (i : Fin dd) (μ : Fin 2 →₀ ℕ) (hμ0 : μ 0 < V.l) (hμ1 : μ 1 < V.l) :
    MvPowerSeries.coeff μ
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) (Y.B.G.F i) -
        cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ i)) = 0 := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hX : ∀ k : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X k : MvPowerSeries (Fin 2) C) = 0 :=
    fun k => MvPowerSeries.constantCoeff_X k
  have hS : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) C) = 0 := by
    rw [map_add (f := _), hX 0, hX 1, add_zero]
  have hP0 : ∀ (k : Fin 2) (j : Fin dd), MvPowerSeries.constantCoeff (cvAt (MvPowerSeries.X k) (γ j)) = 0 :=
    fun k j => const_cvAt (hX k) (hγ0 j)
  have hQ0 : ∀ j, MvPowerSeries.constantCoeff (cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ j)) = 0 :=
    fun j => const_cvAt hS (hγ0 j)
  have hPP : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hP0 q.1 q.2
  have hFP0 : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) (Y.B.G.F j)) = 0 :=
    fun j => MvPowerSeries.constantCoeff_subst_eq_zero hPP (fun q => hP0 q.1 q.2) (Y.B.G.const j)
  have hAt : ∀ (s : MvPowerSeries (Fin 2) C), MvPowerSeries.constantCoeff s = 0 → ∀ j,
      Agr (V.l ^ 2) (MvPowerSeries.subst (fun j' => cvAt s (γ j')) (un1 (Y.lg j))) (U j • s) := by
    intro s hs j
    rw [subst_cvAt hs hγ0, ← cvAt_smul_X hs]
    exact agr_subst_right (a := fun _ : Unit => s) (fun _ => hs) (hlg j)
  have hsum : ∀ j, Agr (V.l ^ 2)
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0) (γ j')) (un1 (Y.lg j)) +
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 1) (γ j')) (un1 (Y.lg j)))
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ j')) (un1 (Y.lg j))) := by
    intro j
    refine ((hAt _ (hX 0) j).add (hAt _ (hX 1) j)).trans ?_
    rw [← smul_add]
    exact (hAt _ hS j).symm
  have e1 := Y.ex_lg_at' _ hFP0 i
  have e1' : (fun j => MvPowerSeries.subst
      (fun j' => MvPowerSeries.subst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) (Y.B.G.F j'))
      (un1 (Y.lg j))) = fun j =>
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0) (γ j')) (un1 (Y.lg j)) +
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 1) (γ j')) (un1 (Y.lg j)) := by
    funext j
    exact lg_addOf Y (fun k j' => cvAt (MvPowerSeries.X k) (γ j')) hP0 j
  rw [e1'] at e1
  have e2 := Y.ex_lg_at' _ hQ0 i
  have hc : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0) (γ j')) (un1 (Y.lg j)) +
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 1) (γ j')) (un1 (Y.lg j))) = 0 := by
    intro j
    rw [map_add (f := _), MvPowerSeries.constantCoeff_subst_eq_zero
        (MvPowerSeries.hasSubst_of_constantCoeff_zero fun j' => hP0 0 j') (fun j' => hP0 0 j') (Y.uncurry_log_constantCoeff_chart j),
      MvPowerSeries.constantCoeff_subst_eq_zero
        (MvPowerSeries.hasSubst_of_constantCoeff_zero fun j' => hP0 1 j') (fun j' => hP0 1 j') (Y.uncurry_log_constantCoeff_chart j),
      add_zero]
  have hc' : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ j')) (un1 (Y.lg j))) = 0 :=
    fun j => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hQ0) hQ0 (Y.uncurry_log_constantCoeff_chart j)
  have hag := agr_subst_left hc hc' hsum (un1 (Y.ex i))
  rw [e1, e2] at hag
  have hdeg : μ.degree < V.l ^ 2 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    nlinarith
  rw [map_sub, sub_eq_zero]
  exact hag μ hdeg

theorem coeff1_of_lgLin (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C} {U : Fin dd → C} (hγ : IsCv V γ)
    (hlg : Y.LgLin γ U) (i : Fin dd) : PowerSeries.coeff 1 (γ i) = U i := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hlin : Agr 2 (un1 (Y.lg i)) (MvPowerSeries.X i) := fun e he => Y.uncurry_linear_combination i e (by omega)
  have h2 := agr_subst_right (a := γ) hγ0 hlin
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0)] at h2
  have h3 := (hlg i).mono (show 2 ≤ V.l ^ 2 by nlinarith)
  have h4 := (h2.symm.trans h3) (Finsupp.single () 1) (by rw [Finsupp.degree_single]; omega)
  change PowerSeries.coeff 1 (γ i) = PowerSeries.coeff 1 _ at h4
  rw [h4, map_smul, coeffX', if_pos rfl, smul_eq_mul, mul_one]

theorem agr_of_ty {I : Fin 2 → Type} [∀ g, Fintype (I g)] {g : Fin 2} {w : I g → C} {x : ℕ → I g ⊕ JJ I g → C}
    (h0 : x 0 = Sum.elim w 0) (h1 : ∀ c, x 1 (Sum.inl c) = 0) (cf : I g → C) :
    Agr (V.l ^ 2) (∑ c : I g, cf c • tyS V.l (fun s => x s (Sum.inl c)))
      ((∑ c, cf c * w c) • (MvPowerSeries.X () : PowerSeries C)) := by
  intro e he
  have hl := V.l_prime.two_le
  obtain ⟨n, rfl⟩ : ∃ n, e = Finsupp.single () n := ⟨e (), Finsupp.unique_single e⟩
  rw [Finsupp.degree_single] at he
  change PowerSeries.coeff n _ = PowerSeries.coeff n _

  rw [map_sum, map_smul, coeffX']
  simp only [map_smul, smul_eq_mul, tyS_good_coeff h0 h1 hl _ n he]
  by_cases hn1 : n = 1
  · simp [hn1]
  · simp [hn1]

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem limSelf_holds : LimSelfSt := by
  unfold LimSelfSt AllSelf
  intro C _ _ V O _ _ dd Y d _ I0 _ p g x x' hx hlim
  exact LimTy.lim_mem (Y.rawSelf p) V.l_prime.two_le
    (fun i => FBChart.self_chart_log_constantCoeff (Y := Y) (p := p) i)
    (fun i => FBChart.self_chart_exp_constantCoeff (Y := Y) (p := p) i)
    (fun i => FBChart.rawSelf_lgex (Y := Y) (p := p) i)
    (fun i => FBChart.rawSelf_exlg (Y := Y) (p := p) i)
    g x x' hx hlim

end Formalism.L2.FormalSeriesBounds
end
end
