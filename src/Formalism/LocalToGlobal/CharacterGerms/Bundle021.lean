module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Formalism.LocalToGlobal.CharacterGerms.Bundle019
public import Formalism.LocalToGlobal.CharacterGerms.CoeffSubstEqSum
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjFB
public import Formalism.LocalToGlobal.CharacterGerms.Bundle020
public import Formalism.LocalToGlobal.CharacterGerms.Bundle001
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
import Formalism.LocalToGlobal.CharacterGerms.Bundle013
import Formalism.LocalToGlobal.CharacterGerms.Bundle018

@[expose] public section

section

noncomputable section
open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.BasicNotions

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

def RowData.rk (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I g => (X.G g).ty (Sum.inl c) = a).card

structure Flag (X : RowData C V d I J) where
  en : ∀ g a, Fin (X.rk g a) → I g
  en_inj : ∀ g a, Function.Injective (en g a)
  en_ty : ∀ g a c, (X.G g).ty (Sum.inl (en g a c)) = a

def Flag.letter {X : RowData C V d I J} (F : Flag X) (g : Fin 2) (a : ZMod d) {N : ℕ}
    (x : Fin N × Fin (X.rk g a)) : Fin N × WV I := (x.1, ⟨g, F.en g a x.2⟩)

def bg (a : ZMod d) : Fin 2 := if Even a.val then 0 else 1

inductive GlobalTheory (d : ℕ) where

  | bi (g : Fin 2) (a : ZMod d) (i y : ℕ)

  | ch (g : Fin 2) (a : ZMod d) (u : ℕ)

  | mon (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ)

namespace GlobalTheory

def what₂ (n : ℕ) : GlobalTheory d → ℕ
  | bi _ _ _ _ => n
  | ch _ _ _ => n
  | mon _ _ N => N

variable (X : RowData C V d I J) (F : Flag X)

def poly : (b : GlobalTheory d) → MvPolynomial (Fin (b.what₂ X.n) × WV I) C
  | bi g a i y =>
      MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rk g a) X.n) ^ (V.l ^ i * y) *
        MvPolynomial.rename (F.letter (1 - g) (a + (i : ZMod d)))
          (minorK C X.n (X.rk (1 - g) (a + (i : ZMod d))) X.n) ^ y
  | ch g a u => MvPolynomial.rename (F.letter g a) (minorK C X.n (X.rk g a) X.n) ^ u
  | mon g e N => ∏ a : ZMod d, MvPolynomial.rename (F.letter g a) (monP C N (X.rk g a) (e a))

def kind (n : ℕ) : (b : GlobalTheory d) → Fin (b.what₂ n) → Option (Fin 2 × ZMod d × ZMod d)
  | bi g a i _ => fun _ => some (g, a, a + (i : ZMod d))
  | ch _ _ _ => fun _ => none
  | mon _ _ _ => fun _ => none

def wt : GlobalTheory d → Fin 2 → ZMod d → ℕ → ℕ
  | bi g a i y => fun g' a' k =>
      (if g' = g ∧ a' = a ∧ k = X.n then V.l ^ i * y else 0) +
        (if g' = 1 - g ∧ a' = a + (i : ZMod d) ∧ k = X.n then y else 0)
  | ch g a u => fun g' a' k => if g' = g ∧ a' = a ∧ k = X.n then u else 0
  | mon g e N => fun g' a' k => if g' = g ∧ 1 ≤ k ∧ k ≤ min N (X.rk g a') then e a' k else 0

def Attains (b : GlobalTheory d) (c : ℝ) : Prop :=
  ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) ∧
    ∃ gr : Fin (b.what₂ X.n) → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
      V.v (ValOf X.hL (b.poly X F) (b.kind X.n) gr) ≤ ((c : ℝ) : WithTop ℝ)

end GlobalTheory

def BiSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), X.Alt → 5 ≤ V.l → 1 ≤ X.n →
    ∀ g a, X.big g a → ∀ i : ℕ, Odd i → i < d →
      Windows (S0 V.l i X.n) {y | (GlobalTheory.bi g a i y).Attains X F (blockBd V.l X.n X.m i y)}

def CHSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X), ∀ g a, X.big g a → ∀ u : ℕ,
      (X.Alt → (GlobalTheory.ch g a u).Attains X F (chBd V.l X.n X.m u)) ∧
      ((∀ a, X.big g a) → (GlobalTheory.ch g a u).Attains X F ((u : ℝ) * (X.m / ((V.l : ℝ) - 1))))

def monDegAll (X : RowData C V d I J) (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ a : ZMod d, monDeg N (X.rk g a) (e a)

def MONSupply : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (F : Flag X) (g : Fin 2) (e : ZMod d → ℕ → ℕ)
    (N : ℕ),
      (GlobalTheory.mon g e N).Attains X F ((monDegAll X g e N : ℝ) / ((V.l : ℝ) - 1)) ∧
      ((∀ a ρ, monAl N (X.rk g a) (e a) ρ < V.l) → (GlobalTheory.mon g e N).Attains X F 0)

def ValBlocks {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
    [∀ o g, Fintype (J o g)] (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o))
    (Z : Finset Orb) (nW : ℕ) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (ν : ℝ) : Prop :=
  ∀ L : Orb → List (GlobalTheory d × ℝ),
    (∀ o ∈ Z, ∀ p ∈ L o, p.1.Attains (X o) (F o) p.2) →
    (∑ o ∈ Z, ((L o).map fun p => p.1.what₂ (X o).n).sum) ≤ nW →
    (∀ o ∈ Z, ∀ g a k, ((L o).map fun p => p.1.wt (X o) g a k).sum = ga o g a k) →
    ν ≤ ∑ o ∈ Z, ((L o).map Prod.snd).sum

def restDeg (bgr : ZMod d → Fin 2) (n : ℕ) (ga : Fin 2 → ZMod d → ℕ → ℕ) (K : ℕ) : ℕ :=
  ∑ g : Fin 2, ∑ a : ZMod d, ∑ k ∈ Finset.Icc 1 K, if g = bgr a ∧ k = n then 0 else k * ga g a k

structure WtHyp (N : NumDatum) (l : ℕ) (Z : Finset (RPl N.R)) (bgr : ZMod (N.ordP l) → Fin 2)
    (rk : RPl N.R → Fin 2 → ZMod (N.ordP l) → ℕ)
    (ga : RPl N.R → Fin 2 → ZMod (N.ordP l) → ℕ → ℕ) (W exc : RPl N.R → ℕ) (rest : ℝ) : Prop where
  supp : ∀ z ∈ Z, ∀ g a k, ga z g a k ≠ 0 → 1 ≤ k ∧ k ≤ rk z g a
  main : ∀ z ∈ Z, ∀ a, ga z (bgr a) a (N.R.k - 1) = alongOrb N l z W a + alongOrb N l z exc a
  rest_eq : rest = ∑ z ∈ Z, ((restDeg bgr (N.R.k - 1) (ga z) N.R.r : ℝ) +
    ∑ a, ((N.R.k : ℝ) - 1) * ((alongOrb N l z exc a : ℕ) : ℝ))

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePLie

section Glue

variable {C : Type} [Field C] {V : VF C}

theorem tends_pow_zero {a : C} (ha : V.MM a) : Tends V (fun n => a ^ V.l ^ n) 0 := by
  unfold Tends VF.MM at *
  intro w
  by_cases ha0 : a = 0
  · refine ⟨0, fun n _ => ?_⟩
    unfold VF.Ge
    show (w : WithTop ℝ) ≤ V.v (0 - a ^ V.l ^ n)
    rw [ha0, zero_pow (pow_pos V.l_prime.pos n).ne', sub_zero, AddValuation.map_zero]
    exact le_top
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff V.v).mpr ha0)
    have hr0 : 0 < r := by
      rw [← hr] at ha
      exact WithTop.coe_pos.mp ha
    refine ⟨⌈w / r⌉₊, fun n hn => ?_⟩
    unfold VF.Ge
    show (w : WithTop ℝ) ≤ V.v (0 - a ^ V.l ^ n)
    rw [zero_sub, AddValuation.map_neg, AddValuation.map_pow, ← hr, ← WithTop.coe_nsmul,
      WithTop.coe_le_coe, nsmul_eq_mul]
    have h1 : (n : ℝ) ≤ ((V.l ^ n : ℕ) : ℝ) := by
      first
        | exact_mod_cast (Nat.lt_pow_self V.l_prime.one_lt n).le
        | exact_mod_cast (Nat.lt_pow_self V.l_prime.one_lt).le
    have h2 : w / r ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    exact (div_mul_cancel₀ w hr0.ne').ge.trans (mul_le_mul_of_nonneg_right (h2.trans h1) hr0.le)

variable [CharZero C] {O : Type} [CommRing O] {n d : ℕ}

theorem chi_kill (K : KeyData C V O n d) (w : Fin n → C) (hw : w ≠ 0) (hP : Matrix.mulVec K.P w = w)
    (χ : O →+* C) (hχ : ∀ x, Matrix.mulVec (K.ρ x) w = χ x • w) :
    (∀ y, V.Ge 0 (χ y)) ∧ ∀ z, (∀ a, V.MM (K.em a z)) → V.MM (χ z) := by
  have hint : ∀ y, V.Ge 0 (χ y) := fun y => eig_int (K.ρ y) (K.ρ_int y) w hw (χ y) (hχ y)
  refine ⟨hint, ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hw (funext hc)

  have hT : Tends V (fun m => χ K.ε ^ V.l ^ m * w i) (w i) := by
    have h1 : Tends V (fun m => Matrix.mulVec (K.ρ (K.ε ^ V.l ^ m)) w i) (Matrix.mulVec K.P w i) := by
      simp only [Matrix.mulVec, dotProduct]
      refine Tends.sum _ fun j _ => Tends.mul ?_ (tends_const _)
      exact RowTiePProj.tends_of_nat fun N => K.P_lim N i j
    have e : (fun m => Matrix.mulVec (K.ρ (K.ε ^ V.l ^ m)) w i) = fun m => χ K.ε ^ V.l ^ m * w i := by
      funext m
      rw [hχ, map_pow]; rfl
    rw [e, hP] at h1
    exact h1
  have hunit : ¬ V.MM (χ K.ε) := by
    intro hm
    have h0 := (tends_pow_zero hm).mul (tends_const (V := V) (w i))
    rw [zero_mul] at h0
    exact hi (hT.unique h0)
  intro z hz
  obtain ⟨y, hy⟩ := K.ε_ann z hz
  have h1 := congrArg (fun t => V.v (χ t)) hy
  simp only [map_mul, map_natCast, AddValuation.map_mul, V.v_l] at h1
  unfold VF.MM at hunit ⊢
  push_neg at hunit
  have he0 : V.v (χ K.ε) = 0 := le_antisymm hunit (hint K.ε)
  rw [he0, zero_add] at h1
  rw [h1]
  have := hint y
  unfold VF.Ge at this
  calc (0 : WithTop ℝ) < 1 := by exact_mod_cast one_pos
    _ = 1 + 0 := (add_zero _).symm
    _ ≤ 1 + V.v (χ y) := add_le_add le_rfl (by exact_mod_cast this)

end Glue

section Top

theorem keyLA_of (hE : KeyEigSt) (hR : KeyResSt) (hD : KeyDeltaSt) (C : Type) [Field C] [CharZero C] (V : VF C)
    (hac : IsAlgClosed C)
    (hcpl : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n))
    (O : Type) [CommRing O] (n d : ℕ) [NeZero d] (K : KeyData C V O n d) (x : O) :
    Polynomial.aeval (K.ρ x) (∏ c : ZMod d, (Polynomial.X - Polynomial.C (K.em c x))) * K.P = 0 := by
  have hv : ∀ v : Fin n → C,
      Matrix.mulVec (Polynomial.aeval (K.ρ x) (∏ c : ZMod d, (Polynomial.X - Polynomial.C (K.em c x))) * K.P) v = 0 := by
    intro v
    obtain ⟨m, w, χ, hPv, hw⟩ := hE C V hac hcpl O n d K v
    rw [← Matrix.mulVec_mulVec, hPv, Matrix.mulVec_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h0 : w j = 0
    · rw [h0, Matrix.mulVec_zero]
    obtain ⟨hPw, hχ⟩ := hw j
    obtain ⟨hint, hkill⟩ := chi_kill K (w j) h0 hPw (χ j) hχ
    obtain ⟨c, hc⟩ := hR C V O n d K (χ j) hint hkill
    have heq := hD C V O n d K (χ j) c hint hc
    rw [aeval_mulVec _ _ _ (hχ x), Polynomial.eval_prod]
    have : ∏ c' : ZMod d, Polynomial.eval (χ j x) (Polynomial.X - Polynomial.C (K.em c' x)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ c) (by rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        heq, sub_self])
    rw [this, zero_smul]
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

end Top

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

theorem echelon {C : Type} [Field C] (vm : Valuation C NNReal) (n : ℕ) :
    ∀ (k : ℕ) (M : Submodule C (Fin n → C)), Module.finrank C M = k →
    ∃ (s : ℕ) (J : Fin s → Fin n) (B : Fin s → Fin n → C), (∀ i, B i ∈ M) ∧ (∀ i x, vm (B i x) ≤ 1) ∧
      (∀ i i', B i (J i') = if i = i' then 1 else 0) ∧ ∀ v ∈ M, v = ∑ i, v (J i) • B i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro M hM
  by_cases h0 : ∃ v ∈ M, v ≠ 0
  swap
  · push_neg at h0
    refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun v hv => ?_⟩
    simp [h0 v hv]
  obtain ⟨v, hvM, hv0⟩ := h0
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 hv0
  obtain ⟨j, -, hjmax⟩ := (Finset.univ : Finset (Fin n)).exists_max_image (fun x => vm (v x))
    ⟨x₀, Finset.mem_univ _⟩
  have hvj : v j ≠ 0 := by
    intro h
    have h1 : vm (v x₀) ≤ vm (v j) := hjmax x₀ (Finset.mem_univ _)
    rw [h, map_zero] at h1
    exact hx₀ ((Valuation.zero_iff vm).1 (le_antisymm h1 zero_le'))

  set v₀ : Fin n → C := (v j)⁻¹ • v with hv₀
  have hv₀j : v₀ j = 1 := by simp [hv₀, hvj]
  have hv₀M : v₀ ∈ M := M.smul_mem _ hvM
  have hv₀le : ∀ x, vm (v₀ x) ≤ 1 := by
    intro x
    have hpos : 0 < vm (v j) := pos_iff_ne_zero.2 ((Valuation.ne_zero_iff vm).2 hvj)
    simp only [hv₀, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact hjmax x (Finset.mem_univ _)
  set M' : Submodule C (Fin n → C) := M ⊓ LinearMap.ker (LinearMap.proj j) with hM'
  have hlt : M' < M := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    have h1 : v₀ ∈ M' := h ▸ hv₀M
    have h2 : v₀ j = 0 := (Submodule.mem_inf.1 h1).2
    rw [hv₀j] at h2
    exact one_ne_zero h2
  have hfr : Module.finrank C M' < k := hM ▸ Submodule.finrank_lt_finrank_of_lt hlt
  obtain ⟨s, J', B', hB'M, hB'le, hB'δ, hB'span⟩ := ih _ hfr M' rfl
  have hB'j : ∀ i, B' i j = 0 := fun i => (Submodule.mem_inf.1 (hB'M i)).2
  have hB'M0 : ∀ i, B' i ∈ M := fun i => (Submodule.mem_inf.1 (hB'M i)).1
  set b : Fin n → C := v₀ - ∑ i, v₀ (J' i) • B' i with hb
  have hbM : b ∈ M := M.sub_mem hv₀M (M.sum_mem fun i _ => M.smul_mem _ (hB'M0 i))
  have hbj : b j = 1 := by simp [hb, Finset.sum_apply, hB'j, hv₀j]
  have hbJ : ∀ i', b (J' i') = 0 := by
    intro i'
    simp [hb, Finset.sum_apply, hB'δ]
  have hble : ∀ x, vm (b x) ≤ 1 := by
    intro x
    simp only [hb, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Valuation.map_sub_le _ (hv₀le x) (Valuation.map_sum_le _ fun i _ => ?_)
    rw [map_mul]
    exact mul_le_one' (hv₀le _) (hB'le i x)
  refine ⟨s + 1, (Fin.cons j J' : Fin (s + 1) → Fin n), (Fin.cons b B' : Fin (s + 1) → Fin n → C),
    ?_, ?_, ?_, ?_⟩
  · intro i
    induction i using Fin.cases with
    | zero => simpa using hbM
    | succ i => simpa using hB'M0 i
  · intro i x
    induction i using Fin.cases with
    | zero => simpa using hble x
    | succ i => simpa using hB'le i x
  · intro i i'
    induction i using Fin.cases with
    | zero =>
      induction i' using Fin.cases with
      | zero => simp [hbj]
      | succ i' => simp only [Fin.cons_zero, Fin.cons_succ, hbJ]; rw [if_neg (Fin.succ_ne_zero i').symm]
    | succ i =>
      induction i' using Fin.cases with
      | zero => simp only [Fin.cons_zero, Fin.cons_succ, hB'j]; rw [if_neg (Fin.succ_ne_zero i)]
      | succ i' => simp [hB'δ, Fin.succ_inj]
  · intro w hw
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hw' : w - w j • b ∈ M' := by
      refine Submodule.mem_inf.2 ⟨M.sub_mem hw (M.smul_mem _ hbM), ?_⟩
      simp [LinearMap.mem_ker, hbj]
    have h1 := hB'span _ hw'
    have e : ∀ i, (w - w j • b) (J' i) = w (J' i) := by
      intro i
      simp [hbJ]
    simp only [e] at h1
    rw [← h1]
    abel

theorem eigFreeSt_holds : EigFreeSt := by
  intro C _ vm R _ _ hI n ι L χ
  set f := algebraMap R C
  let M : Submodule C (Fin n → C) :=
    { carrier := {w | ∀ a, ((L a).map f).mulVec w = f (χ a) • w}
      add_mem' := by
        intro w w' hw hw' a
        simp only [Set.mem_setOf_eq] at hw hw' ⊢
        rw [Matrix.mulVec_add, hw a, hw' a, smul_add]
      zero_mem' := by
        intro a
        simp
      smul_mem' := by
        intro c w hw a
        simp only [Set.mem_setOf_eq] at hw ⊢
        rw [Matrix.mulVec_smul, hw a, smul_comm] }
  obtain ⟨s, J, B, hBM, hBle, hBδ, hspan⟩ := echelon vm n _ M rfl
  have hlift : ∀ i x, ∃ r : R, f r = B i x := fun i x => hI.exists_of_le_one (hBle i x)
  choose W hW using hlift
  have hfW : ∀ i, f ∘ W i = B i := fun i => funext (hW i)
  have hmap : ∀ (A : Matrix (Fin n) (Fin n) R) (v : Fin n → R), f ∘ (A.mulVec v) = (A.map f).mulVec (f ∘ v) := by
    intro A v
    funext x

    simp [Matrix.mulVec, dotProduct, map_sum]
  have hinj : Function.Injective f := hI.hom_inj
  have hinjv : ∀ v w : Fin n → R, f ∘ v = f ∘ w → v = w :=
    fun v w h => funext fun x => hinj (congrFun h x)
  refine ⟨s, W, fun i a => ?_, fun v hv => ?_⟩
  · apply hinjv
    rw [hmap, hfW, hBM i a]
    funext x
    simp [hW]
  · have hvM : f ∘ v ∈ M := by
      intro a
      rw [← hmap, hv a]
      funext x
      simp
    refine ⟨fun i => v (J i), ?_, ?_⟩
    · apply hinjv
      have h1 := hspan _ hvM
      funext x
      have hx := congrFun h1 x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at hx ⊢

      rw [map_sum]
      simp only [map_mul, hW]
      exact hx.symm
    · intro c hc
      funext i
      have h1 := congrFun hc (J i)
      apply hinj
      rw [← h1]

      simp [Finset.sum_apply, map_sum, hW, hBδ]

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

theorem placeSt_of_X (h : Pl.PlaceCriterionOfIdempotent) : PlaceSt := by
  intro l _ OE _ _ _ _ _ R _ _ _ _ _ hl hd d _ em h1 h2 h3
  obtain ⟨e, he1, he2, he3, iN, t, jj, hj, ht, b, hb⟩ := h l OE R hl hd d em h1 h2 h3
  exact ⟨⟨e, he1, he2, he3⟩, iN, t, jj, hj, ht, b, hb⟩

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end
