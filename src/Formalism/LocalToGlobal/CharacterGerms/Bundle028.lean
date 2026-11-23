module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Formalism.LocalToGlobal.CharacterGerms.Bundle007
public import Formalism.LocalToGlobal.CharacterGerms.Bundle014
public import Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfUnitGerm
public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Formalism.LocalToGlobal.CharacterGerms.Bundle027
import Formalism.LocalToGlobal.CharacterGerms.LemmaMLin
import Formalism.LocalToGlobal.CharacterGerms.Bundle008
import Formalism.LocalToGlobal.CharacterGerms.Bundle011
public import Formalism.LocalToGlobal.CharacterGerms.TripleSubstSecondCoordinate
public import Formalism.LocalToGlobal.CharacterGerms.Bundle019
public import Formalism.LocalToGlobal.CharacterGerms.Bundle024
public import Formalism.LocalToGlobal.CharacterGerms.Bundle002
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyTeich2
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

namespace WeightHomogeneousLetters

open WeightHomogeneousMinors

section WH

variable {R : Type} [CommRing R]

theorem isWH_aeval {σ τ : Type} {w : τ → ℕ} {w' : σ → ℕ} (f : σ → MvPolynomial τ R)
    (hf : ∀ x, IsWeightedHomogeneous w (f x) (w' x)) {p : MvPolynomial σ R} {D : ℕ}
    (hp : IsWeightedHomogeneous w' p D) : IsWeightedHomogeneous w (aeval f p) D := by
  rw [aeval_def, eval₂_eq]
  apply IsWeightedHomogeneous.sum
  intro m hm
  have h1 : IsWeightedHomogeneous w (∏ i ∈ m.support, f i ^ m i) (∑ i ∈ m.support, m i • w' i) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => (hf i).pow (m i)
  have h2 : (∑ i ∈ m.support, m i • w' i) = D := by
    rw [← hp (mem_support_iff.1 hm), Finsupp.weight_apply]
    rfl
  have h3 := (isWeightedHomogeneous_C w (AddMonoidAlgebra.coeff p m)).mul h1
  rw [zero_add, h2] at h3
  exact h3

theorem isWH_add {σ : Type} {w1 w2 : σ → ℕ} {p : MvPolynomial σ R} {D1 D2 : ℕ}
    (h1 : IsWeightedHomogeneous w1 p D1) (h2 : IsWeightedHomogeneous w2 p D2) :
    IsWeightedHomogeneous (fun x => w1 x + w2 x) p (D1 + D2) := by
  intro m hm
  have e1 := h1 hm
  have e2 := h2 hm
  simp only [Finsupp.weight_apply, Finsupp.sum] at e1 e2 ⊢
  rw [← e1, ← e2, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => smul_add _ _ _

end WH

section Block

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X) (idx : ∀ g, I g → ℕ) (std : ∀ g t (c : Fin (X.rkF g t)), idx g (F.en g t c) = c.val)

def wRowG {N : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (x : Fin N × WV I) : ℕ :=
  if x.2.1 = g0 ∧ (X.G x.2.1).ty (Sum.inl x.2.2) = t0 ∧ idx x.2.1 x.2.2 = c0 then 1 else 0

include std in
theorem wRowG_letter {N : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d)
    (x : Fin N × Fin (X.rkF g t)) :
    wRowG X idx g0 t0 c0 (F.letter g t x) = if (g = g0 ∧ t = t0) ∧ (x.2 : ℕ) = c0 then 1 else 0 := by
  simp only [wRowG, Flag.letter, F.en_ty, std, and_assoc]

include std in
theorem isWH_letter_minorK {N k : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d) :
    IsWeightedHomogeneous (wRowG X idx (N := N) g0 t0 c0) (rename (F.letter g t) (minorK C N (X.rkF g t) k))
      (if k ≤ N ∧ k ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < k then 1 else 0) :=
  isWH_rename _ (isWH_minorK_row (g = g0 ∧ t = t0) c0 fun x => wRowG_letter X F idx std g0 t0 c0 g t x)

theorem num_ch (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (t : ZMod d) (u : ℕ) :
    u • (if X.n ≤ X.n ∧ X.n ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < X.n then 1 else 0) =
      ∑ k ∈ Finset.Icc (c0 + 1) (X.rkF g0 t0), (if g0 = g ∧ t0 = t ∧ k = X.n then u else 0) := by
  by_cases hg : g = g0 ∧ t = t0
  · obtain ⟨rfl, rfl⟩ := hg
    simp only [le_refl, true_and, and_true, Finset.sum_ite_eq', Finset.mem_Icc]
    split_ifs <;> first | omega | simp
  · rw [if_neg (fun h => hg h.2.2.1), smul_zero, Finset.sum_eq_zero]
    intro k _
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    exact hg ⟨h1.symm, h2.symm⟩

theorem num_mon (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) (g : Fin 2) (e : ZMod d → ℕ → ℕ) (N : ℕ) :
    (∑ t : ZMod d, ∑ k ∈ Finset.Icc 1 (min N (X.rkF g t)),
      e t k • (if k ≤ N ∧ k ≤ X.rkF g t ∧ (g = g0 ∧ t = t0) ∧ c0 < k then 1 else 0)) =
      ∑ k ∈ Finset.Icc (c0 + 1) (X.rkF g0 t0),
        (if g0 = g ∧ 1 ≤ k ∧ k ≤ min N (X.rkF g t0) then e t0 k else 0) := by
  by_cases hg : g0 = g
  · subst hg
    rw [Fintype.sum_eq_single t0]
    · simp only [eq_self_iff_true, true_and, and_true, smul_ite, smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    · intro t ht
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg (fun h => ht h.2.2.1.2), smul_zero]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    all_goals first
      | (intro k _; rw [if_neg (fun h => hg h.1)])
      | (intro t _; exact Finset.sum_eq_zero fun k _ => by rw [if_neg (fun h => hg h.2.2.1.1.symm), smul_zero])


include std in
theorem blockPoly_isWeightedHomogeneous' (b : GlobalTheory d) (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ) :
    IsWeightedHomogeneous (wRowG X idx g0 t0 c0) (b.poly X F)
      (∑ k ∈ Finset.Icc (c0 + 1) (X.rkF g0 t0), b.wt X g0 t0 k) := by
  cases b with
  | ch g t u =>
    exact isWH_deg ((isWH_letter_minorK X F idx std g0 t0 c0 g t).pow u) (num_ch X g0 t0 c0 g t u)
  | bi g t i y =>
    refine isWH_deg (((isWH_letter_minorK X F idx std g0 t0 c0 g t).pow (V.l ^ i * y)).mul
      ((isWH_letter_minorK X F idx std g0 t0 c0 (1 - g) (t + (i : ZMod d))).pow y)) ?_
    simp only [GlobalTheory.wt]
    rw [Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) (num_ch X g0 t0 c0 g t _) (num_ch X g0 t0 c0 (1 - g) (t + (i : ZMod d)) y)
  | mon g e N =>
    refine isWH_deg (IsWeightedHomogeneous.prod _ _ _ fun t _ => isWH_rename _
      (IsWeightedHomogeneous.prod _ _ _ fun k _ =>
        (isWH_minorK_row (g = g0 ∧ t = t0) c0 fun x => wRowG_letter X F idx std g0 t0 c0 g t x).pow (e t k))) ?_
    simp only [GlobalTheory.wt]
    exact num_mon X g0 t0 c0 g e N

end Block

end WeightHomogeneousLetters

end Formalism.L2.FormalSeriesBounds.RF
end
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ChG

section Uniq

variable {K : Type} [Field K] [CharZero K] {τ : Type} [Fintype τ]

theorem exp_unique (y : τ → K) (Ψ : MvPowerSeries τ K) (h0 : MvPowerSeries.constantCoeff Ψ = 1)
    (hd : ∀ w, MvPowerSeries.pderiv (R := K) w Ψ = Ψ * MvPowerSeries.C (y w)) : Ψ = mvExp (linF y) := by
  have step : ∀ (w : τ) (m : τ →₀ ℕ), MvPowerSeries.coeff (m + Finsupp.single w 1) Ψ * ((m w : K) + 1) =
      y w * MvPowerSeries.coeff m Ψ := by
    intro w m
    have h := congrArg (MvPowerSeries.coeff m) (hd w)
    rw [MvPowerSeries.coeff_pderiv, mul_comm Ψ, MvPowerSeries.coeff_C_mul] at h
    exact h
  have key : ∀ (n : ℕ) (m : τ →₀ ℕ), m.degree = n →
      MvPowerSeries.coeff m Ψ = MvPowerSeries.coeff m (mvExp (linF y)) := by
    intro n
    induction n with
    | zero =>
      intro m hm
      have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 hm
      subst hm0
      rw [coeff_zero_mvExp, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    | succ n ih =>
      intro m hm
      obtain ⟨w, hw⟩ : ∃ w, m w ≠ 0 := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        have : m = 0 := Finsupp.ext hcon
        rw [this] at hm
        simp at hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by
        refine ⟨m - Finsupp.single w 1, ?_⟩
        ext x
        by_cases hx : x = w
        · subst hx
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_same]
          omega
        · simp [Ne.symm hx]
      have hdeg : m'.degree = n := by
        rw [map_add (f := _), Finsupp.degree_single] at hm
        omega
      have hne : ((m' w : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m' w)
      have e1 := step w m'
      have e2 := coeff_mvExp_linF_step y w m'
      rw [ih m' hdeg, ← e2] at e1
      exact mul_right_cancel₀ hne e1
  ext m
  exact key _ m rfl

end Uniq

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)

open VP

theorem chi_mul {χ : PS C 1 dd} (hχ : Y.IsChar χ) :
    MvPowerSeries.subst (fun k => Y.B.G.F k) (un1 χ) =
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (un1 χ) *
        MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (un1 χ) := by
  have h := hχ.2.2
  rw [eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst] at h
  rw [subst_singlePointUncurry (cc_F Y), subst_singlePointUncurry (fun _ => cc_X _), subst_singlePointUncurry (fun _ => cc_X _)]
  have h2 : (fun p : Fin 1 × Fin dd => addOf Y.B.G.F (pt C dd 0) (pt C dd 1) p.2) =
      fun p : Fin 1 × Fin dd => Y.B.G.F p.2 := by
    funext p
    exact ev_id _
  rw [h2] at h
  exact h

theorem constantCoeff_pderiv_uncurry (χ : PS C 1 dd) (i : Fin dd) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (R := C) i (un1 χ)) = dlogC χ i := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  have h1 : MvPowerSeries.coeff (Finsupp.single i 1) (un1 χ) = dlogC χ i := by
    show MvPowerSeries.coeff ((Finsupp.single i 1).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) χ = _
    rw [Finsupp.mapDomain_single]
    rfl
  simp [h1]

def Psi (χ : PS C 1 dd) : MvPowerSeries (Fin dd) C := MvPowerSeries.subst (e Y) (un1 χ)

theorem chi_ode {χ : PS C 1 dd} (hχ : Y.IsChar χ) (i : Fin dd) :
    MvPowerSeries.pderiv (R := C) i (Psi Y χ) = Psi Y χ * MvPowerSeries.C (dlogC χ i) := by
  have hFK : ∀ k, Y.B.FK C k = Y.B.G.F k := by
    intro k
    show MvPowerSeries.map (algebraMap C C) (Y.B.G.F k) = _
    rw [Algebra.algebraMap_self, MvPowerSeries.map_id]
    rfl

  have hL : MvPowerSeries.pderiv (R := C) i (Psi Y χ) =
      ∑ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F k)) *
        MvPowerSeries.subst (e Y) (MvPowerSeries.pderiv (R := C) k (un1 χ)) := by
    unfold Psi
    rw [pderiv_subst (og (cc_e Y))]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := expODE Y i k
    rw [hFK] at this
    show MvPowerSeries.pderiv (R := C) i (un1 (Y.ex k)) * _ = _
    rw [this]

  have h := congrArg (fun G => MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) G)) (chi_mul Y hχ)
  beta_reduce at h
  rw [Derivation.leibniz, pderiv_subst (og (cc_F Y)), pderiv_subst (og fun _ => cc_X _), pderiv_subst (og fun _ => cc_X _),
    MvPowerSeries.subst_add (hs (cc_exZero Y)), subst_sum (cc_exZero Y), smul_eq_mul, smul_eq_mul,
    subst_mul (cc_exZero Y), subst_mul (cc_exZero Y), subst_sum (cc_exZero Y), subst_sum (cc_exZero Y)] at h
  have h1 : ∀ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F k) *
      MvPowerSeries.subst (fun k => Y.B.G.F k) (MvPowerSeries.pderiv (R := C) k (un1 χ))) =
      MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F k)) *
        MvPowerSeries.subst (e Y) (MvPowerSeries.pderiv (R := C) k (un1 χ)) := by
    intro k
    rw [subst_mul (cc_exZero Y), subst_subst (cc_F Y) (cc_exZero Y)]
    congr 2
    funext k'
    exact F_exZero Y k'
  have h2 : ∀ k, MvPowerSeries.subst (exZero Y)
      (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd) *
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv (R := C) k (un1 χ))) = 0 := by
    intro k
    rw [MvPowerSeries.pderiv_X_of_ne (fun hh => by simpa using (Prod.ext_iff.1 hh).1), zero_mul,
      subst_zero' (cc_exZero Y)]
  have h3 : ∀ k, MvPowerSeries.subst (exZero Y)
      (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd) *
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv (R := C) k (un1 χ))) = if k = i then MvPowerSeries.C (dlogC χ i) else 0 := by
    intro k
    by_cases hk : k = i
    · subst hk
      rw [MvPowerSeries.pderiv_X_self, one_mul, subst_subst (fun _ => cc_X _) (cc_exZero Y), if_pos rfl]
      have : (fun s : Fin dd => MvPowerSeries.subst (exZero Y) (MvPowerSeries.X ((1 : Fin 2), s) : PS C 2 dd)) =
          fun _ => 0 := by
        funext s
        rw [subst_X (cc_exZero Y)]
        rfl
      rw [this, subst_zeroPt, constantCoeff_pderiv_uncurry]
    · rw [MvPowerSeries.pderiv_X_of_ne (fun hh => hk (Prod.ext_iff.1 hh).2), zero_mul, subst_zero' (cc_exZero Y),
        if_neg hk]
  have h4 : MvPowerSeries.subst (exZero Y)
      (MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (un1 χ)) = Psi Y χ := by
    rw [subst_subst (fun _ => cc_X _) (cc_exZero Y)]
    unfold Psi
    congr 1
    funext s
    rw [subst_X (cc_exZero Y)]
    rfl
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_congr rfl fun k _ => h2 k,
    Finset.sum_congr rfl fun k _ => h3 k, Finset.sum_const_zero, mul_zero, add_zero, Finset.sum_ite_eq', h4] at h
  rw [hL, h]
  simp

theorem cc_Psi {χ : PS C 1 dd} (hχ : Y.IsChar χ) : MvPowerSeries.constantCoeff (Psi Y χ) = 1 := by
  obtain ⟨-, hχ1, -⟩ := hχ
  have hu : ∀ f : PS C 1 dd, MvPowerSeries.constantCoeff (un1 f) = MvPowerSeries.constantCoeff f := by
    intro f
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f = _
    rw [Finsupp.mapDomain_zero]
  have he0 : ∀ k, MvPowerSeries.constantCoeff (e Y k) = 0 := fun k => (hu _).trans (Y.ex_const k)
  have hA : MvPowerSeries.HasSubst (e Y) := MvPowerSeries.hasSubst_of_constantCoeff_zero he0
  unfold Psi
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst hA, finsum_eq_single _ 0]
  · simp [hu, hχ1]
  · intro d hd
    obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod,
      Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs), smul_zero]
    rw [map_pow, he0, zero_pow hs]

theorem chi_exp {χ : PS C 1 dd} (hχ : Y.IsChar χ) : Psi Y χ = mvExp (linF (dlogC χ)) := exp_unique (dlogC χ) (Psi Y χ) (cc_Psi Y hχ) (chi_ode Y hχ)

end ChG

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

variable (Y : FBChart C V O dd)

def exAt (a : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C := fun i => MvPowerSeries.subst a (e Y i)

theorem cc_exAt {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (exAt Y a i) = 0 := by
  unfold exAt
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, cc_e Y i]
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
      rw [map_finsuppProd]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
      show MvPowerSeries.constantCoeff (a s ^ d s) = 0
      rw [map_pow, ha s, zero_pow hs]
    rw [h0, smul_zero]

theorem l_add_at {u v : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0)
    (hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0) (m : Fin dd) :
    MvPowerSeries.subst (addAt Y u v) (l Y m) = MvPowerSeries.subst u (l Y m) + MvPowerSeries.subst v (l Y m) := by
  have h := congrArg (MvPowerSeries.subst (P2 u v)) (l_add Y m)
  have hP := constantCoeff_pair_substitution hu hv
  rw [subst_add' hP, subst_subst (cc_F Y) hP,
    subst_subst (a := fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (fun _ => cc_X _) hP,
    subst_subst (a := fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (fun _ => cc_X _) hP] at h
  have e0 : (fun s : Fin dd => MvPowerSeries.subst (P2 u v) (MvPowerSeries.X ((0 : Fin 2), s) : PS C 2 dd)) = u :=
    funext fun i => subst_X hP _
  have e1 : (fun s : Fin dd => MvPowerSeries.subst (P2 u v) (MvPowerSeries.X ((1 : Fin 2), s) : PS C 2 dd)) = v :=
    funext fun i => subst_X hP _
  rw [e0, e1] at h
  exact h

theorem l_exAt {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (m : Fin dd) :
    MvPowerSeries.subst (exAt Y a) (l Y m) = a m := by
  unfold exAt
  rw [← subst_subst (cc_e Y) ha, lgex, subst_X ha]

theorem e_lAt {P : Fin dd → MvPowerSeries τ C} (hP : ∀ i, MvPowerSeries.constantCoeff (P i) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun m => MvPowerSeries.subst P (l Y m)) (e Y i) = P i := by
  rw [← subst_subst (cc_l Y) hP, exlg, subst_X hP]

theorem ex_add {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    exAt Y (fun m => a m + b m) = addAt Y (exAt Y a) (exAt Y b) := by
  funext i
  have hP := cc_addAt Y (cc_exAt Y ha) (cc_exAt Y hb)
  rw [← e_lAt Y hP i]
  unfold exAt
  congr 1
  funext m
  show a m + b m = MvPowerSeries.subst (addAt Y (exAt Y a) (exAt Y b)) (l Y m)
  rw [l_add_at Y (cc_exAt Y ha) (cc_exAt Y hb), l_exAt Y ha, l_exAt Y hb]

theorem exAt_zero : exAt Y (fun _ : Fin dd => (0 : MvPowerSeries τ C)) = fun _ => 0 := by
  funext i
  ext e'
  simp only [exAt]
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => map_zero _)),
    finsum_eq_zero_of_forall_eq_zero]
  · simp
  · intro d
    by_cases hd : d = 0
    · subst hd
      simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, cc_e Y i]
    · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
      have h0 : (d.prod fun s e => (0 : MvPowerSeries τ C) ^ e) = 0 :=
        Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs)
      rw [h0, map_zero, smul_zero]

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

end Formalism.L2.FormalSeriesBounds
end
end

section

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

theorem keyEig_holds : KeyEigSt := RowTiePKeyEig.keyEig_of RowTiePKeyTeich.teich_holds jointEig_holds

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end
