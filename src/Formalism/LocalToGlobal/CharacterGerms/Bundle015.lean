module

import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.LinearFormDegree.InvFun
public import Formalism.IncomingBounds.Bundle002
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Formalism.IncomingBounds.FlowDegreeBounds.Bundle002
public import Formalism.LocalToGlobal.CharacterGerms.Bundle002
public import Formalism.LocalToGlobal.CharacterGerms.RowTieDefs
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
public import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
public import Formalism.LocalToGlobal.CharacterGerms.Bundle010
import Formalism.LocalToGlobal.CharacterGerms.LemmaMLin
public import Formalism.LocalToGlobal.CharacterGerms.Bundle009
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

theorem finsupp_deg_one {σ : Type} (e : σ →₀ ℕ) (h : e.degree = 1) : ∃ i, e = Finsupp.single i 1 := by
  apply ReciprocityTheory.ChartRestriction.G.LF.InvFun.eq_single_of_degree_eq_one <;> assumption

theorem coeff_alongCv_low {σ : Type} [Fintype σ] {γ : σ → PowerSeries C} {n : ℕ} (hn : 1 ≤ n)
    (hγ : ∀ i, ∀ m < n, PowerSeries.coeff m (γ i) = 0) {f : MvPowerSeries σ C}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff n (alongCv γ f) =
      ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) f * PowerSeries.coeff n (γ i) := by
  have hγ0 : ∀ i, MvPowerSeries.constantCoeff (γ i) = 0 := fun i => by
    have := hγ i 0 (by omega)
    rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
  unfold alongCv
  show MvPowerSeries.coeff (Finsupp.single () n) _ = _
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0),
    finsum_eq_sum_of_support_subset (s := Finset.univ.image fun i : σ => Finsupp.single i 1)]
  · rw [Finset.sum_image (fun a _ b _ h => Finsupp.single_left_injective one_ne_zero h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp : (Finsupp.single i 1 : σ →₀ ℕ).prod (fun s e => γ s ^ e) = γ i := by
      rw [Finsupp.prod_single_index (h := fun s e => γ s ^ e) (pow_zero _), pow_one]
    show MvPowerSeries.coeff (Finsupp.single i 1) f •
      MvPowerSeries.coeff (Finsupp.single () n) ((Finsupp.single i 1 : σ →₀ ℕ).prod fun s e => γ s ^ e) = _
    rw [hp, smul_eq_mul]
    rfl
  · intro e he
    rw [Function.mem_support] at he
    rw [Finset.coe_image, Set.mem_image]
    by_contra hc
    apply he
    have hdeg : e.degree ≠ 1 := fun h => by
      obtain ⟨i, hi⟩ := finsupp_deg_one e h
      exact hc ⟨i, by simp, hi.symm⟩
    by_cases h0 : e.degree = 0
    · rw [Finsupp.degree_eq_zero_iff] at h0
      rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
    · have h2 : 2 ≤ e.degree := by omega
      have hdvd : (PowerSeries.X : PowerSeries C) ^ (n * e.degree) ∣ e.prod fun s m => γ s ^ m := by
        unfold Finsupp.prod
        rw [Finsupp.degree_apply, pow_mul, ← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_dvd_prod_of_dvd
        intro i _
        exact pow_dvd_pow_of_dvd (PowerSeries.X_pow_dvd_iff.2 (hγ i)) _
      have hz : PowerSeries.coeff n (e.prod fun s m => γ s ^ m) = 0 :=
        PowerSeries.X_pow_dvd_iff.1 hdvd n (by nlinarith)
      show MvPowerSeries.coeff e f • PowerSeries.coeff n (e.prod fun s m => γ s ^ m) = 0
      rw [hz, smul_zero]

theorem coeff_tyS_lt {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) (s : ℕ) (ha : ∀ i < s, a i = 0) (m : ℕ) (hm : m < l ^ s) :
    PowerSeries.coeff m (tyS l a) = 0 := by
  simp only [tyS, PowerSeries.coeff_mk]
  apply Finset.sum_eq_zero
  intro t _
  split_ifs with ht
  · apply ha
    by_contra hc
    push_neg at hc
    have : l ^ s ≤ l ^ t := Nat.pow_le_pow_right (by omega) hc
    omega
  · rfl

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem val_nonneg_leading_coeff_of_mem_tySet (V : VF C) (g : Fin 2)
    (hlin : ∀ i (μ : κ →₀ ℕ), μ.degree ≤ 1 →
      MvPowerSeries.coeff μ (X.lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries κ C))
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (hsat : ∃ w : κ → I g → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (hmis : ∀ (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q → V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q)))
    (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) (s : ℕ) (h0 : ∀ i < s, x i = 0) (n : I g ⊕ JJ I g) :
    V.Ge 0 (x s n) := by
  have hl2 := V.l_prime.two_le
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hx
  obtain ⟨w, hw, huw⟩ := hsat
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hlin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hlg1 : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (X.lg i) = if j = i then 1 else 0 := fun i j => by
    rw [hlin i _ (by rw [Finsupp.degree_single]), MvPowerSeries.coeff_X]
    by_cases hji : j = i
    · rw [hji, if_pos rfl, if_pos rfl]
    · rw [if_neg hji, if_neg]
      intro h
      exact hji (Finsupp.single_left_injective one_ne_zero h)
  have hpos : 1 ≤ V.l ^ s := Nat.one_le_pow _ _ (by omega)
  have hlow : ∀ (m : ℕ) (hm1 : 1 ≤ m), (∀ i, ∀ m' < m, PowerSeries.coeff m' (γ i) = 0) → ∀ i,
      PowerSeries.coeff m (γ i) = ∑ c : I g, X.u g c i * PowerSeries.coeff m (tyS V.l fun s => x s (Sum.inl c)) := by
    intro m hm1 hm i
    have e1 := coeff_alongCv_low hm1 hm (hlg0 i)

    rw [h1 i, map_sum] at e1
    simp only [hlg1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      PowerSeries.coeff_smul, smul_eq_mul] at e1
    exact e1.symm
  have hord : ∀ m, m < V.l ^ s → ∀ i, PowerSeries.coeff m (γ i) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm i
      by_cases hm0 : m = 0
      · rw [hm0, PowerSeries.coeff_zero_eq_constantCoeff_apply]
        exact (hγ i).1
      · rw [hlow m (by omega) (fun i m' hm' => ih m' hm' (by omega) i) i]
        apply Finset.sum_eq_zero
        intro c _
        rw [coeff_tyS_lt hl2 _ s (fun i hi => by rw [h0 i hi]; rfl) m hm, mul_zero]
  have hord' : ∀ i, ∀ m < V.l ^ s, PowerSeries.coeff m (γ i) = 0 := fun i m hm => hord m hm i
  have hlead : ∀ i, PowerSeries.coeff (V.l ^ s) (γ i) = ∑ c : I g, X.u g c i * x s (Sum.inl c) := by
    intro i
    rw [hlow _ hpos hord' i]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [coeff_tyS_pow hl2]
  have hinl : ∀ c', x s (Sum.inl c') = ∑ i, PowerSeries.coeff (V.l ^ s) (γ i) * w i c' := by
    intro c'
    simp only [hlead, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ c : I g, ∑ i, X.u g c i * x s (Sum.inl c) * w i c' = (if c = c' then 1 else 0) * x s (Sum.inl c) := by
      intro c
      rw [← huw c c', Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by ring
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hinlInt : ∀ c', V.Ge 0 (x s (Sum.inl c')) := by
    intro c'
    rw [hinl c']
    exact VF.Ge.sum fun i _ => ((hγ i).2 _).mul_int (hw i c')
  cases n with
  | inl c' => exact hinlInt c'
  | inr q =>
    have e2 := congrArg (PowerSeries.coeff (V.l ^ s)) (h2 q)

    rw [coeff_tyS_pow hl2, map_add (f := _), map_sub, coeff_alongCv_low hpos hord' (X.constantCoeff_sg hh _), map_sum] at e2
    have e3 : ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) (X.sg (X.u (1 - g) q)) * PowerSeries.coeff (V.l ^ s) (γ i) =
        ∑ c : I g, X.sg1 (X.u g c) (X.u (1 - g) q) * x s (Sum.inl c) := by
      simp only [hlead, sg1, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring
    have e4 : ∀ c : I g, PowerSeries.coeff (V.l ^ s) (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0) =
        if X.ty g c = X.ty (1 - g) q then X.sg1 (X.u g c) (X.u (1 - g) q) * x s (Sum.inl c) else 0 := by
      intro c
      split_ifs
      · rw [PowerSeries.coeff_smul, coeff_tyS_pow hl2, smul_eq_mul]
      · rw [map_zero]
    simp only [e4] at e2
    rw [e3, sub_add, ← Finset.sum_sub_distrib] at e2
    rw [e2]
    refine ((hlam q).2 _).sub (VF.Ge.sum fun c _ => ?_)
    split_ifs with hc
    · rw [sub_self]
      exact VF.Ge.zero 0
    · rw [sub_zero]
      exact (hmis c q hc).mul_int (hinlInt c)

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

namespace VP

theorem cc_subst_eq {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  set c := MvPowerSeries.constantCoeff f with hc
  have hg : MvPowerSeries.constantCoeff (f - algebraMap C (MvPowerSeries σ C) c) = 0 := by
    simp [hc, MvPowerSeries.algebraMap_apply]
  have hf : f = algebraMap C (MvPowerSeries σ C) c + (f - algebraMap C (MvPowerSeries σ C) c) := by
    ring
  have h1 : MvPowerSeries.subst a (algebraMap C (MvPowerSeries σ C) c) =
      algebraMap C (MvPowerSeries τ C) c := by
    rw [← MvPowerSeries.coe_substAlgHom hs]
    exact (MvPowerSeries.substAlgHom hs).commutes c
  rw [hf, MvPowerSeries.subst_add hs, map_add (f := _), h1, constantCoeff_subst_zero ha hg]
  simp [MvPowerSeries.algebraMap_apply]

private theorem jetAt0_zero_left' {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 (0 : MvPolynomial σ C) G = 0 := by
  simp [jetAt0]

private theorem jetAt0_finset_sum_left {σ ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ C)
    (G : MvPowerSeries σ C) : jetAt0 (∑ j ∈ s, P j) G = ∑ j ∈ s, jetAt0 (P j) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jetAt0_zero_left']
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, tpjet_jetAt0_add, ih]

theorem jet_lin {σ ι : Type} [Fintype ι] (e : ι → σ) (q : MvPolynomial σ C) (c : ι → C) (G : MvPowerSeries σ C) :
    jetAt0 (q * ∑ w, MvPolynomial.C (c w) * MvPolynomial.X (e w)) G =
      jetAt0 q (∑ w, c w • MvPowerSeries.pderiv (R := C) (e w) G) := by
  rw [Finset.mul_sum, jetAt0_finset_sum_left, jet_sum_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← mul_assoc, jet_mul_X, jet_mul_C, jet_smul_right, dVar_eq_pderiv]

variable {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)}

end VP

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds PartialDerivEval

variable {C : Type} [Field C]

def RawChart.expG {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} (X : RawChart C d I κ) (g : Fin 2)
    (i : κ) : MvPowerSeries (I g) C :=
  MvPowerSeries.subst (fun j : κ => ∑ c : I g, X.u g c j • (MvPowerSeries.X c : MvPowerSeries (I g) C)) (X.ex i)

namespace RowTiePCEq

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem hasSubst_X (g : Fin 2) : MvPowerSeries.HasSubst
    (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _

theorem upG_eq (g : Fin 2) (F : MvPowerSeries (I g) C) :
    upG g F = MvPowerSeries.substAlgHom (hasSubst_X (C := C) g) F := by
  rw [MvPowerSeries.substAlgHom_apply]
  rfl

theorem upG_const (g : Fin 2) {F : MvPowerSeries (I g) C} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (upG g F) = 0 :=
  constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) hF

theorem upG_subst {σ : Type} [Finite σ] (g : Fin 2) {a : σ → MvPowerSeries (I g) C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) :
    upG g (MvPowerSeries.subst a f) = MvPowerSeries.subst (fun s => upG g (a s)) f := by
  unfold upG
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) (hasSubst_X g)]

theorem upG_X (g : Fin 2) (c : I g) :
    upG g (MvPowerSeries.X c : MvPowerSeries (I g) C) = MvPowerSeries.X (⟨g, c⟩ : WV I) := by
  unfold upG
  rw [MvPowerSeries.subst_X (hasSubst_X g)]

theorem intS_upG {V : VF C} (g : Fin 2) {F : MvPowerSeries (I g) C} (hF : IntS V F) : IntS V (upG g F) :=
  IntS.subst (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => intS_X _) hF

theorem lin_const {κ : Type} (X : RawChart C d I κ) (g : Fin 2) (j : κ) :
    MvPowerSeries.constantCoeff (∑ c : I g, X.u g c j • (MvPowerSeries.X c : MvPowerSeries (I g) C)) = 0 := by

  rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_smul,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X, mul_zero]

theorem expPt_eq {κ : Type} [Fintype κ] (X : RawChart C d I κ) (g : Fin 2) (i : κ) :
    X.expPt g i = upG g (X.expG g i) := by
  unfold RawChart.expG
  rw [upG_subst g (lin_const X g)]
  unfold RawChart.expPt
  congr 1
  funext j

  rw [upG_eq, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, ← upG_eq, upG_X]

def tW (t : ∀ g, I g → MvPowerSeries (I g) C) : WV I → MvPowerSeries (WV I) C := fun w => upG w.1 (t w.1 w.2)

theorem tW_const {t : ∀ g, I g → MvPowerSeries (I g) C} (ht : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0) :
    ∀ w, MvPowerSeries.constantCoeff (tW t w) = 0 := fun w => upG_const _ (ht _ _)

theorem subst_tW_upG {t : ∀ g, I g → MvPowerSeries (I g) C} (ht : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0)
    (g : Fin 2) (f : MvPowerSeries (I g) C) :
    MvPowerSeries.subst (tW t) (upG g f) = upG g (MvPowerSeries.subst (t g) f) := by
  rw [upG_subst g (ht g) f]
  show MvPowerSeries.subst (tW t) (MvPowerSeries.subst _ f) = _
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_X g)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (tW_const ht))]
  congr 1
  funext c
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero (tW_const ht))]
  rfl

theorem coeff_toLeaf {V : VF C} {J : Fin 2 → Type} [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g))
    (g : Fin 2) (a a' : ZMod d) (F : MvPowerSeries (WV I) C) (μ : WV I →₀ ℕ) :
    MvPowerSeries.coeff μ (toLeaf G g a a' F) =
      if ∀ w ∈ μ.support, OnLeafV G g a a' w then MvPowerSeries.coeff μ F else 0 := rfl

def toLeafL {V : VF C} {J : Fin 2 → Type} [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g))
    (g : Fin 2) (a a' : ZMod d) : MvPowerSeries (WV I) C →ₗ[C] MvPowerSeries (WV I) C where
  toFun := toLeaf G g a a'
  map_add' F F' := by
    ext μ
    rw [coeff_toLeaf, map_add (f := _), map_add (f := _), coeff_toLeaf, coeff_toLeaf]
    split_ifs <;> simp
  map_smul' r F := by
    ext μ
    rw [coeff_toLeaf, RingHom.id_apply, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_toLeaf]
    split_ifs <;> simp

theorem toLeaf_X_off {V : VF C} {J : Fin 2 → Type} [∀ g, Fintype (J g)] (G : ∀ g, Cart V d (I g) (J g))
    (g : Fin 2) (a a' : ZMod d) (w : WV I) (hw : ¬ OnLeafV G g a a' w) :
    toLeaf G g a a' (MvPowerSeries.X w : MvPowerSeries (WV I) C) = 0 := by
  ext μ
  rw [coeff_toLeaf, MvPowerSeries.coeff_X, map_zero]
  split_ifs with h1 h2
  · exfalso
    apply hw
    apply h1
    rw [h2]
    simp
  · rfl
  · rfl

theorem dVar_hLf {κ : Type} [Fintype κ] {V : VF C} (X : RawChart C d I κ) (H : ∀ g, X.CartHyp V g)
    (g : Fin 2) (a a' : ZMod d) (w : WV I) (hw : X.OnLf g a a' w) :
    dVar w (X.hLf g a a') = toLeaf (fun g => RawChart.cart (H g)) g a a' (dVar w X.hRow) := by
  ext μ
  rw [coeff_toLeaf]
  have key : (∀ x ∈ (μ + Finsupp.single w 1).support, X.OnLf g a a' x) ↔ ∀ x ∈ μ.support, X.OnLf g a a' x := by
    constructor
    · intro h x hx
      apply h
      rw [Finsupp.mem_support_iff] at hx ⊢
      rw [Finsupp.add_apply]
      omega
    · intro h x hx
      by_cases hxw : x = w
      · exact hxw ▸ hw
      · apply h
        rw [Finsupp.mem_support_iff] at hx ⊢
        rwa [Finsupp.add_apply, Finsupp.single_eq_of_ne hxw, add_zero] at hx
  show ((μ w + 1 : ℕ) : C) * (if ∀ x ∈ (μ + Finsupp.single w 1).support, X.OnLf g a a' x then
      MvPowerSeries.coeff (μ + Finsupp.single w 1) X.hRow else 0) =
    if ∀ x ∈ μ.support, X.OnLf g a a' x then ((μ w + 1 : ℕ) : C) * MvPowerSeries.coeff (μ + Finsupp.single w 1) X.hRow
      else 0
  by_cases hc : ∀ x ∈ μ.support, X.OnLf g a a' x
  · rw [if_pos (key.2 hc), if_pos hc]
  · rw [if_neg (fun h => hc (key.1 h)), if_neg hc, mul_zero]

end RowTiePCEq

open RowTiePCEq

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

variable {C : Type} [Field C]

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem typ_link (V : VF C) (g : Fin 2) {L : ℕ → I g ⊕ JJ I g → C} (hL : L ∈ X.AllSet V g)
    (h0 : ∀ n k, (¬ ∃ s, V.l ^ s = n) → L n k = 0) :
    (fun s k => L (V.l ^ s) k) ∈ X.TySet V g := by
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hL
  have key : ∀ k, tyS V.l (fun s => L (V.l ^ s) k) = PowerSeries.mk (fun n => L n k) := by
    intro k
    apply tyS_eq V.l_prime.two_le
    · intro s; rw [PowerSeries.coeff_mk]
    · intro m hm
      rw [PowerSeries.coeff_mk]
      exact h0 m k (fun ⟨s, hs⟩ => hm s hs)
  refine ⟨γ, lam, hγ, hlam, ?_, ?_⟩
  · intro i; simp only [key]; exact h1 i
  · intro q; simp only [key]; exact h2 q

end RawChart

end Formalism.L2.FormalSeriesBounds
end
end
