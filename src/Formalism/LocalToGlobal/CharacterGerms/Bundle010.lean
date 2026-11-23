module

public import Formalism.FrobeniusBaseCase.Statement
public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Formalism.LocalToGlobal.CharacterGerms.LemmaMLin
public import Formalism.LocalToGlobal.CharacterGerms.Bundle006
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (OrdGE)

variable {C : Type} [Field C] {σ τ : Type}

theorem jet_smul_right (P : MvPolynomial σ C) (a : C) (G : MvPowerSeries σ C) :
    jetAt0 P (a • G) = a * jetAt0 P G := by
  simp only [jetAt0, map_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem jet_sum_right {ι : Type} (s : Finset ι) (P : MvPolynomial σ C)
    (G : ι → MvPowerSeries σ C) : jetAt0 P (∑ j ∈ s, G j) = ∑ j ∈ s, jetAt0 P (G j) := by

  simp only [jetAt0, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem jet_C (a : C) (G : MvPowerSeries σ C) :
    jetAt0 (MvPolynomial.C a) G = a * constantCoeff G := by
  by_cases ha : a = 0
  · subst ha
    simp [jetAt0]
  · simp [jetAt0, MvPolynomial.support_C, ha, mfact, MvPowerSeries.coeff_zero_eq_constantCoeff]

theorem mfact_add_single (m : σ →₀ ℕ) (x : σ) :
    mfact (m + Finsupp.single x 1) = (m x + 1) * mfact m := by
  unfold mfact
  set s := insert x m.support with hs
  have hsub : (m + Finsupp.single x 1).support ⊆ s := by
    intro y hy
    rcases Finset.mem_union.1 (Finsupp.support_add hy) with h | h
    · exact Finset.mem_insert_of_mem h
    · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h
      rw [h]
      exact Finset.mem_insert_self _ _
  rw [Finsupp.prod_of_support_subset (m + Finsupp.single x 1) hsub _ (fun _ _ => Nat.factorial_zero),
    Finsupp.prod_of_support_subset m (Finset.subset_insert _ _) _ (fun _ _ => Nat.factorial_zero)]
  have hx : x ∈ s := Finset.mem_insert_self _ _
  rw [← Finset.mul_prod_erase s _ hx, ← Finset.mul_prod_erase s (fun y => (m y).factorial) hx]
  have hrest : ∏ y ∈ s.erase x, ((m + Finsupp.single x 1 : σ →₀ ℕ) y).factorial = ∏ y ∈ s.erase x, (m y).factorial :=
    Finset.prod_congr rfl fun y hy => by
      rw [Finset.mem_erase] at hy
      simp [Finsupp.single_apply, Ne.symm hy.1]
  rw [hrest]
  simp [Nat.factorial_succ]
  ring

theorem jet_mul_X (p : MvPolynomial σ C) (x : σ) (G : MvPowerSeries σ C) :
    jetAt0 (p * MvPolynomial.X x) G = jetAt0 p (dVar x G) := by
  unfold jetAt0
  rw [MvPolynomial.support_mul_X, Finset.sum_map]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hd : MvPowerSeries.coeff n (dVar x G) =
      ((n x + 1 : ℕ) : C) * MvPowerSeries.coeff (n + Finsupp.single x 1) G := rfl
  simp only [addRightEmbedding_apply]
  rw [MvPolynomial.coeff_mul_X, mfact_add_single, hd]
  push_cast
  ring

theorem jet_mul_C (p : MvPolynomial σ C) (a : C) (G : MvPowerSeries σ C) :
    jetAt0 (p * MvPolynomial.C a) G = a * jetAt0 p G := by
  rw [mul_comm p]
  unfold jetAt0
  rw [Finset.mul_sum]
  refine (Finset.sum_subset ?_ ?_).trans (Finset.sum_congr rfl fun m _ => ?_)
  · intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hm
    rw [h, mul_zero]
  · intro m _ hm
    rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]
  · rw [MvPolynomial.coeff_C_mul]
    ring

theorem coeff_mvExp_partial {h : MvPowerSeries σ C} (hh : OrdGE 1 h) (N : ℕ) (m : σ →₀ ℕ)
    (hm : m.degree ≤ N) :
    coeff m (mvExp h) = coeff m (∑ k ∈ Finset.range (N + 1), ((k.factorial : C)⁻¹) • h ^ k) := by
  have hpow : ∀ k, OrdGE k (h ^ k) := by
    intro k
    have := ordGE_finset_prod (Finset.range k) (fun _ => 1) (fun _ => h) (fun _ _ => hh)
    simpa [Finset.prod_const, Finset.card_range] using this
  show (∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C)) = _

  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_subset (Finset.range_mono (by omega : m.degree + 1 ≤ N + 1)) ?_]
  · exact Finset.sum_congr rfl fun k _ => by rw [div_eq_inv_mul]
  · intro k hk hk'
    rw [Finset.mem_range] at hk hk'
    rw [hpow k m (by omega), zero_div]

theorem subst_mvExp [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s))
    {h : MvPowerSeries σ C} (hh : OrdGE 1 h) : subst a (mvExp h) = mvExp (subst a h) := by
  ext e
  have hsh : OrdGE 1 (subst a h) := ordGE_subst ha hh
  rw [coeff_subst_congr ha (F := mvExp h)
      (G := ∑ k ∈ Finset.range (e.degree + 1), ((k.factorial : C)⁻¹) • h ^ k) (N := e.degree)
      (fun d hd => coeff_mvExp_partial hh e.degree d hd) e le_rfl,
    coeff_mvExp_partial hsh e.degree e le_rfl]
  congr 1

  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_of_ordGE ha), map_sum]
  simp only [map_smul, map_pow]

end Formalism.L2.FormalSeriesBounds
end
end

section

namespace Formalism.L2.FormalSeriesBounds

theorem germIAll_holds : GermIAllSt := fun _ _ _ _ _ _ _ _ Y => germI_holds Y

end Formalism.L2.FormalSeriesBounds
end

section

set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace LogEx

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries PartialDerivEval

section Law

variable {C : Type} [Field C] [CharZero C] {d : ℕ} (G : FGLaw C d)

theorem constant_zero_zero_point {n : ℕ} (P : Pt C n d) (hP : ∀ j, constantCoeff (P j) = 0) :
    Z0 (![0, P] : Fin 2 → Pt C n d) := by
  intro k i; fin_cases k
  · simp
  · exact hP i

theorem coordinate_point_constantCoeff {n : ℕ} (k : Fin n) : ∀ j, constantCoeff (pt C d k j) = 0 := fun j => z0_pt k j

theorem eval_eval_pair {m n : ℕ} {a b : Pt C m d} (hab : Z0 (![a, b] : Fin 2 → Pt C m d)) {E : Fin m → Pt C n d}
    (hE : Z0 E) {a' b' : Pt C n d} (ha : ∀ i, ev E (a i) = a' i) (hb : ∀ i, ev E (b i) = b' i) (f : PS C 2 d) :
    ev E (ev ![a, b] f) = ev ![a', b'] f := by
  rw [ev_ev hab hE]
  congr 1
  funext k i
  fin_cases k
  · exact ha i
  · exact hb i

theorem eval_eval_single {m n : ℕ} {a : Pt C m d} (ha0 : Z0 (![a] : Fin 1 → Pt C m d)) {E : Fin m → Pt C n d} (hE : Z0 E)
    {a' : Pt C n d} (ha : ∀ i, ev E (a i) = a' i) (f : PS C 1 d) : ev E (ev ![a] f) = ev ![a'] f := by
  rw [ev_ev ha0 hE]
  congr 1
  funext k i
  fin_cases k
  exact ha i

theorem ev_self1 (g : PS C 1 d) : ev (n := 1) ![pt C d 0] g = g := by
  unfold ev
  have h : (fun p : Fin 1 × Fin d => (![pt C d 0] : Fin 1 → Pt C 1 d) p.1 p.2) = X := by
    funext p
    obtain ⟨k, j⟩ := p
    fin_cases k
    rfl
  rw [h, subst_self]
  rfl

theorem F_0P {n : ℕ} (P : Pt C n d) (hP : ∀ j, constantCoeff (P j) = 0) (a : Fin d) :
    ev ![0, P] (G.F a) = P a := by
  have h := congrArg (ev (![P] : Fin 1 → Pt C n d)) (G.unit a)
  rw [ev_ev (constant_zero_zero_point (pt C d 0) (coordinate_point_constantCoeff 0)) (z0_1 P hP), ev_X (z0_1 P hP)] at h
  have e : (fun k i => ev (![P] : Fin 1 → Pt C n d) ((![0, pt C d 0] : Fin 2 → Pt C 1 d) k i)) =
      (![0, P] : Fin 2 → Pt C n d) := by
    funext k i
    fin_cases k
    · exact ev_zero (z0_1 P hP)
    · exact ev_X (z0_1 P hP) 0 i
  rw [e] at h
  exact h

theorem group_law_zero_right {n : ℕ} (P : Pt C n d) (hP : ∀ j, constantCoeff (P j) = 0) (a : Fin d) :
    ev ![P, 0] (G.F a) = P a := by
  rw [← G.comm a, eval_eval_pair (z0_pp 1 0) (z0_p0 P hP) (a' := 0) (b' := P)
    (fun i => ev_X (z0_p0 P hP) 1 i) (fun i => ev_X (z0_p0 P hP) 0 i)]
  exact F_0P G P hP a

def Mm (j k : Fin d) : PS C 1 d :=
  ev (n := 1) ![pt C d 0, 0] (pderiv (R := C) ((1 : Fin 2), k) (G.F j))

theorem constant_zero_first_zero : Z0 (![pt C d 0, 0] : Fin 2 → Pt C 1 d) := z0_p0 _ (coordinate_point_constantCoeff 0)

theorem cc_Mm (j k : Fin d) : constantCoeff (Mm G j k) = if j = k then 1 else 0 := by
  rw [Mm, constantCoeff_ev constant_zero_first_zero]
  have h := congrArg (pderiv (R := C) ((0 : Fin 1), k)) (G.unit j)
  have hchain := Formalism.G.LogCR.pderiv_subst
    (a := fun p : Fin 2 × Fin d => (![0, pt C d 0] : Fin 2 → Pt C 1 d) p.1 p.2)
    (fun p => constant_zero_zero_point (pt C d 0) (coordinate_point_constantCoeff 0) p.1 p.2)
    (G.F j) ((0 : Fin 1), k)
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at hchain
  unfold ev at h
  rw [hchain] at h
  rw [Finset.sum_eq_zero (fun c _ => by
      rw [show ((![0, pt C d 0] : Fin 2 → Pt C 1 d) 0 c) = 0 from rfl, map_zero, mul_zero]), zero_add,
    Finset.sum_eq_single k] at h
  · rw [show ((![0, pt C d 0] : Fin 2 → Pt C 1 d) 1 k) = X ((0 : Fin 1), k) from rfl, pderiv_X_self,
      mul_one] at h
    change ev ![0, pt C d 0] (pderiv (R := C) ((1 : Fin 2), k) (G.F j)) = _ at h
    have h2 := congrArg constantCoeff h
    rw [constantCoeff_ev (constant_zero_zero_point (pt C d 0) (coordinate_point_constantCoeff 0))] at h2
    rw [h2]
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [pderiv_X_of_ne (by simp [hjk]), if_neg hjk, map_zero]
  · intro c _ hc
    rw [show ((![0, pt C d 0] : Fin 2 → Pt C 1 d) 1 c) = X ((0 : Fin 1), c) from rfl,
      pderiv_X_of_ne (by simp [hc]), mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

def MM : Matrix (Fin d) (Fin d) (PS C 1 d) := Matrix.of fun j k => Mm G j k

theorem MM_cc : (constantCoeff : PS C 1 d →+* C).mapMatrix (MM G) = 1 := by
  ext j k
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, MM, Matrix.of_apply, cc_Mm, Matrix.one_apply]

theorem MM_det : IsUnit (MM G).det := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, MM_cc, Matrix.det_one]
  exact isUnit_one

def NN : Matrix (Fin d) (Fin d) (PS C 1 d) := (MM G)⁻¹

theorem MM_NN : MM G * NN G = 1 := Matrix.mul_nonsing_inv _ (MM_det G)

theorem pderiv_eval_single {n : ℕ} (P : Pt C n d) (hP : ∀ j, constantCoeff (P j) = 0) (g : PS C 1 d) (q : Fin n × Fin d) :
    pderiv (R := C) q (ev ![P] g) =
      ∑ b, ev ![P] (pderiv (R := C) ((0 : Fin 1), b) g) * pderiv (R := C) q (P b) := by
  unfold ev
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 1 × Fin d => (![P] : Fin 1 → Pt C n d) p.1 p.2)
    (fun p => z0_1 P hP p.1 p.2) g q, Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

theorem sum_d_pt_self {n : ℕ} (k : Fin n) (f : Fin d → PS C n d) (q : Fin d) :
    ∑ b, f b * pderiv (R := C) (k, q) (pt C d k b) = f q := by
  rw [Finset.sum_eq_single q]
  · show f q * pderiv (R := C) _ (X (k, q)) = _
    rw [pderiv_X_self, mul_one]
  · intro b _ hb
    show f b * pderiv (R := C) _ (X (k, b)) = 0
    rw [pderiv_X_of_ne (by simp [hb]), mul_zero]
  · intro h; exact absurd (Finset.mem_univ q) h

theorem sum_d_pt_other {n : ℕ} (k k' : Fin n) (hk : k ≠ k') (f : Fin d → PS C n d) (q : Fin d) :
    ∑ b, f b * pderiv (R := C) (k', q) (pt C d k b) = 0 :=
  Finset.sum_eq_zero fun b _ => by
    show f b * pderiv (R := C) _ (X (k, b)) = 0
    rw [pderiv_X_of_ne (by simp [hk]), mul_zero]

theorem eval_group_law_at_zero (h : PS C 1 d) : ev (n := 1) ![pt C d 0, 0] (ev (n := 2) ![G.F] h) = h := by
  rw [eval_eval_single (z0_1 G.F G.const) constant_zero_first_zero (a' := pt C d 0) (fun b => group_law_zero_right G (pt C d 0) (coordinate_point_constantCoeff 0) b), ev_self1]

theorem vec_cancel (u : Fin d → PS C 1 d) (a : Fin d) :
    ∑ k, (∑ c, Mm G c k * u c) * NN G k a = u a := by
  have h : ∀ c, ∑ k, Mm G c k * NN G k a = if c = a then 1 else 0 := fun c => by
    have := congrFun (congrFun (MM_NN G) c) a
    simp only [Matrix.mul_apply, Matrix.one_apply, MM, Matrix.of_apply] at this
    exact this
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have e : ∀ c, ∑ k, Mm G c k * u c * NN G k a = u c * ∑ k, Mm G c k * NN G k a := fun c => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  simp only [e, h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Law

end LogEx

end Formalism.L2.FormalSeriesBounds
end
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

def up (m : ℕ) : Fin m × Fin dd → Fin (m + 1) × Fin dd := fun p => (p.1.succ, p.2)

theorem up_inj (m : ℕ) : Function.Injective (up (dd := dd) m) := by
  intro a b h
  simp only [up, Prod.mk.injEq, Fin.succ_inj] at h
  exact Prod.ext h.1 h.2

def rz (m : ℕ) : Fin (m + 1) → Pt C m dd := Fin.cons 0 (fun k => pt C dd k)

theorem constant_zero_restrict_points (m : ℕ) : Z0 (rz (C := C) (dd := dd) m) := by
  intro k i
  refine Fin.cases ?_ (fun k => ?_) k
  · show MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin m × Fin dd) C) = 0
    simp
  · exact MvPowerSeries.constantCoeff_X (R := C) (k, i)

theorem rz_zero (m : ℕ) (i : Fin dd) : rz (C := C) (dd := dd) m 0 i = 0 := rfl

theorem up_ne_zero (m : ℕ) (i : Fin dd) : ((0 : Fin (m + 1)), i) ∉ Set.range (up (dd := dd) m) := by
  rintro ⟨p, hp⟩
  exact Fin.succ_ne_zero _ (congrArg Prod.fst hp)

theorem coeff_rz (m : ℕ) (f : PS C (m + 1) dd) (ν : Fin m × Fin dd →₀ ℕ) :
    coeff ν (ev (rz m) f) = coeff (ν.mapDomain (up m)) f := by
  unfold ev
  rw [coeff_subst (hasSubst_ev (constant_zero_restrict_points m)), finsum_eq_single _ (ν.mapDomain (up m))]
  · rw [Finsupp.prod_mapDomain_index_inj (up_inj m)]
    have e : (ν.prod fun t e => (fun p : Fin (m + 1) × Fin dd => rz (C := C) (dd := dd) m p.1 p.2) (up m t) ^ e) =
        monomial ν (1 : C) := by
      have h1 := monomial_eq (R := C) ν (fun _ => (1 : C))
      simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
      rw [Finsupp.prod, h1]
      rfl
    rw [e, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  · intro d hd
    by_cases hx : ∃ j, d ((0 : Fin (m + 1)), j) ≠ 0
    · obtain ⟨j, hj⟩ := hx
      rw [Finsupp.prod, Finset.prod_eq_zero (i := ((0 : Fin (m + 1)), j)) (Finsupp.mem_support_iff.2 hj)
        (by show (rz (C := C) (dd := dd) m 0 j) ^ _ = 0; rw [rz_zero]; exact zero_pow hj),
        map_zero, smul_zero]
    · push_neg at hx
      have hsub : ↑d.support ⊆ Set.range (up (dd := dd) m) := by
        intro s hs
        obtain ⟨s1, s2⟩ := s
        have hs1 : s1 ≠ 0 := by
          rintro rfl
          exact (Finsupp.mem_support_iff.1 hs) (hx s2)
        exact ⟨(s1.pred hs1, s2), by simp [up, Fin.succ_pred]⟩
      set e := Finsupp.comapDomain (up m) d ((up_inj m).injOn) with he
      have hde : e.mapDomain (up m) = d := Finsupp.mapDomain_comapDomain _ (up_inj m) d hsub
      have hne : e ≠ ν := by
        intro h; apply hd; rw [← hde, h]
      rw [← hde, Finsupp.prod_mapDomain_index_inj (up_inj m)]
      have e2 : (e.prod fun t k => (fun p : Fin (m + 1) × Fin dd => rz (C := C) (dd := dd) m p.1 p.2) (up m t) ^ k) =
          monomial e (1 : C) := by
        have h1 := monomial_eq (R := C) e (fun _ => (1 : C))
        simp only [one_pow, Finsupp.prod, Finset.prod_const_one, one_smul] at h1
        rw [Finsupp.prod, h1]
        rfl
      rw [e2, coeff_monomial, if_neg (Ne.symm hne), smul_zero]

theorem coeff_iter_pderiv {σ : Type} (q : σ) (L : ℕ) (f : MvPowerSeries σ C) (n : σ →₀ ℕ) :
    coeff n ((pderiv (R := C) q)^[L] f) =
      coeff (n + L • Finsupp.single q 1) f * ∏ r ∈ Finset.range L, ((n q : C) + r + 1) := by
  induction L generalizing f with
  | zero => simp
  | succ L ih =>
    have h1 : n + (L + 1) • Finsupp.single q 1 = n + L • Finsupp.single q 1 + Finsupp.single q 1 := by
      rw [add_smul, one_smul, add_assoc]
    rw [Function.iterate_succ_apply, ih, coeff_pderiv, Finset.prod_range_succ, h1]
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    ring

theorem coeff_rz_iter (m : ℕ) (i : Fin dd) (L : ℕ) (f : PS C (m + 1) dd) (ν : Fin m × Fin dd →₀ ℕ) :
    coeff ν (ev (rz m) ((pderiv (R := C) ((0 : Fin (m + 1)), i))^[L] f)) =
      (L.factorial : C) * coeff (Finsupp.single ((0 : Fin (m + 1)), i) L + ν.mapDomain (up m)) f := by
  rw [coeff_rz, coeff_iter_pderiv, Finsupp.mapDomain_notin_range _ _ (up_ne_zero m i)]
  simp only [Nat.cast_zero, zero_add]
  rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, Finsupp.smul_single_one,
    add_comm (Finsupp.mapDomain (up m) ν)]
  push_cast
  ring

end Formalism.L2.FormalSeriesBounds.FunEq
end
end
