module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle002
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogInv
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle009

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

section Int

variable (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]

def Ig (σ : Type) : Subring (MvPowerSeries σ k) := (MvPowerSeries.map (σ := σ) (algebraMap R k)).range

variable {R k}

theorem ig_map {σ : Type} (f : MvPowerSeries σ R) : MvPowerSeries.map (algebraMap R k) f ∈ Ig R k σ := RingHom.mem_range.mpr ⟨f, rfl⟩

theorem ig_C {σ : Type} (r : R) : (C (algebraMap R k r) : MvPowerSeries σ k) ∈ Ig R k σ := RingHom.mem_range.mpr ⟨C r, by simp⟩

theorem ig_X {σ : Type} (s : σ) : (X s : MvPowerSeries σ k) ∈ Ig R k σ := RingHom.mem_range.mpr ⟨X s, by simp⟩

theorem map_pderiv' {σ : Type} (f : MvPowerSeries σ R) (v : σ) :
    MvPowerSeries.map (algebraMap R k) (pderiv v f) = pderiv v (MvPowerSeries.map (algebraMap R k) f) := by
  ext n
  simp only [coeff_map, coeff_pderiv, map_mul, map_add, map_natCast, map_one]

theorem ig_pderiv {σ : Type} {f : MvPowerSeries σ k} (hf : f ∈ Ig R k σ) (v : σ) : pderiv v f ∈ Ig R k σ := by
  obtain ⟨g, rfl⟩ := RingHom.mem_range.mp hf
  exact RingHom.mem_range.mpr ⟨pderiv v g, map_pderiv' g v⟩

theorem ig_subst {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ k} (ha : ∀ s, a s ∈ Ig R k τ)
    (hc : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ k} (hf : f ∈ Ig R k σ) : subst a f ∈ Ig R k τ := by
  choose a' ha' using fun s => RingHom.mem_range.1 (ha s)
  obtain ⟨f', rfl⟩ := RingHom.mem_range.1 hf
  set b : σ → MvPowerSeries τ R := fun s => a' s - C (constantCoeff (a' s)) with hb
  have hbc : ∀ s, constantCoeff (b s) = 0 := fun s => by simp [hb]
  have hmap : ∀ s, MvPowerSeries.map (algebraMap R k) (b s) = a s := fun s => by
    have e1 : algebraMap R k (constantCoeff (a' s)) = 0 := by
      rw [← hc s, ← ha' s, constantCoeff_map]
    simp [hb, ha' s, e1]
  refine RingHom.mem_range.2 ⟨subst b f', ?_⟩
  rw [MvPowerSeries.map_subst (hasSubst_of_constantCoeff_zero hbc)]
  simp only [hmap]

theorem ig_ev {m n d : ℕ} {a : Fin m → Pt k n d} (hc : CZ a) (ha : ∀ j i, a j i ∈ Ig R k (Fin n × Fin d))
    {f : PS k m d} (hf : f ∈ Ig R k (Fin m × Fin d)) : ev a f ∈ Ig R k (Fin n × Fin d) := by
  unfold ev
  refine ig_subst (a := fun p : Fin m × Fin d => a p.1 p.2) ?_ ?_ hf
  · intro p
    exact ha p.1 p.2
  · intro p
    exact hc p.1 p.2

theorem ig_liftX [Algebra ℚ k] {d : ℕ} {f : PS k 1 d} (hf : f ∈ Ig R k (Fin 1 × Fin d)) :
    liftX k f ∈ Ig R k (Fin d ⊕ Fin d) := by
  unfold liftX
  refine ig_subst ?_ ?_ hf
  · intro p
    exact ig_X _
  · intro p
    exact MvPowerSeries.constantCoeff_X _

theorem ig_of_intAA {σ : Type} {G : MvPowerSeries σ k} (hG : IntAA (R := R) k G) : G ∈ Ig R k σ := by
  unfold IntAA at hG
  refine RingHom.mem_range.mpr ⟨(fun n => (hG n).choose : MvPowerSeries σ R), ?_⟩
  ext n
  exact (hG n).choose_spec

theorem cc_ev' {K : Type} [CommRing K] {m n d : ℕ} {a : Fin m → Pt K n d} (ha : CZ a) (f : PS K m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  unfold ev
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun p => ha p.1 p.2)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
          (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs'⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hs'),
      smul_zero]
    rw [map_pow, ha s.1 s.2, zero_pow hs']

theorem pderiv_expS [Algebra ℚ k] {n d : ℕ} {f : PS k n d} (hf : constantCoeff f = 0) (v : Fin n × Fin d) :
    pderiv v (FB.expS k f) = FB.expS k f * pderiv v f := by
  rw [FB.expS, Formalism.G.LogCR.pderiv_psubst hf, PowerSeries.derivative_exp]

theorem ig_dlog [Algebra ℚ k] {n d : ℕ} (U : PS R n d) (hU : constantCoeff U = 1) (H : PS k n d)
    (hH : constantCoeff H = 0) (he : MvPowerSeries.map (algebraMap R k) U = FB.expS k H) (v : Fin n × Fin d) :
    pderiv v H ∈ Ig R k (Fin n × Fin d) := by
  have h1 : pderiv v (MvPowerSeries.map (algebraMap R k) U) =
      MvPowerSeries.map (algebraMap R k) U * pderiv v H := by
    rw [he]
    exact pderiv_expS hH v
  have hinv : U * MvPowerSeries.invOfUnit U 1 = 1 :=
    MvPowerSeries.mul_invOfUnit U 1 (by rw [hU, Units.val_one])
  have h2 : pderiv v H =
      MvPowerSeries.map (algebraMap R k) (MvPowerSeries.invOfUnit U 1 * pderiv v U) := by
    rw [map_mul, map_pderiv', h1, ← mul_assoc, ← map_mul, mul_comm (MvPowerSeries.invOfUnit U 1) U,
      hinv, map_one, one_mul]
  rw [h2]
  exact ig_map _

end Int

section Fam

variable {R : Type} [CommRing R] {k : Type} [CommRing k] [Algebra R k] {d : ℕ}

theorem ig_pt {n : ℕ} (j : Fin n) (i : Fin d) : pt k d j i ∈ Ig R k (Fin n × Fin d) := by
  unfold pt
  exact ig_X _

theorem integral_family_point_zero : ∀ j i, (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) j i ∈ Ig R k (Fin 1 × Fin d) := by
  intro j i
  fin_cases j
  · first
      | exact ig_pt 0 i
      | simpa using ig_pt (R := R) (k := k) (0 : Fin 1) i
  · first
      | exact (Ig R k _).zero_mem
      | simpa using (Ig R k (Fin 1 × Fin d)).zero_mem

theorem integral_family_pair_zero : ∀ j i, (![pt k (n := 2) d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d) j i ∈ Ig R k (Fin 2 × Fin d) := by
  intro j i
  fin_cases j
  · first
      | exact ig_pt 0 i
      | simpa using ig_pt (R := R) (k := k) (0 : Fin 2) i
  · first
      | exact ig_pt 1 i
      | simpa using ig_pt (R := R) (k := k) (1 : Fin 2) i
  · first
      | exact (Ig R k _).zero_mem
      | simpa using (Ig R k (Fin 2 × Fin d)).zero_mem

end Fam

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
end
end

section

noncomputable section

open MvPowerSeries TensorProduct

namespace ReciprocityTheory.ChartRestriction.G.TB.Canon

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

section Prim

variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [DecidableEq τ]

end Prim

variable {k : Type} [CommRing k] {d : ℕ}


variable (k d) in
def Q (n : ℕ) : AddSubgroup (Pt k n d) where
  carrier := {p | ∀ i, constantCoeff (p i) = 0}
  add_mem' := fun ha hb i => by rw [Pi.add_apply, map_add (f := _), ha i, hb i, add_zero]
  zero_mem' := fun _ => map_zero _
  neg_mem' := fun ha i => by rw [Pi.neg_apply, map_neg, ha i, neg_zero]

variable {n l : ℕ}

def gen (j : Fin n) : Q k d n := ⟨pt k d j, cc_pt j⟩

theorem czQ (b : Fin n → Q k d l) : CZ (fun j => (b j).1) := fun j i => (b j).2 i

def sb (b : Fin n → Q k d l) : PS k n d →+* PS k l d := evHom (czQ b)

theorem sb_apply (b : Fin n → Q k d l) (f : PS k n d) : sb b f = ev (fun j => (b j).1) f := evHom_apply (czQ b) f

def sq (b : Fin n → Q k d l) : Q k d n →+ Q k d l where
  toFun p := ⟨fun i => sb b (p.1 i), fun i =>
    (congrArg constantCoeff (sb_apply b _)).trans (constantCoeff_ev (czQ b) (p.2 i))⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)

@[simp] theorem sq_gen (b : Fin n → Q k d l) (j : Fin n) : sq b (gen j) = b j := Subtype.ext <| funext fun i => (sb_apply b _).trans (ev_X (czQ b) j i)

theorem sb_sb {m : ℕ} (b : Fin n → Q k d l) (a : Fin m → Q k d n) (f : PS k m d) :
    sb b (sb a f) = sb (fun j => sq b (a j)) f := by
  simp only [sb_apply]
  rw [ev_ev (czQ b) (czQ a)]
  congr 1
  funext j i
  exact (sb_apply b _).symm

theorem sb_gen (f : PS k n d) : sb gen f = f := (sb_apply _ f).trans (ev_pt f)

def E2 (f : PS k 2 d) (u v : Q k d n) : PS k n d := sb ![u, v] f

def E3 (f : PS k 3 d) (u v w : Q k d n) : PS k n d := sb ![u, v, w] f

@[simp] theorem formalPointSubstitutionSeries_valueAtTwoPoints (b : Fin n → Q k d l) (f : PS k 2 d) (u v : Q k d n) : sb b (E2 f u v) = E2 f (sq b u) (sq b v) := by
  have e : (fun j => sq b (![u, v] j)) = ![sq b u, sq b v] := by
    funext i
    fin_cases i <;> rfl
  show sb b (sb ![u, v] f) = sb ![sq b u, sq b v] f
  rw [sb_sb, e]

theorem formalSeriesValueAtTwoPoints_genericPoints (f : PS k 2 d) : E2 f (gen 0) (gen 1) = f := by
  have h : (![gen 0, gen 1] : Fin 2 → Q k d 2) = gen := by
    funext i
    fin_cases i <;> rfl
  show sb ![gen 0, gen 1] f = f
  rw [h, sb_gen]

theorem formalSeriesValueAtThreePoints_genericPoints (f : PS k 3 d) : E3 f (gen 0) (gen 1) (gen 2) = f := by
  have h : (![gen 0, gen 1, gen 2] : Fin 3 → Q k d 3) = gen := by
    funext i
    fin_cases i <;> rfl
  show sb ![gen 0, gen 1, gen 2] f = f
  rw [h, sb_gen]

theorem coeff_kill (j : Fin n) (f : PS k n d) (m : Fin n × Fin d →₀ ℕ) :
    coeff m (sb (Function.update gen j 0) f) = if ∀ b, m (j, b) = 0 then coeff m f else 0 := by
  let a : Fin n × Fin d → PS k n d := fun p => ((Function.update gen j 0 p.1 : Q k d n) : Pt k n d) p.2
  have ha : MvPowerSeries.HasSubst a := (czQ (Function.update gen j 0)).hasSubst
  have key : ∀ e : Fin n × Fin d →₀ ℕ, coeff m (e.prod fun s i => a s ^ i) =
      if e = m ∧ ∀ b, m (j, b) = 0 then 1 else 0 := by
    intro e
    by_cases he : ∀ b, e (j, b) = 0
    · have hp : (e.prod fun s i => a s ^ i) = MvPowerSeries.monomial e 1 := by
        refine (Finsupp.prod_congr fun s hs => ?_).trans (MvPowerSeries.monomial_one_eq e).symm
        have hs1 : s.1 ≠ j := by
          intro h1
          apply Finsupp.mem_support_iff.mp hs
          rw [show s = (j, s.2) from Prod.ext h1 rfl]
          exact he s.2
        show ((Function.update gen j 0 s.1 : Q k d n) : Pt k n d) s.2 ^ e s = X s ^ e s
        rw [Function.update_of_ne hs1]
        rfl
      rw [hp, MvPowerSeries.coeff_monomial]
      by_cases hem : e = m
      · subst hem
        simp [he]
      · rw [if_neg (Ne.symm hem), if_neg (fun h => hem h.1)]
    · push_neg at he
      obtain ⟨b, hb⟩ := he
      have hp : (e.prod fun s i => a s ^ i) = 0 := by
        refine Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hb) ?_
        show ((Function.update gen j 0 j : Q k d n) : Pt k n d) b ^ e (j, b) = 0
        first
        | rw [Function.update_self]
        | rw [Function.update_same]
        exact zero_pow hb
      rw [hp, map_zero, if_neg]
      rintro ⟨rfl, h⟩
      exact hb (h b)
  rw [sb_apply]
  show coeff m (MvPowerSeries.subst a f) = _
  rw [MvPowerSeries.coeff_subst ha, finsum_eq_single _ m]
  · show coeff m f • coeff m (m.prod fun s i => a s ^ i) = _
    rw [key]
    by_cases hm : ∀ b, m (j, b) = 0 <;> simp [hm]
  · intro e he
    show coeff e f • coeff m (e.prod fun s i => a s ^ i) = 0
    rw [key, if_neg (fun h => he h.1), smul_zero]

variable [Algebra ℚ k]

end ReciprocityTheory.ChartRestriction.G.TB.Canon
end
end
