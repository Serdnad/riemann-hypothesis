module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ValuationBoundAdd
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle005
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StmtNumEOf
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcTsumOdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem prime_cast_ne_zero : ((p : ℕ) : K0 p) ≠ 0 := by
  have h1 : ((p : ℕ) : WW p) ≠ 0 := WittVector.p_nonzero p (kb p)
  have h2 : algebraMap (WW p) (K0 p) ((p : ℕ) : WW p) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (WW p) (K0 p))).2 h1
  simpa using h2

theorem pKf_ne (Y : Pend X) : ((p : ℕ) : X.G.Kf) ≠ 0 := by
  intro h
  have h1 : algebraMap X.G.Kf Y.Kc ((p : ℕ) : X.G.Kf) = 0 := by rw [h, map_zero]
  have h2 : algebraMap (K0 p) Y.Kc ((p : ℕ) : K0 p) = 0 := by
    rw [map_natCast] at h1 ⊢
    exact h1
  exact prime_cast_ne_zero ((map_eq_zero _).1 h2)

theorem algebraMap_inj (Y : Pend X) (he : 0 < X.eO) : Function.Injective (algebraMap X.G.O X.G.Kf) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha0 X.unif
  obtain ⟨u, hu⟩ := hn

  have h1 : algebraMap X.G.O X.G.Kf (X.vp ^ n) = 0 := by rw [← hu, map_mul, ha, zero_mul]
  have h2 : algebraMap X.G.O X.G.Kf X.vp = 0 := by
    rw [map_pow] at h1
    by_contra h
    exact pow_ne_zero n h h1
  obtain ⟨u', hu'⟩ := X.eO_spec
  have h3 : algebraMap X.G.O X.G.Kf ((p : X.G.O) * u') = 0 := by
    rw [hu', map_pow, h2, zero_pow (by omega)]
  rw [map_mul, map_natCast] at h3
  rcases mul_eq_zero.1 h3 with h | h
  · exact pKf_ne Y h
  · have : algebraMap X.G.O X.G.Kf ((u' : X.G.O) * ((u'⁻¹ : X.G.Oˣ) : X.G.O)) = 0 := by rw [map_mul, h, zero_mul]
    simp at this

theorem isFractionRing_of_pos_eO (Y : Pend X) (he : 0 < X.eO) : IsFractionRing X.G.O X.G.Kf := by
  have : FaithfulSMul X.G.O X.G.Kf := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap_inj Y he)
  apply IsFractionRing.of_field
  intro z
  rcases Y.Oc_val (algebraMap X.G.Kf Y.Kc z) with h | h
  · obtain ⟨a, ha⟩ := (mem_intK X).1 ((Y.Oc_K z).1 h)
    exact ⟨a, 1, by simp [ha]⟩
  · rw [← map_inv₀] at h
    obtain ⟨a, ha⟩ := (mem_intK X).1 ((Y.Oc_K z⁻¹).1 h)
    exact ⟨1, a, by simp [ha]⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

theorem en_p_mem : (p : Y.Kc) ∈ Y.Oc := by
  exact natCast_mem Y.Oc p

theorem en_ppow_mem (N : ℤ) (hN : 0 ≤ N) : (p : Y.Kc) ^ N ∈ Y.Oc := by
  lift N to ℕ using hN
  rw [zpow_natCast]
  exact Y.Oc.pow_mem (en_p_mem Y) _

theorem en_root (z : Y.Kc) (M : ℕ) (hM : 0 < M) (h : z ^ M ∈ Y.Oc) : z ∈ Y.Oc := by
  rcases Y.Oc_val z with hz | hz
  · exact hz
  · by_cases h0 : z = 0
    · rw [h0]
      exact Y.Oc.zero_mem
    · have e : z = z ^ M * (z⁻¹) ^ (M - 1) := by
        rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero _ h0), ← pow_succ']
        congr 1
        omega
      rw [e]
      exact Y.Oc.mul_mem h (Y.Oc.pow_mem hz _)

theorem en_geC_one : Y.geC 1 0 := by
  intro a b hb hab
  rw [one_pow, one_mul]
  have h' : (a : ℝ) ≤ 0 := by linarith
  have h'' : a ≤ 0 := by exact_mod_cast h'
  exact en_ppow_mem Y (-a) (by omega)

theorem en_geC_mul_rat {x y : Y.Kc} (q1 q2 : ℚ) (hx : Y.geC x q1) (hy : Y.geC y q2) :
    Y.geC (x * y) ((q1 + q2 : ℚ) : ℝ) := by
  intro a b hb hab
  have hp := pKc_ne Y
  have hM0 : 0 < q1.den * q2.den := Nat.mul_pos q1.den_pos q2.den_pos
  obtain ⟨a1, ha1⟩ : ∃ a1 : ℤ, (a1 : ℝ) = (q1 : ℝ) * ((b * (q1.den * q2.den) : ℕ) : ℝ) := by
    refine ⟨q1.num * q2.den * b, ?_⟩
    have hd : (q1.den : ℝ) ≠ 0 := by exact_mod_cast q1.den_pos.ne'
    rw [Rat.cast_def]
    push_cast
    field_simp
  obtain ⟨a2, ha2⟩ : ∃ a2 : ℤ, (a2 : ℝ) = (q2 : ℝ) * ((b * (q1.den * q2.den) : ℕ) : ℝ) := by
    refine ⟨q2.num * q1.den * b, ?_⟩
    have hd : (q2.den : ℝ) ≠ 0 := by exact_mod_cast q2.den_pos.ne'
    rw [Rat.cast_def]
    push_cast
    field_simp
  have hx' := hx a1 (b * (q1.den * q2.den)) (Nat.mul_pos hb hM0) ha1.le
  have hy' := hy a2 (b * (q1.den * q2.den)) (Nat.mul_pos hb hM0) ha2.le
  have hle : a * ((q1.den * q2.den : ℕ) : ℤ) ≤ a1 + a2 := by
    have h' : ((a * ((q1.den * q2.den : ℕ) : ℤ) : ℤ) : ℝ) ≤ ((a1 + a2 : ℤ) : ℝ) := by
      push_cast
      rw [ha1, ha2]
      push_cast at hab ⊢
      have hM' : (0 : ℝ) ≤ (q1.den : ℝ) * q2.den := by positivity
      nlinarith
    exact_mod_cast h'
  have key : ((x * y) ^ b * (p : Y.Kc) ^ (-a)) ^ (q1.den * q2.den) =
      (x ^ (b * (q1.den * q2.den)) * (p : Y.Kc) ^ (-a1)) * (y ^ (b * (q1.den * q2.den)) * (p : Y.Kc) ^ (-a2)) *
        (p : Y.Kc) ^ (a1 + a2 - a * ((q1.den * q2.den : ℕ) : ℤ)) := by
    have h1 : ((p : Y.Kc) ^ (-a)) ^ (q1.den * q2.den) =
        (p : Y.Kc) ^ (-a1) * (p : Y.Kc) ^ (-a2) * (p : Y.Kc) ^ (a1 + a2 - a * ((q1.den * q2.den : ℕ) : ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ hp, ← zpow_add₀ hp]
      congr 1
      push_cast
      ring
    rw [mul_pow, h1]
    ring
  apply en_root Y _ (q1.den * q2.den) hM0
  rw [key]
  exact Y.Oc.mul_mem (Y.Oc.mul_mem hx' hy') (en_ppow_mem Y _ (by omega))

theorem en_geC_sum {α : Type} (s : Finset α) (f : α → Y.Kc) (g : ℝ) (h : ∀ i ∈ s, Y.geC (f i) g) :
    Y.geC (∑ i ∈ s, f i) g := by
  exact Finset.sum_induction f (fun x => Y.geC x g) (fun _ _ ha hb => geC_add Y ha hb) (geC_zero Y g) h

def geP {τ : Type} (a : MvPolynomial τ Y.Kc) (g : ℝ) : Prop := ∀ n, Y.geC (AddMonoidAlgebra.coeff a n) g

theorem valuation_coeff_one_nonneg {τ : Type} : geP Y (1 : MvPolynomial τ Y.Kc) 0 := by
  classical
  intro n
  rw [MvPolynomial.coeff_one]
  split_ifs
  · exact en_geC_one Y
  · exact geC_zero Y 0

theorem valuation_coeff_ge_mul_rat {τ : Type} {a b : MvPolynomial τ Y.Kc} (q1 q2 : ℚ) (ha : geP Y a q1) (hb : geP Y b q2) :
    geP Y (a * b) ((q1 + q2 : ℚ) : ℝ) := by
  classical
  intro n
  rw [MvPolynomial.coeff_mul]
  exact en_geC_sum Y _ _ _ fun x _ => en_geC_mul_rat Y q1 q2 (ha x.1) (hb x.2)

theorem valuation_coeff_ge_prod_rat {τ α : Type} (s : Finset α) (a : α → MvPolynomial τ Y.Kc) (q : α → ℚ)
    (h : ∀ i ∈ s, geP Y (a i) (q i)) : geP Y (∏ i ∈ s, a i) ((∑ i ∈ s, q i : ℚ) : ℝ) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using valuation_coeff_one_nonneg Y (τ := τ)
  · intro i t hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact valuation_coeff_ge_mul_rat Y _ _ (h i (Finset.mem_insert_self i t))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem valuation_coeff_ge_sum {τ α : Type} (s : Finset α) (a : α → MvPolynomial τ Y.Kc) (g : ℝ) (h : ∀ i ∈ s, geP Y (a i) g) :
    geP Y (∑ i ∈ s, a i) g := by
  intro n
  rw [MvPolynomial.coeff_sum]
  exact en_geC_sum Y _ _ _ fun i hi => h i hi n

theorem valuation_coeff_ge_smul {τ : Type} {a : MvPolynomial τ Y.Kc} {g : ℝ} {c : Y.Kc} (hc : c ∈ Y.Oc) (h : geP Y a g) :
    geP Y (c • a) g := by
  intro n
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  exact geC_mul_Oc Y (h n) hc

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem nc_modsub (a b e' n : ℕ) (ha : a < n) (hb : b < n) (he : e' < n) (h : (a + e') % n = b) :
    (b + n - a) % n = e' := by
  rcases Nat.lt_or_ge (a + e') n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    subst h
    have : a + e' + n - a = e' + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt he]
  · have h2 : (a + e') % n = a + e' - n := by
      rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
    rw [h2] at h
    subst h
    have : a + e' - n + n - a = e' := by omega
    rw [this, Nat.mod_eq_of_lt he]

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

include hL ht0 in
theorem nc_shift (s s' : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) (e : ℕ) :
    nc_iota Y u w hg t0 s + e • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) = nc_iota Y u w hg t0 s' ↔
      (s.val + e) % (D.gat u w hg).P.n' (Y.vOf u w hg t0) = s'.val := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  have key : ∀ (a b : ℕ), b < addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) →
      (t0 + a • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) + e • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) =
        t0 + b • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ↔
      (a + e) % addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) = b) := by
    intro a b hb
    have hpos : 0 < addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := by omega
    rw [add_assoc, ← add_nsmul, show (a + e) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) =
      ((a + e) % addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) by
        rw [mod_addOrderOf_nsmul]]
    constructor
    · intro h
      exact nsmul_injOn_Iio_addOrderOf (show (a + e) % _ ∈ Set.Iio _ from Nat.mod_lt _ hpos)
        (show b ∈ Set.Iio _ from hb) (add_left_cancel h)
    · intro h; rw [h]
  have := key s.val s'.val (by rw [← hn]; exact s'.isLt)
  rw [← hn] at this
  exact this

include hL ht0 in
theorem nc_excl (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) (e : ℕ)
    (he : 2 * e + 1 ∈ dSet ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) s) :
    Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) (2 * e + 1) := by
  have hloc := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  unfold dSet at he
  obtain ⟨s', hs', hd⟩ := Finset.mem_image.1 he
  rw [Finset.mem_filter] at hs'
  have hpos : 0 < (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by have := s.isLt; omega
  have hlt : 2 * e + 1 < (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by rw [← hd]; exact Nat.mod_lt _ hpos
  have hne : s' ≠ s := fun h => hs'.2 (by rw [h])
  refine ⟨⟨e, rfl⟩, nc_iota Y u w hg t0 s', ((hloc s').2.1).1 hs'.1, fun h => hne (hinj h), ?_⟩
  refine ⟨by omega, ?_, ?_⟩
  · rw [nc_partner hg]
    congr 1
    show nc_iota Y u w hg t0 s + (2 * e + 1) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) = nc_iota Y u w hg t0 s'
    refine (nc_shift X Y hT hL u w hg t0 ht0 s s' (2 * e + 1)).2 ?_
    rw [← hd]
    have := s.isLt
    have := s'.isLt
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have : s.val + (s'.val + (D.gat u w hg).P.n' (Y.vOf u w hg t0) - s.val) =
        s'.val + (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt s'.isLt]
  · intro e' he0 he1 hp
    rw [nc_partner hg] at hp
    have hp' : nc_iota Y u w hg t0 s + e' • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) = nc_iota Y u w hg t0 s' :=
      (Prod.mk.inj hp).2
    have h1 := (nc_shift X Y hT hL u w hg t0 ht0 s s' e').1 hp'
    have h2 := nc_modsub s.val s'.val e' _ s.isLt s'.isLt (by omega) h1
    rw [hd] at h2
    omega

end Orbit

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

include hL ht0 in
theorem nc_capU (j : ℕ) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) (k : ℕ) :
    Formalism.MainNotions.G.capU X (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j (nc_iota Y u w hg t0 s) k =
      nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s k) := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  unfold Formalism.MainNotions.G.capU nc_zc
  rw [nc_partner hg]
  have key : ∀ a : ℕ, t0 + a • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) + k • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) =
      t0 + ((a + k) % (D.gat u w hg).P.n' (Y.vOf u w hg t0)) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) := by
    intro a
    rw [hn, mod_addOrderOf_nsmul, add_nsmul, add_assoc]
  exact congrArg (fun t => Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) j (false, t) + Formalism.MainNotions.G.cG L) (key s.val)

open Classical in
include hL ht0 in
theorem nc_gU_eq (K : Formalism.MainNotions.G.Consts) (j : ℕ) :
    Formalism.MainNotions.G.gU X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0 =
      Formalism.MainNotions.FormalGroupSystem.gam (D.what₂.places.resChar w) * ∑ s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0), nc_ya X Y u w hg t0 s -
        ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos, ∑' e : ℕ,
          min (nc_ya X Y u w hg t0 s / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ (2 * e + 1))
            (nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1))) -
        Formalism.MainNotions.G.dl X K (D.what₂.places.resChar w) t0 := by
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  unfold Formalism.MainNotions.G.gU
  rw [nc_topsOn X Y hT hL u w hg t0 ht0, Finset.sum_image (fun a _ b _ h => hinj h), Finset.filter_image,
    Finset.sum_image (fun a _ b _ h => hinj h)]
  have hf : ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter
      (fun a => ¬ Formalism.MainNotions.G.IsV X (D.what₂.places.resChar w) (nc_iota Y u w hg t0 a)) =
      ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos := by
    apply Finset.filter_congr
    intro s _
    rw [nc_isV X Y hT hL u w hg t0 ht0 s, not_not]
  rw [hf]
  congr 2
  apply Finset.sum_congr rfl
  intro s _
  rw [nc_tsum_odd]
  apply tsum_congr
  intro e
  rw [nc_capU X Y hT hL u w hg t0 ht0]
  rfl

open Classical in
include hL ht0 in
theorem growth_exclusion_sum_eq (K : Formalism.MainNotions.G.Consts) (j : ℕ) :
    Formalism.MainNotions.G.g0 X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0 =
      ∑ s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0), ∑' e : ℕ,
        (if Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w)
            (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) (2 * e + 1) then 0 else
          max 0 (nc_ya X Y u w hg t0 s / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ (2 * e + 1) -
            nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) -
        Formalism.MainNotions.G.dl X K (D.what₂.places.resChar w) t0 := by
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  unfold Formalism.MainNotions.G.g0
  rw [nc_topsOn X Y hT hL u w hg t0 ht0, Finset.sum_image (fun a _ b _ h => hinj h)]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  have e1 : ∀ e : ℕ, (if Odd e ∧ ¬ Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) e then
        max 0 (Formalism.MainNotions.G.al L (Formalism.MainNotions.G.aL L) (nc_iota Y u w hg t0 s) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ e -
          Formalism.MainNotions.G.capU X (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j (nc_iota Y u w hg t0 s) e) else 0) =
      (if Odd e then (if Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) e then 0 else
        max 0 (Formalism.MainNotions.G.al L (Formalism.MainNotions.G.aL L) (nc_iota Y u w hg t0 s) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ e -
          Formalism.MainNotions.G.capU X (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j (nc_iota Y u w hg t0 s) e)) else 0) := by
    intro e
    by_cases h1 : Odd e <;> by_cases h2 : Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) e <;>
      simp [h1, h2]
  rw [tsum_congr e1, nc_tsum_odd]
  apply tsum_congr
  intro e
  rw [nc_capU X Y hT hL u w hg t0 ht0]
  rfl

end Orbit

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
