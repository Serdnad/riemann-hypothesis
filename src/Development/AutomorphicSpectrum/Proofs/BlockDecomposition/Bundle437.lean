module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle104
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DpZeroRight
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

universe w w' v u v' u'

namespace GlobalTheory.CompanionTheory.CrisFil

section General

variable {R R' : Type} [CommRing R] [CommRing R'] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R'} {σ : R →+* R'}

def subMor (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F')
    (h : ∀ (T : C') (x : F.obj (m.G.obj T)), x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) :
    CH.Mor S.fn S'.fn σ where
  G := m.G
  τ T := ((m.τ T).domRestrict (S.S (m.G.obj T))).codRestrict (S'.S T) fun x => h T x.1 x.2
  nat φ x := Subtype.ext (m.nat φ x.1)

theorem pull_inc (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F')
    (h : ∀ (T : C') (x : F.obj (m.G.obj T)), x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) (n : ℕ) (y : CH.H S.fn n) :
    m.pull n (S.inc.pull n y) = S'.inc.pull n ((subMor m S S' h).pull n y) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

theorem pull_img (m : CH.Mor F F' σ) (S : CH.SubF F) (S' : CH.SubF F')
    (h : ∀ (T : C') (x : F.obj (m.G.obj T)), x ∈ S.S (m.G.obj T) → m.τ T x ∈ S'.S T) (n : ℕ) (x : CH.H F n)
    (hx : x ∈ S.img n) : m.pull n x ∈ S'.img n := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨(subMor m S S' h).pull n y, (pull_inc m S S' h n y).symm⟩

end General

section Thick

variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R}

variable {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R}

theorem omMor_img (m : GlobalTheory.LogCris.Mor L L' σ) (σ₀ : Λ →+* Λ') (h : ∀ a, σ (c a) = c' (σ₀ a)) (r j : ℕ)
    (x : CH.H (OM L c) j) (hx : x ∈ (pdS L c r).img j) : (omMor m σ₀ h).pull j x ∈ (pdS L' c' r).img j :=
  pull_img (omMor m σ₀ h) (pdS L c r) (pdS L' c' r) (fun _ _ hz => hz) j x hx

end Thick

theorem red_fil : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m)
    (r j : ℕ), ∀ x ∈ HcFil F κ k m r j, redHc F κ k h j x ∈ HcFil F κ k n r j := by
  intro l _ O _ F κ k m n h r j x hx
  exact omMor_img _ _ _ r j x hx

end GlobalTheory.CompanionTheory.CrisFil
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.CLiftEx

theorem thick_isNilpotent {b : Base} {L : b.Fun} (T : Thick L) (x : T.B) (hx : x ∈ T.J) :
    IsNilpotent x := by
  by_cases hp : b.p = 0
  · obtain ⟨k, hk⟩ := T.adm.2 hp
    refine ⟨k, ?_⟩
    simpa [hk] using Ideal.pow_mem_pow hx k
  · obtain ⟨k, hk⟩ := T.adm.1 hp
    refine ⟨b.p * k, ?_⟩
    have hfac : ((b.p.factorial : ℕ) : T.B) = (b.p : T.B) * ((b.p - 1).factorial : T.B) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp]
    rw [pow_mul, ← T.δ.factorial_mul_dpow_eq_pow hx, hfac, mul_assoc, mul_pow, hk, zero_mul]

theorem unit_lift {B : Type} [CommRing B] (J : Ideal B) (hJ : ∀ x ∈ J, IsNilpotent x) (u : (B ⧸ J)ˣ) :
    ∃ w : Bˣ, Ideal.Quotient.mk J (w : B) = (u : B ⧸ J) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ J)
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (B ⧸ J)ˣ) : B ⧸ J)
  have hmem : a * c - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ha, hc, Units.mul_inv, map_one, sub_self]
  have hunit : IsUnit (a * c) := by
    have h1 := (hJ _ hmem).isUnit_one_add
    have h2 : (1 : B) + (a * c - 1) = a * c := by ring
    rwa [h2] at h1
  obtain ⟨w, hw⟩ := isUnit_of_mul_isUnit_left hunit
  exact ⟨w, by rw [hw, ha]⟩

theorem nonempty_cLift : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {b : Base} {ht : b.t = 1}
    {κ : O →+* b.R ⧸ b.I} {C : Type 1} [Category.{0} C] (G : C ⥤ Thick ((B.schFn q).cr b ht κ)) (D : E.LineData X),
    (∀ T, ∃ p : Spec (CommRingCat.of ((G.obj T).B ⧸ (G.obj T).J)) ⟶ D.Y, p ≫ D.f = B.thPt (G.obj T)) → Nonempty (B.CLift G D) := by
  intro O _ X q b ht κ C _ G D h
  classical
  choose p hp using h
  refine ⟨⟨p, hp, fun {T T'} φ =>
    if h : (B.thSp (G.map φ) ≫ p T) ≫ D.f = p T' ≫ D.f then
      (unit_lift (G.obj T').J (fun x hx => thick_isNilpotent (G.obj T') x hx)
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of ((G.obj T').B ⧸ (G.obj T').J))).hom.hom.toMonoidHom
          (D.u (B.thSp (G.map φ) ≫ p T) (p T') h))).choose
    else 1, fun {T T'} φ h => ?_⟩⟩
  rw [dite_eq_left h]
  exact (unit_lift (G.obj T').J (fun x hx => thick_isNilpotent (G.obj T') x hx)
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of ((G.obj T').B ⧸ (G.obj T').J))).hom.hom.toMonoidHom
      (D.u (B.thSp (G.map φ) ≫ p T) (p T') h))).choose_spec

end GlobalTheory.CompanionTheory.CLiftEx
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
namespace GlobalTheory.CompanionTheory.TruncLog

variable {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J)

theorem mul_dpow_eq_succ {x : A} (hx : x ∈ J) (a : ℕ) :
    x * δ.dpow a x = ((a : A) + 1) * δ.dpow (a + 1) x := by
  have h := δ.mul_dpow (m := 1) (n := a) hx
  rw [δ.dpow_one hx] at h
  rw [h, Nat.choose_one_right, add_comm 1 a]
  push_cast
  ring

theorem factorial_mul_dpow_eq_zero {N : ℕ} {x : A}
    (hN : ∀ k, N ≤ k → (k.factorial : A) * δ.dpow (k + 1) x = 0) {a k : ℕ} (ha : N < a)
    (hk : a ≤ k + 1) : (k.factorial : A) * δ.dpow a x = 0 := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  obtain ⟨d, hd⟩ := Nat.factorial_dvd_factorial (show c ≤ k by omega)
  rw [hd]
  push_cast
  rw [mul_comm (c.factorial : A), mul_assoc, hN c (by omega), mul_zero]

theorem one_add_mul_sum_succ {x : A} (hx : x ∈ J) (m n : ℕ) :
    (1 + x) * ∑ a ∈ Finset.range (n + 1),
        (-1 : A) ^ a * ((a + (m + 1)).factorial : A) * δ.dpow a x =
      ((m : A) + 1) * ∑ a ∈ Finset.range (n + 1),
        (-1 : A) ^ a * ((a + m).factorial : A) * δ.dpow a x
      + (-1) ^ n * ((n + (m + 1)).factorial : A) * ((n : A) + 1) * δ.dpow (n + 1) x := by
  induction n with
  | zero =>
    have e : (((m + 1).factorial : ℕ) : A) = ((m : A) + 1) * (m.factorial : A) := by
      rw [Nat.factorial_succ]; push_cast; ring
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, δ.dpow_zero hx, δ.dpow_one hx,
      mul_one, e, Nat.cast_zero]
    ring
  | succ n ih =>
    have e1 : ((n + 1 + (m + 1)).factorial : A)
        = ((n : A) + m + 2) * ((n + (m + 1)).factorial : A) := by
      rw [show n + 1 + (m + 1) = (n + (m + 1)) + 1 by omega, Nat.factorial_succ]
      push_cast; ring
    have e2 : ((n + 1 + m).factorial : A) = ((n + (m + 1)).factorial : A) := by
      rw [show n + 1 + m = n + (m + 1) by omega]
    have hxp := mul_dpow_eq_succ δ hx (n + 1)
    rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ _ (n + 1), e1, e2]
    push_cast at hxp ⊢
    linear_combination
      (-1 : A) ^ (n + 1) * ((n : A) + m + 2) * ((n + (m + 1)).factorial : A) * hxp

theorem one_add_mul_sum_zero {x : A} (hx : x ∈ J) (n : ℕ) :
    (1 + x) * ∑ a ∈ Finset.range (n + 1), (-1 : A) ^ a * (a.factorial : A) * δ.dpow a x =
      1 + (-1) ^ n * (n.factorial : A) * ((n : A) + 1) * δ.dpow (n + 1) x := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, δ.dpow_zero hx, δ.dpow_one hx,
      mul_one, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero]
  | succ n ih =>
    have e1 : ((n + 1).factorial : A) = ((n : A) + 1) * (n.factorial : A) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hxp := mul_dpow_eq_succ δ hx (n + 1)
    rw [Finset.sum_range_succ, mul_add, ih, e1]
    push_cast at hxp ⊢
    linear_combination (-1 : A) ^ (n + 1) * ((n : A) + 1) * (n.factorial : A) * hxp

theorem one_add_pow_mul_sum {N : ℕ} {x : A} (hx : x ∈ J)
    (hN : ∀ k, N ≤ k → (k.factorial : A) * δ.dpow (k + 1) x = 0) (m : ℕ) :
    (1 + x) ^ (m + 1) * ∑ a ∈ Finset.range (N + 1),
      (-1 : A) ^ a * ((a + m).factorial : A) * δ.dpow a x = (m.factorial : A) := by
  induction m with
  | zero =>
    simp only [zero_add, pow_one, add_zero, Nat.factorial_zero, Nat.cast_one]
    rw [one_add_mul_sum_zero δ hx N]
    have := hN N le_rfl
    linear_combination ((-1 : A) ^ N * ((N : A) + 1)) * this
  | succ m ih =>
    have z := factorial_mul_dpow_eq_zero δ hN (a := N + 1) (k := N + (m + 1)) (by omega) (by omega)
    rw [pow_succ, mul_assoc, one_add_mul_sum_succ δ hx m N, Nat.factorial_succ]
    push_cast
    linear_combination ((m : A) + 1) * ih
      + (1 + x) ^ (m + 1) * (-1 : A) ^ N * ((N : A) + 1) * z

theorem sum_antidiagonal_eq_sum_box (g : ℕ → ℕ → A) {N M : ℕ} (hM : 2 * N ≤ M)
    (hg : ∀ a b, N < a ∨ N < b → g a b = 0) :
    ∑ k ∈ Finset.range (M + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, g p.1 p.2 =
      ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), g a b := by
  rw [← Finset.sum_product' (f := g),
    ← Finset.sum_fiberwise_of_maps_to
      (s := Finset.range (N + 1) ×ˢ Finset.range (N + 1)) (t := Finset.range (M + 1))
      (g := fun p => p.1 + p.2)
      (by intro p hp; simp only [Finset.mem_product, Finset.mem_range] at hp ⊢; omega)]
  refine Finset.sum_congr rfl fun k _ => ?_
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter] at hp
    simpa using hp.2
  · intro p hp hp'
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, not_and] at hp'
    apply hg
    by_contra hc
    exact hp' (by omega) hp

theorem dlog_mul {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) (N : ℕ)
    (h : ∀ k, N ≤ k → ∀ x ∈ J, (k.factorial : A) * δ.dpow (k + 1) x = 0) (v w : A)
    (hv : v - 1 ∈ J) (hw : w - 1 ∈ J) :
    B.dlog δ N (v * w) = B.dlog δ N v + B.dlog δ N w := by
  obtain ⟨x, rfl⟩ : ∃ x, v = 1 + x := ⟨v - 1, by ring⟩
  obtain ⟨y, rfl⟩ : ∃ y, w = 1 + y := ⟨w - 1, by ring⟩
  have hx : x ∈ J := by simpa using hv
  have hy : y ∈ J := by simpa using hw
  have hvy : (1 + x) * y ∈ J := J.mul_mem_left _ hy
  have hz : x + (1 + x) * y ∈ J := J.add_mem hx hvy
  have dl : ∀ t : A, B.dlog δ N (1 + t) =
      ∑ k ∈ Finset.range N, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) t := by
    intro t; simp [B.dlog]
  have dz : B.dlog δ N ((1 + x) * (1 + y)) =
      ∑ k ∈ Finset.range N, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) := by
    have : (1 + x) * (1 + y) = 1 + (x + (1 + x) * y) := by ring
    rw [this, dl]
  let g : ℕ → ℕ → A := fun a b => (-1 : A) ^ (a + b + 1) * ((a + b - 1).factorial : A) *
    δ.dpow a x * ((1 + x) ^ b * δ.dpow b y)
  have hg : ∀ a b, N < a ∨ N < b → g a b = 0 := by
    intro a b hab
    rcases hab with hab | hab
    · have := factorial_mul_dpow_eq_zero δ (fun k hk => h k hk x hx) (a := a) (k := a + b - 1)
        hab (by omega)
      simp only [g]
      rw [mul_assoc ((-1 : A) ^ (a + b + 1)), this]
      ring
    · have := factorial_mul_dpow_eq_zero δ (fun k hk => h k hk y hy) (a := b) (k := a + b - 1)
        hab (by omega)
      simp only [g]
      linear_combination
        ((-1 : A) ^ (a + b + 1) * δ.dpow a x * (1 + x) ^ b) * this
  have s1 : B.dlog δ N ((1 + x) * (1 + y)) = ∑ k ∈ Finset.range (2 * N),
      (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) := by
    rw [dz]
    apply Finset.sum_subset
    · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
    · intro k _ hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [mul_assoc, h k hk _ hz, mul_zero]
  have s2 : ∀ k, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), g p.1 p.2 := by
    intro k
    rw [δ.dpow_add hx hvy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p.1 + p.2 = k + 1 := by simpa using hp
    simp only [g]
    rw [hp', δ.dpow_mul hy, show k + 1 - 1 = k by omega]
    ring
  have s3 := sum_antidiagonal_eq_sum_box g (N := N) (M := 2 * N) le_rfl hg
  rw [Finset.sum_range_succ'] at s3
  have s4 : ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), g a b =
      g 0 0 + (B.dlog δ N (1 + x) + B.dlog δ N (1 + y)) := by
    rw [Finset.sum_comm, Finset.sum_range_succ', Finset.sum_range_succ' (fun a => g a 0), dl, dl]
    have t1 : ∀ k, g (k + 1) 0 = (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) x := by
      intro k
      simp only [g, add_zero, pow_zero, δ.dpow_zero hy, show k + 1 - 1 = k by omega]
      ring
    have t2 : ∀ b, ∑ a ∈ Finset.range (N + 1), g a (b + 1) =
        (-1 : A) ^ b * (b.factorial : A) * δ.dpow (b + 1) y := by
      intro b
      rw [← one_add_pow_mul_sum δ hx (fun k hk => h k hk x hx) b]
      simp only [g]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [show a + (b + 1) - 1 = a + b by omega]
      ring
    simp only [t1, t2]
    ring
  have s5 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 0, g p.1 p.2 = g 0 0 := by simp
  rw [s5, s4] at s3
  simp only [← s2] at s3
  rw [s1]
  linear_combination s3

end GlobalTheory.CompanionTheory.TruncLog
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

variable {l : ℕ} [Fact l.Prime]

instance neZeroPow (m : ℕ) : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

def ind (A : PAlg l) (m : ℕ) (c : ZMod (l ^ m)) : (A.cont ℤ_[l]).A :=
  ⟨fun z => if PadicInt.toZModPow m z = c then 1 else 0, fun k =>
    ((GlobalTheory.CompanionTheory.PadicShift.isLocallyConstant_toZModPow l m).comp fun a =>
      if a = c then (1 : A.A) else 0).comp (Ideal.Quotient.mk (Ideal.span {A.pi ^ k}))⟩

theorem ev_ind (A : PAlg l) (m : ℕ) (c : ZMod (l ^ m)) (z : ℤ_[l]) :
    Hom.f (A.evCont z) (ind A m c) = if PadicInt.toZModPow m z = c then 1 else 0 := rfl

theorem cont_ext {A : PAlg l} {f g : (A.cont ℤ_[l]).A}
    (h : ∀ z, Hom.f (A.evCont z) f = Hom.f (A.evCont z) g) : f = g :=
  Subtype.ext (funext h)

theorem ev_toCont (A : PAlg l) (z : ℤ_[l]) (a : A.A) :
    Hom.f (A.evCont z) (Hom.f (A.toCont ℤ_[l]) a) = a := rfl

theorem mem_span_pi_pow (A : PAlg l) (k : ℕ) (f : (A.cont ℤ_[l]).A) :
    f ∈ Ideal.span {(A.cont ℤ_[l]).pi ^ k} ↔ ∀ z, Hom.f (A.evCont z) f ∈ Ideal.span {A.pi ^ k} :=
  (RL.cont_ex A ℤ_[l]).2.2.2 k f

theorem sharp_zero (A : PAlg l) : A.sharp 0 = 0 := by
  have h : WittVector.teichmuller l (0 : A.A) = 0 := by
    ext n
    cases n with
    | zero => simp [WittVector.teichmuller_coeff_zero]
    | succ n => simp [WittVector.teichmuller_coeff_pos]
  change A.th (WittVector.teichmuller l (0 : A.A)) = 0
  rw [h, map_zero]

theorem sharp_add (A : PAlg l) {e f : A.A} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : e * f = 0) : A.sharp (e + f) = A.sharp e + A.sharp f := by
  have hs : IsIdempotentElem (e + f) := by
    have h' : f * e = 0 := by rw [mul_comm, h]
    simp only [IsIdempotentElem, add_mul, mul_add, h, h', he.eq, hf.eq, add_zero, zero_add]
  have h1 := (RL.sharp_cong A).2.2 _ hs
  have h2 := (RL.sharp_cong A).2.2 _ he
  have h3 := (RL.sharp_cong A).2.2 _ hf
  have h4 : (1 - (e + f)) = (1 - e) * (1 - f) := by
    have : (1 - e) * (1 - f) = 1 - e - f + e * f := by ring
    rw [this, h]; ring
  have h5 : A.sharp e * A.sharp f = 0 := by rw [← map_mul, h, sharp_zero]
  rw [h4, map_mul, h2, h3] at h1
  have : (1 - A.sharp e) * (1 - A.sharp f) = 1 - A.sharp e - A.sharp f + A.sharp e * A.sharp f := by ring
  rw [this, h5] at h1
  have h6 : A.sharp (e + f) = 1 - (1 - A.sharp e - A.sharp f + 0) := by rw [h1]; ring
  rw [h6]; ring

theorem sharp_sum (A : PAlg l) {I : Type} (s : Finset I) (e : I → A.A)
    (hi : ∀ i ∈ s, IsIdempotentElem (e i))
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0) :
    A.sharp (∑ i ∈ s, e i) = ∑ i ∈ s, A.sharp (e i) ∧ IsIdempotentElem (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using sharp_zero A, by simp [IsIdempotentElem]⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih (fun i h => hi i (Finset.mem_insert_of_mem h))
      (fun i h j h' => ho i (Finset.mem_insert_of_mem h) j (Finset.mem_insert_of_mem h'))
    have h3 : e a * ∑ i ∈ s, e i = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun i h => ho a (Finset.mem_insert_self _ _) i
        (Finset.mem_insert_of_mem h) (fun e' => ha (e' ▸ h))
    have h4 := hi a (Finset.mem_insert_self _ _)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨by rw [sharp_add A h4 h2 h3, h1], ?_⟩
    have h5 : (∑ i ∈ s, e i) * e a = 0 := by rw [mul_comm, h3]
    simp only [IsIdempotentElem, add_mul, mul_add, h3, h5, h4.eq, h2.eq, add_zero, zero_add]

theorem sum_sharp_eq_one (A : PAlg l) {I : Type} [Fintype I] {e : I → A.A}
    (h : CompleteOrthogonalIdempotents e) : ∑ i, A.sharp (e i) = 1 := by
  have := (sharp_sum A Finset.univ e (fun i _ => h.idem i) (fun i _ j _ hij => h.ortho hij)).1
  rw [← this, h.complete]
  exact (map_one A.sharp)

theorem ind_mul_ind (A : PAlg l) (m : ℕ) (c : ZMod (l ^ m)) :
    ind A m c * ind A m c = ind A m c := by
  refine cont_ext fun z => ?_
  rw [map_mul, ev_ind]
  split_ifs <;> simp

theorem ind_orth (A : PAlg l) (m : ℕ) {c c' : ZMod (l ^ m)} (h : c ≠ c') :
    ind A m c * ind A m c' = 0 := by
  refine cont_ext fun z => ?_
  rw [map_mul, ev_ind, ev_ind, map_zero]
  split_ifs with h1 h2
  · exact absurd (h1.symm.trans h2) h
  all_goals simp

theorem sum_ind (A : PAlg l) (m : ℕ) : ∑ c, ind A m c = 1 := by
  refine cont_ext fun z => ?_

  rw [map_sum, map_one]
  simp only [ev_ind]
  rw [Finset.sum_ite_eq]
  simp

theorem coi_ind (A : PAlg l) (m : ℕ) : CompleteOrthogonalIdempotents (ind A m) :=
  ⟨⟨ind_mul_ind A m, fun _ _ h => ind_orth A m h⟩, sum_ind A m⟩

theorem coi_map {A t : PAlg l} (ψ : A.cont ℤ_[l] ⟶ t) (m : ℕ) :
    CompleteOrthogonalIdempotents fun c => Hom.f ψ (ind A m c) :=
  (coi_ind A m).map (Hom.f ψ)

theorem contMap_ind {A A' : PAlg l} (φ : A ⟶ A') (m : ℕ) (c : ZMod (l ^ m)) :
    Hom.f (contMap φ ℤ_[l]) (ind A m c) = ind A' m c := by
  refine cont_ext fun z => ?_
  change Hom.f φ (Hom.f (A.evCont z) (ind A m c)) = _
  rw [ev_ind, ev_ind]
  split_ifs <;> simp

theorem exists_roots (A : PAlg l) (a : A.A) :
    ∃ ρ : ℕ → A.A, ρ 0 = a ∧ ∀ m, ρ (m + 1) ^ l = ρ m := by
  choose g hg using A.frob_bijective.2
  refine ⟨fun m => g^[m] a, rfl, fun m => ?_⟩
  show (g^[m + 1] a) ^ l = g^[m] a
  rw [Function.iterate_succ_apply']
  exact hg _

theorem roots_unique (A : PAlg l) {a b : ℕ → A.A} (h0 : a 0 = b 0)
    (ha : ∀ m, a (m + 1) ^ l = a m) (hb : ∀ m, b (m + 1) ^ l = b m) : a = b := by
  funext m
  induction m with
  | zero => exact h0
  | succ m ih => exact A.frob_bijective.1 ((ha m).trans (ih.trans (hb m).symm))

theorem mul_sub_eq_zero_of_sum {R I : Type} [CommRing R] [Fintype I] [DecidableEq I] {a b : I → R}
    (hi : ∀ i, a i * a i = a i) (ho : ∀ i j, i ≠ j → a i * a j = 0) {x : R}
    (hx : x = ∑ i, a i * b i) (i : I) : a i * (x - b i) = 0 := by
  rw [hx, mul_sub, Finset.mul_sum, Finset.sum_eq_single i, ← mul_assoc, hi, sub_self]
  · intro j _ hj
    rw [← mul_assoc, ho i j hj.symm, zero_mul]
  · simp

theorem eq_sum_of_mul_sub {R I : Type} [CommRing R] [Fintype I] {a b : I → R}
    (h1 : ∑ i, a i = 1) {x : R} (hx : ∀ i, a i * (x - b i) = 0) : x = ∑ i, a i * b i := by
  have : ∑ i, a i * x = ∑ i, a i * b i :=
    Finset.sum_congr rfl fun i _ => by have := hx i; rw [mul_sub, sub_eq_zero] at this; exact this
  rw [← this, ← Finset.sum_mul, h1, one_mul]

end GlobalTheory.CompanionTheory.ContUniv
end
end
