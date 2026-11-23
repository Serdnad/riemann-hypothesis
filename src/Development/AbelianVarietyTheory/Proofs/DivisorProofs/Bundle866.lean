module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle148
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle266
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle833
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris

variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} in
theorem _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish (δ : DividedPowers J) (a : B) (N : ℕ)
    (h : ∀ n, N ≤ n → δ.dpow n a = 0) :
    _root_.GlobalTheory.Cris.dpExp δ a = ∑ n ∈ Finset.range N, δ.dpow n a := by
  unfold _root_.GlobalTheory.Cris.dpExp
  apply finsum_eq_sum_of_support_subset
  intro n hn
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  exact hn (h n (not_lt.mp hlt))


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} in
theorem _root_.GlobalTheory.Cris.IsNilDP.dpExp_add_eq_mul {δ : DividedPowers J}
    (h : _root_.GlobalTheory.Cris.IsNilDP δ) {a b : B} (ha : a ∈ J) (hb : b ∈ J) :
    _root_.GlobalTheory.Cris.dpExp δ (a + b) = _root_.GlobalTheory.Cris.dpExp δ a * _root_.GlobalTheory.Cris.dpExp δ b := by
  obtain ⟨N, hN⟩ := h
  have hvan : ∀ x ∈ J, ∀ n, N ≤ n → δ.dpow n x = 0 := by
    intro x hx n hn
    simpa using hN [(n, x)] (by simpa using hx) (by simpa using hn)
  have hpair : ∀ i j, N ≤ i + j → δ.dpow i a * δ.dpow j b = 0 := by
    intro i j hij
    simpa using hN [(i, a), (j, b)] (by simp [ha, hb]) (by simpa using hij)
  let F : ℕ × ℕ → B := fun p => δ.dpow p.1 a * δ.dpow p.2 b
  rw [_root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ (a + b) N (hvan _ (J.add_mem ha hb)),
    _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ a N (hvan a ha), _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ b N (hvan b hb),
    Finset.sum_mul_sum, ← Finset.sum_product' (f := fun i j => δ.dpow i a * δ.dpow j b)]
  have hfilter : ∑ p ∈ Finset.range N ×ˢ Finset.range N with p.1 + p.2 < N, F p =
      ∑ p ∈ Finset.range N ×ˢ Finset.range N, F p := by
    refine Finset.sum_filter_of_ne fun p _ hp => ?_
    by_contra hlt
    exact hp (hpair p.1 p.2 (not_lt.mp hlt))
  rw [← hfilter, ← Finset.sum_fiberwise_of_maps_to (t := Finset.range N)
    (g := fun p : ℕ × ℕ => p.1 + p.2) (fun p hp => by simpa using (Finset.mem_filter.mp hp).2)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [δ.dpow_add ha hb]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ⟨i, j⟩
  simp only [Finset.mem_range] at hn
  simp only [Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range]
  omega


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry DividedPowers in
variable {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'} in
theorem _root_.GlobalTheory.Cris.dpExp_add_and_natural (B B' : Type) [CommRing B] [CommRing B'] (J : Ideal B) (J' : Ideal B')
    (δ : DividedPowers J) (δ' : DividedPowers J') (h : _root_.GlobalTheory.Cris.IsNilDP δ) :
    (∀ a ∈ J, ∀ b ∈ J, _root_.GlobalTheory.Cris.dpExp δ (a + b) = _root_.GlobalTheory.Cris.dpExp δ a * _root_.GlobalTheory.Cris.dpExp δ b) ∧
      (∀ f : B →+* B', IsDPMorphism δ δ' f → ∀ a ∈ J,
        f (_root_.GlobalTheory.Cris.dpExp δ a) = _root_.GlobalTheory.Cris.dpExp δ' (f a)) := by
  refine ⟨fun a ha b hb => h.dpExp_add_eq_mul ha hb, fun f hf a ha => ?_⟩
  obtain ⟨N, hN⟩ := h
  have hvan : ∀ n, N ≤ n → δ.dpow n a = 0 := by
    intro n hn
    simpa using hN [(n, a)] (by simpa using ha) (by simpa using hn)
  have hvan' : ∀ n, N ≤ n → δ'.dpow n (f a) = 0 := by
    intro n hn
    rw [← hf.map_dpow ha, hvan n hn, map_zero]

  rw [_root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ a N hvan, _root_.GlobalTheory.Cris.dpExp_eq_sum_range_of_vanish δ' (f a) N hvan',
  map_sum]
  exact Finset.sum_congr rfl fun n _ => hf.map_dpow ha

end GlobalTheory.Cris
end

section

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DPLoc

variable {B S : Type} [CommRing B] [CommRing S] [Algebra B S] (M : Submonoid B)
  [IsLocalization M S] {J : Ideal B} (δ : DividedPowers J)


include M in
theorem wellDef {u v : S} {j j' : B} (hj : j ∈ J) (hj' : j' ∈ J)
    (h : u * algebraMap B S j = v * algebraMap B S j') (n : ℕ) :
    u ^ n * algebraMap B S (δ.dpow n j) = v ^ n * algebraMap B S (δ.dpow n j') := by
  obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj M u
  obtain ⟨⟨c, t⟩, hc⟩ := IsLocalization.surj M v
  simp only at ha hc
  have h1 : algebraMap B S (a * t * j) = algebraMap B S (c * s * j') := by
    simp only [map_mul, ← ha, ← hc]
    linear_combination (algebraMap B S s * algebraMap B S t) * h
  obtain ⟨m, hm⟩ := (IsLocalization.eq_iff_exists M S).1 h1
  have h2 : ((m : B) * (a * t)) ^ n * δ.dpow n j = ((m : B) * (c * s)) ^ n * δ.dpow n j' := by
    rw [← δ.dpow_mul hj, ← δ.dpow_mul hj']
    congr 1
    linear_combination hm
  have h3 := congrArg (algebraMap B S) h2
  simp only [map_mul, map_pow, ← ha, ← hc, mul_pow] at h3
  have hu : IsUnit ((algebraMap B S m) ^ n * (algebraMap B S s) ^ n * (algebraMap B S t) ^ n) :=
    (((IsLocalization.map_units S m).pow n).mul ((IsLocalization.map_units S s).pow n)).mul
      ((IsLocalization.map_units S t).pow n)
  apply hu.mul_left_cancel
  linear_combination h3


include M in
theorem rep₂ {x y : S} (hx : x ∈ J.map (algebraMap B S)) (hy : y ∈ J.map (algebraMap B S)) :
    ∃ (u : S) (j j' : B), j ∈ J ∧ j' ∈ J ∧ x = u * algebraMap B S j ∧
      y = u * algebraMap B S j' := by
  obtain ⟨⟨j, s⟩, hj⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hx
  obtain ⟨⟨j', t⟩, hj'⟩ := (IsLocalization.mem_map_algebraMap_iff M S).1 hy
  simp only at hj hj'
  obtain ⟨u, hu⟩ := (IsLocalization.map_units S (s * t)).exists_left_inv
  simp only [Submonoid.coe_mul, map_mul] at hu
  refine ⟨u, t * j, s * j', J.mul_mem_left _ j.2, J.mul_mem_left _ j'.2, ?_, ?_⟩
  · rw [map_mul, ← hj]; linear_combination (-x) * hu
  · rw [map_mul, ← hj']; linear_combination (-y) * hu


include M in
theorem rep {x : S} (hx : x ∈ J.map (algebraMap B S)) :
    ∃ (u : S) (j : B), j ∈ J ∧ x = u * algebraMap B S j := by
  obtain ⟨u, j, _, hj, _, e, _⟩ := rep₂ M hx hx
  exact ⟨u, j, hj, e⟩


open Classical in
def ext (n : ℕ) (x : S) : S :=
  if h : ∃ p : S × B, p.2 ∈ J ∧ x = p.1 * algebraMap B S p.2 then
    h.choose.1 ^ n * algebraMap B S (δ.dpow n h.choose.2) else 0


include M in
theorem ext_eq (n : ℕ) (u : S) {j : B} (hj : j ∈ J) :
    ext δ n (u * algebraMap B S j) = u ^ n * algebraMap B S (δ.dpow n j) := by
  have h : ∃ p : S × B, p.2 ∈ J ∧ u * algebraMap B S j = p.1 * algebraMap B S p.2 :=
    ⟨(u, j), hj, rfl⟩
  rw [ext, dite_eq_left h]
  exact (wellDef M δ hj h.choose_spec.1 h.choose_spec.2 n).symm

def dp : DividedPowers (J.map (algebraMap B S)) where
  dpow := ext δ
  dpow_null {n x} hx := by
    rw [ext, dite_eq_right]
    rintro ⟨p, hp, rfl⟩
    exact hx (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hp))
  dpow_zero hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    simp [ext_eq M δ _ _ hj, δ.dpow_zero hj]
  dpow_one hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    simp [ext_eq M δ _ _ hj, δ.dpow_one hj]
  dpow_mem hn hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    rw [ext_eq M δ _ _ hj]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (δ.dpow_mem hn hj))
  dpow_add hx hy := by
    obtain ⟨u, j, j', hj, hj', rfl, rfl⟩ := rep₂ M hx hy

    rw [← mul_add, ← map_add (f := _), ext_eq M δ _ _ (J.add_mem hj hj'), δ.dpow_add hj hj', map_sum,
    Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [ext_eq M δ _ _ hj, ext_eq M δ _ _ hj', ← (Finset.HasAntidiagonal.mem_antidiagonal.1 hk : k.1 + k.2 = _), map_mul]
    ring
  dpow_mul hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    rw [← mul_assoc, ext_eq M δ _ _ hj, ext_eq M δ _ _ hj]
    ring
  mul_dpow {m n x} hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    have := congrArg (algebraMap B S) (δ.mul_dpow (m := m) (n := n) hj)
    rw [map_mul, map_mul, map_natCast] at this
    simp only [ext_eq M δ _ _ hj]
    linear_combination u ^ (m + n) * this
  dpow_comp {m n x} hn hx := by
    obtain ⟨u, j, hj, rfl⟩ := rep M hx
    rw [ext_eq M δ _ _ hj, ext_eq M δ _ _ hj, ext_eq M δ _ _ (δ.dpow_mem hn hj),
      δ.dpow_comp hn hj, map_mul, map_natCast]
    ring

theorem dp_dpow (n : ℕ) (u : S) {j : B} (hj : j ∈ J) :
    (dp M δ).dpow n (u * algebraMap B S j) = u ^ n * algebraMap B S (δ.dpow n j) :=
  ext_eq M δ n u hj

theorem isDPMorphism : IsDPMorphism δ (dp (S := S) M δ) (algebraMap B S) :=
  ⟨le_rfl, fun {n} a ha ↦ by simpa using dp_dpow M δ n (1 : S) ha⟩

theorem isNilDP (h : IsNilDP δ) : IsNilDP (dp (S := S) M δ) := by
  obtain ⟨N, h⟩ := h
  have key : ∀ l : List (ℕ × S), (∀ p ∈ l, p.2 ∈ J.map (algebraMap B S)) →
      ∃ (c : S) (l' : List (ℕ × B)), (∀ p ∈ l', p.2 ∈ J) ∧
        (l'.map Prod.fst).sum = (l.map Prod.fst).sum ∧
        (l.map fun p ↦ (dp M δ).dpow p.1 p.2).prod =
          c * algebraMap B S (l'.map fun p ↦ δ.dpow p.1 p.2).prod := by
    intro l
    induction l with
    | nil => exact fun _ ↦ ⟨1, [], by simp⟩
    | cons p l ih =>
      intro hl
      obtain ⟨c, l', h1, h2, h3⟩ := ih fun q hq ↦ hl q (by simp [hq])
      obtain ⟨u, j, hj, e⟩ := rep M (hl p (by simp))
      refine ⟨u ^ p.1 * c, (p.1, j) :: l', ?_, by simp [h2], ?_⟩
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        exacts [hj, h1 q hq]
      · simp only [List.map_cons, List.prod_cons, map_mul]
        rw [h3, e, dp_dpow M δ _ _ hj]
        ring
  refine ⟨N, fun l hl hN ↦ ?_⟩
  obtain ⟨c, l', h1, h2, h3⟩ := key l hl
  rw [h3, h l' h1 (h2 ▸ hN), map_zero, mul_zero]

theorem isDPMorphism_of_comp {C : Type} [CommRing C] {J'' : Ideal C} (δ'' : DividedPowers J'')
    (g : S →+* C) (h : IsDPMorphism δ δ'' (g.comp (algebraMap B S))) :
    IsDPMorphism (dp M δ) δ'' g := by
  refine ⟨by rw [Ideal.map_map]; exact h.1, fun {n} x hx ↦ ?_⟩
  obtain ⟨u, j, hj, rfl⟩ := rep M hx
  have hm : g (algebraMap B S j) ∈ J'' := h.1 (Ideal.mem_map_of_mem _ hj)
  have e : δ''.dpow n (g (algebraMap B S j)) = g (algebraMap B S (δ.dpow n j)) := h.2 j hj
  rw [dp_dpow M δ _ _ hj, map_mul, δ''.dpow_mul hm, e, map_mul, map_pow]

theorem exists_away : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (b : B), IsNilDP δ → ∃ δ' : DividedPowers (J.map (algebraMap B (Localization.Away b))), IsNilDP δ' ∧ IsDPMorphism δ δ' (algebraMap B (Localization.Away b)) ∧ ∀ (C : Type) [CommRing C] (J'' : Ideal C) (δ'' : DividedPowers J'') (g : Localization.Away b →+* C), IsDPMorphism δ δ'' (g.comp (algebraMap B _)) → IsDPMorphism δ' δ'' g :=
  fun _ _ _ δ b h ↦ ⟨dp (Submonoid.powers b) δ, isNilDP _ δ h, isDPMorphism _ δ,
    fun _ _ _ δ'' g hg ↦ isDPMorphism_of_comp _ δ δ'' g hg⟩

end GlobalTheory.DPLoc
end
end

section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

namespace GlobalTheory.ExpFrame.CharUnit

open NumberField Polynomial in
private theorem le_one_of_forall_pow_le {a C : ℝ} (h : ∀ n : ℕ, a ^ n ≤ C) : a ≤ 1 := by
  by_contra ha
  push_neg at ha
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C ha
  exact absurd (h n) (not_le.mpr hn)


open NumberField Polynomial in
theorem _root_.GlobalTheory.ExpFrame.CharUnit.norm_eq_one_of_compact {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    [NormedField K] (χ : Γ →* Kˣ) (hc : Continuous fun g => ((χ g : Kˣ) : K)) (g : Γ) :
    ‖((χ g : Kˣ) : K)‖ = 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  have hb : ∀ h : Γ, ∀ n : ℕ, ‖((χ h : Kˣ) : K)‖ ^ n ≤ C := fun h n => by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow]
    exact hC _ ⟨h ^ n, rfl⟩
  have h1 := le_one_of_forall_pow_le (hb g)
  have h2 := le_one_of_forall_pow_le (hb g⁻¹)
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((χ g : Kˣ) : K)‖ := norm_pos_iff.mpr (χ g).ne_zero
  have : 1 ≤ ‖((χ g : Kˣ) : K)‖ := by
    by_contra hlt
    push_neg at hlt
    have := one_lt_inv₀ hpos |>.mpr hlt
    linarith
  linarith


open NumberField Polynomial in
theorem _root_.GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (χ : _root_.Formalism.ConjugateSelfDual.G E Ω →* (PadicAlgCl l)ˣ), Continuous (_root_.GlobalTheory.TripleGal.rk1 χ) → ∀ g, ‖((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1 := by
  intro E Ω _ _ _ _ _ l _ χ hχ g
  refine _root_.GlobalTheory.ExpFrame.CharUnit.norm_eq_one_of_compact χ ?_ g
  have h := (Units.continuous_val.comp hχ).matrix_elem 0 0
  convert h using 1
  funext x
  simp [_root_.GlobalTheory.TripleGal.rk1]

end GlobalTheory.ExpFrame.CharUnit
end

section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

noncomputable section

namespace GlobalTheory.RepFinExtJoint

theorem characterAsRankOneRep_entry {Γ K : Type} [Group Γ] [CommRing K] (χ : Γ →* Kˣ) (g : Γ) :
    ((GlobalTheory.TripleGal.rk1 χ g : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) 0 0 = ((χ g : Kˣ) : K) := by
  simp [GlobalTheory.TripleGal.rk1, Matrix.scalar_apply]

theorem exists_finExt_chars (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] {ι : Type} (χ : ι → G E Ω →* (PadicAlgCl l)ˣ)
    (hχ : ∀ s, Continuous (GlobalTheory.TripleGal.rk1 (χ s))) (S : Finset ι) (L₀ : FinExt l) :
    ∃ L : FinExt l, L₀.1 ≤ L.1 ∧ ∀ s ∈ S, ∀ g, ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ L.1 := by
  classical
  induction S using Finset.induction_on generalizing L₀ with
  | empty => exact ⟨L₀, le_rfl, fun s hs => absurd hs (Finset.notMem_empty s)⟩
  | insert i S hi ih =>
    obtain ⟨L₁, h01, h1⟩ := ih L₀
    obtain ⟨L₂, h12, h2⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) 1
      (GlobalTheory.TripleGal.rk1 (χ i)) (Units.continuous_val.comp (hχ i)) L₁
    refine ⟨L₂, h01.trans h12, fun s hs g => ?_⟩
    rcases Finset.mem_insert.1 hs with rfl | hs
    · have := h2 g 0 0
      rwa [characterAsRankOneRep_entry] at this
    · exact h12 (h1 s hs g)

theorem exists_finExt_root_emb (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∃ L : FinExt l, (∃ ζ : ↥L.1, IsPrimitiveRoot ζ l) ∧ ∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ L.1 := by
  classical
  obtain ⟨ζ, hζ⟩ : ∃ ζ : PadicAlgCl l, IsPrimitiveRoot ζ l := HasEnoughRootsOfUnity.prim
  let b := Module.finBasis ℚ E
  haveI : Fintype (E →+* PadicAlgCl l) := Fintype.ofFinite _
  let T : Finset (PadicAlgCl l) :=
    insert ζ (Finset.univ.image fun p : (E →+* PadicAlgCl l) × Fin (Module.finrank ℚ E) => p.1 (b p.2))
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] (T : Set (PadicAlgCl l))
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hT : ∀ x ∈ T, x ∈ K := fun x hx => IntermediateField.subset_adjoin _ _ hx
  refine ⟨⟨K, inferInstance⟩, ⟨⟨ζ, hT _ (Finset.mem_insert_self _ _)⟩, ?_⟩, fun τ x => ?_⟩
  · exact IsPrimitiveRoot.of_map_of_injective (f := K.val) (by simpa using hζ) K.val.injective

  · rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact SubfieldClass.qsmul_mem K _ (hT _ (Finset.mem_insert_of_mem
      (Finset.mem_image.2 ⟨(τ, i), Finset.mem_univ _, rfl⟩)))

theorem finext_joint : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n a t : ℕ) (r : G E Ω →* GL (Fin n) (PadicAlgCl l)) (ρ : G E Ω →* GL (Fin a) (PadicAlgCl l)) (χ : Fin t → G E Ω →* (PadicAlgCl l)ˣ), Continuous r → Continuous ρ → (∀ s, Continuous (GlobalTheory.TripleGal.rk1 (χ s))) → ∃ LL : FinExt l, (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) ∧ (∀ (τ : E →+* PadicAlgCl l) (x : E), τ x ∈ LL.1) ∧ (∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ LL.1) ∧ (∀ g i j, (ρ g : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j ∈ LL.1) ∧ ∀ s g, ((χ s g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ∈ LL.1 := by
  intro E Ω _ _ _ _ _ l _ n a t r ρ χ hr hρ hχ
  obtain ⟨L₀, ⟨ζ, hζ⟩, hemb⟩ := exists_finExt_root_emb E l
  obtain ⟨L₁, h01, h1⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) n r
    (Units.continuous_val.comp hr) L₀
  obtain ⟨L₂, h12, h2⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) a ρ
    (Units.continuous_val.comp hρ) L₁
  obtain ⟨L₃, h23, h3⟩ := exists_finExt_chars E Ω l χ hχ Finset.univ L₂
  refine ⟨L₃, ⟨⟨ζ, h23 (h12 (h01 ζ.2))⟩, ?_⟩, fun τ x => h23 (h12 (h01 (hemb τ x))),
    fun g i j => h23 (h12 (h1 g i j)), fun g i j => h23 (h2 g i j), fun s g => h3 s (Finset.mem_univ s) g⟩
  have h0 : IsPrimitiveRoot ((ζ : ↥L₀.1) : PadicAlgCl l) l :=
    hζ.map_of_injective (f := L₀.1.val) L₀.1.val.injective
  exact IsPrimitiveRoot.of_map_of_injective (f := L₃.1.val) h0 L₃.1.val.injective

end GlobalTheory.RepFinExtJoint
end
end

section

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.divisorsOfConstants_flat_normal_stage_at_origin : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (sA : A), sA ≠ 0 →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsNoetherianRing A') (_ : IsIntegrallyClosed A')
      (B' : Type) (_ : CommRing B') (_ : IsDomain B') (_ : IsLocalRing B') (_ : IsNoetherianRing B')
      (_ : IsIntegrallyClosed B') (_ : Algebra A' B') (_ : Module.Flat A' B')
      (ι : A →+* A') (α : A' →+* T) (β : Localization.AtPrime QA →+* B') (γ : B' →+* O),
      (algebraMap A' B').comp ι = β.comp (algebraMap A (Localization.AtPrime QA)) ∧
      γ.comp β = jA ∧ γ.comp (algebraMap A' B') = (algebraMap T O).comp α ∧ ι sA ≠ 0 ∧
      ∀ 𝔭 : Ideal A', 𝔭.IsPrime → 𝔭.height = 1 → ι sA ∈ 𝔭 →
        (𝔭.map (algebraMap A' B')).IsPrime := by
  first | (exact @GlobalTheory.GoodStageOrigin.good_stage) | (exact GlobalTheory.GoodStageOrigin.good_stage) | (intros; apply GlobalTheory.GoodStageOrigin.good_stage <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.exists_quotient_kernel_sup_frobeniusKernel : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G H : PDivGroup p k) (q : G ⟶ H), ∃ (C : Type) (_ : CommRing C) (_ : HopfAlgebra k C) (_ : IsCocomm k C) (_ : Module.Finite k C) (π : G.A 1 →ₐc[k] C), Function.Surjective π ∧ RingHom.ker π = kerIdeal (q.app 1) ⊔ frobKerIdeal p k (G.A 1) ∧ (∀ a ∈ augIdeal k C, a ^ p = 0) ∧ frobKerIdeal p k (G.A 1) ≤ augIdeal k (G.A 1) ^ 2 := by
  first | exact @GlobalTheory.PDiv.FrobKerInter.exists_quotient_kerIdeal_sup_frobKerIdeal | exact GlobalTheory.PDiv.FrobKerInter.exists_quotient_kerIdeal_sup_frobKerIdeal | (intros; apply GlobalTheory.PDiv.FrobKerInter.exists_quotient_kerIdeal_sup_frobKerIdeal <;> assumption)
end

section

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.frobeniusKernelIdeal_eq_kernel_relativeFrobenius :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
      (G : PDivGroup p R) (n : ℕ),
      frobKerIdeal p R (G.A n) = kerIdeal ((relFrob h G).app n) :=
  @GlobalTheory.PDiv.frobKerIdeal_eq_kerIdeal_relFrob
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.kummerReductionChernDefect_restriction : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → Sec.res g (GlobalTheory.EtC.RedChern.defect Q q U v) = GlobalTheory.EtC.RedChern.defect Q q V (Units.map g.appTop.hom.toMonoidHom v) := by
  first
  | exact @GlobalTheory.EtC.RedChern.res_defect
  | exact GlobalTheory.EtC.RedChern.res_defect
  | (intros; apply GlobalTheory.EtC.RedChern.res_defect <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pull_h1_surjective_of_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap σ)), Function.Bijective σ → Function.Surjective (pullHO1 h.w) := by
  first | exact @GlobalTheory.AbCoh.pullHO1_surjective_of_bijective_base | exact GlobalTheory.AbCoh.pullHO1_surjective_of_bijective_base | (intros; apply GlobalTheory.AbCoh.pullHO1_surjective_of_bijective_base <;> assumption)
end
