module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
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
public import Mathlib.RingTheory.Polynomial.GaussNorm
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.Finite.Basic
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

@[expose] public section

section

open Polynomial

namespace GlobalTheory.ResiduePowerFixed

theorem pow_fixed_of_algebraic (l : ℕ) [Fact (Nat.Prime l)] {k : Type} [Field k]
    [Algebra (ZMod l) k] (y : k) (hy : IsAlgebraic (ZMod l) y) :
    ∃ N : ℕ, 0 < N ∧ y ^ l ^ N = y := by
  let F := IntermediateField.adjoin (ZMod l) {y}
  haveI : FiniteDimensional (ZMod l) F := IntermediateField.adjoin.finiteDimensional hy.isIntegral
  haveI : Finite F := Module.finite_of_finite (ZMod l)
  letI := Fintype.ofFinite F
  haveI : CharP F l := charP_of_injective_algebraMap (algebraMap (ZMod l) F).injective l
  obtain ⟨n, -, hcard⟩ := FiniteField.card F l
  refine ⟨n, n.pos, ?_⟩
  have h := FiniteField.pow_card (⟨y, IntermediateField.mem_adjoin_simple_self _ y⟩ : F)
  rw [hcard] at h
  simpa using congrArg Subtype.val h

theorem exists_primitive {Ω : Type} [Field Ω] [Algebra ℚ Ω] (x : Ω) (hx : IsAlgebraic ℚ x) :
    ∃ p : ℤ[X], p.IsPrimitive ∧ aeval x p = 0 := by
  have hx' : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).mpr hx
  obtain ⟨p, hp0, hp⟩ := hx'
  refine ⟨p.primPart, p.isPrimitive_primPart, ?_⟩
  have hc : algebraMap ℤ Ω p.content ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ Ω]
    refine (_root_.map_ne_zero _).mpr ?_
    have : p.content ≠ 0 := Polynomial.content_eq_zero_iff.not.mpr hp0
    rw [algebraMap_int_eq, eq_intCast]
    exact_mod_cast this
  rw [Polynomial.eq_C_content_mul_primPart p, map_mul, aeval_C] at hp
  exact (mul_eq_zero.mp hp).resolve_left hc

theorem residue_pow_fixed (l : ℕ) [Fact (Nat.Prime l)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (hl : A.valuation (l : Ω) < 1) (xA : A) :
    ∃ N : ℕ, 0 < N ∧ IsLocalRing.residue A xA ^ l ^ N = IsLocalRing.residue A xA := by
  classical

  have hlm : (l : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    simpa using hl
  have hl0 : ((l : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hlm
  haveI hchar : CharP (IsLocalRing.ResidueField A) l := by
    obtain ⟨q, hq⟩ := CharP.exists (IsLocalRing.ResidueField A)
    haveI := hq
    have hdvd : q ∣ l := (CharP.cast_eq_zero_iff _ q l).mp hl0
    rcases (Fact.out : l.Prime).eq_one_or_self_of_dvd q hdvd with h1 | h1
    · exfalso
      subst h1
      have h := (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) 1 1).mpr dvd_rfl
      have h' : (1 : IsLocalRing.ResidueField A) = 0 := by
        rw [← Nat.cast_one]
        exact h
      exact one_ne_zero h'
    · subst h1
      exact hq
  letI : Algebra (ZMod l) (IsLocalRing.ResidueField A) := ZMod.algebra _ l
  apply pow_fixed_of_algebraic l

  have hxalg : IsAlgebraic ℚ (xA : Ω) := Algebra.IsAlgebraic.isAlgebraic _
  obtain ⟨p, hprim, hp⟩ := exists_primitive (xA : Ω) hxalg
  refine ⟨p.map (Int.castRingHom (ZMod l)), ?_, ?_⟩
  · intro h0
    have hdvd : ∀ n, (l : ℤ) ∣ p.coeff n := fun n => by
      have h := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q n) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at h
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp h
    have hC : Polynomial.C (l : ℤ) ∣ p := (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hdvd
    have hcont := Polynomial.dvd_content_iff_C_dvd.mpr hC
    rw [hprim.content_eq_one] at hcont
    have h1 := Int.eq_one_of_dvd_one (by positivity) hcont
    exact (Fact.out : l.Prime).one_lt.ne' (by exact_mod_cast h1)
  · have hA : aeval xA p = 0 := by
      have h := Polynomial.aeval_algHom_apply (A.subtype.toIntAlgHom) xA p
      have h2 : A.subtype.toIntAlgHom (aeval xA p) = 0 := by
        rw [← h]
        exact hp
      exact Subtype.ext h2
    have e : aeval (IsLocalRing.residue A xA) (p.map (Int.castRingHom (ZMod l))) =
        aeval (IsLocalRing.residue A xA) p := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map]
      congr 1
      exact RingHom.ext_int _ _
    rw [e]
    rw [show IsLocalRing.residue A xA = (IsLocalRing.residue A).toIntAlgHom xA from rfl,
      Polynomial.aeval_algHom_apply, hA, map_zero]

end GlobalTheory.ResiduePowerFixed
end

section

open TensorProduct Coalgebra AddMonoidAlgebra

namespace GlobalTheory

section Units

variable {A : Type*} [CommRing A] {X : Type*} [AddCommGroup X]

variable [IsDomain A]

variable [Module.Free ℤ X]


end Units

section Coordinates

variable {X : Type*} [Zero X] {N : Type*} [AddCommGroup N]

theorem coboundary_apply_zero_left (g : X →₀ N) (x : X) :
    (g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
      g.mapDomain (fun y => (y, (0 : X))) : X × X →₀ N) (0, x) = g x := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.sub_apply] at hf hg ⊢
    rw [← hf, ← hg]; abel
  | single y m =>
    simp only [Finsupp.mapDomain_single, Finsupp.add_apply, Finsupp.sub_apply,
      Finsupp.single_apply, Prod.mk.injEq]
    by_cases h : y = 0
    · subst h; simp
    · simp [h]

theorem finsupp_two_cocycle_eq_coboundary (f : X × X →₀ N)
    (hf : f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
      f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) = 0)
    (g : X →₀ N) (hg : ∀ x, g x = f (0, x)) :
    g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
      g.mapDomain (fun y => (y, (0 : X))) = f := by
  classical
  let s : (X × X →₀ N) →+ (X →₀ N) :=
    Finsupp.comapDomain.addMonoidHom (f := fun x => ((0 : X), x)) (Prod.mk_right_injective 0)
  have hs : ∀ f x, s f x = f (0, x) := fun _ _ => rfl
  have key : ∀ (f : X × X →₀ N) (q : X × X),
      (f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
        f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) :
          X × X × X →₀ N) (0, q) +
      ((s f).mapDomain (fun y => ((0 : X), y)) - (s f).mapDomain (fun y => (y, y)) +
        (s f).mapDomain (fun y => (y, (0 : X))) : X × X →₀ N) q = f q := by
    intro f q
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      simp only [map_add (f := _), Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.sub_apply] at hf hg ⊢
      rw [← hf, ← hg]; abel
    | single p m =>
      obtain ⟨y, z⟩ := p
      by_cases h : y = 0
      · subst h
        have : s (Finsupp.single (0, z) m) = Finsupp.single z m := by
          ext x; simp [hs, Finsupp.single_apply]
        simp [this, Finsupp.single_apply]
      · have : s (Finsupp.single (y, z) m) = 0 := by
          ext x; simp [hs, h]
        simp [this, Finsupp.single_apply, h]
  have e : g = s f := Finsupp.ext hg
  ext q
  rw [← key f q, hf, e]
  simp

end Coordinates

section Ring

variable {X : Type*} [Zero X] {A : Type*} [Ring A]

theorem addMonoidAlgebra_coboundary_eq_iff (f : A[X × X])
    (hf : mapDomain (fun p => ((0 : X), p.1, p.2)) f - mapDomain (fun p => (p.1, p.1, p.2)) f +
      mapDomain (fun p => (p.1, p.2, p.2)) f - mapDomain (fun p => (p.1, p.2, (0 : X))) f = 0)
    (g : A[X]) :
    mapDomain (fun y => ((0 : X), y)) g - mapDomain (fun y => (y, y)) g +
      mapDomain (fun y => (y, (0 : X))) g = f ↔ ∀ x, g.coeff x = f.coeff (0, x) := by
  refine ⟨fun h x => ?_, fun h => coeff_injective
    (finsupp_two_cocycle_eq_coboundary f.coeff (congrArg coeff hf) g.coeff h)⟩
  rw [← h]
  exact (coboundary_apply_zero_left g.coeff x).symm

theorem addMonoidAlgebra_existsUnique_coboundary (f : A[X × X])
    (hf : mapDomain (fun p => ((0 : X), p.1, p.2)) f - mapDomain (fun p => (p.1, p.1, p.2)) f +
      mapDomain (fun p => (p.1, p.2, p.2)) f - mapDomain (fun p => (p.1, p.2, (0 : X))) f = 0) :
    ∃! g : A[X], mapDomain (fun y => ((0 : X), y)) g - mapDomain (fun y => (y, y)) g +
      mapDomain (fun y => (y, (0 : X))) g = f := by
  simp only [addMonoidAlgebra_coboundary_eq_iff f hf]
  exact ⟨ofCoeff (f.coeff.comapDomain (fun x => ((0 : X), x)) (Prod.mk_right_injective 0).injOn),
    fun _ => rfl, fun g hg => coeff_injective (Finsupp.ext hg)⟩

end Ring

section Tensor

variable {R : Type*} [CommRing R] {H : Type*} [Ring H] [Bialgebra R H]
variable {M : Type*} [AddCommGroup M] [Module R M]


variable {X : Type*} [AddMonoid X]


end Tensor

universe u v w

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory

theorem exists_gauss_size_polynomial (K : Type) [NormedField K] [IsUltrametricDist K] :
    ∃ G : K[X] → ℝ, (∀ p, 0 ≤ G p) ∧ (∀ p i, ‖p.coeff i‖ ≤ G p) ∧
      (∀ p r, (∀ i, ‖p.coeff i‖ ≤ r) → G p ≤ r) ∧
      (∀ p q, G (p * q) = G p * G q) ∧ (∀ p q, G (p + q) ≤ max (G p) (G q)) ∧
      (∀ a, G (C a) = ‖a‖) ∧ G X = 1 := by
  let v : AbsoluteValue K ℝ := NormedField.toAbsoluteValue K
  have hv : ∀ a, v a = ‖a‖ := fun _ => rfl
  have hna : IsNonarchimedean v := fun a b => IsUltrametricDist.norm_add_le_max a b
  refine ⟨gaussNorm v 1, fun p => gaussNorm_nonneg v p zero_le_one, fun p i => ?_,
    fun p r hr => ?_, fun p q => gaussNorm_mul hna one_pos p q,
    fun p q => isNonarchimedean_gaussNorm v hna zero_le_one p q, fun a => ?_, ?_⟩
  · simpa [hv] using le_gaussNorm v p zero_le_one i
  · obtain ⟨i, hi⟩ := exists_eq_gaussNorm v 1 p
    rw [hi, hv, one_pow, mul_one]
    exact hr i
  · rw [gaussNorm_C, hv]
  · rw [← monomial_one_one_eq_X, gaussNorm_monomial, hv]
    simp

theorem isogeny_numerator_coeff_norm_le_one :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (A B A' B' : K) (n h : K[X]),
      ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ‖A'‖ ≤ 1 → ‖B'‖ ≤ 1 → (∀ i, ‖h.coeff i‖ ≤ 1) →
      (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2
        = n ^ 3 + C A' * n * h ^ 4 + C B' * h ^ 6 → ∀ i, ‖n.coeff i‖ ≤ 1 := by
  intro K _ _ A B A' B' n h hA hB hA' hB' hh heq
  obtain ⟨G, h0, hle, hub, hmul, hadd, hC, hX⟩ := exists_gauss_size_polynomial K
  have hone : G 1 = 1 := by simpa using hC 1
  have hpow : ∀ p (k : ℕ), G (p ^ k) = G p ^ k := by
    intro p k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  have hneg : ∀ p, G (-p) ≤ G p := fun p =>
    hub _ _ fun i => by rw [coeff_neg, norm_neg]; exact hle p i
  have hadd' : ∀ p q r, G p ≤ r → G q ≤ r → G (p + q) ≤ r := fun p q r hp hq =>
    (hadd p q).trans (max_le hp hq)
  have hsub : ∀ p q r, G p ≤ r → G q ≤ r → G (p - q) ≤ r := fun p q r hp hq => by
    rw [sub_eq_add_neg]
    exact hadd' _ _ _ hp ((hneg q).trans hq)
  have hmul' : ∀ p q r s, G p ≤ r → G q ≤ s → G (p * q) ≤ r * s := fun p q r s hp hq => by
    rw [hmul]
    exact mul_le_mul hp hq (h0 q) ((h0 p).trans hp)
  have hpow' : ∀ p r (k : ℕ), G p ≤ r → G (p ^ k) ≤ r ^ k := fun p r k hp => by
    rw [hpow]
    exact pow_le_pow_left₀ (h0 p) hp k
  have hder : ∀ p, G (derivative p) ≤ G p := fun p =>
    hub _ _ fun i => by
      rw [coeff_derivative, norm_mul]
      have h1 : ‖((i : K) + 1)‖ ≤ 1 := by
        exact_mod_cast IsUltrametricDist.norm_natCast_le_one K (i + 1)
      calc ‖p.coeff (i + 1)‖ * ‖((i : K) + 1)‖ ≤ G p * 1 :=
            mul_le_mul (hle p _) h1 (norm_nonneg _) (h0 p)
        _ = G p := mul_one _
  have hh1 : G h ≤ 1 := hub _ _ hh
  suffices hn : G n ≤ 1 from fun i => (hle n i).trans hn
  by_contra hg
  push Not at hg
  set g := G n with hgdef
  have hX1 : G X ≤ 1 := hX.le
  have hcub : G (X ^ 3 + C A * X + C B) ≤ 1 := by
    refine hadd' _ _ _ (hadd' _ _ _ ?_ ?_) ?_
    · simpa using hpow' X 1 3 hX1
    · simpa using hmul' (C A) X 1 1 (by rw [hC]; exact hA) hX1
    · rw [hC]; exact hB
  have h2n : G (2 * n) ≤ g := by
    rw [two_mul]
    exact hadd' _ _ _ le_rfl le_rfl
  have hW : G (derivative n * h - 2 * n * derivative h) ≤ g := by
    refine hsub _ _ _ ?_ ?_
    · simpa using hmul' _ _ g 1 (hder n) hh1
    · simpa using hmul' _ _ g 1 h2n ((hder h).trans hh1)
  have hL : G ((X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2)
      ≤ g ^ 2 := by
    simpa using hmul' _ _ 1 (g ^ 2) hcub (hpow' _ g 2 hW)
  have hgg : g ≤ g ^ 2 := by nlinarith
  have h1g : 1 ≤ g ^ 2 := hg.le.trans hgg
  have hA2 : G (C A' * n * h ^ 4) ≤ g ^ 2 := by
    refine le_trans ?_ hgg
    simpa using hmul' _ _ (1 * g) (1 ^ 4)
      (hmul' (C A') n 1 g (by rw [hC]; exact hA') le_rfl) (hpow' h 1 4 hh1)
  have hB2 : G (C B' * h ^ 6) ≤ g ^ 2 := by
    refine le_trans ?_ h1g
    simpa using hmul' (C B') _ 1 (1 ^ 6) (by rw [hC]; exact hB') (hpow' h 1 6 hh1)
  have hn3 : n ^ 3 = (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2
      - C A' * n * h ^ 4 - C B' * h ^ 6 := by
    rw [heq]; ring
  have h3 : G (n ^ 3) ≤ g ^ 2 := by
    rw [hn3]
    exact hsub _ _ _ (hsub _ _ _ hL hA2) hB2
  rw [hpow, ← hgdef] at h3
  nlinarith

end GlobalTheory
end

section

open MeasureTheory Filter Topology Set

namespace GlobalTheory

theorem cauchy_parallelogram_upper_half_plane :
    ∀ (g : ℂ → ℂ) (τ : ℂ) (S : ℝ), DifferentiableOn ℂ g {z : ℂ | 0 < z.im} → 0 < τ.im → 0 ≤ S →
    (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I)) =
      Complex.I * (∫ s in (0:ℝ)..S, g (Complex.I + s * Complex.I)) -
        Complex.I * (∫ s in (0:ℝ)..S, g (τ + s * Complex.I)) +
        (τ - Complex.I) * ∫ t in (0:ℝ)..1, g (Complex.I + t * (τ - Complex.I) + S * Complex.I) := by
  intro g τ S hg hτ hS
  set φ : ℝ × ℝ → ℂ := fun x => Complex.I + (x.1 : ℂ) * (τ - Complex.I) + (x.2 : ℂ) * Complex.I
    with hφdef
  set L : ℝ × ℝ →L[ℝ] ℂ := (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (τ - Complex.I) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight Complex.I with hLdef
  have hφL : φ = fun x => Complex.I + L x := by
    funext x; simp [φ, L, Complex.real_smul]; ring
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hpos : ∀ x : ℝ × ℝ, 0 ≤ x.1 → x.1 ≤ 1 → 0 ≤ x.2 → 0 < (φ x).im := by
    rintro ⟨t, s⟩ h0 h1 h2
    simp only [φ, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
    rcases h1.lt_or_eq with h | h
    · nlinarith [mul_nonneg h0 hτ.le]
    · subst h; simp at *; nlinarith
  have hφc : Continuous φ := by
    rw [hφL]; exact continuous_const.add L.continuous
  have hcont : ContinuousOn (fun x => g (φ x)) (uIcc (0:ℝ) 1 ×ˢ uIcc (0:ℝ) S) := by
    refine hg.continuousOn.comp hφc.continuousOn ?_
    intro x hx
    rw [uIcc_of_le zero_le_one, uIcc_of_le hS] at hx
    exact hpos x hx.1.1 hx.1.2 hx.2.1
  set F' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℂ := fun x =>
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv g (φ x))).restrictScalars ℝ).comp L
  have hder : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1) ×ˢ Ioo (min (0:ℝ) S) (max (0:ℝ) S),
      HasFDerivAt (fun x => g (φ x)) (F' x) x := by
    intro x hx
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one, min_eq_left hS, max_eq_right hS] at hx
    have hz : 0 < (φ x).im := hpos x hx.1.1.le hx.1.2.le hx.2.1.le
    have hgd : HasDerivAt g (deriv g (φ x)) (φ x) :=
      (hg.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
    have hφd : HasFDerivAt φ L x := by
      rw [hφL]; exact L.hasFDerivAt.const_add _
    exact (hgd.hasFDerivAt.restrictScalars ℝ).comp x hφd
  have key := integral2_divergence_prod_of_hasFDerivAt
    (fun x => Complex.I * g (φ x)) (fun x => -(τ - Complex.I) * g (φ x))
    (fun x => Complex.I • F' x) (fun x => (-(τ - Complex.I)) • F' x) 0 0 1 S
    (continuousOn_const.mul hcont) (continuousOn_const.mul hcont)
    (fun x hx => (hder x hx).const_mul _) (fun x hx => (hder x hx).const_mul _)
    (by
      have : (fun x : ℝ × ℝ => (Complex.I • F' x) (1, 0) + ((-(τ - Complex.I)) • F' x) (0, 1))
          = fun _ => 0 := by
        funext x; simp [F', L]; ring
      rw [this]; exact integrableOn_zero)
  have hzero : ∀ x : ℝ × ℝ, (Complex.I • F' x) (1, 0) + ((-(τ - Complex.I)) • F' x) (0, 1) = 0 := by
    intro x; simp [F', L]; ring
  simp only [hzero, intervalIntegral.integral_zero, intervalIntegral.integral_const_mul] at key
  have e1 : ∀ s : ℝ, φ (1, s) = τ + s * Complex.I := by
    intro s; simp only [φ]; push_cast; ring
  have e0 : ∀ s : ℝ, φ (0, s) = Complex.I + s * Complex.I := by
    intro s; simp only [φ]; push_cast; ring
  have eS : ∀ t : ℝ, φ (t, S) = Complex.I + t * (τ - Complex.I) + S * Complex.I := fun _ => rfl
  have eT : ∀ t : ℝ, φ (t, 0) = Complex.I + t * (τ - Complex.I) := by
    intro t; simp only [φ]; push_cast; ring
  simp only [e1, e0, eS, eT] at key
  linear_combination -key

end GlobalTheory
end

section

namespace GlobalTheory.NormBoundOfSpan

theorem norm_le_of_mem_span {K E ι : Type} [NormedField K] [AddCommGroup E] [Module K E]
    (φ : ι → E →ₗ[K] K) :
    ∀ f ∈ Submodule.span K (Set.range φ), ∃ (C : ℝ), (0 : ℝ) ≤ C ∧ ∀ (p : E) (r : ℝ),
      (0 : ℝ) ≤ r → (∀ (j : ι), ‖(φ j : E → K) p‖ ≤ r) → ‖(f : E → K) p‖ ≤ C * r := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨1, zero_le_one, fun p r _ h => by simpa using h j⟩
  | zero => exact ⟨0, le_rfl, fun p r _ _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C, hC, h1⟩ := hx
    obtain ⟨D, hD, h2⟩ := hy
    refine ⟨C + D, add_nonneg hC hD, fun p r hr h => ?_⟩
    rw [LinearMap.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h1 p r hr h) (h2 p r hr h))
  | smul a x _ hx =>
    obtain ⟨C, hC, h1⟩ := hx
    refine ⟨‖a‖ * C, mul_nonneg (norm_nonneg a) hC, fun p r hr h => ?_⟩
    rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 p r hr h) (norm_nonneg a)

end GlobalTheory.NormBoundOfSpan
end
