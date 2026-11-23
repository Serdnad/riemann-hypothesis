module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle145
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

@[expose] public section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoVan

theorem evV_awayMap {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)
    {x y z : MvPolynomial (Fin (N + 1)) K} {b : ℕ} (hy : y ∈ grK K N b) (hz : z = x * y)
    (V : X.Opens) (h : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) z)
    (h' : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) x) (u : HomogeneousLocalization.Away (grK K N) x) :
    evV i z V h (HomogeneousLocalization.awayMap (grK K N) hy hz u) = evV i x V h' u := by
  have e := congrArg (fun φ => φ.hom u) (Proj.awayMap_awayToSection (grK K N) hy hz)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [evV, RingHom.coe_comp, Function.comp_apply]
  rw [e, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem evV_res {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)
    {g : MvPolynomial (Fin (N + 1)) K} {V W : X.Opens} (hVW : V ≤ W)
    (hW : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g)
    (u : HomogeneousLocalization.Away (grK K N) g) :
    evV i g V hV u = resO hVW (evV i g W hW u) := by
  have e := congrArg (fun φ => φ.hom ((Proj.awayToSection (grK K N) g).hom u))
    (Scheme.Hom.appLE_map i hW (homOfLE hVW).op)
  exact e.symm

theorem away_factor {K : Type} [Field K] {N : ℕ} {x g f : MvPolynomial (Fin (N + 1)) K} {e s : ℕ}
    (hx : x ∈ grK K N 1) (hg : g ∈ grK K N e) (hf : f ∈ grK K N (s • e))
    (hf' : f ∈ grK K N ((s • e) • 1)) (hc : g ^ s ∈ grK K N ((s • e) • 1)) :
    HomogeneousLocalization.awayMap (grK K N) hg (rfl : x * g = x * g)
        (HomogeneousLocalization.Away.mk (grK K N) hx (s • e) f hf') =
      HomogeneousLocalization.awayMap (grK K N) hx (mul_comm x g)
          (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) *
        HomogeneousLocalization.awayMap (grK K N) hg (rfl : x * g = x * g)
          (HomogeneousLocalization.Away.mk (grK K N) hx (s • e) (g ^ s) hc) := by
  ext
  simp only [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul]
  refine Localization.mk_eq_mk_iff.mpr ?_
  rw [Localization.r_iff_exists]
  use 1
  simp
  ring

theorem mem_homIdeal_of_vanish {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N)
    (hX : IsIntegral X) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e)
    (hg : g ∈ grK K N e) {s : ℕ} {f : MvPolynomial (Fin (N + 1)) K} (hf : f ∈ grK K N (s • e))
    (V : X.Opens) (hVne : (V : Set X).Nonempty)
    (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g)
    (h0 : evV i g V hV (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) = 0) :
    f ∈ homIdeal i := by
  have hf' : f ∈ grK K N ((s • e) • 1) := by simpa using hf
  have hc : g ^ s ∈ grK K N ((s • e) • 1) := by
    have := SetLike.pow_mem_graded s hg
    simpa using this
  refine Ideal.subset_span ⟨s • e, hf', fun j => ?_⟩
  by_cases hU : ((i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) : X.Opens) : Set X).Nonempty
  · have hW : ((V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) : X.Opens) : Set X).Nonempty :=
      nonempty_preirreducible_inter V.isOpen (TopologicalSpace.Opens.isOpen _) hVne hU
    haveI : Nonempty (V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) : X.Opens) := hW.to_subtype
    have hx := xv_mem K N j
    have hWU : V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) ≤
        i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) := inf_le_right
    have hWV : V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) ≤ V := inf_le_left
    have hWg := hWV.trans hV
    have hWx : V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) ≤
        i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j * g) := by
      rw [Proj.basicOpen_mul]
      exact fun y hy => ⟨hWU hy, hWg hy⟩
    apply map_injective_of_isIntegral X (homOfLE hWU)
    rw [map_zero]
    refine (evV_res i hWU le_rfl hWU _).symm.trans ?_
    rw [← evV_awayMap i hg rfl _ hWx hWU, away_factor hx hg hf hf' hc, map_mul,
      evV_awayMap i hx (mul_comm _ g) _ hWx hWg, evV_res i hWV hV hWg, h0, map_zero, zero_mul]
  · refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 ?_)
    refine (X.basicOpen_le _).trans ?_
    intro y hy
    exact (hU ⟨y, hy⟩).elim

end GlobalTheory.CompanionTheory.GeoVan
end
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoUnit

theorem awayMap_ratio_mul {K : Type} [Field K] {N e : ℕ} {a b : MvPolynomial (Fin (N + 1)) K}
    (ha : a ∈ grK K N e) (hb : b ∈ grK K N e) (hb1 : b ∈ grK K N (1 • e)) (ha1 : a ∈ grK K N (1 • e)) :
    HomogeneousLocalization.awayMap (grK K N) hb (x := a * b) rfl
        (HomogeneousLocalization.Away.mk _ ha 1 b hb1) *
      HomogeneousLocalization.awayMap (grK K N) ha (x := a * b) (mul_comm a b)
        (HomogeneousLocalization.Away.mk _ hb 1 a ha1) = 1 := by
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one, Localization.mk_mul,
    ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

theorem tV_isUnit {K : Type} [Field K] {X : Scheme.{0}} {N d e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin (d + 1) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) {V : X.Opens}
    (hV : V ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) (k : Fin d) : IsUnit (tV i y hy V hV k) := by
  have h0 : y 0 ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hy 0)
  have h1 : y k.succ ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hy k.succ)
  have h0' : y 0 ∈ grK K N (1 • e) := by rw [one_smul]; exact h0
  have h1' : y k.succ ∈ grK K N (1 • e) := by rw [one_smul]; exact h1
  have hle : Proj.basicOpen (grK K N) (y 0 * y k.succ) ≤ Proj.basicOpen (grK K N) (y 0) := by
    rw [Proj.basicOpen_mul]; exact inf_le_left
  have hU : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y 0 * y k.succ) := by
    rw [Proj.basicOpen_mul]
    exact le_inf (hV.trans (iInf_le _ 0)) (hV.trans (iInf_le _ k.succ))
  have hu : IsUnit (HomogeneousLocalization.awayMap (grK K N) h1 (x := y 0 * y k.succ) rfl
      (HomogeneousLocalization.Away.mk _ h0 1 (y k.succ) h1')) :=
    isUnit_iff_exists_inv.mpr ⟨_, awayMap_ratio_mul h0 h1 h1' h0'⟩
  have e1 := Scheme.Hom.map_appLE i hU (homOfLE hle).op
  have e2 := Proj.awayMap_awayToSection (grK K N) h1 (f := y 0) (x := y 0 * y k.succ) rfl
  have key : tV i y hy V hV k =
      (Scheme.Hom.appLE i _ V hU).hom ((Proj.awayToSection (grK K N) (y 0 * y k.succ)).hom
        (HomogeneousLocalization.awayMap (grK K N) h1 (x := y 0 * y k.succ) rfl
          (HomogeneousLocalization.Away.mk _ h0 1 (y k.succ) h1'))) := by
    unfold tV yRatio
    rw [← e1, CommRingCat.hom_comp, RingHom.comp_apply]
    congr 1
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← e2, CommRingCat.hom_comp, RingHom.comp_apply]
    rfl
  rw [key]
  exact (hu.map _).map _

end GlobalTheory.CompanionTheory.GeoUnit
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.PlogMul

open Polynomial

variable {B : Type} [CommRing B]

noncomputable def logPoly (c : ℕ → B) (s : ℕ) : B[X] :=
  ∑ k ∈ Finset.range s, C ((-1) ^ k * c k) * X ^ (k + 1)

theorem derivative_logPoly (c : ℕ → B) (hc : ∀ k : ℕ, c k * ((k : B) + 1) = 1) (s : ℕ) :
    derivative (logPoly c s) = ∑ k ∈ Finset.range s, (-X) ^ k := by
  unfold logPoly
  rw [derivative_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (C (c k) : B[X]) * ((k : B[X]) + 1) = 1 := by
    have := congrArg (C : B →+* B[X]) (hc k)
    simpa using this
  rw [derivative_C_mul, derivative_X_pow, neg_pow (X : B[X]) k]
  simp only [Nat.add_sub_cancel, map_mul, map_pow, map_neg, map_one, Nat.cast_add, Nat.cast_one]
  calc _ = (-1) ^ k * (C (c k) * ((k : B[X]) + 1)) * X ^ k := by
        simp only [map_add (f := _), map_natCast, map_one]; ring
    _ = _ := by rw [h1, mul_one]

theorem one_add_mul_geom {R : Type} [CommRing R] (u : R) (s : ℕ) :
    (1 + u) * ∑ k ∈ Finset.range s, (-u) ^ k = 1 - (-u) ^ s := by
  have := mul_neg_geom_sum (-u) s
  simpa using this

theorem geom_comp (s : ℕ) (u : B[X]) :
    (∑ k ∈ Finset.range s, (-X : B[X]) ^ k).comp u = ∑ k ∈ Finset.range s, (-u) ^ k := by
  induction s with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ, ih]

theorem eval_logPoly_zero (c : ℕ → B) (s : ℕ) : (logPoly c s).eval 0 = 0 := by
  simp [logPoly, eval_finsetSum]

theorem eval_logPoly_mul (c : ℕ → B) (hc : ∀ k : ℕ, c k * ((k : B) + 1) = 1)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) (s : ℕ) {x y : B}
    (hxy : ∀ a b : ℕ, s ≤ a + b → x ^ a * y ^ b = 0) :
    (logPoly c s).eval ((1 + x) * (1 + y) - 1) = (logPoly c s).eval x + (logPoly c s).eval y := by
  set a : B[X] := C x * X with ha
  set Z : B[X] := (1 + a) * (1 + C y) - 1 with hZ
  set G : B[X] := (logPoly c s).comp Z - (logPoly c s).comp a - C ((logPoly c s).eval y) with hG
  have has : a ^ s = 0 := by
    have h := hxy s 0 (by simp)
    have h' : x ^ s = 0 := by simpa using h
    rw [ha, mul_pow, ← C_pow, h']
    simp
  have hZs : Z ^ s = 0 := by
    have hZ' : Z = a * (1 + C y) + C y := by rw [hZ]; ring
    rw [hZ', add_pow]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i ≤ s := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h0 := hxy i (s - i) (by omega)
    have : (a * (1 + C y)) ^ i * (C y) ^ (s - i) = C (x ^ i * y ^ (s - i)) * (X ^ i * (1 + C y) ^ i) := by
      rw [ha, C_mul, C_pow, C_pow, mul_pow, mul_pow]; ring
    rw [this, h0]
    simp
  have hderiv : derivative G = 0 := by
    have hda : derivative a = C x := by rw [ha]; simp
    have hdZ : derivative Z = C x * (1 + C y) := by
      rw [hZ]; simp [hda]
    have hD : derivative G = C x * (1 + C y) * (∑ k ∈ Finset.range s, (-Z) ^ k)
        - C x * (∑ k ∈ Finset.range s, (-a) ^ k) := by
      rw [hG, derivative_sub, derivative_sub, derivative_C, sub_zero, derivative_comp, derivative_comp,
        derivative_logPoly c hc, hdZ, hda]
      rw [geom_comp, geom_comp]
    have h1 : (1 + a) * (∑ k ∈ Finset.range s, (-a) ^ k) = 1 := by
      rw [one_add_mul_geom, neg_pow, has]; simp
    have h2 : (1 + a) * (1 + C y) * (∑ k ∈ Finset.range s, (-Z) ^ k) = 1 := by
      have := one_add_mul_geom Z s
      rw [neg_pow, hZs] at this
      have e : 1 + Z = (1 + a) * (1 + C y) := by rw [hZ]; ring
      rw [← e, this]; simp
    have h3 : (1 + a) * derivative G = 0 := by
      rw [hD]
      linear_combination (C x) * h2 - (C x) * h1
    have h4 : derivative G = (∑ k ∈ Finset.range s, (-a) ^ k) * ((1 + a) * derivative G) := by
      linear_combination (- derivative G) * h1
    rw [h4, h3, mul_zero]
  have hG0 : G.eval 0 = 0 := by
    simp [hG, hZ, ha, eval_comp, eval_logPoly_zero]
  have hGC : G = C (G.eval 0) := by
    ext n
    cases n with
    | zero => simp [coeff_zero_eq_eval_zero]
    | succ n =>
      have h := congrArg (fun (p : B[X]) => p.coeff n) hderiv
      simp only [coeff_derivative, coeff_zero] at h
      have hn : IsUnit ((n : B) + 1) := by
        have := hu (n + 1) (by omega)
        simpa using this
      have : G.coeff (n + 1) = 0 := hn.mul_left_eq_zero.1 h
      simp [this, coeff_C]
  have hG1 : G.eval 1 = 0 := by
    rw [hGC, hG0]; simp
  have : (logPoly c s).eval ((1 + x) * (1 + y) - 1) - (logPoly c s).eval x - (logPoly c s).eval y = 0 := by
    simpa [hG, hZ, ha, eval_comp] using hG1
  linear_combination this

theorem plogK_mul {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ)
    (hs : pdP δ s = ⊥) (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) {x y : B} (hx : x ∈ J) (hy : y ∈ J) :
    plogK δ s ((1 + x) * (1 + y) - 1) = plogK δ s x + plogK δ s y := by
  have hunit : ∀ k : ℕ, IsUnit ((k : B) + 1) := fun k => by
    have := hu (k + 1) (by omega)
    simpa using this
  choose c hc using fun k : ℕ => (hunit k).exists_left_inv
  have hlog : ∀ {z : B}, z ∈ J → plogK δ s z = (logPoly c s).eval z := by
    intro z hz
    simp only [plogK, logPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := δ.factorial_mul_dpow_eq_pow (n := k + 1) hz
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
    rw [← h]
    linear_combination (-(-1 : B) ^ k * (k.factorial : B) * δ.dpow (k + 1) z) * hc k
  have hxy : ∀ a b : ℕ, s ≤ a + b → x ^ a * y ^ b = 0 := by
    intro a b hab
    have hmem : δ.dpow a x * δ.dpow b y ∈ pdP δ s := by
      refine Ideal.subset_span ⟨[(a, x), (b, y)], ?_, ?_, ?_⟩
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hx
        · exact hy
      · simpa using hab
      · simp
    rw [hs, Ideal.mem_bot] at hmem
    rw [← δ.factorial_mul_dpow_eq_pow hx, ← δ.factorial_mul_dpow_eq_pow hy]
    linear_combination ((a.factorial : B) * (b.factorial : B)) * hmem
  have hz : (1 + x) * (1 + y) - 1 ∈ J := by
    have e : (1 + x) * (1 + y) - 1 = x + y + x * y := by ring
    rw [e]
    exact J.add_mem (J.add_mem hx hy) (J.mul_mem_right y hx)
  rw [hlog hz, hlog hx, hlog hy]
  exact eval_logPoly_mul c hc hu s hxy

end GlobalTheory.CompanionTheory.PlogMul
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.ConeYq

theorem awayMap_ratio_trans {K : Type} [Field K] {N e : ℕ} {a b c : MvPolynomial (Fin (N + 1)) K}
    (hb : b ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e)
    (hc : c ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e)
    (ha1 : a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • e))
    (hb1 : b ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • e)) :
    HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) hc (x := b * c) rfl
        (HomogeneousLocalization.Away.mk _ hb 1 a ha1) *
      HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) hb (x := b * c)
        (mul_comm b c) (HomogeneousLocalization.Away.mk _ hc 1 b hb1) =
    HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) hb (x := b * c)
        (mul_comm b c) (HomogeneousLocalization.Away.mk _ hc 1 a ha1) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, pow_one]
  ring

theorem away_self {K : Type} [Field K] {N e : ℕ} {a : MvPolynomial (Fin (N + 1)) K}
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e)
    (ha1 : a ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • e)) :
    HomogeneousLocalization.Away.mk _ ha 1 a ha1 = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp

theorem appLE_awayMap {K : Type} [Field K] {X : Scheme.{0}} {N e : ℕ} (i : X ⟶ PSpace K N)
    {f g x : MvPolynomial (Fin (N + 1)) K}
    (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e) (hx : x = f * g) (W : X.Opens)
    (hW : W ≤ i ⁻¹ᵁ Proj.basicOpen _ x) (hW' : W ≤ i ⁻¹ᵁ Proj.basicOpen _ f)
    (u : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) :
    (i.appLE _ W hW').hom ((Proj.awayToSection _ f).hom u) =
      (i.appLE _ W hW).hom ((Proj.awayToSection _ x).hom
        (HomogeneousLocalization.awayMap (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) hg hx u)) := by
  have h := congrArg (fun φ => φ.hom u)
    (Proj.awayMap_awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) hg hx)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h
  rw [h]
  exact (congrArg (fun φ => φ.hom ((Proj.awayToSection _ f).hom u)) (Scheme.Hom.map_appLE i hW _)).symm

theorem yQ_mul_yQ {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (a b c : Fin m) (W : X.Opens)
    (ha : W ≤ uy i y a) (hb : W ≤ uy i y b) (hc : W ≤ uy i y c) :
    (i.appLE _ W hb).hom (yQ y hy a b) * (i.appLE _ W hc).hom (yQ y hy b c) = (i.appLE _ W hc).hom (yQ y hy a c) ∧
    (i.appLE _ W ha).hom (yQ y hy a a) = 1 := by
  have mem : ∀ k, y k ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K e :=
    fun k => (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)
  have mem1 : ∀ k, y k ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • e) :=
    fun k => by simpa using mem k
  constructor
  · have hW : W ≤ i ⁻¹ᵁ Proj.basicOpen _ (y b * y c) := by
      rw [Proj.basicOpen_mul]
      exact le_inf hb hc
    have e1 : (i.appLE _ W hb).hom (yQ y hy a b) = _ :=
      appLE_awayMap i (mem c) (x := y b * y c) rfl W hW hb
        (HomogeneousLocalization.Away.mk _ (mem b) 1 (y a) (mem1 a))
    have e2 : (i.appLE _ W hc).hom (yQ y hy b c) = _ :=
      appLE_awayMap i (mem b) (x := y b * y c) (mul_comm _ _) W hW hc
        (HomogeneousLocalization.Away.mk _ (mem c) 1 (y b) (mem1 b))
    have e3 : (i.appLE _ W hc).hom (yQ y hy a c) = _ :=
      appLE_awayMap i (mem b) (x := y b * y c) (mul_comm _ _) W hW hc
        (HomogeneousLocalization.Away.mk _ (mem c) 1 (y a) (mem1 a))
    rw [e1, e2, e3, ← map_mul, ← map_mul, awayMap_ratio_trans (mem b) (mem c) (mem1 a) (mem1 b)]
  · have : yQ y hy a a = 1 := by
      unfold yQ
      rw [away_self (mem a) (mem1 a), map_one]
    rw [this, map_one]

end GlobalTheory.CompanionTheory.ConeYq
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeSite

theorem wK_rel : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (k : Fin m) ⦃T T' : Thick (smFun X q)⦄,
    (T ⟶ T') → wK q i y s k T → (∃ β, wK q i y s β T') → wK q i y s k T' := by
  intro K _ X q N m i y s k T T' φ h h'
  obtain ⟨β, hQ, -⟩ := h'
  obtain ⟨-, V, hV, hT⟩ := h
  exact ⟨hQ, V, hV, GlobalTheory.CompanionTheory.ThickPt.inU_map V φ hT⟩

end GlobalTheory.CompanionTheory.ConeSite
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo

theorem preimage_basicOpen_nonempty_of_mk_ne_zero {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}
    (i : X ⟶ PSpace K N) (hX : IsIntegral X) {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e)
    (hg : g ∈ grK K N e) (hne : Ideal.Quotient.mk (homIdeal i) g ≠ 0) :
    ((i ⁻¹ᵁ Proj.basicOpen (grK K N) g : X.Opens) : Set X).Nonempty := by
  by_contra hE
  apply hne
  rw [Ideal.Quotient.eq_zero_iff_mem]
  apply Ideal.subset_span
  have hg' : g ∈ grK K N (e • 1) := by simpa using hg
  refine ⟨e, hg', fun j => ?_⟩
  have hy : HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) e g hg' =
      HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hg := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk]
  rw [hy, ← basicOpen_eq_bot_iff]
  have hb := GroundTheory.Arith.SchemeCoh.ProjHom.basicOpen_awayToSection_isLocalizationElem (grK K N)
    (xv_mem K N j) one_pos hg he
  have h2 : X.basicOpen (evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hg)) =
      i ⁻¹ᵁ (PSpace K N).basicOpen (Proj.awayToSection (grK K N) (MvPolynomial.X j)
        (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hg)) := by
    rw [Scheme.preimage_basicOpen]
    simp only [evV, Scheme.Hom.appLE_eq_app]
    rfl
  rw [h2, hb, eq_bot_iff]
  intro x hx
  exact hE ⟨x, hx.2⟩

end GlobalTheory.CompanionTheory.Geo
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.inOpen_finite_inf_iff : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {ι : Type} (U : ι → X.Opens) (S : Finset ι) (T : Thick (nlFun γ p X q κ)), InU (⨅ α ∈ S, U α) T ↔ ∀ α ∈ S, InU (U α) T := by
  first | exact @GlobalTheory.CompanionTheory.Thick.inU_iInf_finset | exact GlobalTheory.CompanionTheory.Thick.inU_iInf_finset | (intros; apply GlobalTheory.CompanionTheory.Thick.inU_iInf_finset <;> assumption)
end
