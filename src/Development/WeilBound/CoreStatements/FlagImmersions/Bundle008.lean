module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle004
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle007
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

section

noncomputable section

namespace RootFieldNumerics.Bh

open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K] {J : K → Type}
  [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_poly (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (hn : IsNormalScheme X)
    (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : Ω} (ha : a ∈ integralClosure (chartRingZ y c) Ω) :
    ∃ p : MRing J, aeval (fun q : Σ k, J k => y q / y ⟨q.1, c q.1⟩) p = a := by
  classical
  have hc0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have hle : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤ chartRingZ y c := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    show (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩ ∈ chartRingZ y c
    rw [← Finset.prod_div_distrib]
    exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
  have hge : chartRingZ y c ≤ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    refine Algebra.subset_adjoin ⟨Function.update c k i, ?_⟩
    show (∏ k', y ⟨k', Function.update c k i k'⟩) / ∏ k, y ⟨k, c k⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · rw [Function.update_self]
    · intro k' _ h
      rw [Function.update_of_ne h, div_self (hc k')]
    · simp
  have hmem : a ∈ chartRingZ y c := by
    refine hle ((T.ring c hc0 a).2 fun q hq => ?_)
    obtain ⟨h1, -, h3⟩ := GlobalTheory.T.regAt_fraction_noetherian_closed X Ω ξ T.gen q
    have h4 := h3 (hn q.1).2
    let φ : chartRingZ y c →+* regAt ξ q :=
      (algebraMap (chartRingZ y c) Ω).codRestrict _ fun r => (T.ring c hc0 r).1 (hge r.2) q hq
    have h5 : IsIntegral (regAt ξ q) a := IsIntegral.map_of_comp_eq φ (RingHom.id Ω) rfl ha
    obtain ⟨r, rfl⟩ := (isIntegrallyClosed_iff Ω).1 h4 h5
    exact r.2
  unfold chartRingZ at hmem
  rw [Algebra.adjoin_range_eq_range_aeval] at hmem
  exact hmem

variable {z : Spec (CommRingCat.of ℂ) ⟶ X} {w : (Σ k, J k) → ℂ}

theorem val_ratio (h : CoordsAt ξ y z w) (k : K) (i c : J k) (hc : w ⟨k, c⟩ ≠ 0) :
    ValAt ξ z (y ⟨k, i⟩ / y ⟨k, c⟩) (w ⟨k, i⟩ / w ⟨k, c⟩) := by
  obtain ⟨r, hr, e⟩ := (h.2 k c (IsUnit.mk0 _ hc)).2 i
  rwa [e, mul_div_cancel_right₀ _ hc]

theorem val_prod (hz : genPt ξ ⤳ centre z) {a : K → Ω} {r : K → ℂ} (h : ∀ k, ValAt ξ z (a k) (r k)) :
    ValAt ξ z (∏ k, a k) (∏ k, r k) := by
  classical
  have : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, a k) (∏ k ∈ s, r k) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using CxVal.one hz
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact CxVal.mul (h k) ih
  exact this _

theorem val_pow (hz : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  induction n with
  | zero => simpa using CxVal.one hz
  | succ n ih => rw [pow_succ, pow_succ]; exact CxVal.mul ih h

def fn (y : (Σ k, J k) → Ω) (s : Ω) (m : ℕ) (k₀ : K) (i₀ : J k₀) (c : (k : K) → J k) : Ω :=
  s * (∏ k, y ⟨k, c k⟩) / y ⟨k₀, i₀⟩ ^ m

theorem val_fn (hz : genPt ξ ⤳ centre z) (h : CoordsAt ξ y z w) {s : Ω} {m : ℕ} {k₀ : K} (i₀ : J k₀) (c c' : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c' k⟩ ≠ 0) (hi : w ⟨k₀, i₀⟩ ≠ 0) {p : MRing J}
    (hp : aeval (fun q : Σ k, J k => y q / y ⟨q.1, c' q.1⟩) p = fn y s m k₀ (c' k₀) c') :
    ValAt ξ z (fn y s m k₀ i₀ c) (aeval (fun q : Σ k, J k => w q / w ⟨q.1, c' q.1⟩) p * (∏ k, w ⟨k, c k⟩ / w ⟨k, c' k⟩) *
      (w ⟨k₀, c' k₀⟩ / w ⟨k₀, i₀⟩) ^ m) := by
  have h1 := CxVal.aeval hz (fun q : Σ k, J k => val_ratio h q.1 q.2 (c' q.1) (hc q.1)) p
  have h2 := val_prod hz fun k => val_ratio h k (c k) (c' k) (hc k)
  have h3 := val_pow hz (val_ratio h k₀ (c' k₀) i₀ hi) m
  have hy := fun k => (h.2 k (c' k) (IsUnit.mk0 _ (hc k))).1
  have hy0 := (h.2 k₀ i₀ (IsUnit.mk0 _ hi)).1
  have hP : (∏ k, y ⟨k, c' k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  have hk := hy k₀
  convert CxVal.mul (CxVal.mul h1 h2) h3 using 1
  have hp' : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c' q.1⟩) p = fn y s m k₀ (c' k₀) c' := hp
  rw [hp', Finset.prod_div_distrib, div_pow]
  unfold fn
  field_simp

theorem fn_eq [DecidableEq K] {s : Ω} {m : ℕ} {k₀ : K} {a : K → ℤ} (ha : a k₀ = 1 ∧ ∀ k, k ≠ k₀ → a k = 0)
    (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    s * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k - 1)) = fn y s m k₀ (c k₀) c := by
  have e : ∀ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k - 1)) = y ⟨k, c k⟩ / y ⟨k, c k⟩ ^ ((m : ℤ) * a k) := fun k => by
    rw [neg_sub, zpow_sub₀ (hc k), zpow_one]
  simp only [e, Finset.prod_div_distrib]
  rw [Finset.prod_eq_single k₀ (f := fun k => y ⟨k, c k⟩ ^ ((m : ℤ) * a k))]
  · rw [ha.1, mul_one, zpow_natCast, fn, mul_div_assoc]
  · intro k _ h
    rw [ha.2 k h, mul_zero, zpow_zero]
  · simp

theorem ne_zero_of_hasVal (hz : genPt ξ ⤳ centre z) (h : CoordsAt ξ y z w) {s : Ω} {a : K → ℤ} (c : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) {p : MRing J}
    (hp : aeval (fun q : Σ k, J k => y q / y ⟨q.1, c q.1⟩) p = s * ∏ k, y ⟨k, c k⟩ ^ (-a k)) {v : ℂ} (hv : v ≠ 0)
    (hs : Small.HasVal y a s w v) : aeval (fun q : Σ k, J k => w q / w ⟨q.1, c q.1⟩) p ≠ 0 := by
  obtain ⟨dg, dh, g, h', hg, hh, hd, e1, hne, e2⟩ := hs
  have hy := fun k => (h.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  have V := fun f : MRing J => CxVal.aeval hz (fun q : Σ k, J k => val_ratio h q.1 q.2 (c q.1) (hc q.1)) f
  have ey : y = fun q => y ⟨q.1, c q.1⟩ * (y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) :=
    funext fun q => (mul_div_cancel₀ _ (hy q.1)).symm
  have ew : w = fun q => w ⟨q.1, c q.1⟩ * (w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩) :=
    funext fun q => (mul_div_cancel₀ _ (hc q.1)).symm
  have g1 := aeval_blockScale hg (fun k => y ⟨k, c k⟩) fun q => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩
  have g2 := aeval_blockScale hh (fun k => y ⟨k, c k⟩) fun q => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩
  have g3 := aeval_blockScale hg (fun k => w ⟨k, c k⟩) fun q => w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩
  rw [← ey] at g1 g2
  rw [← ew] at g3
  have key : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) g =
      aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) p *
        aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) h' := by
    have hp' : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) p = s * ∏ k, y ⟨k, c k⟩ ^ (-a k) := hp
    have h0 : (∏ k, y ⟨k, c k⟩ ^ dg k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
    have h1 : (∏ k, y ⟨k, c k⟩ ^ dg k) * ∏ k, y ⟨k, c k⟩ ^ (-a k) = ∏ k, y ⟨k, c k⟩ ^ dh k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k), hd k]
      congr 1
      ring
    refine mul_left_cancel₀ h0 ?_
    rw [← g1, e1, g2, hp', ← h1]
    ring
  have e3 := CxVal.unique (key ▸ V g) (CxVal.mul (V p) (V h'))
  intro h0
  have h0' : aeval (fun q : Σ k, J k => w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩) p = 0 := h0
  rw [h0', zero_mul] at e3
  rw [e3, mul_zero, e2] at g3
  exact mul_ne_zero hv hne g3

end RootFieldNumerics.Bh
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

namespace Ii

theorem lin_prod_expand {J : Type} [Fintype J] [DecidableEq J] (d : ℕ) (Φ : MvPolynomial J ℝ →ₗ[ℝ] ℝ)
    (c : J → ℝ) :
    Φ ((∑ j, C (c j) * X j) ^ d) =
      ∑ w : Fin d → J, (∏ k, c (w k)) * Φ (monomial (∑ k, Finsupp.single (w k) 1) 1) := by

  rw [← Fin.prod_const, Fintype.prod_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hm : ∏ k, C (c (w k)) * X (w k) = C (∏ k, c (w k)) * monomial (∑ k, Finsupp.single (w k) 1) (1 : ℝ) := by
    rw [Finset.prod_mul_distrib, map_prod, monomial_sum_one]
    rfl
  rw [hm, C_mul', map_smul, smul_eq_mul]

theorem prod_weight {α : Type} [DecidableEq α] {d : ℕ} (w : Fin d → Option α) (x : ℝ) :
    ∏ k, (if w k = none then x else 1) = x ^ (∑ k, Finsupp.single (w k) 1 : Option α →₀ ℕ) none := by
  rw [Finsupp.finsetSum_apply, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finsupp.single_apply]
  split_ifs <;> simp

end Ii

open Ii in
theorem root_model_arithmetic_intersection : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → II M.K M.ι M.P (dimFl Ψ N + 1) (fun _ => combLine (M.line t) n) = M.δ * (q : ℝ) ^ (dimFl Ψ N + 1) * M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  intro II hII Ψ _ N M t lam s q n hn
  classical
  have hsm : ∀ j, IsSmoothHerm (M.line t j) := by
    intro j
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  rw [RootFieldNumerics.intersection_multilinear_expansion II hII M.K M.ι M.P (dimFl Ψ N + 1) _ (M.line t) (fun _ => n) M.arith hsm]
  let cc : Option (Ψ × Fin N) → ℝ := fun j => Option.elim j s (fun r => -lam r.1 r.2)
  have hlin : linA lam s = ∑ j, C (cc j) * X j := by
    rw [Fintype.sum_option]

    simp [cc, linA, toA, linRoot, map_sum, map_neg, rename_X, Finset.sum_neg_distrib, add_comm]
  rw [hlin, lin_prod_expand, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  obtain ⟨hdeg, σ, _, hII2⟩ := RootFieldNumerics.intersection_monomial_lines II hII.1 M.K M.ι M.P (dimFl Ψ N + 1) _ (M.line t) w M.arith hsm
  have hmono : M.arFun II t (monomial (∑ k, Finsupp.single (w k) 1) 1) =
      II M.K M.ι M.P (dimFl Ψ N + 1) (fun k => M.line t (w k)) /
        (M.δ * (M.kA : ℝ) ^ (∑ k, Finsupp.single (w k) 1 : Option (Ψ × Fin N) →₀ ℕ) none) := by
    have hb : (monomial (∑ k, Finsupp.single (w k) 1) (1 : ℝ) : RPA Ψ N) =
        basisMonomials (Option (Ψ × Fin N)) ℝ (∑ k, Finsupp.single (w k) 1) := by
      rw [coe_basisMonomials]
    rw [RootModel.arFun, hb, Module.Basis.constr_basis, RootModel.arMono, if_pos hdeg, hII2]
  have hc : ∏ k, cc (w k) = (∏ k, M.coef lam s (w k)) *
      (M.kA : ℝ) ^ (∑ k, Finsupp.single (w k) 1 : Option (Ψ × Fin N) →₀ ℕ) none := by
    rw [← prod_weight w (M.kA : ℝ), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have hk : (M.kA : ℝ) ≠ 0 := by exact_mod_cast M.kA_pos.ne'
    cases w k with
    | none =>
      simp [cc, RootModel.coef]
      field_simp
    | some r => simp [cc, RootModel.coef]
  have hnp : ∏ k, (n (w k) : ℝ) = (q : ℝ) ^ (dimFl Ψ N + 1) * ∏ k, M.coef lam s (w k) := by
    simp_rw [hn]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hδ : (M.δ : ℝ) ≠ 0 := by exact_mod_cast M.δ_pos.ne'
  have hk : (M.kA : ℝ) ≠ 0 := by exact_mod_cast M.kA_pos.ne'
  rw [hmono, hc, hnp]
  field_simp

end RootFieldNumerics
end
