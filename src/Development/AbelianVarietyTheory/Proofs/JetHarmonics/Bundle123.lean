module

public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthTie
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle002
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle115
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle033
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle032
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle004
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle001
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle002
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

@[expose] public section

section

set_option autoImplicit false

namespace GlobalTheory.GoodDepth

open Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Units

variable {K : Type} [Field K] [NumberField K] [StarRing K] (v : HeightOneSpectrum (𝓞 K))

theorem vwUnit_mul {x y : K} (hx : x ≠ 0 ∧ Formalism.DivisionValues.vw v x = 0) (hy : y ≠ 0 ∧ Formalism.DivisionValues.vw v y = 0) :
    x * y ≠ 0 ∧ Formalism.DivisionValues.vw v (x * y) = 0 :=
  ⟨mul_ne_zero hx.1 hy.1, by rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul v _ _ hx.1 hy.1, hx.2, hy.2, add_zero]⟩

theorem vwUnit_nat {N : ℕ} (hN : ¬ plc v ∣ N) : (N : K) ≠ 0 ∧ Formalism.DivisionValues.vw v (N : K) = 0 := by
  have h0 : N ≠ 0 := by rintro rfl; exact hN (dvd_zero _)
  refine ⟨by exact_mod_cast h0, ?_⟩
  rw [DepthTie.vw_N v N h0, Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hN]
  simp

theorem vwUnit_pow {x : K} (hx : x ≠ 0 ∧ Formalism.DivisionValues.vw v x = 0) (n : ℕ) :
    x ^ n ≠ 0 ∧ Formalism.DivisionValues.vw v (x ^ n) = 0 := by
  induction n with
  | zero =>
    have := vwUnit_nat v (N := 1) (by simpa using (plc_prime v).ne_one)
    simpa using this
  | succ n ih => rw [pow_succ]; exact vwUnit_mul v ih hx

theorem vwUnit_prime {p : ℕ} (hp : p.Prime) (h : plc v ≠ p) : (p : K) ≠ 0 ∧ Formalism.DivisionValues.vw v (p : K) = 0 :=
  vwUnit_nat v fun hd => h ((Nat.prime_dvd_prime_iff_eq (plc_prime v) hp).1 hd)

theorem vwUnit_factor {x y : K} (hx : IsIntegral ℤ x) (hy : IsIntegral ℤ y)
    (h : x * y ≠ 0 ∧ Formalism.DivisionValues.vw v (x * y) = 0) :
    (x ≠ 0 ∧ Formalism.DivisionValues.vw v x = 0) ∧ (y ≠ 0 ∧ Formalism.DivisionValues.vw v y = 0) := by
  have x0 := left_ne_zero_of_mul h.1
  have y0 := right_ne_zero_of_mul h.1
  have h2 := h.2
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul v _ _ x0 y0] at h2
  have a := DepthTie.vw_nonneg_of_isIntegral v x hx
  have b := DepthTie.vw_nonneg_of_isIntegral v y hy
  exact ⟨⟨x0, by omega⟩, ⟨y0, by omega⟩⟩

end Units

theorem vw_sigAt_good {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dd : DepData E) {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 E) K]
    (hsp : PiSplit (H := H) Dd) (hprime : Dd.Q.g1.Prime ∧ Dd.Q.g2.Prime ∧ Dd.Q.q1.Prime ∧ Dd.Q.dd.Prime)
    (v : HeightOneSpectrum (𝓞 K)) (h2 : plc v ∉ Dd.Q.sm) (hq : plc v ≠ Dd.Q.q1) (hd : plc v ≠ Dd.Q.dd)
    (hg1 : plc v ≠ Dd.Q.g1) (hg2 : plc v ≠ Dd.Q.g2) (Dw' : Datum H) (j : ℕ) :
    Formalism.DivisionValues.vw v (sigAt (Dw := Dw') (H := H) (LL := K) Dd j) = 0 := by
  obtain ⟨e0, e1, -⟩ := DepthTie.alg_pi_ne_zero (K := K) Dd hsp ⟨hprime.1, hprime.2.1⟩
  have u1 := vwUnit_prime v hprime.1 hg1
  have u2 := vwUnit_prime v hprime.2.1 hg2
  have uq := vwUnit_prime v hprime.2.2.1 hq
  have ud := vwUnit_prime v hprime.2.2.2 hd
  have ut : ∀ a : ℕ → ℕ, ((∏ p ∈ Dd.Q.sm.filter Nat.Prime, p ^ a p : ℕ) : K) ≠ 0 ∧
      Formalism.DivisionValues.vw v ((∏ p ∈ Dd.Q.sm.filter Nat.Prime, p ^ a p : ℕ) : K) = 0 := fun a => vwUnit_nat v fun hdv => by
    obtain ⟨p, hp, h⟩ := (Prime.dvd_finsetProd_iff (plc_prime v).prime _).1 hdv
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    exact h2 ((Nat.prime_dvd_prime_iff_eq (plc_prime v) hp2).1 ((plc_prime v).dvd_of_dvd_pow h) ▸ hp1)
  obtain ⟨a0, b0⟩ := vwUnit_factor v (DepthTie.isIntegral_alg _) (DepthTie.isIntegral_alg _) (e0 ▸ u1)
  obtain ⟨a1, b1⟩ := vwUnit_factor v (DepthTie.isIntegral_alg _) (DepthTie.isIntegral_alg _) (e1 ▸ u2)
  rw [DepthTie.sigAt_eq]
  refine (vwUnit_mul v ?_ ?_).2
  · unfold nnKAt nnOf
    rw [Fin.prod_univ_two]
    exact vwUnit_mul v (vwUnit_mul v (vwUnit_pow v b0 _) (vwUnit_pow v a0 _))
      (vwUnit_mul v (vwUnit_pow v b1 _) (vwUnit_pow v a1 _))
  · unfold DepthTie.Nsig DepPage.Z1 DepPage.q
    simp only [Nat.cast_mul, Nat.cast_pow]
    exact vwUnit_mul v (vwUnit_pow v (vwUnit_mul v u1 u2) _)
      (vwUnit_mul v (vwUnit_mul v (ut _) (vwUnit_pow v uq _)) (vwUnit_pow v ud _))

theorem normalizedLattice_exponent_eq_roundedDepth_goodPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) lv) (c : Coeff lv) [StarRing (𝓞 E)] (Dd : DepData E)
  (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ),
  (∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j)) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) →
  (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → PiSplit (H := H) Dd → LeafPage O →
  ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J), ¬ (plc v ∈ O.sm ∨ plc v = O.q1 ∨ plc v = O.dd ∨ plc v = O.g1 ∨ plc v = O.g2) →
    O.e0 v j ≤ (Dd.Q.T : ℝ) * ((nuWAt (Xo := Xo (ι j)) Dd (placeBelow (K := c.F) v) (ι j)).toReal / (ramOverZ (placeBelow (K := c.F) v) : ℝ)) + 1 ∧
    (nuWAt (Xo := Xo (ι j)) Dd (placeBelow (K := c.F) v) (ι j) = 0 → O.e0 v j = 0) := by
  intro E _ _ _ H lv Dw Xo c _ Dd K _ _ _ _ _ _ Bs Df S P _ _ oc O ι hE hσ hpr hsp hPg v j hv
  obtain ⟨hprime, -, -⟩ := DepthTie.page_facts Dd O hPg hpr
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpr
  rw [p1, p2, p3, p4, p5] at hv
  simp only [not_or] at hv
  obtain ⟨h2, hq, hd, hg1, hg2⟩ := hv
  have hs := vw_sigAt_good Dd hsp hprime v h2 hq hd hg1 hg2 (Dw (ι j)) (ι j)
  obtain ⟨o1, o2⟩ := DepthTie.one_le_ramOver_below (F := c.F) v
  have hW : 0 ≤ (nuWAt (Xo := Xo (ι j)) (c := c) Dd (placeBelow (K := c.F) v) (ι j)).toReal :=
    EReal.toReal_nonneg (le_max_left _ _)
  have hram : ¬ Dd.Q.IsRam (plc v) := by
    unfold DepPage.IsRam; tauto
  have hbad : ¬ Dd.Q.IsBad (plc v) := by
    unfold DepPage.IsBad; tauto
  have r1 : (1 : ℝ) ≤ (ramOver (K := c.F) v : ℝ) := by exact_mod_cast o1
  have r2 : (1 : ℝ) ≤ (ramOverZ (placeBelow (K := c.F) v) : ℝ) := by exact_mod_cast o2
  have key : O.e0 v j = (⌈(ramOverZ (placeBelow (K := c.F) v) : ℝ) * (Dd.Q.T : ℝ) *
      ((nuWAt (Xo := Xo (ι j)) (c := c) Dd (placeBelow (K := c.F) v) (ι j)).toReal /
        (ramOverZ (placeBelow (K := c.F) v) : ℝ))⌉ : ℝ) / (ramOverZ (placeBelow (K := c.F) v) : ℝ) := by
    unfold OnObj.e0
    rw [hE v j, hσ v j, hs, DepthTie.ramw_eq_below (F := c.F) v]
    unfold EAt expE DepPage.eLam nuStarAt DepPage.nuN DepPage.cP
    simp only []
    rw [DepthTie.resChar_below (F := c.F) v, if_neg hg1, if_neg hg2, if_neg hram, if_neg hbad]
    simp only [Nat.cast_zero, add_zero, Int.cast_zero, sub_zero, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    rw [mul_div_mul_left _ _ (by linarith)]
    congr 1
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.ceil_nonneg (by positivity))]
  refine ⟨?_, fun h0 => ?_⟩
  · rw [key, div_le_iff₀ (by linarith)]
    refine (Int.ceil_lt_add_one _).le.trans ?_
    nlinarith
  · rw [key, h0]
    simp

end GlobalTheory.GoodDepth
end

section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

theorem _root_.GlobalTheory.T.sum_log_prime_depth_bounds_le_mul_weight_size : ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j), 1 ≤ w.n → Real.log (WeightAlgebra.DF w) ≤ 2 * large₂.sc.L → (WeightAlgebra.DF w : ℝ) * (Real.log (WeightAlgebra.DF w) + 2.2) + (c2 D w * Real.log D.host.QS + cHalf w * Real.log D.host.q + cHalf w * Real.log D.host.d) + ∑ i : Fin 2, (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) * Real.log (D.host.g i) ≤ WeightAlgebra.PN D large₂ * w.size := by
  first | exact @GlobalTheory.PtTie.depth_sum_le_PN | exact GlobalTheory.PtTie.depth_sum_le_PN | (intros; apply GlobalTheory.PtTie.depth_sum_le_PN <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FamInt

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}


open Classical in
def ordFn (hϖ : Irreducible ϖ) (c : FractionRing V) : WithTop ℚ :=
  if h : c = 0 then ⊤ else (((hasVal_of_ne_zero hϖ h).choose : ℚ) : WithTop ℚ)

theorem ordFn_of_hasVal (hϖ : Irreducible ϖ) {c : FractionRing V} {n : ℤ} (h : HasVal ϖ c n) :
    ordFn hϖ c = ((n : ℚ) : WithTop ℚ) := by
  have h0 := ne_zero_of_hasVal hϖ h
  rw [ordFn, dite_eq_right h0, hasVal_unique hϖ (hasVal_of_ne_zero hϖ h0).choose_spec h]

theorem ordFn_zero (hϖ : Irreducible ϖ) : ordFn hϖ 0 = ⊤ := by rw [ordFn, dite_eq_left rfl]

theorem le_ordFn_iff (hϖ : Irreducible ϖ) (c : FractionRing V) (n : ℤ) :
    ((n : ℚ) : WithTop ℚ) ≤ ordFn hϖ c ↔
      ∃ b : V, c = algebraMap V (FractionRing V) ϖ ^ n * algebraMap V (FractionRing V) b := by
  have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
  constructor
  · intro h
    by_cases hc : c = 0
    · exact ⟨0, by simp [hc]⟩
    obtain ⟨m, hm⟩ := hasVal_of_ne_zero hϖ hc
    rw [ordFn_of_hasVal hϖ hm] at h
    have hnm : n ≤ m := by exact_mod_cast h
    obtain ⟨d, rfl⟩ : ∃ d : ℕ, m = n + d := ⟨(m - n).toNat, by omega⟩
    obtain ⟨u, hu⟩ := hm
    exact ⟨ϖ ^ d * u, by rw [hu, zpow_add₀ hπ, zpow_natCast, map_mul, map_pow, _root_.mul_assoc]⟩
  · rintro ⟨b, rfl⟩
    by_cases hb : b = 0
    · rw [hb, map_zero, mul_zero, ordFn_zero]; exact le_top
    obtain ⟨d, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
    rw [ordFn_of_hasVal hϖ (n := n + d) ⟨u, by rw [zpow_add₀ hπ, zpow_natCast, map_mul, map_pow]; ring⟩]
    exact_mod_cast (by omega : n ≤ n + d)

def ordVal (hϖ : Irreducible ϖ) : AddValuation (FractionRing V) (WithTop ℚ) :=
  AddValuation.of (ordFn hϖ) (ordFn_zero hϖ)
    (by rw [ordFn_of_hasVal hϖ (n := 0) ⟨1, by simp⟩]; simp)
    (fun x y => by
      by_cases hx : x = 0
      · rw [hx, zero_add]; exact min_le_right _ _
      by_cases hy : y = 0
      · rw [hy, add_zero]; exact min_le_left _ _
      obtain ⟨n, hn⟩ := hasVal_of_ne_zero hϖ hx
      obtain ⟨m, hm⟩ := hasVal_of_ne_zero hϖ hy
      obtain ⟨a, ha⟩ := (le_ordFn_iff hϖ x (min n m)).1
        (by rw [ordFn_of_hasVal hϖ hn]; exact_mod_cast min_le_left n m)
      obtain ⟨b, hb⟩ := (le_ordFn_iff hϖ y (min n m)).1
        (by rw [ordFn_of_hasVal hϖ hm]; exact_mod_cast min_le_right n m)
      refine le_trans ?_ ((le_ordFn_iff hϖ (x + y) (min n m)).2 ⟨a + b, by rw [map_add (f := _), mul_add, ← ha, ← hb]⟩)
      rw [ordFn_of_hasVal hϖ hn, ordFn_of_hasVal hϖ hm]
      exact_mod_cast le_rfl)
    (fun x y => by
      have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
      by_cases hx : x = 0
      · rw [hx, MulZeroClass.zero_mul, ordFn_zero, top_add]
      by_cases hy : y = 0
      · rw [hy, mul_zero, ordFn_zero, add_top]
      obtain ⟨n, u, hn⟩ := hasVal_of_ne_zero hϖ hx
      obtain ⟨m, w, hm⟩ := hasVal_of_ne_zero hϖ hy
      rw [ordFn_of_hasVal hϖ ⟨u, hn⟩, ordFn_of_hasVal hϖ ⟨w, hm⟩, ordFn_of_hasVal hϖ (n := n + m)
        ⟨u * w, by rw [hn, hm, zpow_add₀ hπ, Units.val_mul, map_mul]; ring⟩]
      push_cast; rfl)

theorem valOver_ordVal (hϖ : Irreducible ϖ) : ValOver ϖ (FractionRing V) (ordVal hϖ) :=
  fun _ _ h => ordFn_of_hasVal hϖ h

theorem exists_eq_of_pos (hϖ : Irreducible ϖ) {c : FractionRing V} (h : 0 < ordVal hϖ c) :
    ∃ b : V, c = algebraMap V (FractionRing V) (ϖ * b) := by
  have h1 : (((1 : ℤ) : ℚ) : WithTop ℚ) ≤ ordFn hϖ c := by
    by_cases hc : c = 0
    · rw [hc, ordFn_zero]; exact le_top
    obtain ⟨m, hm⟩ := hasVal_of_ne_zero hϖ hc
    change 0 < ordFn hϖ c at h
    rw [ordFn_of_hasVal hϖ hm] at h ⊢
    have : (0 : ℤ) < m := by exact_mod_cast h
    exact_mod_cast (by omega : (1 : ℤ) ≤ m)
  obtain ⟨b, hb⟩ := (le_ordFn_iff hϖ c 1).1 h1
  exact ⟨b, by rw [hb, zpow_one, map_mul]⟩

def secLin {X : Scheme.{0}} {L : LB X} {n : ℕ} (c : Fin n → Γ(X, ⊤)) (t : Fin n → LB.Sec L) : LB.Sec L where
  f := fun j => ∑ i, resTop _ (c i) * (t i).f j
  compat := fun j j' => by

    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (c i) (t i)).compat j j'

variable {D : DegData V (maximalIdeal V)}

theorem exists_pull {F : Type} [Field F] [Algebra (FractionRing V) F] {k : ℕ} {α : D.toPre.X}
    (β : D.toPre.SecB k α) :
    ∃ s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k)),
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) β (DegPre.prB D.toPre F).left 1 := by
  have hL := D.toPre.P.isLB
  have hformF : FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB α i) (DegPre.famε k)
      (DegPre.famφ D.toPre F α) (DegPre.famε k) := fun U _ g =>
    Finset.prod_congr rfl fun i _ => by rw [GC.famφ_eq]
  obtain ⟨t, ht⟩ := exists_sec hL hformF (pullSec D.toPre.P.L _ _ β (DegPre.prB D.toPre F).left)
  exact ⟨t, SectionScalarValuation.secScal_of_sval hL fun y J hJ =>
    ((ht _ _ y J hJ).trans (SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ)).symm⟩

theorem exists_int_of_vge (hϖ : Irreducible ϖ) {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))} {r : ℚ}
    (hr : 0 < r) (hs : VGe D (FractionRing V) (ordVal hϖ) k α s r) :
    ∃ f f' : D.toPre.SecB k α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left 1 ∧
      SecIsMul D.toPre.P.A.hom ϖ f f' := by
  obtain ⟨n, a, σ, σF, hσ, hva, hsum⟩ := hs
  choose b hb using fun i => exists_eq_of_pos hϖ (lt_of_lt_of_le (by exact_mod_cast hr) (hva i))
  refine ⟨secLin (fun i => scal D.toPre.P.A.hom (ϖ * b i)) σ, secLin (fun i => scal D.toPre.P.A.hom (b i)) σ,
    SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_, fun j => ?_⟩
  · rw [SectionScalarValuation.sval_lin (fun i => scal D.toPre.P.A.hom (ϖ * b i)) σ (fun _ => rfl) _ y hJ,
      SectionScalarValuation.sval_lin (fun i => gF D.toPre (FractionRing V) (a i)) σF (fun j => hsum j) (𝟙 _) y hJ]
    refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ (SectionScalarValuation.secScal_sval (hσ i) _ y hJ)
    have e1 : gs (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y ⊤ (scal D.toPre.P.A.hom (ϖ * b i)) =
        cst ((𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom) y (ϖ * b i) :=
      gs_pull _ _ y ⊤ trivial _
    have e2 : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (a i)) =
        cst (𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) y (a i) :=
      gs_pull _ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial _
    have e3 : (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom =
        ((𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) ≫
          spMap (algebraMap (FractionRing V) (FractionRing V))) ≫ spMap (algebraMap V (FractionRing V)) := by
      rw [Category.id_comp, Category.id_comp, Category.assoc, Over.w]
      exact (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).symm
    rw [e1, e2, e3, cst_comp, cst_comp, hb i]
    rfl
  · show ∑ i, resTop _ (scal D.toPre.P.A.hom (ϖ * b i)) * (σ i).f j =
      resTop _ (scal D.toPre.P.A.hom ϖ) * ∑ i, resTop _ (scal D.toPre.P.A.hom (b i)) * (σ i).f j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [scal, resTop, map_mul, _root_.mul_assoc]

end FamInt

theorem integralFamily_of_strictMin : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (q : ℕ), 1 ≤ q → ∀ (χ : D.toPre.X) (β : D.toPre.SecB q χ), (∀ z, z ≠ 0 → Q χ < Q (χ + q • z)) → ∃ (Φ : Fam D.toPre (FractionRing V) q) (f : ∀ α, D.toPre.SecB q α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α) (D.toPre.famφB α) (DegPre.famε q) (f α) (DegPre.prB D.toPre (FractionRing V)).left 1) ∧ f χ = β ∧ (∀ α, (∀ z, α ≠ χ + q • z) → ∀ j, (f α).f j = 0) ∧ ∀ α, α ≠ χ → ∃ f' : D.toPre.SecB q α, SecIsMul D.toPre.P.A.hom ϖ (f α) f' := by
  intro hL V _ _ _ ϖ hϖ D Q hQ q hq χ β hmin
  classical
  obtain ⟨σ, hσ⟩ := FamInt.exists_pull (F := FractionRing V) β
  obtain ⟨Φ, hΦ, hΦ0⟩ := UUA.exists_fam_rep (F := FractionRing V) hL.globalFns D.tau_bimult q χ (fun a b h => by
    have h' : (q : ℤ) • a = (q : ℤ) • b := by
      rw [natCast_zsmul, natCast_zsmul]; exact add_left_cancel h
    exact smul_right_injective D.toPre.X (by omega : (q : ℤ) ≠ 0) h') σ
  have h0 : VGe D (FractionRing V) (FamInt.ordVal hϖ) q χ (Φ.s χ) 0 := by
    refine ⟨1, fun _ => 1, fun _ => β, fun _ => Φ.s χ, fun _ => hΦ ▸ hσ, fun _ => ?_, fun j => ?_⟩
    · simp
    · simp [DegPre.constBF]
  have key : ∀ α : D.toPre.X, ∃ f : D.toPre.SecB q α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε q) f (DegPre.prB D.toPre (FractionRing V)).left 1 ∧
      (∀ h : χ = α, f = h ▸ β) ∧ ((∀ z, α ≠ χ + q • z) → ∀ j, f.f j = 0) ∧
      (α ≠ χ → ∃ f' : D.toPre.SecB q α, SecIsMul D.toPre.P.A.hom ϖ f f') := by
    intro α
    by_cases hα : χ = α
    · subst hα
      exact ⟨β, hΦ ▸ hσ, fun _ => rfl, fun h => absurd (by simp) (h 0), fun h => absurd rfl h⟩
    by_cases hc : ∃ z, α = χ + q • z
    · obtain ⟨z, rfl⟩ := hc
      have hz : z ≠ 0 := by rintro rfl; exact hα (by simp)
      have H := SectionScalarValuation.fe_move hϖ hQ (FamInt.valOver_ordVal hϖ) q z χ Φ h0
      have hlt := hmin z hz
      rw [q_shift hϖ hQ, lt_add_iff_pos_right] at hlt
      have hpos : (0 : ℤ) < q * Q z + QForm.bOf D.toPre Q z χ := (pos_iff_pos_of_mul_pos hlt).1 (by omega)
      obtain ⟨f, f', h1, h2⟩ := FamInt.exists_int_of_vge hϖ (by rw [zero_add]; exact_mod_cast hpos) H
      exact ⟨f, h1, fun h => absurd h hα, fun h => absurd rfl (h z), fun _ => ⟨f', h2⟩⟩
    · refine ⟨SecOps.secZero, SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_, fun h => absurd h hα,
        fun _ _ => rfl, fun _ => ⟨SecOps.secZero, fun j => (mul_zero _).symm⟩⟩
      rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
        UUA.sval_zero_of (hΦ0 α fun mu e => hc ⟨mu, e.symm⟩) _ y J (hJ.mem _ _)]
  choose f h1 h2 h3 h4 using key
  exact ⟨Φ, f, h1, h2 χ rfl, h3, h4⟩

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnitBallBox

section Fam

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

variable {j : ℕ} {D D' : DegPre R} (pD : IsPowDeg D' D j)

theorem box_secScal {S : Fam D' F k} {s : Fin j → Fam D F k} (hS : IsBoxFam pD F k S s)
    {f' : ∀ α : D'.X, D'.SecB k α} {f : Fin j → ∀ α : D.X, D.SecB k α} (hf : IsBoxFamB pD k f' f) (α' : D'.X)
    (h : ∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F (pD.xe α' i)) (DegPre.famε k) ((s i).s (pD.xe α' i))
      (D.famφB (pD.xe α' i)) (DegPre.famε k) (f i (pD.xe α' i)) (DegPre.prB D F).left 1) :
    GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' F α') (DegPre.famε k) (S.s α')
      (D'.famφB α') (DegPre.famε k) (f' α') (DegPre.prB D' F).left 1 := by
  obtain ⟨hφ, H⟩ := hS α'
  obtain ⟨hψ, H'⟩ := hf α'
  have e₄ : ∀ i, (DegPre.prB D' F).left ≫ (pD.pw.pr i).left =
      prB pD F i ≫ (DegPre.prB D F).left := fun i => by
    rw [← Over.comp_left, ← Over.comp_left]; congr 1; exact (whiskerLeft_snd _ _).symm
  exact BoxFamScalar.secScal_box D.P.isLB D'.P.isLB pD.w (GC.famφ_eq D' F α') e₄
    (S.s α') (fun i => (s i).s (pD.xe α' i)) (f' α') (fun i => f i (pD.xe α' i))
    (fun y _ _ hJ hJ' => BoxFamScalar.box_sval pD.w hφ (S.s α') (fun i => (s i).s (pD.xe α' i)) _ H (𝟙 _) y hJ hJ')
    (fun y _ _ hJ hJ' => BoxFamScalar.box_sval pD.w hψ (f' α') (fun i => f i (pD.xe α' i)) _ H' _ y hJ hJ')
    (fun _ => 1) 1 (fun y => by simp only [NuBox.gs_one, Finset.prod_const_one]) h

end Fam


end GlobalTheory.UnitBallBox
end
end
