module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.LeIff

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nonzeroLocus_zero {M : LB X} : ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (0 : LB.Sec M) = ⊥ := by
  simp [ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus]

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

theorem dict_zero (P : Pair p) (a b : ℤ) {M : HermLB p} (e : M.B.Sec → X.functionField)
    (he : ∀ (u : M.B.Sec) (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j →
      (x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u ↔ UnitAt x (P.loc a b (e u) i j))) : e 0 = 0 := by
  by_contra h
  obtain ⟨i, hi⟩ := exists_chart P.L.isLB (genericPoint X)
  obtain ⟨j, hj⟩ := exists_chart P.A.isLB (genericPoint X)
  have hne : P.loc a b (e 0) i j ≠ 0 := by
    simp only [Pair.loc]
    exact mul_ne_zero (mul_ne_zero h (zpow_ne_zero _ (P.r i).ne_zero)) (zpow_ne_zero _ (P.r' j).ne_zero)
  have hmem := (he 0 _ i j hi hj).2 (unitAt_genericPoint hne)
  rw [nonzeroLocus_zero] at hmem
  simp at hmem

theorem rep_diff (P : Pair p) : P.Rep 1 (-1) (P.L.tens P.A.dual) := by
  obtain ⟨h1, h2, -⟩ := Pair.rep_base k X p P
  have h3 : P.Rep 0 (-1) P.A.dual := by
    have := Pair.rep_dual k X p P 0 1 _ h2
    rwa [neg_zero] at this
  have := Pair.rep_tens k X p P 1 0 0 (-1) _ _ h1 h3
  rwa [add_zero, zero_add] at this

def scaleL (P : Pair p) (f : X.functionFieldˣ) : Pair p :=
  ⟨P.L, P.A, fun i => f * P.r i, P.r', fun i j h => by
    simp only [Units.val_mul]
    rw [P.hr i j h]
    ring, P.hr'⟩

theorem scaleL_loc (P : Pair p) (f : X.functionFieldˣ) (i : P.L.B.ι) (j : P.A.B.ι) :
    (scaleL P f).loc 1 (-1) 1 i j = P.loc 1 (-1) f i j := by
  simp only [Pair.loc, scaleL, Units.val_mul, zpow_one, one_mul]

end GlobalTheory.HSNef.LeIff


open GlobalTheory.HSNef.LeIff in
theorem GlobalTheory.HSNef.le_iff_exists_smallSec : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ A B : HermLB p, Le B A ↔ ∃ s ∈ (A.tens B.dual).smallSec, s ≠ 0 := by
  intro k _ X _ p A B
  constructor
  · rintro ⟨P, rfl, rfl, h1H, h1n⟩
    obtain ⟨e, -, hrange, hnorm, hloc⟩ := RepDict.rep_dict k X p P 1 (-1) _ (rep_diff P)
    obtain ⟨u, hu⟩ : (1 : X.functionField) ∈ Set.range e := by rw [hrange]; exact h1H
    refine ⟨u, fun σ y => ?_, ?_⟩
    · rw [← hnorm, hu]
      have h0 := nu_nonneg P 1 (-1) σ y 1
      have h1 := h1n σ y
      nlinarith
    · rintro rfl
      rw [dict_zero P 1 (-1) e hloc] at hu
      exact zero_ne_one hu
  · rintro ⟨s, hs, hs0⟩
    obtain ⟨P, hPL, hPA⟩ := exists_pair A B
    subst hPL hPA
    obtain ⟨e, hinj, hrange, hnorm, hloc⟩ := RepDict.rep_dict k X p P 1 (-1) _ (rep_diff P)
    have hfH : e s ∈ P.H 1 (-1) := by
      have : e s ∈ Set.range e := ⟨s, rfl⟩
      rw [hrange] at this
      exact this
    have hf0 : e s ≠ 0 := fun h => hs0 (hinj (h.trans (dict_zero P 1 (-1) e hloc).symm))
    have hfn : ∀ σ (y : CxPts p σ), P.nu 1 (-1) σ y (e s) ≤ 1 := fun σ y => by
      have h := hnorm s σ y
      have h' := hs σ y
      have h0 := nu_nonneg P 1 (-1) σ y (e s)
      nlinarith
    refine ⟨scaleL P (Units.mk0 _ hf0), rfl, rfl, fun x i j hi hj => ?_, fun σ y => ?_⟩
    · rw [show (scaleL P (Units.mk0 _ hf0)).loc 1 (-1) 1 i j = P.loc 1 (-1) (e s) i j from
        scaleL_loc P (Units.mk0 _ hf0) i j]
      exact hfH x i j hi hj
    · have := hfn σ y
      simp only [Pair.nu] at this ⊢
      rw [show ∀ i j, (scaleL P (Units.mk0 _ hf0)).loc 1 (-1) 1 i j = P.loc 1 (-1) (e s) i j from
        scaleL_loc P (Units.mk0 _ hf0)]
      exact this
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.doubleSpace_small_of_functionField_embeds_ratFunc : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ j : W.Z.functionField →+* RatFunc Y.Fn, j.comp W.α₁ = algebraMap Y.Fn (RatFunc Y.Fn) → W.Small := by
  first | exact @GlobalTheory.FlagPush.SmallPf.main | exact GlobalTheory.FlagPush.SmallPf.main | (intros; apply GlobalTheory.FlagPush.SmallPf.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.encard_smallSections_le_of_hermLBLeBySmallSection : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ A B : HermLB p, Le B A → B.smallSec.encard ≤ A.smallSec.encard := by
  first | exact @GlobalTheory.HSNef.LeCard.encard_smallSec_le | exact GlobalTheory.HSNef.LeCard.encard_smallSec_le | (intros; apply GlobalTheory.HSNef.LeCard.encard_smallSec_le <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_small_ample_through_off' : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (x z : X) (ε : ℚ), IsAmpleLB N → ¬ z ⤳ x → 0 < ε → ∃ (b : ℚ) (A : X → ℚ), 0 ≤ b ∧ b ≤ ε ∧ QNum p N b A ∧ Off A x ∧ ¬ Off A z := by
  first | exact @GlobalTheory.PairStep.exists_small_ample_through_off | exact GlobalTheory.PairStep.exists_small_ample_through_off | (intros; apply GlobalTheory.PairStep.exists_small_ample_through_off <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.fubiniStudy_le_shift_of_smallSections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M B : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → SmallFam B f w → Le M (B.shift (fun _ => Real.log (Fintype.card J) / 2) fun _ => rfl) := by
  first | exact @GlobalTheory.HSNef.le_shift_of_isFS | exact GlobalTheory.HSNef.le_shift_of_isFS | (intros; apply GlobalTheory.HSNef.le_shift_of_isFS <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.fubiniStudy_subfamily_le_shift_fubiniStudy_family : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M M' : HermLB p) (J J' : Type) [Fintype J] [Fintype J'] (f : J → X.functionField) (w : J → ℝ) (w' : J' → ℝ) (ι : J' → J) (Δ : ℝ), Function.Injective ι → IsFS M f w → IsFS M' (f ∘ ι) w' → (∀ j, w' j + Δ ≤ w (ι j)) → Le (M'.shift (fun _ => Δ) fun _ => rfl) M := by
  first | exact @GlobalTheory.HSNef.le_shift_of_isFS_sub | exact GlobalTheory.HSNef.le_shift_of_isFS_sub | (intros; apply GlobalTheory.HSNef.le_shift_of_isFS_sub <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_not_kltAt_sub_of_not_lcAt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (x : X), IsQCart D → KltAt p n Δ x → ¬ LcAt p n (Δ + D) x → ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ¬ KltAt p n (Δ + (1 - δ) • D) x := by
  first | exact @GlobalTheory.PairStep.not_kltAt_sub_of_not_lcAt | exact GlobalTheory.PairStep.not_kltAt_sub_of_not_lcAt | (intros; apply GlobalTheory.PairStep.not_kltAt_sub_of_not_lcAt <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.not_lcAt_add_of_isNkltCentre' : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ A : X → ℚ) (z x : X), IsNkltCentre p n Γ z → IsQCart A → ¬ Off A z → z ⤳ x → ¬ LcAt p n (Γ + A) x := by
  first | exact @GlobalTheory.PairStep.not_lcAt_add_of_isNkltCentre | exact GlobalTheory.PairStep.not_lcAt_add_of_isNkltCentre | (intros; apply GlobalTheory.PairStep.not_lcAt_add_of_isNkltCentre <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.ratFnFamilySmall_pullback_birationalModel : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ (B : HermLB p) (J : Type) (f : J → X.functionField) (w : J → ℝ), SmallFam B f w → SmallFam (B.pull π hπ) (fun j => φ (f j)) w := by
  first | exact @GlobalTheory.HSNef.smallFam_pull | exact GlobalTheory.HSNef.smallFam_pull | (intros; apply GlobalTheory.HSNef.smallFam_pull <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.smallSections_pairSum_ratFnFamily_tensor : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (J : Type) (f : J → X.functionField) (w : J → ℝ), (∀ j, f j ∈ P.Bl 1 1 (Real.exp (-w j))) → SmallFam (P.L.tens P.A) f w := by
  first | exact @GlobalTheory.HSNef.smallFam_pair_tens | exact GlobalTheory.HSNef.smallFam_pair_tens | (intros; apply GlobalTheory.HSNef.smallFam_pair_tens <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.exists_globalGeneration_ample_pair_multiples : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ P : Pair p, IsAmpleLB P.A.B → ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ j : ℕ, GenAt P (c₀ * j) := by
  first | exact @GlobalTheory.HSNef.AmpleGen.exists_genAt_mul | exact GlobalTheory.HSNef.AmpleGen.exists_genAt_mul | (intros; apply GlobalTheory.HSNef.AmpleGen.exists_genAt_mul <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.genericPair_specializes_diagonal_genericPoint : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K), GenPair Y ψ₁ ψ₂ → ∃ h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str, Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h (IsLocalRing.closedPoint K) ⤳ Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
  first | exact @GlobalTheory.FlagPush.genPair_specializes_diagonal | exact GlobalTheory.FlagPush.genPair_specializes_diagonal | (intros; apply GlobalTheory.FlagPush.genPair_specializes_diagonal <;> assumption)
end
