module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem not_kltAt_sub_of_not_lcAt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D : X → ℚ) (x : X), IsQCart D → KltAt p n Δ x → ¬ LcAt p n (Δ + D) x →
    ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ¬ KltAt p n (Δ + (1 - δ) • D) x := by
  intro X _ _ _ p n hp hn Δ D x hD hk hlc
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨η, m, g, hη, hm, hg, hd⟩ := hk
  obtain ⟨m', f, hm', hf, hDf⟩ := GlobalTheory.T.exists_localEquation_effectiveQCartierDivisor X p D hD x
  obtain ⟨m₁, g₁, hm₁, hg₁, hd₁⟩ := GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Δ D η x m m' g f 1 hm hm' hg hDf
  rw [one_smul] at hg₁
  have hnl := (GlobalTheory.T.logCanonicalAt_iff_of_isLogCanonicalLocalEquation X p n hp hn (Δ + D) η x m₁ g₁ hη hm₁ hg₁).not.1 hlc
  push_neg at hnl
  obtain ⟨E, hE, hlt⟩ := hnl
  rw [hd₁, one_mul] at hlt
  set a := discrep E η m g with ha
  set t : ℚ := (E.ord f : ℚ) / m' with ht
  have hm'q : (0 : ℚ) < m' := by exact_mod_cast hm'
  have ht0 : 0 ≤ t := div_nonneg (by exact_mod_cast (E.ord_nonneg_iff f).2 (hE _ hf)) hm'q.le
  have ha1 := hd E hE
  refine ⟨(-1 - a + t) / (t + 1), div_pos (by linarith) (by linarith), fun δ hδ0 hδ hk' => ?_⟩
  obtain ⟨m₂, g₂, hm₂, hg₂, hd₂⟩ := GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Δ D η x m m' g f (1 - δ) hm hm' hg hDf
  have := ((hg₂.kltAt_iff hn hη hm₂).1 hk') E hE
  rw [hd₂] at this
  have h1 : δ * (t + 1) ≤ -1 - a + t := (le_div_iff₀ (by linarith)).1 hδ
  nlinarith
end GlobalTheory.PairStep
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem not_lcAt_add_of_isNkltCentre : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ A : X → ℚ) (z x : X), IsNkltCentre p n Γ z → IsQCart A → ¬ Off A z → z ⤳ x → ¬ LcAt p n (Γ + A) x := by
  intro X _ _ _ p n hp hn Γ A z x hN hA hoff hzx hlc
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have hlcz := ((GlobalTheory.T.kawamataLogTerminal_logCanonical_generisation X p n (Γ + A) x z hzx).2 hlc)
  obtain ⟨E, η, m, g, hη, hm, hlog, hC, hd⟩ := hN
  obtain ⟨m₀, D₀, hm₀, hEff, rfl⟩ := hA
  obtain ⟨m', f, hm', hreg, heq⟩ := GlobalTheory.T.exists_localEquation_effectiveQCartierDivisor X p (qWeil D₀ m₀) ⟨m₀, D₀, hm₀, hEff, rfl⟩ z
  obtain ⟨m'', g'', hm'', hlog'', hdisc⟩ :=
    GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Γ (qWeil D₀ m₀) η z m m' g f 1 hm hm' hlog heq
  rw [one_smul] at hlog''
  have h1 := ((GlobalTheory.T.logCanonicalAt_iff_of_isLogCanonicalLocalEquation X p n hp hn (Γ + qWeil D₀ m₀) η z m'' g'' hη hm'' hlog'').1 hlcz) E hC.1
  rw [hdisc E, one_mul] at h1
  have hf0 : 0 ≤ E.ord f := (E.ord_nonneg_iff f).2 (hC.1 _ hreg)
  have hm'q : (0 : ℚ) < m' := by exact_mod_cast hm'
  have hfle : (E.ord f : ℚ) / m' ≤ 0 := by linarith
  have hfle' : (E.ord f : ℚ) ≤ 0 := by
    rwa [div_le_iff₀ hm'q, zero_mul] at hfle
  have hord : E.ord f = 0 := by
    have : E.ord f ≤ 0 := by exact_mod_cast hfle'
    omega
  have hreg' := hC.2 f hreg hord
  apply hoff
  intro w hw
  by_cases hc : Order.coheight w = 1
  · obtain ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) hc
    rw [heq w hw F hF]
    have a : 0 ≤ F.ord f :=
      (F.ord_nonneg_iff f).2 ((hF _).2 (regAt_of_specializes hw hreg))
    have b : 0 ≤ F.ord f⁻¹ :=
      (F.ord_nonneg_iff _).2 ((hF _).2 (regAt_of_specializes hw hreg'))
    rw [F.ord_inv] at b
    have : F.ord f = 0 := by omega
    simp [this]
  · have : D₀.mult w = 0 := by
      by_contra h
      exact hc (CartierDiv.coheight_eq_one_of_mult_ne_zero h)
    simp [qWeil, this]

end GlobalTheory.PairStep
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem smallFam_pair_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (J : Type) (f : J → X.functionField) (w : J → ℝ), (∀ j, f j ∈ P.Bl 1 1 (Real.exp (-w j))) → SmallFam (P.L.tens P.A) f w := by
  intro k _ X _ p P J f w hf
  have e (c : (P.L.tens P.A).B.ι) (j : J) :
      f j * (((P.r c.1 * P.r' c.2 : X.functionFieldˣ)) : X.functionField) = P.loc 1 1 (f j) c.1 c.2 := by
    simp only [Pair.loc, Units.val_mul, zpow_one]; ring
  refine ⟨fun c => P.r c.1 * P.r' c.2, GlobalTheory.PtHtComb.isRatSec_tens P.hr P.hr', ?_, ?_⟩
  · intro x c hc j
    rw [e]
    exact (hf j).1 x c.1 c.2 hc.1 hc.2
  · intro σ y c hc j
    obtain ⟨hc₁, hc₂⟩ := mem_ptsIn_inf.1 hc
    have h := nu_eq k X p P 1 1 (f j) (hf j).1 σ y c.1 c.2 hc₁ hc₂
    have hb := (hf j).2 σ y
    rw [h] at hb
    rw [e]
    change _ * Real.exp (-((P.L.φ σ).φ c.1 y + (P.A.φ σ).φ c.2 y) / 2) ≤ _
    simpa using hb

end GlobalTheory.HSNef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.LeCard

theorem encard_smallSec_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ A B : HermLB p, Le B A → B.smallSec.encard ≤ A.smallSec.encard := by
  intro k _ X _ p A B hBA
  obtain ⟨P, rfl, rfl, h1⟩ := hBA
  have hrep := Pair.rep_base k X p P
  have eL : P.L.smallSec.encard = (P.Bl 1 0 1).encard :=
    SmallBall.encard_eq_Bl P hrep.1 P.L.smallSec 1 zero_le_one fun u => by
      simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  have eA : P.A.smallSec.encard = (P.Bl 0 1 1).encard :=
    SmallBall.encard_eq_Bl P hrep.2.1 P.A.smallSec 1 zero_le_one fun u => by
      simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  rw [eL, eA]
  refine Set.encard_le_encard fun f hf => ?_
  have e := NuMul.mul_mem_H_and_nu_mul k X p P 1 (-1) 0 1 1 f h1.1 hf.1
  rw [one_mul, add_zero, neg_add_cancel] at e
  refine ⟨e.1, fun σ y => ?_⟩
  rw [e.2 σ y]
  calc P.nu 1 (-1) σ y 1 * P.nu 0 1 σ y f ≤ 1 * 1 :=
        mul_le_mul (h1.2 σ y) (hf.2 σ y) (SmallBall.nu_nonneg P 0 1 σ y f) zero_le_one
    _ = 1 := one_mul 1

end GlobalTheory.HSNef.LeCard
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.FsTop

variable {X : Scheme.{0}} [IsIntegral X]

theorem regAt_mul' {x : X} {a b : X.functionField} (ha : RegAt x a) (hb : RegAt x b) : RegAt x (a * b) := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  exact ⟨u * v, map_mul _ u v⟩

theorem regAt_inv_of_unitAt {x : X} {a : X.functionField} (ha : UnitAt x a) : RegAt x a⁻¹ := by
  obtain ⟨u, hu, rfl⟩ := ha
  refine ⟨(hu.unit⁻¹ : (X.presheaf.stalk x)ˣ), ?_⟩
  refine (eq_inv_of_mul_eq_one_left ?_)
  rw [← map_mul]
  simp

end GlobalTheory.HSNef.FsTop


open GlobalTheory.HSNef.FsTop in
theorem GlobalTheory.HSNef.le_shift_of_isFS : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M B : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → SmallFam B f w → Le M (B.shift (fun _ => Real.log (Fintype.card J) / 2) fun _ => rfl) := by
  intro k _ X _ p M B J _ f w hM hB
  obtain ⟨ρ, hρ, hreg, hφ⟩ := hM
  obtain ⟨β, hβ, hbreg, hbnorm⟩ := hB
  have key : ∀ (x : X) (c : B.B.ι) (d : M.B.ι), x ∈ B.B.U c → x ∈ M.B.U d →
      RegAt x ((β c : X.functionField) / (ρ d : X.functionField)) := by
    intro x c d hc hd
    obtain ⟨l, hl⟩ := (hreg x d hd).2
    have hfl : f l ≠ 0 := fun h => hl.ne_zero (by rw [h, zero_mul])
    have e : (β c : X.functionField) / (ρ d) = (f l * β c) * (f l * ρ d)⁻¹ := by
      field_simp
    rw [e]
    exact regAt_mul' (hbreg x c hc l) (regAt_inv_of_unitAt hl)
  refine (GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients k X p _ M).2 ⟨β, ρ, hβ, hρ, fun x i j hi hj => key x i j hi hj, ?_⟩
  intro σ y i j hi hj
  have hxi : under y ∈ B.B.U i := mem_ptsIn.1 hi
  have hxj : under y ∈ M.B.U j := mem_ptsIn.1 hj
  have hq := key _ i j hxi hxj
  obtain ⟨l₀, hl₀⟩ := (hreg _ j hxj).2
  set q : X.functionField := (β i : X.functionField) / (ρ j : X.functionField) with hqdef
  have hval : ∀ l, ratVal (f l * (β i : X.functionField)) y = ratVal q y * ratVal (f l * (ρ j : X.functionField)) y := by
    intro l
    have e : f l * (β i : X.functionField) = q * (f l * (ρ j : X.functionField)) := by
      rw [hqdef]; field_simp
    rw [e, ratVal_mul hq ((hreg _ j hxj).1 l)]
  have hφj : (M.φ σ).φ j y = Real.log (∑ l, ‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l)) :=
    hφ σ y j hj
  have hφi : ((B.shift (fun _ => Real.log (Fintype.card J) / 2) fun _ => rfl).φ σ).φ i y =
      (B.φ σ).φ i y + 2 * (Real.log (Fintype.card J) / 2) := rfl
  set S := ∑ l, ‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l) with hS
  set φB := (B.φ σ).φ i y
  set Q := ‖ratVal q y‖
  have hn : (1 : ℝ) ≤ Fintype.card J := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨l₀⟩
  have hSpos : 0 < S := by
    have h0 : 0 < ‖ratVal (f l₀ * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l₀) :=
      mul_pos (pow_pos (norm_pos_iff.2 (ratVal_ne_zero hl₀)) 2) (Real.exp_pos _)
    exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun l => ‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l))
      (fun l _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (Finset.mem_univ l₀))

  have hterm : ∀ l, Q ^ 2 * (‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l)) ≤ Real.exp φB := by
    intro l
    have h1 := hbnorm σ y i hi l
    rw [hval l, norm_mul] at h1
    have h2 : Q * ‖ratVal (f l * (ρ j : X.functionField)) y‖ ≤ Real.exp (-w l) * Real.exp (φB / 2) := by
      have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (φB / 2)).le
      rwa [mul_assoc, ← Real.exp_add, show -φB / 2 + φB / 2 = 0 by ring, Real.exp_zero, mul_one] at this
    have h3 := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) h2 2
    have e1 : (Real.exp (-w l) * Real.exp (φB / 2)) ^ 2 * Real.exp (2 * w l) = Real.exp φB := by
      rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1; push_cast; ring
    calc Q ^ 2 * (‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l))
        = (Q * ‖ratVal (f l * (ρ j : X.functionField)) y‖) ^ 2 * Real.exp (2 * w l) := by ring
      _ ≤ (Real.exp (-w l) * Real.exp (φB / 2)) ^ 2 * Real.exp (2 * w l) :=
          mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
      _ = Real.exp φB := e1
  have hsum : Q ^ 2 * S ≤ Fintype.card J * Real.exp φB := by
    rw [hS, Finset.mul_sum]
    calc ∑ l, Q ^ 2 * (‖ratVal (f l * (ρ j : X.functionField)) y‖ ^ 2 * Real.exp (2 * w l))
        ≤ ∑ _l : J, Real.exp φB := Finset.sum_le_sum fun l _ => hterm l
      _ = Fintype.card J * Real.exp φB := by simp
  rw [hφi, hφj]
  have hE : Real.exp (-(φB + 2 * (Real.log (Fintype.card J) / 2) - Real.log S) / 2) ^ 2 =
      S / (Fintype.card J * Real.exp φB) := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(φB + 2 * (Real.log (Fintype.card J) / 2) - Real.log S) / 2)
        = Real.log S - (Real.log (Fintype.card J) + φB) by push_cast; ring,
      Real.exp_sub, Real.exp_add, Real.exp_log hSpos, Real.exp_log (by linarith)]
  have hpos : 0 ≤ Q * Real.exp (-(φB + 2 * (Real.log (Fintype.card J) / 2) - Real.log S) / 2) :=
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine (pow_le_one_iff_of_nonneg hpos two_ne_zero).1 ?_
  rw [mul_pow, hE, ← mul_div_assoc, div_le_one (by positivity)]
  exact hsum
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_ne_zero {x : X} {h : X.functionField} (hh : UnitAt x h) : h ≠ 0 := by
  obtain ⟨b, hb, rfl⟩ := hh
  intro e
  have h1 : algebraMap (X.presheaf.stalk x) X.functionField (b * ↑hb.unit⁻¹) = 1 := by
    rw [IsUnit.mul_val_inv, map_one]
  rw [map_mul, e, zero_mul] at h1
  exact zero_ne_one h1

theorem regAt_div_unitAt {x : X} {g h : X.functionField} (hg : RegAt x g) (hh : UnitAt x h) :
    RegAt x (g / h) := by
  obtain ⟨a, ha⟩ := hg
  obtain ⟨b, hb, hbh⟩ := hh
  refine ⟨a * ↑hb.unit⁻¹, ?_⟩
  have h1 : algebraMap (X.presheaf.stalk x) X.functionField b *
      algebraMap (X.presheaf.stalk x) X.functionField ↑hb.unit⁻¹ = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  rw [map_mul, ha, div_eq_mul_inv, ← hbh, eq_inv_of_mul_eq_one_right h1]

theorem le_shift_of_isFS_sub : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (M M' : HermLB p) (J J' : Type) [Fintype J] [Fintype J'] (f : J → X.functionField) (w : J → ℝ)
      (w' : J' → ℝ) (ι : J' → J) (Δ : ℝ), Function.Injective ι → IsFS M f w → IsFS M' (f ∘ ι) w' →
      (∀ j, w' j + Δ ≤ w (ι j)) → Le (M'.shift (fun _ => Δ) fun _ => rfl) M := by
  intro k _ X _ p M M' J J' _ _ f w w' ι Δ hι hM hM' hw
  rw [GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients]
  obtain ⟨ρ, hρ, hreg, hφ⟩ := hM
  obtain ⟨ρ', hρ', hreg', hφ'⟩ := hM'
  simp only [Function.comp_apply] at hreg' hφ'

  have hq : ∀ (x : X) c d (j' : J'), UnitAt x (f (ι j') * (ρ' d : X.functionField)) →
      (ρ c : X.functionField) / (ρ' d : X.functionField) =
        f (ι j') * (ρ c : X.functionField) / (f (ι j') * (ρ' d : X.functionField)) := by
    intro x c d j' hu
    have hf : f (ι j') ≠ 0 := left_ne_zero_of_mul (unitAt_ne_zero hu)
    rw [mul_div_mul_left _ _ hf]
  have hτ : ∀ (x : X) c d, x ∈ M.B.U c → x ∈ M'.B.U d →
      RegAt x ((ρ c : X.functionField) / (ρ' d : X.functionField)) := by
    intro x c d hc hd
    obtain ⟨-, j', hj'⟩ := hreg' x d hd
    rw [hq x c d j' hj']
    exact regAt_div_unitAt ((hreg x c hc).1 (ι j')) hj'
  refine ⟨ρ, ρ', hρ, hρ', hτ, ?_⟩
  intro σ y c d hc hd
  have hc' := mem_ptsIn.1 hc
  have hd' := mem_ptsIn.1 hd
  set τ : X.functionField := (ρ c : X.functionField) / (ρ' d : X.functionField) with hτdef
  have hτr : RegAt (under y) τ := hτ _ c d hc' hd'

  have hval : ∀ j' : J', ratVal (f (ι j') * (ρ c : X.functionField)) y =
      ratVal τ y * ratVal (f (ι j') * (ρ' d : X.functionField)) y := by
    intro j'
    have e : f (ι j') * (ρ c : X.functionField) = τ * (f (ι j') * (ρ' d : X.functionField)) := by
      rw [hτdef]; field_simp
    rw [e, ratVal_mul hτr ((hreg' _ d hd').1 j')]
  set S : ℝ := ∑ j, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j) with hS
  set S' : ℝ := ∑ j', ‖ratVal (f (ι j') * (ρ' d : X.functionField)) y‖ ^ 2 * Real.exp (2 * w' j') with hS'
  have e1 : (M.φ σ).φ c y = Real.log S := hφ σ y c hc
  have e2 : ((M'.shift (fun _ => Δ) fun _ => rfl).φ σ).φ d y = Real.log S' + 2 * Δ := by
    change (M'.φ σ).φ d y + 2 * Δ = _
    rw [hφ' σ y d hd]
  have hS'pos : 0 < S' := by
    obtain ⟨-, j₀, hj₀⟩ := hreg' _ d hd'
    refine Finset.sum_pos' (fun j _ => by positivity) ⟨j₀, Finset.mem_univ _, ?_⟩
    have : ratVal (f (ι j₀) * (ρ' d : X.functionField)) y ≠ 0 := ratVal_ne_zero hj₀
    have : 0 < ‖ratVal (f (ι j₀) * (ρ' d : X.functionField)) y‖ := norm_pos_iff.2 this
    positivity
  set t : ℝ := ‖ratVal τ y‖ with ht
  have hineq : t ^ 2 * Real.exp (2 * Δ) * S' ≤ S := by
    classical
    calc t ^ 2 * Real.exp (2 * Δ) * S'
        = ∑ j', ‖ratVal (f (ι j') * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * (w' j' + Δ)) := by
          rw [hS', Finset.mul_sum]
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [hval, norm_mul, ← ht, mul_add, Real.exp_add]; ring
      _ ≤ ∑ j', ‖ratVal (f (ι j') * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w (ι j')) := by
          refine Finset.sum_le_sum fun j' _ => ?_
          gcongr
          exact hw j'
      _ = ∑ j ∈ Finset.univ.image ι, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j) :=
          by rw [Finset.sum_image (fun a _ b _ h => hι h)]
      _ ≤ S := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => by positivity
  rw [e1, e2]
  have ht0 : 0 ≤ t := norm_nonneg _
  rcases ht0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact zero_le_one
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity) hineq
  have hE : Real.exp (-(Real.log S - (Real.log S' + 2 * Δ)) / 2) ^ 2 = S' * Real.exp (2 * Δ) / S := by
    rw [← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (-(Real.log S - (Real.log S' + 2 * Δ)) / 2) = (Real.log S' + 2 * Δ) - Real.log S := by
      push_cast; ring
    rw [this, Real.exp_sub, Real.exp_add, Real.exp_log hS'pos, Real.exp_log hSpos]
  rw [← sq_le_one_iff₀ (by positivity), mul_pow, hE]
  rw [← mul_div_assoc, div_le_one hSpos]
  linarith [hineq]

end GlobalTheory.HSNef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem smallFam_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ (B : HermLB p) (J : Type) (f : J → X.functionField) (w : J → ℝ), SmallFam B f w → SmallFam (B.pull π hπ) (fun j => φ (f j)) w := by
  intro k _ X Y _ _ p q π hπ φ hM B J f w hs
  obtain ⟨β, hβ, hreg, hnorm⟩ := hs
  obtain ⟨hR, -, hF, hV⟩ := GlobalTheory.T.birationalModel_regular_unit_values k X Y p q π hπ φ hM
  refine ⟨fun c => Units.map φ.toMonoidHom (β (c PUnit.unit)), ?_, ?_, ?_⟩
  · intro i j h
    have hi : genericPoint Y ∈ π ⁻¹ᵁ B.B.U (i PUnit.unit) :=
      LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit h.1
    have hj : genericPoint Y ∈ π ⁻¹ᵁ B.B.U (j PUnit.unit) :=
      LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit h.2
    have hX : genericPoint X ∈ B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit) := by
      rw [← hM.gen]; exact ⟨hi, hj⟩
    have eg : ((B.B.pull π).g i j).val = resG Y (fun _ hy => ⟨LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit hy.1, LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit hy.2⟩ : (B.B.pull π).U i ⊓ (B.B.pull π).U j ≤ π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit)))
        (π.app _ (B.B.g (i PUnit.unit) (j PUnit.unit)).val) := by
      dsimp only [LB.pull, LB.LinComb]
      simp only [Fintype.prod_unique, zpow_one, LB.val_res, pullU, Units.coe_map]
      rfl
    show φ (β (i PUnit.unit)) = fnOf _ h ((B.B.pull π).g i j).val * φ (β (j PUnit.unit))
    rw [hβ (i PUnit.unit) (j PUnit.unit) hX, map_mul, hF _ hX ⟨hi, hj⟩, eg]
    exact congrArg (· * φ (β (j PUnit.unit))) (fnOf_resG (X := Y) (U := π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit))) (fun _ hy => ⟨LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit hy.1, LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit hy.2⟩ : (B.B.pull π).U i ⊓ (B.B.pull π).U j ≤ π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit))) h (π.app _ (B.B.g (i PUnit.unit) (j PUnit.unit)).val)).symm
  · intro y c hy j
    show RegAt y (φ (f j) * φ (β (c PUnit.unit)))
    rw [← map_mul]
    exact hR y _ (hreg (π y) (c PUnit.unit) (LB.wchart_le B.B (fun _ : PUnit => π) c PUnit.unit hy) j)
  · intro σ z c hz j
    have hm := mem_of_mem_linComb (m := fun _ => GlobalTheory.Points.PtsOver.map π hπ _ z) (fun _ => rfl) hz
      PUnit.unit
    have hr := hreg (π (under z)) (c PUnit.unit) (mem_ptsIn.1 hm) j
    have e2 : ((B.φ σ).pull π hπ).φ c z = (B.φ σ).φ (c PUnit.unit) (GlobalTheory.Points.PtsOver.map π hπ _ z) :=
      (B.φ σ).pull_φ π hπ c z
    show ‖ratVal (φ (f j) * φ (β (c PUnit.unit))) z‖ * Real.exp (-((B.φ σ).pull π hπ).φ c z / 2) ≤ _
    rw [← map_mul, hV σ z _ hr, e2]
    exact hnorm σ _ (c PUnit.unit) hm j

end GlobalTheory.HSNef
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem GlobalTheory.PairStep.exists_small_ample_through_off : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (x z : X) (ε : ℚ), IsAmpleLB N → ¬ z ⤳ x → 0 < ε → ∃ (b : ℚ) (A : X → ℚ), 0 ≤ b ∧ b ≤ ε ∧ QNum p N b A ∧ Off A x ∧ ¬ Off A z := by
  intro X _ _ p hp N x z ε hN hzx hε
  obtain ⟨l, s, hl, hx, hz⟩ := GlobalTheory.T.exists_ampleSection_nonvanishing_at_not_specializing X N x z hN hzx
  have hs : genericPoint X ∈ nonzeroLocus s :=
    (genericPoint_specializes x).mem_open (nonzeroLocus s).isOpen hx
  obtain ⟨m, hm⟩ := exists_nat_ge ((l : ℚ) / ε)
  have hm0 : 0 < m := by
    have : (0 : ℚ) < (l : ℚ) / ε := div_pos (by exact_mod_cast hl) hε
    exact_mod_cast this.trans_le hm
  obtain ⟨hE, hQ⟩ := GlobalTheory.T.cartierDivOfGlobalSection_pow_numEquiv_multiple X p hp N hN.isLB l m s hs hm0
  refine ⟨(l : ℚ) / m, _, by positivity, ?_, hQ, ?_, ?_⟩
  · have hm' : (0 : ℚ) < m := by exact_mod_cast hm0
    rw [div_le_iff₀ hm']
    rw [div_le_iff₀ hε] at hm
    linarith [mul_comm (m : ℚ) ε]
  · exact (GlobalTheory.T.weilQDivisorAvoidsPoint_cartier_iff_notMem_supp X _ m x hE hm0).2 (notMem_supp_divOfSec.2 hx)
  · rw [GlobalTheory.T.weilQDivisorAvoidsPoint_cartier_iff_notMem_supp X _ m z hE hm0, notMem_supp_divOfSec]
    exact hz
end
