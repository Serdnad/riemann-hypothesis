module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle040
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelTorsionBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle057
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.RelabelTransport
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle007
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle011
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def curveChartMono (c : ∀ k, ι k) (d : K → ℕ) : MRing ι :=
  ∏ k, X ⟨k, c k⟩ ^ d k

def chartUnit (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (τ : ℕ) : Ω :=
  ∏ k, y ⟨k, c k⟩ ^ ((τ : ℤ) * a k)

def chartIndexLog (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (τ : ℕ) : ℝ :=
  Real.log (genIndex (chartLat y a τ) (curveMul y (chartUnit y c a τ)))

def chartRadius (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k) (t : (Σ k, ι k) → ℂ) : ℝ :=
  A.h t / ∏ k, ‖t ⟨k, c k⟩‖ ^ A.a k

end Objects

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


open Classical in
theorem sum_single_chart_apply (k' : K) (j : ι k') (b : ℕ) (k : K) :
    ∑ i, (Finsupp.single (⟨k', j⟩ : Σ k, ι k) b) ⟨k, i⟩ = if k' = k then b else 0 := by
  classical
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro he
    exact h (Sigma.mk.inj_iff.mp he).1

theorem isMultiHomog_curveChartMono (c : ∀ k, ι k) (d : K → ℕ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (curveChartMono c d) d := by
  classical
  have h : curveChartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ) := by
    rw [curveChartMono, monomial_sum_one]
    exact Finset.prod_congr rfl fun k _ => X_pow_eq_monomial
  have hd : (fun k => ∑ i, (∑ k', Finsupp.single (⟨k', c k'⟩ : Σ k, ι k) (d k')) ⟨k, i⟩) = d := by
    funext k
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    simp only [sum_single_chart_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h]
  have hm := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_monomial (ι := ι)
    (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ)
  rw [hd] at hm
  exact hm


omit [∀ k, Fintype (ι k)] in
theorem aeval_curveChartMono (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (curveChartMono c d) = chartUnit y c (fun k => (d k : ℤ)) 1 := by
  simp [curveChartMono, chartUnit, map_prod]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ne_zero_of_X_notMem {y : (Σ k, ι k) → Ω} {p : Σ k, ι k}
    (hp : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  intro h0
  apply hp
  show X p ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]


omit [∀ k, Fintype (ι k)] in
theorem curveChartMono_notMem {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℕ) :
    curveChartMono c d ∉ mCoordIdeal y := by
  intro h
  have h' : mConeMap y (curveChartMono c d) = 0 := h
  rw [curveChartMono, map_prod] at h'
  obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h'
  rw [map_pow, mConeMap, aeval_X] at hk
  exact mul_ne_zero (C_ne_zero.mpr (hc k)) (X_ne_zero _) (pow_eq_zero_iff'.mp hk).1

theorem exists_chart {y : (Σ k, ι k) → Ω} {n : ℕ} (hP : IsArithVar (mCoordIdeal y) n) :
    ∃ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ mCoordIdeal y) ∧ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using hP.2.1.2.2
  exact ⟨c, hc, fun k => ne_zero_of_X_notMem (hc k)⟩

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel

theorem RelSectionsLarge.full : RelSectionsLarge.Statement :=
  RelSectionsLarge.proof RelChartPoly.proof (RelOneStep.proof RelChartPoly.proof RelTorsionBound.proof)

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace NefCountAlongMultiples

section Transport

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem count_shift_le {y : (Σ k, ι k) → Ω} {A N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {e : Ω} {C : ℝ} {p q n : ℕ}
    (he0 : e ≠ 0)
    (hmap : ∀ s : Ω, s ∈ chartLat y N.a n → s * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧
      ∀ c : ℝ, IsBoundedH (mCoordIdeal y) y N n c s →
        IsBoundedH (mCoordIdeal y) y A (q * n) (c * Real.exp (((p * n : ℕ) : ℝ) * C)) (s * e ^ (p * n)))
    (hfin : {s : chartLat y A.a (q * n) | IsSmallH (mCoordIdeal y) y A (q * n) (s : Ω)}.Finite) :
    smallSectionCount (IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)))
        (chartLat y (HermLine.constShift N ((p : ℝ) * C)).a) n ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (q * n) := by
  have hc : Real.exp (-((p : ℝ) * C)) ^ n * Real.exp (((p * n : ℕ) : ℝ) * C) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_zero using 2
    push_cast
    ring
  have hsm : ∀ s : {s : chartLat y (HermLine.constShift N ((p : ℝ) * C)).a n //
      IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n (s : Ω)},
      (s.1 : Ω) * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧
        IsSmallH (mCoordIdeal y) y A (q * n) ((s.1 : Ω) * e ^ (p * n)) := by
    rintro ⟨⟨x, hx⟩, hxs⟩
    have hxs' : IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n x := hxs
    rw [constShift_a] at hx
    show x * e ^ (p * n) ∈ chartLat y A.a (q * n) ∧ IsSmallH (mCoordIdeal y) y A (q * n) (x * e ^ (p * n))
    obtain ⟨hm, hb⟩ := hmap x hx
    refine ⟨hm, fun dg dh g h z hg hh hdeg heq hz => ?_⟩
    have hB : IsBoundedH (mCoordIdeal y) y N n (Real.exp (-((p : ℝ) * C)) ^ n) x := by
      intro dg' dh' g' h' z' hg' hh' hdeg' heq' hz'
      have := hxs' dg' dh' g' h' z' hg' hh' (by rw [constShift_a]; exact hdeg') heq' hz'
      rw [constShift_h, mul_pow] at this
      exact this.trans (le_of_eq (by ring))
    have := hb _ hB dg dh g h z hg hh hdeg heq hz
    rwa [hc, one_mul] at this
  have : Finite {s : chartLat y A.a (q * n) // IsSmallH (mCoordIdeal y) y A (q * n) (s : Ω)} :=
    hfin.to_subtype
  have hcard : Nat.card {s : chartLat y (HermLine.constShift N ((p : ℝ) * C)).a n //
        IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n (s : Ω)} ≤
      Nat.card {s : chartLat y A.a (q * n) // IsSmallH (mCoordIdeal y) y A (q * n) (s : Ω)} :=
    Nat.card_le_card_of_injective (fun s => ⟨⟨(s.1 : Ω) * e ^ (p * n), (hsm s).1⟩, (hsm s).2⟩) fun s s' h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext (mul_right_cancel₀ (pow_ne_zero _ he0) h))
  unfold smallSectionCount
  rcases Nat.eq_zero_or_pos (Nat.card {s : chartLat y (HermLine.constShift N ((p : ℝ) * C)).a n //
      IsSmallH (mCoordIdeal y) y (HermLine.constShift N ((p : ℝ) * C)) n (s : Ω)}) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

end Transport

theorem num_bound {T ε I G g C q : ℝ} {D : ℕ} (hε : 0 < ε) (hq : 0 < q) (hC : 0 ≤ C)
    (hI : |I / q ^ (D + 1) - T| < ε / 4) (hG : |G / q ^ D - g| < ε / 4)
    (hqC : ((D : ℝ) + 1) * C * (g + ε / 4) < q * (ε / 4)) :
    (T - ε) * q ^ (D + 1) + ε / 4 * q ^ (D + 1) ≤ I - ((D : ℝ) + 1) * (((1 : ℕ) : ℝ) * C) * G := by
  have hQ : 0 < q ^ (D + 1) := by positivity
  have hQD : 0 < q ^ D := by positivity
  rw [abs_sub_lt_iff] at hI hG
  have h1 : (T - ε / 4) * q ^ (D + 1) < I := (lt_div_iff₀ hQ).1 (by linarith [hI.2])
  have h2 : G < (g + ε / 4) * q ^ D := (div_lt_iff₀ hQD).1 (by linarith [hG.1])
  have h3 : ((D : ℝ) + 1) * (((1 : ℕ) : ℝ) * C) * G ≤ ((D : ℝ) + 1) * C * ((g + ε / 4) * q ^ D) := by
    rw [Nat.cast_one, one_mul]
    exact mul_le_mul_of_nonneg_left h2.le (by positivity)
  have h4 : ((D : ℝ) + 1) * C * ((g + ε / 4) * q ^ D) ≤ ε / 4 * q ^ (D + 1) :=
    calc ((D : ℝ) + 1) * C * ((g + ε / 4) * q ^ D) = (((D : ℝ) + 1) * C * (g + ε / 4)) * q ^ D := by ring
      _ ≤ (q * (ε / 4)) * q ^ D := (mul_lt_mul_of_pos_right hqC hQD).le
      _ = ε / 4 * q ^ (D + 1) := by ring
  nlinarith [mul_pos hε hQ]

theorem le_arithmeticVolume_of_alongMultiples {Ω : Type} [Field Ω] {Pr : ℕ → Ω → Prop} {La : ℕ → AddSubgroup Ω} {D : ℕ}
    {T Cp : ℝ} (hC : ∀ τ, smallSectionCount Pr La τ ≤ Cp * ((τ : ℝ) + 1) ^ (D + 1))
    (h : ∀ ε : ℝ, 0 < ε → ∃ a : ℕ, 1 ≤ a ∧ ∀ᶠ k : ℕ in atTop,
      (T - ε) * (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤ smallSectionCount Pr La (a * k)) :
    T ≤ arVolP Pr La 1 D := by
  obtain ⟨B, hB⟩ := NormCountBounded.norm_count_bounded D hC
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun k : ℕ => smallSectionCount Pr La (1 * k) /
      (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) := by
    refine ⟨B, ?_⟩
    simpa using hB
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, ha, hev⟩ := h ε hε
  have hfreq : ∃ᶠ k : ℕ in atTop, T - ε ≤ smallSectionCount Pr La (1 * k) /
      (((1 * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
    rw [frequently_atTop]
    intro N
    obtain ⟨k, hk⟩ := (hev.and (eventually_ge_atTop (N + 1))).exists
    refine ⟨a * k, le_trans (by omega) (Nat.le_mul_of_pos_left k ha), ?_⟩
    have hak : 0 < a * k := Nat.mul_pos ha (by omega)
    have hpos : (0 : ℝ) < ((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) :=
      div_pos (pow_pos (by exact_mod_cast hak) _) (by exact_mod_cast Nat.factorial_pos _)
    rw [one_mul, le_div_iff₀ hpos]
    exact hk.1
  have := le_limsup_of_frequently_le hfreq hbdd
  unfold arVolP
  linarith

end NefCountAlongMultiples

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj mcPts segre pot PBlk oneLine
  isSmoothHerm_oneLine)

def PtsPosPartLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (z : (Σ k, ι k) → ℂ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsGoodProj P Ψ' → (∀ j, IsSmoothHerm (L j)) →
    Measurable g → (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z' p) = g z') →
    z ∈ mcPts P → IsSimpleSheetPt P Ψ ((Ψ (segre z) 0)⁻¹ • segre z) →
    IsSimpleSheetPt P Ψ' ((Ψ' (segre z) 0)⁻¹ • segre z) →
      ∃ W : Set ((Σ k, ι k) → ℂ), IsOpen W ∧ z ∈ W ∧
        (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ W ↔ z' ∈ W)) ∧
        ∀ E : Set ((Σ k, ι k) → ℂ), MeasurableSet E →
          (∀ (c : K → ℂ) (z' : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → ((fun p => c p.1 * z' p) ∈ E ↔ z' ∈ E)) →
          E ⊆ W →
            ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) (E.indicator g) y) =
              ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ' (pot L) (E.indicator g) y)

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w v' w'

theorem SymmRelabel.proof : SymmRelabel.Statement.{u, v, w, v', w'} := by
  intro F _ K _ ι _ K' _ ι' _ e h hS I hI V n L σ hV
  have key := hS _ (Relabel.isFieldIntersection_pull e h hI) (V.map (Relabel.ringEquiv F e h)) n
    (fun j => L j ∘ e.symm) σ ((Relabel.isProjVarF_map_iff e h V n).2 hV)
  have hL : ∀ L₀ : Fin n → K → ℤ, (fun j => (fun j => L₀ j ∘ e.symm) j ∘ e) = L₀ := fun L₀ => by
    funext j k
    simp
  simp only [Relabel.pullFamily, Relabel.comap_map] at key
  have h1 := hL (L ∘ σ)
  have h2 := hL L
  simp only [Function.comp_apply] at h1 h2 key
  rw [h1, h2] at key
  exact key

theorem SymmStatement.full {K : Type v} [Fintype K] (F : Type u) [Field F] (ι : K → Type w)
    [∀ k, Fintype (ι k)] : SymmStatement F ι :=
  SymmStatement.of_found SymmRelabel.proof F ι

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj IsSheet ptsIntegral
  ptsIntegralAt sheetDensity fibre maDensity mixedDisc cxHessian pot segre mcPts goodProjExists)

theorem maDensity_eq_zero_of_eventuallyEq_zero {D : ℕ} (φ : Fin (D + 1) → (Fin (D + 1) → ℂ) → ℝ)
    (y : Fin (D + 1) → ℂ) (h : φ 0 =ᶠ[𝓝 y] 0) : maDensity φ y = 0 := by
  have hH : fderiv ℝ (fderiv ℝ (φ 0)) y = 0 := by
    rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq]
    simp
  have hC : cxHessian (φ 0) y = 0 := by
    ext a b
    simp [cxHessian, hH]
  have hU : (fun k => cxHessian (φ k) y) =
      Function.update (fun k => cxHessian (φ k) y) 0 ((0 : ℂ) • (0 : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ)) := by
    funext k
    by_cases hk : k = 0
    · subst hk
      simp [hC]
    · simp [Function.update_of_ne hk]
  have hM : mixedDisc (fun k => cxHessian (φ k) y) = 0 := by
    have hdef : mixedDisc (fun k => cxHessian (φ k) y) = ReciprocityTheory.AnForm.mdisc (fun k => cxHessian (φ k) y) :=
      rfl
    rw [hdef, hU, ReciprocityTheory.AnForm.A.mdisc_update_smul, zero_mul]
  simp [maDensity, hM]

theorem SegreChartIntegral.proof (hGood : SegreCoordGoodProj.Statement)
    (hIndep : PtsIntegralProjIndep.Statement) (hChart : PtsIntegralSegreChartProj.Statement) :
    SegreChartIntegral.Statement := by
  classical
  intro K _ _ ι _ P e m σ i L g δ G Φ hP hL hg hδ hsupp hgerm
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1 + 1) → ℂ), IsGoodProj P Ψ :=
    goodProjExists K ι P (e + 1) hP
  have hpts : ptsIntegral P (pot L) g = ptsIntegralAt P hex.choose (pot L) g := by
    unfold ptsIntegral
    rw [dite_eq_left hex]
  rw [hpts]
  by_cases hne : ∃ z ∈ mcPts P, segre z i ≠ 0
  · obtain ⟨Ψ, hΨ, hΨ0⟩ := hGood K ι P (e + 1) i hP hne
    rw [hIndep K ι P (e + 1) _ Ψ L g hP hex.choose_spec hΨ hL hg]
    exact hChart K ι P e m σ i L g Ψ G Φ hP hL hg hΨ hΨ0 hgerm
  · push Not at hne

    have hset : segreChartSet P σ i = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨z, hz, hzi, -⟩
      rw [hne z hz] at hzi
      exact zero_ne_one hzi
    have hcomp : segreChartComponents P σ i = ∅ := by
      ext J
      simp only [mem_segreChartComponents, Finset.notMem_empty, iff_false]
      intro hJ
      have htop : segreChartIdeal P σ i = ⊤ := by
        rw [segreChartIdeal, hset]
        exact MvPolynomial.vanishingIdeal_empty
      rw [htop] at hJ
      exact hJ.1.1.ne_top (top_le_iff.1 hJ.1.2)
    rw [hcomp, Finset.sum_empty]

    have hin : ∀ z ∈ mcPts P, ‖segre z i‖ < δ * ‖segre z‖ := by
      intro z hz
      rw [hne z hz, norm_zero]
      choose j hj using hz.1
      have hj' : segre z j ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hj k
      exact mul_pos hδ (norm_pos_iff.2 fun h0 => hj' (congrFun h0 j))
    have hterm : ∀ y w, sheetDensity P hex.choose (pot L) g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · have hs : IsSheet P hex.choose y w hγ.choose := hγ.choose_spec
        rcases hsupp with hg0 | hp0
        · rw [hg0 _ (hin _ hs.2.self_of_nhds.2.1), zero_mul]
        · rw [maDensity_eq_zero_of_eventuallyEq_zero _ _ ?_, mul_zero]
          filter_upwards [hs.2] with y' hy'
          exact hp0 _ (hin _ hy'.2.1)
      · rfl
    unfold ptsIntegralAt
    simp [hterm]

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj pot PBlk oneLine)

def PtsPosDensMeasurable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
      AEMeasurable (ptsPosDens P Ψ (pot L) g)

end GroundTheory.Heights₂.Heights
end
end
