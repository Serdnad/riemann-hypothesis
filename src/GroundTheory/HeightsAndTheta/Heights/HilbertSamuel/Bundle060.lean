module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle032
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle054
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem nefOnF_mono {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {I : IFamily F ι} {V Q : Ideal (MRingOver F ι)} {α : K → ℤ} (hN : KH.NefOnF I V α) (hVQ : V ≤ Q) :
    KH.NefOnF I Q α :=
  fun W hW hQW => hN W hW (hVQ.trans hQW)

theorem ampleV_of_nsmul {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {V : Ideal (MRingOver S ι)} {N : K → ℤ} {q : ℕ} (hq : 1 ≤ q)
    (h : KH.AmpleV S V (q • N)) : KH.AmpleV S V N := by
  obtain ⟨q₂, hq₂, hgen, hvan⟩ := h
  refine ⟨q₂ * q, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, fun e => ?_⟩
  · rwa [mul_smul]
  · obtain ⟨c₁, hc⟩ := hvan e
    refine ⟨c₁, fun c hc' => ?_⟩
    have := hc c hc'
    rwa [smul_smul, mul_assoc] at this

theorem KleimanScheme.proof (hVar : KleimanVarietyH1Generation.Statement) (hDev : H1GenerationDevissage.Statement)
    (hGen : GenerationOfH1GenAmple.Statement) (hAG : AmpleOfGenTwist.Statement) : KleimanScheme.Statement := by
  intro F _ K _ _ ι _ _ I V α b a hI hV hN hb ha

  have hamp : H1GenAmple F V (b • α + fun _ => (a : ℤ)) :=
    hDev F K ι V _ inferInstance fun P hP hVP => hVar F K ι I P α b a hI hP (nefOnF_mono hN hVP) hb ha

  obtain ⟨c₁, hc⟩ := hGen F K ι V _ hV hamp (fun _ => -1)
  have hg := hc (c₁ + 1) (Nat.le_succ c₁)

  have h := hAG F K ι V _ 1 1 hV hg le_rfl
  have e : ((1 : ℕ) : ℤ) • ((fun _ => (-1 : ℤ)) + (c₁ + 1) • (b • α + fun _ => (a : ℤ))) +
      (fun _ => ((1 : ℕ) : ℤ)) = (c₁ + 1) • (b • α + fun _ => (a : ℤ)) := by
    funext k
    simp only [Nat.cast_one, one_smul, Pi.add_apply]
    ring
  rw [e] at h
  exact ampleV_of_nsmul (Nat.le_add_left 1 c₁) h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

namespace ArithmeticVolumeDegreeZero

theorem arithmeticVolume_nonneg {Ω : Type*} [CommRing Ω] (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (a D : ℕ) :
    0 ≤ arVolP P La a D := by
  unfold arVolP
  have hu : ∀ k : ℕ, 0 ≤ smallSectionCount P La (a * k) / (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) :=
    fun k => div_nonneg (Real.log_natCast_nonneg _) (by positivity)
  by_cases hb : IsBoundedUnder (· ≤ ·) atTop
      (fun k : ℕ => smallSectionCount P La (a * k) / (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)))
  · exact le_limsup_of_frequently_le (Frequently.of_forall hu) hb
  · rw [Real.limsup_of_not_isBoundedUnder hb]

theorem charZero_of_horizontal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (h : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (MvPolynomial.C (n : ℤ) : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y (MvPolynomial.C (n : ℤ)) = 0
    rw [mConeMap, MvPolynomial.aeval_C, eq_intCast, Int.cast_natCast,
      ← map_natCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  have h' : (n : ℤ) ∈ (mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* MRing ι) := hmem
  rw [h] at h'
  exact_mod_cast (Submodule.mem_bot _).mp h'

theorem coeff_le_of_eval_le_mul {D : ℕ} (p r : Polynomial ℝ) {C : ℝ} (hC : 0 ≤ C) (hp : p.natDegree ≤ D + 1)
    (hr : r.natDegree ≤ D) (hrD : r.coeff D ≤ 0)
    (h : ∀ q : ℕ, 1 ≤ q → p.eval (q : ℝ) ≤ C * ((q : ℝ) + 1) * r.eval (q : ℝ)) : p.coeff (D + 1) ≤ 0 := by
  by_contra hpos
  rw [not_le] at hpos
  set g : Polynomial ℝ := p - Polynomial.C C * ((Polynomial.X + 1) * r) with hg
  have hr1 : r.coeff (D + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hgc : g.coeff (D + 1) = p.coeff (D + 1) - C * r.coeff D := by
    rw [hg, Polynomial.coeff_sub, Polynomial.coeff_C_mul, add_mul, one_mul, Polynomial.coeff_add,
      Polynomial.coeff_X_mul, hr1, add_zero]
  have hgpos : 0 < g.coeff (D + 1) := by
    rw [hgc]; nlinarith
  have hgdeg : g.natDegree ≤ D + 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le hp ?_)
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_mul_le).trans ?_
    have : (Polynomial.X + 1 : Polynomial ℝ).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le Polynomial.natDegree_X_le ?_)
      simp
    omega
  have hgnat : g.natDegree = D + 1 :=
    le_antisymm hgdeg (Polynomial.le_natDegree_of_ne_zero hgpos.ne')
  have hlead : 0 ≤ g.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hgnat]; exact hgpos.le
  have hdeg : 0 < g.degree := by
    rw [Polynomial.degree_eq_natDegree (fun h0 => by simp [h0] at hgpos), hgnat]
    exact_mod_cast Nat.succ_pos D
  have ht := (g.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlead).comp tendsto_natCast_atTop_atTop
  obtain ⟨q, hq1, hq⟩ := ((eventually_ge_atTop 1).and (ht.eventually (eventually_gt_atTop 0))).exists
  have hev : g.eval (q : ℝ) = p.eval (q : ℝ) - C * ((q : ℝ) + 1) * r.eval (q : ℝ) := by
    simp only [hg, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one]
    ring
  have := h q hq1
  simp only [Function.comp_apply] at hq
  linarith

end ArithmeticVolumeDegreeZero

theorem ArithmeticVolumeDegreeZero.proof (hB : G6.StatementB) (hN : ShiftNefBig.Statement) (hV : ShiftVolumeBound.Statement)
    (hI : ShiftIntersectionPolynomial.Statement) (hG : ShiftDegreePolynomial.Statement) :
    ArithmeticVolumeDegreeZero.Statement := by
  intro K _ ι _ Ω _ y D A P0 II hD hII har hb hP0 hs hnef hc hdeg
  have : CharZero Ω := ArithmeticVolumeDegreeZero.charZero_of_horizontal y har.2.2.1
  refine le_trans ?_ (ArithmeticVolumeDegreeZero.arithmeticVolume_nonneg _ _ _ _)
  obtain ⟨C, hC0, hC⟩ := hV K ι Ω y D A P0 hD har hb hP0 hs hnef hc
  obtain ⟨p, hpdeg, hpc, hp⟩ := hI K ι II (mCoordIdeal y) (D + 1) A (fsH ι) hII har hs.1
    (GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1)
  obtain ⟨r, hrdeg, hrc, hr⟩ := hG K ι (mCoordIdeal y) D A.a ((1 : ℤ) • (fsH ι).a) har
  have hbound : ∀ q : ℕ, 1 ≤ q → p.eval (q : ℝ) ≤ C * ((q : ℝ) + 1) * r.eval (q : ℝ) := by
    intro q hq
    rw [← hp q, ← hr q]
    exact (hB K ι Ω y D _ P0 II hD hII har hb (hN K ι Ω y D A P0 hD har hb hP0 hs hnef hc q hq)).trans (hC q hq)
  rw [← hpc]
  exact ArithmeticVolumeDegreeZero.coeff_le_of_eval_le_mul p r hC0 hpdeg hrdeg (by rw [hrc]; exact_mod_cast hdeg) hbound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def BlockResolutionImageSup.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MRingOver ℂ ι, IsMultiHomog f (blockDeg d.k₀ n) →
      ∀ x : d.R.X,
        ‖eval (blockPt d x) f‖ / d.A.h (blockPt d x) ^ n ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2NormComplex d n f

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockResolutionMixedIntegral.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), A'.a = ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg d.k₀ → IsSmoothHerm A' →
    ∑ i ∈ Finset.range (D + 1),
        ptsIntegral (mCoordIdeal d.y) (blockMixPot d.A A' D i) (fun z => Real.log (A'.h z / d.A.h z)) =
      ((D : ℝ) + 1) * blockMetricInt d A'

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartLatQCech.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (b : K → ℤ),
    IsArithVar (mCoordIdeal y) d →
    Nonempty (chartLatQ y b 1 ≃ₗ[ℚ]
      KH.cechHc ι (KH.quotPart ℚ ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))) b 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def DiagonalSectionDifference.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) →
    ∃ C : ℝ, ∀ᶠ j : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((j : ℤ) • (1 : K → ℤ)) 1) : ℝ) ≤
        (Module.finrank ℚ (chartLatQ y ((j : ℤ) • (1 : K → ℤ) - 1) 1) : ℝ) + C * (j : ℝ) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedNefGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    NefOnGenericDeg (mCoordIdeal y) a

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def chartDivSec {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (b : K → ℤ) : Submodule ℚ (chartLatQ y b 1) :=
  (Submodule.map (LinearMap.mulLeft ℚ (∏ k, y ⟨k, c k⟩)) (chartLatQ y (b - 1) 1)).comap
    (chartLatQ y b 1).subtype

def HyperplaneQuotientBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (c : ∀ k, ι k),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1 ⧸ chartDivSec y c ((n : ℤ) • a)) : ℝ) ≤
        C * (n : ℝ) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def HyperplaneRegularSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℕ),
    (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∃ σ : Ω, σ ≠ 0 ∧ σ ∈ chartLatQ y (fun k => (e k : ℤ)) 1 ∧
      ∀ (b : K → ℤ) (s : Ω), s ∈ chartLatQ y b 1 →
        σ * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b + (fun k => (e k : ℤ)) - 1) 1 →
        s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def NefPlusAmpleDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (a : K → ℤ),
    IsArithVar P (D + 1) → NefOnGenericDeg P a →
    ∀ q : ℕ, 0 < genDeg P D ((q : ℤ) • a + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionsDimZero.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ),
    IsArithVar (mCoordIdeal y) 1 →
      (Module.finrank ℚ (chartLatQ y a n) : ℤ) = genDeg (mCoordIdeal y) 0 a

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def ShiftSectionBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (m : ℕ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) ≤
          (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1) : ℝ) ∧
        (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1) : ℝ) ≤
          (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) + C * (n : ℝ) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
