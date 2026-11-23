module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle021
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenTwistVanish.proof (hS : KH.TheoremSStatement) (hG : QuotPartGraded.Statement)
    (hK : GenKoszulStep.Statement) : GenTwistVanish.Statement := by
  intro S _ K _ _ ι _ _ V α hV hα e
  obtain ⟨-, ⟨c₁, hc₁⟩, -⟩ := hS S K ι (MRingOver S ι ⧸ V) (KH.quotPart S V) inferInstance
    inferInstance (hG S K ι V hV)
  obtain ⟨R, hR⟩ := hK S K ι V α hV hα
  set B : ℤ := ∑ k, (|e k| + (R : ℤ) * |α k|) with hB
  refine ⟨(c₁ + B).toNat, ?_⟩

  have key : ∀ j n : ℕ, (c₁ + B).toNat ≤ n → ∀ i : ℕ, 1 ≤ i →
      Subsingleton (KH.cechHc ι (KH.quotPart S V) (e + ((j : ℤ) - R) • α + fun _ => (n : ℤ)) i) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro n hn i hi
      by_cases hj : j < R
      · refine hc₁ _ i hi fun k => ?_
        have h1 : |e k| + (R : ℤ) * |α k| ≤ B :=
          Finset.single_le_sum (f := fun k => |e k| + (R : ℤ) * |α k|)
            (fun k _ => by positivity) (Finset.mem_univ k)
        have h2 : c₁ + B ≤ n := by omega
        have h3 : |((j : ℤ) - R) * α k| ≤ (R : ℤ) * |α k| := by
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          rw [abs_le]
          constructor <;> omega
        have h4 := neg_abs_le (((j : ℤ) - R) * α k)
        have h5 := neg_abs_le (e k)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        linarith
      · rw [not_lt] at hj
        refine hR _ (fun p hp1 hpR i' hi' => ?_) i hi
        have heq : (e + ((j : ℤ) - R) • α + fun _ => (n : ℤ)) - (p : ℤ) • α =
            e + (((j - p : ℕ) : ℤ) - R) • α + fun _ => (n : ℤ) := by
          funext k
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          push_cast [Nat.cast_sub (le_trans hpR hj)]
          ring
        rw [heq]
        exact ih (j - p) (by omega) n hn i' hi'
  intro m n hn
  have h := key (m + R) n hn 1 le_rfl
  have heq : (e + (((m + R : ℕ) : ℤ) - R) • α + fun _ => (n : ℤ)) =
      e + (m : ℤ) • α + fun _ => (n : ℤ) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rwa [heq] at h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem G5.fderiv_fderiv_eq_of_add_const {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ} {y : E}
    (b : ℝ) (h : ∀ᶠ y' in 𝓝 y, f y' = g y' + b) : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [h.eventually_nhds] with y' hy'
  have hfg : f =ᶠ[𝓝 y'] fun x => g x + b := hy'
  rw [hfg.fderiv_eq, fderiv_add_const]

theorem G5.ptsIntegral_eq_of_add_const {e : ℕ} (P : Ideal (MRing ι)) (φ ψ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (h : ∀ j, ∃ b : ℝ, ∀ z ∈ mcPts P, φ j z = ψ j z + b) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ g = ptsIntegral P ψ g := by
  have hs : ∀ Ψ y w, sheetDensity P Ψ φ g y w = sheetDensity P Ψ ψ g y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs with hγ
    · congr 1
      have hH : ∀ j, cxHessian (fun y' => φ j (hγ.choose y')) y = cxHessian (fun y' => ψ j (hγ.choose y')) y := by
        intro j
        obtain ⟨b, hb⟩ := h j
        have hev : ∀ᶠ y' in 𝓝 y, φ j (hγ.choose y') = ψ j (hγ.choose y') + b :=
          hγ.choose_spec.2.mono fun y' hy' => hb _ hy'.2.1
        unfold cxHessian
        rw [G5.fderiv_fderiv_eq_of_add_const b hev]
      simp only [maDensity, hH]
    · rfl
  unfold ptsIntegral ptsIntegralAt
  simp only [hs]

theorem G5.ptsIntegral_const {e : ℕ} (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs <;> ring
  · simp

theorem G5.isSmoothHerm_constLine (c : ℝ) : IsSmoothHerm (constLine (ι := ι) c) := by
  show ContDiffOn ℝ _ (fun _ => Real.exp (-c)) _
  exact contDiffOn_const

theorem G5.log_tensor_constLine (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((A.tensor (constLine c)).h z) = Real.log (A.h z) + -c := by
  show Real.log (A.h z * Real.exp (-c)) = _
  rw [Real.log_mul (A.pos z hz).ne' (Real.exp_pos _).ne', Real.log_exp]

theorem G5.top_tensor_constLine (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (P : Ideal (MRing ι)) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ℝ)
    (hP : IsArithVar P (D + 1)) (hA : IsSmoothHerm A) :
    I P (D + 1) (fun _ => A.tensor (constLine c)) =
      I P (D + 1) (fun _ => A) - ((D + 1 : ℕ) : ℝ) * c * geomDeg P A D := by
  set A' := A.tensor (constLine (ι := ι) c) with hA'def
  have hA' : IsSmoothHerm A' := hA.mul (G5.isSmoothHerm_constLine c)
  let L : ℕ → Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun k j => if (j : ℕ) < k then A' else A
  have hL2 : ∀ k j, L k j = A ∨ L k j = A' := fun k j => by
    by_cases h : (j : ℕ) < k
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  have hLs : ∀ k j, IsSmoothHerm (L k j) := fun k j => (hL2 k j).elim (fun h => h ▸ hA) (fun h => h ▸ hA')

  have hint : ∀ M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (∀ j, M j = A ∨ M j = A') →
      ptsIntegral P (pot M) (fun _ => c) = c * geomDeg P A D := by
    intro M hM
    rw [G5.ptsIntegral_const]
    congr 1
    refine G5.ptsIntegral_eq_of_add_const P _ _ (fun j => ?_) _
    rcases hM j with h | h
    · exact ⟨0, fun z _ => by simp [pot, h]⟩
    · exact ⟨-c, fun z hz => by simp only [pot, h]; exact G5.log_tensor_constLine A c z hz.1⟩
  have step : ∀ k, k ≤ D + 1 → I P (D + 1) (L k) = I P (D + 1) (fun _ => A) - (k : ℝ) * c * geomDeg P A D := by
    intro k
    induction k with
    | zero =>
      intro _
      have : L 0 = fun _ => A := by funext j; simp [L]
      rw [this]; simp
    | succ k ih =>
      intro hk
      have hkD : k < D + 1 := by omega
      set i : Fin (D + 1) := ⟨k, hkD⟩
      set σ := Equiv.swap i (Fin.last D)
      set M : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun j => L (k + 1) (σ (Fin.castSucc j))
      have hne : ∀ j : Fin D, σ (Fin.castSucc j) ≠ i := by
        intro j hj
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at hj
        exact (Fin.castSucc_lt_last j).ne hj
      have hMk : ∀ j : Fin D, L k (σ (Fin.castSucc j)) = M j := by
        intro j
        have h1 : ((σ (Fin.castSucc j) : Fin (D + 1)) : ℕ) ≠ k := fun h => hne j (Fin.ext h)
        simp only [M, L]
        by_cases h2 : ((σ (Fin.castSucc j) : Fin (D + 1)) : ℕ) < k
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
      have hσi : σ (Fin.last D) = i := Equiv.swap_apply_right _ _
      have e1 : L (k + 1) ∘ σ = Fin.snoc M A' := by
        funext x
        refine Fin.lastCases ?_ (fun j => ?_) x
        · simp only [Function.comp_apply, Fin.snoc_last, hσi, L, i]
          exact if_pos (Nat.lt_succ_self k)
        · simp only [Function.comp_apply, Fin.snoc_castSucc, M]
      have e0 : L k ∘ σ = Fin.snoc M A := by
        funext x
        refine Fin.lastCases ?_ (fun j => ?_) x
        · simp only [Function.comp_apply, Fin.snoc_last, hσi, L, i]
          exact if_neg (lt_irrefl k)
        · simp only [Function.comp_apply, Fin.snoc_castSucc]
          exact hMk j
      have hM : ∀ j, M j = A ∨ M j = A' := fun j => hL2 _ _
      have hMs : ∀ j, IsSmoothHerm (M j) := fun j => hLs _ _
      have hmc := metricChange K ι I hI P D M A (fun _ => c) (fun _ _ _ => rfl) hP hMs hA contDiffOn_const
      have s1 := hI.1 P (D + 1) (L (k + 1)) σ hP (hLs _)
      have s0 := hI.1 P (D + 1) (L k) σ hP (hLs _)
      rw [e1] at s1
      rw [e0] at s0
      have hsnoc : I P (D + 1) (Fin.snoc M A') =
          I P (D + 1) (Fin.snoc M A) - ptsIntegral P (pot M) (fun _ => c) := hmc
      rw [← s1, hsnoc, s0, ih (by omega), hint M hM]
      push_cast
      ring
  have hall : L (D + 1) = fun _ => A' := by
    funext j
    exact if_pos j.isLt
  have := step (D + 1) le_rfl
  rw [hall] at this
  rw [this]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ComponentResBridge

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (Res logH)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
  (R : Res ι W e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

set_option linter.unusedSectionVars false

theorem isMultiHomogIdeal_of_mem_minimalPrimes {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    IsMultiHomogIdeal W := by
  have hPCh : IsMultiHomogIdeal (P.map (MvPolynomial.map (Int.castRingHom ℂ))) := by
    obtain ⟨T, hT, hPT⟩ := hP.2.1.2.1
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' T, ?_, by rw [hPT, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hT f hf
    exact ⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩
  exact (GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff W).mp
    (GroundTheory.Heights₂.Heights.NumbersDVR.MinimalPrimeMultiHomog.proof ℂ K ι _ W
      ((GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff _).mpr hPCh) hW)

end ComponentResBridge

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M ComponentResBridge

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end
