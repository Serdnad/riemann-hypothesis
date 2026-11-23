module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle001
import GroundTheory.GlobalFields.CompletionAtPlace.Integers
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaLiftTrivialOrbitTermsVanish
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite
import GroundTheory.GlobalFields.TateThesis.Bundle001
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder
open GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange UpperTheory.ConvolutionTheory.R2.H

private theorem e_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F)
    (x y : PlacesOver E v) (h : x ≠ y) : x.1.asIdeal.ramificationIdx (𝓞 F) = 1 := by
  have hs := sum_ramificationIdx_mul_inertiaDeg E v
  have hfin : Module.finrank F E = 2 := by
    rw [Module.finrank_eq_card_basis D.b, Fintype.card_fin]
  rw [hfin] at hs
  have hpos : ∀ x : PlacesOver E v, 1 ≤ x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F) := fun x =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have h1 := Finset.sum_le_sum_of_subset (f := fun x : PlacesOver E v => x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F))
    (Finset.subset_univ {x, y})
  rw [Finset.sum_pair h, hs] at h1
  have h2 := hpos x
  have h3 := hpos y
  exact Nat.eq_one_of_mul_eq_one_right (show x.1.asIdeal.ramificationIdx (𝓞 F) * x.1.asIdeal.inertiaDeg (𝓞 F) = 1 by omega)

private theorem map_sg {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : P F) (w w' : P E)
    [hl : w.asIdeal.LiesOver v.asIdeal] [hl' : w'.asIdeal.LiesOver v.asIdeal] (hne : w ≠ w')
    (hu : ∀ u : P E, u.asIdeal.LiesOver v.asIdeal → u = w ∨ u = w') (x : Kv v) :
    adeleMap F E (sg v x) = sg w (completionMap v w x) + sg w' (completionMap v w' x) ∧
      ∀ a b, sg w a * sg w' b = 0 := by
  obtain ⟨-, -, hc, -, -, -, -, hs, -, -⟩ := sgLaws F v
  obtain ⟨-, -, hc₁, -, -, -, -, hs₁, -, -⟩ := sgLaws E w
  obtain ⟨-, -, hc₂, -, -, -, -, hs₂, -, -⟩ := sgLaws E w'
  refine ⟨Prod.ext ?_ (FiniteAdeleRing.ext E fun u => ?_), fun a b => Prod.ext ?_ (FiniteAdeleRing.ext E fun u => ?_)⟩
  · change InfinitePlace.infiniteAdeleRingMap (sg v x).1 = (sg w _).1 + (sg w' _).1
    rw [(hs x).1, (hs₁ _).1, (hs₂ _).1, map_zero, add_zero]
  · change completionMap (below F u) u ((sg v x).2 (below F u)) = (sg w _).2 u + (sg w' _).2 u
    by_cases h : u = w
    · subst h
      have hb : below F u = v := (below_eq_iff _ _).2 hl
      subst hb
      rw [(hs₂ _).2 _ hne, add_zero]
      exact (congrArg _ (hc x)).trans (hc₁ _).symm
    by_cases h' : u = w'
    · subst h'
      have hb : below F u = v := (below_eq_iff _ _).2 hl'
      subst hb
      rw [(hs₁ _).2 _ h, zero_add]
      exact (congrArg _ (hc x)).trans (hc₂ _).symm
    · have hb : below F u ≠ v := fun hb => (hu u ((below_eq_iff _ _).1 hb)).elim h h'
      rw [(hs x).2 _ hb, map_zero, (hs₁ _).2 _ h, (hs₂ _).2 _ h', add_zero]
  · change (sg w a).1 * (sg w' b).1 = 0
    rw [(hs₁ _).1, zero_mul]
  · change (sg w a).2 u * (sg w' b).2 u = 0
    by_cases h : u = w
    · subst h
      rw [(hs₂ _).2 _ hne, mul_zero]
    · rw [(hs₁ _).2 _ h, zero_mul]

theorem UpperTheory.ideleEmbedding_uniformizer_of_split_place_pair :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ) (w w' : H.P E), w ≠ w' → w.under (𝓞 ℚ) = v → w'.under (𝓞 ℚ) = v → H.SplitAt v w → H.SplitAt v w' →
          (∀ w'' : H.P E, w''.under (𝓞 ℚ) = v → w'' = w ∨ w'' = w') →
          ∀ ϖ : (H.Kv v)ˣ, H.IsU ϖ → ∃ (ϖ₁ : (H.Kv w)ˣ) (ϖ₂ : (H.Kv w')ˣ), H.IsU ϖ₁ ∧ H.IsU ϖ₂ ∧
            ideleEmbedding ℚ E (H.idl v ϖ) = H.idl w ϖ₁ * H.idl w' ϖ₂ := by
  intro E _ _ D v w w' hne hw hw' _ _ hall ϖ hϖ
  haveI hl : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw]; rfl⟩
  haveI hl' : w'.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw']; rfl⟩
  have hn : (⟨w, hl⟩ : PlacesOver E v) ≠ ⟨w', hl'⟩ := fun h => hne (congrArg Subtype.val h)
  obtain ⟨-, -, -, hi, -, -, -, -, -, -⟩ := sgLaws ℚ v
  obtain ⟨-, -, -, hi₁, -, -, -, -, -, -⟩ := sgLaws E w
  obtain ⟨-, -, -, hi₂, -, -, -, -, -, -⟩ := sgLaws E w'
  refine ⟨Units.map (completionMap v w : Kv v →* Kv w) ϖ, Units.map (completionMap v w' : Kv v →* Kv w') ϖ, ?_, ?_, Units.ext ?_⟩
  · change Valued.v (completionMap v w (ϖ : Kv v)) = _
    rw [valued_completionMap, e_one D v _ _ hn, pow_one]
    exact hϖ
  · change Valued.v (completionMap v w' (ϖ : Kv v)) = _
    rw [valued_completionMap, e_one D v _ _ hn.symm, pow_one]
    exact hϖ
  · obtain ⟨h1, h2⟩ := map_sg v w w' hne (fun u hu => hall u (HeightOneSpectrum.ext hu.over.symm)) ((ϖ : Kv v) - 1)
    change adeleMap ℚ E ((idl v ϖ : (A ℚ)ˣ) : A ℚ) = _
    rw [Units.val_mul, hi, hi₁, hi₂, map_add (f := _), map_one, h1, map_sub, map_sub, map_one, map_one, add_mul, mul_add, mul_add, h2]
    simp only [one_mul, mul_one, add_zero, Units.coe_map, MonoidHom.coe_coe]
    abel
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.exists_good_character_of_inert_CMDatum :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ) (w : H.P E), H.Gd D.δ v → H.Inert D v w →
          ∃ χ : H.Kv w → ℂ, H.Good χ ∧ ∀ x, ∃ u t, H.sg w x = D.mkE u t ∧ ψ (-t) = χ x := by
  intro E _ _ D v w hG hI
  obtain ⟨e, h1, h2, h3, -⟩ := hI.coord
  obtain ⟨sa, sm, sc, -⟩ := H.sgLaws ℚ v
  obtain ⟨-, tm, tc, -⟩ := H.sgLaws E w
  obtain ⟨ga, gi, gm⟩ := hG.psi
  have hs : ∀ u, -(H.sg v u) = H.sg v (-u) := fun u => by
    rw [← neg_one_mul, sm, map_neg, map_one, neg_one_mul]
  have s0 : H.sg v (0 : H.Kv v) = 0 := by simpa using (sm 0 0).symm
  have h4 : ∀ c u t, e (0, c) * e (u, t) = e (H.cp v (rt D.δ) * (c * t), c * u) := fun c u t => by
    have a1 : ∀ x y, H.sg v (x * y) = H.sg v x * H.sg v y := fun x y => by rw [sm, sc]
    have a2 : ∀ x, H.sg v (H.cp v (rt D.δ) * x) = rt D.δ * H.sg v x := fun x => (sm (rt D.δ) x).symm
    have a3 : (rt D.θ : A E) ^ 2 = AdeleBaseChange.adeleMap ℚ E (rt D.δ) := by
      rw [← map_pow, D.sq]
      exact (AdeleBaseChange.adeleMap_algebraMap _).symm
    have : H.sg w (e (0, c) * e (u, t)) = H.sg w (e (H.cp v (rt D.δ) * (c * t), c * u)) := by
      rw [← tc (e (0, c)), ← tm, h1, h1, h1, s0, a2, a1, a1]
      simp only [Dat.mkE, map_mul, map_zero, ← a3]
      ring
    simpa only [tc] using congrArg (H.cp w) this
  have key : ∀ y : H.Kv v, (∀ c, H.IsInt c → ψ (H.sg v (-(c * y))) = 1) → H.IsInt y := fun y hy => by
    have : Valued.v (-y) ≤ 1 := gm _ fun c hc => by
      have := hy c hc
      rwa [show -(c * y) = c * -y by ring] at this
    rwa [Valuation.map_neg] at this
  refine ⟨fun x => ψ (H.sg v (-(e.symm x).2)), ⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩, fun x => ?_⟩
  · beta_reduce
    rw [map_add (f := _), Prod.snd_add, neg_add]
    exact ga _ _
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have ht : Valued.v t ≤ 1 := (le_max_right _ _).trans ((h2 u t).symm.le.trans hx)
    beta_reduce
    rw [e.symm_apply_apply]
    refine gi _ ?_
    show Valued.v _ ≤ 1
    rwa [Valuation.map_neg]
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have ht : H.IsInt t := key t fun c hc => by
      have := hx (e (c, 0)) ((h2 c 0).le.trans (max_le hc (by simp)))
      beta_reduce at this
      rwa [h3, e.symm_apply_apply] at this
    have hu : H.IsInt u := key u fun c hc => by
      have := hx (e (0, c)) ((h2 0 c).le.trans (max_le (by simp) hc))
      beta_reduce at this
      rwa [h4, e.symm_apply_apply] at this
    exact (h2 u t).le.trans (max_le hu ht)
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    exact ⟨_, _, h1 u t, by beta_reduce; rw [hs, e.symm_apply_apply]⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.differentiable_integral_exp_mul_of_rapid_decay :
    ∀ I : ℝ → ℂ, AEStronglyMeasurable I volume → (∀ n : ℕ, ∃ B : ℝ, ∀ t, ‖I t‖ ≤ B * Real.exp (-((n : ℝ) * |t|))) →
        Differentiable ℂ fun s : ℂ => ∫ t : ℝ, Complex.exp (2 * s * t) * I t := by
  intro I hI hdec s₀
  have hexp : Integrable (fun t : ℝ => Real.exp (-|t|)) := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    refine IntegrableOn.union ?_ ?_
    · refine (integrableOn_exp_Iic (0 : ℝ)).congr_fun (fun t ht => ?_) measurableSet_Iic
      simp [abs_of_nonpos (Set.mem_Iic.mp ht)]
    · refine (exp_neg_integrableOn_Ioi 0 (zero_lt_one (α := ℝ))).congr_fun (fun t ht => ?_)
        measurableSet_Ioi
      simp [abs_of_pos (Set.mem_Ioi.mp ht)]
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (|s₀.re| + 1) + 2)
  obtain ⟨B, hB⟩ := hdec n
  have hB0 : 0 ≤ B := by
    have h := hB 0
    simp only [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
    exact (norm_nonneg _).trans h
  have key : ∀ s : ℂ, s ∈ Metric.ball s₀ 1 → ∀ t : ℝ,
      ‖Complex.exp (2 * s * t)‖ * ‖I t‖ ≤ B * Real.exp (-(2 * |t|)) := by
    intro s hs t
    have hre : |s.re| ≤ |s₀.re| + 1 := by
      have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm (s - s₀)
      have h2 : ‖s - s₀‖ < 1 := by simpa [dist_eq_norm] using hs
      have h3 := abs_sub_abs_le_abs_sub s.re s₀.re
      rw [Complex.sub_re] at h1
      linarith
    have hn1 : ‖Complex.exp (2 * s * t)‖ = Real.exp (2 * s.re * t) := by
      rw [Complex.norm_exp]
      simp
    have ht : 2 * s.re * t ≤ 2 * (|s₀.re| + 1) * |t| := by
      have h1 : s.re * t ≤ |s.re| * |t| := by
        rw [← abs_mul]
        exact le_abs_self _
      have h2 : |s.re| * |t| ≤ (|s₀.re| + 1) * |t| :=
        mul_le_mul_of_nonneg_right hre (abs_nonneg t)
      linarith
    have hnt : (2 * (|s₀.re| + 1) + 2) * |t| ≤ (n : ℝ) * |t| :=
      mul_le_mul_of_nonneg_right hn.le (abs_nonneg t)
    calc ‖Complex.exp (2 * s * t)‖ * ‖I t‖
        ≤ Real.exp (2 * (|s₀.re| + 1) * |t|) * (B * Real.exp (-((n : ℝ) * |t|))) := by
          rw [hn1]
          exact mul_le_mul (Real.exp_le_exp.mpr ht) (hB t) (norm_nonneg _) (Real.exp_pos _).le
      _ = B * Real.exp (2 * (|s₀.re| + 1) * |t| + -((n : ℝ) * |t|)) := by
          rw [Real.exp_add]
          ring
      _ ≤ B * Real.exp (-(2 * |t|)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB0
          linarith
  have hcont : ∀ s : ℂ, Continuous fun t : ℝ => Complex.exp (2 * s * t) := fun s => by
    fun_prop
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun t : ℝ => Complex.exp (2 * s * t) * I t) volume :=
    fun s => (hcont s).aestronglyMeasurable.mul hI
  have hmeas' : AEStronglyMeasurable
      (fun t : ℝ => (2 * (t : ℂ)) * Complex.exp (2 * s₀ * t) * I t) volume := by
    have hc : Continuous fun t : ℝ => (2 * (t : ℂ)) * Complex.exp (2 * s₀ * t) := by
      fun_prop
    exact hc.aestronglyMeasurable.mul hI
  have hF_int : Integrable (fun t : ℝ => Complex.exp (2 * s₀ * t) * I t) volume := by
    refine (hexp.const_mul B).mono' (hmeas s₀) (ae_of_all _ fun t => ?_)
    rw [norm_mul]
    refine (key s₀ (Metric.mem_ball_self one_pos) t).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB0)
    linarith [abs_nonneg t]
  have h_bound : ∀ᵐ t : ℝ ∂volume, ∀ s ∈ Metric.ball s₀ 1,
      ‖(2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t‖ ≤ 2 * B * Real.exp (-|t|) := by
    refine ae_of_all _ fun t s hs => ?_
    have hk := key s hs t
    have hnorm : ‖(2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t‖
        = 2 * |t| * (‖Complex.exp (2 * s * t)‖ * ‖I t‖) := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simp only [Complex.norm_ofNat]
      ring
    have habs : |t| ≤ Real.exp |t| := by
      linarith [Real.add_one_le_exp |t|]
    rw [hnorm]
    calc 2 * |t| * (‖Complex.exp (2 * s * t)‖ * ‖I t‖)
        ≤ 2 * Real.exp |t| * (B * Real.exp (-(2 * |t|))) :=
          mul_le_mul (by linarith) hk (by positivity) (by positivity)
      _ = 2 * B * (Real.exp |t| * Real.exp (-(2 * |t|))) := by ring
      _ = 2 * B * Real.exp (-|t|) := by
          rw [← Real.exp_add]
          congr 2
          ring
  have h_diff : ∀ᵐ t : ℝ ∂volume, ∀ s ∈ Metric.ball s₀ 1,
      HasDerivAt (fun x : ℂ => Complex.exp (2 * x * t) * I t)
        ((2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t) s := by
    refine ae_of_all _ fun t s _ => ?_
    have h1 : HasDerivAt (fun x : ℂ => 2 * x * (t : ℂ)) (2 * (t : ℂ)) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 : ℂ)).mul_const (t : ℂ)
    have h2 := h1.cexp.mul_const (I t)
    rwa [show Complex.exp (2 * s * t) * (2 * (t : ℂ)) * I t
        = (2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t by ring] at h2
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun t : ℝ => 2 * B * Real.exp (-|t|))
    (F := fun (s : ℂ) (t : ℝ) => Complex.exp (2 * s * t) * I t)
    (F' := fun (s : ℂ) (t : ℝ) => (2 * (t : ℂ)) * Complex.exp (2 * s * t) * I t)
    (Metric.ball_mem_nhds s₀ one_pos) (Eventually.of_forall hmeas) hF_int hmeas' h_bound
    (hexp.const_mul (2 * B)) h_diff).2.differentiableAt
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private def UpperTheory.powerSeriesFirstDifferenceSeq (a : ℂ) (f : ℕ → ℂ) : ℕ → ℂ
  | 0 => f 0
  | k + 1 => f (k + 1) - a * f k

private theorem UpperTheory.power_series_mul_linear (a : ℂ) (f : ℕ → ℂ) :
    PowerSeries.mk f * (1 - PowerSeries.C a * PowerSeries.X) =
      PowerSeries.mk (UpperTheory.powerSeriesFirstDifferenceSeq a f) := by
  have h : PowerSeries.mk f * (1 - PowerSeries.C a * PowerSeries.X) =
      PowerSeries.mk f - PowerSeries.C a * (PowerSeries.mk f * PowerSeries.X) := by ring
  rw [h]
  ext k
  cases k with
  | zero => simp [UpperTheory.powerSeriesFirstDifferenceSeq]
  | succ k =>
    rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X]
    simp [UpperTheory.powerSeriesFirstDifferenceSeq]

private theorem UpperTheory.geometric_sum_recurrence (x y : ℂ) (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1 + 1), x ^ i * y ^ (k + 1 - i)) =
      x ^ (k + 1) + y * ∑ i ∈ Finset.range (k + 1), x ^ i * y ^ (k - i) := by
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.succ_sub hi', pow_succ]
  ring

private theorem UpperTheory.product_four_geometric_series (x y x' y' c : ℂ) (S T : ℕ → ℂ)
    (hS0 : S 0 = 1) (hT0 : T 0 = 1)
    (hS : ∀ k, S (k + 1) = x ^ (k + 1) + y * S k)
    (hT : ∀ k, T (k + 1) = x' ^ (k + 1) + y' * T k) :
    (PowerSeries.mk fun k : ℕ => c ^ k * S k * T k) *
          ((1 - PowerSeries.C (x * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (x * y' * c) * PowerSeries.X) *
            (1 - PowerSeries.C (y * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (y * y' * c) * PowerSeries.X)) =
          1 - PowerSeries.C (x * y * x' * y' * c ^ 2) * PowerSeries.X ^ 2 := by
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, UpperTheory.power_series_mul_linear, UpperTheory.power_series_mul_linear,
    UpperTheory.power_series_mul_linear, UpperTheory.power_series_mul_linear]
  have hS2 : ∀ k, S (k + 1 + 1) = (x + y) * S (k + 1) - x * y * S k := fun k => by
    rw [hS (k + 1), hS k]; ring
  have hT2 : ∀ k, T (k + 1 + 1) = (x' + y') * T (k + 1) - x' * y' * T k := fun k => by
    rw [hT (k + 1), hT k]; ring
  ext k
  rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_one,
    PowerSeries.coeff_mk]
  rcases k with _ | _ | _ | _ | k
  · simp [UpperTheory.powerSeriesFirstDifferenceSeq, hS0, hT0]
  · simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]
    norm_num
    ring
  · simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]
    norm_num
    ring
  · simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS, hT, hS0, hT0]
    norm_num
    ring
  · rw [if_neg (by omega), if_neg (by omega)]
    simp only [UpperTheory.powerSeriesFirstDifferenceSeq, hS2, hT2]
    ring

theorem UpperTheory.rankinSelberg_local_generating_series_identity :
    ∀ x y x' y' c : ℂ, (PowerSeries.mk fun k : ℕ => c ^ k * (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i)) * (∑ i ∈ Finset.range (k + 1), (x') ^ i * (y') ^ (k - i))) *
          ((1 - PowerSeries.C (x * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (x * y' * c) * PowerSeries.X) *
            (1 - PowerSeries.C (y * x' * c) * PowerSeries.X) * (1 - PowerSeries.C (y * y' * c) * PowerSeries.X)) =
          1 - PowerSeries.C (x * y * x' * y' * c ^ 2) * PowerSeries.X ^ 2 := by
  intro x y x' y' c
  exact UpperTheory.product_four_geometric_series x y x' y' c
    (fun k => ∑ i ∈ Finset.range (k + 1), x ^ i * y ^ (k - i))
    (fun k => ∑ i ∈ Finset.range (k + 1), x' ^ i * y' ^ (k - i))
    (by simp) (by simp) (UpperTheory.geometric_sum_recurrence x y) (UpperTheory.geometric_sum_recurrence x' y')
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem UpperTheory.geometric_power_series_inverse (x : ℂ) :
    (PowerSeries.mk fun k : ℕ => x ^ k) * (1 - PowerSeries.C x * PowerSeries.X) = 1 := by
  ext n
  rw [mul_sub, mul_one, ← mul_assoc, map_sub]
  cases n with
  | zero => simp
  | succ n =>
    rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
    simp [PowerSeries.coeff_one, pow_succ]

theorem UpperTheory.powerSeries_completeHomogeneous_two_mul_eq_one :
    ∀ x y : ℂ, (PowerSeries.mk fun k : ℕ => (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i))) * ((1 - PowerSeries.C x * PowerSeries.X) * (1 - PowerSeries.C y * PowerSeries.X)) = 1 := by
  intro x y
  have h : (PowerSeries.mk fun k : ℕ => (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i)))
      = (PowerSeries.mk fun k : ℕ => x ^ k) * (PowerSeries.mk fun k : ℕ => y ^ k) := by
    ext n
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp
  rw [h, mul_mul_mul_comm, UpperTheory.geometric_power_series_inverse, UpperTheory.geometric_power_series_inverse, mul_one]
end
