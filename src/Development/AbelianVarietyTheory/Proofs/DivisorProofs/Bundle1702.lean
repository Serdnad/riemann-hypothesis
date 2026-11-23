module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1279
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.mem_smallSectionBall_of_mul_pow_section : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (f : X.functionField), f ∈ P.H N 0 → f * s ^ m ∈ P.Bl N m 2 → f ∈ P.Bl N 0 (2 * Real.exp (δ * N + C * m)) := by
  first | exact @GlobalTheory.VolBr.MpDiv.mem_Bl_of_mul_pow | exact GlobalTheory.VolBr.MpDiv.mem_Bl_of_mul_pow | (intros; apply GlobalTheory.VolBr.MpDiv.mem_Bl_of_mul_pow <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem lc_two_le_lc_one_add (hHS : GlobalTheory.Published.ArithHilbertSamuel) (hA : GlobalTheory.Published.ArCalc) (k : Type) [CommRing k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsArithVar p D) (P : Pair p) (b : ℕ)
    (s t : X.functionField) (hG : P.Good D b s t) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      P.lc 0 (b * (n * m : ℕ) + m) 2 ≤ P.lc 0 (b * (n * m : ℕ)) 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  obtain ⟨h, hh⟩ := (hA.1 k X p D hX).1 P.A
  have hα : P.A.IsSelfInter (h (genericPoint X)) := ⟨h, hh, rfl⟩
  have hnef := GlobalTheory.T.hermitianLineBundle_isNef_shift_of_nonneg k X p D hX P.A 0 le_rfl hG.nef
  have hrep : P.Rep 0 1 P.A := (GlobalTheory.T.represents_base_bundles_and_trivial k X p P).2.1
  have key := GlobalTheory.eventually_le_of_poly_asymptotics (D + 1) b
    (fun η j => P.lc 0 (j : ℤ) (Real.exp (η * j))) (fun j => P.lc 0 (j : ℤ) 2)
    (h (genericPoint X) / (D + 1).factorial) ((D + 1) * gdeg P.A D / (D + 1).factorial) (Nat.succ_pos D) hG.pos
    (fun η hη => by
      have := GlobalTheory.T.arith_hilbertSamuel_log_ball_count_tendsto hHS hA k X p D hX P 0 1 P.A (h (genericPoint X)) 0 hrep hα hnef η hη
      simpa only [mul_zero, mul_one] using this)
    (fun η hη => by
      have h1 : ∀ᶠ j : ℕ in atTop, Real.log 2 ≤ η * j :=
        (tendsto_natCast_atTop_atTop.const_mul_atTop hη).eventually_ge_atTop _
      filter_upwards [h1] with j hj
      have h2 : (2 : ℝ) ≤ Real.exp (η * j) := by
        calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ ≤ _ := Real.exp_le_exp.2 hj
      have hsub : P.Bl 0 (j : ℤ) 2 ⊆ P.Bl 0 (j : ℤ) (Real.exp (η * j)) :=
        fun f hf => ⟨hf.1, fun σ y => (hf.2 σ y).trans h2⟩
      have hfin := GlobalTheory.T.hermLineBundlePair_balls_finite hHS k X p D hX P b s t hG 0 (j : ℤ) (Real.exp (η * j)) hA
      have hle := Set.ncard_le_ncard hsub hfin
      simp only [Pair.lc]
      rcases Nat.eq_zero_or_pos (P.Bl 0 (j : ℤ) 2).ncard with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg _
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hle))
    ε hε
  filter_upwards [key] with n hn
  filter_upwards [hn] with m hm
  have e1 : (((b * n + 1) * m : ℕ) : ℤ) = (b : ℤ) * ((n * m : ℕ) : ℤ) + (m : ℤ) := by push_cast; ring
  have e2 : (((b * n * m : ℕ)) : ℤ) = (b : ℤ) * ((n * m : ℕ) : ℤ) := by push_cast; ring
  simp only [e1, e2, zero_mul, Real.exp_zero] at hm
  exact hm

end GlobalTheory.VolBr
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.ampleArithHilbertSamuel_largeRadius_pair : AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b a' b' : ℤ) (M : HermLB p) (α : ℝ), P.Rep a b M → IsAmpleLB M.B → M.SemiPos D → M.IsSelfInter α → ∃ t₀ : ℝ, ∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => P.lc (m * a + a') (m * b + b') (Real.exp (t * m)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α / (D + 1).factorial + (((D : ℝ) + 1) * gdeg M D / (D + 1).factorial) * t)) := by
  first | exact @GlobalTheory.HSNef.ampleHS_pair | exact GlobalTheory.HSNef.ampleHS_pair | (intros; apply GlobalTheory.HSNef.ampleHS_pair <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.generatingPairSections_norm_bounds : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (c : ℕ), GenAt P c → ∃ (n : ℕ) (v : Fin n → X.functionField) (ρ : ℝ), 0 < ρ ∧ (∀ i, v i ∈ P.Bl 0 c ρ⁻¹) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), ∃ i, ρ ≤ P.nu 0 c σ y (v i) := by
  first | exact @GlobalTheory.HSNef.GenLow.gen_low | exact GlobalTheory.HSNef.GenLow.gen_low | (intros; apply GlobalTheory.HSNef.GenLow.gen_low <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.hermLBLeBySmallSection_of_rep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b a' b' : ℤ) (M M' : HermLB p) (f : X.functionField), P.Rep a b M → P.Rep a' b' M' → f ≠ 0 → f ∈ P.Bl (a - a') (b - b') 1 → Le M' M := by
  first | exact @GlobalTheory.HSNef.le_of_rep | exact GlobalTheory.HSNef.le_of_rep | (intros; apply GlobalTheory.HSNef.le_of_rep <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.mixedArithIntersection_nonneg_of_small_section_diff : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (Φ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ), IsArFun ![A, B] D Φ → Le B A → ∀ x y : ℕ, HtNef ((A.pow x).tens (B.pow y)) D → 0 ≤ Φ ((MvPolynomial.X 0 - MvPolynomial.X 1) * (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (y : ℝ) * MvPolynomial.X 1) ^ D) := by
  first | exact @GlobalTheory.HSNef.mixed_diff_nonneg | exact GlobalTheory.HSNef.mixed_diff_nonneg | (intros; apply GlobalTheory.HSNef.mixed_diff_nonneg <;> assumption)
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integrableOn_offHyp_of_norm_le_poin {n : ℕ} (S : Finset (Fin n)) (U K : Set (V n)) (g : V n → ℂ) (C : ℝ)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hs : ∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2)
    (hg : ContinuousOn g (offHyp S U)) (h0 : ∀ v ∈ offHyp S U, v ∉ K → g v = 0)
    (hb : ∀ v ∈ offHyp S U, v ∈ K → ‖g v‖ ≤ C * ∏ a, (poinWt S v a)⁻¹ ^ 2) :
    IntegrableOn g (offHyp S U) := by
  have hO : MeasurableSet (offHyp S U) := (isOpen_offHyp_of_isOpen S U hU).measurableSet
  have hv : IntegrableOn (fun v => C * ∏ a, (poinWt S v a)⁻¹ ^ 2) K :=
    (GlobalTheory.T.poincare_volume_integrableOn_compact_punctured_polydisc S K hK fun v hv => hs v (hKU hv)).const_mul C
  have hi : Integrable (K.indicator fun v => C * ∏ a, (poinWt S v a)⁻¹ ^ 2) :=
    (integrable_indicator_iff hK.measurableSet).2 hv
  refine Integrable.mono' hi.integrableOn (hg.aestronglyMeasurable hO) ?_
  refine (ae_restrict_iff' hO).2 (Eventually.of_forall fun v hvO => ?_)
  by_cases hvK : v ∈ K
  · rw [Set.indicator_of_mem hvK]
    exact hb v hvO hvK
  · rw [Set.indicator_of_notMem hvK, h0 v hvO hvK, norm_zero]

end GlobalTheory.GoodTop
end

section

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem sum_corrDens_eq_zero : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), ∀ {ι : Type} [Fintype ι] (ρ : ι → CxPts X.str σ → ℝ), (∀ i y, CInfAt (ρ i) y) → (∀ y, ∑ i, ρ i y = 1) → ∀ (c : AlgChart X.str σ X.dim) (y : CxPts X.str σ), y ∈ c.e.source → ∑ i, corrDens E H₀ H (ρ i) c y = 0 := by
  intro F _ σ X m E O H H₀ ι _ ρ hρ h1 c y hy
  have hc : IsHoloChart c.e := c.holo
  have key := GlobalTheory.T.sum_transgressionTopCoeffComplex_partitionOfUnity_eq_zero (fun i v => ρ i (c.e.symm v))
    (fun v => H₀ (E.nonempty (under y)).choose (c.e.symm v) ())
    (fun v => H (E.nonempty (under y)).choose (c.e.symm v) ()) (c.e y)
    (fun i => (contDiffAt_holoChart hc hy (hρ i y)).differentiableAt (by simp))
    (fun x => h1 _)
  simp only [corrDens, corrTop]
  rw [← Finset.mul_sum, ← Complex.re_sum, key]
  simp

end GlobalTheory.GoodTop
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

theorem nu_conjPt {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) (a b : ℤ)
    {f : X.functionField} (hf : f ∈ P.H a b) {σ σ' : k →+* ℂ} {y : CxPts p σ} {y' : CxPts p σ'}
    (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) : P.nu a b σ' y' f = P.nu a b σ y f := by
  have hi := mem_pick (P.L.φ σ).isLB y
  have hj := mem_pick (P.A.φ σ).isLB y
  have hi' := CxPts.mem_ptsIn_conj h hi
  have hj' := CxPts.mem_ptsIn_conj h hj
  have hreg := hf _ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
  rw [GlobalTheory.VolBr.nu_eq k X p P a b f hf σ' y' _ _ hi' hj', GlobalTheory.VolBr.nu_eq k X p P a b f hf σ y _ _ hi hj,
    ratVal_conj h hreg, Complex.norm_conj, P.L.conj σ σ' _ y y' h hi, P.A.conj σ σ' _ y y' h hj]

theorem exists_isCan_bdd : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∃ u : SmFn p, IsCan P e n x u ∧ ∀ σ y, |u.u σ y| ≤ B := by
  intro k _ X _ p D hX P e x hx
  obtain ⟨B, hB, hb⟩ := GlobalTheory.T.fubiniStudy_log_sum_weight_uniformly_bounded k X p D hX P e x hx
  refine ⟨B, hB, fun n hn => ⟨⟨fun σ y => ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n)),
    fun σ y => GlobalTheory.T.complexPointsSmoothAt_fubiniStudy_log_sum_weight k X p P D e x hx n hn σ y, fun σ σ' i y y' h _ => ?_⟩, fun σ y => rfl, fun σ y => hb n hn σ y⟩⟩
  change ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ' y' (x l) ^ (2 * n)) =
    ((e : ℝ) * n)⁻¹ * Real.log (∑ l, P.nu e 0 σ y (x l) ^ (2 * n))
  simp only [nu_conjPt P _ _ (hx.mem _) h]

end GlobalTheory.HSAmp
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem GlobalTheory.HSAmp.common_zero_of_le_dim : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (ℓ d : ℕ) (C : Set X) (e : Fin d → ℕ) (g : Fin d → X.functionField), ℓ.Prime → IsIrreducible C → IsClosed C → C ⊆ fib X ℓ → (d : WithBot ℕ∞) ≤ topologicalKrullDim C → (∀ j, 0 < e j ∧ g j ∈ P.H (e j) 0) → (C \ ⋃ j, NV P (e j) 0 (g j)).Nonempty := by
  intro k _ X _ p D hX P hA ℓ d
  induction d with
  | zero =>
    intro C e g hℓ hC hCc hCf hd hg
    obtain ⟨x, hx⟩ := hC.nonempty
    exact ⟨x, hx, by simp⟩
  | succ d ih =>
    intro C e g hℓ hC hCc hCf hd hg
    obtain ⟨C', h1, h2, h3, h4⟩ := GlobalTheory.T.exists_irreducible_codim_one_zero_ample_section_fibre k X p D hX P hA ℓ d (e 0) C (g 0) hℓ hC hCc hCf
      (by exact_mod_cast hd) (hg 0).1 (hg 0).2
    obtain ⟨x, hxC', hx⟩ := ih C' (fun j => e j.succ) (fun j => g j.succ) hℓ h1 h2
      (h3.trans (Set.diff_subset.trans hCf)) h4 (fun j => hg j.succ)
    refine ⟨x, (h3 hxC').1, ?_⟩
    simp only [Set.mem_iUnion, not_exists] at hx ⊢
    intro j
    refine Fin.cases ?_ (fun j => hx j) j
    exact (h3 hxC').2
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_ample_pow_section_nonvanishing_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ T : Set X, IsClosed T → (∀ ℓ : ℕ, (T ∩ fib X ℓ).Finite) → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, T ⊆ NV P e 0 f := by
  first | exact @GlobalTheory.HSAmp.exists_pow_section_nonvanishing_on_closed | exact GlobalTheory.HSAmp.exists_pow_section_nonvanishing_on_closed | (intros; apply GlobalTheory.HSAmp.exists_pow_section_nonvanishing_on_closed <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.exists_sections_cut_genericFibre_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (d : ℕ) (Z : Set X), IsClosed Z → topologicalKrullDim ↥(Z ∩ fib X 0) ≤ d → ∃ (e : Fin d → ℕ) (g : Fin d → X.functionField), (∀ j, 0 < e j ∧ g j ∈ P.H (e j) 0) ∧ ((Z \ ⋃ j, NV P (e j) 0 (g j)) ∩ fib X 0).Finite := by
  first | exact @GlobalTheory.HSAmp.GenCut.exists_sections_finite | exact GlobalTheory.HSAmp.GenCut.exists_sections_finite | (intros; apply GlobalTheory.HSAmp.GenCut.exists_sections_finite <;> assumption)
end
